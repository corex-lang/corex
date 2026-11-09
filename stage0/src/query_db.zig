//! Demand-Driven Incremental Query Engine & Early-Cutoff Database
//!
//! Implements the Salsa-inspired `CompilerDb` incremental query engine (`DR-12` Section 3) with
//! 3-tier `Durability` fast-paths, 128-bit `Wyhash` / `Blake3` `Fingerprint128` Early Cutoff
//! (backdating), position-independent `ItemTree` signature firewalls, and cooperative cancellation.
//!
//! All query memo headers (`MemoHeader`) and dependency edges (`QueryKey`) are stored in flat
//! value arrays indexed by integer offsets so recursive verification (`maybeChangedAfter`) and
//! re-execution (`executeAndBackdate`) never retain dangling pointers across hash table growth.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const diagnostic = @import("diag/diagnostic.zig");

const FileId = mem_foundation.FileId;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
const TokenKind = syntax_arenas.TokenKind;
const CstNodeKind = syntax_arenas.CstNodeKind;
const AstTag = syntax_arenas.AstTag;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const DiagnosticSink = diagnostic.DiagnosticSink;

// ---------------------------------------- TYPES ----------------------------------------

// ---------------- Revisions, Durability & Keys ----------------

/// Monotonically increasing logical database revision clock bumped on input mutations.
pub const Revision = enum(u32) {
    /// Initial revision assigned when `CompilerDb` is constructed (`1`).
    initial = 1,
    _,

    /// Converts a raw 32-bit unsigned integer into a `Revision`.
    pub inline fn fromInt(raw_val: u32) Revision {
        return @enumFromInt(raw_val);
    }

    /// Returns the underlying 32-bit integer representation of `self`.
    pub inline fn asInt(self: Revision) u32 {
        return @intFromEnum(self);
    }

    /// Returns the next sequential `Revision` (`self + 1`).
    pub inline fn next(self: Revision) Revision {
        return @enumFromInt(self.asInt() + 1);
    }

    /// Returns `true` if `self` occurred strictly after `other` (`self > other`).
    pub inline fn isAfter(self: Revision, other: Revision) bool {
        return self.asInt() > other.asInt();
    }
};

/// Input stability classification enabling $O(1)$ subtree verification skips (`DR-12` Section 3.2).
pub const Durability = enum(u2) {
    /// Volatile open editor buffers modified on keystrokes (`textDocument/didChange`).
    low = 0,
    /// Unopened workspace `.cx` source files on disk watched by the file watcher.
    medium = 1,
    /// Immutable standard library (`std::*`) modules and locked external dependencies.
    high = 2,

    /// Returns the less durable (minimum) tier of `first` and `second`.
    pub inline fn minTier(first: Durability, second: Durability) Durability {
        return if (@intFromEnum(first) < @intFromEnum(second)) first else second;
    }
};

/// 128-bit structural or cryptographic content digest used for $O(1)$ Early Cutoff comparisons.
pub const Fingerprint128 = extern struct {
    /// Lower 64 bits of the 128-bit digest.
    low: u64,
    /// Upper 64 bits of the 128-bit digest.
    high: u64,

    /// Canonical all-zero 128-bit fingerprint constant.
    pub const ZERO: Fingerprint128 = .{ .low = 0, .high = 0 };
    /// Primary `Wyhash` seed for the lower 64-bit lane (`0`).
    pub const SEED_LOW: u64 = 0;
    /// Golden-ratio `Wyhash` seed for the upper 64-bit lane (`0x9E3779B97F4A7C15`).
    pub const SEED_HIGH: u64 = 0x9E37_79B9_7F4A_7C15;

    /// Returns `true` if `first` and `second` are bit-for-bit identical across all 128 bits.
    pub inline fn eql(first: Fingerprint128, second: Fingerprint128) bool {
        return first.low == second.low and first.high == second.high;
    }

    /// Computes a fast 128-bit fingerprint of `bytes` using dual-seeded `std.hash.Wyhash`.
    pub inline fn hashBytes(bytes: []const u8) Fingerprint128 {
        return .{
            .low = std.hash.Wyhash.hash(SEED_LOW, bytes),
            .high = std.hash.Wyhash.hash(SEED_HIGH, bytes),
        };
    }

    /// Computes a cryptographic 128-bit truncated `BLAKE3` digest of `bytes`.
    pub fn hashBlake3(bytes: []const u8) Fingerprint128 {
        var digest_bytes: [16]u8 = undefined;
        std.crypto.hash.Blake3.hash(bytes, &digest_bytes, .{});
        return .{
            .low = std.mem.readInt(u64, digest_bytes[0..8], .little),
            .high = std.mem.readInt(u64, digest_bytes[8..16], .little),
        };
    }
};

/// Streaming 128-bit dual-lane `Wyhash` accumulator for position-independent AST/CST hashing.
pub const StructuralHasher = struct {
    /// Lower 64-bit streaming `Wyhash` state seeded with `Fingerprint128.SEED_LOW`.
    low_hasher: std.hash.Wyhash,
    /// Upper 64-bit streaming `Wyhash` state seeded with `Fingerprint128.SEED_HIGH`.
    high_hasher: std.hash.Wyhash,

    /// Initializes a new streaming 128-bit `StructuralHasher`.
    pub inline fn init() StructuralHasher {
        return .{
            .low_hasher = std.hash.Wyhash.init(Fingerprint128.SEED_LOW),
            .high_hasher = std.hash.Wyhash.init(Fingerprint128.SEED_HIGH),
        };
    }

    /// Feeds an arbitrary byte slice (prefixed by its 32-bit length) into both hash lanes.
    pub inline fn updateBytes(self: *StructuralHasher, bytes: []const u8) void {
        self.updateU32(@intCast(@min(bytes.len, std.math.maxInt(u32))));
        self.low_hasher.update(bytes);
        self.high_hasher.update(bytes);
    }

    /// Feeds a single 8-bit unsigned integer into both hash lanes.
    pub inline fn updateU8(self: *StructuralHasher, value: u8) void {
        const buf = [1]u8{value};
        self.low_hasher.update(&buf);
        self.high_hasher.update(&buf);
    }

    /// Feeds a little-endian 16-bit unsigned integer into both hash lanes.
    pub inline fn updateU16(self: *StructuralHasher, value: u16) void {
        var buf: [2]u8 = undefined;
        std.mem.writeInt(u16, &buf, value, .little);
        self.low_hasher.update(&buf);
        self.high_hasher.update(&buf);
    }

    /// Feeds a little-endian 32-bit unsigned integer into both hash lanes.
    pub inline fn updateU32(self: *StructuralHasher, value: u32) void {
        var buf: [4]u8 = undefined;
        std.mem.writeInt(u32, &buf, value, .little);
        self.low_hasher.update(&buf);
        self.high_hasher.update(&buf);
    }

    /// Feeds a little-endian 64-bit unsigned integer into both hash lanes.
    pub inline fn updateU64(self: *StructuralHasher, value: u64) void {
        var buf: [8]u8 = undefined;
        std.mem.writeInt(u64, &buf, value, .little);
        self.low_hasher.update(&buf);
        self.high_hasher.update(&buf);
    }

    /// Feeds an existing 128-bit `Fingerprint128` into both hash lanes.
    pub inline fn updateFingerprint(self: *StructuralHasher, fp: Fingerprint128) void {
        self.updateU64(fp.low);
        self.updateU64(fp.high);
    }

    /// Finalizes and returns the 128-bit `Fingerprint128` digest.
    pub inline fn final(self: *StructuralHasher) Fingerprint128 {
        return .{
            .low = self.low_hasher.final(),
            .high = self.high_hasher.final(),
        };
    }
};

/// Packed 32-bit definition handle encoding a 20-bit `FileId` and 12-bit file-local item index.
pub const DefId = packed struct(u32) {
    /// Zero-based item ordinal within `file_index` (`0..4095`).
    local_item_index: u12 = 0,
    /// Owning source file index (`0..1,048,574`).
    file_index: u20 = 0,

    /// Sentinel `DefId` representing no definition (`0xFFFF_FFFF`).
    pub const NONE: DefId = @bitCast(@as(u32, std.math.maxInt(u32)));

    /// Constructs a `DefId` from `file_id` and `item_index`, clamping to avoid `DefId.NONE`.
    pub inline fn init(file_id: FileId, item_index: u12) DefId {
        std.debug.assert(!file_id.isNone());
        const masked_file: u20 = @intCast(file_id.asInt() & 0xF_FFFF);
        const safe_item: u12 = if (masked_file == 0xF_FFFF and item_index == 0xFFF)
            0xFFE
        else
            item_index;
        return .{
            .local_item_index = safe_item,
            .file_index = masked_file,
        };
    }

    /// Extracts the owning `FileId` of `self`.
    pub inline fn fileId(self: DefId) FileId {
        if (self.isNone()) return .none;
        return FileId.fromInt(self.file_index);
    }

    /// Returns the zero-based local item ordinal within `self.fileId()`.
    pub inline fn itemIndex(self: DefId) u12 {
        return self.local_item_index;
    }

    /// Returns the raw 32-bit integer backing `self`.
    pub inline fn asInt(self: DefId) u32 {
        return @bitCast(self);
    }

    /// Reconstructs a `DefId` from a raw 32-bit unsigned integer.
    pub inline fn fromInt(raw_val: u32) DefId {
        return @bitCast(raw_val);
    }

    /// Zero-extends `self` into a 64-bit unsigned integer key.
    pub inline fn asU64(self: DefId) u64 {
        return @as(u64, self.asInt());
    }

    /// Returns `true` if `self` is the `DefId.NONE` sentinel.
    pub inline fn isNone(self: DefId) bool {
        return self.asInt() == std.math.maxInt(u32);
    }
};

/// Canonical 10-stage demand-driven query pipeline (`PLAN.md` Phase 3 & `DR-12` Section 3.1).
pub const QueryStage = enum(u8) {
    /// Stage 0: External source text input (`FileId -> SourceInput`).
    source_text = 0,
    /// Stage 1: Lossless CST and token stream parse (`FileId -> ParsedCstArtifact`).
    parse_cst = 1,
    /// Stage 2: Trivia-stripped AST lowering with comment/whitespace Early Cutoff (`FileId -> LoweredAstArtifact`).
    lower_ast = 2,
    /// Stage 3: Position-independent top-level `ItemTree` extraction (`FileId -> ItemTree`).
    item_tree = 3,
    /// Stage 4: Per-item signature fingerprint projection (`DefId -> Fingerprint128`).
    item_tree_sig_proj = 4,
    /// Stage 5: Position-independent body AST window projection (`DefId -> BodyAstWindow`).
    body_ast_proj = 5,
    /// Stage 6: Module-level exported and local signature table resolution (`FileId -> ResolvedSignaturesArtifact`).
    resolve_signatures = 6,
    /// Stage 7: Fine-grained symbol signature lookup (`DefId -> DefSignatureArtifact`).
    def_signature = 7,
    /// Stage 8: Isolated per-definition bidirectional body typecheck (`DefId -> TypedBodyArtifact`).
    typecheck_body = 8,
    /// Stage 9: Per-definition SSA MIR SAST memory and exclusivity verification (`DefId -> SastVerificationArtifact`).
    verify_sast_mir = 9,
};

/// Universal 8-byte key uniquely identifying a node in the `CompilerDb` dependency DAG.
pub const QueryKey = extern struct {
    /// Pipeline stage of this query (`1` byte).
    stage: QueryStage,
    /// Optional query mode or disambiguator flags (`1` byte).
    flags: u8 = 0,
    /// Reserved alignment padding (`2` bytes, always `0`).
    reserved: u16 = 0,
    /// Target entity index (`FileId.asInt()` or `DefId.asInt()`, `4` bytes).
    entity_index: u32,

    /// Constructs a `QueryKey` targeting `file_id` at `stage`.
    pub inline fn forFile(stage: QueryStage, file_id: FileId) QueryKey {
        return .{
            .stage = stage,
            .flags = 0,
            .reserved = 0,
            .entity_index = file_id.asInt(),
        };
    }

    /// Constructs a `QueryKey` targeting `def_id` at `stage`.
    pub inline fn forDef(stage: QueryStage, def_id: DefId) QueryKey {
        return .{
            .stage = stage,
            .flags = 0,
            .reserved = 0,
            .entity_index = def_id.asInt(),
        };
    }

    /// Packs `self` into a 64-bit unsigned integer for $O(1)$ hash table lookup.
    pub inline fn asU64(self: QueryKey) u64 {
        return (@as(u64, self.entity_index) << 32) |
            (@as(u64, self.reserved) << 16) |
            (@as(u64, self.flags) << 8) |
            @as(u64, @intFromEnum(self.stage));
    }
};

/// 40-byte memoized query header tracking revisions, durability, and dependency edge slices.
pub const MemoHeader = struct {
    /// 128-bit structural fingerprint of the most recently computed query output (`16` bytes).
    output_fingerprint: Fingerprint128,
    /// Latest `Revision` in which all transitive dependencies of this memo were verified (`4` bytes).
    verified_at: Revision,
    /// Latest `Revision` in which `output_fingerprint` actually changed (preserved on Early Cutoff, `4` bytes).
    changed_at: Revision,
    /// Starting index into `CompilerDb.dep_edges` (`4` bytes).
    dep_edge_start: u32,
    /// Number of direct dependency edges in `CompilerDb.dep_edges` (`2` bytes).
    dep_edge_len: u16,
    /// Minimum `Durability` tier across all transitive inputs read by this query (`1` byte).
    min_durability: Durability,
    /// `true` if every transitive dependency of this query has `.high` durability (`1` byte).
    is_pure_high_durability: bool,
    /// Dense slot index into the stage-specific artifact storage table (`4` bytes).
    artifact_index: u32,
    /// Explicit trailing alignment padding (`4` bytes, always `0`).
    padding: u32 = 0,
};

/// Active call-stack frame tracking dynamic dependencies during query execution.
pub const ActiveQueryFrame = struct {
    /// Query currently being executed in this stack frame.
    key: QueryKey,
    /// Starting offset in `CompilerDb.scratch_dep_edges` owned by this frame.
    start_dep_index: usize,
    /// Minimum `Durability` observed across child queries read so far.
    min_durability: Durability,
    /// `true` if all child queries read so far are pure `.high` durability.
    is_pure_high_durability: bool,
    /// Maximum `changed_at` revision observed across child queries read so far.
    max_dep_changed_at: Revision,
};

/// Error set returned by demand-driven queries in `CompilerDb`.
pub const QueryError = error{
    /// Cooperative cancellation was requested via `requestCancellation()`.
    Cancelled,
    /// A cyclic query dependency was detected on the active execution stack.
    DependencyCycle,
    /// Queried `FileId` has not been registered via `setInput()`.
    MissingSourceInput,
    /// Queried `DefId` is `.NONE` or out of bounds for its file's `ItemTree`.
    InvalidDefId,
    /// Backing arena or table allocation failed.
    OutOfMemory,
};

// --------------- Stage Artifact Representations ---------------

/// Stage 0 input record owning the UTF-8 source buffer and durability metadata for a `FileId`.
pub const SourceInput = struct {
    /// Owned UTF-8 source text buffer allocated in `CompilerDb.allocator`.
    owned_text: []u8,
    /// 128-bit `Wyhash` content fingerprint of `owned_text`.
    content_fingerprint: Fingerprint128,
    /// Stability tier assigned to this source file.
    durability: Durability,
    /// Revision at which this source input last mutated.
    changed_at: Revision,
};

/// Stage 1 parsed syntax artifact owning the reusable `TokenBuffer`, `LosslessCstArena`, and `AstArena`.
pub const ParsedCstArtifact = struct {
    /// SoA lexical token and trivia buffer.
    token_buffer: TokenBuffer,
    /// Pre-order lossless Concrete Syntax Tree arena.
    cst_arena: LosslessCstArena,
    /// Lowered Structure-of-Arrays Abstract Syntax Tree arena.
    ast_arena: AstArena,
    /// Arena-backed syntax diagnostic sink.
    diagnostics: DiagnosticSink,
    /// Full lossless CST + trivia 128-bit fingerprint.
    cst_fingerprint: Fingerprint128 = Fingerprint128.ZERO,
    /// Trivia-stripped, offset-independent 128-bit AST fingerprint.
    ast_fingerprint: Fingerprint128 = Fingerprint128.ZERO,
    /// Root translation unit AST node (`NodeIndex.root`).
    root_node: NodeIndex = .root,
    /// `true` if lexical or syntax errors were encountered during parsing.
    has_parse_errors: bool = false,

    /// Initializes an empty `ParsedCstArtifact` bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) ParsedCstArtifact {
        return .{
            .token_buffer = TokenBuffer.init(allocator),
            .cst_arena = LosslessCstArena.init(allocator),
            .ast_arena = AstArena.init(allocator),
            .diagnostics = DiagnosticSink.init(allocator),
        };
    }

    /// Clears syntax tables while retaining allocated capacity for fast incremental re-parsing.
    pub fn resetForReparse(self: *ParsedCstArtifact) void {
        self.token_buffer.tokens.shrinkRetainingCapacity(0);
        self.token_buffer.trivia.clearRetainingCapacity();
        self.cst_arena.nodes.shrinkRetainingCapacity(0);
        self.cst_arena.parse_stack.clearRetainingCapacity();
        self.cst_arena.has_parse_errors = false;
        self.ast_arena.nodes.shrinkRetainingCapacity(0);
        self.ast_arena.extra_data.clearRetainingCapacity();
        self.ast_arena.ast_to_cst.clearRetainingCapacity();
        self.diagnostics.diagnostics.clearRetainingCapacity();
        self.diagnostics.arena.resetRetainingCapacity();
        self.diagnostics.error_count = 0;
        self.diagnostics.warning_count = 0;
        self.diagnostics.has_reached_limit = false;
        self.has_parse_errors = false;
    }

    /// Releases all owned syntax arenas and diagnostic buffers.
    pub fn deinit(self: *ParsedCstArtifact) void {
        self.token_buffer.deinit();
        self.cst_arena.deinit();
        self.ast_arena.deinit();
        self.diagnostics.deinit();
        self.* = undefined;
    }
};

/// Stage 2 lowered AST summary artifact with trivia-insensitive Early Cutoff fingerprint.
pub const LoweredAstArtifact = struct {
    /// Source file handle.
    file_id: FileId,
    /// Root AST node index (`NodeIndex.root`).
    root_node: NodeIndex,
    /// Total number of AST nodes in `AstArena`.
    node_count: u32,
    /// `true` if syntax or lexical errors occurred in `file_id`.
    has_parse_errors: bool,
    /// Trivia-stripped, byte-offset-independent 128-bit AST fingerprint.
    ast_fingerprint: Fingerprint128,
};

/// Classification of top-level declarations in a file's `ItemTree`.
pub const ItemKind = enum(u8) {
    /// Module declaration (`mod`).
    mod_decl = 0,
    /// Import declaration (`use`).
    use_decl = 1,
    /// Function or subscript declaration (`fn` / `subscript`).
    fn_decl = 2,
    /// Struct or `bit_field` declaration (`struct` / `bit_field`).
    struct_decl = 3,
    /// Enum declaration (`enum`).
    enum_decl = 4,
    /// Union declaration (`union`).
    union_decl = 5,
    /// Trait interface declaration (`trait`).
    trait_decl = 6,
    /// Trait or inherent implementation block (`impl`).
    impl_decl = 7,
    /// Type alias declaration (`type`).
    type_alias_decl = 8,
    /// Compile-time constant declaration (`const`).
    const_decl = 9,
    /// Top-level `comptime` or extern block item.
    extern_block = 10,
};

/// Single top-level declaration entry in a file's position-independent `ItemTree`.
pub const ItemTreeEntry = struct {
    /// File-scoped definition identifier (`(file_id, local_item_index)`).
    def_id: DefId,
    /// Declaration category tag.
    kind: ItemKind,
    /// `true` if the declaration carries a top-level `pub` visibility modifier.
    is_pub: bool,
    /// Interned symbol handle for the declaration's primary identifier.
    name_symbol: SymbolId,
    /// Borrowed NUL-terminated slice from `CompilerDb.interner` for `name_symbol`.
    name_text: []const u8,
    /// Top-level AST node index inside `ParsedCstArtifact.ast_arena`.
    ast_node: NodeIndex,
    /// Originating CST node index inside `ParsedCstArtifact.cst_arena`.
    cst_node: CstNodeIndex,
    /// Body AST node index (`block` for `fn_decl`, initializer expr for `const_decl`, `.none` otherwise).
    body_ast_node: NodeIndex,
    /// Body CST node index (`block` CST node for `fn_decl`, initializer CST for `const_decl`, `.none` otherwise).
    body_cst_node: CstNodeIndex,
    /// Position-independent 128-bit fingerprint of the item's signature (excluding function body blocks).
    signature_fingerprint: Fingerprint128,
    /// Position-independent 128-bit fingerprint of the item's body block or initializer.
    body_fingerprint: Fingerprint128,
};

/// Stage 3 position-independent `ItemTree` firewall for a single source file.
pub const ItemTree = struct {
    /// Owned slice of top-level item descriptors in declaration order.
    entries: []ItemTreeEntry = &.{},
    /// Owning source file identifier.
    file_id: FileId = .none,
    /// 128-bit fingerprint of all item signatures in this file (excluding function bodies).
    tree_fingerprint: Fingerprint128 = Fingerprint128.ZERO,
    /// Combined 128-bit fingerprint covering both `tree_fingerprint` and all `body_fingerprint`s.
    combined_fingerprint: Fingerprint128 = Fingerprint128.ZERO,
    /// `LoweredAstArtifact.ast_fingerprint` from which this `ItemTree` was extracted.
    source_ast_fingerprint: Fingerprint128 = Fingerprint128.ZERO,

    /// Releases the owned `entries` slice back to `allocator`.
    pub fn deinit(self: *ItemTree, allocator: std.mem.Allocator) void {
        if (self.entries.len > 0) {
            allocator.free(self.entries);
        }
        self.* = undefined;
    }

    /// Looks up the `ItemTreeEntry` for `def_id` in $O(1)$ array index time.
    pub inline fn getEntry(self: *const ItemTree, def_id: DefId) ?*const ItemTreeEntry {
        if (def_id.isNone() or def_id.fileId() != self.file_id) return null;
        const idx: usize = def_id.itemIndex();
        if (idx >= self.entries.len) return null;
        return &self.entries[idx];
    }

    /// Searches `entries` for the first declaration named `name_text`.
    pub fn findByName(self: *const ItemTree, name_text: []const u8) ?*const ItemTreeEntry {
        for (self.entries) |*entry| {
            if (std.mem.eql(u8, entry.name_text, name_text)) {
                return entry;
            }
        }
        return null;
    }
};

/// Stage 5 position-independent relative body AST projection window for a `DefId`.
pub const BodyAstWindow = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Enclosing source file handle.
    file_id: FileId,
    /// Enclosing declaration AST node handle.
    item_ast_node: NodeIndex,
    /// Root AST node of the body block or constant initializer.
    body_ast_node: NodeIndex,
    /// Root CST node of the body block or constant initializer.
    body_cst_node: CstNodeIndex,
    /// Position-independent 128-bit fingerprint of the body's tokens and CST structure.
    body_fingerprint: Fingerprint128,
};

/// Stage 6 resolved module signature table summary for a `FileId`.
pub const ResolvedSignaturesArtifact = struct {
    /// Target source file handle.
    file_id: FileId,
    /// Total number of top-level items resolved in `file_id`.
    item_count: u32,
    /// Total number of `pub`-exported items in `file_id`.
    public_item_count: u32,
    /// 128-bit fingerprint of the resolved module signature map.
    signatures_fingerprint: Fingerprint128,
};

/// Stage 7 resolved definition signature summary for a single `DefId`.
pub const DefSignatureArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Declaration category tag.
    kind: ItemKind,
    /// `true` if exported with `pub`.
    is_pub: bool,
    /// Interned symbol identifier.
    name_symbol: SymbolId,
    /// 128-bit fingerprint of this definition's signature.
    signature_fingerprint: Fingerprint128,
};

/// Stage 8 per-definition bidirectional body type-checking artifact.
pub const TypedBodyArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Owning source file handle.
    file_id: FileId,
    /// Root AST node of the checked body.
    body_ast_node: NodeIndex,
    /// 128-bit signature fingerprint consumed during body checking.
    signature_fingerprint: Fingerprint128,
    /// 128-bit position-independent body AST fingerprint consumed during body checking.
    body_fingerprint: Fingerprint128,
    /// Combined 128-bit fingerprint of the typed body output.
    typed_fingerprint: Fingerprint128,
};

/// Stage 9 per-definition MIR SAST ownership and memory safety verification artifact.
pub const SastVerificationArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Owning source file handle.
    file_id: FileId,
    /// `true` if the body passed SAST verification without fatal memory safety errors.
    is_verified_sound: bool,
    /// 128-bit fingerprint of the SAST verification summary.
    sast_fingerprint: Fingerprint128,
};

/// Telemetry counters tracking per-stage query executions, Early Cutoffs, and fast-path hits.
pub const QueryTelemetry = struct {
    /// Number of times each `QueryStage` (`0..9`) executed its compute function.
    stage_executions: [STAGE_COUNT]u64 = @splat(0),
    /// Number of times `maybeChangedAfter` verified a memo on the Green Path without re-execution.
    green_hits: u64 = 0,
    /// Number of times `maybeChangedAfter` skipped dependency traversal via the Durability fast-path.
    durability_fast_path_hits: u64 = 0,
    /// Number of times `executeAndBackdate` recomputed an identical fingerprint and backdated `changed_at`.
    early_cutoff_hits: u64 = 0,

    /// Returns the total execution count recorded for `stage`.
    pub inline fn countExecutions(self: *const QueryTelemetry, stage: QueryStage) u64 {
        return self.stage_executions[@intFromEnum(stage)];
    }

    /// Resets all telemetry counters to zero.
    pub inline fn reset(self: *QueryTelemetry) void {
        self.* = .{};
    }
};

/// Optional callback hook invoked at the start of `computeStage` for deterministic cycle testing.
pub const CustomStageHook = *const fn (db: *CompilerDb, key: QueryKey) QueryError!void;

// --------------------------------------- CONSTS ----------------------------------------

/// Total number of `QueryStage` variants in the canonical pipeline (`10`).
pub const STAGE_COUNT: usize = @typeInfo(QueryStage).@"enum".field_names.len;
/// Total number of `Durability` tiers (`3`: `.low`, `.medium`, `.high`).
pub const DURABILITY_COUNT: usize = @typeInfo(Durability).@"enum".field_names.len;
/// Maximum number of top-level items encoded in a 12-bit `DefId.local_item_index` (`4,096`).
pub const MAX_ITEMS_PER_FILE: usize = std.math.maxInt(u12) + 1;
/// Maximum number of direct dependencies recorded in a single `MemoHeader` (`65,535`).
pub const MAX_DEPS_PER_MEMO: usize = std.math.maxInt(u16);
/// Sentinel byte hashed into `signature_fingerprint` in place of a skipped `.block` body.
const BODY_BLOCK_OMITTED_MARKER: u8 = 0xB0;
/// Sentinel byte hashed for parser-injected error recovery leaves (`is_missing_or_injected and has_error`).
const INJECTED_ERROR_LEAF_MARKER: u8 = 0xEE;

// -------------------------------------- INTERNALS --------------------------------------

// -------------- Lexeme & Token Helper Functions ---------------

/// Returns the UTF-8 source slice of `token_id`, or `""` for synthesized/out-of-bounds tokens.
inline fn getTokenLexeme(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    token_id: TokenIndex,
) []const u8 {
    if (token_id.isNone() or token_id.asInt() >= token_buffer.countTokens()) return "";
    const record = token_buffer.getToken(token_id);
    if (record.flags.is_synthesized or record.byte_len == 0) return "";
    const start_off: usize = record.byte_offset;
    const end_off: usize = @min(start_off + @as(usize, record.byte_len), source.len);
    if (start_off >= end_off) return "";
    return source[start_off..end_off];
}

/// Returns `true` if `kind` is an identifier token (`.ident`, `.type_ident`, or `.const_ident`).
inline fn isIdentifierTokenKind(kind: TokenKind) bool {
    return kind == .ident or kind == .type_ident or kind == .const_ident;
}

// ---------- Position-Independent Structural Hashers -----------

/// Computes the Stage 1 128-bit lossless CST fingerprint covering all tokens, trivia, and CST nodes.
pub fn computeCstFingerprint(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    hasher.updateU8(if (cst_arena.has_parse_errors) 1 else 0);
    hasher.updateU32(@intCast(source.len));
    hasher.updateBytes(source);

    const token_count = token_buffer.countTokens();
    hasher.updateU32(@intCast(token_count));
    var i: usize = 0;
    while (i < token_count) : (i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(i));
        const tok_rec = token_buffer.getToken(tok_id);
        hasher.updateU8(@intFromEnum(tok_rec.kind));
        hasher.updateU8(@bitCast(tok_rec.flags));
        hasher.updateU16(tok_rec.byte_len);
        hasher.updateU32(tok_rec.byte_offset);
    }

    const cst_count = cst_arena.countNodes();
    hasher.updateU32(@intCast(cst_count));
    i = 0;
    while (i < cst_count) : (i += 1) {
        const cst_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(i)));
        hasher.updateU8(@intFromEnum(cst_rec.kind));
        hasher.updateU8(@bitCast(cst_rec.flags));
        hasher.updateU32(cst_rec.token.asInt());
        hasher.updateU32(cst_rec.subtree_size);
    }
    return hasher.final();
}

/// Computes the Stage 2 128-bit AST fingerprint, stripping all comments, whitespace trivia, and byte offsets.
pub fn computeAstFingerprint(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    hasher.updateU8(if (cst_arena.has_parse_errors) 1 else 0);

    // [1] Hash all lowered AST nodes using token kinds and lexeme strings (ignoring byte offsets):
    const ast_count = ast_arena.countNodes();
    hasher.updateU32(@intCast(ast_count));
    var i: usize = 0;
    while (i < ast_count) : (i += 1) {
        const node = ast_arena.getNode(NodeIndex.fromInt(@intCast(i)));
        hasher.updateU8(@intFromEnum(node.tag));
        if (!node.main_token.isNone() and node.main_token.asInt() < token_buffer.countTokens()) {
            const main_rec = token_buffer.getToken(node.main_token);
            hasher.updateU8(@intFromEnum(main_rec.kind));
            hasher.updateBytes(getTokenLexeme(source, token_buffer, node.main_token));
        } else {
            hasher.updateU8(0xFF);
        }

        hasher.updateU8(@intFromEnum(node.lhs.tag));
        if (node.lhs.tag == .token) {
            const lhs_tok = TokenIndex.fromInt(node.lhs.payload);
            if (lhs_tok.asInt() < token_buffer.countTokens()) {
                hasher.updateU8(@intFromEnum(token_buffer.getToken(lhs_tok).kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, lhs_tok));
            }
        } else {
            hasher.updateU32(node.lhs.payload);
        }

        hasher.updateU8(@intFromEnum(node.rhs.tag));
        if (node.rhs.tag == .token) {
            const rhs_tok = TokenIndex.fromInt(node.rhs.payload);
            if (rhs_tok.asInt() < token_buffer.countTokens()) {
                hasher.updateU8(@intFromEnum(token_buffer.getToken(rhs_tok).kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, rhs_tok));
            }
        } else {
            hasher.updateU32(node.rhs.payload);
        }
    }

    hasher.updateU32(@intCast(ast_arena.extra_data.items.len));
    for (ast_arena.extra_data.items) |extra_val| {
        hasher.updateU32(extra_val);
    }

    // [2] Hash non-carrier CST nodes and leaf token lexemes (ignoring trivia and byte offsets):
    const cst_count = cst_arena.countNodes();
    i = 0;
    while (i < cst_count) : (i += 1) {
        const cst_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(i)));
        const is_leaf = cst_rec.subtree_size <= 1 and !cst_rec.flags.is_bracketed;
        if (is_leaf and cst_rec.flags.is_missing_or_injected and !cst_rec.flags.has_error) {
            continue;
        }
        hasher.updateU8(@intFromEnum(cst_rec.kind));
        hasher.updateU8(if (cst_rec.flags.has_error) 1 else 0);
        if (is_leaf) {
            if (cst_rec.flags.is_missing_or_injected and cst_rec.flags.has_error) {
                hasher.updateU8(INJECTED_ERROR_LEAF_MARKER);
            } else if (!cst_rec.token.isNone() and cst_rec.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(cst_rec.token);
                hasher.updateU8(@intFromEnum(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, cst_rec.token));
            }
        } else {
            hasher.updateU32(cst_rec.subtree_size);
        }
    }
    return hasher.final();
}

/// Computes the position-independent signature fingerprint of `item_cst_node`, skipping `.block` bodies.
pub fn computeItemSignatureFingerprint(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
    body_cst_node: CstNodeIndex,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) {
        return hasher.final();
    }

    const root_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        root_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var fn_member_end_idx: usize = if (root_rec.kind == .fn_item or
        root_rec.kind == .trait_member or
        root_rec.kind == .impl_member)
        end_idx
    else
        0;
    var after_fn_sig_idx: usize = std.math.maxInt(usize);
    var cursor: usize = root_idx;
    while (cursor < end_idx) {
        const current_cst_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(current_cst_id);
        const step_size: usize = @max(@as(usize, node.subtree_size), 1);

        // [1] Skip explicit `body_cst_node`, `comptime` inner `.block`, or direct function/method body `.block`:
        if (!body_cst_node.isNone() and current_cst_id == body_cst_node) {
            hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
            cursor += step_size;
            continue;
        }
        if (cursor > root_idx) {
            if (root_rec.kind == .block and node.kind == .block) {
                hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                cursor += step_size;
                continue;
            }
            if (node.kind == .block and cursor >= after_fn_sig_idx and cursor < fn_member_end_idx) {
                hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                after_fn_sig_idx = std.math.maxInt(usize);
                cursor += step_size;
                continue;
            }
        }

        if (node.kind == .fn_item or node.kind == .trait_member or node.kind == .impl_member) {
            fn_member_end_idx = cursor + step_size;
            after_fn_sig_idx = std.math.maxInt(usize);
        } else if (node.kind == .fn_sig and cursor < fn_member_end_idx) {
            after_fn_sig_idx = cursor + step_size;
        }

        // [2] Hash CST node kind and leaf token lexeme while skipping pure trivia carriers:
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (is_leaf) {
            if (node.flags.is_missing_or_injected) {
                if (node.flags.has_error) {
                    hasher.updateU8(@intFromEnum(node.kind));
                    hasher.updateU8(INJECTED_ERROR_LEAF_MARKER);
                }
                cursor += 1;
                continue;
            }
            hasher.updateU8(@intFromEnum(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            if (!node.token.isNone() and node.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(node.token);
                hasher.updateU8(@intFromEnum(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
            }
        } else {
            hasher.updateU8(@intFromEnum(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            if (cursor > root_idx and node.kind != .trait_member and node.kind != .impl_member) {
                hasher.updateU32(node.subtree_size);
            }
        }
        cursor += 1;
    }
    return hasher.final();
}

/// Appends the position-independent CST structure and token lexemes of `subtree_cst` into `hasher`.
fn hashPositionIndependentCstSubtree(
    hasher: *StructuralHasher,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    subtree_cst: CstNodeIndex,
) void {
    if (subtree_cst.isNone() or subtree_cst.asInt() >= cst_arena.countNodes()) return;
    const start_idx: usize = subtree_cst.asInt();
    const root_rec = cst_arena.getNode(subtree_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (is_leaf) {
            if (node.flags.is_missing_or_injected) {
                if (node.flags.has_error) {
                    hasher.updateU8(@intFromEnum(node.kind));
                    hasher.updateU8(INJECTED_ERROR_LEAF_MARKER);
                }
                continue;
            }
            hasher.updateU8(@intFromEnum(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            if (!node.token.isNone() and node.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(node.token);
                hasher.updateU8(@intFromEnum(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
            }
        } else {
            hasher.updateU8(@intFromEnum(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            hasher.updateU32(node.subtree_size);
        }
    }
}

/// Computes the position-independent 128-bit fingerprint of an item's body block or initializer.
pub fn computeItemBodyFingerprint(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
    body_cst_node: CstNodeIndex,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    if (!body_cst_node.isNone() and body_cst_node.asInt() < cst_arena.countNodes()) {
        hasher.updateU8(1);
        hashPositionIndependentCstSubtree(&hasher, source, token_buffer, cst_arena, body_cst_node);
        return hasher.final();
    }

    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) {
        hasher.updateU8(0);
        return hasher.final();
    }

    const root_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        root_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    // For `trait` or `impl` containers, hash any default/member method `.block` subtrees:
    if (root_rec.kind == .trait_item or root_rec.kind == .impl_item) {
        var has_any_block = false;
        var cursor: usize = root_idx + 1;
        while (cursor < end_idx) {
            const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
            const sub_node = cst_arena.getNode(sub_id);
            if (sub_node.kind == .block) {
                has_any_block = true;
                hashPositionIndependentCstSubtree(&hasher, source, token_buffer, cst_arena, sub_id);
                cursor += @max(@as(usize, sub_node.subtree_size), 1);
                continue;
            }
            cursor += 1;
        }
        if (!has_any_block) hasher.updateU8(0);
        return hasher.final();
    }

    // For `.const_item` without a mapped `body_cst_node`, hash tokens following `=`:
    if (root_rec.kind == .const_item) {
        var has_seen_eq = false;
        var cursor: usize = root_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!has_seen_eq) {
                if (is_leaf and !node.flags.is_missing_or_injected and
                    !node.token.isNone() and node.token.asInt() < token_buffer.countTokens() and
                    token_buffer.getToken(node.token).kind == .eq)
                {
                    has_seen_eq = true;
                    hasher.updateU8(1);
                }
                continue;
            }
            if (is_leaf and !node.flags.is_missing_or_injected and
                !node.token.isNone() and node.token.asInt() < token_buffer.countTokens())
            {
                const tok_rec = token_buffer.getToken(node.token);
                if (tok_rec.kind == .semi) break;
                hasher.updateU8(@intFromEnum(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
            }
        }
        if (!has_seen_eq) hasher.updateU8(0);
        return hasher.final();
    }

    hasher.updateU8(0);
    return hasher.final();
}

// ---------------- ItemTree Extraction Helpers -----------------

/// Maps an `AstTag` at top-level item position to its corresponding `ItemKind`, or `null` for holes.
fn astTagToItemKind(tag: AstTag) ?ItemKind {
    return switch (tag) {
        .mod_decl => .mod_decl,
        .use_decl => .use_decl,
        .fn_decl => .fn_decl,
        .struct_decl => .struct_decl,
        .enum_decl => .enum_decl,
        .union_decl => .union_decl,
        .trait_decl => .trait_decl,
        .impl_decl => .impl_decl,
        .type_alias_decl => .type_alias_decl,
        .const_decl => .const_decl,
        .block => .extern_block,
        else => null,
    };
}

/// Returns `true` if `item_cst_node` has a top-level `.visibility_modifier` leaf before `main_token`.
fn extractItemIsPub(
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
    main_token: TokenIndex,
) bool {
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) return false;
    const start_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (!node.token.isNone() and !main_token.isNone() and node.token.asInt() >= main_token.asInt()) {
            break;
        }
        if (node.kind == .visibility_modifier) return true;
        if (node.kind == .attribute and node.subtree_size > 1) {
            cursor += @as(usize, node.subtree_size) - 1;
        }
    }
    return false;
}

/// Extracts the primary identifier lexeme of a top-level item from its AST/CST representation.
fn extractItemNameSlice(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_kind: ItemKind,
    main_token: TokenIndex,
    item_cst_node: CstNodeIndex,
) []const u8 {
    if (item_kind == .extern_block) return "comptime";
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) return "";

    const start_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    if (item_kind == .use_decl) {
        var last_ident: []const u8 = "";
        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
            if (node.token.asInt() >= token_buffer.countTokens()) continue;
            if (isIdentifierTokenKind(token_buffer.getToken(node.token).kind)) {
                last_ident = getTokenLexeme(source, token_buffer, node.token);
            }
        }
        return last_ident;
    }

    if (item_kind == .impl_decl) {
        var first_type_tok: TokenIndex = .none;
        var target_type_tok: TokenIndex = .none;
        var has_seen_for = false;
        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) : (cursor += 1) {
            const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if ((node.kind == .type_params or node.kind == .type_args or node.kind == .where_clause) and
                node.subtree_size > 1)
            {
                cursor += @as(usize, node.subtree_size) - 1;
                continue;
            }
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
            if (!main_token.isNone() and node.token.asInt() <= main_token.asInt()) continue;
            if (node.token.asInt() >= token_buffer.countTokens()) continue;

            const tok_kind = token_buffer.getToken(node.token).kind;
            if (tok_kind == .lbrace or tok_kind == .kw_where or tok_kind == .semi) break;
            if (tok_kind == .kw_for) {
                has_seen_for = true;
                continue;
            }
            if (isIdentifierTokenKind(tok_kind) or tok_kind == .prim_type or tok_kind == .kw_self_type) {
                if (!has_seen_for) {
                    if (first_type_tok.isNone()) first_type_tok = node.token;
                } else {
                    if (target_type_tok.isNone()) target_type_tok = node.token;
                }
            }
        }
        if (has_seen_for and !target_type_tok.isNone()) {
            if (!first_type_tok.isNone()) {
                const start_rec = token_buffer.getToken(first_type_tok);
                const end_rec = token_buffer.getToken(target_type_tok);
                const slice_start: usize = start_rec.byte_offset;
                const slice_end: usize = @min(source.len, @as(usize, end_rec.byte_offset) + end_rec.byte_len);
                if (slice_start < slice_end) return source[slice_start..slice_end];
            }
            return getTokenLexeme(source, token_buffer, target_type_tok);
        }
        if (!first_type_tok.isNone()) {
            return getTokenLexeme(source, token_buffer, first_type_tok);
        }
        return "";
    }

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
        if (!main_token.isNone() and node.token.asInt() <= main_token.asInt()) continue;
        if (node.token.asInt() >= token_buffer.countTokens()) continue;

        const tok_kind = token_buffer.getToken(node.token).kind;
        if (tok_kind == .lbrace or tok_kind == .semi or tok_kind == .eq or tok_kind == .colon) {
            break;
        }
        if (tok_kind == .lparen) {
            if (item_kind == .fn_decl and !main_token.isNone() and
                main_token.asInt() < token_buffer.countTokens() and
                token_buffer.getToken(main_token).kind == .ident)
            {
                return getTokenLexeme(source, token_buffer, main_token);
            }
            break;
        }
        if (isIdentifierTokenKind(tok_kind)) {
            return getTokenLexeme(source, token_buffer, node.token);
        }
    }
    return "";
}

/// Locates the direct `.block` body CST child inside `item_cst_node` (outside `.fn_sig`) if present.
fn findDirectBodyBlockCst(
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
) CstNodeIndex {
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) return .none;
    const root_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        root_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var sig_end_idx: usize = 0;
    var cursor: usize = root_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const cur_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(cur_id);
        if (node.kind == .fn_sig and cursor >= sig_end_idx) {
            sig_end_idx = cursor + @max(@as(usize, node.subtree_size), 1);
            continue;
        }
        if (cursor >= sig_end_idx and node.kind == .block) {
            return cur_id;
        }
    }
    return .none;
}

/// Locates the initializer CST subtree immediately following the top-level `=` token in `item_cst_node`.
fn findConstInitCst(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
) CstNodeIndex {
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) return .none;
    const root_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        root_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = root_idx + 1;
    while (cursor < end_idx) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        const step_size: usize = @max(@as(usize, node.subtree_size), 1);
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (is_leaf and !node.flags.is_missing_or_injected and
            !node.token.isNone() and node.token.asInt() < token_buffer.countTokens() and
            token_buffer.getToken(node.token).kind == .eq)
        {
            const init_idx = cursor + 1;
            if (init_idx < end_idx) {
                const init_node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(init_idx)));
                const init_is_semi = init_node.subtree_size <= 1 and !init_node.token.isNone() and
                    init_node.token.asInt() < token_buffer.countTokens() and
                    token_buffer.getToken(init_node.token).kind == .semi;
                if (!init_is_semi) {
                    return CstNodeIndex.fromInt(@intCast(init_idx));
                }
            }
            return .none;
        }
        cursor += step_size;
    }
    return .none;
}

/// Extracts the position-independent `ItemTree` from `parsed` for `file_id`.
fn extractItemTreeFromAst(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    parsed: *const ParsedCstArtifact,
) !ItemTree {
    var entries_list: std.ArrayList(ItemTreeEntry) = .empty;
    errdefer entries_list.deinit(allocator);

    if (parsed.ast_arena.countNodes() > 0 and !parsed.root_node.isNone()) {
        const root_ast = parsed.ast_arena.getNode(parsed.root_node);
        if (root_ast.lhs.tag == .extra and root_ast.rhs.tag == .extra and root_ast.rhs.payload > 0) {
            const raw_items = parsed.ast_arena.getExtraSlice(
                ExtraIndex.fromInt(root_ast.lhs.payload),
                root_ast.rhs.payload,
            );
            for (raw_items) |raw_node_idx| {
                if (entries_list.items.len >= MAX_ITEMS_PER_FILE) break;
                const item_ast_node = NodeIndex.fromInt(raw_node_idx);
                if (item_ast_node.asInt() >= parsed.ast_arena.countNodes()) continue;

                const ast_node = parsed.ast_arena.getNode(item_ast_node);
                const item_kind = astTagToItemKind(ast_node.tag) orelse continue;
                var item_cst_node = parsed.ast_arena.getCstOrigin(item_ast_node);

                var body_ast_node: NodeIndex = .none;
                var body_cst_node: CstNodeIndex = .none;
                if (item_kind == .fn_decl) {
                    if (ast_node.rhs.tag == .node) {
                        body_ast_node = NodeIndex.fromInt(ast_node.rhs.payload);
                        if (body_ast_node.asInt() < parsed.ast_arena.countNodes()) {
                            body_cst_node = parsed.ast_arena.getCstOrigin(body_ast_node);
                        }
                    }
                    if (body_cst_node.isNone()) {
                        body_cst_node = findDirectBodyBlockCst(&parsed.cst_arena, item_cst_node);
                    }
                } else if (item_kind == .const_decl) {
                    if (ast_node.rhs.tag == .node) {
                        body_ast_node = NodeIndex.fromInt(ast_node.rhs.payload);
                    }
                    body_cst_node = findConstInitCst(
                        &parsed.token_buffer,
                        &parsed.cst_arena,
                        item_cst_node,
                    );
                    if (body_cst_node.isNone() and !body_ast_node.isNone() and
                        body_ast_node.asInt() < parsed.ast_arena.countNodes())
                    {
                        body_cst_node = parsed.ast_arena.getCstOrigin(body_ast_node);
                    }
                } else if (item_kind == .extern_block) {
                    body_ast_node = item_ast_node;
                    body_cst_node = item_cst_node;
                    if (!item_cst_node.isNone() and item_cst_node.asInt() >= 2) {
                        const parent_cand = CstNodeIndex.fromInt(item_cst_node.asInt() - 2);
                        const parent_rec = parsed.cst_arena.getNode(parent_cand);
                        if (parent_rec.kind == .block and
                            parent_cand.asInt() + parent_rec.subtree_size >=
                                item_cst_node.asInt() + parsed.cst_arena.getNode(item_cst_node).subtree_size)
                        {
                            item_cst_node = parent_cand;
                        }
                    }
                }

                const raw_name = extractItemNameSlice(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    item_kind,
                    ast_node.main_token,
                    item_cst_node,
                );
                const name_symbol = try interner.intern(raw_name);
                const interned_name = interner.get(name_symbol);
                const is_pub = extractItemIsPub(&parsed.cst_arena, item_cst_node, ast_node.main_token);

                const sig_fp = computeItemSignatureFingerprint(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    item_cst_node,
                    body_cst_node,
                );
                const body_fp = computeItemBodyFingerprint(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    item_cst_node,
                    body_cst_node,
                );

                const def_id = DefId.init(file_id, @intCast(entries_list.items.len));
                try entries_list.append(allocator, .{
                    .def_id = def_id,
                    .kind = item_kind,
                    .is_pub = is_pub,
                    .name_symbol = name_symbol,
                    .name_text = interned_name,
                    .ast_node = item_ast_node,
                    .cst_node = item_cst_node,
                    .body_ast_node = body_ast_node,
                    .body_cst_node = body_cst_node,
                    .signature_fingerprint = sig_fp,
                    .body_fingerprint = body_fp,
                });
            }
        }
    }

    var sig_tree_hasher = StructuralHasher.init();
    sig_tree_hasher.updateU32(file_id.asInt());
    sig_tree_hasher.updateU32(@intCast(entries_list.items.len));
    for (entries_list.items) |entry| {
        sig_tree_hasher.updateU32(entry.def_id.asInt());
        sig_tree_hasher.updateU8(@intFromEnum(entry.kind));
        sig_tree_hasher.updateU8(if (entry.is_pub) 1 else 0);
        sig_tree_hasher.updateU32(entry.name_symbol.asInt());
        sig_tree_hasher.updateFingerprint(entry.signature_fingerprint);
    }
    const tree_fp = sig_tree_hasher.final();

    var combined_hasher = StructuralHasher.init();
    combined_hasher.updateFingerprint(tree_fp);
    for (entries_list.items) |entry| {
        combined_hasher.updateFingerprint(entry.body_fingerprint);
    }

    return .{
        .entries = try entries_list.toOwnedSlice(allocator),
        .file_id = file_id,
        .tree_fingerprint = tree_fp,
        .combined_fingerprint = combined_hasher.final(),
        .source_ast_fingerprint = parsed.ast_fingerprint,
    };
}

comptime {
    std.debug.assert(@sizeOf(Revision) == 4);
    std.debug.assert(@sizeOf(Durability) == 1);
    std.debug.assert(@sizeOf(Fingerprint128) == 16);
    std.debug.assert(@alignOf(Fingerprint128) == 8);
    std.debug.assert(@sizeOf(DefId) == 4);
    std.debug.assert(@sizeOf(QueryStage) == 1);
    std.debug.assert(@sizeOf(QueryKey) == 8);
    std.debug.assert(@alignOf(QueryKey) == 4);
    std.debug.assert(@sizeOf(MemoHeader) == 40);
    std.debug.assert(@alignOf(MemoHeader) == 8);
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Demand-driven incremental query database (`DR-12` Section 3) with Early Cutoff and Durability.
pub const CompilerDb = struct {
    /// Backing allocator for query memo tables, dependency edges, and stage artifacts.
    allocator: std.mem.Allocator,
    /// Shared string interner for item symbol names and diagnostic autofixes.
    interner: StringInterner,
    /// Monotonically increasing database revision clock.
    current_revision: Revision = .initial,
    /// Latest `Revision` that mutated any input at or above each `Durability` tier (`0..2`).
    last_changed_by_durability: [DURABILITY_COUNT]Revision = .{ .initial, .initial, .initial },
    /// Cooperative cancellation flag checked before query evaluation and verification steps.
    is_cancelled: std.atomic.Value(bool) = std.atomic.Value(bool).init(false),
    /// Monotonic cancellation counter bumped whenever `requestCancellation` is called.
    cancellation_epoch: std.atomic.Value(u32) = std.atomic.Value(u32).init(0),
    /// Flat memo table mapping `QueryKey.asU64()` to its 40-byte `MemoHeader` value.
    memos: std.AutoHashMapUnmanaged(u64, MemoHeader) = .empty,
    /// Contiguous storage of committed `QueryKey` dependency slices indexed by `MemoHeader.dep_edge_start`.
    dep_edges: std.ArrayList(QueryKey) = .empty,
    /// Scratch buffer accumulating dependency edges for frames currently on `active_stack`.
    scratch_dep_edges: std.ArrayList(QueryKey) = .empty,
    /// Active query execution stack used for automatic dependency recording.
    active_stack: std.ArrayList(ActiveQueryFrame) = .empty,
    /// O(1) hash set of `QueryKey.asU64()` currently executing on `active_stack` for cycle detection.
    in_flight_keys: std.AutoHashMapUnmanaged(u64, void) = .empty,
    /// Stage 0 source inputs keyed by `FileId.asInt()`.
    source_inputs: std.AutoHashMapUnmanaged(u32, SourceInput) = .empty,
    /// Stage 1 parsed CST/AST artifacts keyed by `FileId.asInt()`.
    parsed_artifacts: std.AutoHashMapUnmanaged(u32, ParsedCstArtifact) = .empty,
    /// Stage 2 lowered AST summary artifacts keyed by `FileId.asInt()`.
    lowered_artifacts: std.AutoHashMapUnmanaged(u32, LoweredAstArtifact) = .empty,
    /// Stage 3 position-independent `ItemTree`s keyed by `FileId.asInt()`.
    item_trees: std.AutoHashMapUnmanaged(u32, ItemTree) = .empty,
    /// Stage 5 relative `BodyAstWindow` projections keyed by `DefId.asInt()`.
    body_windows: std.AutoHashMapUnmanaged(u32, BodyAstWindow) = .empty,
    /// Stage 6 resolved module signature summaries keyed by `FileId.asInt()`.
    resolved_signatures: std.AutoHashMapUnmanaged(u32, ResolvedSignaturesArtifact) = .empty,
    /// Stage 7 fine-grained definition signatures keyed by `DefId.asInt()`.
    def_signatures: std.AutoHashMapUnmanaged(u32, DefSignatureArtifact) = .empty,
    /// Stage 8 per-definition typed body artifacts keyed by `DefId.asInt()`.
    typed_bodies: std.AutoHashMapUnmanaged(u32, TypedBodyArtifact) = .empty,
    /// Stage 9 per-definition SAST verification artifacts keyed by `DefId.asInt()`.
    sast_results: std.AutoHashMapUnmanaged(u32, SastVerificationArtifact) = .empty,
    /// Optional hook for injecting synthetic dependency cycles in unit tests.
    custom_stage_hook: ?CustomStageHook = null,
    /// Execution, Green Path, Durability fast-path, and Early Cutoff counters.
    telemetry: QueryTelemetry = .{},

    /// Initializes a new `CompilerDb` instance bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) !CompilerDb {
        return .{
            .allocator = allocator,
            .interner = try StringInterner.init(allocator),
        };
    }

    /// Releases all owned source buffers, syntax arenas, item trees, and memo tables.
    pub fn deinit(self: *CompilerDb) void {
        var source_iter = self.source_inputs.valueIterator();
        while (source_iter.next()) |input_ptr| {
            self.allocator.free(input_ptr.owned_text);
        }
        self.source_inputs.deinit(self.allocator);

        var parsed_iter = self.parsed_artifacts.valueIterator();
        while (parsed_iter.next()) |parsed_ptr| {
            parsed_ptr.deinit();
        }
        self.parsed_artifacts.deinit(self.allocator);

        var tree_iter = self.item_trees.valueIterator();
        while (tree_iter.next()) |tree_ptr| {
            tree_ptr.deinit(self.allocator);
        }
        self.item_trees.deinit(self.allocator);

        self.lowered_artifacts.deinit(self.allocator);
        self.body_windows.deinit(self.allocator);
        self.resolved_signatures.deinit(self.allocator);
        self.def_signatures.deinit(self.allocator);
        self.typed_bodies.deinit(self.allocator);
        self.sast_results.deinit(self.allocator);
        self.memos.deinit(self.allocator);
        self.dep_edges.deinit(self.allocator);
        self.scratch_dep_edges.deinit(self.allocator);
        self.active_stack.deinit(self.allocator);
        self.in_flight_keys.deinit(self.allocator);
        self.interner.deinit();
        self.* = undefined;
    }

    // ------------ Cancellation & Hook Control Methods -------------

    /// Signals cooperative cancellation so in-flight queries unwind with `error.Cancelled`.
    pub inline fn requestCancellation(self: *CompilerDb) void {
        _ = self.cancellation_epoch.fetchAdd(1, .seq_cst);
        self.is_cancelled.store(true, .release);
    }

    /// Clears the cooperative cancellation flag so subsequent queries can execute.
    pub inline fn clearCancellation(self: *CompilerDb) void {
        self.is_cancelled.store(false, .release);
    }

    /// Returns `true` if cooperative cancellation is currently active.
    pub inline fn isCancelled(self: *const CompilerDb) bool {
        return self.is_cancelled.load(.acquire);
    }

    /// Returns `error.Cancelled` if cooperative cancellation has been requested (`DR-12` Section 3.3).
    pub inline fn unwindIfCancelled(self: *const CompilerDb) QueryError!void {
        if (self.isCancelled()) return error.Cancelled;
    }

    /// Installs or clears an optional `CustomStageHook` for deterministic cycle testing.
    pub inline fn setCustomStageHook(self: *CompilerDb, hook: ?CustomStageHook) void {
        self.custom_stage_hook = hook;
    }

    /// Inspects the cached `MemoHeader` for `key` by value without triggering execution.
    pub inline fn getMemoHeader(self: *const CompilerDb, key: QueryKey) ?MemoHeader {
        return self.memos.get(key.asU64());
    }

    // ------------ Stage 0 Input Mutation (`setInput`) -------------

    /// Inserts or updates the source text and `durability` of `file_id`, bumping `current_revision` on change.
    pub fn setInput(
        self: *CompilerDb,
        file_id: FileId,
        source_text: []const u8,
        durability: Durability,
    ) !Revision {
        const new_fp = Fingerprint128.hashBytes(source_text);
        const key = QueryKey.forFile(.source_text, file_id);

        if (self.source_inputs.getPtr(file_id.asInt())) |existing_input| {
            // [1] Same-content and same-durability fast path; no revision bump:
            if (Fingerprint128.eql(existing_input.content_fingerprint, new_fp) and
                existing_input.durability == durability)
            {
                return self.current_revision;
            }

            const old_durability = existing_input.durability;
            const is_content_same = Fingerprint128.eql(existing_input.content_fingerprint, new_fp);
            if (!is_content_same) {
                const cloned_text = try self.allocator.dupe(u8, source_text);
                self.allocator.free(existing_input.owned_text);
                existing_input.owned_text = cloned_text;
                existing_input.content_fingerprint = new_fp;
            }

            self.current_revision = self.current_revision.next();
            const max_affected_tier: usize = @max(@intFromEnum(old_durability), @intFromEnum(durability));
            var tier_idx: usize = 0;
            while (tier_idx <= max_affected_tier) : (tier_idx += 1) {
                self.last_changed_by_durability[tier_idx] = self.current_revision;
            }

            existing_input.durability = durability;
            if (!is_content_same) {
                existing_input.changed_at = self.current_revision;
            }

            try self.memos.put(self.allocator, key.asU64(), .{
                .output_fingerprint = new_fp,
                .verified_at = self.current_revision,
                .changed_at = existing_input.changed_at,
                .dep_edge_start = 0,
                .dep_edge_len = 0,
                .min_durability = durability,
                .is_pure_high_durability = (durability == .high),
                .artifact_index = file_id.asInt(),
            });
            return self.current_revision;
        }

        // [2] New file registration:
        const cloned_text = try self.allocator.dupe(u8, source_text);
        errdefer self.allocator.free(cloned_text);

        if (self.source_inputs.count() > 0) {
            self.current_revision = self.current_revision.next();
        }
        var tier_idx: usize = 0;
        while (tier_idx <= @intFromEnum(durability)) : (tier_idx += 1) {
            self.last_changed_by_durability[tier_idx] = self.current_revision;
        }

        try self.source_inputs.put(self.allocator, file_id.asInt(), .{
            .owned_text = cloned_text,
            .content_fingerprint = new_fp,
            .durability = durability,
            .changed_at = self.current_revision,
        });

        try self.memos.put(self.allocator, key.asU64(), .{
            .output_fingerprint = new_fp,
            .verified_at = self.current_revision,
            .changed_at = self.current_revision,
            .dep_edge_start = 0,
            .dep_edge_len = 0,
            .min_durability = durability,
            .is_pure_high_durability = (durability == .high),
            .artifact_index = file_id.asInt(),
        });
        return self.current_revision;
    }

    // ---------- Public 10-Stage Demand-Driven Query API -----------

    /// Stage 0: Fetches the immutable UTF-8 source text for `file_id`, recording a `.source_text` edge.
    pub fn getSourceText(self: *CompilerDb, file_id: FileId) QueryError![]const u8 {
        _ = try self.fetchQuery(QueryKey.forFile(.source_text, file_id));
        const input_ptr = self.source_inputs.getPtr(file_id.asInt()) orelse return error.MissingSourceInput;
        return input_ptr.owned_text;
    }

    /// Stage 1: Tokenizes and parses `file_id` into a lossless CST and AST arena.
    pub fn parseCst(self: *CompilerDb, file_id: FileId) QueryError!*const ParsedCstArtifact {
        _ = try self.fetchQuery(QueryKey.forFile(.parse_cst, file_id));
        return self.parsed_artifacts.getPtr(file_id.asInt()) orelse error.MissingSourceInput;
    }

    /// Stage 2: Lowers `file_id` to a trivia-stripped `LoweredAstArtifact` with comment/whitespace Early Cutoff.
    pub fn lowerAst(self: *CompilerDb, file_id: FileId) QueryError!LoweredAstArtifact {
        _ = try self.fetchQuery(QueryKey.forFile(.lower_ast, file_id));
        return self.lowered_artifacts.get(file_id.asInt()) orelse error.MissingSourceInput;
    }

    /// Stage 3: Extracts the position-independent `ItemTree` for `file_id`.
    pub fn extractItemTree(self: *CompilerDb, file_id: FileId) QueryError!*const ItemTree {
        _ = try self.fetchQuery(QueryKey.forFile(.item_tree, file_id));
        return self.item_trees.getPtr(file_id.asInt()) orelse error.MissingSourceInput;
    }

    /// Stage 4: Projects the position-independent 128-bit `signature_fingerprint` for `def_id`.
    pub fn getItemTreeSigProj(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        return (try self.fetchQuery(QueryKey.forDef(.item_tree_sig_proj, def_id))).output_fingerprint;
    }

    /// Stage 5: Projects the position-independent `BodyAstWindow` and `body_fingerprint` for `def_id`.
    pub fn getBodyAstProj(self: *CompilerDb, def_id: DefId) QueryError!BodyAstWindow {
        _ = try self.fetchQuery(QueryKey.forDef(.body_ast_proj, def_id));
        return self.body_windows.get(def_id.asInt()) orelse error.InvalidDefId;
    }

    /// Stage 6: Resolves module-level signatures for `file_id`, shielded by `ItemTree.tree_fingerprint`.
    pub fn resolveSignatures(self: *CompilerDb, file_id: FileId) QueryError!ResolvedSignaturesArtifact {
        _ = try self.fetchQuery(QueryKey.forFile(.resolve_signatures, file_id));
        return self.resolved_signatures.get(file_id.asInt()) orelse error.MissingSourceInput;
    }

    /// Stage 7: Fetches the fine-grained `DefSignatureArtifact` for `def_id`.
    pub fn getDefSignature(self: *CompilerDb, def_id: DefId) QueryError!DefSignatureArtifact {
        _ = try self.fetchQuery(QueryKey.forDef(.def_signature, def_id));
        return self.def_signatures.get(def_id.asInt()) orelse error.InvalidDefId;
    }

    /// Stage 8: Type-checks the body of `def_id` in isolation using `.def_signature` and `.body_ast_proj`.
    pub fn typecheckBody(self: *CompilerDb, def_id: DefId) QueryError!TypedBodyArtifact {
        _ = try self.fetchQuery(QueryKey.forDef(.typecheck_body, def_id));
        return self.typed_bodies.get(def_id.asInt()) orelse error.InvalidDefId;
    }

    /// Stage 9: Runs MIR SAST memory and exclusivity verification on `def_id`.
    pub fn verifySastMir(self: *CompilerDb, def_id: DefId) QueryError!SastVerificationArtifact {
        _ = try self.fetchQuery(QueryKey.forDef(.verify_sast_mir, def_id));
        return self.sast_results.get(def_id.asInt()) orelse error.InvalidDefId;
    }

    // -------- Core Salsa Verification & Backdating Engine ---------

    /// Fetches or computes `key`, recording dependency edges and propagating durability to the active caller.
    pub fn fetchQuery(self: *CompilerDb, key: QueryKey) QueryError!MemoHeader {
        try self.unwindIfCancelled();

        // [1] Record `key` as a direct dependency of the enclosing active query frame:
        if (self.active_stack.items.len > 0) {
            try self.recordDependencyEdge(key);
        }

        // [2] Reject dependency cycles immediately if `key` is already on `active_stack`:
        if (self.in_flight_keys.contains(key.asU64())) {
            return error.DependencyCycle;
        }

        // [3] Check existing memo by value (never holding a pointer across recursive calls):
        if (self.memos.get(key.asU64())) |existing_memo| {
            if (existing_memo.verified_at == self.current_revision) {
                self.propagateToParent(existing_memo);
                return existing_memo;
            }

            _ = try self.maybeChangedAfter(key, existing_memo.verified_at);
            const verified_memo = self.memos.get(key.asU64()).?;
            self.propagateToParent(verified_memo);
            return verified_memo;
        }

        // [4] First execution of `key`:
        const computed_memo = try self.executeAndBackdate(key);
        self.propagateToParent(computed_memo);
        return computed_memo;
    }

    /// Verifies whether `key`'s output changed after `after_revision`, re-executing stale nodes when needed.
    pub fn maybeChangedAfter(
        self: *CompilerDb,
        key: QueryKey,
        after_revision: Revision,
    ) QueryError!bool {
        try self.unwindIfCancelled();

        if (self.in_flight_keys.contains(key.asU64())) {
            return error.DependencyCycle;
        }

        const memo_snapshot = self.memos.get(key.asU64()) orelse {
            _ = try self.executeAndBackdate(key);
            return true;
        };

        // [1] Input queries (`.source_text`) are always verified at `current_revision`:
        if (key.stage == .source_text) {
            if (memo_snapshot.verified_at != self.current_revision) {
                if (self.memos.getPtr(key.asU64())) |memo_ptr| {
                    memo_ptr.verified_at = self.current_revision;
                }
            }
            return memo_snapshot.changed_at.isAfter(after_revision);
        }

        // [2] Already verified in `current_revision`:
        const last_verified = memo_snapshot.verified_at;
        if (last_verified == self.current_revision) {
            return memo_snapshot.changed_at.isAfter(after_revision);
        }

        // [3] Durability Fast-Path: if no input at `>= memo_snapshot.min_durability` changed since `last_verified`:
        var has_durability_change = false;
        var tier_idx: usize = @intFromEnum(memo_snapshot.min_durability);
        while (tier_idx < DURABILITY_COUNT) : (tier_idx += 1) {
            if (self.last_changed_by_durability[tier_idx].isAfter(last_verified)) {
                has_durability_change = true;
                break;
            }
        }
        if (!has_durability_change) {
            if (self.memos.getPtr(key.asU64())) |memo_ptr| {
                memo_ptr.verified_at = self.current_revision;
            }
            self.telemetry.durability_fast_path_hits += 1;
            self.telemetry.green_hits += 1;
            return memo_snapshot.changed_at.isAfter(after_revision);
        }

        // [4] Walk dependency edges by integer index (never holding a slice across recursive calls):
        const edge_start: usize = memo_snapshot.dep_edge_start;
        const edge_count: usize = memo_snapshot.dep_edge_len;
        var recomputed_min_dur: Durability = .high;
        var recomputed_pure_high: bool = true;
        var has_changed_dep = false;

        var i: usize = 0;
        while (i < edge_count) : (i += 1) {
            const dep_key = self.dep_edges.items[edge_start + i];
            if (try self.maybeChangedAfter(dep_key, last_verified)) {
                has_changed_dep = true;
                break;
            }
            if (self.memos.get(dep_key.asU64())) |dep_memo| {
                recomputed_min_dur = Durability.minTier(recomputed_min_dur, dep_memo.min_durability);
                if (!dep_memo.is_pure_high_durability) {
                    recomputed_pure_high = false;
                }
            }
        }

        // [5] Red Path: a dependency changed after `last_verified`, so re-execute and check Early Cutoff:
        if (has_changed_dep) {
            const updated_memo = try self.executeAndBackdate(key);
            return updated_memo.changed_at.isAfter(after_revision);
        }

        // [6] Green Path: all dependencies verified unchanged; re-fetch `memo_ptr` and update metadata:
        if (self.memos.getPtr(key.asU64())) |memo_ptr| {
            memo_ptr.min_durability = recomputed_min_dur;
            memo_ptr.is_pure_high_durability = recomputed_pure_high;
            memo_ptr.verified_at = self.current_revision;
        }
        self.telemetry.green_hits += 1;
        return memo_snapshot.changed_at.isAfter(after_revision);
    }

    /// Executes `key`, commits its recorded dependency edges, and backdates `changed_at` on Early Cutoff.
    fn executeAndBackdate(self: *CompilerDb, key: QueryKey) QueryError!MemoHeader {
        try self.unwindIfCancelled();

        if (key.stage == .source_text) {
            const file_id = FileId.fromInt(key.entity_index);
            const input = self.source_inputs.get(file_id.asInt()) orelse return error.MissingSourceInput;
            const input_memo = MemoHeader{
                .output_fingerprint = input.content_fingerprint,
                .verified_at = self.current_revision,
                .changed_at = input.changed_at,
                .dep_edge_start = 0,
                .dep_edge_len = 0,
                .min_durability = input.durability,
                .is_pure_high_durability = (input.durability == .high),
                .artifact_index = file_id.asInt(),
            };
            try self.memos.put(self.allocator, key.asU64(), input_memo);
            return input_memo;
        }

        if (self.in_flight_keys.contains(key.asU64())) {
            return error.DependencyCycle;
        }
        try self.in_flight_keys.put(self.allocator, key.asU64(), {});
        defer _ = self.in_flight_keys.remove(key.asU64());

        const start_dep_index = self.scratch_dep_edges.items.len;
        try self.active_stack.append(self.allocator, .{
            .key = key,
            .start_dep_index = start_dep_index,
            .min_durability = .high,
            .is_pure_high_durability = true,
            .max_dep_changed_at = .initial,
        });
        defer {
            _ = self.active_stack.pop();
            self.scratch_dep_edges.shrinkRetainingCapacity(start_dep_index);
        }

        const old_memo_opt = self.memos.get(key.asU64());
        self.telemetry.stage_executions[@intFromEnum(key.stage)] += 1;

        if (self.custom_stage_hook) |hook_fn| {
            try hook_fn(self, key);
        }

        const computed_fp = try self.computeStage(key);
        const frame = self.active_stack.items[self.active_stack.items.len - 1];
        const recorded_slice = self.scratch_dep_edges.items[start_dep_index..];
        const clamped_len: u16 = @intCast(@min(recorded_slice.len, MAX_DEPS_PER_MEMO));

        // Reuse existing `dep_edge_start` slice if capacity suffices; otherwise extend or append to `dep_edges`:
        var dep_edge_start: u32 = 0;
        if (old_memo_opt) |old_memo| {
            if (clamped_len <= old_memo.dep_edge_len and old_memo.dep_edge_len > 0) {
                dep_edge_start = old_memo.dep_edge_start;
                const dest_start: usize = dep_edge_start;
                @memcpy(
                    self.dep_edges.items[dest_start .. dest_start + clamped_len],
                    recorded_slice[0..clamped_len],
                );
            } else if (old_memo.dep_edge_len > 0 and
                @as(usize, old_memo.dep_edge_start) + old_memo.dep_edge_len == self.dep_edges.items.len)
            {
                dep_edge_start = old_memo.dep_edge_start;
                const dest_start: usize = dep_edge_start;
                @memcpy(
                    self.dep_edges.items[dest_start .. dest_start + old_memo.dep_edge_len],
                    recorded_slice[0..old_memo.dep_edge_len],
                );
                try self.dep_edges.appendSlice(
                    self.allocator,
                    recorded_slice[old_memo.dep_edge_len..clamped_len],
                );
            } else if (clamped_len > 0) {
                dep_edge_start = @intCast(self.dep_edges.items.len);
                try self.dep_edges.appendSlice(self.allocator, recorded_slice[0..clamped_len]);
            }
        } else if (clamped_len > 0) {
            dep_edge_start = @intCast(self.dep_edges.items.len);
            try self.dep_edges.appendSlice(self.allocator, recorded_slice[0..clamped_len]);
        }

        // Early Cutoff (Backdating): preserve `old_memo.changed_at` when `computed_fp` is unchanged:
        var changed_at = self.current_revision;
        if (old_memo_opt) |old_memo| {
            if (Fingerprint128.eql(old_memo.output_fingerprint, computed_fp)) {
                changed_at = old_memo.changed_at;
                self.telemetry.early_cutoff_hits += 1;
            }
        }

        const new_memo = MemoHeader{
            .output_fingerprint = computed_fp,
            .verified_at = self.current_revision,
            .changed_at = changed_at,
            .dep_edge_start = dep_edge_start,
            .dep_edge_len = clamped_len,
            .min_durability = frame.min_durability,
            .is_pure_high_durability = frame.is_pure_high_durability,
            .artifact_index = key.entity_index,
        };
        try self.memos.put(self.allocator, key.asU64(), new_memo);
        return new_memo;
    }

    /// Appends `dep_key` to the active frame's scratch dependency list if not already recorded.
    fn recordDependencyEdge(self: *CompilerDb, dep_key: QueryKey) !void {
        const frame = &self.active_stack.items[self.active_stack.items.len - 1];
        for (self.scratch_dep_edges.items[frame.start_dep_index..]) |existing_dep| {
            if (existing_dep.asU64() == dep_key.asU64()) return;
        }
        try self.scratch_dep_edges.append(self.allocator, dep_key);
    }

    /// Propagates `child_memo`'s durability and `changed_at` revision into the parent `ActiveQueryFrame`.
    inline fn propagateToParent(self: *CompilerDb, child_memo: MemoHeader) void {
        if (self.active_stack.items.len == 0) return;
        var parent_frame = &self.active_stack.items[self.active_stack.items.len - 1];
        parent_frame.min_durability = Durability.minTier(
            parent_frame.min_durability,
            child_memo.min_durability,
        );
        if (!child_memo.is_pure_high_durability) {
            parent_frame.is_pure_high_durability = false;
        }
        if (child_memo.changed_at.isAfter(parent_frame.max_dep_changed_at)) {
            parent_frame.max_dep_changed_at = child_memo.changed_at;
        }
    }

    // ------------- Stage Compute Dispatch & Builders --------------

    /// Dispatches `key` to its concrete stage computation routine and returns the new `Fingerprint128`.
    fn computeStage(self: *CompilerDb, key: QueryKey) QueryError!Fingerprint128 {
        return switch (key.stage) {
            .source_text => blk: {
                const input = self.source_inputs.get(key.entity_index) orelse return error.MissingSourceInput;
                break :blk input.content_fingerprint;
            },
            .parse_cst => self.computeParseCst(FileId.fromInt(key.entity_index)),
            .lower_ast => self.computeLowerAst(FileId.fromInt(key.entity_index)),
            .item_tree => self.computeItemTree(FileId.fromInt(key.entity_index)),
            .item_tree_sig_proj => self.computeItemTreeSigProj(DefId.fromInt(key.entity_index)),
            .body_ast_proj => self.computeBodyAstProj(DefId.fromInt(key.entity_index)),
            .resolve_signatures => self.computeResolveSignatures(FileId.fromInt(key.entity_index)),
            .def_signature => self.computeDefSignature(DefId.fromInt(key.entity_index)),
            .typecheck_body => self.computeTypecheckBody(DefId.fromInt(key.entity_index)),
            .verify_sast_mir => self.computeVerifySastMir(DefId.fromInt(key.entity_index)),
        };
    }

    /// Stage 1 implementation: tokenizes and parses `file_id` into `parsed_artifacts`.
    fn computeParseCst(self: *CompilerDb, file_id: FileId) QueryError!Fingerprint128 {
        const source = try self.getSourceText(file_id);
        try self.unwindIfCancelled();

        const gop = try self.parsed_artifacts.getOrPut(self.allocator, file_id.asInt());
        if (!gop.found_existing) {
            gop.value_ptr.* = ParsedCstArtifact.init(self.allocator);
        } else {
            gop.value_ptr.resetForReparse();
        }
        errdefer if (!gop.found_existing) {
            gop.value_ptr.deinit();
            _ = self.parsed_artifacts.remove(file_id.asInt());
        };

        const parsed_ptr = gop.value_ptr;
        const root_node = parser.parseSource(
            source,
            file_id,
            &parsed_ptr.token_buffer,
            &parsed_ptr.cst_arena,
            &parsed_ptr.ast_arena,
            &parsed_ptr.diagnostics,
            &self.interner,
        ) catch return error.OutOfMemory;

        parsed_ptr.root_node = root_node;
        parsed_ptr.has_parse_errors = parsed_ptr.cst_arena.has_parse_errors or
            parsed_ptr.diagnostics.hasErrors();
        parsed_ptr.cst_fingerprint = computeCstFingerprint(
            source,
            &parsed_ptr.token_buffer,
            &parsed_ptr.cst_arena,
        );
        parsed_ptr.ast_fingerprint = computeAstFingerprint(
            source,
            &parsed_ptr.token_buffer,
            &parsed_ptr.cst_arena,
            &parsed_ptr.ast_arena,
        );
        return parsed_ptr.cst_fingerprint;
    }

    /// Stage 2 implementation: builds `LoweredAstArtifact` with trivia-stripped `ast_fingerprint`.
    fn computeLowerAst(self: *CompilerDb, file_id: FileId) QueryError!Fingerprint128 {
        const parsed = try self.parseCst(file_id);
        try self.unwindIfCancelled();

        const artifact = LoweredAstArtifact{
            .file_id = file_id,
            .root_node = parsed.root_node,
            .node_count = @intCast(parsed.ast_arena.countNodes()),
            .has_parse_errors = parsed.has_parse_errors,
            .ast_fingerprint = parsed.ast_fingerprint,
        };
        try self.lowered_artifacts.put(self.allocator, file_id.asInt(), artifact);
        return artifact.ast_fingerprint;
    }

    /// Ensures `self.item_trees` holds an `ItemTree` matching `lowered.ast_fingerprint` for `file_id`.
    fn ensureFreshItemTree(
        self: *CompilerDb,
        file_id: FileId,
        lowered: LoweredAstArtifact,
    ) QueryError!*const ItemTree {
        if (self.item_trees.getPtr(file_id.asInt())) |existing_tree| {
            if (Fingerprint128.eql(existing_tree.source_ast_fingerprint, lowered.ast_fingerprint)) {
                return existing_tree;
            }
        }

        const input_ptr = self.source_inputs.getPtr(file_id.asInt()) orelse return error.MissingSourceInput;
        const parsed_ptr = self.parsed_artifacts.getPtr(file_id.asInt()) orelse return error.MissingSourceInput;
        const new_tree = try extractItemTreeFromAst(
            self.allocator,
            &self.interner,
            file_id,
            input_ptr.owned_text,
            parsed_ptr,
        );
        if (self.item_trees.fetchRemove(file_id.asInt())) |old_kv| {
            var old_tree = old_kv.value;
            old_tree.deinit(self.allocator);
        }
        try self.item_trees.put(self.allocator, file_id.asInt(), new_tree);
        return self.item_trees.getPtr(file_id.asInt()).?;
    }

    /// Stage 3 implementation: extracts `ItemTree` for `file_id` (depending on `.lower_ast`).
    fn computeItemTree(self: *CompilerDb, file_id: FileId) QueryError!Fingerprint128 {
        const lowered = try self.lowerAst(file_id);
        try self.unwindIfCancelled();
        const tree_ptr = try self.ensureFreshItemTree(file_id, lowered);
        return tree_ptr.combined_fingerprint;
    }

    /// Stage 4 implementation: projects `entry.signature_fingerprint` for `def_id` (depending on `.item_tree`).
    fn computeItemTreeSigProj(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const item_tree = try self.extractItemTree(def_id.fileId());
        const entry = item_tree.getEntry(def_id) orelse return error.InvalidDefId;
        return entry.signature_fingerprint;
    }

    /// Stage 5 implementation: projects `BodyAstWindow` for `def_id` (depending on `.lower_ast`).
    fn computeBodyAstProj(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const file_id = def_id.fileId();
        const lowered = try self.lowerAst(file_id);
        try self.unwindIfCancelled();

        const item_tree = try self.ensureFreshItemTree(file_id, lowered);
        const entry = item_tree.getEntry(def_id) orelse return error.InvalidDefId;
        const window = BodyAstWindow{
            .def_id = def_id,
            .file_id = file_id,
            .item_ast_node = entry.ast_node,
            .body_ast_node = entry.body_ast_node,
            .body_cst_node = entry.body_cst_node,
            .body_fingerprint = entry.body_fingerprint,
        };
        try self.body_windows.put(self.allocator, def_id.asInt(), window);
        return window.body_fingerprint;
    }

    /// Stage 6 implementation: resolves module signatures for `file_id` (shielded by `tree_fingerprint`).
    fn computeResolveSignatures(self: *CompilerDb, file_id: FileId) QueryError!Fingerprint128 {
        const item_tree = try self.extractItemTree(file_id);
        try self.unwindIfCancelled();

        var hasher = StructuralHasher.init();
        hasher.updateU32(file_id.asInt());
        hasher.updateFingerprint(item_tree.tree_fingerprint);

        var public_count: u32 = 0;
        for (item_tree.entries) |entry| {
            const sig_fp = try self.getItemTreeSigProj(entry.def_id);
            hasher.updateFingerprint(sig_fp);
            if (entry.is_pub) public_count += 1;
        }

        const resolved_fp = hasher.final();
        try self.resolved_signatures.put(self.allocator, file_id.asInt(), .{
            .file_id = file_id,
            .item_count = @intCast(item_tree.entries.len),
            .public_item_count = public_count,
            .signatures_fingerprint = resolved_fp,
        });
        return resolved_fp;
    }

    /// Stage 7 implementation: computes `DefSignatureArtifact` for `def_id`.
    fn computeDefSignature(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const file_id = def_id.fileId();
        const item_sig_fp = try self.getItemTreeSigProj(def_id);
        _ = try self.resolveSignatures(file_id);
        try self.unwindIfCancelled();

        const item_tree = self.item_trees.getPtr(file_id.asInt()) orelse return error.MissingSourceInput;
        const entry = item_tree.getEntry(def_id) orelse return error.InvalidDefId;

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateU8(@intFromEnum(entry.kind));
        hasher.updateU8(if (entry.is_pub) 1 else 0);
        hasher.updateU32(entry.name_symbol.asInt());
        hasher.updateFingerprint(item_sig_fp);
        const def_sig_fp = hasher.final();

        try self.def_signatures.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .kind = entry.kind,
            .is_pub = entry.is_pub,
            .name_symbol = entry.name_symbol,
            .signature_fingerprint = def_sig_fp,
        });
        return def_sig_fp;
    }

    /// Stage 8 implementation: type-checks `def_id`'s body in isolation from sibling definitions.
    fn computeTypecheckBody(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const def_sig = try self.getDefSignature(def_id);
        const body_window = try self.getBodyAstProj(def_id);
        try self.unwindIfCancelled();

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateFingerprint(def_sig.signature_fingerprint);
        hasher.updateFingerprint(body_window.body_fingerprint);
        const typed_fp = hasher.final();

        try self.typed_bodies.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .file_id = def_id.fileId(),
            .body_ast_node = body_window.body_ast_node,
            .signature_fingerprint = def_sig.signature_fingerprint,
            .body_fingerprint = body_window.body_fingerprint,
            .typed_fingerprint = typed_fp,
        });
        return typed_fp;
    }

    /// Stage 9 implementation: runs SAST MIR verification on `def_id`'s typed body.
    fn computeVerifySastMir(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const typed_body = try self.typecheckBody(def_id);
        try self.unwindIfCancelled();

        const file_id = def_id.fileId();
        const has_errors = if (self.parsed_artifacts.getPtr(file_id.asInt())) |parsed_ptr|
            parsed_ptr.has_parse_errors
        else
            false;

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateU8(if (has_errors) 0 else 1);
        hasher.updateFingerprint(typed_body.typed_fingerprint);
        const sast_fp = hasher.final();

        try self.sast_results.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .file_id = file_id,
            .is_verified_sound = !has_errors,
            .sast_fingerprint = sast_fp,
        });
        return sast_fp;
    }
};

// ---------------------------------------- MAIN -----------------------------------------

// ------------------- Fingerprinting & Keys --------------------

test "test_fingerprint128_wyhash_blake3_and_structural_hasher" {
    const sample_a = "pub fn add(a: i32, b: i32) -> i32 { return a + b; }";
    const sample_b = "pub fn add(a: i32, b: i32) -> i32 { return a - b; }";

    const wy_a1 = Fingerprint128.hashBytes(sample_a);
    const wy_a2 = Fingerprint128.hashBytes(sample_a);
    const wy_b = Fingerprint128.hashBytes(sample_b);
    try std.testing.expect(Fingerprint128.eql(wy_a1, wy_a2));
    try std.testing.expect(!Fingerprint128.eql(wy_a1, wy_b));
    try std.testing.expect(!Fingerprint128.eql(wy_a1, Fingerprint128.ZERO));

    const b3_a1 = Fingerprint128.hashBlake3(sample_a);
    const b3_a2 = Fingerprint128.hashBlake3(sample_a);
    const b3_b = Fingerprint128.hashBlake3(sample_b);
    try std.testing.expect(Fingerprint128.eql(b3_a1, b3_a2));
    try std.testing.expect(!Fingerprint128.eql(b3_a1, b3_b));

    var hasher_one = StructuralHasher.init();
    hasher_one.updateU8(1);
    hasher_one.updateU16(258);
    hasher_one.updateU32(999);
    hasher_one.updateU64(123_456_789);
    hasher_one.updateBytes("corex");
    hasher_one.updateFingerprint(wy_a1);

    var hasher_two = StructuralHasher.init();
    hasher_two.updateU8(1);
    hasher_two.updateU16(258);
    hasher_two.updateU32(999);
    hasher_two.updateU64(123_456_789);
    hasher_two.updateBytes("corex");
    hasher_two.updateFingerprint(wy_a2);

    try std.testing.expect(Fingerprint128.eql(hasher_one.final(), hasher_two.final()));

    const file_id = FileId.fromInt(42);
    const def_id = DefId.init(file_id, 7);
    try std.testing.expect(!def_id.isNone());
    try std.testing.expect(DefId.NONE.isNone());
    try std.testing.expectEqual(file_id, def_id.fileId());
    try std.testing.expectEqual(@as(u12, 7), def_id.itemIndex());
    try std.testing.expectEqual(def_id, DefId.fromInt(def_id.asInt()));
}

// --------------- Input Mutations & Early Cutoff ---------------

test "test_set_input_noop_durability_upgrade_and_comment_early_cutoff" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(1);
    const initial_src = "pub fn compute(val: i32) -> i32 {\n    return val + 1;\n}\n";

    // [1] Register initial source input at Revision 1:
    const rev1 = try db.setInput(file_id, initial_src, .low);
    try std.testing.expectEqual(Revision.initial, rev1);

    // [2] Identical source and durability is a no-op (stays at Revision 1):
    const rev_same = try db.setInput(file_id, initial_src, .low);
    try std.testing.expectEqual(rev1, rev_same);

    // [3] Evaluate `extractItemTree` at Revision 1:
    const tree_r1 = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 1), tree_r1.entries.len);
    try std.testing.expectEqualStrings("compute", tree_r1.entries[0].name_text);
    try std.testing.expect(tree_r1.entries[0].is_pub);
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.parse_cst));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.lower_ast));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.item_tree));

    // [4] Changing durability with identical content bumps Revision to 2, preserving `changed_at`:
    const rev2 = try db.setInput(file_id, initial_src, .medium);
    try std.testing.expect(rev2.isAfter(rev1));

    // [5] Editing comments and whitespace bumps Revision to 3, but triggers Early Cutoff at `lower_ast`:
    const commented_src =
        "// Header comment added\n/// Doc comment\npub fn compute(   val: i32 ) -> i32 {\n\n    // Inner comment\n    return val + 1;\n}\n";
    const rev3 = try db.setInput(file_id, commented_src, .medium);
    try std.testing.expect(rev3.isAfter(rev2));

    const tree_r3 = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 1), tree_r3.entries.len);
    // `parse_cst` and `lower_ast` re-executed, `lower_ast` backdated `changed_at = R1`, so `item_tree` skipped!
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.parse_cst));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.lower_ast));
    try std.testing.expectEqual(@as(u64, 1), db.telemetry.countExecutions(.item_tree));
    try std.testing.expect(db.telemetry.early_cutoff_hits >= 1);

    const lower_memo = db.getMemoHeader(QueryKey.forFile(.lower_ast, file_id)).?;
    try std.testing.expectEqual(rev1, lower_memo.changed_at);
    try std.testing.expectEqual(rev3, lower_memo.verified_at);
}

// --------- ItemTree Signature Firewall & Body Window ----------

test "test_item_tree_signature_firewall_and_position_independent_sibling_bodies" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(2);
    const source_v1 =
        \\pub fn foo(input_val: i32) -> i32 {
        \\    let step_one = input_val + 1;
        \\    return step_one;
        \\}
        \\
        \\pub fn bar(multiplier: i32) -> i32 {
        \\    let scaled = multiplier * 10;
        \\    return scaled + 2;
        \\}
    ;

    const rev1 = try db.setInput(file_id, source_v1, .low);
    const tree_v1 = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 2), tree_v1.entries.len);

    const def_foo = tree_v1.entries[0].def_id;
    const def_bar = tree_v1.entries[1].def_id;
    try std.testing.expectEqualStrings("foo", tree_v1.entries[0].name_text);
    try std.testing.expectEqualStrings("bar", tree_v1.entries[1].name_text);

    // Run full semantic pipeline on both `foo` and `bar` at `rev1`:
    _ = try db.verifySastMir(def_foo);
    _ = try db.verifySastMir(def_bar);
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.verify_sast_mir));

    // Edit `foo`'s body AND insert 20 extra lines before `bar` so `bar` shifts down by 20 lines:
    const source_v2 =
        \\pub fn foo(input_val: i32) -> i32 {
        \\    let step_one = input_val + 100;
        \\    let step_two = step_one * 3;
        \\    let step_three = step_two - 7;
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\
        \\    return step_three;
        \\}
        \\
        \\pub fn bar(multiplier: i32) -> i32 {
        \\    let scaled = multiplier * 10;
        \\    return scaled + 2;
        \\}
    ;

    const rev2 = try db.setInput(file_id, source_v2, .low);
    try std.testing.expect(rev2.isAfter(rev1));

    // [1] Verify `bar` first: `bar` shifted by 20 lines, yet `typecheckBody(def_bar)` is NOT re-executed!
    _ = try db.verifySastMir(def_bar);
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.verify_sast_mir));

    // [2] Verify `foo`: `foo`'s signature projections backdate to `rev1`, while `typecheckBody(def_foo)` re-runs!
    _ = try db.verifySastMir(def_foo);
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.verify_sast_mir));

    const foo_sig_proj_memo = db.getMemoHeader(QueryKey.forDef(.item_tree_sig_proj, def_foo)).?;
    const foo_def_sig_memo = db.getMemoHeader(QueryKey.forDef(.def_signature, def_foo)).?;
    const foo_body_proj_memo = db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_foo)).?;
    const bar_body_proj_memo = db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_bar)).?;

    try std.testing.expectEqual(rev1, foo_sig_proj_memo.changed_at);
    try std.testing.expectEqual(rev1, foo_def_sig_memo.changed_at);
    try std.testing.expectEqual(rev2, foo_body_proj_memo.changed_at);
    try std.testing.expectEqual(rev1, bar_body_proj_memo.changed_at);
}

// -------- Durability Fast-Path, Cycles & Cancellation ---------

/// Test hook creating a 2-node dependency cycle between `DefId(file, 0)` and `DefId(file, 1)`.
fn testCycleHook(db: *CompilerDb, key: QueryKey) QueryError!void {
    if (key.stage == .def_signature) {
        const current_def = DefId.fromInt(key.entity_index);
        const peer_index: u12 = if (current_def.itemIndex() == 0) 1 else 0;
        const peer_def = DefId.init(current_def.fileId(), peer_index);
        _ = try db.getDefSignature(peer_def);
    }
}

test "test_durability_fast_path_cycle_recovery_and_cancellation" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const stdlib_file = FileId.fromInt(10);
    const active_file = FileId.fromInt(11);

    _ = try db.setInput(
        stdlib_file,
        "pub fn clamp_val(val: i32) -> i32 { return val; }\npub fn abs_val(val: i32) -> i32 { return val; }\n",
        .high,
    );
    _ = try db.setInput(
        active_file,
        "pub fn entry_point() -> i32 { return 0; }\n",
        .low,
    );

    const stdlib_tree = try db.extractItemTree(stdlib_file);
    const stdlib_def0 = stdlib_tree.entries[0].def_id;
    _ = try db.verifySastMir(stdlib_def0);

    const stdlib_sast_memo = db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, stdlib_def0)).?;
    try std.testing.expectEqual(Durability.high, stdlib_sast_memo.min_durability);
    try std.testing.expect(stdlib_sast_memo.is_pure_high_durability);

    // Mutate only the `.low` durability active editor buffer:
    _ = try db.setInput(
        active_file,
        "pub fn entry_point() -> i32 { return 42; }\n",
        .low,
    );

    const fast_hits_before = db.telemetry.durability_fast_path_hits;
    _ = try db.verifySastMir(stdlib_def0);
    try std.testing.expect(db.telemetry.durability_fast_path_hits > fast_hits_before);

    // Test deterministic `error.DependencyCycle` detection and clean stack unwinding:
    _ = try db.setInput(
        stdlib_file,
        "pub fn clamp_val(val: i64) -> i64 { return val + 1; }\npub fn abs_val(val: i64) -> i64 { return val; }\n",
        .high,
    );
    db.setCustomStageHook(testCycleHook);
    try std.testing.expectError(error.DependencyCycle, db.getDefSignature(stdlib_def0));
    try std.testing.expectEqual(@as(usize, 0), db.active_stack.items.len);
    try std.testing.expectEqual(@as(usize, 0), db.in_flight_keys.count());
    db.setCustomStageHook(null);

    // Verify clean recovery after clearing the cycle hook:
    const recovered_sig = try db.getDefSignature(stdlib_def0);
    try std.testing.expectEqual(stdlib_def0, recovered_sig.def_id);

    // Test cooperative cancellation (`requestCancellation` -> `error.Cancelled` -> `clearCancellation`):
    db.requestCancellation();
    try std.testing.expect(db.isCancelled());
    try std.testing.expectError(error.Cancelled, db.verifySastMir(stdlib_def0));
    db.clearCancellation();
    try std.testing.expect(!db.isCancelled());
    const sast_after = try db.verifySastMir(stdlib_def0);
    try std.testing.expect(sast_after.is_verified_sound);
}

test "test_red_team_const_paren_init_comptime_firewall_impl_names_and_def_id_clamp" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] `DefId.init` boundary clamping never produces `DefId.NONE`:
    const max_file = FileId.fromInt(0xF_FFFF);
    const clamped_def = DefId.init(max_file, 0xFFF);
    try std.testing.expect(!clamped_def.isNone());
    try std.testing.expectEqual(@as(u12, 0xFFE), clamped_def.itemIndex());

    // [2] Parenthesized `const` initializer & top-level `comptime` block firewall:
    const file_id = FileId.fromInt(20);
    const src_v1 =
        "const LIMIT: i32 = (100);\n" ++
        "comptime {\n    let init_step = 1;\n}\n" ++
        "impl Display for Point {}\n" ++
        "impl Display for Circle {}\n";
    _ = try db.setInput(file_id, src_v1, .low);
    const tree_v1 = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 4), tree_v1.entries.len);

    const const_sig_v1 = tree_v1.entries[0].signature_fingerprint;
    const const_body_v1 = tree_v1.entries[0].body_fingerprint;
    const comptime_sig_v1 = tree_v1.entries[1].signature_fingerprint;
    const comptime_body_v1 = tree_v1.entries[1].body_fingerprint;

    try std.testing.expectEqualStrings("Display for Point", tree_v1.entries[2].name_text);
    try std.testing.expectEqualStrings("Display for Circle", tree_v1.entries[3].name_text);

    const src_v2 =
        "const LIMIT: i32 = (200);\n" ++
        "comptime {\n    let init_step = 999;\n}\n" ++
        "impl Display for Point {}\n" ++
        "impl Display for Circle {}\n";
    _ = try db.setInput(file_id, src_v2, .low);
    const tree_v2 = try db.extractItemTree(file_id);

    try std.testing.expect(Fingerprint128.eql(const_sig_v1, tree_v2.entries[0].signature_fingerprint));
    try std.testing.expect(!Fingerprint128.eql(const_body_v1, tree_v2.entries[0].body_fingerprint));
    try std.testing.expect(Fingerprint128.eql(comptime_sig_v1, tree_v2.entries[1].signature_fingerprint));
    try std.testing.expect(!Fingerprint128.eql(comptime_body_v1, tree_v2.entries[1].body_fingerprint));

    // [3] Missing-identifier syntax errors never steal identifiers from inside `{ … }`:
    const broken_file = FileId.fromInt(21);
    _ = try db.setInput(broken_file, "fn () { let stolen_local = 1; }\nstruct { stolen_field: i32 }\n", .low);
    const broken_tree = try db.extractItemTree(broken_file);
    for (broken_tree.entries) |entry| {
        try std.testing.expectEqualStrings("", entry.name_text);
    }
}

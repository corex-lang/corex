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
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const diagnostic = @import("diag/diagnostic.zig");
const router = @import("cli/router.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const hir = @import("hir.zig");
const mir = @import("mir.zig");
const mir_sast = @import("mir_sast.zig");
const mir_vm = @import("mir_vm.zig");
const mir_opt = @import("mir_opt.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const TypeId = mem_foundation.TypeId;
const HirIndex = mem_foundation.HirIndex;
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
const LabeledSpan = diagnostic.LabeledSpan;
const ScopeId = symbol_resolver.ScopeId;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;
const InternPool = type_system.InternPool;
const TypeChecker = type_system.TypeChecker;
const TargetLayout = type_system.TargetLayout;
const BodySemanticSideTables = type_system.BodySemanticSideTables;

// ---------------------------------------- TYPES ----------------------------------------

// ---------------- Revisions, Durability & Keys ----------------

/// Monotonically increasing logical database revision clock bumped on input mutations.
pub const Revision = enum(u32) {
    /// Initial revision assigned when `CompilerDb` is constructed (`1`).
    initial = 1,
    _,

    /// Converts a raw 32-bit unsigned integer into a `Revision`.
    pub inline fn fromInt(raw_val: u32) Revision {
        return @fromBackingInt(@intCast(raw_val));
    }

    /// Returns the underlying 32-bit integer representation of `self`.
    pub inline fn asInt(self: Revision) u32 {
        return @backingInt(self);
    }

    /// Returns the next sequential `Revision` (`self + 1`).
    pub inline fn next(self: Revision) Revision {
        return @fromBackingInt(@intCast(self.asInt() + 1));
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
        return if (@backingInt(first) < @backingInt(second)) first else second;
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

/// Canonical 14-stage demand-driven query pipeline (`PLAN.md` Phase 3 & Phase 5, `DR-12` Section 3.1).
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
    /// Stage 10: Isolated per-definition `AST -> HIR` desugaring (`DefId -> HirStore`, `[CRITICAL-11]`).
    lower_def_hir = 10,
    /// Stage 11: Per-definition Block-Argument SSA `HIR -> MIR` construction (`DefId -> DefMirArtifact`).
    build_def_mir = 11,
    /// Stage 12: Sandboxed `MirVm` `const` / `comptime` evaluation with Early Cutoff (`DefId -> ComptimeEvalArtifact`).
    eval_comptime_def = 12,
    /// Stage 13: Dual-mode `--dev` / `--release` module `MIR` optimization (`(FileId, is_release) -> MirOptModuleResult`).
    optimize_mir_module = 13,
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

    /// Constructs a `QueryKey` targeting `(file_id, is_release_mode)` at `stage`.
    pub inline fn forFileMode(stage: QueryStage, file_id: FileId, is_release_mode: bool) QueryKey {
        return .{
            .stage = stage,
            .flags = @intFromBool(is_release_mode),
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

    /// Constructs a Stage 9 `QueryKey` projecting only the 34 caller-observable `FnRegionSummary` bytes (`DR-17` §2.5).
    pub inline fn forSastSummaryProj(def_id: DefId) QueryKey {
        return .{
            .stage = .verify_sast_mir,
            .flags = SAST_SUMMARY_PROJ_FLAG,
            .reserved = 0,
            .entity_index = def_id.asInt(),
        };
    }

    /// Constructs a synthetic `.source_text` `QueryKey` for a Stage-0 compiler config slot (`[CRITICAL-17]`).
    pub inline fn forConfig(config_entity: u32) QueryKey {
        return .{
            .stage = .source_text,
            .flags = 0,
            .reserved = 0,
            .entity_index = config_entity,
        };
    }

    /// Constructs a synthetic `.source_text` `QueryKey` tracking an `@embed_bytes` relative path (`[CRITICAL-02]`).
    pub inline fn forEmbedFile(path_symbol: SymbolId) QueryKey {
        return .{
            .stage = .source_text,
            .flags = EMBED_FILE_KEY_FLAG,
            .reserved = 0,
            .entity_index = path_symbol.asInt(),
        };
    }

    /// Packs `self` into a 64-bit unsigned integer for $O(1)$ hash table lookup.
    pub inline fn asU64(self: QueryKey) u64 {
        return (@as(u64, self.entity_index) << 32) |
            (@as(u64, self.reserved) << 16) |
            (@as(u64, self.flags) << 8) |
            @as(u64, @backingInt(self.stage));
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
    /// `true` if `recorded_slice.len` exceeded `MAX_DEPS_PER_MEMO`, forcing conservative Red Path (`1` byte).
    has_overflowed_deps: bool = false,
    /// Explicit trailing alignment padding (`1` byte, always `0`).
    _pad0: u8 = 0,
    /// Explicit trailing alignment padding (`2` bytes, always `0`).
    _pad1: u16 = 0,
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
    /// Root module lexical `ScopeId` in `CompilerDb.symbol_table`.
    module_scope: ScopeId = .none,
    /// Total number of top-level items resolved in `file_id`.
    item_count: u32,
    /// Total number of `pub`-exported items in `file_id`.
    public_item_count: u32,
    /// Total number of name-resolution or signature errors emitted in `file_id`.
    error_count: u32 = 0,
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
    /// Resolved symbol handle in `CompilerDb.symbol_table`.
    symbol_index: SymbolIndex = .none,
    /// Resolved canonical `TypeId` in `CompilerDb.type_pool`.
    type_id: TypeId = .err_ty,
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
    /// Number of type-checking errors emitted inside `def_id`'s body.
    error_count: u32 = 0,
    /// Number of warnings (e.g., `W0401`, `W0402`) emitted inside `def_id`'s body.
    warning_count: u32 = 0,
    /// 128-bit signature fingerprint consumed during body checking.
    signature_fingerprint: Fingerprint128,
    /// 128-bit position-independent body AST fingerprint consumed during body checking.
    body_fingerprint: Fingerprint128,
    /// Combined 128-bit fingerprint of the typed body output.
    typed_fingerprint: Fingerprint128,
};

/// Stage 9 per-definition MIR SAST ownership, contract, and capability verification artifact.
pub const SastVerificationArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Owning source file handle.
    file_id: FileId,
    /// `true` if the body passed SAST verification without fatal memory, contract, or sandbox errors.
    is_verified_sound: bool,
    /// Number of SAST errors emitted inside `def_id`.
    error_count: u32 = 0,
    /// Number of SAST warnings (`W0308`, `W0314`, `W0329`, `W0330`) emitted inside `def_id`.
    warning_count: u32 = 0,
    /// Count of `bounds_check` / `slice_range_check` intrinsics statically proven & eliminated.
    eliminated_bounds_checks: u32 = 0,
    /// Count of `.narrow()` (`narrow_check`) intrinsics statically proven & eliminated.
    eliminated_narrow_checks: u32 = 0,
    /// Count of `drop_in_place` / `drop_if_live` instructions synthesized by `ElaborateDrops`.
    emitted_drops: u32 = 0,
    /// Finalized 40-byte `FnRegionSummary` (`34` caller-observable bytes for Early Cutoff).
    summary: mir_sast.FnRegionSummary = .{},
    /// 128-bit fingerprint of the SAST verification summary.
    sast_fingerprint: Fingerprint128,
};

/// Stage 11 per-definition lowered and `V1`–`V6` verified `MIR` bundle artifact.
pub const DefMirArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Owning source file handle.
    file_id: FileId,
    /// `true` if `bundle` contains a synthetic initializer wrapper (`const` or `comptime` block) rather than runtime `fn`s.
    is_comptime_initializer_only: bool = false,
    /// Lowered `MirBody` records (primary function/initializer plus any nested closures or `@derive` methods).
    bundle: mir.MirModuleBundle,
    /// 128-bit position-independent structural fingerprint of `bundle`.
    mir_fingerprint: Fingerprint128,

    /// Releases all `MirBody` allocations owned by `self.bundle`.
    pub fn deinit(self: *DefMirArtifact) void {
        self.bundle.deinit();
        self.* = undefined;
    }

    /// Returns the primary `MirBody` matching `self.def_id` (or the first body in `bundle` if non-empty).
    pub fn primaryBody(self: *const DefMirArtifact) ?*const mir.MirBody {
        for (self.bundle.bodies.items) |*body_item| {
            if (body_item.def_id == self.def_id) return body_item;
        }
        if (self.bundle.bodies.items.len > 0) return &self.bundle.bodies.items[0];
        return null;
    }
};

/// Cached drop-elaborated `MirModuleBundle` for `MirVm` `comptime` execution, keyed to `DefMirArtifact.mir_fingerprint`.
pub const ComptimeElabMirEntry = struct {
    /// Fingerprint of the unelaborated `DefMirArtifact` from which `bundle` was elaborated.
    source_mir_fp: Fingerprint128,
    /// Drop-elaborated `MirModuleBundle` with `drop_in_place` / `drop_if_live` instructions materialized.
    bundle: mir.MirModuleBundle,

    /// Releases all `MirBody` allocations owned by `self.bundle`.
    pub fn deinit(self: *ComptimeElabMirEntry) void {
        self.bundle.deinit();
        self.* = undefined;
    }
};

/// Stage 12 evaluated `const` / `comptime` definition artifact with `.rodata` promotion & Early Cutoff fingerprint.
pub const ComptimeEvalArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Concrete `TypeId` of the evaluated value.
    type_id: TypeId,
    /// Evaluated `ComptimeValue` representation.
    value: hir.ComptimeValue = .unit_val,
    /// Promoted `.rodata` handle in `CompilerDb.rodata_pool` (`.none` when unpromoted or errored).
    rodata_id: mir_vm.ComptimeAllocId = .none,
    /// `true` if compile-time evaluation trapped (`E0501`–`E0510`).
    has_errors: bool = false,
    /// 128-bit fingerprint computed strictly from `(type_id, canonical_value)` for Early Cutoff backdating.
    value_fingerprint: Fingerprint128,
};

/// Telemetry counters tracking per-stage query executions, Early Cutoffs, and fast-path hits.
pub const QueryTelemetry = struct {
    /// Number of times each `QueryStage` (`0..13`) executed its compute function.
    stage_executions: [STAGE_COUNT]u64 = @splat(0),
    /// Number of times `maybeChangedAfter` verified a memo on the Green Path without re-execution.
    green_hits: u64 = 0,
    /// Number of times `maybeChangedAfter` skipped dependency traversal via the Durability fast-path.
    durability_fast_path_hits: u64 = 0,
    /// Number of times `executeAndBackdate` recomputed an identical fingerprint and backdated `changed_at`.
    early_cutoff_hits: u64 = 0,

    /// Returns the total execution count recorded for `stage`.
    pub inline fn countExecutions(self: *const QueryTelemetry, stage: QueryStage) u64 {
        return self.stage_executions[@backingInt(stage)];
    }

    /// Resets all telemetry counters to zero.
    pub inline fn reset(self: *QueryTelemetry) void {
        self.* = .{};
    }
};

/// Optional callback hook invoked at the start of `computeStage` for deterministic cycle testing.
pub const CustomStageHook = *const fn (db: *CompilerDb, key: QueryKey) QueryError!void;

// --------------------------------------- CONSTS ----------------------------------------

/// Total number of `QueryStage` variants in the canonical pipeline (`14`).
pub const STAGE_COUNT: usize = @typeInfo(QueryStage).@"enum".field_names.len;
/// Total number of `Durability` tiers (`3`: `.low`, `.medium`, `.high`).
pub const DURABILITY_COUNT: usize = @typeInfo(Durability).@"enum".field_names.len;
/// Maximum number of top-level items encoded in a 12-bit `DefId.local_item_index` (`4,096`).
pub const MAX_ITEMS_PER_FILE: usize = std.math.maxInt(u12) + 1;
/// Maximum number of direct dependencies recorded in a single `MemoHeader` (`65,535`).
pub const MAX_DEPS_PER_MEMO: usize = std.math.maxInt(u16);
/// Reserved synthetic `.source_text` entity index tracking `CompilerDb.target_layout` (`[CRITICAL-17]`).
pub const CONFIG_KEY_TARGET_LAYOUT: u32 = 0xFFFF_FFF0;
/// Reserved synthetic `.source_text` entity index tracking `CompilerDb.comptime_step_limit` (`[CRITICAL-17]`).
pub const CONFIG_KEY_COMPTIME_LIMIT: u32 = 0xFFFF_FFF1;
/// Reserved synthetic `.source_text` entity index tracking `CompilerDb` `@embed_bytes` sandbox (`[CRITICAL-17]`).
pub const CONFIG_KEY_EMBED_SANDBOX: u32 = 0xFFFF_FFF2;
/// Reserved synthetic `.source_text` entity index tracking `--sast-strict` (`CompilerDb.is_sast_strict`).
pub const CONFIG_KEY_SAST_STRICT: u32 = 0xFFFF_FFF3;
/// Flag bit on `.source_text` `QueryKey.flags` identifying a tracked `@embed_bytes` file dependency (`[CRITICAL-02]`).
pub const EMBED_FILE_KEY_FLAG: u8 = 0x01;
/// Flag bit on `.verify_sast_mir` `QueryKey.flags` projecting only the 34 caller-observable `FnRegionSummary` bytes.
pub const SAST_SUMMARY_PROJ_FLAG: u8 = 1 << 1;
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
        hasher.updateU8(@backingInt(tok_rec.kind));
        hasher.updateU8(@bitCast(tok_rec.flags));
        hasher.updateU16(tok_rec.byte_len);
        hasher.updateU32(tok_rec.byte_offset);
    }

    const cst_count = cst_arena.countNodes();
    hasher.updateU32(@intCast(cst_count));
    i = 0;
    while (i < cst_count) : (i += 1) {
        const cst_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(i)));
        hasher.updateU8(@backingInt(cst_rec.kind));
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
        hasher.updateU8(@backingInt(node.tag));
        if (!node.main_token.isNone() and node.main_token.asInt() < token_buffer.countTokens()) {
            const main_rec = token_buffer.getToken(node.main_token);
            hasher.updateU8(@backingInt(main_rec.kind));
            hasher.updateBytes(getTokenLexeme(source, token_buffer, node.main_token));
        } else {
            hasher.updateU8(0xFF);
        }

        hasher.updateU8(@backingInt(node.lhs.tag));
        if (node.lhs.tag == .token) {
            const lhs_tok = TokenIndex.fromInt(node.lhs.payload);
            if (lhs_tok.asInt() < token_buffer.countTokens()) {
                hasher.updateU8(@backingInt(token_buffer.getToken(lhs_tok).kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, lhs_tok));
            }
        } else {
            hasher.updateU32(node.lhs.payload);
        }

        hasher.updateU8(@backingInt(node.rhs.tag));
        if (node.rhs.tag == .token) {
            const rhs_tok = TokenIndex.fromInt(node.rhs.payload);
            if (rhs_tok.asInt() < token_buffer.countTokens()) {
                hasher.updateU8(@backingInt(token_buffer.getToken(rhs_tok).kind));
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
        hasher.updateU8(@backingInt(cst_rec.kind));
        hasher.updateU8(if (cst_rec.flags.has_error) 1 else 0);
        if (is_leaf) {
            if (cst_rec.flags.is_missing_or_injected and cst_rec.flags.has_error) {
                hasher.updateU8(INJECTED_ERROR_LEAF_MARKER);
            } else if (!cst_rec.token.isNone() and cst_rec.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(cst_rec.token);
                hasher.updateU8(@backingInt(tok_rec.kind));
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
                    hasher.updateU8(@backingInt(node.kind));
                    hasher.updateU8(INJECTED_ERROR_LEAF_MARKER);
                }
                cursor += 1;
                continue;
            }
            hasher.updateU8(@backingInt(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            if (!node.token.isNone() and node.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(node.token);
                hasher.updateU8(@backingInt(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
            }
        } else {
            hasher.updateU8(@backingInt(node.kind));
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
                    hasher.updateU8(@backingInt(node.kind));
                    hasher.updateU8(INJECTED_ERROR_LEAF_MARKER);
                }
                continue;
            }
            hasher.updateU8(@backingInt(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            if (!node.token.isNone() and node.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(node.token);
                hasher.updateU8(@backingInt(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
            }
        } else {
            hasher.updateU8(@backingInt(node.kind));
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
                hasher.updateU8(@backingInt(tok_rec.kind));
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
        sig_tree_hasher.updateU8(@backingInt(entry.kind));
        sig_tree_hasher.updateU8(if (entry.is_pub) 1 else 0);
        sig_tree_hasher.updateBytes(entry.name_text);
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

/// Appends a pool-order-independent canonical representation of `sym_id` to `hasher`.
fn hashSymbolTextCanonical(
    hasher: *StructuralHasher,
    interner: *const StringInterner,
    sym_id: SymbolId,
) void {
    if (sym_id == .empty or sym_id == .none) {
        hasher.updateU8(0);
        hasher.updateU32(sym_id.asInt());
        return;
    }
    hasher.updateU8(1);
    hasher.updateBytes(interner.get(sym_id));
}

/// Appends a pool-order-independent canonical representation of `ty` to `hasher`.
fn hashTypeCanonical(
    hasher: *StructuralHasher,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    ty: TypeId,
) void {
    if (ty.toU32() < 64 or ty.isNone()) {
        hasher.updateU8(0);
        hasher.updateU32(ty.toU32());
        return;
    }
    var ty_buf: [512]u8 = undefined;
    const formatted_ty = pool.formatType(ty, sym_table, &ty_buf);
    hasher.updateU8(1);
    hasher.updateBytes(formatted_ty);
}

/// Returns `true` if `extra_idx` falls inside the `TypeId` argument slice of any `.hir_intrinsic_call`.
fn isIntrinsicTypeArgExtraSlot(store: *const hir.HirStore, extra_idx: usize) bool {
    for (0..store.nodes.len) |node_idx| {
        const node = store.nodes.get(node_idx);
        if (node.tag == .hir_intrinsic_call and node.data.rhs + 2 <= store.extra_data.items.len) {
            const ty_arg_len: usize = store.extra_data.items[node.data.rhs];
            const ty_start: usize = node.data.rhs + 2;
            if (extra_idx >= ty_start and extra_idx < ty_start + ty_arg_len) {
                return true;
            }
        }
    }
    return false;
}

/// Computes a position- and pool-order-independent 128-bit structural fingerprint of a lowered `HirStore`.
fn computeHirStoreFingerprint(
    store: *const hir.HirStore,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    hasher.updateU32(store.root_hir.asInt());
    hasher.updateU8(store.target_layout.ptr_byte_size);
    hasher.updateU8(store.target_layout.ptr_align_log2);
    hasher.updateU32(@intCast(store.nodes.len));
    var has_intrinsic_type_args = false;
    for (0..store.nodes.len) |node_idx| {
        const node = store.nodes.get(node_idx);
        hasher.updateU8(@backingInt(node.tag));
        hasher.updateU8(@bitCast(node.flags));
        hashTypeCanonical(&hasher, pool, sym_table, node.type_id);
        hasher.updateU32(node.data.lhs);
        switch (node.tag) {
            .hir_struct_decl, .hir_enum_decl, .hir_global_ref => {
                hasher.updateU32(0);
            },
            .hir_intrinsic_call => {
                hasher.updateU32(node.data.rhs);
                if (node.data.rhs + 2 <= store.extra_data.items.len) {
                    const ty_arg_len: usize = store.extra_data.items[node.data.rhs];
                    if (ty_arg_len > 0) {
                        has_intrinsic_type_args = true;
                        const ty_start: usize = node.data.rhs + 2;
                        const safe_end = @min(ty_start + ty_arg_len, store.extra_data.items.len);
                        for (store.extra_data.items[ty_start..safe_end]) |raw_ty_arg| {
                            hashTypeCanonical(&hasher, pool, sym_table, TypeId.fromInt(raw_ty_arg));
                        }
                    }
                }
            },
            else => hasher.updateU32(node.data.rhs),
        }
    }
    hasher.updateU32(@intCast(store.extra_data.items.len));
    for (store.extra_data.items, 0..) |extra_word, extra_idx| {
        if (has_intrinsic_type_args and isIntrinsicTypeArgExtraSlot(store, extra_idx)) {
            hasher.updateU32(0);
        } else {
            hasher.updateU32(extra_word);
        }
    }
    hasher.updateU32(@intCast(store.locals.items.len));
    for (store.locals.items) |loc_decl| {
        hashSymbolTextCanonical(&hasher, interner, loc_decl.name);
        hashTypeCanonical(&hasher, pool, sym_table, loc_decl.type_id);
        hasher.updateU8(@backingInt(loc_decl.mode));
        hasher.updateU8(@intFromBool(loc_decl.is_mut));
        hasher.updateU8(@intFromBool(loc_decl.is_comptime));
    }
    hasher.updateU32(@intCast(store.functions.items.len));
    for (store.functions.items) |fn_meta| {
        hasher.updateU32(fn_meta.def_id.asInt());
        hashSymbolTextCanonical(&hasher, interner, fn_meta.name);
        hashTypeCanonical(&hasher, pool, sym_table, fn_meta.fn_ty);
        hashTypeCanonical(&hasher, pool, sym_table, fn_meta.ret_ty);
        hasher.updateU32(fn_meta.body_hir.asInt());
        hasher.updateU8(@intFromBool(fn_meta.is_comptime));
        hasher.updateU8(@intFromBool(fn_meta.is_contextless));
    }
    hasher.updateU32(@intCast(store.const_pool.items.len));
    for (store.const_pool.items) |const_item| {
        hashComptimeValueShallow(&hasher, const_item, pool, sym_table, interner);
    }
    hasher.updateU32(@intCast(store.const_elements.items.len));
    for (store.const_elements.items) |elem_idx| {
        hasher.updateU32(elem_idx);
    }
    return hasher.final();
}

/// Appends the pool-order-independent structural content of a `hir.ComptimeValue` entry to `hasher`.
fn hashComptimeValueShallow(
    hasher: *StructuralHasher,
    val: hir.ComptimeValue,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
) void {
    switch (val) {
        .unit_val => hasher.updateU8(0),
        .bool_val => |flag| {
            hasher.updateU8(1);
            hasher.updateU8(@intFromBool(flag));
        },
        .int_val => |int_v| {
            hasher.updateU8(2);
            const raw_u128: u128 = @bitCast(int_v);
            hasher.updateU64(@truncate(raw_u128));
            hasher.updateU64(@truncate(raw_u128 >> 64));
        },
        .float_val => |flt_v| {
            hasher.updateU8(3);
            hasher.updateU64(@bitCast(flt_v));
        },
        .char_val => |cp| {
            hasher.updateU8(4);
            hasher.updateU32(cp);
        },
        .str_val => |sym_id| {
            hasher.updateU8(5);
            hashSymbolTextCanonical(hasher, interner, sym_id);
        },
        .bytes_val => |sym_id| {
            hasher.updateU8(6);
            hashSymbolTextCanonical(hasher, interner, sym_id);
        },
        .aggregate => |agg| {
            hasher.updateU8(7);
            hashTypeCanonical(hasher, pool, sym_table, agg.type_id);
            hasher.updateU32(agg.elem_start);
            hasher.updateU32(agg.elem_len);
        },
        .variant => |var_v| {
            hasher.updateU8(8);
            hashTypeCanonical(hasher, pool, sym_table, var_v.type_id);
            hasher.updateU32(var_v.tag_ordinal);
            hasher.updateU32(var_v.payload_const_idx);
        },
        .type_info_mirror => |ti| {
            hasher.updateU8(9);
            hashTypeCanonical(hasher, pool, sym_table, ti.reflected_ty);
            hasher.updateU64(ti.size_bytes);
            hasher.updateU32(ti.align_bytes);
            hashSymbolTextCanonical(hasher, interner, ti.type_name_id);
        },
        .field_info_mirror => |fi| {
            hasher.updateU8(10);
            hashTypeCanonical(hasher, pool, sym_table, fi.owner_ty);
            hasher.updateU32(fi.field_ordinal);
            hasher.updateU64(fi.byte_offset);
        },
        .variant_info_mirror => |vi| {
            hasher.updateU8(11);
            hashTypeCanonical(hasher, pool, sym_table, vi.owner_ty);
            hasher.updateU32(vi.variant_ordinal);
        },
    }
}

/// Computes a position- and pool-order-independent 128-bit structural fingerprint of a `MirModuleBundle`.
fn computeMirBundleFingerprint(
    bundle: *const mir.MirModuleBundle,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    hasher.updateU32(@intCast(bundle.bodies.items.len));
    for (bundle.bodies.items) |*body_item| {
        hasher.updateU32(body_item.def_id.asInt());
        hashSymbolTextCanonical(&hasher, interner, body_item.name);
        hashTypeCanonical(&hasher, pool, sym_table, body_item.ret_ty);
        hasher.updateU32(body_item.param_count);
        hasher.updateU8(@intFromBool(body_item.is_contextless));
        hasher.updateU8(@intFromBool(body_item.has_ghost_instructions));
        hasher.updateU32(@intCast(body_item.locals.items.len));
        for (body_item.locals.items) |loc| {
            hashTypeCanonical(&hasher, pool, sym_table, loc.type_id);
            hasher.updateU8(loc.mode_raw);
            hasher.updateU8(loc.flags_raw);
            hasher.updateU16(loc.region_raw);
        }
        hasher.updateU32(@intCast(body_item.blocks.items.len));
        for (body_item.blocks.items, 0..) |bb, bb_idx| {
            const bb_id = mem_foundation.MirBlockId.fromInt(@intCast(bb_idx));
            hasher.updateU16(bb.paramLen());
            for (body_item.getBlockParams(bb_id)) |param_val| {
                const param_inst = body_item.getInst(param_val);
                hasher.updateU32(param_val.asInt());
                hashTypeCanonical(&hasher, pool, sym_table, param_inst.type_id);
            }
            for (body_item.getBlockInsts(bb_id)) |inst_val| {
                const inst = body_item.getInst(inst_val);
                hasher.updateU32(inst_val.asInt());
                hasher.updateU8(@backingInt(inst.op));
                hasher.updateU16(inst.aux_u16);
                hashTypeCanonical(&hasher, pool, sym_table, inst.type_id);
                if (inst.op == .fn_addr) {
                    hasher.updateU32(inst.operands.lhs);
                    hasher.updateU32(0);
                } else if (inst.op == .intrinsic_op) {
                    const ikind: mir.MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    if (ikind.hasPlaceInLhs()) {
                        hasher.updateU32(inst.operands.lhs);
                        hasher.updateU32(inst.operands.rhs);
                    } else if (ikind.hasTypeIdInLhs()) {
                        hashTypeCanonical(&hasher, pool, sym_table, TypeId.fromInt(inst.operands.lhs));
                        hasher.updateU32(inst.operands.rhs);
                    } else if (ikind.hasExtraArgs() and inst.operands.rhs > 0 and
                        inst.operands.lhs + inst.operands.rhs <= body_item.extra_args.items.len)
                    {
                        hasher.updateU32(inst.operands.rhs);
                        for (body_item.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |arg_val| {
                            hasher.updateU32(arg_val);
                        }
                    } else {
                        hasher.updateU32(inst.operands.lhs);
                        hasher.updateU32(inst.operands.rhs);
                    }
                } else {
                    hasher.updateU32(inst.operands.lhs);
                    hasher.updateU32(inst.operands.rhs);
                }
            }
            hasher.updateU8(@backingInt(bb.terminator.kind));
            hasher.updateU32(bb.terminator.cond_or_val);
            for (body_item.getOutgoingEdges(bb_id)) |edge| {
                hasher.updateU32(edge.target_bb.asInt());
                hasher.updateU16(edge.args_len);
                hasher.updateU16(edge.case_tag_idx);
                for (0..edge.args_len) |arg_i| {
                    hasher.updateU32(body_item.extra_args.items[edge.args_start + arg_i]);
                }
            }
        }
        hasher.updateU32(@intCast(body_item.consts.items.len));
        for (body_item.consts.items) |mc| {
            switch (mc) {
                .unit_val => hasher.updateU8(0),
                .bool_val => |flag| {
                    hasher.updateU8(1);
                    hasher.updateU8(@intFromBool(flag));
                },
                .char_val => |cp| {
                    hasher.updateU8(2);
                    hasher.updateU32(cp);
                },
                .int_val => |iv| {
                    hasher.updateU8(3);
                    const raw_bits: u128 = @bitCast(iv);
                    hasher.updateU64(@truncate(raw_bits));
                    hasher.updateU64(@truncate(raw_bits >> 64));
                },
                .float_val => |fv| {
                    hasher.updateU8(4);
                    hasher.updateU64(@bitCast(fv));
                },
                .str_val => |sid| {
                    hasher.updateU8(5);
                    hashSymbolTextCanonical(&hasher, interner, sid);
                },
                .bytes_val => |bid| {
                    hasher.updateU8(6);
                    hashSymbolTextCanonical(&hasher, interner, bid);
                },
            }
        }
    }
    return hasher.final();
}

/// Lowers a top-level `hir_const_decl` or `hir_block` (`comptime { … }`) into a zero-argument `MirBody`.
fn lowerInitializerHirToMirBody(
    allocator: std.mem.Allocator,
    def_id: DefId,
    source_store: *const hir.HirStore,
    expr_hir: HirIndex,
    ret_ty: TypeId,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
) !mir.MirBody {
    var temp_store = hir.HirStore.init(allocator, source_store.file_id);
    temp_store.target_layout = source_store.target_layout;
    defer temp_store.deinit();

    try temp_store.nodes.ensureTotalCapacity(allocator, source_store.nodes.len);
    for (0..source_store.nodes.len) |node_i| {
        temp_store.nodes.appendAssumeCapacity(source_store.nodes.get(node_i));
    }
    try temp_store.origin_ast.appendSlice(allocator, source_store.origin_ast.items);
    try temp_store.extra_data.appendSlice(allocator, source_store.extra_data.items);
    try temp_store.patterns.appendSlice(allocator, source_store.patterns.items);
    try temp_store.match_arms.appendSlice(allocator, source_store.match_arms.items);
    try temp_store.locals.appendSlice(allocator, source_store.locals.items);
    try temp_store.functions.appendSlice(allocator, source_store.functions.items);
    try temp_store.const_pool.appendSlice(allocator, source_store.const_pool.items);
    try temp_store.const_elements.appendSlice(allocator, source_store.const_elements.items);

    // Prepend synthetic return slot `0` and shift any local references inside `temp_store` by `+1`:
    const old_local_count = temp_store.locals.items.len;
    var shifted_locals = try std.ArrayListUnmanaged(hir.HirLocalDecl).initCapacity(
        allocator,
        old_local_count + 1,
    );
    errdefer shifted_locals.deinit(allocator);
    shifted_locals.appendAssumeCapacity(.{
        .name = .empty,
        .type_id = ret_ty,
        .decl_span = Span.init(source_store.file_id, 0, 0),
        .mode = .let_mode,
        .is_mut = true,
        .is_temp = true,
    });
    for (temp_store.locals.items) |old_loc| {
        var cloned_loc = old_loc;
        cloned_loc.is_param = false;
        shifted_locals.appendAssumeCapacity(cloned_loc);
    }
    temp_store.locals.deinit(allocator);
    temp_store.locals = shifted_locals;

    if (old_local_count > 0) {
        for (0..temp_store.nodes.len) |ni| {
            var nd = temp_store.nodes.get(ni);
            if (nd.tag == .hir_local_decl or nd.tag == .hir_var_ref) {
                nd.data.lhs += 1;
                temp_store.nodes.set(ni, nd);
            } else if (nd.tag == .hir_defer and (nd.data.lhs >> 1) > 0) {
                const old_err = (nd.data.lhs >> 1) - 1;
                nd.data.lhs = ((old_err + 2) << 1) | (nd.data.lhs & 1);
                temp_store.nodes.set(ni, nd);
            }
        }
        for (temp_store.patterns.items) |*pat| {
            if (pat.kind == .bind) {
                pat.kind.bind.local_id += 1;
            }
        }
    }

    const wrapper_fn_ty = try pool.internFn(.fn_ty, &.{}, &.{}, ret_ty, false);
    const sym_idx = sym_table.def_to_symbol.get(def_id.asInt()) orelse .none;
    const item_name = if (!sym_idx.isNone()) sym_table.getSymbol(sym_idx).name else .empty;
    const fn_meta = hir.HirFnMeta{
        .def_id = def_id,
        .symbol_index = sym_idx,
        .name = item_name,
        .fn_ty = wrapper_fn_ty,
        .ret_ty = ret_ty,
        .return_local_id = 0,
        .param_local_start = 1,
        .param_len = 0,
        .total_local_len = @intCast(temp_store.locals.items.len),
        .body_hir = expr_hir,
        .is_comptime = true,
    };

    return mir.lowerHirFnToMir(
        allocator,
        &temp_store,
        fn_meta,
        pool,
        sym_table,
        interner,
        diagnostic_sink,
    );
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
    /// Stage 9 finalized 40-byte `FnRegionSummary` records keyed by `DefId.asInt()`.
    sast_summaries: std.AutoHashMapUnmanaged(u32, mir_sast.FnRegionSummary) = .empty,
    /// Stage 9 per-symbol `FnRegionSummary` records (including `impl` methods) keyed by `SymbolIndex.asInt()`.
    sast_sym_summaries: std.AutoHashMapUnmanaged(u32, mir_sast.FnRegionSummary) = .empty,
    /// Canonical deduplicated `InternPool` (`TypeArena`) shared across queries.
    type_pool: InternPool,
    /// Unified lexical and module `SymbolTable` shared across queries.
    symbol_table: SymbolTable,
    /// Step-count budget (`--comptime-limit`) enforced by `MirVm` (`E0501`).
    comptime_step_limit: u64 = router.DEFAULT_COMPTIME_STEP_LIMIT,
    /// Active target pointer size and alignment (`NATIVE_64` vs `WASM32`).
    target_layout: TargetLayout = TargetLayout.NATIVE_64,
    /// Active `--sast-strict` policy flag (`W0314` on unproven bounds checks outside `@no_panic`).
    is_sast_strict: bool = false,
    /// Optional workspace root directory path for VFS-sandboxed `@embed_bytes` (`DR-05` §3.3).
    workspace_root: ?[]const u8 = null,
    /// Optional Zig `Io` handle for disk-backed `@embed_bytes` inside `workspace_root`.
    embed_io: ?std.Io = null,
    /// Optional in-memory virtual file map (`relative_path -> bytes`) for `@embed_bytes`.
    virtual_files: ?*const std.StringHashMapUnmanaged([]const u8) = null,
    /// Monotonic counter bumped on every `setEmbedSandbox` / `setEmbedIo` mutation (`[CRITICAL-17]`).
    embed_sandbox_epoch: u64 = 0,
    /// Last-changed revisions for synthetic config keys `0xFFFF_FFF0..0xFFFF_FFF3` (`[CRITICAL-17]`).
    config_changed_at: [4]Revision = .{ .initial, .initial, .initial, .initial },
    /// Deduplicated `.rodata` constant pool shared across `MirVm` evaluations.
    rodata_pool: mir_vm.RodataPool,
    /// Bounded `Wyhash(0)` pure-call memoization cache shared across `MirVm` runs.
    pure_call_memo_cache: mir_vm.PureCallMemoCache,
    /// Per-file semantic side tables (`@attribute_schema` instances) keyed by `FileId.asInt()`.
    file_side_tables: std.AutoHashMapUnmanaged(u32, BodySemanticSideTables) = .empty,
    /// Per-definition windowed semantic side tables keyed by `DefId.asInt()` (`[CRITICAL-11]`).
    def_side_tables: std.AutoHashMapUnmanaged(u32, BodySemanticSideTables) = .empty,
    /// Stage 10 per-definition lowered `HirStore`s keyed by `DefId.asInt()`.
    lowered_def_hirs: std.AutoHashMapUnmanaged(u32, hir.HirStore) = .empty,
    /// Stage 11 per-definition verified `MIR` bundles keyed by `DefId.asInt()`.
    built_def_mirs: std.AutoHashMapUnmanaged(u32, DefMirArtifact) = .empty,
    /// Cached drop-elaborated `MIR` bundles for `MirVm` `comptime` execution keyed by `DefId.asInt()`.
    comptime_elab_mirs: std.AutoHashMapUnmanaged(u32, ComptimeElabMirEntry) = .empty,
    /// Cross-`DefId` mutual-recursion peer sets discovered during Stage 9 `verify_sast_mir`.
    sast_cycle_peers: std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(DefId)) = .empty,
    /// Stage 12 evaluated `const` / `comptime` artifacts keyed by `DefId.asInt()`.
    evaluated_comptime_defs: std.AutoHashMapUnmanaged(u32, ComptimeEvalArtifact) = .empty,
    /// Stage 13 optimized `MIR` module results keyed by `QueryKey.forFileMode(…).asU64()`.
    optimized_mir_modules: std.AutoHashMapUnmanaged(u64, mir_opt.MirOptModuleResult) = .empty,
    /// Per-file signature resolution diagnostic sinks keyed by `FileId.asInt()`.
    sig_diagnostics: std.AutoHashMapUnmanaged(u32, DiagnosticSink) = .empty,
    /// Per-definition body type-checking diagnostic sinks keyed by `DefId.asInt()`.
    body_diagnostics: std.AutoHashMapUnmanaged(u32, DiagnosticSink) = .empty,
    /// Per-definition Stage 9 `MIR` SAST diagnostic sinks keyed by `DefId.asInt()`.
    sast_diagnostics: std.AutoHashMapUnmanaged(u32, DiagnosticSink) = .empty,
    /// Per-definition `HIR` lowering diagnostic sinks keyed by `DefId.asInt()`.
    hir_diagnostics: std.AutoHashMapUnmanaged(u32, DiagnosticSink) = .empty,
    /// Per-definition `MIR` construction & verification diagnostic sinks keyed by `DefId.asInt()`.
    mir_diagnostics: std.AutoHashMapUnmanaged(u32, DiagnosticSink) = .empty,
    /// Per-definition `MirVm` compile-time evaluation diagnostic sinks keyed by `DefId.asInt()`.
    comptime_diagnostics: std.AutoHashMapUnmanaged(u32, DiagnosticSink) = .empty,
    /// Per-`(FileId, is_release_mode)` `MIR` optimization diagnostic sinks keyed by `QueryKey.asU64()`.
    opt_diagnostics: std.AutoHashMapUnmanaged(u64, DiagnosticSink) = .empty,
    /// Optional hook for injecting synthetic dependency cycles in unit tests.
    custom_stage_hook: ?CustomStageHook = null,
    /// Execution, Green Path, Durability fast-path, and Early Cutoff counters.
    telemetry: QueryTelemetry = .{},

    /// Initializes a new `CompilerDb` instance bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) !CompilerDb {
        var interner = try StringInterner.init(allocator);
        errdefer interner.deinit();

        var type_pool = try InternPool.init(allocator);
        errdefer type_pool.deinit();

        const symbol_table = try SymbolTable.init(allocator, &interner);

        return .{
            .allocator = allocator,
            .interner = interner,
            .type_pool = type_pool,
            .symbol_table = symbol_table,
            .rodata_pool = mir_vm.RodataPool.init(allocator),
            .pure_call_memo_cache = mir_vm.PureCallMemoCache.init(allocator),
        };
    }

    /// Releases all owned source buffers, syntax arenas, item trees, IR artifacts, and memo tables.
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

        var file_st_iter = self.file_side_tables.valueIterator();
        while (file_st_iter.next()) |st_ptr| {
            st_ptr.deinit();
        }
        self.file_side_tables.deinit(self.allocator);

        var def_st_iter = self.def_side_tables.valueIterator();
        while (def_st_iter.next()) |st_ptr| {
            st_ptr.deinit();
        }
        self.def_side_tables.deinit(self.allocator);

        var hir_iter = self.lowered_def_hirs.valueIterator();
        while (hir_iter.next()) |hir_ptr| {
            hir_ptr.deinit();
        }
        self.lowered_def_hirs.deinit(self.allocator);

        var mir_iter = self.built_def_mirs.valueIterator();
        while (mir_iter.next()) |mir_ptr| {
            mir_ptr.deinit();
        }
        self.built_def_mirs.deinit(self.allocator);

        var elab_mir_iter = self.comptime_elab_mirs.valueIterator();
        while (elab_mir_iter.next()) |elab_ptr| {
            elab_ptr.deinit();
        }
        self.comptime_elab_mirs.deinit(self.allocator);

        var cycle_peer_iter = self.sast_cycle_peers.valueIterator();
        while (cycle_peer_iter.next()) |peer_list_ptr| {
            peer_list_ptr.deinit(self.allocator);
        }
        self.sast_cycle_peers.deinit(self.allocator);

        self.evaluated_comptime_defs.deinit(self.allocator);

        var opt_iter = self.optimized_mir_modules.valueIterator();
        while (opt_iter.next()) |opt_ptr| {
            opt_ptr.deinit();
        }
        self.optimized_mir_modules.deinit(self.allocator);

        var sig_diag_iter = self.sig_diagnostics.valueIterator();
        while (sig_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.sig_diagnostics.deinit(self.allocator);

        var body_diag_iter = self.body_diagnostics.valueIterator();
        while (body_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.body_diagnostics.deinit(self.allocator);

        var sast_diag_iter = self.sast_diagnostics.valueIterator();
        while (sast_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.sast_diagnostics.deinit(self.allocator);

        var hir_diag_iter = self.hir_diagnostics.valueIterator();
        while (hir_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.hir_diagnostics.deinit(self.allocator);

        var mir_diag_iter = self.mir_diagnostics.valueIterator();
        while (mir_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.mir_diagnostics.deinit(self.allocator);

        var ct_diag_iter = self.comptime_diagnostics.valueIterator();
        while (ct_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.comptime_diagnostics.deinit(self.allocator);

        var opt_diag_iter = self.opt_diagnostics.valueIterator();
        while (opt_diag_iter.next()) |sink_ptr| {
            sink_ptr.deinit();
        }
        self.opt_diagnostics.deinit(self.allocator);

        self.pure_call_memo_cache.deinit();
        self.rodata_pool.deinit();
        self.symbol_table.deinit();
        self.type_pool.deinit();
        self.lowered_artifacts.deinit(self.allocator);
        self.body_windows.deinit(self.allocator);
        self.resolved_signatures.deinit(self.allocator);
        self.def_signatures.deinit(self.allocator);
        self.typed_bodies.deinit(self.allocator);
        self.sast_results.deinit(self.allocator);
        self.sast_summaries.deinit(self.allocator);
        self.sast_sym_summaries.deinit(self.allocator);
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

    // -------------- Stage 0 Input & Config Mutations --------------

    /// Computes the 128-bit fingerprint of a synthetic Stage-0 compiler config key (`[CRITICAL-17]`).
    fn computeConfigFingerprint(self: *const CompilerDb, config_entity: u32) Fingerprint128 {
        var hasher = StructuralHasher.init();
        hasher.updateU32(config_entity);
        switch (config_entity) {
            CONFIG_KEY_TARGET_LAYOUT => {
                hasher.updateU8(self.target_layout.ptr_byte_size);
                hasher.updateU8(self.target_layout.ptr_align_log2);
            },
            CONFIG_KEY_COMPTIME_LIMIT => {
                hasher.updateU64(self.comptime_step_limit);
            },
            CONFIG_KEY_EMBED_SANDBOX => {
                hasher.updateU64(self.embed_sandbox_epoch);
                if (self.workspace_root) |ws_root| {
                    hasher.updateU8(1);
                    hasher.updateBytes(ws_root);
                } else {
                    hasher.updateU8(0);
                }
            },
            CONFIG_KEY_SAST_STRICT => {
                hasher.updateU8(@intFromBool(self.is_sast_strict));
            },
            else => {},
        }
        return hasher.final();
    }

    /// Bumps `current_revision`, invalidates durability tiers, updates `config_entity`'s memo, and clears pure-call cache.
    fn bumpConfigInput(self: *CompilerDb, config_entity: u32) void {
        self.current_revision = self.current_revision.next();
        var tier_idx: usize = 0;
        while (tier_idx < DURABILITY_COUNT) : (tier_idx += 1) {
            self.last_changed_by_durability[tier_idx] = self.current_revision;
        }
        const slot_idx = config_entity - CONFIG_KEY_TARGET_LAYOUT;
        self.config_changed_at[slot_idx] = self.current_revision;
        if (self.memos.getPtr(QueryKey.forConfig(config_entity).asU64())) |memo_ptr| {
            memo_ptr.output_fingerprint = self.computeConfigFingerprint(config_entity);
            memo_ptr.changed_at = self.current_revision;
            memo_ptr.verified_at = self.current_revision;
        }
        self.pure_call_memo_cache.clear();
    }

    /// Reads `target_layout` while recording a tracked dependency on `CONFIG_KEY_TARGET_LAYOUT` (`[CRITICAL-17]`).
    pub fn readTargetLayout(self: *CompilerDb) QueryError!TargetLayout {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_TARGET_LAYOUT));
        return self.target_layout;
    }

    /// Reads `comptime_step_limit` while recording a tracked dependency on `CONFIG_KEY_COMPTIME_LIMIT` (`[CRITICAL-17]`).
    pub fn readComptimeStepLimit(self: *CompilerDb) QueryError!u64 {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_COMPTIME_LIMIT));
        return self.comptime_step_limit;
    }

    /// Reads `is_sast_strict` while recording a tracked dependency on `CONFIG_KEY_SAST_STRICT`.
    pub fn readSastStrict(self: *CompilerDb) QueryError!bool {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_SAST_STRICT));
        return self.is_sast_strict;
    }

    /// Records a tracked dependency on `CONFIG_KEY_EMBED_SANDBOX` whenever `@embed_bytes` queries sandbox state.
    pub fn recordEmbedSandboxDependency(self: *CompilerDb) QueryError!QueryKey {
        const cfg_key = QueryKey.forConfig(CONFIG_KEY_EMBED_SANDBOX);
        _ = try self.fetchQuery(cfg_key);
        return cfg_key;
    }

    /// Records a tracked content-hashed dependency for an `@embed_bytes(rel_path)` read (`[CRITICAL-02]`).
    pub fn recordEmbeddedFileRead(
        self: *CompilerDb,
        rel_path: []const u8,
        content_bytes: []const u8,
    ) QueryError!QueryKey {
        const path_sym = self.interner.intern(rel_path) catch return error.OutOfMemory;
        const embed_key = QueryKey.forEmbedFile(path_sym);
        const content_fp = Fingerprint128.hashBytes(content_bytes);

        if (self.memos.getPtr(embed_key.asU64())) |existing_ptr| {
            if (!Fingerprint128.eql(existing_ptr.output_fingerprint, content_fp)) {
                existing_ptr.output_fingerprint = content_fp;
                existing_ptr.changed_at = self.current_revision;
            }
            existing_ptr.verified_at = self.current_revision;
        } else {
            try self.memos.put(self.allocator, embed_key.asU64(), .{
                .output_fingerprint = content_fp,
                .verified_at = self.current_revision,
                .changed_at = self.current_revision,
                .dep_edge_start = 0,
                .dep_edge_len = 0,
                .min_durability = .low,
                .is_pure_high_durability = false,
                .artifact_index = path_sym.asInt(),
            });
        }

        _ = try self.fetchQuery(embed_key);
        return embed_key;
    }

    /// Re-probes the current VFS or disk content fingerprint of a tracked `@embed_bytes` path (`[CRITICAL-02]`).
    fn probeEmbeddedFileFingerprint(self: *CompilerDb, path_sym: SymbolId) Fingerprint128 {
        const rel_path = self.interner.get(path_sym);
        if (mir_vm.isValidSandboxedEmbedPath(rel_path)) {
            if (self.virtual_files) |vfs_map| {
                if (vfs_map.get(rel_path)) |vfs_bytes| {
                    return Fingerprint128.hashBytes(vfs_bytes);
                }
            }
            if (self.workspace_root) |ws_root| {
                if (self.embed_io) |io_handle| {
                    if (std.Io.Dir.cwd().realPathFileAlloc(io_handle, ws_root, self.allocator)) |canon_ws| {
                        defer self.allocator.free(canon_ws);
                        if (std.fs.path.join(self.allocator, &.{ canon_ws, rel_path })) |full_path| {
                            defer self.allocator.free(full_path);
                            if (std.Io.Dir.cwd().openFile(io_handle, full_path, .{
                                .mode = .read_only,
                                .allow_directory = false,
                                .follow_symlinks = false,
                            })) |opened_file| {
                                defer opened_file.close(io_handle);
                                if (opened_file.stat(io_handle)) |file_stat| {
                                    const max_read_bytes: u64 = @min(
                                        mir_vm.DEFAULT_MEM_LIMIT,
                                        std.math.maxInt(u32),
                                    );
                                    if (file_stat.kind == .file and file_stat.size <= max_read_bytes) {
                                        if (std.Io.Dir.cwd().realPathFileAlloc(
                                            io_handle,
                                            full_path,
                                            self.allocator,
                                        )) |canon_target| {
                                            defer self.allocator.free(canon_target);
                                            if (mir_vm.isDirectCanonicalSubpath(canon_ws, canon_target, rel_path)) {
                                                const expected_size: usize = @intCast(file_stat.size);
                                                if (self.allocator.alloc(u8, expected_size)) |disk_bytes| {
                                                    defer self.allocator.free(disk_bytes);
                                                    if (opened_file.readPositionalAll(
                                                        io_handle,
                                                        disk_bytes,
                                                        0,
                                                    )) |actual_read| {
                                                        if (actual_read == expected_size) {
                                                            return Fingerprint128.hashBytes(disk_bytes);
                                                        }
                                                    } else |_| {}
                                                } else |_| {}
                                            }
                                        } else |_| {}
                                    }
                                } else |_| {}
                            } else |_| {}
                        } else |_| {}
                    } else |_| {}
                }
            }
        }
        var missing_hasher = StructuralHasher.init();
        missing_hasher.updateU8(0xEE);
        missing_hasher.updateBytes(rel_path);
        return missing_hasher.final();
    }

    /// Updates `--comptime-limit` (`comptime_step_limit`) and bumps `current_revision` when changed.
    pub fn setComptimeStepLimit(self: *CompilerDb, new_limit: u64) void {
        if (self.comptime_step_limit == new_limit) return;
        self.comptime_step_limit = new_limit;
        self.bumpConfigInput(CONFIG_KEY_COMPTIME_LIMIT);
    }

    /// Updates `target_layout` (`NATIVE_64` vs `WASM32`) and bumps `current_revision` when changed.
    pub fn setTargetLayout(self: *CompilerDb, new_layout: TargetLayout) void {
        if (self.target_layout.ptr_byte_size == new_layout.ptr_byte_size and
            self.target_layout.ptr_align_log2 == new_layout.ptr_align_log2)
        {
            return;
        }
        self.target_layout = new_layout;
        self.bumpConfigInput(CONFIG_KEY_TARGET_LAYOUT);
    }

    /// Updates `--sast-strict` (`is_sast_strict`) and bumps `current_revision` when changed.
    pub fn setSastStrict(self: *CompilerDb, is_strict: bool) void {
        if (self.is_sast_strict == is_strict) return;
        self.is_sast_strict = is_strict;
        self.bumpConfigInput(CONFIG_KEY_SAST_STRICT);
    }

    /// Configures the workspace root directory and optional in-memory VFS overlay for `@embed_bytes`.
    pub fn setEmbedSandbox(
        self: *CompilerDb,
        workspace_root: ?[]const u8,
        virtual_files: ?*const std.StringHashMapUnmanaged([]const u8),
    ) void {
        self.workspace_root = workspace_root;
        self.virtual_files = virtual_files;
        self.embed_sandbox_epoch +%= 1;
        self.bumpConfigInput(CONFIG_KEY_EMBED_SANDBOX);
    }

    /// Configures the optional `std.Io` handle used for disk-backed `@embed_bytes` inside `workspace_root`.
    pub fn setEmbedIo(self: *CompilerDb, io_handle: ?std.Io) void {
        self.embed_io = io_handle;
        self.embed_sandbox_epoch +%= 1;
        self.bumpConfigInput(CONFIG_KEY_EMBED_SANDBOX);
    }

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
                self.pure_call_memo_cache.clear();
            }

            self.current_revision = self.current_revision.next();
            const max_affected_tier: usize = @max(@backingInt(old_durability), @backingInt(durability));
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
        while (tier_idx <= @backingInt(durability)) : (tier_idx += 1) {
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

    // ---------- Public 14-Stage Demand-Driven Query API -----------

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

    /// Stage 9 summary firewall: fetches `def_id`'s 40-byte `FnRegionSummary` gated by its 34 caller-observable bytes.
    pub fn getSastSummaryProj(self: *CompilerDb, def_id: DefId) QueryError!mir_sast.FnRegionSummary {
        _ = try self.fetchQuery(QueryKey.forSastSummaryProj(def_id));
        return self.sast_summaries.get(def_id.asInt()) orelse .{};
    }

    /// Inspects the cached Stage 9 `FnRegionSummary` for `def_id` without triggering execution.
    pub inline fn getSastSummary(self: *const CompilerDb, def_id: DefId) ?mir_sast.FnRegionSummary {
        return self.sast_summaries.get(def_id.asInt());
    }

    /// Stage 10: Lowers a single `def_id` into an owned `HirStore` (`[CRITICAL-11]` per-`DefId` firewall).
    pub fn lowerDefHir(self: *CompilerDb, def_id: DefId) QueryError!*const hir.HirStore {
        _ = try self.fetchQuery(QueryKey.forDef(.lower_def_hir, def_id));
        return self.lowered_def_hirs.getPtr(def_id.asInt()) orelse error.InvalidDefId;
    }

    /// Stage 11: Builds and `V1`–`V6` verifies the `DefMirArtifact` for `def_id`.
    pub fn buildDefMirArtifact(self: *CompilerDb, def_id: DefId) QueryError!*const DefMirArtifact {
        _ = try self.fetchQuery(QueryKey.forDef(.build_def_mir, def_id));
        return self.built_def_mirs.getPtr(def_id.asInt()) orelse error.InvalidDefId;
    }

    /// Stage 11 convenience wrapper returning the primary `MirBody` for `def_id` (`null` for type-only defs).
    pub fn buildDefMir(self: *CompilerDb, def_id: DefId) QueryError!?*const mir.MirBody {
        return (try self.buildDefMirArtifact(def_id)).primaryBody();
    }

    /// Returns drop-elaborated `MirBody` records for `def_id` for `MirVm` `comptime` execution (`[CRITICAL-04]`).
    pub fn getComptimeElaboratedMirBodies(
        self: *CompilerDb,
        def_id: DefId,
    ) QueryError![]const mir.MirBody {
        const mir_art = try self.buildDefMirArtifact(def_id);
        if (mir_art.bundle.bodies.items.len == 0) return &.{};

        if (self.comptime_elab_mirs.getPtr(def_id.asInt())) |cached_ptr| {
            if (Fingerprint128.eql(cached_ptr.source_mir_fp, mir_art.mir_fingerprint)) {
                return cached_ptr.bundle.bodies.items;
            }
        }

        var elab_bundle = mir.MirModuleBundle{ .allocator = self.allocator };
        errdefer elab_bundle.deinit();
        for (mir_art.bundle.bodies.items) |*src_body| {
            var dup_body = src_body.clone(self.allocator) catch return error.OutOfMemory;
            errdefer dup_body.deinit();
            try elab_bundle.bodies.append(self.allocator, dup_body);
        }

        const file_id = def_id.fileId();
        const src_opt = if (self.source_inputs.getPtr(file_id.asInt())) |in_ptr| in_ptr.owned_text else null;
        const parsed_opt = self.parsed_artifacts.getPtr(file_id.asInt());
        var scratch_sink = DiagnosticSink.init(self.allocator);
        defer scratch_sink.deinit();

        const elab_ok = if (mir_sast.analyzeAndElaborateMirModule(
            self.allocator,
            elab_bundle.bodies.items,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
            .{
                .diagnostic_sink = &scratch_sink,
                .is_comptime_context = false,
                .source_text = src_opt,
                .token_buffer = if (parsed_opt) |pp| &pp.token_buffer else null,
                .cst_arena = if (parsed_opt) |pp| &pp.cst_arena else null,
                .external_resolver = .{
                    .compiler_db = self,
                    .resolve_fn = resolveDbCalleeSummary,
                },
            },
        )) |elab_res_val| blk: {
            var elab_res = elab_res_val;
            elab_res.deinit();
            break :blk scratch_sink.error_count == 0;
        } else |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            else => false,
        };

        if (!elab_ok) {
            elab_bundle.deinit();
            return mir_art.bundle.bodies.items;
        }

        const entry = ComptimeElabMirEntry{
            .source_mir_fp = mir_art.mir_fingerprint,
            .bundle = elab_bundle,
        };
        if (try self.comptime_elab_mirs.fetchPut(self.allocator, def_id.asInt(), entry)) |prev_kv| {
            var old_entry = prev_kv.value;
            old_entry.deinit();
        }
        return self.comptime_elab_mirs.getPtr(def_id.asInt()).?.bundle.bodies.items;
    }

    /// Stage 12: Evaluates `def_id` in `MirVm`, promotes to `.rodata`, and emits `E0509` on evaluation cycles.
    pub fn evalComptimeDef(self: *CompilerDb, def_id: DefId) QueryError!ComptimeEvalArtifact {
        _ = self.fetchQuery(QueryKey.forDef(.eval_comptime_def, def_id)) catch |err| {
            if (err == error.DependencyCycle) {
                try self.emitComptimeCycleDiagnostic(def_id);
            }
            return err;
        };
        return self.evaluated_comptime_defs.get(def_id.asInt()) orelse error.InvalidDefId;
    }

    /// Stage 13: Runs the `--dev` (`D1`–`D5`) or `--release` (`D1`–`D5` + `R1`–`R6`) `MIR` pipeline on `file_id`.
    pub fn optimizeMirModule(
        self: *CompilerDb,
        file_id: FileId,
        is_release_mode: bool,
    ) QueryError!*const mir_opt.MirOptModuleResult {
        const key = QueryKey.forFileMode(.optimize_mir_module, file_id, is_release_mode);
        _ = try self.fetchQuery(key);
        return self.optimized_mir_modules.getPtr(key.asU64()) orelse error.MissingSourceInput;
    }

    /// Bridge invoked by `mir_vm.makeComptimeEvalHook` to resolve cross-definition `const` `DefId`s.
    pub fn evalComptimeDefValue(
        self: *CompilerDb,
        def_id: DefId,
        sink: ?*DiagnosticSink,
    ) QueryError!?hir.ComptimeValue {
        const artifact = self.evalComptimeDef(def_id) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            error.DependencyCycle => {
                if (sink) |out_sink| {
                    try self.emitComptimeCycleIntoSink(out_sink, def_id);
                }
                return error.DependencyCycle;
            },
            error.MissingSourceInput, error.InvalidDefId => return null,
        };
        if (artifact.has_errors) return null;
        return artifact.value;
    }

    /// Bridge invoked by `mir_vm.makeComptimeEvalHook` to evaluate Tier-2 `HIR` subtrees via `MirVm`.
    pub fn evalHirExprInVm(
        self: *CompilerDb,
        mutable_store: *hir.HirStore,
        hir_id: HirIndex,
        expected_ty: TypeId,
        sink: ?*DiagnosticSink,
    ) QueryError!?hir.ComptimeValue {
        var file_tokens: std.AutoHashMapUnmanaged(u32, *const TokenBuffer) = .empty;
        defer file_tokens.deinit(self.allocator);
        try self.populateFileTokensMap(&file_tokens);

        const vm_opts = try self.makeVmExecOptions(&file_tokens);
        return mir_vm.evalHirSubtreeWithMirVm(
            self.allocator,
            mutable_store,
            hir_id,
            expected_ty,
            &self.interner,
            &self.type_pool,
            &self.symbol_table,
            &self.rodata_pool,
            &self.pure_call_memo_cache,
            sink,
            vm_opts,
            mutable_store,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            error.EvaluationCycle => return error.DependencyCycle,
        };
    }

    /// Bridge invoked by `MirVm` `.fn_addr` when loading a global `const` symbol on demand (`E0509` on cycle).
    pub fn loadEvaluatedConstInVm(
        self: *CompilerDb,
        vm: *mir_vm.MirVm,
        target_def: DefId,
        expected_ty: TypeId,
    ) mir_vm.VmEvalError!mir_vm.RegSlot {
        const artifact = self.evalComptimeDef(target_def) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            error.DependencyCycle => {
                return vm.failWithTrap(
                    error.EvaluationCycle,
                    .e0509_comptime_evaluation_cycle,
                    "cyclic compile-time constant evaluation detected",
                    "cycle re-entered here",
                    null,
                );
            },
            error.MissingSourceInput, error.InvalidDefId => return error.UnresolvedCallee,
        };
        if (artifact.has_errors or artifact.rodata_id.isNone()) {
            return error.UnresolvedCallee;
        }
        const load_ty = if (!expected_ty.isError()) expected_ty else artifact.type_id;
        return vm.loadTypedSlotFromMemory(.{ .alloc_id = artifact.rodata_id, .byte_offset = 0 }, load_ty);
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

        // [1] Input queries (`.source_text`, synthetic config keys, and `@embed_bytes` file keys):
        if (key.stage == .source_text) {
            if ((key.flags & EMBED_FILE_KEY_FLAG) != 0) {
                if (memo_snapshot.verified_at != self.current_revision) {
                    const live_fp = self.probeEmbeddedFileFingerprint(SymbolId.fromInt(key.entity_index));
                    var effective_changed_at = memo_snapshot.changed_at;
                    if (!Fingerprint128.eql(live_fp, memo_snapshot.output_fingerprint)) {
                        effective_changed_at = self.current_revision;
                        self.pure_call_memo_cache.clear();
                    }
                    if (self.memos.getPtr(key.asU64())) |memo_ptr| {
                        memo_ptr.output_fingerprint = live_fp;
                        memo_ptr.changed_at = effective_changed_at;
                        memo_ptr.verified_at = self.current_revision;
                    }
                    return effective_changed_at.isAfter(after_revision);
                }
                return memo_snapshot.changed_at.isAfter(after_revision);
            }
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

        // [2.5] Conservative Red Path if direct dependency count exceeded `MAX_DEPS_PER_MEMO` (`[MAJOR-18]`):
        if (memo_snapshot.has_overflowed_deps) {
            const updated_memo = try self.executeAndBackdate(key);
            return updated_memo.changed_at.isAfter(after_revision);
        }

        // [3] Durability Fast-Path: if no input at `>= memo_snapshot.min_durability` changed since `last_verified`:
        var has_durability_change = false;
        var tier_idx: usize = @backingInt(memo_snapshot.min_durability);
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
            if ((key.flags & EMBED_FILE_KEY_FLAG) != 0) {
                const live_fp = self.probeEmbeddedFileFingerprint(SymbolId.fromInt(key.entity_index));
                const embed_memo = MemoHeader{
                    .output_fingerprint = live_fp,
                    .verified_at = self.current_revision,
                    .changed_at = self.current_revision,
                    .dep_edge_start = 0,
                    .dep_edge_len = 0,
                    .min_durability = .low,
                    .is_pure_high_durability = false,
                    .artifact_index = key.entity_index,
                };
                try self.memos.put(self.allocator, key.asU64(), embed_memo);
                return embed_memo;
            }
            if (key.entity_index >= CONFIG_KEY_TARGET_LAYOUT and
                key.entity_index <= CONFIG_KEY_SAST_STRICT)
            {
                const cfg_slot = key.entity_index - CONFIG_KEY_TARGET_LAYOUT;
                const cfg_memo = MemoHeader{
                    .output_fingerprint = self.computeConfigFingerprint(key.entity_index),
                    .verified_at = self.current_revision,
                    .changed_at = self.config_changed_at[cfg_slot],
                    .dep_edge_start = 0,
                    .dep_edge_len = 0,
                    .min_durability = .high,
                    .is_pure_high_durability = true,
                    .artifact_index = key.entity_index,
                };
                try self.memos.put(self.allocator, key.asU64(), cfg_memo);
                return cfg_memo;
            }
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
        self.telemetry.stage_executions[@backingInt(key.stage)] += 1;

        if (self.custom_stage_hook) |hook_fn| {
            try hook_fn(self, key);
        }

        const computed_fp = try self.computeStage(key);
        const frame = self.active_stack.items[self.active_stack.items.len - 1];
        const recorded_slice = self.scratch_dep_edges.items[start_dep_index..];
        const has_overflowed_deps = recorded_slice.len > MAX_DEPS_PER_MEMO;
        const clamped_len: u16 = if (has_overflowed_deps) 0 else @intCast(recorded_slice.len);

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
            .min_durability = if (has_overflowed_deps) .low else frame.min_durability,
            .is_pure_high_durability = if (has_overflowed_deps) false else frame.is_pure_high_durability,
            .artifact_index = key.entity_index,
            .has_overflowed_deps = has_overflowed_deps,
        };
        try self.memos.put(self.allocator, key.asU64(), new_memo);
        return new_memo;
    }

    /// Appends `dep_key` to the active frame's scratch dependency list if not already recorded.
    fn recordDependencyEdge(self: *CompilerDb, dep_key: QueryKey) !void {
        const frame = &self.active_stack.items[self.active_stack.items.len - 1];
        const cur_slice = self.scratch_dep_edges.items[frame.start_dep_index..];
        if (cur_slice.len > MAX_DEPS_PER_MEMO) return;
        for (cur_slice) |existing_dep| {
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
                if ((key.flags & EMBED_FILE_KEY_FLAG) != 0) {
                    break :blk self.probeEmbeddedFileFingerprint(SymbolId.fromInt(key.entity_index));
                }
                if (key.entity_index >= CONFIG_KEY_TARGET_LAYOUT and
                    key.entity_index <= CONFIG_KEY_SAST_STRICT)
                {
                    break :blk self.computeConfigFingerprint(key.entity_index);
                }
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
            .verify_sast_mir => self.computeVerifySastMirKey(key),
            .lower_def_hir => self.computeLowerDefHir(DefId.fromInt(key.entity_index)),
            .build_def_mir => self.computeBuildDefMir(DefId.fromInt(key.entity_index)),
            .eval_comptime_def => self.computeEvalComptimeDef(DefId.fromInt(key.entity_index)),
            .optimize_mir_module => self.computeOptimizeMirModule(
                FileId.fromInt(key.entity_index),
                (key.flags & 1) != 0,
            ),
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
        // Keep module-symbol `ast_node`/`cst_node` synchronized when `resolveSignatures` hits Early Cutoff:
        for (new_tree.entries) |entry| {
            if (self.symbol_table.def_to_symbol.get(entry.def_id.asInt())) |sym_idx| {
                if (!sym_idx.isNone()) {
                    const sym_mut = self.symbol_table.getSymbolMut(sym_idx);
                    sym_mut.ast_node = entry.ast_node;
                    sym_mut.cst_node = entry.cst_node;
                }
            }
        }
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

    /// Returns the signature resolution `DiagnosticSink` for `file_id` if available.
    pub fn getSignatureDiagnostics(self: *const CompilerDb, file_id: FileId) ?*const DiagnosticSink {
        return self.sig_diagnostics.getPtr(file_id.asInt());
    }

    /// Returns the body type-checking `DiagnosticSink` for `def_id` if available.
    pub fn getBodyDiagnostics(self: *const CompilerDb, def_id: DefId) ?*const DiagnosticSink {
        return self.body_diagnostics.getPtr(def_id.asInt());
    }

    /// Returns the Stage 9 `MIR` SAST `DiagnosticSink` for `def_id` if available.
    pub fn getSastDiagnostics(self: *const CompilerDb, def_id: DefId) ?*const DiagnosticSink {
        return self.sast_diagnostics.getPtr(def_id.asInt());
    }

    /// Returns the `HIR` lowering `DiagnosticSink` for `def_id` if available.
    pub fn getHirDiagnostics(self: *const CompilerDb, def_id: DefId) ?*const DiagnosticSink {
        return self.hir_diagnostics.getPtr(def_id.asInt());
    }

    /// Returns the `MIR` lowering & verification `DiagnosticSink` for `def_id` if available.
    pub fn getMirDiagnostics(self: *const CompilerDb, def_id: DefId) ?*const DiagnosticSink {
        return self.mir_diagnostics.getPtr(def_id.asInt());
    }

    /// Returns the `MirVm` compile-time evaluation `DiagnosticSink` for `def_id` if available.
    pub fn getComptimeDiagnostics(self: *const CompilerDb, def_id: DefId) ?*const DiagnosticSink {
        return self.comptime_diagnostics.getPtr(def_id.asInt());
    }

    /// Returns the `MIR` optimization `DiagnosticSink` for `(file_id, is_release_mode)` if available.
    pub fn getOptimizedMirDiagnostics(
        self: *const CompilerDb,
        file_id: FileId,
        is_release_mode: bool,
    ) ?*const DiagnosticSink {
        const key = QueryKey.forFileMode(.optimize_mir_module, file_id, is_release_mode);
        return self.opt_diagnostics.getPtr(key.asU64());
    }

    /// Resets or creates a `u32`-keyed `DiagnosticSink` in `sink_map`.
    fn resetOrCreateDefDiagSink(
        sink_map: *std.AutoHashMapUnmanaged(u32, DiagnosticSink),
        allocator: std.mem.Allocator,
        raw_key: u32,
    ) !*DiagnosticSink {
        const gop = try sink_map.getOrPut(allocator, raw_key);
        if (!gop.found_existing) {
            gop.value_ptr.* = DiagnosticSink.init(allocator);
        } else {
            gop.value_ptr.diagnostics.clearRetainingCapacity();
            gop.value_ptr.arena.resetRetainingCapacity();
            gop.value_ptr.error_count = 0;
            gop.value_ptr.warning_count = 0;
            gop.value_ptr.has_reached_limit = false;
        }
        return gop.value_ptr;
    }

    /// Resets or creates a `u64`-keyed `DiagnosticSink` in `sink_map`.
    fn resetOrCreateModeDiagSink(
        sink_map: *std.AutoHashMapUnmanaged(u64, DiagnosticSink),
        allocator: std.mem.Allocator,
        raw_key: u64,
    ) !*DiagnosticSink {
        const gop = try sink_map.getOrPut(allocator, raw_key);
        if (!gop.found_existing) {
            gop.value_ptr.* = DiagnosticSink.init(allocator);
        } else {
            gop.value_ptr.diagnostics.clearRetainingCapacity();
            gop.value_ptr.arena.resetRetainingCapacity();
            gop.value_ptr.error_count = 0;
            gop.value_ptr.warning_count = 0;
            gop.value_ptr.has_reached_limit = false;
        }
        return gop.value_ptr;
    }

    /// Populates `out_map` with `(file_id -> &parsed.token_buffer)` across all parsed files in `self`.
    fn populateFileTokensMap(
        self: *const CompilerDb,
        out_map: *std.AutoHashMapUnmanaged(u32, *const TokenBuffer),
    ) !void {
        var iter = self.parsed_artifacts.iterator();
        while (iter.next()) |kv| {
            try out_map.put(self.allocator, kv.key_ptr.*, &kv.value_ptr.token_buffer);
        }
    }

    /// Constructs `mir_vm.VmExecOptions` inheriting `self`'s tracked limits, target layout, and VFS sandbox.
    fn makeVmExecOptions(
        self: *CompilerDb,
        file_tokens: ?*const std.AutoHashMapUnmanaged(u32, *const TokenBuffer),
    ) QueryError!mir_vm.VmExecOptions {
        const active_step_limit = try self.readComptimeStepLimit();
        const active_layout = try self.readTargetLayout();
        return .{
            .step_budget = active_step_limit,
            .target_layout = active_layout,
            .workspace_root = self.workspace_root,
            .io = self.embed_io,
            .virtual_files = self.virtual_files,
            .file_tokens = file_tokens,
            .compiler_db = self,
        };
    }

    /// Emits `E0509` (`e0509_comptime_evaluation_cycle`) into `sink` for `def_id`.
    fn emitComptimeCycleIntoSink(
        self: *const CompilerDb,
        sink: *DiagnosticSink,
        def_id: DefId,
    ) !void {
        var cycle_span = Span.init(def_id.fileId(), 0, 0);
        if (self.symbol_table.def_to_symbol.get(def_id.asInt())) |sym_idx| {
            if (!sym_idx.isNone()) {
                cycle_span = self.symbol_table.getSymbol(sym_idx).decl_span;
            }
        }
        const primary_label = LabeledSpan{
            .span = cycle_span,
            .label = "constant evaluation cycle involves this definition",
            .style = .primary,
        };
        try sink.emit(.{
            .code = .e0509_comptime_evaluation_cycle,
            .severity = .err,
            .primary_span = cycle_span,
            .message = "cyclic compile-time constant evaluation detected",
            .labels = (&primary_label)[0..1],
        });
    }

    /// Emits `E0509` (`e0509_comptime_evaluation_cycle`) into `comptime_diagnostics[def_id]`.
    fn emitComptimeCycleDiagnostic(self: *CompilerDb, def_id: DefId) !void {
        const sink = try resetOrCreateDefDiagSink(
            &self.comptime_diagnostics,
            self.allocator,
            def_id.asInt(),
        );
        try self.emitComptimeCycleIntoSink(sink, def_id);
    }

    /// Stage 6 implementation: resolves module signatures for `file_id` (shielded by `tree_fingerprint`).
    fn computeResolveSignatures(self: *CompilerDb, file_id: FileId) QueryError!Fingerprint128 {
        const item_tree = try self.extractItemTree(file_id);
        const active_layout = try self.readTargetLayout();
        try self.unwindIfCancelled();

        var hasher = StructuralHasher.init();
        hasher.updateU32(file_id.asInt());
        hasher.updateU8(active_layout.ptr_byte_size);
        hasher.updateFingerprint(item_tree.tree_fingerprint);

        var public_count: u32 = 0;
        for (item_tree.entries) |entry| {
            const sig_fp = try self.getItemTreeSigProj(entry.def_id);
            hasher.updateFingerprint(sig_fp);
            if (entry.is_pub) public_count += 1;
        }

        // Run Phase 4 symbol collection, `use` resolution, and signature type resolution for `file_id`:
        var mod_scope: ScopeId = .none;
        var sig_err_count: u32 = 0;
        if (self.source_inputs.getPtr(file_id.asInt())) |input_ptr| {
            if (self.parsed_artifacts.getPtr(file_id.asInt())) |parsed_ptr| {
                const sig_sink = try resetOrCreateDefDiagSink(
                    &self.sig_diagnostics,
                    self.allocator,
                    file_id.asInt(),
                );

                // Detach previous module scope for `file_id` so re-runs allocate a clean scope:
                _ = self.symbol_table.file_module_scopes.remove(file_id.asInt());

                mod_scope = symbol_resolver.collectFileModuleItems(
                    &self.symbol_table,
                    &self.interner,
                    file_id,
                    input_ptr.owned_text,
                    &parsed_ptr.token_buffer,
                    &parsed_ptr.cst_arena,
                    &parsed_ptr.ast_arena,
                    sig_sink,
                ) catch return error.OutOfMemory;

                symbol_resolver.resolveFileUseImports(
                    &self.symbol_table,
                    &self.interner,
                    file_id,
                    input_ptr.owned_text,
                    &parsed_ptr.token_buffer,
                    &parsed_ptr.cst_arena,
                    sig_sink,
                ) catch return error.OutOfMemory;

                var checker = TypeChecker.init(
                    self.allocator,
                    &self.interner,
                    &self.type_pool,
                    &self.symbol_table,
                    file_id,
                    input_ptr.owned_text,
                    &parsed_ptr.token_buffer,
                    &parsed_ptr.cst_arena,
                    &parsed_ptr.ast_arena,
                    sig_sink,
                ) catch return error.OutOfMemory;
                defer checker.deinit();
                checker.db = self;
                checker.target_layout = active_layout;
                checker.is_stdlib_file = (input_ptr.durability == .high);

                checker.resolveModuleSignatures() catch return error.OutOfMemory;
                sig_err_count = sig_sink.error_count;

                var file_st = checker.extractFileSemanticSideTables(self.allocator) catch
                    return error.OutOfMemory;
                errdefer file_st.deinit();
                if (try self.file_side_tables.fetchPut(self.allocator, file_id.asInt(), file_st)) |prev_kv| {
                    var old_st = prev_kv.value;
                    old_st.deinit();
                }
            }
        }

        const resolved_fp = hasher.final();
        try self.resolved_signatures.put(self.allocator, file_id.asInt(), .{
            .file_id = file_id,
            .module_scope = mod_scope,
            .item_count = @intCast(item_tree.entries.len),
            .public_item_count = public_count,
            .error_count = sig_err_count,
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

        const sym_idx = self.symbol_table.def_to_symbol.get(def_id.asInt()) orelse .none;
        const resolved_ty: TypeId = if (!sym_idx.isNone())
            self.symbol_table.getSymbol(sym_idx).type_id
        else
            .err_ty;

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateU8(@backingInt(entry.kind));
        hasher.updateU8(if (entry.is_pub) 1 else 0);
        hasher.updateU32(entry.name_symbol.asInt());
        hasher.updateU32(resolved_ty.toU32());
        hasher.updateFingerprint(item_sig_fp);
        const def_sig_fp = hasher.final();

        try self.def_signatures.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .kind = entry.kind,
            .is_pub = entry.is_pub,
            .name_symbol = entry.name_symbol,
            .symbol_index = sym_idx,
            .type_id = resolved_ty,
            .signature_fingerprint = def_sig_fp,
        });
        return def_sig_fp;
    }

    /// Stage 8 implementation: type-checks `def_id`'s body in isolation from sibling definitions.
    fn computeTypecheckBody(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const def_sig = try self.getDefSignature(def_id);
        const body_window = try self.getBodyAstProj(def_id);
        const active_layout = try self.readTargetLayout();
        try self.unwindIfCancelled();

        const file_id = def_id.fileId();
        var body_err_count: u32 = 0;
        var body_warn_count: u32 = 0;

        if (self.source_inputs.getPtr(file_id.asInt())) |input_ptr| {
            if (self.parsed_artifacts.getPtr(file_id.asInt())) |parsed_ptr| {
                const body_sink = try resetOrCreateDefDiagSink(
                    &self.body_diagnostics,
                    self.allocator,
                    def_id.asInt(),
                );

                var checker = TypeChecker.init(
                    self.allocator,
                    &self.interner,
                    &self.type_pool,
                    &self.symbol_table,
                    file_id,
                    input_ptr.owned_text,
                    &parsed_ptr.token_buffer,
                    &parsed_ptr.cst_arena,
                    &parsed_ptr.ast_arena,
                    body_sink,
                ) catch return error.OutOfMemory;
                defer checker.deinit();
                checker.db = self;
                checker.target_layout = active_layout;
                checker.is_stdlib_file = (input_ptr.durability == .high);

                checker.checkDefBody(def_id) catch return error.OutOfMemory;
                body_err_count = body_sink.error_count;
                body_warn_count = body_sink.warning_count;

                var body_st = checker.extractBodySemanticSideTables(self.allocator, def_id) catch
                    return error.OutOfMemory;
                errdefer body_st.deinit();

                // Propagate module-level `@attribute_schema` instances so `@field_attr_lookup` sees nominal attrs:
                if (self.file_side_tables.getPtr(file_id.asInt())) |file_st| {
                    if (file_st.attr_instances.len > 0) {
                        var merged_attrs: std.ArrayListUnmanaged(type_system.AttrInstance) = .empty;
                        errdefer {
                            for (merged_attrs.items) |attr_item| {
                                if (attr_item.fields.len > 0) self.allocator.free(attr_item.fields);
                            }
                            merged_attrs.deinit(self.allocator);
                        }
                        for (body_st.attr_instances) |existing_attr| {
                            const duped = self.allocator.dupe(
                                type_system.AttrFieldInit,
                                existing_attr.fields,
                            ) catch return error.OutOfMemory;
                            var cloned = existing_attr;
                            cloned.fields = duped;
                            merged_attrs.append(self.allocator, cloned) catch {
                                if (duped.len > 0) self.allocator.free(duped);
                                return error.OutOfMemory;
                            };
                        }
                        for (file_st.attr_instances) |mod_attr| {
                            if (mod_attr.owner_def_id == def_id) continue;
                            const duped = self.allocator.dupe(
                                type_system.AttrFieldInit,
                                mod_attr.fields,
                            ) catch return error.OutOfMemory;
                            var cloned = mod_attr;
                            cloned.fields = duped;
                            merged_attrs.append(self.allocator, cloned) catch {
                                if (duped.len > 0) self.allocator.free(duped);
                                return error.OutOfMemory;
                            };
                        }
                        for (body_st.attr_instances) |old_attr| {
                            if (old_attr.fields.len > 0) self.allocator.free(old_attr.fields);
                        }
                        if (body_st.attr_instances.len > 0) self.allocator.free(body_st.attr_instances);
                        body_st.attr_instances = merged_attrs.toOwnedSlice(self.allocator) catch
                            return error.OutOfMemory;
                    }
                }

                if (try self.def_side_tables.fetchPut(self.allocator, def_id.asInt(), body_st)) |prev_kv| {
                    var old_st = prev_kv.value;
                    old_st.deinit();
                }
            }
        }

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateU8(active_layout.ptr_byte_size);
        hasher.updateFingerprint(def_sig.signature_fingerprint);
        hasher.updateFingerprint(body_window.body_fingerprint);
        const typed_fp = hasher.final();

        try self.typed_bodies.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .file_id = file_id,
            .body_ast_node = body_window.body_ast_node,
            .error_count = body_err_count,
            .warning_count = body_warn_count,
            .signature_fingerprint = def_sig.signature_fingerprint,
            .body_fingerprint = body_window.body_fingerprint,
            .typed_fingerprint = typed_fp,
        });
        return typed_fp;
    }

    /// Constructs a fail-closed conservative `FnRegionSummary` for an in-flight mutual-recursion cycle (`[CRITICAL-03]`).
    fn makeConservativeCycleSummary(
        db: *const CompilerDb,
        target_def: DefId,
        callee_sym: SymbolIndex,
    ) mir_sast.FnRegionSummary {
        var summary = mir_sast.FnRegionSummary{
            .ret_provenance_mask = std.math.maxInt(u64),
            .param_flow_matrix = std.math.maxInt(u64),
            .global_escape_mask = std.math.maxInt(u32),
            .max_subtree_bytes = mir_sast.FnRegionSummary.STACK_UNBOUNDED,
            .direct_effects_bits = 0x0FFF,
            .inferred_effects_bits = 0x0FFF,
        };
        var cs_mask = mir_sast.FnContractScratchMask{
            .is_scc_recursive = true,
            .scratch_touch_mask = 0b11,
            .scratch_rewind_mask = 0b11,
        };
        var resolved_sym = callee_sym;
        if (resolved_sym.isNone() and !target_def.isNone()) {
            resolved_sym = db.symbol_table.def_to_symbol.get(target_def.asInt()) orelse .none;
        }
        if (!resolved_sym.isNone() and resolved_sym.asInt() < db.symbol_table.symbols.items.len) {
            const srec = db.symbol_table.getSymbol(resolved_sym).*;
            cs_mask.has_no_alloc = srec.contract_flags.is_no_alloc;
            cs_mask.has_no_panic = srec.contract_flags.is_no_panic;
            cs_mask.has_no_block = srec.contract_flags.is_no_block;
            cs_mask.has_max_stack_attr = srec.contract_flags.has_max_stack;
        }
        summary.setContractsScratch(cs_mask);
        return summary;
    }

    /// Records all `.verify_sast_mir` participants on `active_stack` from `target_def` upward as mutual-recursion peers.
    fn recordSastCycleOnActiveStack(db: *CompilerDb, target_def: DefId) !void {
        var cycle_start: ?usize = null;
        for (db.active_stack.items, 0..) |frame, idx| {
            if (frame.key.stage == .verify_sast_mir and frame.key.entity_index == target_def.asInt()) {
                cycle_start = idx;
                break;
            }
        }
        const start_idx = cycle_start orelse return;

        var participants: std.ArrayListUnmanaged(DefId) = .empty;
        defer participants.deinit(db.allocator);
        for (db.active_stack.items[start_idx..]) |frame| {
            if (frame.key.stage != .verify_sast_mir) continue;
            const p_def = DefId.fromInt(frame.key.entity_index);
            if (p_def.isNone()) continue;
            var is_existing = false;
            for (participants.items) |existing| {
                if (existing == p_def) {
                    is_existing = true;
                    break;
                }
            }
            if (!is_existing) try participants.append(db.allocator, p_def);
        }

        for (participants.items) |owner_def| {
            const gop = try db.sast_cycle_peers.getOrPut(db.allocator, owner_def.asInt());
            if (!gop.found_existing) {
                gop.value_ptr.* = .empty;
            }
            for (participants.items) |peer_def| {
                if (peer_def == owner_def) continue;
                var is_already_recorded = false;
                for (gop.value_ptr.items) |existing_peer| {
                    if (existing_peer == peer_def) {
                        is_already_recorded = true;
                        break;
                    }
                }
                if (!is_already_recorded) {
                    try gop.value_ptr.append(db.allocator, peer_def);
                }
            }
        }
    }

    /// Resolves cross-`DefId` `FnRegionSummary` dependencies via `getSastSummaryProj` (34-byte Early Cutoff).
    fn resolveDbCalleeSummary(
        compiler_db_opt: ?*CompilerDb,
        summary_map_opt: ?*const std.AutoHashMapUnmanaged(u32, mir_sast.FnRegionSummary),
        callee_def: DefId,
        callee_sym: SymbolIndex,
    ) QueryError!?mir_sast.FnRegionSummary {
        if (summary_map_opt) |smap| {
            if (!callee_def.isNone()) {
                if (smap.get(callee_def.asInt())) |found_sum| return found_sum;
            }
        }
        const db = compiler_db_opt orelse return null;
        var target_def = callee_def;
        if (!callee_sym.isNone() and callee_sym.asInt() < db.symbol_table.symbols.items.len) {
            const sym_rec = db.symbol_table.getSymbol(callee_sym).*;
            if (sym_rec.flags.is_extern or sym_rec.flags.is_prototype_only) return null;
            if (target_def.isNone()) {
                target_def = if (!sym_rec.def_id.isNone()) sym_rec.def_id else sym_rec.owner_def_id;
            }
        }
        if (target_def.isNone()) return null;

        if (db.def_signatures.get(target_def.asInt())) |dsig| {
            if (dsig.kind == .extern_block) return null;
        }

        // Detect cross-`DefId` mutual recursion before recording a cyclic edge in `dep_edges`:
        if (db.in_flight_keys.contains(QueryKey.forDef(.verify_sast_mir, target_def).asU64()) or
            db.in_flight_keys.contains(QueryKey.forSastSummaryProj(target_def).asU64()))
        {
            recordSastCycleOnActiveStack(db, target_def) catch return error.OutOfMemory;
            return makeConservativeCycleSummary(db, target_def, callee_sym);
        }

        const def_summary = db.getSastSummaryProj(target_def) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            error.DependencyCycle => {
                recordSastCycleOnActiveStack(db, target_def) catch return error.OutOfMemory;
                return makeConservativeCycleSummary(db, target_def, callee_sym);
            },
            error.MissingSourceInput, error.InvalidDefId => return null,
        };
        if (!callee_sym.isNone()) {
            if (db.sast_sym_summaries.get(callee_sym.asInt())) |method_sum| {
                return method_sum;
            }
        }
        return def_summary;
    }

    /// Lowers clean pre-SAST `MirBody` records for `target_def` into `out_bodies` for Stage 9 SAST analysis.
    fn appendCleanSastBodiesForDef(
        self: *CompilerDb,
        target_def: DefId,
        active_layout: TargetLayout,
        out_bodies: *std.ArrayListUnmanaged(mir.MirBody),
        out_is_comptime: *bool,
    ) QueryError!void {
        const target_file = target_def.fileId();
        const parsed_ptr = self.parsed_artifacts.getPtr(target_file.asInt()) orelse return;
        const input_ptr = self.source_inputs.getPtr(target_file.asInt()) orelse return;

        if (self.body_windows.get(target_def.asInt())) |body_window| {
            try self.syncDefWindowAndSideTables(target_def, parsed_ptr, body_window.item_ast_node);
        } else if (self.item_trees.getPtr(target_file.asInt())) |tree_ptr| {
            if (tree_ptr.getEntry(target_def)) |entry| {
                try self.syncDefWindowAndSideTables(target_def, parsed_ptr, entry.ast_node);
            }
        }

        var hir_scratch_sink = DiagnosticSink.init(self.allocator);
        defer hir_scratch_sink.deinit();
        const eval_hook = mir_vm.makeComptimeEvalHook(self, target_def.asInt());

        var store = hir.lowerDefToHir(
            self.allocator,
            target_def,
            input_ptr.owned_text,
            &parsed_ptr.token_buffer,
            &parsed_ptr.cst_arena,
            &parsed_ptr.ast_arena,
            &self.interner,
            &self.type_pool,
            &self.symbol_table,
            self.def_side_tables.getPtr(target_def.asInt()),
            &hir_scratch_sink,
            active_layout,
            eval_hook,
        ) catch |err| switch (err) {
            error.Cancelled => return error.Cancelled,
            error.DependencyCycle => return error.DependencyCycle,
            error.MissingSourceInput => return error.MissingSourceInput,
            error.InvalidDefId => return error.InvalidDefId,
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.OutOfMemory,
        };
        defer store.deinit();
        if (hir_scratch_sink.error_count != 0) return;

        var mir_scratch_sink = DiagnosticSink.init(self.allocator);
        defer mir_scratch_sink.deinit();

        var bundle = mir.lowerHirToMirForSast(
            self.allocator,
            &store,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
            &mir_scratch_sink,
        ) catch return error.OutOfMemory;
        defer bundle.deinit();

        const def_sig_opt = self.def_signatures.get(target_def.asInt());
        if (!store.root_hir.isNone() and store.root_hir.asInt() < store.nodes.len) {
            const root_node = store.getNode(store.root_hir);
            if (root_node.tag == .hir_const_decl) {
                const init_hir = HirIndex.fromInt(root_node.data.rhs);
                if (!init_hir.isNone()) {
                    var init_body = lowerInitializerHirToMirBody(
                        self.allocator,
                        target_def,
                        &store,
                        init_hir,
                        root_node.type_id,
                        &self.type_pool,
                        &self.symbol_table,
                        &self.interner,
                        &mir_scratch_sink,
                    ) catch return error.OutOfMemory;
                    errdefer init_body.deinit();
                    try bundle.bodies.append(self.allocator, init_body);
                    out_is_comptime.* = true;
                }
            } else if (def_sig_opt != null and
                def_sig_opt.?.kind == .extern_block and
                root_node.tag == .hir_block)
            {
                var blk_body = lowerInitializerHirToMirBody(
                    self.allocator,
                    target_def,
                    &store,
                    store.root_hir,
                    .unit_ty,
                    &self.type_pool,
                    &self.symbol_table,
                    &self.interner,
                    &mir_scratch_sink,
                ) catch return error.OutOfMemory;
                errdefer blk_body.deinit();
                try bundle.bodies.append(self.allocator, blk_body);
                out_is_comptime.* = true;
            }
        }

        if (mir_scratch_sink.error_count != 0) return;
        try out_bodies.ensureUnusedCapacity(self.allocator, bundle.bodies.items.len);
        for (bundle.bodies.items) |moved_body| {
            out_bodies.appendAssumeCapacity(moved_body);
        }
        bundle.bodies.shrinkRetainingCapacity(0);
    }

    /// Synchronizes `symbol_table` AST/CST handles and rebases `def_side_tables` after sibling line shifts.
    fn syncDefWindowAndSideTables(
        self: *CompilerDb,
        def_id: DefId,
        parsed_ptr: *const ParsedCstArtifact,
        item_ast_node: NodeIndex,
    ) QueryError!void {
        if (item_ast_node.isNone() or item_ast_node.asInt() >= parsed_ptr.ast_arena.countNodes()) return;
        const item_cst = parsed_ptr.ast_arena.getCstOrigin(item_ast_node);
        if (self.symbol_table.def_to_symbol.get(def_id.asInt())) |sym_idx| {
            if (!sym_idx.isNone()) {
                const sym_mut = self.symbol_table.getSymbolMut(sym_idx);
                sym_mut.ast_node = item_ast_node;
                sym_mut.cst_node = item_cst;
            }
        }
        if (self.def_side_tables.getPtr(def_id.asInt())) |st_ptr| {
            if (!item_cst.isNone() and item_cst.asInt() < parsed_ptr.cst_arena.countNodes()) {
                const cst_map = syntax_arenas.computeCstToAstMap(
                    self.allocator,
                    parsed_ptr.cst_arena.countNodes(),
                    &parsed_ptr.ast_arena,
                ) catch return error.OutOfMemory;
                defer if (cst_map.len > 0) self.allocator.free(cst_map);

                const cst_start: usize = item_cst.asInt();
                const cst_rec = parsed_ptr.cst_arena.getNode(item_cst);
                const cst_end: usize = @min(
                    cst_start + @max(@as(usize, cst_rec.subtree_size), 1),
                    cst_map.len,
                );
                var min_ast: u32 = std.math.maxInt(u32);
                for (cst_map[cst_start..cst_end]) |mapped_ast| {
                    if (!mapped_ast.isNone() and mapped_ast.asInt() < min_ast) {
                        min_ast = mapped_ast.asInt();
                    }
                }
                if (min_ast != std.math.maxInt(u32) and min_ast != st_ptr.ast_start) {
                    st_ptr.rebaseWindow(min_ast);
                }
            }
        }
    }

    /// Stage 9 implementation: dispatches either full SAST verification (`flags == 0`) or 34-byte summary projection.
    fn computeVerifySastMirKey(self: *CompilerDb, key: QueryKey) QueryError!Fingerprint128 {
        const def_id = DefId.fromInt(key.entity_index);
        if (def_id.isNone()) return error.InvalidDefId;

        if ((key.flags & SAST_SUMMARY_PROJ_FLAG) != 0) {
            _ = try self.verifySastMir(def_id);
            try self.unwindIfCancelled();
            const summary = self.sast_summaries.get(def_id.asInt()) orelse mir_sast.FnRegionSummary{};
            var obs_bytes: [34]u8 = undefined;
            summary.writeObservableBytes(&obs_bytes);

            var proj_hasher = StructuralHasher.init();
            proj_hasher.updateU32(def_id.asInt());
            proj_hasher.updateBytes(&obs_bytes);
            return proj_hasher.final();
        }

        return self.computeVerifySastMir(def_id);
    }

    /// Stage 9 implementation: runs Phase 6 MIR SAST & elaboration on `def_id`'s typed body.
    fn computeVerifySastMir(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const typed_body = try self.typecheckBody(def_id);
        const active_layout = try self.readTargetLayout();
        const is_strict = try self.readSastStrict();
        try self.unwindIfCancelled();

        if (self.sast_cycle_peers.getPtr(def_id.asInt())) |peer_list| {
            peer_list.clearRetainingCapacity();
        }

        const file_id = def_id.fileId();
        const parsed_init_opt = self.parsed_artifacts.getPtr(file_id.asInt());
        const has_front_errors = if (parsed_init_opt) |parsed_ptr|
            parsed_ptr.has_parse_errors or typed_body.error_count > 0
        else
            typed_body.error_count > 0;

        var local_sast_sink = DiagnosticSink.init(self.allocator);
        var is_sink_installed = false;
        errdefer if (!is_sink_installed) local_sast_sink.deinit();

        var final_summary = mir_sast.FnRegionSummary{};
        var elim_bounds: u32 = 0;
        var elim_narrow: u32 = 0;
        var emitted_drops: u32 = 0;

        if (!has_front_errors and
            self.parsed_artifacts.contains(file_id.asInt()) and
            self.source_inputs.contains(file_id.asInt()))
        {
            var local_tok_buf = self.parsed_artifacts.getPtr(file_id.asInt()).?.token_buffer;
            var local_cst_arena = self.parsed_artifacts.getPtr(file_id.asInt()).?.cst_arena;
            const src_text = self.source_inputs.getPtr(file_id.asInt()).?.owned_text;

            var active_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
            defer {
                for (active_bodies.items) |*body_item| body_item.deinit();
                active_bodies.deinit(self.allocator);
            }
            var is_comptime_item = false;
            try self.appendCleanSastBodiesForDef(
                def_id,
                active_layout,
                &active_bodies,
                &is_comptime_item,
            );

            const primary_len = active_bodies.items.len;
            if (primary_len > 0) {
                var sast_res = mir_sast.analyzeAndElaborateMirModule(
                    self.allocator,
                    active_bodies.items,
                    &self.type_pool,
                    &self.symbol_table,
                    &self.interner,
                    .{
                        .diagnostic_sink = &local_sast_sink,
                        .is_sast_strict = is_strict,
                        .is_comptime_context = is_comptime_item,
                        .primary_body_count = primary_len,
                        .source_text = src_text,
                        .token_buffer = &local_tok_buf,
                        .cst_arena = &local_cst_arena,
                        .external_resolver = .{
                            .compiler_db = self,
                            .resolve_fn = resolveDbCalleeSummary,
                        },
                    },
                ) catch |err| switch (err) {
                    error.Cancelled => return error.Cancelled,
                    error.DependencyCycle => return error.DependencyCycle,
                    error.MissingSourceInput => return error.MissingSourceInput,
                    error.InvalidDefId => return error.InvalidDefId,
                    error.OutOfMemory => return error.OutOfMemory,
                    else => return error.OutOfMemory,
                };
                var has_live_sast_res = true;
                defer if (has_live_sast_res) sast_res.deinit();

                // If `resolveDbCalleeSummary` discovered a cross-`DefId` mutual-recursion cycle (`[CRITICAL-03]`),
                // expand `active_bodies` with all peer `DefId`s and converge the full Tarjan SCC precisely:
                var cycle_round: usize = 0;
                var prev_peer_count: usize = 0;
                while (cycle_round < 4) : (cycle_round += 1) {
                    const cur_peer_count = if (self.sast_cycle_peers.getPtr(def_id.asInt())) |peer_list|
                        peer_list.items.len
                    else
                        0;
                    if (cur_peer_count == 0 or cur_peer_count == prev_peer_count) break;
                    prev_peer_count = cur_peer_count;

                    const peers_snapshot = try self.allocator.dupe(
                        DefId,
                        self.sast_cycle_peers.getPtr(def_id.asInt()).?.items,
                    );
                    defer self.allocator.free(peers_snapshot);

                    sast_res.deinit();
                    has_live_sast_res = false;
                    local_sast_sink.deinit();
                    local_sast_sink = DiagnosticSink.init(self.allocator);
                    for (active_bodies.items) |*body_item| body_item.deinit();
                    active_bodies.clearRetainingCapacity();

                    var is_dummy_ct = false;
                    try self.appendCleanSastBodiesForDef(
                        def_id,
                        active_layout,
                        &active_bodies,
                        &is_dummy_ct,
                    );
                    const rerun_primary_len = active_bodies.items.len;
                    for (peers_snapshot) |peer_def| {
                        const peer_tb = self.typecheckBody(peer_def) catch |err| switch (err) {
                            error.OutOfMemory => return error.OutOfMemory,
                            error.Cancelled => return error.Cancelled,
                            else => continue,
                        };
                        if (peer_tb.error_count == 0) {
                            var is_peer_ct = false;
                            try self.appendCleanSastBodiesForDef(
                                peer_def,
                                active_layout,
                                &active_bodies,
                                &is_peer_ct,
                            );
                        }
                    }

                    local_tok_buf = self.parsed_artifacts.getPtr(file_id.asInt()).?.token_buffer;
                    local_cst_arena = self.parsed_artifacts.getPtr(file_id.asInt()).?.cst_arena;
                    const refreshed_src = self.source_inputs.getPtr(file_id.asInt()).?.owned_text;
                    sast_res = mir_sast.analyzeAndElaborateMirModule(
                        self.allocator,
                        active_bodies.items,
                        &self.type_pool,
                        &self.symbol_table,
                        &self.interner,
                        .{
                            .diagnostic_sink = &local_sast_sink,
                            .is_sast_strict = is_strict,
                            .is_comptime_context = is_comptime_item,
                            .primary_body_count = rerun_primary_len,
                            .source_text = refreshed_src,
                            .token_buffer = &local_tok_buf,
                            .cst_arena = &local_cst_arena,
                            .external_resolver = .{
                                .compiler_db = self,
                                .resolve_fn = resolveDbCalleeSummary,
                            },
                        },
                    ) catch |err| switch (err) {
                        error.Cancelled => return error.Cancelled,
                        error.DependencyCycle => return error.DependencyCycle,
                        error.MissingSourceInput => return error.MissingSourceInput,
                        error.InvalidDefId => return error.InvalidDefId,
                        error.OutOfMemory => return error.OutOfMemory,
                        else => return error.OutOfMemory,
                    };
                    has_live_sast_res = true;
                }

                elim_bounds = sast_res.eliminated_bounds_checks;
                elim_narrow = sast_res.eliminated_narrow_checks;
                emitted_drops = sast_res.emitted_drops;

                var has_matched_primary = false;
                const summary_limit = @min(primary_len, sast_res.summary_store.summaries.len);
                for (sast_res.summary_store.summaries[0..summary_limit], 0..) |slot_sum, slot_i| {
                    const slot_def = sast_res.summary_store.def_ids[slot_i];
                    const slot_sym = sast_res.summary_store.symbol_indices[slot_i];
                    if (!slot_sym.isNone()) {
                        try self.sast_sym_summaries.put(
                            self.allocator,
                            slot_sym.asInt(),
                            slot_sum,
                        );
                    }
                    if (!slot_def.isNone()) {
                        try self.sast_summaries.put(
                            self.allocator,
                            slot_def.asInt(),
                            slot_sum,
                        );
                        if (slot_def == def_id) {
                            final_summary = slot_sum;
                            has_matched_primary = true;
                        }
                    }
                }
                if (!has_matched_primary and summary_limit > 0) {
                    final_summary = sast_res.summary_store.summaries[0];
                }
            }
        }

        const sink_gop = try self.sast_diagnostics.getOrPut(self.allocator, def_id.asInt());
        if (sink_gop.found_existing) {
            sink_gop.value_ptr.deinit();
        }
        sink_gop.value_ptr.* = local_sast_sink;
        is_sink_installed = true;

        try self.sast_summaries.put(self.allocator, def_id.asInt(), final_summary);
        var obs_bytes: [34]u8 = undefined;
        final_summary.writeObservableBytes(&obs_bytes);

        const total_sast_errors = sink_gop.value_ptr.error_count;
        const total_sast_warnings = sink_gop.value_ptr.warning_count;
        const is_sound = !has_front_errors and total_sast_errors == 0;

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateU8(if (is_sound) 1 else 0);
        hasher.updateU32(total_sast_errors);
        hasher.updateU32(total_sast_warnings);
        hasher.updateBytes(&obs_bytes);
        hasher.updateFingerprint(typed_body.typed_fingerprint);
        const sast_fp = hasher.final();

        try self.sast_results.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .file_id = file_id,
            .is_verified_sound = is_sound,
            .error_count = total_sast_errors,
            .warning_count = total_sast_warnings,
            .eliminated_bounds_checks = elim_bounds,
            .eliminated_narrow_checks = elim_narrow,
            .emitted_drops = emitted_drops,
            .summary = final_summary,
            .sast_fingerprint = sast_fp,
        });
        return sast_fp;
    }

    /// Stage 10 implementation: lowers `def_id` into an isolated `HirStore` (`[CRITICAL-11]`).
    fn computeLowerDefHir(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        _ = try self.typecheckBody(def_id);
        const body_window = try self.getBodyAstProj(def_id);
        const active_layout = try self.readTargetLayout();
        try self.unwindIfCancelled();

        const file_id = def_id.fileId();
        const input_ptr = self.source_inputs.getPtr(file_id.asInt()) orelse return error.MissingSourceInput;
        const parsed_ptr = self.parsed_artifacts.getPtr(file_id.asInt()) orelse return error.MissingSourceInput;
        const hir_sink = try resetOrCreateDefDiagSink(&self.hir_diagnostics, self.allocator, def_id.asInt());

        try self.syncDefWindowAndSideTables(def_id, parsed_ptr, body_window.item_ast_node);

        const eval_hook = mir_vm.makeComptimeEvalHook(self, def_id.asInt());
        var store = hir.lowerDefToHir(
            self.allocator,
            def_id,
            input_ptr.owned_text,
            &parsed_ptr.token_buffer,
            &parsed_ptr.cst_arena,
            &parsed_ptr.ast_arena,
            &self.interner,
            &self.type_pool,
            &self.symbol_table,
            self.def_side_tables.getPtr(def_id.asInt()),
            hir_sink,
            active_layout,
            eval_hook,
        ) catch |err| switch (err) {
            error.Cancelled => return error.Cancelled,
            error.DependencyCycle => return error.DependencyCycle,
            error.MissingSourceInput => return error.MissingSourceInput,
            error.InvalidDefId => return error.InvalidDefId,
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.OutOfMemory,
        };
        errdefer store.deinit();

        const hir_fp = computeHirStoreFingerprint(
            &store,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
        );
        if (try self.lowered_def_hirs.fetchPut(self.allocator, def_id.asInt(), store)) |prev_kv| {
            var old_store = prev_kv.value;
            old_store.deinit();
        }
        return hir_fp;
    }

    /// Stage 11 implementation: builds and `V1`–`V6` verifies `DefMirArtifact` for `def_id`.
    fn computeBuildDefMir(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const def_sig = try self.getDefSignature(def_id);
        const hir_store = try self.lowerDefHir(def_id);
        try self.unwindIfCancelled();

        const mir_sink = try resetOrCreateDefDiagSink(&self.mir_diagnostics, self.allocator, def_id.asInt());
        var bundle = mir.lowerHirToMir(
            self.allocator,
            hir_store,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
            mir_sink,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => blk: {
                _ = try resetOrCreateDefDiagSink(&self.mir_diagnostics, self.allocator, def_id.asInt());
                break :blk mir.lowerHirToMirForSast(
                    self.allocator,
                    hir_store,
                    &self.type_pool,
                    &self.symbol_table,
                    &self.interner,
                    mir_sink,
                ) catch return error.OutOfMemory;
            },
        };
        errdefer bundle.deinit();

        var is_init_only = false;
        if (!hir_store.root_hir.isNone() and hir_store.root_hir.asInt() < hir_store.nodes.len) {
            const root_node = hir_store.getNode(hir_store.root_hir);
            if (root_node.tag == .hir_const_decl) {
                const init_hir = HirIndex.fromInt(root_node.data.rhs);
                if (!init_hir.isNone()) {
                    var init_body = lowerInitializerHirToMirBody(
                        self.allocator,
                        def_id,
                        hir_store,
                        init_hir,
                        root_node.type_id,
                        &self.type_pool,
                        &self.symbol_table,
                        &self.interner,
                        mir_sink,
                    ) catch return error.OutOfMemory;
                    errdefer init_body.deinit();
                    try bundle.bodies.append(self.allocator, init_body);
                    is_init_only = true;
                }
            } else if (def_sig.kind == .extern_block and root_node.tag == .hir_block) {
                var blk_body = lowerInitializerHirToMirBody(
                    self.allocator,
                    def_id,
                    hir_store,
                    hir_store.root_hir,
                    .unit_ty,
                    &self.type_pool,
                    &self.symbol_table,
                    &self.interner,
                    mir_sink,
                ) catch return error.OutOfMemory;
                errdefer blk_body.deinit();
                try bundle.bodies.append(self.allocator, blk_body);
                is_init_only = true;
            }
        }

        const mir_fp = computeMirBundleFingerprint(
            &bundle,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
        );
        const artifact = DefMirArtifact{
            .def_id = def_id,
            .file_id = def_id.fileId(),
            .is_comptime_initializer_only = is_init_only,
            .bundle = bundle,
            .mir_fingerprint = mir_fp,
        };
        if (try self.built_def_mirs.fetchPut(self.allocator, def_id.asInt(), artifact)) |prev_kv| {
            var old_art = prev_kv.value;
            old_art.deinit();
        }
        return mir_fp;
    }

    /// Stage 12 implementation: evaluates `def_id` via `MirVm`, promotes to `.rodata`, and computes Early Cutoff hash.
    fn computeEvalComptimeDef(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        _ = try self.getDefSignature(def_id);
        const mir_art = try self.buildDefMirArtifact(def_id);
        try self.unwindIfCancelled();

        const ct_sink = try resetOrCreateDefDiagSink(
            &self.comptime_diagnostics,
            self.allocator,
            def_id.asInt(),
        );

        const target_body = mir_art.primaryBody() orelse {
            var empty_hasher = StructuralHasher.init();
            empty_hasher.updateU32(def_id.asInt());
            empty_hasher.updateU8(0);
            const empty_fp = empty_hasher.final();
            try self.evaluated_comptime_defs.put(self.allocator, def_id.asInt(), .{
                .def_id = def_id,
                .type_id = .unit_ty,
                .value = .unit_val,
                .rodata_id = .none,
                .has_errors = false,
                .value_fingerprint = empty_fp,
            });
            return empty_fp;
        };

        var primary_idx: usize = 0;
        for (mir_art.bundle.bodies.items, 0..) |*body_item, b_idx| {
            if (body_item.def_id == def_id) {
                primary_idx = b_idx;
                break;
            }
        }

        // `Fix-17` Gate D/F + `[CRITICAL-04]`: Elaborate `drop_in_place` / `drop_if_live` & reject `E0325` before `MirVm`!
        var cloned_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
        defer {
            for (cloned_bodies.items) |*cloned_item| cloned_item.deinit();
            cloned_bodies.deinit(self.allocator);
        }
        var is_using_elaborated_clones = false;
        {
            const file_id = def_id.fileId();
            const src_opt = if (self.source_inputs.getPtr(file_id.asInt())) |in_ptr| in_ptr.owned_text else null;
            const parsed_opt = self.parsed_artifacts.getPtr(file_id.asInt());

            for (mir_art.bundle.bodies.items) |*src_body| {
                var dup_body = src_body.clone(self.allocator) catch return error.OutOfMemory;
                errdefer dup_body.deinit();
                try cloned_bodies.append(self.allocator, dup_body);
            }

            var gate_sink = DiagnosticSink.init(self.allocator);
            defer gate_sink.deinit();

            if (mir_sast.analyzeAndElaborateMirModule(
                self.allocator,
                cloned_bodies.items,
                &self.type_pool,
                &self.symbol_table,
                &self.interner,
                .{
                    .diagnostic_sink = &gate_sink,
                    .is_comptime_context = true,
                    .source_text = src_opt,
                    .token_buffer = if (parsed_opt) |pp| &pp.token_buffer else null,
                    .cst_arena = if (parsed_opt) |pp| &pp.cst_arena else null,
                    .external_resolver = .{
                        .compiler_db = self,
                        .resolve_fn = resolveDbCalleeSummary,
                    },
                },
            )) |gate_res_val| {
                var gate_res = gate_res_val;
                defer gate_res.deinit();
                var has_e0325 = false;
                for (gate_sink.diagnostics.items) |diag_item| {
                    if (diag_item.code == .e0325_comptime_sandbox_violation) {
                        has_e0325 = true;
                        const sink_alloc = ct_sink.arena.asAllocator();
                        const dup_msg = sink_alloc.dupe(u8, diag_item.message) catch return error.OutOfMemory;
                        const dup_labels = sink_alloc.alloc(LabeledSpan, diag_item.labels.len) catch
                            return error.OutOfMemory;
                        for (diag_item.labels, 0..) |src_lbl, lbl_i| {
                            dup_labels[lbl_i] = .{
                                .span = src_lbl.span,
                                .label = sink_alloc.dupe(u8, src_lbl.label) catch return error.OutOfMemory,
                                .style = src_lbl.style,
                            };
                        }
                        const dup_notes = sink_alloc.alloc([]const u8, diag_item.notes.len) catch
                            return error.OutOfMemory;
                        for (diag_item.notes, 0..) |src_note, note_i| {
                            dup_notes[note_i] = sink_alloc.dupe(u8, src_note) catch return error.OutOfMemory;
                        }
                        try ct_sink.emit(.{
                            .code = diag_item.code,
                            .severity = .err,
                            .primary_span = diag_item.primary_span,
                            .message = dup_msg,
                            .labels = dup_labels,
                            .notes = dup_notes,
                        });
                    }
                }
                if (has_e0325) {
                    var sandbox_hasher = StructuralHasher.init();
                    sandbox_hasher.updateU32(def_id.asInt());
                    sandbox_hasher.updateU8(0xFD);
                    sandbox_hasher.updateU32(ct_sink.error_count);
                    const sandbox_fp = sandbox_hasher.final();
                    try self.evaluated_comptime_defs.put(self.allocator, def_id.asInt(), .{
                        .def_id = def_id,
                        .type_id = target_body.ret_ty,
                        .value = .unit_val,
                        .rodata_id = .none,
                        .has_errors = true,
                        .value_fingerprint = sandbox_fp,
                    });
                    return sandbox_fp;
                }
                if (gate_sink.error_count == 0 and cloned_bodies.items.len > primary_idx) {
                    is_using_elaborated_clones = true;
                }
            } else |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                error.Cancelled => return error.Cancelled,
                else => {},
            }
        }

        var file_tokens: std.AutoHashMapUnmanaged(u32, *const TokenBuffer) = .empty;
        defer file_tokens.deinit(self.allocator);
        try self.populateFileTokensMap(&file_tokens);

        const vm_opts = try self.makeVmExecOptions(&file_tokens);
        var vm = mir_vm.MirVm.init(
            self.allocator,
            &self.interner,
            &self.type_pool,
            &self.symbol_table,
            &self.rodata_pool,
            &self.pure_call_memo_cache,
            ct_sink,
            vm_opts,
        ) catch return error.OutOfMemory;
        defer vm.deinit();

        vm.markDbBackedDef(def_id) catch return error.OutOfMemory;
        const exec_bodies = if (is_using_elaborated_clones) cloned_bodies.items else mir_art.bundle.bodies.items;
        const exec_target = if (is_using_elaborated_clones) &cloned_bodies.items[primary_idx] else target_body;
        for (exec_bodies) |*body_item| {
            const sym_idx = if (!body_item.symbol_index.isNone())
                body_item.symbol_index
            else
                self.symbol_table.def_to_symbol.get(body_item.def_id.asInt()) orelse .none;
            _ = vm.registerBody(body_item, sym_idx) catch return error.OutOfMemory;
        }

        const eval_res = vm.evalBody(exec_target, &.{}) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            error.EvaluationCycle => return error.DependencyCycle,
            else => {
                var err_hasher = StructuralHasher.init();
                err_hasher.updateU32(def_id.asInt());
                err_hasher.updateU8(0xFF);
                err_hasher.updateU32(ct_sink.error_count);
                const err_fp = err_hasher.final();
                try self.evaluated_comptime_defs.put(self.allocator, def_id.asInt(), .{
                    .def_id = def_id,
                    .type_id = target_body.ret_ty,
                    .value = .unit_val,
                    .rodata_id = .none,
                    .has_errors = true,
                    .value_fingerprint = err_fp,
                });
                return err_fp;
            },
        };

        const rodata_id = vm.promoteResultToRodata(eval_res) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            else => {
                var err_hasher = StructuralHasher.init();
                err_hasher.updateU32(def_id.asInt());
                err_hasher.updateU8(0xFE);
                err_hasher.updateU32(ct_sink.error_count);
                const err_fp = err_hasher.final();
                try self.evaluated_comptime_defs.put(self.allocator, def_id.asInt(), .{
                    .def_id = def_id,
                    .type_id = eval_res.type_id,
                    .value = .unit_val,
                    .rodata_id = .none,
                    .has_errors = true,
                    .value_fingerprint = err_fp,
                });
                return err_fp;
            },
        };

        const out_hir_store = self.lowered_def_hirs.getPtr(def_id.asInt());
        const ct_val = vm.resultToComptimeValue(eval_res, out_hir_store) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.Cancelled => return error.Cancelled,
            else => hir.ComptimeValue.unit_val,
        };

        // Canonical Early-Cutoff fingerprint strictly over `(def_id, type_shape, canonical_rodata_blob)`:
        var val_hasher = StructuralHasher.init();
        val_hasher.updateU32(def_id.asInt());
        hashTypeCanonical(&val_hasher, &self.type_pool, &self.symbol_table, eval_res.type_id);
        val_hasher.updateU8(@backingInt(rodata_id.domain()));
        if (rodata_id.domain() == .rodata_blob) {
            if (self.rodata_pool.getBlob(rodata_id.payloadIndex())) |blob| {
                val_hasher.updateU64(blob.content_hash);
            }
        } else {
            hashComptimeValueShallow(
                &val_hasher,
                ct_val,
                &self.type_pool,
                &self.symbol_table,
                &self.interner,
            );
        }
        const value_fp = val_hasher.final();

        try self.evaluated_comptime_defs.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .type_id = eval_res.type_id,
            .value = ct_val,
            .rodata_id = rodata_id,
            .has_errors = false,
            .value_fingerprint = value_fp,
        });
        return value_fp;
    }

    /// Stage 13 implementation: optimizes all runtime `MIR` bodies in `file_id` (`--dev` or `--release`).
    fn computeOptimizeMirModule(
        self: *CompilerDb,
        file_id: FileId,
        is_release_mode: bool,
    ) QueryError!Fingerprint128 {
        const item_tree = try self.extractItemTree(file_id);
        _ = try self.resolveSignatures(file_id);
        const active_layout = try self.readTargetLayout();
        try self.unwindIfCancelled();

        const mode_key = QueryKey.forFileMode(.optimize_mir_module, file_id, is_release_mode);
        const opt_sink = try resetOrCreateModeDiagSink(
            &self.opt_diagnostics,
            self.allocator,
            mode_key.asU64(),
        );

        var collected_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
        defer {
            for (collected_bodies.items) |*body_item| body_item.deinit();
            collected_bodies.deinit(self.allocator);
        }

        var comptime_fn_defs: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer comptime_fn_defs.deinit(self.allocator);

        for (item_tree.entries) |entry| {
            if (entry.kind == .extern_block) {
                _ = self.evalComptimeDef(entry.def_id) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.Cancelled => return error.Cancelled,
                    else => {},
                };
            }
            const def_mir = try self.buildDefMirArtifact(entry.def_id);
            if (self.lowered_def_hirs.getPtr(entry.def_id.asInt())) |hir_ptr| {
                for (hir_ptr.functions.items) |fn_meta| {
                    if (fn_meta.is_comptime and !fn_meta.def_id.isNone()) {
                        try comptime_fn_defs.put(self.allocator, fn_meta.def_id.asInt(), {});
                    }
                }
            }
            if (def_mir.is_comptime_initializer_only) continue;
            for (def_mir.bundle.bodies.items) |*src_body| {
                var cloned_body = src_body.clone(self.allocator) catch return error.OutOfMemory;
                errdefer cloned_body.deinit();
                try collected_bodies.append(self.allocator, cloned_body);
            }
        }

        const maybe_syntax_view: ?mir_opt.FileSyntaxView = if (self.source_inputs.getPtr(file_id.asInt())) |in_ptr| blk: {
            if (self.parsed_artifacts.getPtr(file_id.asInt())) |p_ptr| {
                break :blk .{
                    .source = in_ptr.owned_text,
                    .tokens = &p_ptr.token_buffer,
                    .cst_arena = &p_ptr.cst_arena,
                };
            }
            break :blk null;
        } else null;

        const is_strict = try self.readSastStrict();
        var opt_res = mir_opt.optimizeMirModule(
            self.allocator,
            collected_bodies.items,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
            .{
                .is_release_mode = is_release_mode,
                .target_layout = active_layout,
                .syntax_view = maybe_syntax_view,
                .comptime_fn_defs = &comptime_fn_defs,
                .is_sast_enabled = true,
                .is_sast_strict = is_strict,
                .sast_config = .{
                    .is_sast_strict = is_strict,
                    .external_resolver = .{
                        .compiler_db = self,
                        .resolve_fn = resolveDbCalleeSummary,
                    },
                },
            },
            opt_sink,
        ) catch |err| switch (err) {
            error.Cancelled => return error.Cancelled,
            else => return error.OutOfMemory,
        };
        errdefer opt_res.deinit();

        var hasher = StructuralHasher.init();
        hasher.updateU32(file_id.asInt());
        hasher.updateU8(@intFromBool(is_release_mode));
        hasher.updateU8(active_layout.ptr_byte_size);
        hasher.updateU64(opt_res.fingerprint);
        hasher.updateU32(opt_res.dedup_merged_count);
        hasher.updateU32(opt_res.icf_folded_count);
        hasher.updateU32(opt_sink.error_count);
        const opt_fp = hasher.final();

        if (try self.optimized_mir_modules.fetchPut(
            self.allocator,
            mode_key.asU64(),
            opt_res,
        )) |prev_kv| {
            var old_res = prev_kv.value;
            old_res.deinit();
        }
        return opt_fp;
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
    // `parse_cst` and `lower_ast` re-executed, `lower_ast` backdated `changed_at = R1`, so `item_tree` skipped:
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

    // [1] Verify `bar` first: `bar` shifted by 20 lines, yet `typecheckBody(def_bar)` is NOT re-executed:
    _ = try db.verifySastMir(def_bar);
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.typecheck_body));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.verify_sast_mir));

    // [2] Verify `foo`: `foo`'s signature projections backdate to `rev1`, while `typecheckBody(def_foo)` re-runs:
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

// --------- Phase 5: HIR/MIR, Comptime & Optimization ----------

test "test_phase5_lower_def_hir_and_build_def_mir_sibling_body_shift_firewall" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(30);
    const src_v1 =
        \\pub fn alpha(val: i32) -> i32 {
        \\    let step = val + 1;
        \\    return step;
        \\}
        \\
        \\pub fn beta(scale: i32) -> i32 {
        \\    let prod = scale * 4;
        \\    return prod + 2;
        \\}
        \\
        \\pub fn gamma(offset: i32) -> i32 {
        \\    let shifted = offset - 3;
        \\    return shifted * 2;
        \\}
    ;

    const rev1 = try db.setInput(file_id, src_v1, .low);
    const tree_v1 = try db.extractItemTree(file_id);
    try std.testing.expectEqual(@as(usize, 3), tree_v1.entries.len);
    const def_alpha = tree_v1.entries[0].def_id;
    const def_beta = tree_v1.entries[1].def_id;
    const def_gamma = tree_v1.entries[2].def_id;

    // Build MIR for `alpha` and `beta` at `rev1`, while only typechecking `gamma` (not lowering `gamma` yet):
    try std.testing.expect((try db.buildDefMir(def_alpha)) != null);
    try std.testing.expect((try db.buildDefMir(def_beta)) != null);
    _ = try db.typecheckBody(def_gamma);

    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.lower_def_hir));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.build_def_mir));

    // Mutate `alpha` with extra local declarations + blank lines so `beta` and `gamma` shift AST/CST indices:
    const src_v2 =
        \\pub fn alpha(val: i32) -> i32 {
        \\    let s1 = val + 10;
        \\    let s2 = s1 * 3;
        \\    let s3 = s2 - 5;
        \\    let s4 = s3 + 9;
        \\
        \\
        \\
        \\    return s4;
        \\}
        \\
        \\pub fn beta(scale: i32) -> i32 {
        \\    let prod = scale * 4;
        \\    return prod + 2;
        \\}
        \\
        \\pub fn gamma(offset: i32) -> i32 {
        \\    let shifted = offset - 3;
        \\    return shifted * 2;
        \\}
    ;
    const rev2 = try db.setInput(file_id, src_v2, .low);
    try std.testing.expect(rev2.isAfter(rev1));

    // [1] Verify `beta` is shielded by the per-`DefId` firewall with zero HIR/MIR re-executions:
    try std.testing.expect((try db.buildDefMir(def_beta)) != null);
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.lower_def_hir));
    try std.testing.expectEqual(@as(u64, 2), db.telemetry.countExecutions(.build_def_mir));

    // [2] `gamma` was typechecked at `rev1` and is lowered to HIR/MIR for the first time AFTER shifting at `rev2`:
    const gamma_mir = (try db.buildDefMir(def_gamma)).?;
    try std.testing.expectEqual(TypeId.i32_ty, gamma_mir.ret_ty);
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.lower_def_hir));
    try std.testing.expectEqual(@as(u64, 3), db.telemetry.countExecutions(.build_def_mir));
}

test "test_phase5_eval_comptime_def_rodata_early_cutoff_and_cycle_e0509" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(31);
    const src_v1 =
        \\pub fn add_pair(lhs: i32, rhs: i32) -> i32 {
        \\    return lhs + rhs;
        \\}
        \\pub const TARGET: i32 = add_pair(20, 22);
    ;

    const rev1 = try db.setInput(file_id, src_v1, .low);
    const tree_v1 = try db.extractItemTree(file_id);
    const def_target = tree_v1.entries[1].def_id;

    const eval_r1 = try db.evalComptimeDef(def_target);
    try std.testing.expect(!eval_r1.has_errors);
    try std.testing.expectEqual(@as(i128, 42), eval_r1.value.int_val);
    try std.testing.expectEqual(mir_vm.AllocDomain.rodata_blob, eval_r1.rodata_id.domain());

    // Change `add_pair(20, 22)` -> `add_pair(10, 32)` so MIR changes while evaluated `.rodata` stays `42`:
    const src_v2 =
        \\pub fn add_pair(lhs: i32, rhs: i32) -> i32 {
        \\    return lhs + rhs;
        \\}
        \\pub const TARGET: i32 = add_pair(10, 32);
    ;
    const rev2 = try db.setInput(file_id, src_v2, .low);
    try std.testing.expect(rev2.isAfter(rev1));

    const eval_r2 = try db.evalComptimeDef(def_target);
    try std.testing.expectEqual(@as(i128, 42), eval_r2.value.int_val);
    try std.testing.expectEqual(eval_r1.rodata_id.asInt(), eval_r2.rodata_id.asInt());

    const target_memo = db.getMemoHeader(QueryKey.forDef(.eval_comptime_def, def_target)).?;
    try std.testing.expectEqual(rev1, target_memo.changed_at);
    try std.testing.expectEqual(rev2, target_memo.verified_at);

    // Verify cyclic `const` definitions across functions emit `E0509` (`error.DependencyCycle`):
    const cycle_file = FileId.fromInt(32);
    const cycle_src =
        \\pub fn read_second() -> i32 { return SECOND; }
        \\pub fn read_first() -> i32 { return FIRST; }
        \\pub const FIRST: i32 = read_second() + 1;
        \\pub const SECOND: i32 = read_first() + 1;
    ;
    _ = try db.setInput(cycle_file, cycle_src, .low);
    const cycle_tree = try db.extractItemTree(cycle_file);
    const def_first = cycle_tree.entries[2].def_id;

    try std.testing.expectError(error.DependencyCycle, db.evalComptimeDef(def_first));
    const ct_diags = db.getComptimeDiagnostics(def_first).?;
    try std.testing.expect(ct_diags.hasErrors());
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0509_comptime_evaluation_cycle,
        ct_diags.diagnostics.items[0].code,
    );
}

test "test_phase5_optimize_mir_module_dev_vs_release_and_comptime_step_limit" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(33);
    const opt_src =
        \\pub fn dup_one(val: i32) -> i32 {
        \\    var tmp: i32 = val + 1;
        \\    return tmp * 2;
        \\}
        \\pub fn dup_two(other: i32) -> i32 {
        \\    var acc: i32 = other + 1;
        \\    return acc * 2;
        \\}
    ;
    _ = try db.setInput(file_id, opt_src, .low);

    const dev_res = try db.optimizeMirModule(file_id, false);
    try std.testing.expectEqual(@as(usize, 2), dev_res.bodies.items.len);
    for (dev_res.bodies.items) |body_item| {
        try std.testing.expect(body_item.is_ghost_stripped);
        try std.testing.expect(!body_item.has_ghost_instructions);
        try std.testing.expect(body_item.is_contextless);
    }

    const rel_res = try db.optimizeMirModule(file_id, true);
    try std.testing.expectEqual(@as(u32, 1), rel_res.icf_folded_count);
    try std.testing.expectEqual(@as(usize, 2), rel_res.bodies.items.len);
    for (rel_res.bodies.items) |rel_body| {
        for (rel_body.blocks.items, 0..) |_, bb_idx| {
            for (rel_body.getBlockInsts(mem_foundation.MirBlockId.fromInt(@intCast(bb_idx)))) |iv| {
                const rel_inst = rel_body.getInst(iv);
                if (rel_inst.op == .place_store) {
                    try std.testing.expectEqual(@as(u32, 0), rel_body.places.items[rel_inst.operands.lhs].base);
                }
            }
        }
    }

    // Verify `setComptimeStepLimit` triggers `E0501` (`e0501_comptime_step_limit_exceeded`):
    const loop_file = FileId.fromInt(34);
    const loop_src =
        \\pub fn spin(limit: i32) -> i32 {
        \\    var cur: i32 = 0;
        \\    while cur < limit {
        \\        cur = cur + 1;
        \\    }
        \\    return cur;
        \\}
        \\pub const SPUN: i32 = spin(500);
    ;
    _ = try db.setInput(loop_file, loop_src, .low);
    db.setComptimeStepLimit(25);
    const loop_tree = try db.extractItemTree(loop_file);
    const spin_eval = try db.evalComptimeDef(loop_tree.entries[1].def_id);
    try std.testing.expect(spin_eval.has_errors);
    const spin_diags = db.getComptimeDiagnostics(loop_tree.entries[1].def_id).?;
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0501_comptime_step_limit_exceeded,
        spin_diags.diagnostics.items[0].code,
    );
}

test "test_phase5_config_invalidation_target_layout_wasm32_step_limit_and_embed_sandbox" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] `[CRITICAL-17]`: `setTargetLayout(WASM32)` invalidates cached `@size_of[*u8]()` (`8 -> 4`):
    const layout_file = FileId.fromInt(40);
    const layout_src =
        \\pub const PTR_SZ: usize = @size_of[*u8]();
    ;
    _ = try db.setInput(layout_file, layout_src, .low);
    const layout_tree = try db.extractItemTree(layout_file);
    const def_ptr_sz = layout_tree.entries[0].def_id;

    const eval_64 = try db.evalComptimeDef(def_ptr_sz);
    try std.testing.expect(!eval_64.has_errors);
    try std.testing.expectEqual(@as(i128, 8), eval_64.value.int_val);

    db.setTargetLayout(type_system.TargetLayout.WASM32);
    const eval_32 = try db.evalComptimeDef(def_ptr_sz);
    try std.testing.expect(!eval_32.has_errors);
    try std.testing.expectEqual(@as(i128, 4), eval_32.value.int_val);

    // [2] `[CRITICAL-02]` & `[CRITICAL-17]`: `setEmbedSandbox` invalidates cached `@embed_bytes` queries:
    var vfs_v1: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_v1.deinit(std.testing.allocator);
    try vfs_v1.put(std.testing.allocator, "assets/ver.txt", "v1");

    var vfs_v2: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_v2.deinit(std.testing.allocator);
    try vfs_v2.put(std.testing.allocator, "assets/ver.txt", "version_two");

    db.setEmbedSandbox(null, &vfs_v1);
    const embed_file = FileId.fromInt(41);
    const embed_src =
        \\pub const EMBED_LEN: usize = @embed_bytes("assets/ver.txt").len;
    ;
    _ = try db.setInput(embed_file, embed_src, .low);
    const embed_tree = try db.extractItemTree(embed_file);
    const def_embed_len = embed_tree.entries[0].def_id;

    const embed_r1 = try db.evalComptimeDef(def_embed_len);
    try std.testing.expect(!embed_r1.has_errors);
    try std.testing.expectEqual(@as(i128, 2), embed_r1.value.int_val);

    db.setEmbedSandbox(null, &vfs_v2);
    const embed_r2 = try db.evalComptimeDef(def_embed_len);
    try std.testing.expect(!embed_r2.has_errors);
    try std.testing.expectEqual(@as(i128, 11), embed_r2.value.int_val);

    // [3] `[CRITICAL-17]`: Raising `setComptimeStepLimit` invalidates cached `E0501` and succeeds:
    const step_file = FileId.fromInt(42);
    const step_src =
        \\pub fn count_to(goal: i32) -> i32 {
        \\    var cur: i32 = 0;
        \\    while cur < goal {
        \\        cur = cur + 1;
        \\    }
        \\    return cur;
        \\}
        \\pub const GOAL_OUT: i32 = count_to(40);
    ;
    _ = try db.setInput(step_file, step_src, .low);
    db.setComptimeStepLimit(15);
    const step_tree = try db.extractItemTree(step_file);
    const def_goal = step_tree.entries[1].def_id;

    const trapped_eval = try db.evalComptimeDef(def_goal);
    try std.testing.expect(trapped_eval.has_errors);

    db.setComptimeStepLimit(50_000);
    const recovered_eval = try db.evalComptimeDef(def_goal);
    try std.testing.expect(!recovered_eval.has_errors);
    try std.testing.expectEqual(@as(i128, 40), recovered_eval.value.int_val);
}

test "test_phase5_pure_call_memo_replays_deps_overflow_deps_red_path_cancel_and_loop_uaf" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] `[CRITICAL-01]`: `PureCallMemoCache` hit replays transitive `CompilerDb` `QueryKey` dependencies:
    const memo_file = FileId.fromInt(43);
    const memo_src_v1 =
        \\pub fn read_factor() -> i32 { return 3; }
        \\pub const FACTOR: i32 = read_factor();
        \\pub fn scale_val(val: i32) -> i32 {
        \\    return val * FACTOR;
        \\}
        \\pub const SCALED_ONE: i32 = scale_val(10);
        \\pub const SCALED_TWO: i32 = scale_val(10);
    ;
    _ = try db.setInput(memo_file, memo_src_v1, .low);
    const memo_tree = try db.extractItemTree(memo_file);
    const def_scaled_one = memo_tree.entries[3].def_id;
    const def_scaled_two = memo_tree.entries[4].def_id;

    const one_r1 = try db.evalComptimeDef(def_scaled_one);
    try std.testing.expect(db.pure_call_memo_cache.insert_count >= 1);
    const two_r1 = try db.evalComptimeDef(def_scaled_two);
    try std.testing.expectEqual(@as(i128, 30), one_r1.value.int_val);
    try std.testing.expectEqual(@as(i128, 30), two_r1.value.int_val);
    try std.testing.expect(db.pure_call_memo_cache.hit_count >= 1);

    // Mutate ONLY `read_factor` (`3 -> 7`); `SCALED_TWO` (which hit `pure_call_memo_cache` at `rev1`) MUST invalidate to `70`:
    const memo_src_v2 =
        \\pub fn read_factor() -> i32 { return 7; }
        \\pub const FACTOR: i32 = read_factor();
        \\pub fn scale_val(val: i32) -> i32 {
        \\    return val * FACTOR;
        \\}
        \\pub const SCALED_ONE: i32 = scale_val(10);
        \\pub const SCALED_TWO: i32 = scale_val(10);
    ;
    _ = try db.setInput(memo_file, memo_src_v2, .low);
    const two_r2 = try db.evalComptimeDef(def_scaled_two);
    try std.testing.expectEqual(@as(i128, 70), two_r2.value.int_val);

    // [2] `[MAJOR-18]`: `MemoHeader.has_overflowed_deps` forces conservative Red-Path verification past `MAX_DEPS_PER_MEMO`:
    const ovf_file = FileId.fromInt(44);
    const ovf_src_v1 =
        \\pub fn id_int(val: i32) -> i32 { return val; }
        \\pub const C_A: i32 = id_int(1);
        \\pub const C_B: i32 = id_int(1);
        \\pub const SUM_TWO: i32 = C_A + C_B;
    ;
    _ = try db.setInput(ovf_file, ovf_src_v1, .low);
    const ovf_tree = try db.extractItemTree(ovf_file);
    const def_sum_two = ovf_tree.entries[3].def_id;

    const HookHelper = struct {
        /// Injects `MAX_DEPS_PER_MEMO` synthetic dependency edges to trigger `has_overflowed_deps`.
        fn padMaxDepsOnEvalSum(hook_db: *CompilerDb, key: QueryKey) QueryError!void {
            if (key.stage == .eval_comptime_def and key.entity_index == FileId.fromInt(44).asInt() << 12 | 3) {
                try hook_db.scratch_dep_edges.ensureUnusedCapacity(hook_db.allocator, MAX_DEPS_PER_MEMO);
                for (0..MAX_DEPS_PER_MEMO) |i| {
                    hook_db.scratch_dep_edges.appendAssumeCapacity(
                        QueryKey.forFile(.source_text, FileId.fromInt(@intCast(10_000 + i))),
                    );
                }
            }
        }
    };
    db.setCustomStageHook(HookHelper.padMaxDepsOnEvalSum);
    const sum_r1 = try db.evalComptimeDef(def_sum_two);
    db.setCustomStageHook(null);
    try std.testing.expectEqual(@as(i128, 2), sum_r1.value.int_val);
    const sum_hdr = db.getMemoHeader(QueryKey.forDef(.eval_comptime_def, def_sum_two)).?;
    try std.testing.expect(sum_hdr.has_overflowed_deps);

    // Mutate `C_B` (`1 -> 101`, pushed past `MAX_DEPS_PER_MEMO = 65,535`): conservative Red Path MUST recompute `102`:
    const ovf_src_v2 =
        \\pub fn id_int(val: i32) -> i32 { return val; }
        \\pub const C_A: i32 = id_int(1);
        \\pub const C_B: i32 = id_int(101);
        \\pub const SUM_TWO: i32 = C_A + C_B;
    ;
    _ = try db.setInput(ovf_file, ovf_src_v2, .low);
    const sum_r2 = try db.evalComptimeDef(def_sum_two);
    try std.testing.expectEqual(@as(i128, 102), sum_r2.value.int_val);

    // [3] `[MAJOR-05]` & `[MAJOR-06]`: `requestCancellation` propagates `error.Cancelled`, and loop UAF traps `E0506`:
    const uaf_file = FileId.fromInt(45);
    const uaf_src =
        \\pub fn loop_uaf() -> i64 {
        \\    var outer_val: i64 = 10;
        \\    var saved_ref: &i64 = &outer_val;
        \\    var iter: i64 = 0;
        \\    while iter < 2 {
        \\        let inner_val: i64 = 99;
        \\        if iter == 0 {
        \\            saved_ref = &inner_val;
        \\        } else {
        \\            return *saved_ref;
        \\        }
        \\        iter = iter + 1;
        \\    }
        \\    return *saved_ref;
        \\}
        \\pub const BAD_UAF: i64 = loop_uaf();
    ;
    _ = try db.setInput(uaf_file, uaf_src, .low);
    const uaf_tree = try db.extractItemTree(uaf_file);
    const def_bad_uaf = uaf_tree.entries[1].def_id;

    db.requestCancellation();
    try std.testing.expectError(error.Cancelled, db.evalComptimeDef(def_bad_uaf));
    db.clearCancellation();

    const uaf_eval = try db.evalComptimeDef(def_bad_uaf);
    try std.testing.expect(uaf_eval.has_errors);
    const uaf_diags = db.getComptimeDiagnostics(def_bad_uaf).?;
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0506_comptime_invalid_pointer,
        uaf_diags.diagnostics.items[0].code,
    );
}

// -------- Phase 6: 34B Summary Firewall & Strict Gate ---------

test "test_phase6_sast_summary_early_cutoff_sast_strict_and_comptime_e0325" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] 34-byte `SAST_SUMMARY_PROJ_FLAG` Early Cutoff shields caller when callee body changes internally:
    const file_id = FileId.fromInt(60);
    const src_v1 =
        \\pub fn leaf_calc(val: i32) -> i32 {
        \\    let step = val + 1;
        \\    return step;
        \\}
        \\
        \\pub fn caller_fn(arr: [i32; 4], idx: usize) -> i32 {
        \\    return leaf_calc(arr[idx]);
        \\}
    ;
    const rev1 = try db.setInput(file_id, src_v1, .low);
    const tree_v1 = try db.extractItemTree(file_id);
    const def_leaf = tree_v1.entries[0].def_id;
    const def_caller = tree_v1.entries[1].def_id;

    const caller_r1 = try db.verifySastMir(def_caller);
    try std.testing.expect(caller_r1.is_verified_sound);
    try std.testing.expectEqual(@as(u32, 0), caller_r1.warning_count);

    // Edit `leaf_calc`'s internal arithmetic without changing its 34-byte `FnRegionSummary`:
    const src_v2 =
        \\pub fn leaf_calc(val: i32) -> i32 {
        \\    let step_a = val * 3;
        \\    let step_b = step_a - 7;
        \\    return step_b;
        \\}
        \\
        \\pub fn caller_fn(arr: [i32; 4], idx: usize) -> i32 {
        \\    return leaf_calc(arr[idx]);
        \\}
    ;
    const rev2 = try db.setInput(file_id, src_v2, .low);
    try std.testing.expect(rev2.isAfter(rev1));

    const caller_r2 = try db.verifySastMir(def_caller);
    try std.testing.expect(caller_r2.is_verified_sound);
    const proj_memo = db.getMemoHeader(QueryKey.forSastSummaryProj(def_leaf)).?;
    const caller_memo = db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, def_caller)).?;
    try std.testing.expectEqual(rev1, proj_memo.changed_at);
    try std.testing.expectEqual(rev1, caller_memo.changed_at);
    try std.testing.expectEqual(rev2, caller_memo.verified_at);

    // [2] Toggling `setSastStrict(true)` invalidates `CONFIG_KEY_SAST_STRICT` and emits `W0314` on `arr[idx]`:
    db.setSastStrict(true);
    const caller_strict = try db.verifySastMir(def_caller);
    try std.testing.expect(caller_strict.is_verified_sound);
    try std.testing.expect(caller_strict.warning_count >= 1);
    const strict_diags = db.getSastDiagnostics(def_caller).?;
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.w0314_unproven_bounds_access,
        strict_diags.diagnostics.items[0].code,
    );
    db.setSastStrict(false);

    // [3] `evalComptimeDef` rejects transitive FFI/host capability (`E0325`) before `MirVm` executes:
    const ct_file = FileId.fromInt(61);
    const ct_src =
        \\extern "C" fn host_clock() -> i32;
        \\pub fn sneaky_bridge() -> i32 {
        \\    return unsafe { host_clock() };
        \\}
        \\pub const BAD_CT: i32 = sneaky_bridge();
    ;
    _ = try db.setInput(ct_file, ct_src, .low);
    const ct_tree = try db.extractItemTree(ct_file);
    const def_bad_ct = ct_tree.entries[2].def_id;

    const ct_art = try db.evalComptimeDef(def_bad_ct);
    try std.testing.expect(ct_art.has_errors);
    const ct_diags = db.getComptimeDiagnostics(def_bad_ct).?;
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0325_comptime_sandbox_violation,
        ct_diags.diagnostics.items[0].code,
    );
}

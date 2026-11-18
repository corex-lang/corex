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
const codegen_abi = @import("codegen_abi.zig");
const codegen_dev_seam = @import("codegen_dev_seam.zig");
pub const c_frontend = @import("c_frontend.zig");
pub const c_translate = @import("c_translate.zig");

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
pub const Visibility = symbol_resolver.Visibility;
pub const PackageId = symbol_resolver.PackageId;
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
    /// Immutable standard library (`cx.*`) modules and locked external dependencies.
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

/// 64-bit semantic `Wyhash(0)` nominal field/variant layout digest (`DR-19` §1.2, `DR-20` Seam `#3`).
pub const FieldHash64 = enum(u64) {
    /// Sentinel zero digest (`0`).
    zero = 0,
    _,

    /// Wraps a raw 64-bit `Wyhash(0)` digest into `FieldHash64`.
    pub inline fn fromInt(raw_val: u64) FieldHash64 {
        return @fromBackingInt(raw_val);
    }

    /// Returns the underlying 64-bit unsigned integer digest.
    pub inline fn asInt(self: FieldHash64) u64 {
        return @backingInt(self);
    }

    /// Returns `true` when `self` equals `FieldHash64.zero`.
    pub inline fn isZero(self: FieldHash64) bool {
        return self == .zero;
    }
};

/// Strongly typed 32-bit `.cx_got[got_idx]` slot handle (`DR-19` §1.1, `DR-20` Seam `#3`).
pub const GotSlotId = enum(u32) {
    /// Sentinel indicating direct emission with no `.cx_got` slot (`0xFFFF_FFFF`).
    none = std.math.maxInt(u32),
    _,

    /// Wraps a zero-based `.cx_got` slot ordinal into `GotSlotId`.
    pub inline fn fromInt(raw_val: u32) GotSlotId {
        return @fromBackingInt(raw_val);
    }

    /// Returns the raw 32-bit slot ordinal.
    pub inline fn asInt(self: GotSlotId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` if `self` equals `GotSlotId.none`.
    pub inline fn isNone(self: GotSlotId) bool {
        return self == .none;
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
    /// Stage 10: Isolated per-definition `AST -> HIR` desugaring (`DefId -> HirStore`).
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

    /// Constructs a synthetic `.source_text` `QueryKey` for a Stage-0 compiler config slot.
    pub inline fn forConfig(config_entity: u32) QueryKey {
        return .{
            .stage = .source_text,
            .flags = 0,
            .reserved = 0,
            .entity_index = config_entity,
        };
    }

    /// Constructs a synthetic `.source_text` `QueryKey` tracking an `@embed_bytes` or `@c_import` file path.
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
    /// Function declaration (`fn`).
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
    /// Top-level `comptime` block item.
    extern_block = 10,
    /// Dedicated `subscript(…) -> T { let { … } inout { … } }` declaration (`SE-21`).
    subscript_decl = 11,
    /// First-class `test "…" { … }` declaration (`SE-16`).
    test_decl = 12,
    /// First-class `bench "…" (b: &var Bencher) { … }` declaration (`SE-16`).
    bench_decl = 13,
    /// Foreign ABI block declaration (`extern ["C"] { … }`; flattened into member `DefId` entries).
    ffi_extern_block = 14,
    /// Foreign or exported static global declaration (`extern ["C"] static [mut] NAME: T;`).
    extern_static = 15,
};

/// Single top-level declaration entry in a file's position-independent `ItemTree`.
pub const ItemTreeEntry = struct {
    /// File-scoped definition identifier (`(file_id, local_item_index)`).
    def_id: DefId,
    /// Declaration category tag.
    kind: ItemKind,
    /// Four-tier visibility (`private`, `pub_super`, `pub_pkg`, `public`; `ADR-22E`).
    visibility: Visibility = .private,
    /// Interned symbol handle for the declaration's primary identifier or test/bench description.
    name_symbol: SymbolId,
    /// Borrowed NUL-terminated slice from `CompilerDb.interner` for `name_symbol`.
    name_text: []const u8,
    /// Top-level AST node index inside `ParsedCstArtifact.ast_arena`.
    ast_node: NodeIndex,
    /// Originating CST node index inside `ParsedCstArtifact.cst_arena`.
    cst_node: CstNodeIndex,
    /// Body AST node index (`block`/expr for `fn_decl`/`subscript_decl`/`test_decl`/`bench_decl`, init for `const_decl`).
    body_ast_node: NodeIndex,
    /// Body CST node index (`block` CST node for functions/tests/benches, init CST for `const_decl`, `.none` otherwise).
    body_cst_node: CstNodeIndex,
    /// Position-independent 128-bit fingerprint of the item's signature (excluding function/accessor body blocks).
    signature_fingerprint: Fingerprint128,
    /// Position-independent 128-bit fingerprint of the item's body block or initializer.
    body_fingerprint: Fingerprint128,

    /// Returns `true` only when exported across package boundaries and `.cxi` interfaces (`visibility == .public`).
    pub inline fn isPublicOutsidePkg(self: ItemTreeEntry) bool {
        return self.visibility.isPublicOutsidePkg();
    }
};

/// Stage 3 position-independent `ItemTree` firewall for a single source file.
pub const ItemTree = struct {
    /// Owned slice of top-level item descriptors in declaration order.
    entries: []ItemTreeEntry = &.{},
    /// Owning source file identifier.
    file_id: FileId = .none,
    /// Whether `test` and `bench` declarations were retained when extracting `entries`.
    is_including_tests: bool = true,
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
    /// Total number of externally exported `pub` (`Visibility.public`) items in `file_id`.
    public_item_count: u32,
    /// Total number of name-resolution or signature errors emitted in `file_id`.
    error_count: u32 = 0,
    /// 128-bit fingerprint of the intra-package resolved module signature map.
    signatures_fingerprint: Fingerprint128,
    /// `.cxi` cross-package export firewall digest covering ONLY `Visibility.public` items (`ADR-22E`).
    public_interface_fingerprint: Fingerprint128 = Fingerprint128.ZERO,
};

/// Stage 7 resolved definition signature summary for a single `DefId`.
pub const DefSignatureArtifact = struct {
    /// Target definition handle.
    def_id: DefId,
    /// Declaration category tag.
    kind: ItemKind,
    /// Four-tier visibility (`private`, `pub_super`, `pub_pkg`, `public`; `ADR-22E`).
    visibility: Visibility = .private,
    /// Interned symbol identifier.
    name_symbol: SymbolId,
    /// Resolved symbol handle in `CompilerDb.symbol_table`.
    symbol_index: SymbolIndex = .none,
    /// Resolved canonical `TypeId` in `CompilerDb.type_pool`.
    type_id: TypeId = .err_ty,
    /// Borrowed per-parameter zone/named/default descriptors from `CompilerDb.symbol_table` (`SE-07`, `SE-11`).
    param_specs: []const symbol_resolver.FnParamSpec = &.{},
    /// Borrowed generic parameter default descriptors from `CompilerDb.symbol_table` (`SE-10`).
    generic_specs: []const symbol_resolver.GenericParamSpec = &.{},
    /// 128-bit fingerprint of this definition's signature.
    signature_fingerprint: Fingerprint128,

    /// Returns `true` only when exported across package boundaries and `.cxi` interfaces (`visibility == .public`).
    pub inline fn isPublicOutsidePkg(self: DefSignatureArtifact) bool {
        return self.visibility.isPublicOutsidePkg();
    }
};

/// Read-only syntax and file-level semantic side-table view for cross-file default argument lowering (`SE-07`).
pub const ExternalFileSyntaxView = struct {
    /// UTF-8 source buffer of `file_id`.
    source: []const u8,
    /// Lossless token buffer of `file_id`.
    tokens: *const TokenBuffer,
    /// Lossless CST arena of `file_id`.
    cst_arena: *const LosslessCstArena,
    /// Lowered AST arena of `file_id`.
    ast_arena: *const AstArena,
    /// File-level signature semantic side tables of `file_id`, if available.
    file_side_tables: ?*const BodySemanticSideTables,
};

/// Symbol-table watermark and AST fingerprint state for `resolveSignatures` Early Cutoff rebasing (`SE-07`).
const FileSigSyncState = struct {
    /// Inclusive `SymbolIndex` watermark recorded before `collectFileModuleItems`.
    sym_start: u32 = 0,
    /// Exclusive `SymbolIndex` watermark recorded after `collectFileModuleItems`.
    sym_end: u32 = 0,
    /// `ParsedCstArtifact.ast_fingerprint` matching `fn_param_specs` and `file_side_tables`.
    ast_fingerprint: Fingerprint128 = .ZERO,
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

/// Errors returned by `CompilerDb.compileModuleArtifact`.
pub const ModuleCompileError = QueryError || error{
    /// Front-end, SAST, comptime, or `@embed_bytes` diagnostics prevented artifact emission.
    FrontendErrors,
    /// Tier A or Tier B IR emission / atomic output write failed (`E0007`).
    BackendFailure,
    /// External `zig cc` / `LLD` driver invocation failed (`E0008`).
    CompilerDriverFailed,
    /// `.object_file` or `.executable` requested without `output_path` or `io`.
    MissingOutputConfig,
    /// `-Dllvm-prefix` static C++20 `corex_llvm` bridge was requested when not linked in.
    StaticBridgeUnavailable,
};

/// Configuration options for `CompilerDb.compileModuleArtifact`.
pub const ModuleCompileOptions = struct {
    /// Logical module name emitted in `.ll` / debug headers.
    module_name: []const u8 = "corex_mod",
    /// Optional additional `.cx` `FileId`s compiled into the same artifact alongside `root_file_id`.
    extra_file_ids: []const FileId = &.{},
    /// Optional `VfsSourceMap` for `#line` directives and DWARF source spans.
    vfs_source_map: ?*const vfs_sourcemap.VfsSourceMap = null,
    /// Emit `--dev` GOT function-pointer table indirection + `.cx_dev_meta` seam (`DR-19`).
    is_dev_got_enabled: bool = false,
    /// Enable `COREX_ORACLE_TRACE_FILE` trap/drop/return instrumentation (`D-07A`).
    is_oracle_trace_enabled: bool = false,
    /// Requested output form (`.source_text`, `.object_file`, `.executable`, `.static_library`, `.shared_library`).
    artifact_kind: codegen_abi.OutputArtifactKind = .source_text,
    /// Requested binary linkage mode (`.auto`, `.static`, or `.dynamic`).
    link_mode: codegen_abi.LinkMode = .auto,
    /// Additional `-l<lib>` or `.a`/`.lib`/`.def` link inputs forwarded to the linker driver.
    extra_libs: []const []const u8 = &.{},
    /// Additional `-L<dir>` library search directories forwarded to the linker driver.
    lib_dirs: []const []const u8 = &.{},
    /// Output file path on disk (required for non-`.source_text` artifacts).
    output_path: ?[]const u8 = null,
    /// Zig `Io` handle for `zig cc` subprocesses and `atomicWriteOutputFile`.
    io: ?std.Io = null,
    /// Optional host environment map forwarded to `zig cc`.
    environ_map: ?*const std.process.Environ.Map = null,
    /// Optional diagnostic sink receiving backend/linker errors (`E0007` / `E0008`).
    diagnostic_sink: ?*DiagnosticSink = null,
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

/// Active `.param_list` range containing a positional-only `/` zone separator (`ADR-22F`).
const ParamSlashScope = struct {
    /// Exclusive ending CST node index of the enclosing `.param_list` subtree.
    list_end: usize,
    /// CST node index of the `/` separator leaf inside the `.param_list`.
    slash_idx: usize,
};

/// Enclosing `extern ["C"] { … }` block context propagated to flattened member `ItemTreeEntry` items.
const ExternBlockItemContext = struct {
    /// Effective ABI string literal without quotes (e.g., `"C"`).
    abi_lexeme: []const u8,
    /// Visibility modifier written on the enclosing `extern` block header.
    visibility: Visibility,
    /// `true` if `unsafe extern` was written on the enclosing block header.
    is_unsafe: bool,
    /// Position-independent 128-bit digest of the enclosing block's attributes and ABI header.
    header_fingerprint: Fingerprint128,
};

/// Owned transitive `#include` path and `BLAKE3` content digest stored inside `CImportCache`.
pub const CImportIncludeDep = struct {
    /// Owned path string (VFS key or resolved filesystem path) allocated from `CompilerDb.allocator`.
    owned_path: []u8,
    /// 256-bit `BLAKE3` content digest observed when the `@c_import` header was translated.
    content_blake3: [32]u8,
};

/// Borrowed read-only view of a cached `@c_import` header translation entry (`Durability.medium`).
pub const CImportCacheView = struct {
    /// 128-bit content-addressed key (`Wyhash` over header bytes, `target_spec.archOsTag()`, and `defines`).
    key: Fingerprint128,
    /// Borrowed canonical `.cx` translation text owned by `CImportCache`.
    translated_cx_text: []const u8,
    /// Virtual `FileId` registered in `CompilerDb` with `Durability.medium`.
    virtual_file_id: FileId,
    /// Assigned Salsa durability tier (`.medium`).
    durability: Durability = .medium,
    /// Borrowed transitive `#include` `(owned_path, content_blake3)` pairs recorded during translation.
    included_files: []const CImportIncludeDep = &.{},
};

/// Intrusive doubly-linked LRU slot inside `CImportCache`.
const CImportCacheNode = struct {
    /// Content-addressed 128-bit lookup key.
    key: Fingerprint128 = Fingerprint128.ZERO,
    /// Owned canonical `.cx` source buffer allocated from `CompilerDb.allocator`.
    owned_cx_text: []u8 = &.{},
    /// Owned transitive `#include` `(owned_path, content_blake3)` pairs recorded during translation.
    included_files: []CImportIncludeDep = &.{},
    /// Virtual `FileId` associated with this translated header.
    virtual_file_id: FileId = .none,
    /// Assigned Salsa durability tier (`.medium`).
    durability: Durability = .medium,
    /// Previous (more recently used) slot index, or `NONE_C_IMPORT_LRU` at `head_mru`.
    prev_idx: u32 = NONE_C_IMPORT_LRU,
    /// Next (less recently used) slot index, or `NONE_C_IMPORT_LRU` at `tail_lru`.
    next_idx: u32 = NONE_C_IMPORT_LRU,
    /// `true` while this slot holds an active un-evicted entry.
    is_occupied: bool = false,
};

/// Hash-map context keying `CImportCache.index_by_key` directly by 128-bit `Fingerprint128`.
const Fingerprint128Context = struct {
    /// Mixes both 64-bit `Wyhash` lanes into a 64-bit hash-table bucket hash.
    pub fn hash(_: Fingerprint128Context, fp: Fingerprint128) u64 {
        return fp.low ^ (fp.high *% Fingerprint128.SEED_HIGH);
    }

    /// Compares two 128-bit fingerprints for exact bit equality.
    pub fn eql(_: Fingerprint128Context, first: Fingerprint128, second: Fingerprint128) bool {
        return Fingerprint128.eql(first, second);
    }
};

/// Bounded content-addressed LRU cache for `@c_import` header translations (`AGENTS.md` §2).
///
/// Enforces BOTH `MAX_C_IMPORT_CACHE_ENTRIES` (`128`) and `MAX_C_IMPORT_CACHE_BYTES` (`16 MiB`)
/// with $O(1)$ intrusive doubly-linked LRU promotion and eviction, and zero startup allocations.
pub const CImportCache = struct {
    /// Flat arena of LRU node slots (lazily allocated on first `put`).
    nodes: std.ArrayListUnmanaged(CImportCacheNode) = .empty,
    /// Recycled slot indices from prior LRU evictions.
    free_slots: std.ArrayListUnmanaged(u32) = .empty,
    /// $O(1)$ lookup table mapping `Fingerprint128` -> slot index in `nodes`.
    index_by_key: std.HashMapUnmanaged(Fingerprint128, u32, Fingerprint128Context, 80) = .empty,
    /// Most-recently-used slot index (`NONE_C_IMPORT_LRU` when empty).
    head_mru: u32 = NONE_C_IMPORT_LRU,
    /// Least-recently-used slot index (`NONE_C_IMPORT_LRU` when empty).
    tail_lru: u32 = NONE_C_IMPORT_LRU,
    /// Active cached entry count (`<= MAX_C_IMPORT_CACHE_ENTRIES`).
    entry_count: usize = 0,
    /// Total byte footprint of all active `owned_cx_text` and `included_files` buffers (`<= MAX_C_IMPORT_CACHE_BYTES`).
    total_bytes: usize = 0,
    /// Total number of cache hits observed via `get`.
    hits: u64 = 0,
    /// Total number of cache misses observed via `get`.
    misses: u64 = 0,
    /// Total number of LRU evictions triggered by entry-count or byte-budget caps.
    evictions: u64 = 0,

    /// Returns a zero-allocation lazily initialized `CImportCache`.
    pub inline fn init() CImportCache {
        return .{};
    }

    /// Computes the owned byte footprint of `deps` for `MAX_C_IMPORT_CACHE_BYTES` accounting.
    fn includeDepsByteSize(deps: []const CImportIncludeDep) usize {
        var bytes: usize = 0;
        for (deps) |dep| {
            bytes +|= dep.owned_path.len + @sizeOf([32]u8);
        }
        return bytes;
    }

    /// Releases owned transitive `#include` path buffers and slice storage in `deps`.
    fn freeIncludeDeps(allocator: std.mem.Allocator, deps: []CImportIncludeDep) void {
        for (deps) |dep| {
            if (dep.owned_path.len > 0) allocator.free(dep.owned_path);
        }
        if (deps.len > 0) allocator.free(deps);
    }

    /// Clones `recorded` transitive `#include` descriptors into an owned `[]CImportIncludeDep` slice.
    fn cloneIncludeDeps(
        allocator: std.mem.Allocator,
        recorded: []const c_frontend.RecordedIncludeFile,
    ) ![]CImportIncludeDep {
        if (recorded.len == 0) return &.{};
        const out = try allocator.alloc(CImportIncludeDep, recorded.len);
        var init_count: usize = 0;
        errdefer {
            var idx: usize = 0;
            while (idx < init_count) : (idx += 1) {
                if (out[idx].owned_path.len > 0) allocator.free(out[idx].owned_path);
            }
            allocator.free(out);
        }
        for (recorded, 0..) |item, i| {
            out[i] = .{
                .owned_path = if (item.path.len > 0) try allocator.dupe(u8, item.path) else &.{},
                .content_blake3 = item.content_blake3,
            };
            init_count += 1;
        }
        return out;
    }

    /// Releases all owned `.cx` translation buffers and internal tables back to `allocator`.
    pub fn deinit(self: *CImportCache, allocator: std.mem.Allocator) void {
        for (self.nodes.items) |*slot| {
            if (slot.is_occupied) {
                if (slot.owned_cx_text.len > 0) allocator.free(slot.owned_cx_text);
                freeIncludeDeps(allocator, slot.included_files);
            }
        }
        self.nodes.deinit(allocator);
        self.free_slots.deinit(allocator);
        self.index_by_key.deinit(allocator);
        self.* = .{};
    }

    /// Clears all cached `@c_import` entries while retaining table capacities for workspace reuse.
    pub fn clear(self: *CImportCache, allocator: std.mem.Allocator) void {
        for (self.nodes.items) |*slot| {
            if (slot.is_occupied) {
                if (slot.owned_cx_text.len > 0) allocator.free(slot.owned_cx_text);
                freeIncludeDeps(allocator, slot.included_files);
            }
            slot.* = .{};
        }
        self.nodes.clearRetainingCapacity();
        self.free_slots.clearRetainingCapacity();
        self.index_by_key.clearRetainingCapacity();
        self.head_mru = NONE_C_IMPORT_LRU;
        self.tail_lru = NONE_C_IMPORT_LRU;
        self.entry_count = 0;
        self.total_bytes = 0;
    }

    /// Computes the canonical 128-bit `Wyhash` cache key over header bytes, `target_spec`, `defines`, and `include_dirs`.
    pub fn computeKey(
        header_source_bytes: []const u8,
        target_spec: codegen_abi.TargetSpec,
        defines: []const []const u8,
        include_dirs: []const []const u8,
    ) Fingerprint128 {
        var hasher = StructuralHasher.init();
        hasher.updateU8(0xC7);
        hasher.updateU16(target_spec.archOsTag());
        hasher.updateU8(@backingInt(target_spec.simd_level));
        hasher.updateBytes(header_source_bytes);
        hasher.updateU32(@intCast(@min(defines.len, std.math.maxInt(u32))));
        for (defines) |define_str| {
            hasher.updateBytes(define_str);
        }
        hasher.updateU32(@intCast(@min(include_dirs.len, std.math.maxInt(u32))));
        for (include_dirs) |include_dir| {
            hasher.updateBytes(include_dir);
        }
        return hasher.final();
    }

    /// Detaches `slot_idx` from the intrusive doubly-linked LRU list in $O(1)$ time.
    fn detachSlot(self: *CImportCache, slot_idx: u32) void {
        const node = self.nodes.items[slot_idx];
        if (node.prev_idx != NONE_C_IMPORT_LRU) {
            self.nodes.items[node.prev_idx].next_idx = node.next_idx;
        } else {
            self.head_mru = node.next_idx;
        }
        if (node.next_idx != NONE_C_IMPORT_LRU) {
            self.nodes.items[node.next_idx].prev_idx = node.prev_idx;
        } else {
            self.tail_lru = node.prev_idx;
        }
        self.nodes.items[slot_idx].prev_idx = NONE_C_IMPORT_LRU;
        self.nodes.items[slot_idx].next_idx = NONE_C_IMPORT_LRU;
    }

    /// Attaches `slot_idx` at `head_mru` as the most-recently-used entry in $O(1)$ time.
    fn attachAtHead(self: *CImportCache, slot_idx: u32) void {
        self.nodes.items[slot_idx].prev_idx = NONE_C_IMPORT_LRU;
        self.nodes.items[slot_idx].next_idx = self.head_mru;
        if (self.head_mru != NONE_C_IMPORT_LRU) {
            self.nodes.items[self.head_mru].prev_idx = slot_idx;
        } else {
            self.tail_lru = slot_idx;
        }
        self.head_mru = slot_idx;
    }

    /// Evicts the least-recently-used entry at `tail_lru` in $O(1)$ time, returning its virtual `FileId`.
    fn evictLeastRecentlyUsed(self: *CImportCache, allocator: std.mem.Allocator) !?FileId {
        const victim_idx = self.tail_lru;
        if (victim_idx == NONE_C_IMPORT_LRU) return null;
        self.detachSlot(victim_idx);
        const victim = self.nodes.items[victim_idx];
        _ = self.index_by_key.remove(victim.key);
        const victim_bytes = victim.owned_cx_text.len +| includeDepsByteSize(victim.included_files);
        self.total_bytes -|= victim_bytes;
        if (victim.owned_cx_text.len > 0) allocator.free(victim.owned_cx_text);
        freeIncludeDeps(allocator, victim.included_files);
        self.nodes.items[victim_idx] = .{};
        try self.free_slots.append(allocator, victim_idx);
        self.entry_count -|= 1;
        self.evictions += 1;
        return victim.virtual_file_id;
    }

    /// Looks up `key` in $O(1)$ time and promotes the entry to `head_mru` on hit.
    pub fn get(self: *CImportCache, key: Fingerprint128) ?CImportCacheView {
        const slot_idx = self.index_by_key.get(key) orelse {
            self.misses += 1;
            return null;
        };
        if (slot_idx != self.head_mru) {
            self.detachSlot(slot_idx);
            self.attachAtHead(slot_idx);
        }
        self.hits += 1;
        const slot = self.nodes.items[slot_idx];
        return .{
            .key = slot.key,
            .translated_cx_text = slot.owned_cx_text,
            .virtual_file_id = slot.virtual_file_id,
            .durability = slot.durability,
            .included_files = slot.included_files,
        };
    }

    /// Inspects `key` in $O(1)$ time without mutating LRU order or hit/miss telemetry.
    pub fn peek(self: *const CImportCache, key: Fingerprint128) ?CImportCacheView {
        const slot_idx = self.index_by_key.get(key) orelse return null;
        const slot = self.nodes.items[slot_idx];
        return .{
            .key = slot.key,
            .translated_cx_text = slot.owned_cx_text,
            .virtual_file_id = slot.virtual_file_id,
            .durability = slot.durability,
            .included_files = slot.included_files,
        };
    }

    /// Inserts or updates `(key, translated_cx_text, virtual_file_id)`, enforcing `128`-entry and `16 MiB` LRU caps.
    pub fn put(
        self: *CImportCache,
        allocator: std.mem.Allocator,
        key: Fingerprint128,
        translated_cx_text: []const u8,
        virtual_file_id: FileId,
    ) !?CImportCacheView {
        return self.putWithIncludesAndEvicted(allocator, key, translated_cx_text, &.{}, virtual_file_id, null);
    }

    /// Inserts or updates `(key, translated_cx_text, virtual_file_id)`, recording any LRU-evicted virtual `FileId`s.
    pub fn putWithEvicted(
        self: *CImportCache,
        allocator: std.mem.Allocator,
        key: Fingerprint128,
        translated_cx_text: []const u8,
        virtual_file_id: FileId,
        evicted_fids: ?*std.ArrayListUnmanaged(FileId),
    ) !?CImportCacheView {
        return self.putWithIncludesAndEvicted(
            allocator,
            key,
            translated_cx_text,
            &.{},
            virtual_file_id,
            evicted_fids,
        );
    }

    /// Inserts or updates `(key, translated_cx_text, included_files, virtual_file_id)` under `128`-entry / `16 MiB` caps.
    pub fn putWithIncludesAndEvicted(
        self: *CImportCache,
        allocator: std.mem.Allocator,
        key: Fingerprint128,
        translated_cx_text: []const u8,
        included_files: []const c_frontend.RecordedIncludeFile,
        virtual_file_id: FileId,
        evicted_fids: ?*std.ArrayListUnmanaged(FileId),
    ) !?CImportCacheView {
        var new_entry_bytes: usize = translated_cx_text.len;
        for (included_files) |inc_item| {
            new_entry_bytes +|= inc_item.path.len + @sizeOf([32]u8);
        }
        if (new_entry_bytes > MAX_C_IMPORT_CACHE_BYTES) return null;

        if (self.index_by_key.get(key)) |existing_idx| {
            const prev_slot = self.nodes.items[existing_idx];
            const prev_bytes = prev_slot.owned_cx_text.len +| includeDepsByteSize(prev_slot.included_files);
            const prev_fid = prev_slot.virtual_file_id;
            self.detachSlot(existing_idx);
            while (self.entry_count > 1 and
                (self.total_bytes -| prev_bytes) + new_entry_bytes > MAX_C_IMPORT_CACHE_BYTES)
            {
                const evicted_fid = (try self.evictLeastRecentlyUsed(allocator)) orelse break;
                if (evicted_fids) |out_list| {
                    if (!evicted_fid.isNone()) try out_list.append(allocator, evicted_fid);
                }
            }
            const duped_text = try allocator.dupe(u8, translated_cx_text);
            errdefer if (duped_text.len > 0) allocator.free(duped_text);
            const duped_includes = try cloneIncludeDeps(allocator, included_files);
            errdefer freeIncludeDeps(allocator, duped_includes);

            if (prev_slot.owned_cx_text.len > 0) allocator.free(prev_slot.owned_cx_text);
            freeIncludeDeps(allocator, prev_slot.included_files);
            if (evicted_fids) |out_list| {
                if (!prev_fid.isNone() and prev_fid != virtual_file_id) {
                    try out_list.append(allocator, prev_fid);
                }
            }
            self.total_bytes = (self.total_bytes -| prev_bytes) + new_entry_bytes;
            self.nodes.items[existing_idx].owned_cx_text = duped_text;
            self.nodes.items[existing_idx].included_files = duped_includes;
            self.nodes.items[existing_idx].virtual_file_id = virtual_file_id;
            self.nodes.items[existing_idx].durability = .medium;
            self.attachAtHead(existing_idx);
            return .{
                .key = key,
                .translated_cx_text = duped_text,
                .virtual_file_id = virtual_file_id,
                .durability = .medium,
                .included_files = duped_includes,
            };
        }

        while (self.entry_count >= MAX_C_IMPORT_CACHE_ENTRIES or
            self.total_bytes + new_entry_bytes > MAX_C_IMPORT_CACHE_BYTES)
        {
            const evicted_fid = (try self.evictLeastRecentlyUsed(allocator)) orelse break;
            if (evicted_fids) |out_list| {
                if (!evicted_fid.isNone()) try out_list.append(allocator, evicted_fid);
            }
        }

        const duped_text = try allocator.dupe(u8, translated_cx_text);
        errdefer if (duped_text.len > 0) allocator.free(duped_text);
        const duped_includes = try cloneIncludeDeps(allocator, included_files);
        errdefer freeIncludeDeps(allocator, duped_includes);

        const slot_idx: u32 = if (self.free_slots.items.len > 0)
            self.free_slots.pop().?
        else blk_new: {
            const next_idx: u32 = @intCast(self.nodes.items.len);
            try self.nodes.append(allocator, .{});
            break :blk_new next_idx;
        };

        self.nodes.items[slot_idx] = .{
            .key = key,
            .owned_cx_text = duped_text,
            .included_files = duped_includes,
            .virtual_file_id = virtual_file_id,
            .durability = .medium,
            .is_occupied = true,
        };
        try self.index_by_key.put(allocator, key, slot_idx);
        self.attachAtHead(slot_idx);
        self.entry_count += 1;
        self.total_bytes += new_entry_bytes;
        return .{
            .key = key,
            .translated_cx_text = duped_text,
            .virtual_file_id = virtual_file_id,
            .durability = .medium,
            .included_files = duped_includes,
        };
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Total number of `QueryStage` variants in the canonical pipeline (`14`).
pub const STAGE_COUNT: usize = @typeInfo(QueryStage).@"enum".field_names.len;
/// Total number of `Durability` tiers (`3`: `.low`, `.medium`, `.high`).
pub const DURABILITY_COUNT: usize = @typeInfo(Durability).@"enum".field_names.len;
/// Maximum number of top-level items encoded in a 12-bit `DefId.local_item_index` (`4,096`).
pub const MAX_ITEMS_PER_FILE: usize = std.math.maxInt(u12) + 1;
/// Maximum number of direct dependencies recorded in a single `MemoHeader` (`65,535`).
pub const MAX_DEPS_PER_MEMO: usize = std.math.maxInt(u16);
/// Maximum number of `@c_import` header translations retained in `CImportCache` (`AGENTS.md` §2).
pub const MAX_C_IMPORT_CACHE_ENTRIES: usize = 128;
/// Maximum total UTF-8 `.cx` byte footprint retained in `CImportCache` (`16 MiB`, `AGENTS.md` §2).
pub const MAX_C_IMPORT_CACHE_BYTES: usize = 16 * 1024 * 1024;
/// Starting 20-bit virtual `FileId` reserved for cached `@c_import` modules (`983,040`).
pub const VIRTUAL_C_IMPORT_FILE_ID_BASE: u32 = 0x000F_0000;
/// Sentinel LRU node index indicating the end of an intrusive `CImportCache` list (`0xFFFF_FFFF`).
const NONE_C_IMPORT_LRU: u32 = std.math.maxInt(u32);
/// Reserved synthetic `.source_text` entity index tracking `CompilerDb.target_layout`.
pub const CONFIG_KEY_TARGET_LAYOUT: u32 = 0xFFFF_FFF0;
/// Reserved synthetic `.source_text` entity index tracking `CompilerDb.comptime_step_limit`.
pub const CONFIG_KEY_COMPTIME_LIMIT: u32 = 0xFFFF_FFF1;
/// Reserved synthetic `.source_text` entity index tracking `CompilerDb` `@embed_bytes` sandbox.
pub const CONFIG_KEY_EMBED_SANDBOX: u32 = 0xFFFF_FFF2;
/// Reserved synthetic `.source_text` entity index tracking `--sast-strict` (`CompilerDb.is_sast_strict`).
pub const CONFIG_KEY_SAST_STRICT: u32 = 0xFFFF_FFF3;
/// Reserved synthetic `.source_text` entity index tracking `--internal-core` (`CompilerDb.is_internal_core`).
pub const CONFIG_KEY_INTERNAL_CORE: u32 = 0xFFFF_FFF4;
/// Reserved synthetic `.source_text` entity index tracking test/bench inclusion (`CompilerDb.is_including_tests`).
pub const CONFIG_KEY_INCLUDE_TESTS: u32 = 0xFFFF_FFF5;
/// Flag bit on `.source_text` `QueryKey.flags` identifying a tracked `@embed_bytes` or `@c_import` file dependency.
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

/// Locates the direct child CST index of a `/` positional-only zone separator inside `param_list_cst` (`0` if none).
fn findPositionalOnlySlashInParamList(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    param_list_cst: CstNodeIndex,
) usize {
    if (param_list_cst.isNone() or param_list_cst.asInt() >= cst_arena.countNodes()) return 0;
    const start_idx: usize = param_list_cst.asInt();
    const list_rec = cst_arena.getNode(param_list_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, list_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    var child_cursor: usize = start_idx + 1;
    while (child_cursor < end_idx) {
        const child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
        const step_size: usize = @max(@as(usize, child.subtree_size), 1);
        if (child.kind == .param_zone_sep) {
            const sep_end = @min(child_cursor + step_size, end_idx);
            var sub_cursor: usize = child_cursor;
            while (sub_cursor < sep_end) : (sub_cursor += 1) {
                const sub_node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_cursor)));
                const is_leaf = sub_node.subtree_size <= 1 and !sub_node.flags.is_bracketed;
                if (is_leaf and !sub_node.flags.is_missing_or_injected and
                    !sub_node.token.isNone() and sub_node.token.asInt() < token_buffer.countTokens() and
                    token_buffer.getToken(sub_node.token).kind == .slash)
                {
                    return child_cursor;
                }
            }
        } else if (child.subtree_size <= 1 and !child.flags.is_bracketed and
            !child.flags.is_missing_or_injected and !child.token.isNone() and
            child.token.asInt() < token_buffer.countTokens() and
            token_buffer.getToken(child.token).kind == .slash)
        {
            return child_cursor;
        }
        child_cursor += step_size;
    }
    return 0;
}

/// Locates the parameter identifier leaf CST index inside a positional-only `.fn_param` (`0` for `self` or unnamed).
fn findPositionalOnlyParamNameCst(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    fn_param_cst: CstNodeIndex,
) usize {
    if (fn_param_cst.isNone() or fn_param_cst.asInt() >= cst_arena.countNodes()) return 0;
    const start_idx: usize = fn_param_cst.asInt();
    const param_rec = cst_arena.getNode(fn_param_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, param_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .attribute) {
            cursor += @max(@as(usize, node.subtree_size), 1);
            continue;
        }
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (is_leaf and !node.flags.is_missing_or_injected and
            !node.token.isNone() and node.token.asInt() < token_buffer.countTokens())
        {
            const tok_kind = token_buffer.getToken(node.token).kind;
            if (tok_kind == .colon or tok_kind == .eq or tok_kind == .comma or tok_kind == .rparen) {
                return 0;
            }
            if (tok_kind == .kw_self_val) return 0;
            if (tok_kind == .kw_var or tok_kind == .kw_mut or tok_kind == .kw_own or
                tok_kind == .kw_comptime or tok_kind == .amp)
            {
                cursor += 1;
                continue;
            }
            if (isIdentifierTokenKind(tok_kind) or tok_kind == .underscore) return cursor;
        }
        cursor += 1;
    }
    return 0;
}

/// Returns `true` if `block_cst` directly wraps `.subscript_arm` nodes (`{ let { … } inout { … } }`).
fn hasBlockSubscriptArm(cst_arena: *const LosslessCstArena, block_cst: CstNodeIndex) bool {
    if (block_cst.isNone() or block_cst.asInt() >= cst_arena.countNodes()) return false;
    const start_idx: usize = block_cst.asInt();
    const block_rec = cst_arena.getNode(block_cst);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, block_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    var child_cursor: usize = start_idx + 1;
    while (child_cursor < end_idx) {
        const child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_cursor)));
        if (child.kind == .subscript_arm) return true;
        child_cursor += @max(@as(usize, child.subtree_size), 1);
    }
    return false;
}

/// Advances `start_cursor` past a top-level `= expr;` function expression body up to and including `.semi`.
fn skipFnExprBodyUntilSemi(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    start_cursor: usize,
    limit_idx: usize,
) usize {
    var paren_depth: u32 = 0;
    var bracket_depth: u32 = 0;
    var brace_depth: u32 = 0;
    var scan_idx: usize = start_cursor;
    while (scan_idx < limit_idx) : (scan_idx += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(scan_idx)));
        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
        if (node.token.asInt() >= token_buffer.countTokens()) continue;
        switch (token_buffer.getToken(node.token).kind) {
            .lparen => paren_depth += 1,
            .rparen => paren_depth -|= 1,
            .lbracket => bracket_depth += 1,
            .rbracket => bracket_depth -|= 1,
            .lbrace => brace_depth += 1,
            .rbrace => brace_depth -|= 1,
            .semi => {
                if (paren_depth == 0 and bracket_depth == 0 and brace_depth == 0) {
                    return scan_idx + 1;
                }
            },
            else => {},
        }
    }
    return limit_idx;
}

/// Computes the position-independent signature fingerprint of `item_cst_node`, skipping function/accessor bodies.
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

    var param_slash_stack: [8]ParamSlashScope = undefined;
    var param_slash_depth: usize = 0;
    var erased_param_name_cst_idx: usize = 0;

    var fn_member_end_idx: usize = if (root_rec.kind == .fn_item or
        root_rec.kind == .subscript_item or
        root_rec.kind == .test_item or
        root_rec.kind == .bench_item or
        root_rec.kind == .trait_member or
        root_rec.kind == .impl_member)
        end_idx
    else
        0;
    var is_fn_like_member: bool = (root_rec.kind == .fn_item);
    var is_subscript_member: bool = (root_rec.kind == .subscript_item);
    var after_fn_sig_idx: usize = if (root_rec.kind == .test_item or root_rec.kind == .bench_item)
        root_idx + 1
    else
        std.math.maxInt(usize);
    var paren_depth: u32 = 0;
    var bracket_depth: u32 = 0;
    var brace_depth: u32 = 0;

    var cursor: usize = root_idx;
    while (cursor < end_idx) {
        while (param_slash_depth > 0 and cursor >= param_slash_stack[param_slash_depth - 1].list_end) {
            param_slash_depth -= 1;
        }
        if (cursor >= fn_member_end_idx) {
            is_fn_like_member = false;
            is_subscript_member = false;
            after_fn_sig_idx = std.math.maxInt(usize);
        }

        const current_cst_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(current_cst_id);
        const step_size: usize = @max(@as(usize, node.subtree_size), 1);
        const is_outer_subscript_block = is_subscript_member and
            node.kind == .block and
            hasBlockSubscriptArm(cst_arena, current_cst_id);

        // [1] Skip explicit `body_cst_node`, `comptime` inner `.block`, subscript arm `.block`, or `= expr;` body:
        if (!body_cst_node.isNone() and current_cst_id == body_cst_node and !is_outer_subscript_block) {
            if (root_rec.kind != .fn_item or node.kind == .block or node.kind == .fn_expr_body) {
                hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                cursor += step_size;
                if (node.kind == .fn_expr_body) {
                    cursor = skipFnExprBodyUntilSemi(token_buffer, cst_arena, cursor, end_idx);
                }
                continue;
            }
        }
        if (cursor > root_idx) {
            if (root_rec.kind == .block and node.kind == .block) {
                hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                cursor += step_size;
                continue;
            }
            if (is_subscript_member and node.kind == .block and !is_outer_subscript_block and
                cursor >= after_fn_sig_idx and cursor < fn_member_end_idx)
            {
                hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                cursor += step_size;
                continue;
            }
            if ((node.kind == .block or node.kind == .fn_expr_body) and !is_outer_subscript_block and
                cursor >= after_fn_sig_idx and
                cursor < fn_member_end_idx)
            {
                hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                const member_limit = fn_member_end_idx;
                after_fn_sig_idx = std.math.maxInt(usize);
                is_fn_like_member = false;
                cursor += step_size;
                if (node.kind == .fn_expr_body) {
                    cursor = skipFnExprBodyUntilSemi(token_buffer, cst_arena, cursor, member_limit);
                }
                continue;
            }
        }

        if (node.kind == .fn_item or
            node.kind == .subscript_item or
            node.kind == .test_item or
            node.kind == .bench_item or
            node.kind == .trait_member or
            node.kind == .impl_member)
        {
            fn_member_end_idx = @min(cursor + step_size, end_idx);
            is_fn_like_member = (node.kind == .fn_item);
            is_subscript_member = (node.kind == .subscript_item);
            after_fn_sig_idx = if (node.kind == .test_item or node.kind == .bench_item)
                cursor + 1
            else
                std.math.maxInt(usize);
            paren_depth = 0;
            bracket_depth = 0;
            brace_depth = 0;
        } else if ((node.kind == .fn_sig or node.kind == .param_list) and cursor < fn_member_end_idx) {
            after_fn_sig_idx = @min(cursor + step_size, fn_member_end_idx);
        }

        if (node.kind == .param_list) {
            const slash_idx = findPositionalOnlySlashInParamList(token_buffer, cst_arena, current_cst_id);
            if (slash_idx > 0 and param_slash_depth < param_slash_stack.len) {
                param_slash_stack[param_slash_depth] = .{
                    .list_end = @min(cursor + step_size, end_idx),
                    .slash_idx = slash_idx,
                };
                param_slash_depth += 1;
            }
        } else if (node.kind == .fn_param and param_slash_depth > 0) {
            const top_slash = param_slash_stack[param_slash_depth - 1];
            if (cursor < top_slash.slash_idx) {
                erased_param_name_cst_idx = findPositionalOnlyParamNameCst(
                    token_buffer,
                    cst_arena,
                    current_cst_id,
                );
            }
        } else if (node.kind == .subscript_arm) {
            is_subscript_member = true;
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
            if (!node.token.isNone() and node.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(node.token);
                if (cursor < fn_member_end_idx) {
                    if (tok_rec.kind == .kw_fn) {
                        is_fn_like_member = true;
                    } else if (tok_rec.kind == .kw_subscript) {
                        is_subscript_member = true;
                    } else if (is_fn_like_member and
                        cursor >= after_fn_sig_idx and
                        paren_depth == 0 and
                        bracket_depth == 0 and
                        brace_depth == 0 and
                        tok_rec.kind == .eq)
                    {
                        hasher.updateU8(BODY_BLOCK_OMITTED_MARKER);
                        const member_limit = fn_member_end_idx;
                        after_fn_sig_idx = std.math.maxInt(usize);
                        is_fn_like_member = false;
                        cursor = skipFnExprBodyUntilSemi(token_buffer, cst_arena, cursor + 1, member_limit);
                        continue;
                    }
                    switch (tok_rec.kind) {
                        .lparen => paren_depth += 1,
                        .rparen => paren_depth -|= 1,
                        .lbracket => bracket_depth += 1,
                        .rbracket => bracket_depth -|= 1,
                        .lbrace => brace_depth += 1,
                        .rbrace => brace_depth -|= 1,
                        else => {},
                    }
                }
                hasher.updateU8(@backingInt(node.kind));
                hasher.updateU8(if (node.flags.has_error) 1 else 0);
                if (cursor == erased_param_name_cst_idx) {
                    erased_param_name_cst_idx = 0;
                    hasher.updateU8(@backingInt(TokenKind.ident));
                    hasher.updateBytes("_");
                } else {
                    hasher.updateU8(@backingInt(tok_rec.kind));
                    hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
                }
            } else {
                hasher.updateU8(@backingInt(node.kind));
                hasher.updateU8(if (node.flags.has_error) 1 else 0);
            }
        } else {
            hasher.updateU8(@backingInt(node.kind));
            hasher.updateU8(if (node.flags.has_error) 1 else 0);
            if (cursor > root_idx and
                node.kind != .trait_member and
                node.kind != .impl_member and
                node.kind != .fn_item and
                node.kind != .subscript_item and
                node.kind != .subscript_arm and
                !is_outer_subscript_block)
            {
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

/// Hashes positional-only parameter names (`before /`) into `hasher` so self-body typecheck invalidates cleanly.
fn hashPositionalOnlyParamNamesForBody(
    hasher: *StructuralHasher,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
) void {
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) return;
    const root_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        root_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );
    var cursor: usize = root_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const cur_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(cur_id);
        if (node.kind != .param_list) continue;
        const slash_idx = findPositionalOnlySlashInParamList(token_buffer, cst_arena, cur_id);
        if (slash_idx == 0) continue;
        var child_cursor: usize = cursor + 1;
        while (child_cursor < slash_idx) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child = cst_arena.getNode(child_id);
            if (child.kind == .fn_param) {
                const name_cst_idx = findPositionalOnlyParamNameCst(token_buffer, cst_arena, child_id);
                if (name_cst_idx > 0) {
                    const name_node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(name_cst_idx)));
                    hasher.updateU8(0x50);
                    hasher.updateBytes(getTokenLexeme(source, token_buffer, name_node.token));
                }
            }
            child_cursor += @max(@as(usize, child.subtree_size), 1);
        }
    }
}

/// Hashes the CST nodes of a top-level `= expr;` function expression body inside `[member_start .. member_end)`.
fn hashFnExprBodyTokensInRange(
    hasher: *StructuralHasher,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    member_start: usize,
    member_end: usize,
) bool {
    var after_params_idx: usize = std.math.maxInt(usize);
    var paren_depth: u32 = 0;
    var bracket_depth: u32 = 0;
    var brace_depth: u32 = 0;
    var has_seen_eq = false;
    var cursor: usize = member_start;
    while (cursor < member_end) : (cursor += 1) {
        const cur_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(cur_id);
        if (!has_seen_eq) {
            if (node.kind == .fn_sig or node.kind == .param_list) {
                after_params_idx = @min(cursor + @max(@as(usize, node.subtree_size), 1), member_end);
            } else if (node.kind == .fn_expr_body and cursor >= after_params_idx) {
                hasher.updateU8(2);
                hashPositionIndependentCstSubtree(hasher, source, token_buffer, cst_arena, cur_id);
                return true;
            }
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
            if (node.token.asInt() >= token_buffer.countTokens()) continue;
            const tok_kind = token_buffer.getToken(node.token).kind;
            if (cursor >= after_params_idx and
                paren_depth == 0 and
                bracket_depth == 0 and
                brace_depth == 0 and
                tok_kind == .eq)
            {
                has_seen_eq = true;
                hasher.updateU8(2);
                continue;
            }
            switch (tok_kind) {
                .lparen => paren_depth += 1,
                .rparen => paren_depth -|= 1,
                .lbracket => bracket_depth += 1,
                .rbracket => bracket_depth -|= 1,
                .lbrace => brace_depth += 1,
                .rbrace => brace_depth -|= 1,
                else => {},
            }
            continue;
        }

        const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
        if (is_leaf) {
            if (node.flags.is_missing_or_injected) continue;
            if (!node.token.isNone() and node.token.asInt() < token_buffer.countTokens()) {
                const tok_rec = token_buffer.getToken(node.token);
                if (paren_depth == 0 and bracket_depth == 0 and brace_depth == 0 and tok_rec.kind == .semi) {
                    break;
                }
                switch (tok_rec.kind) {
                    .lparen => paren_depth += 1,
                    .rparen => paren_depth -|= 1,
                    .lbracket => bracket_depth += 1,
                    .rbracket => bracket_depth -|= 1,
                    .lbrace => brace_depth += 1,
                    .rbrace => brace_depth -|= 1,
                    else => {},
                }
                hasher.updateU8(@backingInt(node.kind));
                hasher.updateU8(@backingInt(tok_rec.kind));
                hasher.updateBytes(getTokenLexeme(source, token_buffer, node.token));
            }
        } else {
            hasher.updateU8(@backingInt(node.kind));
            hasher.updateU32(node.subtree_size);
        }
    }
    return has_seen_eq;
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
    hashPositionalOnlyParamNamesForBody(&hasher, source, token_buffer, cst_arena, item_cst_node);

    if (!item_cst_node.isNone() and item_cst_node.asInt() < cst_arena.countNodes()) {
        const root_idx: usize = item_cst_node.asInt();
        const root_rec = cst_arena.getNode(item_cst_node);
        const end_idx: usize = @min(
            root_idx + @max(@as(usize, root_rec.subtree_size), 1),
            cst_arena.countNodes(),
        );

        // For `.fn_item` with top-level `= expr;` (where `body_cst_node` is not a `.block`), hash full RHS:
        if (root_rec.kind == .fn_item) {
            const has_block_body = !body_cst_node.isNone() and
                body_cst_node.asInt() < cst_arena.countNodes() and
                cst_arena.getNode(body_cst_node).kind == .block;
            if (!has_block_body) {
                if (hashFnExprBodyTokensInRange(&hasher, source, token_buffer, cst_arena, root_idx + 1, end_idx)) {
                    return hasher.final();
                }
            }
        }

        // For `.subscript_item`, hash all `.subscript_arm` or accessor `.block` subtrees:
        if (root_rec.kind == .subscript_item) {
            var has_arm_body = false;
            var cursor: usize = root_idx + 1;
            while (cursor < end_idx) {
                const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
                const sub_node = cst_arena.getNode(sub_id);
                if (sub_node.kind == .subscript_arm) {
                    has_arm_body = true;
                    hashPositionIndependentCstSubtree(&hasher, source, token_buffer, cst_arena, sub_id);
                    cursor += @max(@as(usize, sub_node.subtree_size), 1);
                    continue;
                }
                cursor += 1;
            }
            if (has_arm_body) return hasher.final();
        }
    }

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

    // For `trait` or `impl` containers, hash any default/member method `.block`, `.subscript_arm`, or `= expr;` bodies:
    if (root_rec.kind == .trait_item or root_rec.kind == .impl_item) {
        var has_any_block = false;
        var cursor: usize = root_idx + 1;
        while (cursor < end_idx) {
            const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
            const sub_node = cst_arena.getNode(sub_id);
            const sub_step = @max(@as(usize, sub_node.subtree_size), 1);
            if (sub_node.kind == .fn_item or sub_node.kind == .trait_member or sub_node.kind == .impl_member) {
                const sub_end = @min(cursor + sub_step, end_idx);
                if (hashFnExprBodyTokensInRange(&hasher, source, token_buffer, cst_arena, cursor + 1, sub_end)) {
                    has_any_block = true;
                    cursor = sub_end;
                    continue;
                }
            }
            if (sub_node.kind == .block or sub_node.kind == .fn_expr_body or sub_node.kind == .subscript_arm) {
                has_any_block = true;
                hashPositionIndependentCstSubtree(&hasher, source, token_buffer, cst_arena, sub_id);
                cursor += sub_step;
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
        .struct_decl, .bit_field_decl => .struct_decl,
        .enum_decl => .enum_decl,
        .union_decl => .union_decl,
        .trait_decl => .trait_decl,
        .impl_decl => .impl_decl,
        .type_alias_decl => .type_alias_decl,
        .const_decl => .const_decl,
        .block => .extern_block,
        .subscript_decl => .subscript_decl,
        .test_decl => .test_decl,
        .bench_decl => .bench_decl,
        .extern_block_decl => .ffi_extern_block,
        .extern_static_decl => .extern_static,
        else => null,
    };
}

/// Converts `syntax_arenas.ExternVisibility` into the 4-tier `Visibility` enum.
fn externVisToVisibility(ext_vis: syntax_arenas.ExternVisibility) Visibility {
    return switch (ext_vis) {
        .private => .private,
        .pub_super => .pub_super,
        .pub_pkg => .pub_pkg,
        .public => .public,
    };
}

/// Extracts the unquoted ABI string literal from `abi_tok` (defaulting to `"C"` when absent).
fn extractExternAbiSlice(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    abi_tok: TokenIndex,
) []const u8 {
    if (abi_tok.isNone() or abi_tok.asInt() >= token_buffer.countTokens()) return "C";
    const raw_lex = getTokenLexeme(source, token_buffer, abi_tok);
    if (raw_lex.len >= 2 and raw_lex[0] == '"' and raw_lex[raw_lex.len - 1] == '"') {
        return raw_lex[1 .. raw_lex.len - 1];
    }
    return if (raw_lex.len > 0) raw_lex else "C";
}

/// Hashes a contiguous slice of CST `.attribute` subtrees stored in `ast_arena.extra_data`.
fn hashExtraAttrSlice(
    hasher: *StructuralHasher,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    attr_start: u32,
    attr_len: u32,
) void {
    hasher.updateU32(attr_len);
    if (attr_len == 0) return;
    const end_idx: usize = @as(usize, attr_start) + @as(usize, attr_len);
    if (end_idx > ast_arena.extra_data.items.len) return;
    for (ast_arena.getExtraSlice(ExtraIndex.fromInt(attr_start), attr_len)) |raw_attr_cst| {
        const attr_cst = CstNodeIndex.fromInt(raw_attr_cst);
        hasher.updateFingerprint(computeItemSignatureFingerprint(
            source,
            token_buffer,
            cst_arena,
            attr_cst,
            .none,
        ));
    }
}

/// Builds the inherited `ExternBlockItemContext` for members flattened out of `block_ast_node`.
fn computeExternBlockContext(
    source: []const u8,
    parsed: *const ParsedCstArtifact,
    block_ast_node: NodeIndex,
    header: syntax_arenas.ExternBlockHeader,
) ExternBlockItemContext {
    const abi_lexeme = extractExternAbiSlice(source, &parsed.token_buffer, header.abi_tok);
    const outer_vis = externVisToVisibility(header.flags.visibility);
    var hdr_hasher = StructuralHasher.init();
    hdr_hasher.updateU8(0xEB);
    hdr_hasher.updateBytes(abi_lexeme);
    hdr_hasher.updateU8(@backingInt(outer_vis));
    hdr_hasher.updateU8(@intFromBool(header.flags.is_unsafe));
    hashExtraAttrSlice(
        &hdr_hasher,
        source,
        &parsed.token_buffer,
        &parsed.cst_arena,
        &parsed.ast_arena,
        header.attr_start,
        header.attr_len,
    );
    const block_cst = parsed.ast_arena.getCstOrigin(block_ast_node);
    if (!block_cst.isNone() and block_cst.asInt() < parsed.cst_arena.countNodes()) {
        const start_idx: usize = block_cst.asInt();
        const root_rec = parsed.cst_arena.getNode(block_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
            parsed.cst_arena.countNodes(),
        );
        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) {
            const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
            const sub_node = parsed.cst_arena.getNode(sub_id);
            if (sub_node.kind == .attribute) {
                hdr_hasher.updateFingerprint(computeItemSignatureFingerprint(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    sub_id,
                    .none,
                ));
                cursor += @max(@as(usize, sub_node.subtree_size), 1);
                continue;
            }
            if (sub_node.subtree_size <= 1 and !sub_node.token.isNone() and
                sub_node.token.asInt() < parsed.token_buffer.countTokens() and
                parsed.token_buffer.getToken(sub_node.token).kind == .lbrace)
            {
                break;
            }
            cursor += 1;
        }
    }
    return .{
        .abi_lexeme = abi_lexeme,
        .visibility = outer_vis,
        .is_unsafe = header.flags.is_unsafe,
        .header_fingerprint = hdr_hasher.final(),
    };
}

/// Computes a deterministic position-independent signature fingerprint for an `extern_static_decl`.
fn computeExternStaticSigFingerprint(
    source: []const u8,
    parsed: *const ParsedCstArtifact,
    item_ast_node: NodeIndex,
    item_cst_node: CstNodeIndex,
    name_text: []const u8,
    effective_vis: Visibility,
    enclosing_ctx: ?ExternBlockItemContext,
) Fingerprint128 {
    var hasher = StructuralHasher.init();
    hasher.updateU8(0xE5);
    hasher.updateBytes(name_text);
    hasher.updateU8(@backingInt(effective_vis));

    const static_extra = parsed.ast_arena.getExternStaticExtra(item_ast_node);
    const effective_abi = if (!static_extra.abi_tok.isNone())
        extractExternAbiSlice(source, &parsed.token_buffer, static_extra.abi_tok)
    else if (enclosing_ctx) |ctx|
        ctx.abi_lexeme
    else
        "C";
    const is_effective_unsafe = static_extra.flags.is_unsafe or
        (enclosing_ctx != null and enclosing_ctx.?.is_unsafe);
    hasher.updateBytes(effective_abi);
    hasher.updateU8(@intFromBool(static_extra.flags.is_mut));
    hasher.updateU8(@intFromBool(static_extra.flags.has_extern or enclosing_ctx != null));
    hasher.updateU8(@intFromBool(is_effective_unsafe));
    hashExtraAttrSlice(
        &hasher,
        source,
        &parsed.token_buffer,
        &parsed.cst_arena,
        &parsed.ast_arena,
        static_extra.attr_start,
        static_extra.attr_len,
    );
    if (enclosing_ctx) |ctx| {
        hasher.updateU8(1);
        hasher.updateFingerprint(ctx.header_fingerprint);
    } else {
        hasher.updateU8(0);
    }
    hasher.updateFingerprint(computeItemSignatureFingerprint(
        source,
        &parsed.token_buffer,
        &parsed.cst_arena,
        item_cst_node,
        .none,
    ));
    return hasher.final();
}

/// Extracts the 4-tier `Visibility` (`private`, `pub_super`, `pub_pkg`, `public`) from `item_cst_node`.
fn extractItemVisibility(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst_node: CstNodeIndex,
    main_token: TokenIndex,
) Visibility {
    if (item_cst_node.isNone() or item_cst_node.asInt() >= cst_arena.countNodes()) return .private;
    const start_idx: usize = item_cst_node.asInt();
    const root_rec = cst_arena.getNode(item_cst_node);
    const end_idx: usize = @min(
        start_idx + @max(@as(usize, root_rec.subtree_size), 1),
        cst_arena.countNodes(),
    );

    var cursor: usize = start_idx + 1;
    while (cursor < end_idx) : (cursor += 1) {
        const cur_id = CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(cur_id);
        if (!node.token.isNone() and !main_token.isNone() and node.token.asInt() >= main_token.asInt()) {
            break;
        }
        if (node.kind == .visibility_modifier) {
            return symbol_resolver.extractVisibilityFromCst(source, token_buffer, cst_arena, cur_id);
        }
        if (node.kind == .attribute and node.subtree_size > 1) {
            cursor += @as(usize, node.subtree_size) - 1;
        }
    }
    return .private;
}

/// Extracts the primary identifier or description lexeme of a top-level item from its AST/CST representation.
fn extractItemNameSlice(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_kind: ItemKind,
    main_token: TokenIndex,
    item_cst_node: CstNodeIndex,
) []const u8 {
    if (item_kind == .extern_block) return "comptime";
    if (item_kind == .ffi_extern_block) return "extern";
    if (item_kind == .extern_static) {
        if (!main_token.isNone() and main_token.asInt() < token_buffer.countTokens()) {
            return getTokenLexeme(source, token_buffer, main_token);
        }
        return "";
    }
    if (item_kind == .subscript_decl) return "subscript";
    if (item_kind == .test_decl or item_kind == .bench_decl) {
        return symbol_resolver.extractTestOrBenchDescriptionSlice(
            source,
            token_buffer,
            cst_arena,
            item_cst_node,
            main_token,
        );
    }
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
            if ((node.kind == .visibility_modifier or node.kind == .attribute) and node.subtree_size > 1) {
                cursor += @as(usize, node.subtree_size) - 1;
                continue;
            }
            const is_leaf = node.subtree_size <= 1 and !node.flags.is_bracketed;
            if (!is_leaf or node.flags.is_missing_or_injected or node.token.isNone()) continue;
            if (node.token.asInt() >= token_buffer.countTokens()) continue;
            const use_tok_kind = token_buffer.getToken(node.token).kind;
            if (isIdentifierTokenKind(use_tok_kind) or use_tok_kind == .kw_async) {
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
            if ((node.kind == .type_params or node.kind == .type_args or node.kind == .where_clause or
                node.kind == .visibility_modifier or node.kind == .attribute) and
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
                    target_type_tok = node.token;
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
        if ((node.kind == .visibility_modifier or node.kind == .attribute) and node.subtree_size > 1) {
            cursor += @as(usize, node.subtree_size) - 1;
            continue;
        }
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
        if (isIdentifierTokenKind(tok_kind) or (item_kind == .mod_decl and tok_kind == .kw_async)) {
            return getTokenLexeme(source, token_buffer, node.token);
        }
    }
    return "";
}

/// Locates the direct `.block` or `.fn_expr_body` CST child inside `item_cst_node` (outside `.fn_sig`) if present.
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
        if ((node.kind == .fn_sig or node.kind == .param_list) and cursor >= sig_end_idx) {
            sig_end_idx = cursor + @max(@as(usize, node.subtree_size), 1);
            continue;
        }
        if (cursor >= sig_end_idx and (node.kind == .block or node.kind == .fn_expr_body)) {
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

/// Appends a single top-level or flattened `extern` member `ItemTreeEntry` into `entries_list`.
fn appendExtractedAstItemEntry(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    parsed: *const ParsedCstArtifact,
    is_including_tests: bool,
    item_ast_node: NodeIndex,
    enclosing_ctx: ?ExternBlockItemContext,
    entries_list: *std.ArrayList(ItemTreeEntry),
) !void {
    if (entries_list.items.len >= MAX_ITEMS_PER_FILE) return;
    if (item_ast_node.asInt() >= parsed.ast_arena.countNodes()) return;

    const ast_node = parsed.ast_arena.getNode(item_ast_node);
    const item_kind = astTagToItemKind(ast_node.tag) orelse return;
    if (!is_including_tests and (item_kind == .test_decl or item_kind == .bench_decl)) {
        return;
    }

    // Flatten `extern ["C"] { … }` blocks into individual foreign declaration `DefId`s:
    if (item_kind == .ffi_extern_block) {
        const block_header = parsed.ast_arena.getExternBlockHeader(item_ast_node);
        const block_ctx = computeExternBlockContext(source, parsed, item_ast_node, block_header);
        for (parsed.ast_arena.getExternBlockItems(item_ast_node)) |member_raw_idx| {
            if (entries_list.items.len >= MAX_ITEMS_PER_FILE) break;
            const member_ast = NodeIndex.fromInt(member_raw_idx);
            if (member_ast.asInt() >= parsed.ast_arena.countNodes()) continue;
            const member_tag = parsed.ast_arena.getNode(member_ast).tag;
            if (member_tag != .fn_decl and member_tag != .extern_static_decl and member_tag != .const_decl) {
                continue;
            }
            try appendExtractedAstItemEntry(
                allocator,
                interner,
                file_id,
                source,
                parsed,
                is_including_tests,
                member_ast,
                block_ctx,
                entries_list,
            );
        }
        return;
    }

    var item_cst_node = parsed.ast_arena.getCstOrigin(item_ast_node);
    var body_ast_node: NodeIndex = .none;
    var body_cst_node: CstNodeIndex = .none;
    if (item_kind == .fn_decl or
        item_kind == .subscript_decl or
        item_kind == .test_decl or
        item_kind == .bench_decl)
    {
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
    var visibility = if (item_kind == .extern_static) blk_vis: {
        const static_extra = parsed.ast_arena.getExternStaticExtra(item_ast_node);
        const ast_vis = externVisToVisibility(static_extra.flags.visibility);
        if (ast_vis != .private) break :blk_vis ast_vis;
        break :blk_vis extractItemVisibility(
            source,
            &parsed.token_buffer,
            &parsed.cst_arena,
            item_cst_node,
            ast_node.main_token,
        );
    } else extractItemVisibility(
        source,
        &parsed.token_buffer,
        &parsed.cst_arena,
        item_cst_node,
        ast_node.main_token,
    );
    if (visibility == .private and enclosing_ctx != null and enclosing_ctx.?.visibility != .private) {
        visibility = enclosing_ctx.?.visibility;
    }

    const sig_fp: Fingerprint128 = if (item_kind == .extern_static)
        computeExternStaticSigFingerprint(
            source,
            parsed,
            item_ast_node,
            item_cst_node,
            interned_name,
            visibility,
            enclosing_ctx,
        )
    else blk_sig: {
        const base_sig_fp = computeItemSignatureFingerprint(
            source,
            &parsed.token_buffer,
            &parsed.cst_arena,
            item_cst_node,
            body_cst_node,
        );
        if (enclosing_ctx) |ctx| {
            var mixed = StructuralHasher.init();
            mixed.updateU8(0xEC);
            mixed.updateFingerprint(ctx.header_fingerprint);
            mixed.updateFingerprint(base_sig_fp);
            break :blk_sig mixed.final();
        }
        break :blk_sig base_sig_fp;
    };

    const body_fp = if (item_kind == .extern_static)
        Fingerprint128.ZERO
    else
        computeItemBodyFingerprint(
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
        .visibility = visibility,
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

/// Extracts the position-independent `ItemTree` from `parsed` for `file_id`.
fn extractItemTreeFromAst(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    file_id: FileId,
    source: []const u8,
    parsed: *const ParsedCstArtifact,
    is_including_tests: bool,
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
                try appendExtractedAstItemEntry(
                    allocator,
                    interner,
                    file_id,
                    source,
                    parsed,
                    is_including_tests,
                    NodeIndex.fromInt(raw_node_idx),
                    null,
                    &entries_list,
                );
            }
        }
    }

    var sig_tree_hasher = StructuralHasher.init();
    sig_tree_hasher.updateU32(file_id.asInt());
    sig_tree_hasher.updateU32(@intCast(entries_list.items.len));
    for (entries_list.items) |entry| {
        sig_tree_hasher.updateU32(entry.def_id.asInt());
        sig_tree_hasher.updateU8(@backingInt(entry.kind));
        sig_tree_hasher.updateU8(@backingInt(entry.visibility));
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
        .is_including_tests = is_including_tests,
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
                .raw_blob => |rb| {
                    hasher.updateU8(7);
                    hasher.updateU32(rb.blob_id);
                    hasher.updateU8(rb.align_log2);
                    hasher.updateU64(rb.byte_len);
                },
                .source_loc => |src_loc| {
                    hasher.updateU8(8);
                    hashSymbolTextCanonical(&hasher, interner, src_loc.file_sym);
                    hashSymbolTextCanonical(&hasher, interner, src_loc.fn_sym);
                    hasher.updateU32(src_loc.line);
                    hasher.updateU32(src_loc.col);
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
            } else if (pat.kind == .at_pat) {
                pat.kind.at_pat.local_id += 1;
            } else if (pat.kind == .slice_pat and pat.kind.slice_pat.rest_local_id != hir.NONE_U32) {
                pat.kind.slice_pat.rest_local_id += 1;
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

/// Computes a cycle-safe recursive `Wyhash(0)` semantic `FieldHash64` (`DR-19` §1.2).
fn computeNominalFieldHash64Bounded(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    target_layout: TargetLayout,
    subst: *const type_system.NominalTypeSubst,
    visited_syms: []const u32,
    depth: u32,
) u64 {
    const ty = subst.resolve(raw_ty);
    var hasher = std.hash.Wyhash.init(0);
    if (ty.isError() or depth >= 32) {
        const raw_id = ty.toU32();
        hasher.update(std.mem.asBytes(&raw_id));
        return hasher.final();
    }
    const shape_key = mir_opt.computeLayoutShapeKey(pool, sym_table, ty, target_layout);
    const shape_hash = std.hash.Wyhash.hash(0, std.mem.asBytes(&shape_key));
    const tier_byte: u8 = @backingInt(type_system.classifyOwnershipTier(pool, sym_table, ty));
    if (ty.isPrimitive()) {
        const prim_raw = ty.toU32();
        hasher.update(&[_]u8{ 0x01, tier_byte });
        hasher.update(std.mem.asBytes(&prim_raw));
        hasher.update(std.mem.asBytes(&shape_hash));
        return hasher.final();
    }
    const node = pool.getNode(ty);
    hasher.update(&[_]u8{ @backingInt(node.tag), tier_byte });
    hasher.update(std.mem.asBytes(&shape_hash));
    switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .slice_ty, .soa_slice_ty => {
            const pointee_ty = subst.resolve(TypeId.fromInt(node.lhs));
            if (!pointee_ty.isPrimitiveOrSentinel()) {
                const pointee_node = pool.getNode(pointee_ty);
                if (pointee_node.tag == .struct_ty or pointee_node.tag == .enum_ty or pointee_node.tag == .union_ty) {
                    for (visited_syms) |seen_sym| {
                        if (seen_sym == pointee_node.rhs) {
                            hasher.update("cycle:");
                            if (pointee_node.rhs < sym_table.symbols.items.len) {
                                hasher.update(sym_table.getSymbol(SymbolIndex.fromInt(pointee_node.rhs)).name_text);
                            }
                            return hasher.final();
                        }
                    }
                }
            }
            const sub_h = computeNominalFieldHash64Bounded(
                pool,
                sym_table,
                pointee_ty,
                target_layout,
                subst,
                visited_syms,
                depth + 1,
            );
            hasher.update(std.mem.asBytes(&sub_h));
            hasher.update(std.mem.asBytes(&node.rhs));
        },
        .array_ty, .soa_array_ty, .optional_ty => {
            const elem_h = computeNominalFieldHash64Bounded(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
                subst,
                visited_syms,
                depth + 1,
            );
            hasher.update(std.mem.asBytes(&elem_h));
            hasher.update(std.mem.asBytes(&node.rhs));
        },
        .result_ty => {
            const ok_h = computeNominalFieldHash64Bounded(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
                subst,
                visited_syms,
                depth + 1,
            );
            const err_h = computeNominalFieldHash64Bounded(
                pool,
                sym_table,
                TypeId.fromInt(node.rhs),
                target_layout,
                subst,
                visited_syms,
                depth + 1,
            );
            hasher.update(std.mem.asBytes(&ok_h));
            hasher.update(std.mem.asBytes(&err_h));
        },
        .tuple_ty => {
            for (pool.getTupleElements(ty), 0..) |raw_elem, elem_i| {
                const elem_ord: u32 = @intCast(elem_i);
                const elem_off = type_system.computeTupleElemOffset(pool, sym_table, ty, elem_ord, target_layout) orelse 0;
                const elem_h = computeNominalFieldHash64Bounded(
                    pool,
                    sym_table,
                    TypeId.fromInt(raw_elem),
                    target_layout,
                    subst,
                    visited_syms,
                    depth + 1,
                );
                hasher.update(std.mem.asBytes(&elem_ord));
                hasher.update(std.mem.asBytes(&elem_off));
                hasher.update(std.mem.asBytes(&elem_h));
            }
        },
        .distinct_ty, .bit_field_ty => {
            if (node.rhs < sym_table.symbols.items.len) {
                const nom_sym = sym_table.getSymbol(SymbolIndex.fromInt(node.rhs)).*;
                hasher.update(nom_sym.name_text);
            }
            const base_h = computeNominalFieldHash64Bounded(
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                target_layout,
                subst,
                visited_syms,
                depth + 1,
            );
            hasher.update(std.mem.asBytes(&base_h));
        },
        .refined_ty => {
            if (pool.getRefinementBounds(ty)) |bounds| {
                hasher.update(std.mem.asBytes(&bounds.min_val));
                hasher.update(std.mem.asBytes(&bounds.max_val));
            }
            const base_h = computeNominalFieldHash64Bounded(
                pool,
                sym_table,
                TypeId.fromInt(node.rhs),
                target_layout,
                subst,
                visited_syms,
                depth + 1,
            );
            hasher.update(std.mem.asBytes(&base_h));
        },
        .struct_ty, .union_ty, .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const nom_sym = sym_table.getSymbol(sym_idx).*;
                const flags_bits: u16 = @bitCast(nom_sym.contract_flags);
                hasher.update(nom_sym.name_text);
                hasher.update(std.mem.asBytes(&flags_bits));
                hasher.update(&[_]u8{ nom_sym.explicit_align_log2_plus1, nom_sym.repr_tag_bits });
                var next_visited_buf: [32]u32 = undefined;
                const prev_len = @min(visited_syms.len, 31);
                @memcpy(next_visited_buf[0..prev_len], visited_syms[0..prev_len]);
                next_visited_buf[prev_len] = sym_idx.asInt();
                const next_visited = next_visited_buf[0 .. prev_len + 1];
                const child_subst = type_system.NominalTypeSubst.fromNominal(pool, sym_table, ty, nom_sym, subst);
                const active_subst = if (child_subst.len > 0) &child_subst else subst;
                if (!nom_sym.target_scope.isNone()) {
                    var member_ord: u32 = 0;
                    for (sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (node.tag == .enum_ty) {
                            if (mem_sym.kind != .enum_variant_sym) continue;
                            hasher.update(mem_sym.name_text);
                            hasher.update(std.mem.asBytes(&member_ord));
                            const var_h = computeNominalFieldHash64Bounded(
                                pool,
                                sym_table,
                                mem_sym.type_id,
                                target_layout,
                                active_subst,
                                next_visited,
                                depth + 1,
                            );
                            hasher.update(std.mem.asBytes(&var_h));
                            member_ord += 1;
                        } else {
                            if (mem_sym.kind != .field_sym) continue;
                            const phys_off: u64 = if (node.tag == .struct_ty)
                                (type_system.computeStructFieldOffset(
                                    pool,
                                    sym_table,
                                    ty,
                                    member_ord,
                                    target_layout,
                                ) orelse 0)
                            else
                                0;
                            hasher.update(mem_sym.name_text);
                            hasher.update(std.mem.asBytes(&member_ord));
                            hasher.update(std.mem.asBytes(&phys_off));
                            const field_h = computeNominalFieldHash64Bounded(
                                pool,
                                sym_table,
                                mem_sym.type_id,
                                target_layout,
                                active_subst,
                                next_visited,
                                depth + 1,
                            );
                            hasher.update(std.mem.asBytes(&field_h));
                            member_ord += 1;
                        }
                    }
                }
            }
        },
        else => {
            hasher.update(std.mem.asBytes(&node.lhs));
            hasher.update(std.mem.asBytes(&node.rhs));
        },
    }
    return hasher.final();
}

comptime {
    std.debug.assert(@sizeOf(Revision) == 4);
    std.debug.assert(@sizeOf(Durability) == 1);
    std.debug.assert(@sizeOf(Fingerprint128) == 16);
    std.debug.assert(@alignOf(Fingerprint128) == 8);
    std.debug.assert(@sizeOf(DefId) == 4);
    std.debug.assert(@sizeOf(FieldHash64) == 8);
    std.debug.assert(@sizeOf(GotSlotId) == 4);
    std.debug.assert(@sizeOf(QueryStage) == 1);
    std.debug.assert(@sizeOf(QueryKey) == 8);
    std.debug.assert(@alignOf(QueryKey) == 4);
    std.debug.assert(@sizeOf(MemoHeader) == 40);
    std.debug.assert(@alignOf(MemoHeader) == 8);
}

/// Recursively collects composite `TypeId`s reachable across a MIR module for `.cx_dev_meta` records.
fn discoverDevRecordTypeBounded(
    allocator: std.mem.Allocator,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    seen_set: *std.AutoHashMapUnmanaged(u32, void),
    out_ids: *std.ArrayListUnmanaged(u32),
    depth: u32,
) !void {
    if (depth >= 64) return;
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    if (unwrapped.isError() or unwrapped == .unit_ty or unwrapped == .never_ty) return;
    if (unwrapped == .str_ty) {
        if (!(try seen_set.getOrPut(allocator, TypeId.str_ty.toU32())).found_existing) {
            try out_ids.append(allocator, TypeId.str_ty.toU32());
        }
        return;
    }
    if (unwrapped.isPrimitiveOrSentinel() or unwrapped.isBuiltinGroup()) return;
    if ((try seen_set.getOrPut(allocator, unwrapped.toU32())).found_existing) return;

    const node = pool.getNode(unwrapped);
    switch (node.tag) {
        .struct_ty,
        .tuple_ty,
        .union_ty,
        .array_ty,
        .soa_array_ty,
        .slice_ty,
        .soa_slice_ty,
        .optional_ty,
        .result_ty,
        .closure_ty,
        .enum_ty,
        => try out_ids.append(allocator, unwrapped.toU32()),
        else => {},
    }

    switch (node.tag) {
        .ref_ty,
        .mut_ref_ty,
        .raw_ptr_ty,
        .slice_ty,
        .soa_slice_ty,
        .array_ty,
        .soa_array_ty,
        .optional_ty,
        .bit_field_ty,
        => {
            try discoverDevRecordTypeBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                seen_set,
                out_ids,
                depth + 1,
            );
        },
        .result_ty => {
            try discoverDevRecordTypeBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                seen_set,
                out_ids,
                depth + 1,
            );
            try discoverDevRecordTypeBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.rhs),
                seen_set,
                out_ids,
                depth + 1,
            );
        },
        .tuple_ty => {
            for (pool.getTupleElements(unwrapped)) |elem_raw| {
                try discoverDevRecordTypeBounded(
                    allocator,
                    pool,
                    sym_table,
                    TypeId.fromInt(elem_raw),
                    seen_set,
                    out_ids,
                    depth + 1,
                );
            }
        },
        .struct_ty, .union_ty, .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const nom_sym = sym_table.getSymbol(sym_idx).*;
                if (!nom_sym.target_scope.isNone()) {
                    const subst = type_system.NominalTypeSubst.init(pool, sym_table, unwrapped);
                    for (sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym and mem_sym.kind != .enum_variant_sym) continue;
                        if (mem_sym.type_id.isError() or mem_sym.type_id == unwrapped) continue;
                        try discoverDevRecordTypeBounded(
                            allocator,
                            pool,
                            sym_table,
                            subst.resolve(mem_sym.type_id),
                            seen_set,
                            out_ids,
                            depth + 1,
                        );
                    }
                }
            }
        },
        .fn_ty, .closure_ty => {
            if (pool.getFnSignatureView(unwrapped)) |sig| {
                try discoverDevRecordTypeBounded(
                    allocator,
                    pool,
                    sym_table,
                    sig.ret_ty,
                    seen_set,
                    out_ids,
                    depth + 1,
                );
                var param_i: usize = 0;
                while (param_i < sig.paramCount()) : (param_i += 1) {
                    try discoverDevRecordTypeBounded(
                        allocator,
                        pool,
                        sym_table,
                        sig.getParamType(param_i),
                        seen_set,
                        out_ids,
                        depth + 1,
                    );
                }
            }
        },
        else => {},
    }
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
    /// Active Phase 7 `TargetSpec` synchronized with `target_layout`.
    target_spec: codegen_abi.TargetSpec = codegen_abi.TargetSpec.host(),
    /// External `mod <name>;` file bindings keyed by `(parent_file_id << 32) | mod_name_sym`.
    external_mod_files: std.AutoHashMapUnmanaged(u64, FileId) = .empty,
    /// Root package/stdlib module bindings (`"core" -> core/root.cx`) keyed by `SymbolId.asInt()`.
    root_module_files: std.AutoHashMapUnmanaged(u32, FileId) = .empty,
    /// Active `--sast-strict` policy flag (`W0314` on unproven bounds checks outside `@no_panic`).
    is_sast_strict: bool = false,
    /// Active `--internal-core` privilege flag allowing direct `core.*` kernel root access (`E0218`).
    is_internal_core: bool = false,
    /// Active test/benchmark inclusion flag (`true` in `corex test` / `corex bench`, `false` in production builds).
    is_including_tests: bool = true,
    /// Monotonic counter bumped when a file's `Durability.high` stdlib privilege toggles in `setInput`.
    stdlib_privilege_epoch: u64 = 0,
    /// Optional workspace root directory path for VFS-sandboxed `@embed_bytes` (`DR-05` §3.3).
    workspace_root: ?[]const u8 = null,
    /// Optional Zig `Io` handle for disk-backed `@embed_bytes` inside `workspace_root`.
    embed_io: ?std.Io = null,
    /// Optional in-memory virtual file map (`relative_path -> bytes`) for `@embed_bytes`.
    virtual_files: ?*const std.StringHashMapUnmanaged([]const u8) = null,
    /// Monotonic counter bumped on every `setEmbedSandbox` / `setEmbedIo` mutation.
    embed_sandbox_epoch: u64 = 0,
    /// Last-changed revisions for synthetic config keys `0xFFFF_FFF0..0xFFFF_FFF5`.
    config_changed_at: [6]Revision = .{ .initial, .initial, .initial, .initial, .initial, .initial },
    /// Deduplicated `.rodata` constant pool shared across `MirVm` evaluations.
    rodata_pool: mir_vm.RodataPool,
    /// Bounded `Wyhash(0)` pure-call memoization cache shared across `MirVm` runs.
    pure_call_memo_cache: mir_vm.PureCallMemoCache,
    /// Per-file semantic side tables (`@attribute_schema` instances) keyed by `FileId.asInt()`.
    file_side_tables: std.AutoHashMapUnmanaged(u32, BodySemanticSideTables) = .empty,
    /// Per-file signature AST synchronization watermarks keyed by `FileId.asInt()` (`SE-07`).
    file_sig_sync_states: std.AutoHashMapUnmanaged(u32, FileSigSyncState) = .empty,
    /// Per-definition windowed semantic side tables keyed by `DefId.asInt()`.
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
    /// Bounded content-addressed LRU cache for `@c_import` header translations (`128` entries / `16 MiB`).
    c_import_cache: CImportCache = .{},
    /// Next 20-bit virtual `FileId` counter allocated for cached `@c_import` modules (`Durability.medium`).
    next_virtual_c_import_file_id: u32 = VIRTUAL_C_IMPORT_FILE_ID_BASE,
    /// Owned `-DNAME` / `-DNAME=VAL` strings included in `@c_import` cache keys and `c_frontend`.
    c_import_defines: std.ArrayListUnmanaged([]u8) = .empty,
    /// Owned `-Idir` search directory paths consulted by `@c_import` and `#include`.
    c_import_include_dirs: std.ArrayListUnmanaged([]u8) = .empty,
    /// Optional source file path map keyed by `FileId.asInt()` for caller-relative `@c_import` resolution.
    file_paths: std.AutoHashMapUnmanaged(u32, []u8) = .empty,
    /// Cached `.module_sym` `SymbolIndex` handles keyed by virtual `@c_import` `FileId.asInt()`.
    c_import_mod_syms: std.AutoHashMapUnmanaged(u32, SymbolIndex) = .empty,
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

        const host_spec = codegen_abi.TargetSpec.host();
        var symbol_table = try SymbolTable.init(allocator, &interner);
        symbol_table.cfg_env = type_system.CfgEnv.fromTargetSpec(host_spec, true);
        symbol_table.refreshCxFfiTargetAliases(&interner);
        symbol_table.c_import_loader = &loadCImportFromDb;

        return .{
            .allocator = allocator,
            .interner = interner,
            .type_pool = type_pool,
            .symbol_table = symbol_table,
            .target_spec = host_spec,
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
        self.file_sig_sync_states.deinit(self.allocator);

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

        self.c_import_cache.deinit(self.allocator);
        for (self.c_import_defines.items) |owned_def| self.allocator.free(owned_def);
        self.c_import_defines.deinit(self.allocator);
        for (self.c_import_include_dirs.items) |owned_dir| self.allocator.free(owned_dir);
        self.c_import_include_dirs.deinit(self.allocator);
        var fp_iter = self.file_paths.valueIterator();
        while (fp_iter.next()) |owned_path| self.allocator.free(owned_path.*);
        self.file_paths.deinit(self.allocator);
        self.c_import_mod_syms.deinit(self.allocator);
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
        self.external_mod_files.deinit(self.allocator);
        self.root_module_files.deinit(self.allocator);
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

    /// Computes the 128-bit fingerprint of a synthetic Stage-0 compiler config key.
    fn computeConfigFingerprint(self: *const CompilerDb, config_entity: u32) Fingerprint128 {
        var hasher = StructuralHasher.init();
        hasher.updateU32(config_entity);
        switch (config_entity) {
            CONFIG_KEY_TARGET_LAYOUT => {
                hasher.updateU8(@backingInt(self.target_spec.arch));
                hasher.updateU8(@backingInt(self.target_spec.os));
                hasher.updateU8(@backingInt(self.target_spec.abi));
                hasher.updateU8(@backingInt(self.target_spec.simd_level));
                hasher.updateU8(self.target_layout.ptr_byte_size);
                hasher.updateU8(self.target_layout.ptr_align_log2);
                hasher.updateU8(self.target_layout.cache_line_align_log2);
                hasher.updateU8(self.target_layout.simd_align_log2);
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
            CONFIG_KEY_INTERNAL_CORE => {
                hasher.updateU8(@intFromBool(self.is_internal_core));
                hasher.updateU64(self.stdlib_privilege_epoch);
            },
            CONFIG_KEY_INCLUDE_TESTS => {
                hasher.updateU8(@intFromBool(self.is_including_tests));
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

    /// Reads `target_layout` while recording a tracked dependency on `CONFIG_KEY_TARGET_LAYOUT`.
    pub fn readTargetLayout(self: *CompilerDb) QueryError!TargetLayout {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_TARGET_LAYOUT));
        return self.target_layout;
    }

    /// Reads `comptime_step_limit` while recording a tracked dependency on `CONFIG_KEY_COMPTIME_LIMIT`.
    pub fn readComptimeStepLimit(self: *CompilerDb) QueryError!u64 {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_COMPTIME_LIMIT));
        return self.comptime_step_limit;
    }

    /// Reads `is_sast_strict` while recording a tracked dependency on `CONFIG_KEY_SAST_STRICT`.
    pub fn readSastStrict(self: *CompilerDb) QueryError!bool {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_SAST_STRICT));
        return self.is_sast_strict;
    }

    /// Reads `is_internal_core` while recording a tracked dependency on `CONFIG_KEY_INTERNAL_CORE`.
    pub fn readInternalCore(self: *CompilerDb) bool {
        _ = self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_INTERNAL_CORE)) catch {};
        return self.is_internal_core;
    }

    /// Reads `is_including_tests` while recording a tracked dependency on `CONFIG_KEY_INCLUDE_TESTS`.
    pub fn readIncludeTests(self: *CompilerDb) QueryError!bool {
        _ = try self.fetchQuery(QueryKey.forConfig(CONFIG_KEY_INCLUDE_TESTS));
        return self.is_including_tests;
    }

    /// Records a tracked dependency on `CONFIG_KEY_EMBED_SANDBOX` whenever `@embed_bytes` queries sandbox state.
    pub fn recordEmbedSandboxDependency(self: *CompilerDb) QueryError!QueryKey {
        const cfg_key = QueryKey.forConfig(CONFIG_KEY_EMBED_SANDBOX);
        _ = try self.fetchQuery(cfg_key);
        return cfg_key;
    }

    /// Records a tracked content-hashed dependency for an `@embed_bytes` or `@c_import` file read.
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

    /// Re-probes the current VFS or disk content fingerprint of a tracked `@embed_bytes` or `@c_import` path.
    fn probeEmbeddedFileFingerprint(self: *CompilerDb, path_sym: SymbolId) Fingerprint128 {
        const rel_path = self.interner.get(path_sym);
        if (self.virtual_files) |vfs_map| {
            if (vfs_map.get(rel_path)) |vfs_bytes| {
                return Fingerprint128.hashBytes(vfs_bytes);
            }
        }
        if (mir_vm.isValidSandboxedEmbedPath(rel_path)) {
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
        } else if (self.embed_io) |io_handle| {
            if (std.Io.Dir.cwd().readFileAlloc(
                io_handle,
                rel_path,
                self.allocator,
                .limited(16 * 1024 * 1024),
            )) |disk_bytes| {
                defer self.allocator.free(disk_bytes);
                return Fingerprint128.hashBytes(disk_bytes);
            } else |_| {}
        }
        if (c_frontend.BUNDLED_SYSTEM_HEADERS.get(rel_path)) |bundled_src| {
            return Fingerprint128.hashBytes(bundled_src);
        }
        var missing_hasher = StructuralHasher.init();
        missing_hasher.updateU8(0xEE);
        missing_hasher.updateBytes(rel_path);
        return missing_hasher.final();
    }

    /// Loads live bytes for a recorded `@c_import` `#include` path from `virtual_files`, `embed_io`, or `workspace_root`.
    fn loadTrackedCImportIncludeBytes(
        self: *CompilerDb,
        inc_path: []const u8,
        out_owned_bytes: *?[]u8,
    ) ?[]const u8 {
        if (self.virtual_files) |vfs_map| {
            if (vfs_map.get(inc_path)) |vfs_bytes| return vfs_bytes;
        }
        if (self.embed_io) |io_handle| {
            if (std.Io.Dir.cwd().readFileAlloc(
                io_handle,
                inc_path,
                self.allocator,
                .limited(16 * 1024 * 1024),
            )) |direct_bytes| {
                out_owned_bytes.* = direct_bytes;
                return direct_bytes;
            } else |_| {}

            if (self.workspace_root) |ws_root| {
                if (std.fs.path.join(self.allocator, &.{ ws_root, inc_path })) |joined_ws| {
                    defer self.allocator.free(joined_ws);
                    if (std.Io.Dir.cwd().readFileAlloc(
                        io_handle,
                        joined_ws,
                        self.allocator,
                        .limited(16 * 1024 * 1024),
                    )) |ws_bytes| {
                        out_owned_bytes.* = ws_bytes;
                        return ws_bytes;
                    } else |_| {}
                } else |_| {}
            }
        }
        return null;
    }

    /// Updates `--comptime-limit` (`comptime_step_limit`) and bumps `current_revision` when changed.
    pub fn setComptimeStepLimit(self: *CompilerDb, new_limit: u64) void {
        if (self.comptime_step_limit == new_limit) return;
        self.comptime_step_limit = new_limit;
        self.bumpConfigInput(CONFIG_KEY_COMPTIME_LIMIT);
    }

    /// Updates `target_layout` (`NATIVE_64`, `AARCH64_MACOS`, `WASM32`, …) and bumps `current_revision` when changed.
    pub fn setTargetLayout(self: *CompilerDb, new_layout: TargetLayout) void {
        if (self.target_layout.ptr_byte_size == new_layout.ptr_byte_size and
            self.target_layout.ptr_align_log2 == new_layout.ptr_align_log2 and
            self.target_layout.cache_line_align_log2 == new_layout.cache_line_align_log2 and
            self.target_layout.simd_align_log2 == new_layout.simd_align_log2)
        {
            return;
        }
        self.target_layout = new_layout;
        self.bumpConfigInput(CONFIG_KEY_TARGET_LAYOUT);
    }

    /// Updates `target_spec` and synchronizes `target_layout` and `cx.ffi` aliases across all `(arch, os, abi)` targets.
    pub fn setTargetSpec(self: *CompilerDb, new_spec: codegen_abi.TargetSpec) void {
        const new_layout = new_spec.asTargetLayout();
        const has_spec_changed = self.target_spec.arch != new_spec.arch or
            self.target_spec.os != new_spec.os or
            self.target_spec.abi != new_spec.abi or
            self.target_spec.simd_level != new_spec.simd_level;
        const has_layout_changed = self.target_layout.ptr_byte_size != new_layout.ptr_byte_size or
            self.target_layout.ptr_align_log2 != new_layout.ptr_align_log2 or
            self.target_layout.cache_line_align_log2 != new_layout.cache_line_align_log2 or
            self.target_layout.simd_align_log2 != new_layout.simd_align_log2;
        self.symbol_table.cfg_env = type_system.CfgEnv.fromTargetSpec(new_spec, self.is_including_tests);
        self.symbol_table.refreshCxFfiTargetAliases(&self.interner);
        if (!has_spec_changed and !has_layout_changed) return;
        self.target_spec = new_spec;
        self.target_layout = new_layout;
        self.bumpConfigInput(CONFIG_KEY_TARGET_LAYOUT);
    }

    /// Computes the 128-bit `@c_import` cache key over `header_source_bytes`, `target_spec`, `defines`, and `include_dirs`.
    pub inline fn computeCImportKey(
        self: *const CompilerDb,
        header_source_bytes: []const u8,
        defines: []const []const u8,
    ) Fingerprint128 {
        return CImportCache.computeKey(
            header_source_bytes,
            self.target_spec,
            defines,
            self.c_import_include_dirs.items,
        );
    }

    /// Looks up a cached `@c_import` translation, verifying and recording all transitive `#include` digests.
    pub fn lookupCImportCache(
        self: *CompilerDb,
        header_source_bytes: []const u8,
        defines: []const []const u8,
    ) ?CImportCacheView {
        const cache_key = self.computeCImportKey(header_source_bytes, defines);
        const peeked = self.c_import_cache.peek(cache_key) orelse {
            self.c_import_cache.misses += 1;
            return null;
        };
        if (peeked.included_files.len == 0) {
            return self.c_import_cache.get(cache_key);
        }

        const VerifiedIncludeRead = struct {
            path: []const u8,
            bytes: []const u8,
            owned_buf: ?[]u8,
        };
        var verified_reads: std.ArrayListUnmanaged(VerifiedIncludeRead) = .empty;
        defer {
            for (verified_reads.items) |read_item| {
                if (read_item.owned_buf) |owned_slice| self.allocator.free(owned_slice);
            }
            verified_reads.deinit(self.allocator);
        }

        for (peeked.included_files) |inc_dep| {
            var owned_inc_buf: ?[]u8 = null;
            const live_bytes = self.loadTrackedCImportIncludeBytes(inc_dep.owned_path, &owned_inc_buf) orelse {
                self.c_import_cache.misses += 1;
                return null;
            };
            var live_blake3: [32]u8 = undefined;
            std.crypto.hash.Blake3.hash(live_bytes, &live_blake3, .{});
            if (!std.mem.eql(u8, &live_blake3, &inc_dep.content_blake3)) {
                if (owned_inc_buf) |buf| self.allocator.free(buf);
                self.c_import_cache.misses += 1;
                return null;
            }
            verified_reads.append(self.allocator, .{
                .path = inc_dep.owned_path,
                .bytes = live_bytes,
                .owned_buf = owned_inc_buf,
            }) catch {
                if (owned_inc_buf) |buf| self.allocator.free(buf);
                self.c_import_cache.misses += 1;
                return null;
            };
        }

        for (verified_reads.items) |read_item| {
            _ = self.recordEmbeddedFileRead(read_item.path, read_item.bytes) catch {};
        }
        return self.c_import_cache.get(cache_key);
    }

    /// Extracts the owning `FileId` targeted by `key`, or `null` for synthetic config and `@embed_bytes` keys.
    fn queryKeyTargetFileId(key: QueryKey) ?FileId {
        return switch (key.stage) {
            .source_text => {
                if ((key.flags & EMBED_FILE_KEY_FLAG) != 0 or key.entity_index >= CONFIG_KEY_TARGET_LAYOUT) {
                    return null;
                }
                return FileId.fromInt(key.entity_index);
            },
            .parse_cst, .lower_ast, .item_tree, .resolve_signatures, .optimize_mir_module => {
                return FileId.fromInt(key.entity_index);
            },
            .item_tree_sig_proj,
            .body_ast_proj,
            .def_signature,
            .typecheck_body,
            .verify_sast_mir,
            .lower_def_hir,
            .build_def_mir,
            .eval_comptime_def,
            => DefId.fromInt(key.entity_index).fileId(),
        };
    }

    /// Unpacks a 64-bit `memos` hash-table key back into its structured `QueryKey`.
    inline fn unpackQueryKeyU64(raw_key: u64) QueryKey {
        return .{
            .stage = @fromBackingInt(@as(u8, @truncate(raw_key))),
            .flags = @as(u8, @truncate(raw_key >> 8)),
            .reserved = @as(u16, @truncate(raw_key >> 16)),
            .entity_index = @as(u32, @truncate(raw_key >> 32)),
        };
    }

    /// Returns `true` when any query currently on `active_stack` directly targets `target_fid`.
    fn isFileIdInFlight(self: *const CompilerDb, target_fid: FileId) bool {
        for (self.active_stack.items) |active_frame| {
            if (queryKeyTargetFileId(active_frame.key)) |frame_fid| {
                if (frame_fid == target_fid) return true;
            }
        }
        return false;
    }

    /// Collects all raw `DefId` keys in `map` whose owning `FileId` equals `target_fid`.
    fn collectMatchingDefMapKeys(
        allocator: std.mem.Allocator,
        comptime ValType: type,
        map: *const std.AutoHashMapUnmanaged(u32, ValType),
        target_fid: FileId,
        out_keys: *std.ArrayListUnmanaged(u32),
    ) !void {
        out_keys.clearRetainingCapacity();
        var key_iter = map.keyIterator();
        while (key_iter.next()) |def_raw_ptr| {
            if (DefId.fromInt(def_raw_ptr.*).fileId() == target_fid) {
                try out_keys.append(allocator, def_raw_ptr.*);
            }
        }
    }

    /// Purges cached artifacts and `memos` belonging to an evicted or mid-query-updated virtual `FileId`.
    fn purgeVirtualFileArtifacts(
        self: *CompilerDb,
        target_fid: FileId,
        is_removing_source_input: bool,
    ) void {
        if (target_fid.isNone() or self.isFileIdInFlight(target_fid)) return;
        const fid_raw = target_fid.asInt();

        if (is_removing_source_input) {
            if (self.source_inputs.fetchRemove(fid_raw)) |removed_kv| {
                self.allocator.free(removed_kv.value.owned_text);
            }
            if (self.file_paths.fetchRemove(fid_raw)) |removed_kv| {
                self.allocator.free(removed_kv.value);
            }
            _ = self.c_import_mod_syms.remove(fid_raw);
        }

        if (self.parsed_artifacts.fetchRemove(fid_raw)) |removed_kv| {
            var artifact_val = removed_kv.value;
            artifact_val.deinit();
        }
        _ = self.lowered_artifacts.remove(fid_raw);
        if (self.item_trees.fetchRemove(fid_raw)) |removed_kv| {
            var tree_val = removed_kv.value;
            tree_val.deinit(self.allocator);
        }
        _ = self.resolved_signatures.remove(fid_raw);
        if (self.file_side_tables.fetchRemove(fid_raw)) |removed_kv| {
            var side_val = removed_kv.value;
            side_val.deinit();
        }
        _ = self.file_sig_sync_states.remove(fid_raw);
        if (self.sig_diagnostics.fetchRemove(fid_raw)) |removed_kv| {
            var sink_val = removed_kv.value;
            sink_val.deinit();
        }
        _ = self.symbol_table.file_module_scopes.remove(fid_raw);

        for ([_]bool{ false, true }) |is_release_mode| {
            const opt_key = QueryKey.forFileMode(.optimize_mir_module, target_fid, is_release_mode).asU64();
            if (self.optimized_mir_modules.fetchRemove(opt_key)) |removed_kv| {
                var opt_val = removed_kv.value;
                opt_val.deinit();
            }
            if (self.opt_diagnostics.fetchRemove(opt_key)) |removed_kv| {
                var sink_val = removed_kv.value;
                sink_val.deinit();
            }
        }

        var scratch_def_keys: std.ArrayListUnmanaged(u32) = .empty;
        defer scratch_def_keys.deinit(self.allocator);

        if (collectMatchingDefMapKeys(self.allocator, BodyAstWindow, &self.body_windows, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| _ = self.body_windows.remove(def_raw);
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, DefSignatureArtifact, &self.def_signatures, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| _ = self.def_signatures.remove(def_raw);
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, TypedBodyArtifact, &self.typed_bodies, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| _ = self.typed_bodies.remove(def_raw);
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, SastVerificationArtifact, &self.sast_results, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| _ = self.sast_results.remove(def_raw);
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, mir_sast.FnRegionSummary, &self.sast_summaries, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| _ = self.sast_summaries.remove(def_raw);
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, ComptimeEvalArtifact, &self.evaluated_comptime_defs, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| _ = self.evaluated_comptime_defs.remove(def_raw);
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, BodySemanticSideTables, &self.def_side_tables, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| {
                if (self.def_side_tables.fetchRemove(def_raw)) |removed_kv| {
                    var side_val = removed_kv.value;
                    side_val.deinit();
                }
            }
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, hir.HirStore, &self.lowered_def_hirs, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| {
                if (self.lowered_def_hirs.fetchRemove(def_raw)) |removed_kv| {
                    var hir_val = removed_kv.value;
                    hir_val.deinit();
                }
            }
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, DefMirArtifact, &self.built_def_mirs, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| {
                if (self.built_def_mirs.fetchRemove(def_raw)) |removed_kv| {
                    var mir_val = removed_kv.value;
                    mir_val.deinit();
                }
            }
        } else |_| {}
        if (collectMatchingDefMapKeys(self.allocator, ComptimeElabMirEntry, &self.comptime_elab_mirs, target_fid, &scratch_def_keys)) |_| {
            for (scratch_def_keys.items) |def_raw| {
                if (self.comptime_elab_mirs.fetchRemove(def_raw)) |removed_kv| {
                    var elab_val = removed_kv.value;
                    elab_val.deinit();
                }
            }
        } else |_| {}
        if (collectMatchingDefMapKeys(
            self.allocator,
            std.ArrayListUnmanaged(DefId),
            &self.sast_cycle_peers,
            target_fid,
            &scratch_def_keys,
        )) |_| {
            for (scratch_def_keys.items) |def_raw| {
                if (self.sast_cycle_peers.fetchRemove(def_raw)) |removed_kv| {
                    var peer_list = removed_kv.value;
                    peer_list.deinit(self.allocator);
                }
            }
        } else |_| {}

        const diag_maps = [_]*std.AutoHashMapUnmanaged(u32, DiagnosticSink){
            &self.body_diagnostics,
            &self.sast_diagnostics,
            &self.hir_diagnostics,
            &self.mir_diagnostics,
            &self.comptime_diagnostics,
        };
        for (diag_maps) |diag_map_ptr| {
            if (collectMatchingDefMapKeys(self.allocator, DiagnosticSink, diag_map_ptr, target_fid, &scratch_def_keys)) |_| {
                for (scratch_def_keys.items) |def_raw| {
                    if (diag_map_ptr.fetchRemove(def_raw)) |removed_kv| {
                        var sink_val = removed_kv.value;
                        sink_val.deinit();
                    }
                }
            } else |_| {}
        }

        var scratch_memo_keys: std.ArrayListUnmanaged(u64) = .empty;
        defer scratch_memo_keys.deinit(self.allocator);
        var memo_key_iter = self.memos.keyIterator();
        while (memo_key_iter.next()) |raw_key_ptr| {
            const unpacked_key = unpackQueryKeyU64(raw_key_ptr.*);
            if (!is_removing_source_input and unpacked_key.stage == .source_text) continue;
            if (queryKeyTargetFileId(unpacked_key)) |memo_fid| {
                if (memo_fid == target_fid) {
                    scratch_memo_keys.append(self.allocator, raw_key_ptr.*) catch break;
                }
            }
        }
        for (scratch_memo_keys.items) |memo_raw_key| {
            _ = self.memos.remove(memo_raw_key);
        }
    }

    /// Registers a translated `@c_import` `.cx` module in `c_import_cache` and `source_inputs` (`Durability.medium`).
    pub fn storeCImportTranslation(
        self: *CompilerDb,
        header_source_bytes: []const u8,
        defines: []const []const u8,
        translated_cx_text: []const u8,
        explicit_file_id: ?FileId,
    ) !FileId {
        return self.storeCImportTranslationWithIncludes(
            header_source_bytes,
            defines,
            translated_cx_text,
            &.{},
            explicit_file_id,
        );
    }

    /// Registers a translated `@c_import` `.cx` module and its transitive `included_files` in `c_import_cache`.
    pub fn storeCImportTranslationWithIncludes(
        self: *CompilerDb,
        header_source_bytes: []const u8,
        defines: []const []const u8,
        translated_cx_text: []const u8,
        included_files: []const c_frontend.RecordedIncludeFile,
        explicit_file_id: ?FileId,
    ) !FileId {
        const cache_key = self.computeCImportKey(header_source_bytes, defines);
        const virtual_fid: FileId = if (explicit_file_id) |given_fid|
            given_fid
        else if (self.c_import_cache.peek(cache_key)) |existing_view|
            existing_view.virtual_file_id
        else blk_alloc_fid: {
            const raw_fid = self.next_virtual_c_import_file_id;
            if (self.next_virtual_c_import_file_id < 0x000F_FFFE) {
                self.next_virtual_c_import_file_id += 1;
            }
            break :blk_alloc_fid FileId.fromInt(raw_fid);
        };
        var evicted_fids: std.ArrayListUnmanaged(FileId) = .empty;
        defer evicted_fids.deinit(self.allocator);
        _ = try self.setInput(virtual_fid, translated_cx_text, .medium);
        _ = try self.c_import_cache.putWithIncludesAndEvicted(
            self.allocator,
            cache_key,
            translated_cx_text,
            included_files,
            virtual_fid,
            &evicted_fids,
        );
        for (evicted_fids.items) |evicted_fid| {
            if (evicted_fid != virtual_fid) {
                self.purgeVirtualFileArtifacts(evicted_fid, true);
            }
        }
        return virtual_fid;
    }

    /// Returns the active Phase 7 `TargetSpec` configured on `self`.
    pub inline fn getTargetSpec(self: *const CompilerDb) codegen_abi.TargetSpec {
        return self.target_spec;
    }

    /// Binds an external `mod <mod_name>;` declaration in `parent_file_id` to `child_file_id`.
    pub fn bindExternalModule(
        self: *CompilerDb,
        parent_file_id: FileId,
        mod_name: []const u8,
        child_file_id: FileId,
    ) !void {
        const parent_pkg = self.symbol_table.getFilePackageId(parent_file_id);
        if (parent_pkg != .root and self.symbol_table.getFilePackageId(child_file_id) == .root) {
            try self.symbol_table.setFilePackageId(child_file_id, parent_pkg);
        }
        const mod_sym = try self.interner.intern(mod_name);
        const key: u64 = (@as(u64, parent_file_id.asInt()) << 32) | @as(u64, mod_sym.asInt());
        if (self.external_mod_files.get(key)) |existing_fid| {
            if (existing_fid == child_file_id) return;
        }
        try self.external_mod_files.put(self.allocator, key, child_file_id);
        self.bumpConfigInput(CONFIG_KEY_TARGET_LAYOUT);
    }

    /// Registers a root module prefix (such as `"core" -> core/root.cx`) visible across workspace files.
    pub fn registerRootModule(
        self: *CompilerDb,
        mod_name: []const u8,
        root_file_id: FileId,
    ) !void {
        const mod_sym = try self.interner.intern(mod_name);
        var has_changed = false;
        if (self.root_module_files.get(mod_sym.asInt()) != root_file_id) {
            try self.root_module_files.put(self.allocator, mod_sym.asInt(), root_file_id);
            has_changed = true;
        }
        if (std.mem.eql(u8, mod_name, "core")) {
            if (self.symbol_table.getFilePackageId(root_file_id) == .root) {
                try self.symbol_table.setFilePackageId(root_file_id, .std_core);
            }
            const cx_sym = try self.interner.intern("cx");
            if (!self.root_module_files.contains(cx_sym.asInt())) {
                try self.root_module_files.put(self.allocator, cx_sym.asInt(), root_file_id);
                has_changed = true;
            }
        }
        if (has_changed) {
            self.bumpConfigInput(CONFIG_KEY_TARGET_LAYOUT);
        }
    }

    /// Assigns `pkg_id` to `file_id` for `pub(pkg)` visibility enforcement (`ADR-22E`).
    pub fn setFilePackageId(self: *CompilerDb, file_id: FileId, pkg_id: PackageId) !void {
        if (self.symbol_table.getFilePackageId(file_id) == pkg_id) return;
        try self.symbol_table.setFilePackageId(file_id, pkg_id);
        self.bumpConfigInput(CONFIG_KEY_TARGET_LAYOUT);
    }

    /// Returns the `PackageId` currently assigned to `file_id` (`.root` by default).
    pub inline fn getFilePackageId(self: *const CompilerDb, file_id: FileId) PackageId {
        return self.symbol_table.getFilePackageId(file_id);
    }

    /// Updates `--sast-strict` (`is_sast_strict`) and bumps `current_revision` when changed.
    pub fn setSastStrict(self: *CompilerDb, is_strict: bool) void {
        if (self.is_sast_strict == is_strict) return;
        self.is_sast_strict = is_strict;
        self.bumpConfigInput(CONFIG_KEY_SAST_STRICT);
    }

    /// Updates `--internal-core` (`is_internal_core`) and bumps `current_revision` when changed.
    pub fn setInternalCore(self: *CompilerDb, is_enabled: bool) !void {
        if (self.is_internal_core == is_enabled) return;
        self.is_internal_core = is_enabled;
        self.bumpConfigInput(CONFIG_KEY_INTERNAL_CORE);
    }

    /// Updates `is_including_tests` (`test` / `bench` retention) and invalidates `CONFIG_KEY_INCLUDE_TESTS` without reparsing CSTs.
    pub fn setIncludeTests(self: *CompilerDb, is_enabled: bool) void {
        if (self.is_including_tests == is_enabled) return;
        self.is_including_tests = is_enabled;
        self.symbol_table.is_including_tests = is_enabled;
        self.bumpConfigInput(CONFIG_KEY_INCLUDE_TESTS);
    }

    /// Resolves `target_file`'s signatures (recording query dependency) and returns its syntax + side-table view.
    pub fn getExternalFileSyntaxView(
        self: *CompilerDb,
        target_file: FileId,
    ) QueryError!?ExternalFileSyntaxView {
        if (target_file.isNone()) return null;
        if (!self.in_flight_keys.contains(QueryKey.forFile(.parse_cst, target_file).asU64())) {
            _ = try self.parseCst(target_file);
        }
        if (!self.in_flight_keys.contains(QueryKey.forFile(.resolve_signatures, target_file).asU64())) {
            _ = try self.resolveSignatures(target_file);
        }
        const input_ptr = self.source_inputs.getPtr(target_file.asInt()) orelse return null;
        const parsed_ptr = self.parsed_artifacts.getPtr(target_file.asInt()) orelse return null;
        return .{
            .source = input_ptr.owned_text,
            .tokens = &parsed_ptr.token_buffer,
            .cst_arena = &parsed_ptr.cst_arena,
            .ast_arena = &parsed_ptr.ast_arena,
            .file_side_tables = self.file_side_tables.getPtr(target_file.asInt()),
        };
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

    /// Associates `file_id` with its virtual or filesystem `path` for caller-relative `@c_import` lookups.
    pub fn setFilePath(self: *CompilerDb, file_id: FileId, path: []const u8) !void {
        const cloned_path = try self.allocator.dupe(u8, path);
        errdefer self.allocator.free(cloned_path);
        if (try self.file_paths.fetchPut(self.allocator, file_id.asInt(), cloned_path)) |prev_kv| {
            self.allocator.free(prev_kv.value);
        }
    }

    /// Configures `-D` macro defines (`"NAME"` / `"NAME=VAL"`) and `-I` include directories for `@c_import`.
    pub fn setCImportConfig(
        self: *CompilerDb,
        defines: []const []const u8,
        include_dirs: []const []const u8,
    ) !void {
        for (self.c_import_defines.items) |old_def| self.allocator.free(old_def);
        self.c_import_defines.clearRetainingCapacity();
        for (defines) |def_str| {
            const duped_def = try self.allocator.dupe(u8, def_str);
            errdefer self.allocator.free(duped_def);
            try self.c_import_defines.append(self.allocator, duped_def);
        }

        for (self.c_import_include_dirs.items) |old_dir| self.allocator.free(old_dir);
        self.c_import_include_dirs.clearRetainingCapacity();
        for (include_dirs) |dir_str| {
            const duped_dir = try self.allocator.dupe(u8, dir_str);
            errdefer self.allocator.free(duped_dir);
            try self.c_import_include_dirs.append(self.allocator, duped_dir);
        }

        self.embed_sandbox_epoch +%= 1;
        self.bumpConfigInput(CONFIG_KEY_EMBED_SANDBOX);
    }

    /// Strongly typed `SymbolTable.c_import_loader` callback bridging `@c_import` through `CompilerDb` (`DR-10`, `@fieldParentPtr`).
    fn loadCImportFromDb(
        sym_table: *SymbolTable,
        interner: *StringInterner,
        caller_file_id: FileId,
        header_path: []const u8,
        diagnostic_sink: ?*DiagnosticSink,
    ) anyerror!SymbolIndex {
        const db: *CompilerDb = @fieldParentPtr("symbol_table", sym_table);
        if (header_path.len == 0) return .none;

        // [1] Resolve `header_path` bytes and resolved path from VFS, caller dir, `workspace_root`, `-I`, or bundled:
        var owned_disk_bytes: ?[]u8 = null;
        defer if (owned_disk_bytes) |buf| db.allocator.free(buf);
        var owned_resolved_path: ?[]u8 = null;
        defer if (owned_resolved_path) |path_buf| db.allocator.free(path_buf);
        const resolved_hdr = (try db.resolveCImportHeaderSource(
            caller_file_id,
            header_path,
            &owned_disk_bytes,
            &owned_resolved_path,
        )) orelse return .none;

        // Record tracked sandbox and file-read dependencies so `-D`/`-I` or header edits invalidate signatures:
        _ = db.recordEmbedSandboxDependency() catch {};
        _ = db.recordEmbeddedFileRead(resolved_hdr.resolved_path, resolved_hdr.bytes) catch {};

        // [2] Probe `CImportCache` (`128` entries / `16 MiB` bounded LRU; replays transitive `#include` reads on hit):
        var virtual_fid: FileId = .none;
        if (db.lookupCImportCache(resolved_hdr.bytes, db.c_import_defines.items)) |cached_view| {
            virtual_fid = cached_view.virtual_file_id;
        } else {
            var macro_defs: std.ArrayListUnmanaged(c_frontend.MacroDefine) = .empty;
            defer macro_defs.deinit(db.allocator);
            for (db.c_import_defines.items) |def_text| {
                if (std.mem.indexOfScalar(u8, def_text, '=')) |eq_pos| {
                    try macro_defs.append(db.allocator, .{
                        .name = def_text[0..eq_pos],
                        .value = def_text[eq_pos + 1 ..],
                    });
                } else {
                    try macro_defs.append(db.allocator, .{ .name = def_text, .value = null });
                }
            }

            var vfs_headers: std.ArrayListUnmanaged(c_frontend.VirtualHeaderEntry) = .empty;
            defer vfs_headers.deinit(db.allocator);
            if (db.virtual_files) |vfs_map| {
                var vfs_it = vfs_map.iterator();
                while (vfs_it.next()) |kv| {
                    try vfs_headers.append(db.allocator, .{
                        .path = kv.key_ptr.*,
                        .content = kv.value_ptr.*,
                    });
                }
            }

            var search_dirs: std.ArrayListUnmanaged([]const u8) = .empty;
            defer search_dirs.deinit(db.allocator);
            if (db.file_paths.get(caller_file_id.asInt())) |caller_path| {
                if (std.fs.path.dirname(caller_path)) |caller_dir| {
                    try search_dirs.append(db.allocator, caller_dir);
                }
            }
            if (db.workspace_root) |ws_root| {
                try search_dirs.append(db.allocator, ws_root);
            }
            for (db.c_import_include_dirs.items) |inc_dir| {
                try search_dirs.append(db.allocator, inc_dir);
            }

            var local_sink = DiagnosticSink.init(db.allocator);
            defer local_sink.deinit();
            const active_sink = diagnostic_sink orelse &local_sink;

            const frontend_opts = c_frontend.CFrontendOptions{
                .target = db.target_spec,
                .defines = macro_defs.items,
                .include_dirs = search_dirs.items,
                .virtual_headers = vfs_headers.items,
                .include_loader = if (db.embed_io) |io_h| .{ .host_fs = io_h } else .none,
            };
            var unit = c_frontend.parseCHeader(
                db.allocator,
                resolved_hdr.bytes,
                resolved_hdr.resolved_path,
                caller_file_id,
                frontend_opts,
                active_sink,
            ) catch |err| switch (err) {
                error.TranslationFailed => return .none,
                else => return err,
            };
            defer unit.deinit();

            const translated_cx = c_translate.translateUnit(
                db.allocator,
                &unit,
                .{},
            ) catch |err| switch (err) {
                error.InvalidTranslatedSyntax => {
                    try active_sink.emit(.{
                        .code = .e0009_c_header_translation_failed,
                        .severity = .err,
                        .primary_span = .{ .file_id = caller_file_id, .start_byte = 0, .end_byte = 0 },
                        .message = "translated C header failed CoreX syntax verification",
                    });
                    return .none;
                },
                else => return err,
            };
            defer db.allocator.free(translated_cx);

            for (unit.included_files.items) |inc_file| {
                _ = db.recordEmbeddedFileRead(inc_file.path, inc_file.content) catch {};
            }

            virtual_fid = try db.storeCImportTranslationWithIncludes(
                resolved_hdr.bytes,
                db.c_import_defines.items,
                translated_cx,
                unit.included_files.items,
                null,
            );
        }

        // [3] Resolve signatures of the virtual `.cx` module inside `CompilerDb`:
        const sigs_res = try db.resolveSignatures(virtual_fid);
        if (sigs_res.module_scope.isNone()) return .none;

        if (db.c_import_mod_syms.get(virtual_fid.asInt())) |existing_sym_idx| {
            sym_table.symbols.items[existing_sym_idx.asInt()].target_scope = sigs_res.module_scope;
            return existing_sym_idx;
        }

        var mod_name_buf: [128]u8 = undefined;
        const synth_mod_name = std.fmt.bufPrint(
            &mod_name_buf,
            "__c_import_{d}",
            .{virtual_fid.asInt()},
        ) catch "__c_import_mod";
        const mod_name_id = try interner.intern(synth_mod_name);
        const mod_sym_idx = try sym_table.appendSymbol(.{
            .name = mod_name_id,
            .name_text = interner.get(mod_name_id),
            .kind = .module_sym,
            .namespace = .value_ns,
            .visibility = .public,
            .scope_id = sym_table.prelude_scope,
            .decl_span = .{ .file_id = virtual_fid, .start_byte = 0, .end_byte = 0 },
            .target_scope = sigs_res.module_scope,
        });
        try db.c_import_mod_syms.put(db.allocator, virtual_fid.asInt(), mod_sym_idx);
        return mod_sym_idx;
    }

    /// Resolves C header bytes and canonical lookup path from `virtual_files`, caller dir, `workspace_root`, `-I`, or bundled.
    fn resolveCImportHeaderSource(
        self: *CompilerDb,
        caller_file_id: FileId,
        header_path: []const u8,
        out_owned_bytes: *?[]u8,
        out_owned_path: *?[]u8,
    ) !?struct { bytes: []const u8, resolved_path: []const u8 } {
        if (self.virtual_files) |vfs_map| {
            if (vfs_map.getEntry(header_path)) |direct_kv| {
                return .{ .bytes = direct_kv.value_ptr.*, .resolved_path = direct_kv.key_ptr.* };
            }
            if (self.file_paths.get(caller_file_id.asInt())) |caller_path| {
                if (std.fs.path.dirname(caller_path)) |caller_dir| {
                    const joined_rel = try std.fmt.allocPrint(self.allocator, "{s}/{s}", .{ caller_dir, header_path });
                    defer self.allocator.free(joined_rel);
                    if (vfs_map.getEntry(joined_rel)) |rel_kv| {
                        return .{ .bytes = rel_kv.value_ptr.*, .resolved_path = rel_kv.key_ptr.* };
                    }
                }
            }
        }

        if (self.embed_io) |io_handle| {
            var candidate_paths: std.ArrayListUnmanaged([]u8) = .empty;
            defer {
                for (candidate_paths.items) |cand_p| self.allocator.free(cand_p);
                candidate_paths.deinit(self.allocator);
            }
            if (self.file_paths.get(caller_file_id.asInt())) |caller_path| {
                if (std.fs.path.dirname(caller_path)) |caller_dir| {
                    try candidate_paths.append(
                        self.allocator,
                        try std.fs.path.join(self.allocator, &.{ caller_dir, header_path }),
                    );
                }
            }
            if (self.workspace_root) |ws_root| {
                try candidate_paths.append(
                    self.allocator,
                    try std.fs.path.join(self.allocator, &.{ ws_root, header_path }),
                );
            }
            for (self.c_import_include_dirs.items) |inc_dir| {
                try candidate_paths.append(
                    self.allocator,
                    try std.fs.path.join(self.allocator, &.{ inc_dir, header_path }),
                );
            }
            if (std.fs.path.isAbsolute(header_path)) {
                try candidate_paths.append(self.allocator, try self.allocator.dupe(u8, header_path));
            }
            for (candidate_paths.items) |cand_path| {
                if (std.Io.Dir.cwd().readFileAlloc(
                    io_handle,
                    cand_path,
                    self.allocator,
                    .limited(4 * 1024 * 1024),
                )) |disk_bytes| {
                    const duped_path = try self.allocator.dupe(u8, cand_path);
                    out_owned_bytes.* = disk_bytes;
                    out_owned_path.* = duped_path;
                    return .{ .bytes = disk_bytes, .resolved_path = duped_path };
                } else |_| {}
            }
        }

        if (c_frontend.BUNDLED_SYSTEM_HEADERS.get(header_path)) |bundled_src| {
            return .{ .bytes = bundled_src, .resolved_path = header_path };
        }
        return null;
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
            const is_mid_query = self.active_stack.items.len > 0;
            if (!is_content_same) {
                const cloned_text = try self.allocator.dupe(u8, source_text);
                self.allocator.free(existing_input.owned_text);
                existing_input.owned_text = cloned_text;
                existing_input.content_fingerprint = new_fp;
                self.pure_call_memo_cache.clear();
                if (is_mid_query) {
                    self.purgeVirtualFileArtifacts(file_id, false);
                }
            }

            if (!is_mid_query) {
                self.current_revision = self.current_revision.next();
                const max_affected_tier: usize = @max(@backingInt(old_durability), @backingInt(durability));
                var tier_idx: usize = 0;
                while (tier_idx <= max_affected_tier) : (tier_idx += 1) {
                    self.last_changed_by_durability[tier_idx] = self.current_revision;
                }
            }

            existing_input.durability = durability;
            if (!is_content_same) {
                existing_input.changed_at = self.current_revision;
            }
            if ((old_durability == .high) != (durability == .high)) {
                self.stdlib_privilege_epoch +%= 1;
                const core_slot = CONFIG_KEY_INTERNAL_CORE - CONFIG_KEY_TARGET_LAYOUT;
                self.config_changed_at[core_slot] = self.current_revision;
                if (self.memos.getPtr(QueryKey.forConfig(CONFIG_KEY_INTERNAL_CORE).asU64())) |cfg_memo| {
                    cfg_memo.output_fingerprint = self.computeConfigFingerprint(CONFIG_KEY_INTERNAL_CORE);
                    cfg_memo.changed_at = self.current_revision;
                    cfg_memo.verified_at = self.current_revision;
                }
                self.pure_call_memo_cache.clear();
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

        if (self.active_stack.items.len == 0) {
            if (self.source_inputs.count() > 0) {
                self.current_revision = self.current_revision.next();
            }
            var tier_idx: usize = 0;
            while (tier_idx <= @backingInt(durability)) : (tier_idx += 1) {
                self.last_changed_by_durability[tier_idx] = self.current_revision;
            }
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
        try self.ensureFreshSignatureAstAndSideTables(file_id);
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

    /// Stage 10: Lowers a single `def_id` into an owned `HirStore` (per-`DefId` firewall).
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

    /// Returns drop-elaborated `MirBody` records for `def_id` for `MirVm` `comptime` execution.
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

    /// Appends `file_id` and its transitive `external_mod_files` children into `out_files` in dependency-first order.
    fn appendModuleSubtreePostOrder(
        self: *CompilerDb,
        file_id: FileId,
        seen_files: *std.AutoHashMapUnmanaged(u32, void),
        out_files: *std.ArrayListUnmanaged(FileId),
        depth: u32,
    ) QueryError!void {
        if (file_id.isNone() or depth >= 64) return;
        const seen_gop = try seen_files.getOrPut(self.allocator, file_id.asInt());
        if (seen_gop.found_existing) return;

        var entry_idx: usize = 0;
        while (entry_idx < (try self.extractItemTree(file_id)).entries.len) : (entry_idx += 1) {
            const entry = (try self.extractItemTree(file_id)).entries[entry_idx];
            if (entry.kind == .mod_decl) {
                const ext_key: u64 = (@as(u64, file_id.asInt()) << 32) | @as(u64, entry.name_symbol.asInt());
                if (self.external_mod_files.get(ext_key)) |child_fid| {
                    try self.appendModuleSubtreePostOrder(child_fid, seen_files, out_files, depth + 1);
                }
            }
        }
        try out_files.append(self.allocator, file_id);
    }

    /// Collects all reachable `FileId`s for `root_file_id` (including `root_module_files` and `extra_file_ids`).
    pub fn collectReachableModuleFiles(
        self: *CompilerDb,
        root_file_id: FileId,
        extra_file_ids: []const FileId,
        out_files: *std.ArrayListUnmanaged(FileId),
    ) QueryError!void {
        var seen_files: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer seen_files.deinit(self.allocator);

        var root_syms: std.ArrayListUnmanaged(u32) = .empty;
        defer root_syms.deinit(self.allocator);
        var root_iter = self.root_module_files.keyIterator();
        while (root_iter.next()) |sym_key| {
            try root_syms.append(self.allocator, sym_key.*);
        }
        std.mem.sort(u32, root_syms.items, {}, std.sort.asc(u32));
        for (root_syms.items) |sym_raw| {
            if (self.root_module_files.get(sym_raw)) |pkg_root_fid| {
                if (pkg_root_fid != root_file_id) {
                    try self.appendModuleSubtreePostOrder(pkg_root_fid, &seen_files, out_files, 0);
                }
            }
        }

        for (extra_file_ids) |extra_fid| {
            if (extra_fid != root_file_id) {
                try self.appendModuleSubtreePostOrder(extra_fid, &seen_files, out_files, 0);
            }
        }
        try self.appendModuleSubtreePostOrder(root_file_id, &seen_files, out_files, 0);
    }

    /// Clones and optimizes (`--dev` or `--release`) all `MirBody` items across `reachable_files` into `out_bodies`.
    pub fn collectOptimizedModuleBodies(
        self: *CompilerDb,
        out_allocator: std.mem.Allocator,
        root_file_id: FileId,
        reachable_files: []const FileId,
        is_release_mode: bool,
        diagnostic_sink: ?*DiagnosticSink,
        out_bodies: *std.ArrayListUnmanaged(mir.MirBody),
    ) ModuleCompileError!void {
        const active_layout = try self.readTargetLayout();
        const is_strict = try self.readSastStrict();

        if (reachable_files.len == 1 and reachable_files[0] == root_file_id) {
            const opt_res = try self.optimizeMirModule(root_file_id, is_release_mode);
            if (self.getOptimizedMirDiagnostics(root_file_id, is_release_mode)) |opt_sink| {
                if (opt_sink.hasErrors()) return error.FrontendErrors;
            }
            try out_bodies.ensureTotalCapacity(out_allocator, opt_res.bodies.items.len);
            for (opt_res.bodies.items) |*src_body| {
                var cloned_body = src_body.clone(out_allocator) catch return error.OutOfMemory;
                errdefer cloned_body.deinit();
                out_bodies.appendAssumeCapacity(cloned_body);
            }
            return;
        }

        var raw_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
        defer {
            for (raw_bodies.items) |*raw_item| raw_item.deinit();
            raw_bodies.deinit(out_allocator);
        }
        var comptime_fn_defs: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer comptime_fn_defs.deinit(out_allocator);

        for (reachable_files) |mod_fid| {
            _ = try self.resolveSignatures(mod_fid);
            var entry_idx: usize = 0;
            while (entry_idx < (try self.extractItemTree(mod_fid)).entries.len) : (entry_idx += 1) {
                const entry = (try self.extractItemTree(mod_fid)).entries[entry_idx];
                if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) continue;
                const def_mir = try self.buildDefMirArtifact(entry.def_id);
                if (self.lowered_def_hirs.getPtr(entry.def_id.asInt())) |hir_ptr| {
                    for (hir_ptr.functions.items) |fn_meta| {
                        if (fn_meta.is_comptime and !fn_meta.def_id.isNone()) {
                            try comptime_fn_defs.put(out_allocator, fn_meta.def_id.asInt(), {});
                        }
                    }
                }
                if (def_mir.is_comptime_initializer_only) continue;
                for (def_mir.bundle.bodies.items) |*src_body| {
                    var cloned_body = src_body.clone(out_allocator) catch return error.OutOfMemory;
                    errdefer cloned_body.deinit();
                    try raw_bodies.append(out_allocator, cloned_body);
                }
            }
        }

        var local_opt_sink = DiagnosticSink.init(out_allocator);
        defer local_opt_sink.deinit();
        const active_opt_sink = if (diagnostic_sink) |ext_sink| ext_sink else &local_opt_sink;

        const root_syntax_view: ?mir_opt.FileSyntaxView = if (self.source_inputs.getPtr(root_file_id.asInt())) |in_ptr| blk: {
            if (self.parsed_artifacts.getPtr(root_file_id.asInt())) |p_ptr| {
                break :blk .{
                    .source = in_ptr.owned_text,
                    .tokens = &p_ptr.token_buffer,
                    .cst_arena = &p_ptr.cst_arena,
                };
            }
            break :blk null;
        } else null;

        var multi_opt = mir_opt.optimizeMirModule(
            out_allocator,
            raw_bodies.items,
            &self.type_pool,
            &self.symbol_table,
            &self.interner,
            .{
                .is_release_mode = is_release_mode,
                .target_layout = active_layout,
                .syntax_view = root_syntax_view,
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
            active_opt_sink,
        ) catch |opt_err| switch (opt_err) {
            error.Cancelled => return error.Cancelled,
            else => return error.OutOfMemory,
        };
        defer multi_opt.deinit();
        if (active_opt_sink.hasErrors()) return error.FrontendErrors;

        try out_bodies.ensureTotalCapacity(out_allocator, multi_opt.bodies.items.len);
        for (multi_opt.bodies.items) |*opt_body| {
            var cloned_body = opt_body.clone(out_allocator) catch return error.OutOfMemory;
            errdefer cloned_body.deinit();
            out_bodies.appendAssumeCapacity(cloned_body);
        }
    }

    /// Stage 14 orchestrator: verifies all reachable module files, runs `MIR` opt + `@embed_bytes`, and emits codegen.
    pub fn compileModuleArtifact(
        self: *CompilerDb,
        root_file_id: FileId,
        backend: codegen_abi.CodegenBackend,
        options: ModuleCompileOptions,
    ) ModuleCompileError!codegen_abi.CodegenArtifact {
        self.setTargetSpec(backend.targetSpec());

        var reachable_files: std.ArrayListUnmanaged(FileId) = .empty;
        defer reachable_files.deinit(self.allocator);
        try self.collectReachableModuleFiles(root_file_id, options.extra_file_ids, &reachable_files);

        var has_front_errors = false;
        for (reachable_files.items) |mod_fid| {
            if ((try self.parseCst(mod_fid)).diagnostics.hasErrors()) has_front_errors = true;
            if ((try self.resolveSignatures(mod_fid)).error_count > 0) has_front_errors = true;

            var entry_idx: usize = 0;
            while (entry_idx < (try self.extractItemTree(mod_fid)).entries.len) : (entry_idx += 1) {
                const entry = (try self.extractItemTree(mod_fid)).entries[entry_idx];
                if ((try self.typecheckBody(entry.def_id)).error_count > 0) has_front_errors = true;
                if (!(try self.verifySastMir(entry.def_id)).is_verified_sound) has_front_errors = true;

                if (!has_front_errors and (entry.kind == .const_decl or entry.kind == .extern_block)) {
                    const ct_art = self.evalComptimeDef(entry.def_id) catch |ct_err| switch (ct_err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        error.Cancelled => return error.Cancelled,
                        else => {
                            has_front_errors = true;
                            continue;
                        },
                    };
                    if (ct_art.has_errors) has_front_errors = true;
                }
            }
        }
        if (has_front_errors) return error.FrontendErrors;

        var working_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
        defer {
            for (working_bodies.items) |*body_item| body_item.deinit();
            working_bodies.deinit(self.allocator);
        }
        try self.collectOptimizedModuleBodies(
            self.allocator,
            root_file_id,
            reachable_files.items,
            backend.isReleaseMode(),
            options.diagnostic_sink,
            &working_bodies,
        );

        // Materialize reachable `@embed_bytes` constants per body:
        var blob_store = mir.MirBlobStore.init(self.allocator);
        defer blob_store.deinit();
        var local_embed_sink = DiagnosticSink.init(self.allocator);
        defer local_embed_sink.deinit();
        const active_embed_sink = if (options.diagnostic_sink) |ext_sink| ext_sink else &local_embed_sink;
        const active_io = if (options.io) |io_handle| io_handle else self.embed_io;

        var is_embed_ok = true;
        for (working_bodies.items) |*body_ptr| {
            const body_fid = body_ptr.def_id.fileId();
            const body_tokens = if (self.parsed_artifacts.getPtr(body_fid.asInt())) |p_ptr|
                &p_ptr.token_buffer
            else
                null;
            const ok = mir.materializeBodyEmbedBytes(
                body_ptr,
                &self.interner,
                body_tokens,
                &blob_store,
                .{
                    .workspace_root = self.workspace_root,
                    .io = active_io,
                    .virtual_files = self.virtual_files,
                },
                active_embed_sink,
            ) catch return error.OutOfMemory;
            if (!ok) is_embed_ok = false;
        }
        if (!is_embed_ok or active_embed_sink.hasErrors()) return error.FrontendErrors;

        // Compute Pentagon `ProvenValueRange` slices:
        const body_count = working_bodies.items.len;
        const proven_views = try self.allocator.alloc([]const codegen_abi.ProvenValueRange, body_count);
        defer self.allocator.free(proven_views);
        const owned_proven = try self.allocator.alloc([]codegen_abi.ProvenValueRange, body_count);
        @memset(owned_proven, &.{});
        defer {
            for (owned_proven) |slice_item| {
                if (slice_item.len > 0) self.allocator.free(slice_item);
            }
            self.allocator.free(owned_proven);
        }
        for (working_bodies.items, 0..) |*body_ptr, b_idx| {
            const computed_ranges = mir_sast.computeBodyProvenRanges(
                self.allocator,
                body_ptr,
                &self.type_pool,
                &self.symbol_table,
            ) catch return error.OutOfMemory;
            owned_proven[b_idx] = computed_ranges;
            proven_views[b_idx] = computed_ranges;
        }

        var file_tokens: std.AutoHashMapUnmanaged(u32, *const TokenBuffer) = .empty;
        defer file_tokens.deinit(self.allocator);
        try self.populateFileTokensMap(&file_tokens);

        return backend.emitModule(self.allocator, .{
            .bodies = working_bodies.items,
            .pool = &self.type_pool,
            .sym_table = &self.symbol_table,
            .interner = &self.interner,
            .module_name = options.module_name,
            .vfs_source_map = options.vfs_source_map,
            .file_tokens = &file_tokens,
            .rodata_pool = &self.rodata_pool,
            .blob_store = &blob_store,
            .proven_ranges = proven_views,
            .is_dev_got_enabled = options.is_dev_got_enabled,
            .is_oracle_trace_enabled = options.is_oracle_trace_enabled,
            .artifact_kind = options.artifact_kind,
            .link_mode = options.link_mode,
            .extra_libs = options.extra_libs,
            .lib_dirs = options.lib_dirs,
            .output_path = options.output_path,
            .io = active_io,
            .environ_map = options.environ_map,
            .diagnostic_sink = options.diagnostic_sink,
        });
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
            if (queryKeyTargetFileId(key)) |target_fid| {
                if (target_fid.asInt() >= VIRTUAL_C_IMPORT_FILE_ID_BASE and
                    target_fid.asInt() < CONFIG_KEY_TARGET_LAYOUT and
                    !self.source_inputs.contains(target_fid.asInt()))
                {
                    return true;
                }
            }
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

        // [2.5] Conservative Red Path if direct dependency count exceeded `MAX_DEPS_PER_MEMO`:
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
                key.entity_index <= CONFIG_KEY_INCLUDE_TESTS)
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
                    key.entity_index <= CONFIG_KEY_INCLUDE_TESTS)
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

    /// Ensures `self.item_trees` holds an `ItemTree` matching `lowered.ast_fingerprint` and `is_including_tests` for `file_id`.
    fn ensureFreshItemTree(
        self: *CompilerDb,
        file_id: FileId,
        lowered: LoweredAstArtifact,
    ) QueryError!*const ItemTree {
        const is_including_tests = try self.readIncludeTests();
        if (self.item_trees.getPtr(file_id.asInt())) |existing_tree| {
            if (Fingerprint128.eql(existing_tree.source_ast_fingerprint, lowered.ast_fingerprint) and
                existing_tree.is_including_tests == is_including_tests)
            {
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
            is_including_tests,
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
        var is_same_sig_tree = false;
        if (self.item_trees.fetchRemove(file_id.asInt())) |old_kv| {
            var old_tree = old_kv.value;
            is_same_sig_tree = Fingerprint128.eql(old_tree.tree_fingerprint, new_tree.tree_fingerprint);
            old_tree.deinit(self.allocator);
        }
        try self.item_trees.put(self.allocator, file_id.asInt(), new_tree);
        if (is_same_sig_tree) {
            try self.ensureFreshSignatureAstAndSideTables(file_id);
        }
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

    /// Returns `true` if `candidate_fid` equals `subtree_root_fid` or is a transitive `external_mod_files` child.
    fn isModuleSubtreeMember(
        self: *const CompilerDb,
        subtree_root_fid: FileId,
        candidate_fid: FileId,
    ) !bool {
        if (subtree_root_fid == candidate_fid) return true;
        if (self.external_mod_files.count() == 0) return false;

        var visited_fids: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer visited_fids.deinit(self.allocator);
        var work_stack: std.ArrayListUnmanaged(u32) = .empty;
        defer work_stack.deinit(self.allocator);

        try visited_fids.put(self.allocator, subtree_root_fid.asInt(), {});
        try work_stack.append(self.allocator, subtree_root_fid.asInt());

        while (work_stack.pop()) |parent_raw| {
            var ext_iter = self.external_mod_files.iterator();
            while (ext_iter.next()) |kv| {
                const key_parent: u32 = @truncate(kv.key_ptr.* >> 32);
                if (key_parent != parent_raw) continue;
                const child_raw = kv.value_ptr.asInt();
                if (child_raw == candidate_fid.asInt()) return true;
                const gop = try visited_fids.getOrPut(self.allocator, child_raw);
                if (!gop.found_existing) {
                    try work_stack.append(self.allocator, child_raw);
                }
            }
        }
        return false;
    }

    /// Resolves the body or initializer CST node for a nested AST item inside an inline `mod` or `impl`.
    fn resolveNestedAstItemBodyCst(
        parsed: *const ParsedCstArtifact,
        item_kind: ItemKind,
        ast_node: syntax_arenas.AstNode,
        item_cst_node: CstNodeIndex,
    ) CstNodeIndex {
        if (item_kind == .fn_decl or item_kind == .subscript_decl or
            item_kind == .test_decl or item_kind == .bench_decl)
        {
            if (ast_node.rhs.tag == .node) {
                const body_ast = NodeIndex.fromInt(ast_node.rhs.payload);
                if (body_ast.asInt() < parsed.ast_arena.countNodes()) {
                    const cst_id = parsed.ast_arena.getCstOrigin(body_ast);
                    if (!cst_id.isNone()) return cst_id;
                }
            }
            return findDirectBodyBlockCst(&parsed.cst_arena, item_cst_node);
        }
        if (item_kind == .const_decl or item_kind == .type_alias_decl) {
            const init_cst = findConstInitCst(&parsed.token_buffer, &parsed.cst_arena, item_cst_node);
            if (!init_cst.isNone()) return init_cst;
            if (ast_node.rhs.tag == .node) {
                const body_ast = NodeIndex.fromInt(ast_node.rhs.payload);
                if (body_ast.asInt() < parsed.ast_arena.countNodes()) {
                    return parsed.ast_arena.getCstOrigin(body_ast);
                }
            }
        }
        return .none;
    }

    /// Hashes header CST nodes in `[start_after_root .. header_end_idx)` without hashing the outer container's `subtree_size`.
    fn hashContainerHeaderRangeForCxi(
        hasher: *StructuralHasher,
        source: []const u8,
        token_buffer: *const TokenBuffer,
        cst_arena: *const LosslessCstArena,
        start_after_root: usize,
        header_end_idx: usize,
    ) void {
        var cursor = start_after_root;
        while (cursor < header_end_idx) : (cursor += 1) {
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

    /// Returns `true` if `sym_idx` is externally `.public` outside the current package (walking enclosing scopes).
    fn isSymbolExternallyPublic(sym_table: *const SymbolTable, sym_idx: SymbolIndex) bool {
        if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.countSymbols()) return false;
        var sym = sym_table.getSymbol(sym_idx).*;
        var alias_hops: u8 = 0;
        while (sym.kind == .use_alias_sym and !sym.target_symbol.isNone() and
            sym.target_symbol.asInt() < sym_table.countSymbols() and alias_hops < 16) : (alias_hops += 1)
        {
            if (sym.visibility != .public) return false;
            sym = sym_table.getSymbol(sym.target_symbol).*;
        }
        if (sym.flags.is_builtin) return true;
        if (sym.visibility != .public) return false;

        var cur_scope = sym.scope_id;
        var depth: u8 = 0;
        while (!cur_scope.isNone() and depth < 32) : (depth += 1) {
            const scope_rec = sym_table.scope_arena.getScope(cur_scope);
            if (scope_rec.parent.isNone()) break;
            for (sym_table.getScopeMembers(scope_rec.parent)) |parent_mem_idx| {
                const parent_mem = sym_table.getSymbol(parent_mem_idx).*;
                if (parent_mem.target_scope == cur_scope and parent_mem.kind != .use_alias_sym) {
                    if (parent_mem.visibility != .public) return false;
                    break;
                }
            }
            cur_scope = scope_rec.parent;
        }
        return true;
    }

    /// Returns `true` if the `TypePath` (`path_tokens`) referenced in an `impl` header resolves to an externally `.public` type/trait.
    fn isImplTypePathExternallyPublic(
        self: *const CompilerDb,
        enclosing_scope: ScopeId,
        source: []const u8,
        token_buffer: *const TokenBuffer,
        path_tokens: []const TokenIndex,
    ) bool {
        if (path_tokens.len == 0) return false;
        if (path_tokens.len == 1) {
            const single_tok = path_tokens[0];
            if (single_tok.isNone() or single_tok.asInt() >= token_buffer.countTokens()) return false;
            const tok_kind = token_buffer.getToken(single_tok).kind;
            if (tok_kind == .prim_type) return true;
            const name_slice = getTokenLexeme(source, token_buffer, single_tok);
            const sym_id = self.interner.lookup(name_slice) orelse return false;
            return switch (self.symbol_table.lookupLexical(
                enclosing_scope,
                sym_id,
                symbol_resolver.NamespaceMask.TYPE_ONLY,
            )) {
                .found => |sym_idx| isSymbolExternallyPublic(&self.symbol_table, sym_idx),
                else => false,
            };
        }

        var active_scope = enclosing_scope;
        for (path_tokens[0 .. path_tokens.len - 1], 0..) |mod_tok, seg_idx| {
            const seg_name = getTokenLexeme(source, token_buffer, mod_tok);
            const seg_sym_id = self.interner.lookup(seg_name) orelse return false;
            const found_mod_idx: SymbolIndex = if (seg_idx == 0) switch (self.symbol_table.lookupLexical(
                active_scope,
                seg_sym_id,
                symbol_resolver.NamespaceMask.TYPE_OR_VALUE,
            )) {
                .found => |idx| idx,
                else => {
                    if (self.symbol_table.named_module_scopes.get(seg_sym_id.asInt())) |named_scope| {
                        active_scope = named_scope;
                        continue;
                    }
                    return false;
                },
            } else self.symbol_table.lookupInScopeDirect(
                active_scope,
                seg_sym_id,
                symbol_resolver.NamespaceMask.TYPE_OR_VALUE,
            );
            if (found_mod_idx.isNone() or !isSymbolExternallyPublic(&self.symbol_table, found_mod_idx)) {
                return false;
            }
            active_scope = self.symbol_table.getSymbol(found_mod_idx).target_scope;
            if (active_scope.isNone()) return false;
        }

        const leaf_name = getTokenLexeme(source, token_buffer, path_tokens[path_tokens.len - 1]);
        const leaf_sym_id = self.interner.lookup(leaf_name) orelse return false;
        const leaf_idx = self.symbol_table.lookupInScopeDirect(
            active_scope,
            leaf_sym_id,
            symbol_resolver.NamespaceMask.TYPE_ONLY,
        );
        return !leaf_idx.isNone() and isSymbolExternallyPublic(&self.symbol_table, leaf_idx);
    }

    /// Appends externally `.public` `impl` headers and member signatures/consts into `public_hasher`.
    fn hashImplDeclForPublicCxi(
        self: *CompilerDb,
        public_hasher: *StructuralHasher,
        checker: *TypeChecker,
        enclosing_scope: ScopeId,
        source: []const u8,
        parsed: *const ParsedCstArtifact,
        impl_ast_id: NodeIndex,
    ) void {
        const impl_cst = parsed.ast_arena.getCstOrigin(impl_ast_id);
        if (impl_cst.isNone() or impl_cst.asInt() >= parsed.cst_arena.countNodes()) return;
        if (!checker.isCstNodeCfgEnabled(impl_cst)) return;

        const start_idx: usize = impl_cst.asInt();
        const root_rec = parsed.cst_arena.getNode(impl_cst);
        const end_idx: usize = @min(
            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
            parsed.cst_arena.countNodes(),
        );
        const impl_main_tok = parsed.ast_arena.getNode(impl_ast_id).main_token;

        var generic_names: [16][]const u8 = undefined;
        var generic_name_len: usize = 0;
        var first_path_toks: [8]TokenIndex = undefined;
        var first_path_len: usize = 0;
        var target_path_toks: [8]TokenIndex = undefined;
        var target_path_len: usize = 0;
        var has_seen_for = false;
        var header_end_pos: usize = end_idx;

        var cursor: usize = start_idx + 1;
        while (cursor < end_idx) {
            const sub_id = CstNodeIndex.fromInt(@intCast(cursor));
            const sub = parsed.cst_arena.getNode(sub_id);
            const step_size: usize = @max(@as(usize, sub.subtree_size), 1);
            if (sub.kind == .type_params) {
                const tp_end = @min(cursor + step_size, end_idx);
                var tp_cur = cursor + 1;
                while (tp_cur < tp_end) : (tp_cur += 1) {
                    const tp_node = parsed.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(tp_cur)));
                    if (tp_node.kind == .type_param) {
                        const param_end = @min(tp_cur + @max(@as(usize, tp_node.subtree_size), 1), tp_end);
                        var p_cur = tp_cur + 1;
                        while (p_cur < param_end) : (p_cur += 1) {
                            const leaf = parsed.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(p_cur)));
                            if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
                                !leaf.token.isNone() and leaf.token.asInt() < parsed.token_buffer.countTokens())
                            {
                                const tk = parsed.token_buffer.getToken(leaf.token).kind;
                                if (tk == .colon or tk == .eq) break;
                                if (isIdentifierTokenKind(tk) and generic_name_len < generic_names.len) {
                                    generic_names[generic_name_len] = getTokenLexeme(source, &parsed.token_buffer, leaf.token);
                                    generic_name_len += 1;
                                    break;
                                }
                            }
                        }
                        tp_cur = param_end - 1;
                    }
                }
                cursor = tp_end;
                continue;
            }
            if (sub.kind == .type_args or sub.kind == .visibility_modifier or sub.kind == .attribute) {
                cursor += step_size;
                continue;
            }
            if (sub.kind == .where_clause) {
                cursor += step_size;
                continue;
            }
            const is_leaf = sub.subtree_size <= 1 and !sub.flags.is_bracketed;
            if (is_leaf and !sub.flags.is_missing_or_injected and
                !sub.token.isNone() and sub.token.asInt() < parsed.token_buffer.countTokens())
            {
                if (impl_main_tok.isNone() or sub.token.asInt() > impl_main_tok.asInt()) {
                    const tok_kind = parsed.token_buffer.getToken(sub.token).kind;
                    if (tok_kind == .lbrace or tok_kind == .semi) {
                        header_end_pos = cursor;
                        break;
                    }
                    if (tok_kind == .kw_for) {
                        has_seen_for = true;
                        cursor += 1;
                        continue;
                    }
                    if (isIdentifierTokenKind(tok_kind) or tok_kind == .prim_type) {
                        if (!has_seen_for) {
                            if (first_path_len < first_path_toks.len) {
                                first_path_toks[first_path_len] = sub.token;
                                first_path_len += 1;
                            }
                        } else if (target_path_len < target_path_toks.len) {
                            target_path_toks[target_path_len] = sub.token;
                            target_path_len += 1;
                        }
                    }
                }
            }
            cursor += 1;
        }

        const check_target_slice = if (has_seen_for)
            target_path_toks[0..target_path_len]
        else
            first_path_toks[0..first_path_len];
        var is_target_generic_param = false;
        if (check_target_slice.len == 1) {
            const target_lex = getTokenLexeme(source, &parsed.token_buffer, check_target_slice[0]);
            for (generic_names[0..generic_name_len]) |g_name| {
                if (std.mem.eql(u8, g_name, target_lex)) {
                    is_target_generic_param = true;
                    break;
                }
            }
        }
        const is_target_pub = is_target_generic_param or self.isImplTypePathExternallyPublic(
            enclosing_scope,
            source,
            &parsed.token_buffer,
            check_target_slice,
        );
        if (!is_target_pub) return;

        const member_ids = symbol_resolver.extractImplMemberItems(&parsed.ast_arena, impl_ast_id);
        if (has_seen_for) {
            const is_trait_pub = self.isImplTypePathExternallyPublic(
                enclosing_scope,
                source,
                &parsed.token_buffer,
                first_path_toks[0..first_path_len],
            );
            if (!is_trait_pub) return;

            public_hasher.updateU8(0xC1);
            hashContainerHeaderRangeForCxi(
                public_hasher,
                source,
                &parsed.token_buffer,
                &parsed.cst_arena,
                start_idx + 1,
                header_end_pos,
            );
            var active_member_count: u32 = 0;
            for (member_ids) |raw_mem_id| {
                const mem_ast_id = NodeIndex.fromInt(raw_mem_id);
                if (mem_ast_id.asInt() >= parsed.ast_arena.countNodes()) continue;
                const mem_ast = parsed.ast_arena.getNode(mem_ast_id);
                const mem_kind = astTagToItemKind(mem_ast.tag) orelse continue;
                const mem_cst = parsed.ast_arena.getCstOrigin(mem_ast_id);
                if (!checker.isCstNodeCfgEnabled(mem_cst)) continue;
                active_member_count += 1;
                const mem_body_cst = resolveNestedAstItemBodyCst(parsed, mem_kind, mem_ast, mem_cst);
                public_hasher.updateU8(@backingInt(mem_kind));
                public_hasher.updateFingerprint(computeItemSignatureFingerprint(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    mem_cst,
                    mem_body_cst,
                ));
                if (mem_kind == .const_decl or mem_kind == .type_alias_decl) {
                    public_hasher.updateFingerprint(computeItemBodyFingerprint(
                        source,
                        &parsed.token_buffer,
                        &parsed.cst_arena,
                        mem_cst,
                        mem_body_cst,
                    ));
                }
            }
            public_hasher.updateU32(active_member_count);
            return;
        }

        // Inherent `impl Target`: hash header + ONLY `.public` members (skipping entirely if 0 `.public` members):
        var pub_member_count: u32 = 0;
        for (member_ids) |raw_mem_id| {
            const mem_ast_id = NodeIndex.fromInt(raw_mem_id);
            if (mem_ast_id.asInt() >= parsed.ast_arena.countNodes()) continue;
            const mem_ast = parsed.ast_arena.getNode(mem_ast_id);
            const mem_kind = astTagToItemKind(mem_ast.tag) orelse continue;
            if (mem_kind == .test_decl or mem_kind == .bench_decl) continue;
            const mem_cst = parsed.ast_arena.getCstOrigin(mem_ast_id);
            if (!checker.isCstNodeCfgEnabled(mem_cst)) continue;
            const mem_vis = extractItemVisibility(
                source,
                &parsed.token_buffer,
                &parsed.cst_arena,
                mem_cst,
                mem_ast.main_token,
            );
            if (mem_vis != .public) continue;
            if (pub_member_count == 0) {
                public_hasher.updateU8(0xC2);
                hashContainerHeaderRangeForCxi(
                    public_hasher,
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    start_idx + 1,
                    header_end_pos,
                );
            }
            pub_member_count += 1;
            const mem_body_cst = resolveNestedAstItemBodyCst(parsed, mem_kind, mem_ast, mem_cst);
            public_hasher.updateU8(@backingInt(mem_kind));
            public_hasher.updateFingerprint(computeItemSignatureFingerprint(
                source,
                &parsed.token_buffer,
                &parsed.cst_arena,
                mem_cst,
                mem_body_cst,
            ));
            if (mem_kind == .const_decl) {
                public_hasher.updateFingerprint(computeItemBodyFingerprint(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    mem_cst,
                    mem_body_cst,
                ));
            }
        }
        if (pub_member_count > 0) {
            public_hasher.updateU32(pub_member_count);
        }
    }

    /// Recursively hashes externally `.public` items inside an inline `pub mod` block.
    fn hashInlinePublicModForCxi(
        self: *CompilerDb,
        public_hasher: *StructuralHasher,
        checker: *TypeChecker,
        parent_scope: ScopeId,
        source: []const u8,
        parsed: *const ParsedCstArtifact,
        mod_ast_id: NodeIndex,
        mod_name_sym: SymbolId,
        mod_name_text: []const u8,
        depth: u32,
    ) void {
        if (depth >= 32) return;
        var child_scope: ScopeId = .none;
        if (!parent_scope.isNone() and !mod_name_sym.isNone()) {
            const mod_sym_idx = self.symbol_table.lookupInScopeDirect(
                parent_scope,
                mod_name_sym,
                symbol_resolver.NamespaceMask.TYPE_OR_VALUE,
            );
            if (!mod_sym_idx.isNone()) {
                child_scope = self.symbol_table.getSymbol(mod_sym_idx).target_scope;
            }
        }

        public_hasher.updateU8(0xD1);
        public_hasher.updateBytes(mod_name_text);
        var pub_child_count: u32 = 0;
        const inner_items = symbol_resolver.extractModInnerItems(&parsed.ast_arena, mod_ast_id);
        for (inner_items) |raw_child_id| {
            const child_ast_id = NodeIndex.fromInt(raw_child_id);
            if (child_ast_id.asInt() >= parsed.ast_arena.countNodes()) continue;
            const child_ast = parsed.ast_arena.getNode(child_ast_id);
            const child_kind = astTagToItemKind(child_ast.tag) orelse continue;
            if (child_kind == .test_decl or child_kind == .bench_decl or child_kind == .extern_block) continue;
            const child_cst = parsed.ast_arena.getCstOrigin(child_ast_id);
            if (child_kind == .ffi_extern_block) {
                if (!checker.isCstNodeCfgEnabled(child_cst)) continue;
                const blk_hdr = parsed.ast_arena.getExternBlockHeader(child_ast_id);
                const blk_ctx = computeExternBlockContext(source, parsed, child_ast_id, blk_hdr);
                for (parsed.ast_arena.getExternBlockItems(child_ast_id)) |ext_mem_raw| {
                    const ext_mem_ast_id = NodeIndex.fromInt(ext_mem_raw);
                    if (ext_mem_ast_id.asInt() >= parsed.ast_arena.countNodes()) continue;
                    const ext_mem_ast = parsed.ast_arena.getNode(ext_mem_ast_id);
                    const ext_mem_kind = astTagToItemKind(ext_mem_ast.tag) orelse continue;
                    const ext_mem_cst = parsed.ast_arena.getCstOrigin(ext_mem_ast_id);
                    if (!checker.isCstNodeCfgEnabled(ext_mem_cst)) continue;
                    var ext_vis = if (ext_mem_kind == .extern_static) blk_sv: {
                        const sext = parsed.ast_arena.getExternStaticExtra(ext_mem_ast_id);
                        const avis = externVisToVisibility(sext.flags.visibility);
                        if (avis != .private) break :blk_sv avis;
                        break :blk_sv extractItemVisibility(
                            source,
                            &parsed.token_buffer,
                            &parsed.cst_arena,
                            ext_mem_cst,
                            ext_mem_ast.main_token,
                        );
                    } else extractItemVisibility(
                        source,
                        &parsed.token_buffer,
                        &parsed.cst_arena,
                        ext_mem_cst,
                        ext_mem_ast.main_token,
                    );
                    if (ext_vis == .private and blk_ctx.visibility != .private) {
                        ext_vis = blk_ctx.visibility;
                    }
                    if (ext_vis != .public) continue;
                    pub_child_count += 1;
                    const ext_name = extractItemNameSlice(
                        source,
                        &parsed.token_buffer,
                        &parsed.cst_arena,
                        ext_mem_kind,
                        ext_mem_ast.main_token,
                        ext_mem_cst,
                    );
                    public_hasher.updateU8(@backingInt(ext_mem_kind));
                    public_hasher.updateBytes(ext_name);
                    if (ext_mem_kind == .extern_static) {
                        public_hasher.updateFingerprint(computeExternStaticSigFingerprint(
                            source,
                            parsed,
                            ext_mem_ast_id,
                            ext_mem_cst,
                            ext_name,
                            ext_vis,
                            blk_ctx,
                        ));
                    } else {
                        const ext_body_cst = resolveNestedAstItemBodyCst(
                            parsed,
                            ext_mem_kind,
                            ext_mem_ast,
                            ext_mem_cst,
                        );
                        public_hasher.updateFingerprint(blk_ctx.header_fingerprint);
                        public_hasher.updateFingerprint(computeItemSignatureFingerprint(
                            source,
                            &parsed.token_buffer,
                            &parsed.cst_arena,
                            ext_mem_cst,
                            ext_body_cst,
                        ));
                        if (ext_mem_kind == .const_decl) {
                            public_hasher.updateFingerprint(computeItemBodyFingerprint(
                                source,
                                &parsed.token_buffer,
                                &parsed.cst_arena,
                                ext_mem_cst,
                                ext_body_cst,
                            ));
                        }
                    }
                }
                continue;
            }
            if (child_kind == .impl_decl) {
                self.hashImplDeclForPublicCxi(public_hasher, checker, child_scope, source, parsed, child_ast_id);
                continue;
            }
            if (!checker.isCstNodeCfgEnabled(child_cst)) continue;
            const child_vis = extractItemVisibility(
                source,
                &parsed.token_buffer,
                &parsed.cst_arena,
                child_cst,
                child_ast.main_token,
            );
            if (child_vis != .public) continue;

            pub_child_count += 1;
            const child_name = extractItemNameSlice(
                source,
                &parsed.token_buffer,
                &parsed.cst_arena,
                child_kind,
                child_ast.main_token,
                child_cst,
            );
            if (child_kind == .mod_decl and child_ast.rhs.tag == .extra) {
                const nested_sym = self.interner.lookup(child_name) orelse .none;
                self.hashInlinePublicModForCxi(
                    public_hasher,
                    checker,
                    child_scope,
                    source,
                    parsed,
                    child_ast_id,
                    nested_sym,
                    child_name,
                    depth + 1,
                );
                continue;
            }
            const child_body_cst = resolveNestedAstItemBodyCst(parsed, child_kind, child_ast, child_cst);
            public_hasher.updateU8(@backingInt(child_kind));
            public_hasher.updateBytes(child_name);
            public_hasher.updateFingerprint(computeItemSignatureFingerprint(
                source,
                &parsed.token_buffer,
                &parsed.cst_arena,
                child_cst,
                child_body_cst,
            ));
            if (child_kind == .const_decl) {
                public_hasher.updateFingerprint(computeItemBodyFingerprint(
                    source,
                    &parsed.token_buffer,
                    &parsed.cst_arena,
                    child_cst,
                    child_body_cst,
                ));
            }
        }
        public_hasher.updateU32(pub_child_count);
    }

    /// Stage 6 implementation: resolves module signatures for `file_id` (shielded by `tree_fingerprint`).
    fn computeResolveSignatures(self: *CompilerDb, file_id: FileId) QueryError!Fingerprint128 {
        const init_tree = try self.extractItemTree(file_id);
        const item_tree_fp = init_tree.tree_fingerprint;
        const is_including_tests = init_tree.is_including_tests;
        const active_layout = try self.readTargetLayout();
        const is_internal_core = self.readInternalCore();
        const is_stdlib_durability = if (self.source_inputs.get(file_id.asInt())) |inp|
            inp.durability == .high
        else
            false;
        const is_core_allowed = is_internal_core or is_stdlib_durability;
        try self.unwindIfCancelled();

        var hasher = StructuralHasher.init();
        hasher.updateU32(file_id.asInt());
        hasher.updateU8(active_layout.ptr_byte_size);
        hasher.updateU8(@backingInt(self.target_spec.arch));
        hasher.updateU8(@backingInt(self.target_spec.os));
        hasher.updateU8(@backingInt(self.target_spec.abi));
        hasher.updateU8(@backingInt(self.target_spec.simd_level));
        hasher.updateU8(@intFromBool(is_including_tests));
        hasher.updateU8(@intFromBool(is_core_allowed));
        hasher.updateFingerprint(item_tree_fp);

        var public_cxi_hasher = StructuralHasher.init();
        public_cxi_hasher.updateU32(file_id.asInt());
        public_cxi_hasher.updateU8(active_layout.ptr_byte_size);
        public_cxi_hasher.updateU8(@backingInt(self.target_spec.arch));
        public_cxi_hasher.updateU8(@backingInt(self.target_spec.os));
        public_cxi_hasher.updateU8(@backingInt(self.target_spec.abi));
        public_cxi_hasher.updateU8(@backingInt(self.target_spec.simd_level));

        var sig_entry_idx: usize = 0;
        while (sig_entry_idx < (try self.extractItemTree(file_id)).entries.len) : (sig_entry_idx += 1) {
            const entry = (try self.extractItemTree(file_id)).entries[sig_entry_idx];
            const sig_fp = try self.getItemTreeSigProj(entry.def_id);
            hasher.updateFingerprint(sig_fp);
        }

        // Resolve registered root packages (`core/root.cx` / `cx`) deduplicating shared `FileId`s:
        var root_mod_syms: std.ArrayListUnmanaged(u32) = .empty;
        defer root_mod_syms.deinit(self.allocator);
        var root_key_iter = self.root_module_files.keyIterator();
        while (root_key_iter.next()) |sym_key| {
            try root_mod_syms.append(self.allocator, sym_key.*);
        }
        std.mem.sort(u32, root_mod_syms.items, {}, std.sort.asc(u32));
        var resolved_root_fids: std.AutoHashMapUnmanaged(u32, ScopeId) = .empty;
        defer resolved_root_fids.deinit(self.allocator);
        for (root_mod_syms.items) |root_sym_raw| {
            const root_fid = self.root_module_files.get(root_sym_raw) orelse continue;
            if (resolved_root_fids.get(root_fid.asInt())) |cached_scope| {
                if (!cached_scope.isNone()) {
                    try self.symbol_table.named_module_scopes.put(
                        self.allocator,
                        root_sym_raw,
                        cached_scope,
                    );
                }
                continue;
            }
            if (root_fid != file_id and
                !(try self.isModuleSubtreeMember(root_fid, file_id)) and
                !self.in_flight_keys.contains(QueryKey.forFile(.resolve_signatures, root_fid).asU64()))
            {
                const root_sigs = try self.resolveSignatures(root_fid);
                hasher.updateFingerprint(root_sigs.signatures_fingerprint);
                try resolved_root_fids.put(self.allocator, root_fid.asInt(), root_sigs.module_scope);
                if (!root_sigs.module_scope.isNone()) {
                    try self.symbol_table.named_module_scopes.put(
                        self.allocator,
                        root_sym_raw,
                        root_sigs.module_scope,
                    );
                }
            }
        }
        var stale_ext_keys: std.ArrayListUnmanaged(u64) = .empty;
        defer stale_ext_keys.deinit(self.allocator);
        var ext_iter = self.symbol_table.external_module_scopes.keyIterator();
        while (ext_iter.next()) |ext_key_ptr| {
            if (@as(u32, @truncate(ext_key_ptr.* >> 32)) == file_id.asInt()) {
                try stale_ext_keys.append(self.allocator, ext_key_ptr.*);
            }
        }
        for (stale_ext_keys.items) |stale_ext_key| {
            _ = self.symbol_table.external_module_scopes.remove(stale_ext_key);
        }
        var mod_entry_idx: usize = 0;
        while (mod_entry_idx < (try self.extractItemTree(file_id)).entries.len) : (mod_entry_idx += 1) {
            const entry = (try self.extractItemTree(file_id)).entries[mod_entry_idx];
            if (entry.kind == .mod_decl) {
                const ext_key: u64 = (@as(u64, file_id.asInt()) << 32) | @as(u64, entry.name_symbol.asInt());
                if (self.external_mod_files.get(ext_key)) |child_fid| {
                    if (child_fid != file_id and
                        !self.in_flight_keys.contains(QueryKey.forFile(.resolve_signatures, child_fid).asU64()))
                    {
                        const child_sigs = try self.resolveSignatures(child_fid);
                        hasher.updateFingerprint(child_sigs.signatures_fingerprint);
                        if (!child_sigs.module_scope.isNone()) {
                            try self.symbol_table.bindExternalModuleScope(
                                file_id,
                                entry.name_symbol,
                                child_sigs.module_scope,
                            );
                            try self.symbol_table.named_module_scopes.put(
                                self.allocator,
                                entry.name_symbol.asInt(),
                                child_sigs.module_scope,
                            );
                        }
                    }
                }
            }
        }

        // Run Phase 4 symbol collection, `use` resolution, and signature type resolution for `file_id`:
        var mod_scope: ScopeId = .none;
        var sig_err_count: u32 = 0;
        var public_count: u32 = 0;
        if (self.source_inputs.getPtr(file_id.asInt())) |input_ptr| {
            if (self.parsed_artifacts.getPtr(file_id.asInt())) |parsed_ptr| {
                const was_core_allowed = self.symbol_table.is_internal_core;
                const had_included_tests = self.symbol_table.is_including_tests;
                const prev_cfg_env = self.symbol_table.cfg_env;
                self.symbol_table.is_internal_core = is_core_allowed;
                self.symbol_table.is_including_tests = is_including_tests;
                self.symbol_table.cfg_env = type_system.CfgEnv.fromTargetSpec(self.target_spec, is_including_tests);
                defer {
                    self.symbol_table.is_internal_core = was_core_allowed;
                    self.symbol_table.is_including_tests = had_included_tests;
                    self.symbol_table.cfg_env = prev_cfg_env;
                }

                const sig_sink = try resetOrCreateDefDiagSink(
                    &self.sig_diagnostics,
                    self.allocator,
                    file_id.asInt(),
                );

                // Detach previous module scope for `file_id` so re-runs allocate a clean scope:
                _ = self.symbol_table.file_module_scopes.remove(file_id.asInt());

                const sym_start: u32 = self.symbol_table.countSymbols();
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
                const sym_end: u32 = self.symbol_table.countSymbols();

                const sync_entries = (try self.extractItemTree(file_id)).entries;
                // Synchronize `DefId` bindings with flattened `extern` `ItemTree` entries when present:
                try self.syncFlattenedExternDefIds(
                    file_id,
                    is_including_tests,
                    parsed_ptr,
                    sync_entries,
                    sym_start,
                    sym_end,
                );

                if (!mod_scope.isNone()) {
                    // Link `parent_module` for both external child modules and any already-resolved parent file:
                    for (sync_entries) |entry| {
                        if (entry.kind == .mod_decl) {
                            const ext_key: u64 = (@as(u64, file_id.asInt()) << 32) |
                                @as(u64, entry.name_symbol.asInt());
                            if (self.symbol_table.external_module_scopes.get(ext_key)) |child_mod_scope| {
                                self.symbol_table.scope_arena.setParentModule(child_mod_scope, mod_scope);
                            }
                        }
                    }
                    var parent_ext_iter = self.external_mod_files.iterator();
                    while (parent_ext_iter.next()) |ext_kv| {
                        if (ext_kv.value_ptr.* == file_id) {
                            const parent_raw_fid: u32 = @truncate(ext_kv.key_ptr.* >> 32);
                            if (self.symbol_table.file_module_scopes.get(parent_raw_fid)) |parent_mod_scope| {
                                self.symbol_table.scope_arena.setParentModule(mod_scope, parent_mod_scope);
                            }
                            break;
                        }
                    }
                }

                for (root_mod_syms.items) |root_sym_raw| {
                    if (self.root_module_files.get(root_sym_raw) == file_id and !mod_scope.isNone()) {
                        try self.symbol_table.named_module_scopes.put(self.allocator, root_sym_raw, mod_scope);
                    }
                }

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
                checker.cfg_env = type_system.CfgEnv.fromTargetSpec(self.target_spec, is_including_tests);
                checker.is_including_tests = is_including_tests;
                checker.is_stdlib_file = (input_ptr.durability == .high);
                checker.is_internal_core = is_core_allowed;

                checker.resolveModuleSignatures() catch return error.OutOfMemory;
                sig_err_count = sig_sink.error_count;

                // Finalize `.cxi` `public_interface_fingerprint` across public items, inline `pub mod`, `pub const`, and `impl`s:
                const post_input_ptr = self.source_inputs.getPtr(file_id.asInt()) orelse
                    return error.MissingSourceInput;
                const post_parsed_ptr = self.parsed_artifacts.getPtr(file_id.asInt()) orelse
                    return error.MissingSourceInput;
                const latest_entries = (try self.extractItemTree(file_id)).entries;
                for (latest_entries) |entry| {
                    if (entry.kind == .impl_decl) {
                        self.hashImplDeclForPublicCxi(
                            &public_cxi_hasher,
                            &checker,
                            mod_scope,
                            post_input_ptr.owned_text,
                            post_parsed_ptr,
                            entry.ast_node,
                        );
                        continue;
                    }
                    if (!entry.isPublicOutsidePkg()) continue;
                    if (!checker.isCstNodeCfgEnabled(entry.cst_node)) continue;
                    public_count += 1;

                    if (entry.kind == .mod_decl) {
                        const is_inline_mod = !entry.ast_node.isNone() and
                            entry.ast_node.asInt() < post_parsed_ptr.ast_arena.countNodes() and
                            post_parsed_ptr.ast_arena.getNode(entry.ast_node).rhs.tag == .extra;
                        if (is_inline_mod) {
                            self.hashInlinePublicModForCxi(
                                &public_cxi_hasher,
                                &checker,
                                mod_scope,
                                post_input_ptr.owned_text,
                                post_parsed_ptr,
                                entry.ast_node,
                                entry.name_symbol,
                                entry.name_text,
                                0,
                            );
                        } else {
                            public_cxi_hasher.updateU8(@backingInt(entry.kind));
                            public_cxi_hasher.updateBytes(entry.name_text);
                            public_cxi_hasher.updateFingerprint(entry.signature_fingerprint);
                            const ext_key: u64 = (@as(u64, file_id.asInt()) << 32) |
                                @as(u64, entry.name_symbol.asInt());
                            if (self.external_mod_files.get(ext_key)) |child_fid| {
                                if (self.resolved_signatures.get(child_fid.asInt())) |child_sigs| {
                                    public_cxi_hasher.updateFingerprint(child_sigs.public_interface_fingerprint);
                                }
                            }
                        }
                        continue;
                    }

                    public_cxi_hasher.updateU8(@backingInt(entry.kind));
                    public_cxi_hasher.updateBytes(entry.name_text);
                    public_cxi_hasher.updateFingerprint(entry.signature_fingerprint);
                    if (entry.kind == .const_decl) {
                        public_cxi_hasher.updateFingerprint(entry.body_fingerprint);
                    }
                }
                if (!mod_scope.isNone()) {
                    for (self.symbol_table.getScopeMembers(mod_scope)) |mem_idx| {
                        const mem_sym = self.symbol_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind == .use_alias_sym and mem_sym.visibility == .public and
                            !mem_sym.target_symbol.isNone() and
                            mem_sym.target_symbol.asInt() < self.symbol_table.countSymbols())
                        {
                            const target_sym = self.symbol_table.getSymbol(mem_sym.target_symbol).*;
                            public_cxi_hasher.updateU8(0xE1);
                            public_cxi_hasher.updateBytes(mem_sym.name_text);
                            hashTypeCanonical(
                                &public_cxi_hasher,
                                &self.type_pool,
                                &self.symbol_table,
                                target_sym.type_id,
                            );
                        }
                    }
                }
                public_cxi_hasher.updateU32(public_count);

                var file_st = checker.extractFileSemanticSideTables(self.allocator) catch
                    return error.OutOfMemory;
                errdefer file_st.deinit();
                if (try self.file_side_tables.fetchPut(self.allocator, file_id.asInt(), file_st)) |prev_kv| {
                    var old_st = prev_kv.value;
                    old_st.deinit();
                }
                try self.file_sig_sync_states.put(self.allocator, file_id.asInt(), .{
                    .sym_start = sym_start,
                    .sym_end = sym_end,
                    .ast_fingerprint = post_parsed_ptr.ast_fingerprint,
                });
            }
        } else {
            for ((try self.extractItemTree(file_id)).entries) |entry| {
                if (entry.isPublicOutsidePkg()) {
                    public_count += 1;
                    public_cxi_hasher.updateU8(@backingInt(entry.kind));
                    public_cxi_hasher.updateBytes(entry.name_text);
                    public_cxi_hasher.updateFingerprint(entry.signature_fingerprint);
                    if (entry.kind == .const_decl) {
                        public_cxi_hasher.updateFingerprint(entry.body_fingerprint);
                    }
                }
            }
            public_cxi_hasher.updateU32(public_count);
        }

        if (self.active_stack.items.len > 0) {
            const cur_frame = self.active_stack.items[self.active_stack.items.len - 1];
            var has_embed_or_c_import = false;
            for (self.scratch_dep_edges.items[cur_frame.start_dep_index..]) |dep_key| {
                if (dep_key.stage == .source_text and (dep_key.flags & EMBED_FILE_KEY_FLAG) != 0) {
                    has_embed_or_c_import = true;
                } else if (dep_key.stage == .resolve_signatures and
                    dep_key.entity_index >= VIRTUAL_C_IMPORT_FILE_ID_BASE and
                    dep_key.entity_index < CONFIG_KEY_TARGET_LAYOUT)
                {
                    has_embed_or_c_import = true;
                    if (self.resolved_signatures.get(dep_key.entity_index)) |c_imp_sigs| {
                        hasher.updateU32(dep_key.entity_index);
                        hasher.updateFingerprint(c_imp_sigs.public_interface_fingerprint);
                        hasher.updateU32(c_imp_sigs.error_count);
                    }
                }
            }
            if (has_embed_or_c_import) {
                hasher.updateU32(sig_err_count);
            }
        }

        const final_item_count: u32 = @intCast((try self.extractItemTree(file_id)).entries.len);
        const resolved_fp = hasher.final();
        try self.resolved_signatures.put(self.allocator, file_id.asInt(), .{
            .file_id = file_id,
            .module_scope = mod_scope,
            .item_count = final_item_count,
            .public_item_count = public_count,
            .error_count = sig_err_count,
            .signatures_fingerprint = resolved_fp,
            .public_interface_fingerprint = public_cxi_hasher.final(),
        });
        return resolved_fp;
    }

    /// Reconciles `SymbolRecord.def_id`, `owner_def_id`, and `def_to_symbol` with flattened `extern` `ItemTree` entries.
    fn syncFlattenedExternDefIds(
        self: *CompilerDb,
        file_id: FileId,
        is_including_tests: bool,
        parsed_ptr: *const ParsedCstArtifact,
        item_entries: []const ItemTreeEntry,
        sym_start: u32,
        sym_end: u32,
    ) QueryError!void {
        if (parsed_ptr.ast_arena.countNodes() == 0 or parsed_ptr.root_node.isNone()) return;
        const root_ast = parsed_ptr.ast_arena.getNode(parsed_ptr.root_node);
        if (root_ast.lhs.tag != .extra or root_ast.rhs.tag != .extra or root_ast.rhs.payload == 0) return;
        const raw_items = parsed_ptr.ast_arena.getExtraSlice(
            ExtraIndex.fromInt(root_ast.lhs.payload),
            root_ast.rhs.payload,
        );
        var has_extern_items = false;
        for (raw_items) |raw_idx| {
            const top_id = NodeIndex.fromInt(raw_idx);
            if (top_id.asInt() >= parsed_ptr.ast_arena.countNodes()) continue;
            const top_tag = parsed_ptr.ast_arena.getNode(top_id).tag;
            if (top_tag == .extern_block_decl or top_tag == .extern_static_decl) {
                has_extern_items = true;
                break;
            }
        }
        if (!has_extern_items) return;

        var ast_to_def: std.AutoHashMapUnmanaged(u32, DefId) = .empty;
        defer ast_to_def.deinit(self.allocator);
        for (item_entries) |entry| {
            if (!entry.ast_node.isNone()) {
                try ast_to_def.put(self.allocator, entry.ast_node.asInt(), entry.def_id);
            }
        }

        var unflattened_owner_remap: std.AutoHashMapUnmanaged(u32, DefId) = .empty;
        defer unflattened_owner_remap.deinit(self.allocator);
        var raw_ord: u12 = 0;
        for (raw_items) |raw_idx| {
            const top_id = NodeIndex.fromInt(raw_idx);
            if (top_id.asInt() >= parsed_ptr.ast_arena.countNodes()) continue;
            const top_tag = parsed_ptr.ast_arena.getNode(top_id).tag;
            if (top_tag == .item_hole) continue;
            if (!is_including_tests and (top_tag == .test_decl or top_tag == .bench_decl)) continue;
            const unflattened_def = DefId.init(file_id, raw_ord);
            if (raw_ord < std.math.maxInt(u12)) raw_ord += 1;
            if (ast_to_def.get(top_id.asInt())) |flattened_def| {
                if (flattened_def != unflattened_def) {
                    try unflattened_owner_remap.put(self.allocator, unflattened_def.asInt(), flattened_def);
                }
            }
        }

        var has_unflattened_syms = false;
        var check_sym: u32 = sym_start;
        while (check_sym < sym_end) : (check_sym += 1) {
            const sym = self.symbol_table.getSymbol(SymbolIndex.fromInt(check_sym)).*;
            if (sym.ast_node.isNone() or sym.def_id.isNone()) continue;
            if (ast_to_def.get(sym.ast_node.asInt())) |expected_def| {
                if (sym.def_id != expected_def) {
                    has_unflattened_syms = true;
                    break;
                }
            }
        }

        var stale_defs: std.ArrayListUnmanaged(u32) = .empty;
        defer stale_defs.deinit(self.allocator);
        var def_iter = self.symbol_table.def_to_symbol.keyIterator();
        while (def_iter.next()) |def_key_ptr| {
            if (DefId.fromInt(def_key_ptr.*).fileId() == file_id) {
                try stale_defs.append(self.allocator, def_key_ptr.*);
            }
        }
        for (stale_defs.items) |stale_raw| {
            _ = self.symbol_table.def_to_symbol.remove(stale_raw);
        }

        var sym_raw: u32 = sym_start;
        while (sym_raw < sym_end) : (sym_raw += 1) {
            const sym_idx = SymbolIndex.fromInt(sym_raw);
            const sym_mut = self.symbol_table.getSymbolMut(sym_idx);
            if (!sym_mut.ast_node.isNone()) {
                if (ast_to_def.get(sym_mut.ast_node.asInt())) |canonical_def| {
                    if (sym_mut.kind != .field_sym and
                        sym_mut.kind != .enum_variant_sym and
                        sym_mut.kind != .param_sym and
                        sym_mut.kind != .type_param_sym and
                        sym_mut.kind != .const_param_sym)
                    {
                        sym_mut.def_id = canonical_def;
                        try self.symbol_table.def_to_symbol.put(
                            self.allocator,
                            canonical_def.asInt(),
                            sym_idx,
                        );
                        continue;
                    }
                }
            }
            if (!sym_mut.def_id.isNone() and sym_mut.def_id.fileId() == file_id) {
                try self.symbol_table.def_to_symbol.put(
                    self.allocator,
                    sym_mut.def_id.asInt(),
                    sym_idx,
                );
            }
            if (has_unflattened_syms and !sym_mut.owner_def_id.isNone()) {
                if (unflattened_owner_remap.get(sym_mut.owner_def_id.asInt())) |mapped_owner| {
                    sym_mut.owner_def_id = mapped_owner;
                }
            }
        }
    }

    /// Synchronizes `.fn_sym` AST/CST handles and default-argument side tables after Early Cutoff (`SE-07`).
    fn ensureFreshSignatureAstAndSideTables(self: *CompilerDb, file_id: FileId) QueryError!void {
        const sync_ptr = self.file_sig_sync_states.getPtr(file_id.asInt()) orelse return;
        const parsed_ptr = self.parsed_artifacts.getPtr(file_id.asInt()) orelse return;
        if (Fingerprint128.eql(sync_ptr.ast_fingerprint, parsed_ptr.ast_fingerprint)) return;
        const input_ptr = self.source_inputs.getPtr(file_id.asInt()) orelse return;
        const is_including_tests = try self.readIncludeTests();

        const fn_handles = try symbol_resolver.collectFileFnDeclHandlesWithOptions(
            self.allocator,
            input_ptr.owned_text,
            &parsed_ptr.token_buffer,
            &parsed_ptr.cst_arena,
            &parsed_ptr.ast_arena,
            is_including_tests,
        );
        defer if (fn_handles.len > 0) self.allocator.free(fn_handles);

        var default_fn_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
        defer default_fn_syms.deinit(self.allocator);

        const clamped_end = @min(sync_ptr.sym_end, self.symbol_table.countSymbols());
        var handle_cursor: usize = 0;
        var sym_raw: u32 = sync_ptr.sym_start;
        while (sym_raw < clamped_end and handle_cursor < fn_handles.len) : (sym_raw += 1) {
            const sym_idx = SymbolIndex.fromInt(sym_raw);
            const sym = self.symbol_table.getSymbol(sym_idx).*;
            if (sym.kind != .fn_sym or sym.flags.is_builtin or sym.flags.is_imported) continue;
            if (sym.decl_span.file_id != file_id) continue;

            const sym_mut = self.symbol_table.getSymbolMut(sym_idx);
            sym_mut.ast_node = fn_handles[handle_cursor].ast_node;
            sym_mut.cst_node = fn_handles[handle_cursor].cst_node;
            handle_cursor += 1;

            for (self.symbol_table.getFnParamSpecs(sym_idx)) |spec| {
                if (spec.has_default and spec.decl_file_id == file_id) {
                    try default_fn_syms.append(self.allocator, sym_idx);
                    break;
                }
            }
        }

        if (default_fn_syms.items.len > 0) {
            const active_layout = try self.readTargetLayout();
            const is_core_allowed = self.readInternalCore() or (input_ptr.durability == .high);
            const was_core_allowed = self.symbol_table.is_internal_core;
            self.symbol_table.is_internal_core = is_core_allowed;
            defer self.symbol_table.is_internal_core = was_core_allowed;

            var scratch_sink = DiagnosticSink.init(self.allocator);
            defer scratch_sink.deinit();

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
                &scratch_sink,
            ) catch return error.OutOfMemory;
            defer checker.deinit();
            checker.db = self;
            checker.target_layout = active_layout;
            checker.cfg_env = type_system.CfgEnv.fromTargetSpec(self.target_spec, is_including_tests);
            checker.is_including_tests = is_including_tests;
            checker.is_stdlib_file = (input_ptr.durability == .high);
            checker.is_internal_core = is_core_allowed;

            for (default_fn_syms.items) |fn_sym_idx| {
                checker.refreshFnDefaultParamAstAndSideTables(fn_sym_idx) catch return error.OutOfMemory;
            }

            var new_file_st = checker.extractFileSemanticSideTables(self.allocator) catch return error.OutOfMemory;
            errdefer new_file_st.deinit();

            if (self.file_side_tables.getPtr(file_id.asInt())) |prev_st_ptr| {
                if (prev_st_ptr.attr_instances.len > 0 and new_file_st.attr_instances.len == 0) {
                    new_file_st.attr_instances = prev_st_ptr.attr_instances;
                    prev_st_ptr.attr_instances = &.{};
                }
            }
            if (try self.file_side_tables.fetchPut(self.allocator, file_id.asInt(), new_file_st)) |prev_kv| {
                var old_st = prev_kv.value;
                old_st.deinit();
            }
        }
        sync_ptr.ast_fingerprint = parsed_ptr.ast_fingerprint;
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
        const param_specs = if (!sym_idx.isNone())
            self.symbol_table.getFnParamSpecs(sym_idx)
        else
            &.{};
        const generic_specs = if (!sym_idx.isNone())
            self.symbol_table.getGenericParamSpecs(sym_idx)
        else
            &.{};

        var hasher = StructuralHasher.init();
        hasher.updateU32(def_id.asInt());
        hasher.updateU8(@backingInt(entry.kind));
        hasher.updateU8(@backingInt(entry.visibility));
        hasher.updateBytes(entry.name_text);
        hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, resolved_ty);
        hasher.updateU32(@intCast(param_specs.len));
        for (param_specs) |pspec| {
            // Erase positional-only (`before /`) parameter names so caller signatures hit Early Cutoff (`SE-11`):
            if (pspec.is_positional_only) {
                hasher.updateU8(1);
                hasher.updateU32(1);
                hasher.updateBytes("_");
            } else {
                hashSymbolTextCanonical(&hasher, &self.interner, pspec.name);
            }
            hasher.updateU8(@intFromBool(pspec.has_default));
            hasher.updateU8(@intFromBool(pspec.is_positional_only));
            hasher.updateU8(@intFromBool(pspec.is_keyword_only));
            hasher.updateU8(@intFromBool(pspec.is_variadic));
            hasher.updateU8(@intFromBool(pspec.is_builder));
            hasher.updateU8(@intFromBool(pspec.is_caller_location_default));
        }
        hasher.updateU32(@intCast(generic_specs.len));
        for (generic_specs) |gspec| {
            hashSymbolTextCanonical(&hasher, &self.interner, gspec.name);
            hasher.updateU8(@intFromBool(gspec.is_const));
            hasher.updateU8(@intFromBool(gspec.has_default));
            if (gspec.has_default) {
                hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, gspec.default_type_id);
                hashSymbolTextCanonical(&hasher, &self.interner, gspec.default_type_sym);
                hasher.updateU64(gspec.default_syntax_hash);
            }
        }
        hasher.updateFingerprint(item_sig_fp);
        const def_sig_fp = hasher.final();

        try self.def_signatures.put(self.allocator, def_id.asInt(), .{
            .def_id = def_id,
            .kind = entry.kind,
            .visibility = entry.visibility,
            .name_symbol = entry.name_symbol,
            .symbol_index = sym_idx,
            .type_id = resolved_ty,
            .param_specs = param_specs,
            .generic_specs = generic_specs,
            .signature_fingerprint = def_sig_fp,
        });
        return def_sig_fp;
    }

    /// Stage 8 implementation: type-checks `def_id`'s body in isolation from sibling definitions.
    fn computeTypecheckBody(self: *CompilerDb, def_id: DefId) QueryError!Fingerprint128 {
        if (def_id.isNone()) return error.InvalidDefId;
        const file_id = def_id.fileId();
        _ = try self.resolveSignatures(file_id);
        const def_sig = try self.getDefSignature(def_id);
        const body_window = try self.getBodyAstProj(def_id);
        const active_layout = try self.readTargetLayout();
        const is_including_tests = try self.readIncludeTests();
        const is_internal_core = self.readInternalCore();
        const is_stdlib_durability = if (self.source_inputs.get(file_id.asInt())) |inp|
            inp.durability == .high
        else
            false;
        const is_core_allowed = is_internal_core or is_stdlib_durability;
        try self.unwindIfCancelled();

        var body_err_count: u32 = 0;
        var body_warn_count: u32 = 0;

        if (self.source_inputs.getPtr(file_id.asInt())) |input_ptr| {
            if (self.parsed_artifacts.getPtr(file_id.asInt())) |parsed_ptr| {
                const was_core_allowed = self.symbol_table.is_internal_core;
                self.symbol_table.is_internal_core = is_core_allowed;
                defer self.symbol_table.is_internal_core = was_core_allowed;

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
                checker.cfg_env = type_system.CfgEnv.fromTargetSpec(self.target_spec, is_including_tests);
                checker.is_including_tests = is_including_tests;
                checker.is_stdlib_file = (input_ptr.durability == .high);
                checker.is_internal_core = is_core_allowed;

                if (def_sig.kind == .extern_static or def_sig.kind == .ffi_extern_block) {
                    // Prototype-only foreign static/block declarations carry no body block.
                } else if (!def_sig.symbol_index.isNone() and
                    (def_sig.kind == .fn_decl or def_sig.kind == .const_decl) and
                    !body_window.item_ast_node.isNone() and
                    body_window.item_ast_node.asInt() < parsed_ptr.ast_arena.countNodes())
                {
                    const sym_idx = def_sig.symbol_index;
                    if (!checker.isSymbolCfgDisabled(sym_idx)) {
                        const sym_mut = self.symbol_table.getSymbolMut(sym_idx);
                        sym_mut.ast_node = body_window.item_ast_node;
                        sym_mut.cst_node = parsed_ptr.ast_arena.getCstOrigin(body_window.item_ast_node);
                        const sym_rec = sym_mut.*;
                        if (sym_rec.kind == .fn_sym) {
                            if (!sym_rec.target_scope.isNone()) {
                                const param_specs = self.symbol_table.getFnParamSpecs(sym_idx);
                                for (self.symbol_table.getScopeMembers(sym_rec.target_scope)) |mem_idx| {
                                    const mem_sym = self.symbol_table.getSymbol(mem_idx).*;
                                    if (mem_sym.kind == .param_sym) {
                                        self.symbol_table.getSymbolMut(mem_idx).flags.is_used =
                                            mem_sym.member_ordinal < param_specs.len and
                                            param_specs[mem_sym.member_ordinal].is_used_by_default;
                                    }
                                }
                            }
                            checker.checkFnDeclBody(sym_idx) catch return error.OutOfMemory;
                        } else if (sym_rec.kind == .const_sym) {
                            const temp_const_def = DefId.init(file_id, std.math.maxInt(u12) - 1);
                            try self.symbol_table.def_to_symbol.put(
                                self.allocator,
                                temp_const_def.asInt(),
                                sym_idx,
                            );
                            defer _ = self.symbol_table.def_to_symbol.remove(temp_const_def.asInt());
                            checker.checkDefBody(temp_const_def) catch return error.OutOfMemory;
                        } else {
                            checker.checkDefBody(def_id) catch return error.OutOfMemory;
                        }
                    }
                } else {
                    var target_check_def = def_id;
                    if (!body_window.item_ast_node.isNone() and parsed_ptr.ast_arena.countNodes() > 0) {
                        const root_node = parsed_ptr.ast_arena.getNode(.root);
                        if (root_node.lhs.tag == .extra and root_node.rhs.tag == .extra and
                            root_node.rhs.payload > 0)
                        {
                            const raw_slice = parsed_ptr.ast_arena.getExtraSlice(
                                ExtraIndex.fromInt(root_node.lhs.payload),
                                root_node.rhs.payload,
                            );
                            var top_ord: u12 = 0;
                            for (raw_slice) |raw_idx| {
                                const cand_id = NodeIndex.fromInt(raw_idx);
                                if (cand_id.asInt() >= parsed_ptr.ast_arena.countNodes()) continue;
                                if (parsed_ptr.ast_arena.getNode(cand_id).tag == .item_hole) continue;
                                if (cand_id == body_window.item_ast_node) {
                                    target_check_def = DefId.init(file_id, top_ord);
                                    break;
                                }
                                if (top_ord < std.math.maxInt(u12)) top_ord += 1;
                            }
                        }
                    }
                    if (target_check_def != def_id and def_sig.symbol_index.isNone()) {
                        const saved_occupant = self.symbol_table.def_to_symbol.fetchRemove(
                            target_check_def.asInt(),
                        );
                        defer if (saved_occupant) |occ_kv| {
                            self.symbol_table.def_to_symbol.put(
                                self.allocator,
                                occ_kv.key,
                                occ_kv.value,
                            ) catch {};
                        };
                        var remapped_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
                        defer {
                            for (remapped_syms.items) |rem_idx| {
                                self.symbol_table.getSymbolMut(rem_idx).owner_def_id = def_id;
                            }
                            remapped_syms.deinit(self.allocator);
                        }
                        var scan_i: u32 = 0;
                        while (scan_i < self.symbol_table.countSymbols()) : (scan_i += 1) {
                            const cand_sym_idx = SymbolIndex.fromInt(scan_i);
                            if (self.symbol_table.getSymbol(cand_sym_idx).owner_def_id == def_id) {
                                self.symbol_table.getSymbolMut(cand_sym_idx).owner_def_id = target_check_def;
                                try remapped_syms.append(self.allocator, cand_sym_idx);
                            }
                        }
                        checker.checkDefBody(target_check_def) catch return error.OutOfMemory;
                    } else {
                        checker.checkDefBody(def_id) catch return error.OutOfMemory;
                    }
                }
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
        hasher.updateU8(@backingInt(self.target_spec.arch));
        hasher.updateU8(@backingInt(self.target_spec.os));
        hasher.updateU8(@backingInt(self.target_spec.abi));
        hasher.updateU8(@backingInt(self.target_spec.simd_level));
        hasher.updateU8(@intFromBool(is_core_allowed));
        hasher.updateFingerprint(def_sig.signature_fingerprint);
        hasher.updateFingerprint(body_window.body_fingerprint);
        hasher.updateU32(body_err_count);
        hasher.updateU32(body_warn_count);

        if (self.def_side_tables.getPtr(def_id.asInt())) |st_ptr| {
            hasher.updateU8(1);
            var referenced_defs: std.AutoHashMapUnmanaged(u32, void) = .empty;
            defer referenced_defs.deinit(self.allocator);
            var sorted_keys: std.ArrayListUnmanaged(u32) = .empty;
            defer sorted_keys.deinit(self.allocator);

            hasher.updateU32(@intCast(st_ptr.node_types.len));
            for (st_ptr.node_types) |node_ty| {
                hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, node_ty);
            }

            hasher.updateU32(@intCast(st_ptr.node_symbols.len));
            for (st_ptr.node_symbols) |sym_idx| {
                if (sym_idx.isNone() or sym_idx.asInt() >= self.symbol_table.countSymbols()) {
                    hasher.updateU8(0);
                } else {
                    const sym = self.symbol_table.getSymbol(sym_idx).*;
                    hasher.updateU8(1);
                    hasher.updateU8(@backingInt(sym.kind));
                    hasher.updateU32(sym.def_id.asInt());
                    hasher.updateU32(sym.owner_def_id.asInt());
                    hasher.updateU16(sym.member_ordinal);
                    hasher.updateBytes(sym.name_text);
                    hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, sym.type_id);
                    var resolved_sym = sym;
                    var alias_hops: u8 = 0;
                    while (resolved_sym.kind == .use_alias_sym and
                        !resolved_sym.target_symbol.isNone() and
                        resolved_sym.target_symbol.asInt() < self.symbol_table.countSymbols() and
                        alias_hops < 16) : (alias_hops += 1)
                    {
                        resolved_sym = self.symbol_table.getSymbol(resolved_sym.target_symbol).*;
                    }
                    const ref_def = if (!resolved_sym.def_id.isNone())
                        resolved_sym.def_id
                    else
                        resolved_sym.owner_def_id;
                    if (!ref_def.isNone() and ref_def != def_id) {
                        try referenced_defs.put(self.allocator, ref_def.asInt(), {});
                    }
                }
            }

            sorted_keys.clearRetainingCapacity();
            var inst_key_iter = st_ptr.call_instantiations.keyIterator();
            while (inst_key_iter.next()) |key_ptr| {
                try sorted_keys.append(self.allocator, key_ptr.*);
            }
            std.mem.sort(u32, sorted_keys.items, {}, std.sort.asc(u32));
            hasher.updateU32(@intCast(sorted_keys.items.len));
            for (sorted_keys.items) |rel_key| {
                const ty_slice = st_ptr.call_instantiations.get(rel_key).?;
                hasher.updateU32(rel_key);
                hasher.updateU32(@intCast(ty_slice.len));
                for (ty_slice) |inst_ty| {
                    hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, inst_ty);
                }
            }

            sorted_keys.clearRetainingCapacity();
            var try_key_iter = st_ptr.try_conversions.keyIterator();
            while (try_key_iter.next()) |key_ptr| {
                try sorted_keys.append(self.allocator, key_ptr.*);
            }
            std.mem.sort(u32, sorted_keys.items, {}, std.sort.asc(u32));
            hasher.updateU32(@intCast(sorted_keys.items.len));
            for (sorted_keys.items) |rel_key| {
                const conv_def = st_ptr.try_conversions.get(rel_key).?;
                hasher.updateU32(rel_key);
                hasher.updateU32(conv_def.asInt());
                if (!conv_def.isNone() and conv_def != def_id) {
                    try referenced_defs.put(self.allocator, conv_def.asInt(), {});
                }
            }

            sorted_keys.clearRetainingCapacity();
            var narrow_key_iter = st_ptr.narrow_calls.keyIterator();
            while (narrow_key_iter.next()) |key_ptr| {
                try sorted_keys.append(self.allocator, key_ptr.*);
            }
            std.mem.sort(u32, sorted_keys.items, {}, std.sort.asc(u32));
            hasher.updateU32(@intCast(sorted_keys.items.len));
            for (sorted_keys.items) |rel_key| {
                const narrow_info = st_ptr.narrow_calls.get(rel_key).?;
                hasher.updateU32(rel_key);
                hasher.updateU8(@backingInt(narrow_info.kind));
                hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, narrow_info.src_ty);
                hashTypeCanonical(&hasher, &self.type_pool, &self.symbol_table, narrow_info.dst_ty);
                const min_bits: u128 = @bitCast(narrow_info.min_val);
                const max_bits: u128 = @bitCast(narrow_info.max_val);
                hasher.updateU64(@truncate(min_bits));
                hasher.updateU64(@truncate(min_bits >> 64));
                hasher.updateU64(@truncate(max_bits));
                hasher.updateU64(@truncate(max_bits >> 64));
            }

            // Snapshot `call_arg_mappings` keys before any nested `getDefSignature` query call:
            sorted_keys.clearRetainingCapacity();
            var map_key_iter = st_ptr.call_arg_mappings.keyIterator();
            while (map_key_iter.next()) |key_ptr| {
                try sorted_keys.append(self.allocator, key_ptr.*);
            }
            std.mem.sort(u32, sorted_keys.items, {}, std.sort.asc(u32));
            hasher.updateU32(@intCast(sorted_keys.items.len));

            var default_callee_defs: std.ArrayListUnmanaged(DefId) = .empty;
            defer default_callee_defs.deinit(self.allocator);

            for (sorted_keys.items) |rel_key| {
                const mapping = st_ptr.call_arg_mappings.get(rel_key).?;
                hasher.updateU32(rel_key);
                hasher.updateU16(mapping.total_params);
                hasher.updateU8(@intFromBool(mapping.has_reordered_or_default));
                hasher.updateU32(@intCast(mapping.provided_slots.len));
                for (mapping.provided_slots) |slot| {
                    hasher.updateU16(slot.param_index);
                    hasher.updateU32(slot.arg_ast_node.asInt() -| st_ptr.ast_start);
                    hasher.updateU8(@intFromBool(slot.is_named));
                }
                if (!mapping.callee_sym.isNone() and
                    mapping.callee_sym.asInt() < self.symbol_table.countSymbols())
                {
                    var callee_sym = self.symbol_table.getSymbol(mapping.callee_sym).*;
                    var alias_hops: u8 = 0;
                    while (callee_sym.kind == .use_alias_sym and
                        !callee_sym.target_symbol.isNone() and
                        callee_sym.target_symbol.asInt() < self.symbol_table.countSymbols() and
                        alias_hops < 16) : (alias_hops += 1)
                    {
                        callee_sym = self.symbol_table.getSymbol(callee_sym.target_symbol).*;
                    }
                    const callee_def = if (!callee_sym.def_id.isNone())
                        callee_sym.def_id
                    else
                        callee_sym.owner_def_id;
                    hasher.updateU32(callee_def.asInt());
                    if (!callee_def.isNone() and callee_def != def_id) {
                        try referenced_defs.put(self.allocator, callee_def.asInt(), {});
                    }
                    if (!callee_def.isNone() and mapping.provided_slots.len < mapping.total_params) {
                        try default_callee_defs.append(self.allocator, callee_def);
                    }
                } else {
                    hasher.updateU32(DefId.NONE.asInt());
                }
            }

            // Record fine-grained `def_signature` dependencies on referenced callees/items:
            sorted_keys.clearRetainingCapacity();
            var ref_iter = referenced_defs.keyIterator();
            while (ref_iter.next()) |raw_def_ptr| {
                try sorted_keys.append(self.allocator, raw_def_ptr.*);
            }
            std.mem.sort(u32, sorted_keys.items, {}, std.sort.asc(u32));
            for (sorted_keys.items) |raw_ref_def| {
                const ref_def: DefId = @bitCast(raw_ref_def);
                const ref_file = ref_def.fileId();
                if (self.item_trees.getPtr(ref_file.asInt())) |it_ptr| {
                    if (it_ptr.getEntry(ref_def) != null and
                        !self.in_flight_keys.contains(QueryKey.forDef(.def_signature, ref_def).asU64()))
                    {
                        _ = try self.getDefSignature(ref_def);
                    }
                }
            }

            // Hash `def_signature` fingerprints of callees invoked with omitted `ARG_SOURCE_DEFAULT` arguments:
            hasher.updateU32(@intCast(default_callee_defs.items.len));
            for (default_callee_defs.items) |callee_def| {
                const callee_file = callee_def.fileId();
                if (self.item_trees.getPtr(callee_file.asInt())) |it_ptr| {
                    if (it_ptr.getEntry(callee_def) != null and
                        !self.in_flight_keys.contains(QueryKey.forDef(.def_signature, callee_def).asU64()))
                    {
                        const callee_sig = try self.getDefSignature(callee_def);
                        hasher.updateFingerprint(callee_sig.signature_fingerprint);
                    }
                }
            }
        } else {
            hasher.updateU8(0);
        }

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

    /// Constructs a fail-closed conservative `FnRegionSummary` for an in-flight mutual-recursion cycle.
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
            .direct_effects_bits = 0x3FFF,
            .inferred_effects_bits = 0x3FFF,
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
            if (dsig.kind == .extern_block or
                dsig.kind == .ffi_extern_block or
                dsig.kind == .extern_static)
            {
                return null;
            }
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
        if (!callee_sym.isNone() and callee_sym.asInt() < db.symbol_table.symbols.items.len) {
            const sym_rec = db.symbol_table.getSymbol(callee_sym).*;
            if (sym_rec.def_id.isNone()) {
                if (db.sast_sym_summaries.get(callee_sym.asInt())) |method_sum| {
                    return method_sum;
                }
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

        if (self.item_trees.getPtr(target_file.asInt())) |tree_ptr| {
            if (tree_ptr.getEntry(target_def)) |entry| {
                if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) return;
                if (entry.kind == .fn_decl and entry.body_ast_node.isNone()) return;
            }
        }

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
        try self.ensureFreshSignatureAstAndSideTables(def_id.fileId());
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

                // If `resolveDbCalleeSummary` discovered a cross-`DefId` mutual-recursion cycle,
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

    /// Stage 10 implementation: lowers `def_id` into an isolated `HirStore`.
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

        if (self.item_trees.getPtr(file_id.asInt())) |tree_ptr| {
            if (tree_ptr.getEntry(def_id)) |entry| {
                if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) {
                    var empty_store = hir.HirStore.init(self.allocator, file_id);
                    empty_store.target_layout = active_layout;
                    const empty_fp = computeHirStoreFingerprint(
                        &empty_store,
                        &self.type_pool,
                        &self.symbol_table,
                        &self.interner,
                    );
                    if (try self.lowered_def_hirs.fetchPut(self.allocator, def_id.asInt(), empty_store)) |prev_kv| {
                        var old_store = prev_kv.value;
                        old_store.deinit();
                    }
                    return empty_fp;
                }
            }
        }

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

        const target_ret_ty = target_body.ret_ty;
        var primary_idx: usize = 0;
        for (mir_art.bundle.bodies.items, 0..) |*body_item, b_idx| {
            if (body_item.def_id == def_id) {
                primary_idx = b_idx;
                break;
            }
        }

        var unelaborated_clones: std.ArrayListUnmanaged(mir.MirBody) = .empty;
        defer {
            for (unelaborated_clones.items) |*raw_clone| raw_clone.deinit();
            unelaborated_clones.deinit(self.allocator);
        }
        for (mir_art.bundle.bodies.items) |*src_body| {
            var dup_raw = src_body.clone(self.allocator) catch return error.OutOfMemory;
            errdefer dup_raw.deinit();
            try unelaborated_clones.append(self.allocator, dup_raw);
        }

        // Elaborate `drop_in_place` / `drop_if_live` and reject `E0325` before `MirVm` execution:
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

            for (unelaborated_clones.items) |*src_body| {
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
                        .type_id = target_ret_ty,
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
        const exec_bodies = if (is_using_elaborated_clones) cloned_bodies.items else unelaborated_clones.items;
        const exec_target = &exec_bodies[primary_idx];
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
                    .type_id = target_ret_ty,
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

        var entry_idx: usize = 0;
        while (entry_idx < (try self.extractItemTree(file_id)).entries.len) : (entry_idx += 1) {
            const entry = (try self.extractItemTree(file_id)).entries[entry_idx];
            if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) continue;
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
        hasher.updateU8(@backingInt(self.target_spec.arch));
        hasher.updateU8(@backingInt(self.target_spec.os));
        hasher.updateU8(@backingInt(self.target_spec.abi));
        hasher.updateU8(@backingInt(self.target_spec.simd_level));
        hasher.updateU8(active_layout.ptr_byte_size);
        hasher.updateU8(active_layout.cache_line_align_log2);
        hasher.updateU8(active_layout.simd_align_log2);
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

/// Computes the deterministic `DR-19` §1.2 `FieldHash64` (`TypeLayoutHash`) for `raw_ty` under `target_layout`.
pub fn computeNominalFieldHash64(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) FieldHash64 {
    return FieldHash64.fromInt(computeNominalFieldHash64Bounded(
        pool,
        sym_table,
        raw_ty,
        target_layout,
        &type_system.NominalTypeSubst.EMPTY,
        &.{},
        0,
    ));
}

/// Builds a 32-byte `CxTypeLayoutRecord` pairing `LayoutShapeKey` with semantic `FieldHash64` (`DR-19` §1.2).
pub fn buildCxTypeLayoutRecord(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) codegen_dev_seam.CxTypeLayoutRecord {
    const layout = type_system.computeTypeLayoutWithPool(pool, sym_table, raw_ty, target_layout);
    const shape_key = mir_opt.computeLayoutShapeKey(pool, sym_table, raw_ty, target_layout);
    const tier_bits: u8 = @backingInt(type_system.classifyOwnershipTier(pool, sym_table, raw_ty));
    var kind_flags: u8 = tier_bits;
    var fields_len: u16 = 0;
    var fqn_hash32: u32 = 0;
    if (!raw_ty.isPrimitiveOrSentinel()) {
        const node = pool.getNode(raw_ty);
        if (node.tag == .struct_ty or node.tag == .union_ty or node.tag == .enum_ty) {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const nom_sym = sym_table.getSymbol(sym_idx).*;
                fqn_hash32 = @truncate(std.hash.Wyhash.hash(0, nom_sym.name_text));
                if (nom_sym.contract_flags.is_repr_c) kind_flags |= 0x04;
                if (nom_sym.contract_flags.is_packed) kind_flags |= 0x08;
                if (nom_sym.contract_flags.is_cache_aligned) kind_flags |= 0x10;
                if (!nom_sym.target_scope.isNone()) {
                    for (sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                        const mk = sym_table.getSymbol(mem_idx).kind;
                        if (mk == .field_sym or mk == .enum_variant_sym) fields_len +|= 1;
                    }
                }
            }
        }
    }
    return .{
        .type_id = raw_ty,
        .byte_size = @intCast(@min(layout.byte_size, std.math.maxInt(u32))),
        .align_log2 = layout.align_log2,
        .kind_flags = kind_flags,
        .fields_len = fields_len,
        .fqn_hash32 = fqn_hash32,
        .layout_shape_hash64 = std.hash.Wyhash.hash(0, std.mem.asBytes(&shape_key)),
        .field_hash64 = computeNominalFieldHash64(pool, sym_table, raw_ty, target_layout).asInt(),
    };
}

/// Collects deterministic `CxTypeLayoutRecord` entries for all composite types across `bodies`.
pub fn collectModuleDevTypeRecords(
    allocator: std.mem.Allocator,
    bodies: []const mir.MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
) ![]codegen_dev_seam.CxTypeLayoutRecord {
    var seen_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer seen_set.deinit(allocator);
    var discovered_ids: std.ArrayListUnmanaged(u32) = .empty;
    defer discovered_ids.deinit(allocator);

    for (bodies) |*body_ptr| {
        try discoverDevRecordTypeBounded(
            allocator,
            pool,
            sym_table,
            body_ptr.ret_ty,
            &seen_set,
            &discovered_ids,
            0,
        );
        for (body_ptr.locals.items) |loc_decl| {
            try discoverDevRecordTypeBounded(
                allocator,
                pool,
                sym_table,
                loc_decl.type_id,
                &seen_set,
                &discovered_ids,
                0,
            );
        }
        for (0..body_ptr.insts.len) |inst_raw| {
            try discoverDevRecordTypeBounded(
                allocator,
                pool,
                sym_table,
                body_ptr.insts.get(inst_raw).type_id,
                &seen_set,
                &discovered_ids,
                0,
            );
        }
        for (body_ptr.calls.items) |call_site| {
            try discoverDevRecordTypeBounded(
                allocator,
                pool,
                sym_table,
                call_site.ret_ty,
                &seen_set,
                &discovered_ids,
                0,
            );
        }
    }

    std.mem.sort(u32, discovered_ids.items, {}, std.sort.asc(u32));
    const records = try allocator.alloc(codegen_dev_seam.CxTypeLayoutRecord, discovered_ids.items.len);
    for (discovered_ids.items, 0..) |raw_id, idx| {
        records[idx] = buildCxTypeLayoutRecord(
            pool,
            sym_table,
            TypeId.fromInt(raw_id),
            target_layout,
        );
    }
    return records;
}

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
    try std.testing.expectEqual(Visibility.public, tree_r1.entries[0].visibility);
    try std.testing.expect(tree_r1.entries[0].isPublicOutsidePkg());
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
    const spin_def = (try db.extractItemTree(loop_file)).entries[1].def_id;
    const spin_eval = try db.evalComptimeDef(spin_def);
    try std.testing.expect(spin_eval.has_errors);
    const spin_diags = db.getComptimeDiagnostics(spin_def).?;
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0501_comptime_step_limit_exceeded,
        spin_diags.diagnostics.items[0].code,
    );
}

test "test_phase5_config_invalidation_target_layout_wasm32_step_limit_and_embed_sandbox" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] `setTargetLayout(WASM32)` invalidates cached `@size_of[*u8]()` (`8 -> 4`):
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

    // [2] `setEmbedSandbox` invalidates cached `@embed_bytes` queries:
    var vfs_v1: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_v1.deinit(std.testing.allocator);
    try vfs_v1.put(std.testing.allocator, "assets/ver.txt", "v1");

    var vfs_v2: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_v2.deinit(std.testing.allocator);
    try vfs_v2.put(std.testing.allocator, "assets/ver.txt", "version_two");

    db.setEmbedSandbox(null, &vfs_v1);
    const embed_file = FileId.fromInt(41);
    const embed_src =
        \\pub const EMBED_LEN: usize = @embed_bytes("assets/ver.txt").len();
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

    // [3] Raising `setComptimeStepLimit` invalidates cached `E0501` and succeeds:
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

    // [1] `PureCallMemoCache` hit replays transitive `CompilerDb` `QueryKey` dependencies:
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

    // [2] `MemoHeader.has_overflowed_deps` forces conservative Red-Path verification past `MAX_DEPS_PER_MEMO`:
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

    // [3] `requestCancellation` propagates `error.Cancelled`, and loop UAF traps `E0506`:
    const uaf_file = FileId.fromInt(45);
    const uaf_src =
        \\pub fn loop_uaf() -> i64 {
        \\    var outer_val: i64 = 10;
        \\    var saved_ptr: *i64 = &raw outer_val;
        \\    var iter: i64 = 0;
        \\    while iter < 2 {
        \\        let inner_val: i64 = 99;
        \\        if iter == 0 {
        \\            saved_ptr = &raw inner_val;
        \\        } else {
        \\            return comptime { saved_ptr.* };
        \\        }
        \\        iter = iter + 1;
        \\    }
        \\    return comptime { saved_ptr.* };
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

// ----- Phase 7.6: Expr-Fn, Slash, Tests & `.cxi` Firewall -----

test "test_phase76_expr_fn_positional_slash_test_bench_items_and_cxi_visibility_firewall" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] Expression-bodied `pub fn f() -> i32 = expr;` RHS edit preserves `signature_fingerprint`:
    const expr_fn_file = FileId.fromInt(70);
    const expr_v1 =
        \\pub fn double_inc(val: i32) -> i32 = val * 2 + 1;
    ;
    _ = try db.setInput(expr_fn_file, expr_v1, .low);
    const expr_tree_v1 = try db.extractItemTree(expr_fn_file);
    try std.testing.expectEqual(@as(usize, 1), expr_tree_v1.entries.len);
    const expr_sig_v1 = expr_tree_v1.entries[0].signature_fingerprint;
    const expr_body_v1 = expr_tree_v1.entries[0].body_fingerprint;

    const expr_v2 =
        \\pub fn double_inc(val: i32) -> i32 = (val + val) + 99;
    ;
    _ = try db.setInput(expr_fn_file, expr_v2, .low);
    const expr_tree_v2 = try db.extractItemTree(expr_fn_file);
    try std.testing.expect(Fingerprint128.eql(expr_sig_v1, expr_tree_v2.entries[0].signature_fingerprint));
    try std.testing.expect(!Fingerprint128.eql(expr_body_v1, expr_tree_v2.entries[0].body_fingerprint));

    // [2] Positional-only `/` parameter rename (`dst` -> `target`) preserves `signature_fingerprint` & `DefSignature`:
    const slash_file = FileId.fromInt(71);
    const slash_v1 =
        \\pub fn copy_slot(dst: i32, /, scale: i32 = 1) -> i32 {
        \\    return dst * scale;
        \\}
    ;
    const slash_rev1 = try db.setInput(slash_file, slash_v1, .low);
    const slash_tree_v1 = try db.extractItemTree(slash_file);
    const def_copy_slot = slash_tree_v1.entries[0].def_id;
    const slash_sig_v1 = slash_tree_v1.entries[0].signature_fingerprint;
    const slash_def_sig_v1 = (try db.getDefSignature(def_copy_slot)).signature_fingerprint;

    const slash_v2 =
        \\pub fn copy_slot(target: i32, /, scale: i32 = 1) -> i32 {
        \\    return target * scale;
        \\}
    ;
    const slash_rev2 = try db.setInput(slash_file, slash_v2, .low);
    try std.testing.expect(slash_rev2.isAfter(slash_rev1));
    const slash_tree_v2 = try db.extractItemTree(slash_file);
    try std.testing.expect(Fingerprint128.eql(slash_sig_v1, slash_tree_v2.entries[0].signature_fingerprint));
    const slash_def_sig_v2 = (try db.getDefSignature(def_copy_slot)).signature_fingerprint;
    try std.testing.expect(Fingerprint128.eql(slash_def_sig_v1, slash_def_sig_v2));

    // [3] Multiple `test "…"` / `bench "…"` blocks have distinct names and `setIncludeTests(false)` skips them:
    const tb_file = FileId.fromInt(72);
    const tb_src =
        \\pub fn helper_fn() -> i32 { return 7; }
        \\test "alpha case" { let _ = helper_fn(); }
        \\test "beta case" { let _ = helper_fn(); }
        \\bench "throughput loop" (bencher: &var Bencher) { let _ = bencher; }
    ;
    _ = try db.setInput(tb_file, tb_src, .low);
    const tb_tree_with = try db.extractItemTree(tb_file);
    try std.testing.expectEqual(@as(usize, 4), tb_tree_with.entries.len);
    try std.testing.expectEqualStrings("\"alpha case\"", tb_tree_with.entries[1].name_text);
    try std.testing.expectEqualStrings("\"beta case\"", tb_tree_with.entries[2].name_text);
    try std.testing.expectEqualStrings("\"throughput loop\"", tb_tree_with.entries[3].name_text);

    const parse_execs_before = db.telemetry.countExecutions(.parse_cst);
    db.setIncludeTests(false);
    const tb_tree_without = try db.extractItemTree(tb_file);
    try std.testing.expectEqual(@as(usize, 1), tb_tree_without.entries.len);
    try std.testing.expectEqual(parse_execs_before, db.telemetry.countExecutions(.parse_cst));
    db.setIncludeTests(true);

    // [4] 4-tier `Visibility` `.cxi` `public_interface_fingerprint` shields external packages from `pub(pkg)` edits:
    const vis_file = FileId.fromInt(73);
    const vis_v1 =
        \\fn priv_fn() -> i32 { return 1; }
        \\pub(super) fn sup_fn() -> i32 { return 2; }
        \\pub(pkg) fn pkg_fn(val: i32) -> i32 { return val; }
        \\pub fn exported_api(val: i32) -> i32 { return val + 1; }
    ;
    _ = try db.setInput(vis_file, vis_v1, .low);
    const vis_tree_v1 = try db.extractItemTree(vis_file);
    try std.testing.expectEqual(Visibility.private, vis_tree_v1.entries[0].visibility);
    try std.testing.expectEqual(Visibility.pub_super, vis_tree_v1.entries[1].visibility);
    try std.testing.expectEqual(Visibility.pub_pkg, vis_tree_v1.entries[2].visibility);
    try std.testing.expectEqual(Visibility.public, vis_tree_v1.entries[3].visibility);

    const vis_sigs_v1 = try db.resolveSignatures(vis_file);
    try std.testing.expectEqual(@as(u32, 1), vis_sigs_v1.public_item_count);
    const cxi_fp_v1 = vis_sigs_v1.public_interface_fingerprint;
    const intra_fp_v1 = vis_sigs_v1.signatures_fingerprint;

    const vis_v2 =
        \\fn priv_fn() -> i64 { return 10; }
        \\pub(super) fn sup_fn(extra: i32) -> i32 { return extra; }
        \\pub(pkg) fn pkg_fn(val: i64, scale: i64) -> i64 { return val * scale; }
        \\pub fn exported_api(val: i32) -> i32 { return val + 1; }
    ;
    _ = try db.setInput(vis_file, vis_v2, .low);
    const vis_sigs_v2 = try db.resolveSignatures(vis_file);
    try std.testing.expect(Fingerprint128.eql(cxi_fp_v1, vis_sigs_v2.public_interface_fingerprint));
    try std.testing.expect(!Fingerprint128.eql(intra_fp_v1, vis_sigs_v2.signatures_fingerprint));
}

test "test_stage4_cxi_firewall_impl_const_inline_mod_slash_underscore_and_cfg_target" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] Positional-only `src: &[u8], /` <-> `_: &[u8], /` preserves `signature_fingerprint`:
    const slash_u_file = FileId.fromInt(74);
    const slash_named =
        \\pub fn scan_bytes(src: &[u8], /) -> usize {
        \\    return src.len();
        \\}
    ;
    _ = try db.setInput(slash_u_file, slash_named, .low);
    const tree_named = try db.extractItemTree(slash_u_file);
    const sig_named = tree_named.entries[0].signature_fingerprint;
    const def_sig_named = (try db.getDefSignature(tree_named.entries[0].def_id)).signature_fingerprint;

    const slash_wild =
        \\pub fn scan_bytes(_: &[u8], /) -> usize {
        \\    return 0;
        \\}
    ;
    _ = try db.setInput(slash_u_file, slash_wild, .low);
    const tree_wild = try db.extractItemTree(slash_u_file);
    try std.testing.expect(Fingerprint128.eql(sig_named, tree_wild.entries[0].signature_fingerprint));
    const def_sig_wild = (try db.getDefSignature(tree_wild.entries[0].def_id)).signature_fingerprint;
    try std.testing.expect(Fingerprint128.eql(def_sig_named, def_sig_wild));

    // [2] `.cxi` `public_interface_fingerprint`: `pub const` value, `impl` public vs private methods,
    //     trait `impl` visibility, and inline `pub mod` child visibility filtering:
    const cxi_file = FileId.fromInt(75);
    const cxi_base =
        \\pub const MAX_PACKET: usize = 512;
        \\pub(pkg) const INTERNAL_CAP: usize = 16;
        \\pub trait Codec {
        \\    fn tag(&self) -> u32;
        \\}
        \\pub(pkg) trait InternalHook {
        \\    fn hook(&self) -> u32;
        \\}
        \\pub struct Packet {
        \\    pub id: u32,
        \\}
        \\impl Packet {
        \\    pub fn public_id(&self) -> u32 { return self.id; }
        \\    pub(pkg) fn pkg_helper(&self, extra: u32) -> u32 { return self.id + extra; }
        \\    fn priv_helper(&self) -> u32 { return 1; }
        \\}
        \\impl InternalHook for Packet {
        \\    fn hook(&self) -> u32 { return 10; }
        \\}
        \\pub mod nested_pub {
        \\    pub fn exported_nested() -> i32 { return 1; }
        \\    pub(pkg) fn hidden_pkg_nested(arg: i32) -> i32 { return arg; }
        \\}
    ;
    _ = try db.setInput(cxi_file, cxi_base, .low);
    const cxi_fp_base = (try db.resolveSignatures(cxi_file)).public_interface_fingerprint;

    // [2a] Editing `pub(pkg)` const, `pub(pkg)` / private `impl` methods, `pub(pkg)` trait `impl`,
    //      and `pub(pkg)` item inside inline `pub mod` MUST NOT change `public_interface_fingerprint`:
    const cxi_priv_edits =
        \\pub const MAX_PACKET: usize = 512;
        \\pub(pkg) const INTERNAL_CAP: usize = 64;
        \\pub trait Codec {
        \\    fn tag(&self) -> u32;
        \\}
        \\pub(pkg) trait InternalHook {
        \\    fn hook(&self) -> u32;
        \\}
        \\pub struct Packet {
        \\    pub id: u32,
        \\}
        \\impl Packet {
        \\    pub fn public_id(&self) -> u32 { return self.id + 99; }
        \\    pub(pkg) fn pkg_helper(&self, extra: u64, scale: u64) -> u64 { return extra * scale; }
        \\    fn priv_helper(&self, delta: u32) -> u32 { return delta; }
        \\    fn extra_priv(&self) -> bool { return true; }
        \\}
        \\impl InternalHook for Packet {
        \\    fn hook(&self) -> u32 { return 999; }
        \\}
        \\pub mod nested_pub {
        \\    pub fn exported_nested() -> i32 { return 2; }
        \\    pub(pkg) fn hidden_pkg_nested(arg: i64, flag: bool) -> i64 {
        \\        let _ = flag;
        \\        return arg;
        \\    }
        \\}
    ;
    _ = try db.setInput(cxi_file, cxi_priv_edits, .low);
    const cxi_fp_after_priv = (try db.resolveSignatures(cxi_file)).public_interface_fingerprint;
    try std.testing.expect(Fingerprint128.eql(cxi_fp_base, cxi_fp_after_priv));

    // [2b] Changing `pub const MAX_PACKET` value invalidates `public_interface_fingerprint`:
    const cxi_const_edit =
        \\pub const MAX_PACKET: usize = 1024;
        \\pub(pkg) const INTERNAL_CAP: usize = 64;
        \\pub trait Codec {
        \\    fn tag(&self) -> u32;
        \\}
        \\pub(pkg) trait InternalHook {
        \\    fn hook(&self) -> u32;
        \\}
        \\pub struct Packet {
        \\    pub id: u32,
        \\}
        \\impl Packet {
        \\    pub fn public_id(&self) -> u32 { return self.id; }
        \\    pub(pkg) fn pkg_helper(&self, extra: u64, scale: u64) -> u64 { return extra * scale; }
        \\}
        \\pub mod nested_pub {
        \\    pub fn exported_nested() -> i32 { return 2; }
        \\}
    ;
    _ = try db.setInput(cxi_file, cxi_const_edit, .low);
    const cxi_fp_const_edit = (try db.resolveSignatures(cxi_file)).public_interface_fingerprint;
    try std.testing.expect(!Fingerprint128.eql(cxi_fp_base, cxi_fp_const_edit));

    // [2c] Changing a `pub fn` signature inside `impl Packet` or adding `impl Codec for Packet` invalidates `.cxi`:
    const cxi_impl_pub_edit =
        \\pub const MAX_PACKET: usize = 1024;
        \\pub(pkg) const INTERNAL_CAP: usize = 64;
        \\pub trait Codec {
        \\    fn tag(&self) -> u32;
        \\}
        \\pub(pkg) trait InternalHook {
        \\    fn hook(&self) -> u32;
        \\}
        \\pub struct Packet {
        \\    pub id: u32,
        \\}
        \\impl Packet {
        \\    pub fn public_id(&self) -> u64 { return self.id as u64; }
        \\}
        \\impl Codec for Packet {
        \\    fn tag(&self) -> u32 { return self.id; }
        \\}
        \\pub mod nested_pub {
        \\    pub fn exported_nested() -> i32 { return 2; }
        \\}
    ;
    _ = try db.setInput(cxi_file, cxi_impl_pub_edit, .low);
    const cxi_fp_impl_edit = (try db.resolveSignatures(cxi_file)).public_interface_fingerprint;
    try std.testing.expect(!Fingerprint128.eql(cxi_fp_const_edit, cxi_fp_impl_edit));

    // [3] `@cfg` target OS & `cfg.test_mode` synchronization across `CompilerDb`:
    const cfg_file = FileId.fromInt(76);
    const cfg_src =
        \\@cfg(os == "linux")
        \\pub fn linux_only() -> i32 { return 11; }
        \\@cfg(test_mode)
        \\pub fn test_mode_only() -> i32 {
        \\    @compile_error("must be pruned when is_including_tests is false");
        \\    return 0;
        \\}
        \\pub fn portable_fn() -> i32 { return 7; }
    ;
    db.setIncludeTests(false);
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_WINDOWS);
    _ = try db.setInput(cfg_file, cfg_src, .low);
    const win_sigs = try db.resolveSignatures(cfg_file);
    try std.testing.expectEqual(@as(u32, 0), win_sigs.error_count);
    try std.testing.expectEqual(@as(u32, 1), win_sigs.public_item_count);

    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX);
    const linux_sigs = try db.resolveSignatures(cfg_file);
    try std.testing.expectEqual(@as(u32, 0), linux_sigs.error_count);
    try std.testing.expectEqual(@as(u32, 2), linux_sigs.public_item_count);
    try std.testing.expect(!Fingerprint128.eql(win_sigs.public_interface_fingerprint, linux_sigs.public_interface_fingerprint));
    db.setIncludeTests(true);
}

// ------- Phase 8 ABI Cutoff, Extern ItemTree & CImport --------

test "test_phase8_target_abi_cutoff_flattened_extern_item_tree_and_c_import_lru_cache" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] 11-target `TargetSpec.abi` invalidates `CONFIG_KEY_TARGET_LAYOUT`, `resolveSignatures`, and `typecheckBody`:
    const abi_file = FileId.fromInt(90);
    _ = try db.setInput(abi_file, "pub fn abi_probe(val: i32) -> i32 { return val + 1; }\n", .low);
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
    const rev_gnu = db.current_revision;
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
    try std.testing.expectEqual(rev_gnu, db.current_revision);

    const gnu_sigs = try db.resolveSignatures(abi_file);
    const abi_def0 = (try db.extractItemTree(abi_file)).entries[0].def_id;
    const gnu_body = try db.typecheckBody(abi_def0);

    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_MUSL);
    try std.testing.expect(db.current_revision.isAfter(rev_gnu));
    const musl_sigs = try db.resolveSignatures(abi_file);
    const musl_body = try db.typecheckBody(abi_def0);
    try std.testing.expect(!Fingerprint128.eql(gnu_sigs.signatures_fingerprint, musl_sigs.signatures_fingerprint));
    try std.testing.expect(!Fingerprint128.eql(
        gnu_sigs.public_interface_fingerprint,
        musl_sigs.public_interface_fingerprint,
    ));
    try std.testing.expect(!Fingerprint128.eql(gnu_body.typed_fingerprint, musl_body.typed_fingerprint));

    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_WINDOWS_MSVC);
    const msvc_sigs = try db.resolveSignatures(abi_file);
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_WINDOWS_GNU);
    const mingw_sigs = try db.resolveSignatures(abi_file);
    try std.testing.expect(!Fingerprint128.eql(msvc_sigs.signatures_fingerprint, mingw_sigs.signatures_fingerprint));

    // [2] Flattened `extern "C" { … }` & standalone `extern static` `ItemTree` Early Cutoff + `comptime` collision guard:
    const ffi_file = FileId.fromInt(91);
    const ffi_src_v1 =
        \\comptime {
        \\    let check_val: i32 = 1;
        \\}
        \\pub extern "C" {
        \\    fn c_open(path: *const u8, flags: i32) -> i32;
        \\    static mut ERRNO: i32;
        \\}
        \\@thread_local
        \\extern "C" static LAST_CODE: u32;
    ;
    const rev_ffi_1 = try db.setInput(ffi_file, ffi_src_v1, .low);
    const tree_ffi_1 = try db.extractItemTree(ffi_file);
    try std.testing.expectEqual(@as(usize, 4), tree_ffi_1.entries.len);
    try std.testing.expectEqual(ItemKind.extern_block, tree_ffi_1.entries[0].kind);
    try std.testing.expectEqual(ItemKind.fn_decl, tree_ffi_1.entries[1].kind);
    try std.testing.expectEqualStrings("c_open", tree_ffi_1.entries[1].name_text);
    try std.testing.expectEqual(Visibility.public, tree_ffi_1.entries[1].visibility);
    try std.testing.expectEqual(ItemKind.extern_static, tree_ffi_1.entries[2].kind);
    try std.testing.expectEqualStrings("ERRNO", tree_ffi_1.entries[2].name_text);
    try std.testing.expectEqual(Visibility.public, tree_ffi_1.entries[2].visibility);
    try std.testing.expectEqual(ItemKind.extern_static, tree_ffi_1.entries[3].kind);
    try std.testing.expectEqualStrings("LAST_CODE", tree_ffi_1.entries[3].name_text);

    const def_open = tree_ffi_1.entries[1].def_id;
    const def_errno = tree_ffi_1.entries[2].def_id;
    const def_tls = tree_ffi_1.entries[3].def_id;
    const open_sig_1 = try db.getItemTreeSigProj(def_open);
    const errno_sig_1 = try db.getItemTreeSigProj(def_errno);
    const tls_sig_1 = try db.getItemTreeSigProj(def_tls);

    const ffi_src_v2 =
        \\comptime {
        \\    let check_val: i32 = 1;
        \\}
        \\pub extern "C" {
        \\    fn c_open(path: *const u8, flags: i32, mode: u32) -> i32;
        \\    static mut ERRNO: i32;
        \\}
        \\@thread_local
        \\extern "C" static LAST_CODE: u32;
    ;
    const rev_ffi_2 = try db.setInput(ffi_file, ffi_src_v2, .low);
    try std.testing.expect(rev_ffi_2.isAfter(rev_ffi_1));
    const open_sig_2 = try db.getItemTreeSigProj(def_open);
    const errno_sig_2 = try db.getItemTreeSigProj(def_errno);
    const tls_sig_2 = try db.getItemTreeSigProj(def_tls);
    try std.testing.expect(!Fingerprint128.eql(open_sig_1, open_sig_2));
    try std.testing.expect(Fingerprint128.eql(errno_sig_1, errno_sig_2));
    try std.testing.expect(Fingerprint128.eql(tls_sig_1, tls_sig_2));
    try std.testing.expectEqual(
        rev_ffi_1,
        db.getMemoHeader(QueryKey.forDef(.item_tree_sig_proj, def_errno)).?.changed_at,
    );

    // [3] Bounded `CImportCache` (`128` entries AND `16 MiB` total bytes with explicit LRU eviction):
    try std.testing.expectEqual(@as(usize, 0), db.c_import_cache.nodes.capacity);
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
    const defines_a = [_][]const u8{"_GNU_SOURCE=1"};
    const defines_b = [_][]const u8{"_POSIX_C_SOURCE=200809L"};
    const key_gnu_a = db.computeCImportKey("int puts(const char*);", &defines_a);
    const key_gnu_b = db.computeCImportKey("int puts(const char*);", &defines_b);
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_MUSL);
    const key_musl_a = db.computeCImportKey("int puts(const char*);", &defines_a);
    try std.testing.expect(!Fingerprint128.eql(key_gnu_a, key_gnu_b));
    try std.testing.expect(!Fingerprint128.eql(key_gnu_a, key_musl_a));

    const vfid_first = try db.storeCImportTranslation(
        "int puts(const char*);",
        &defines_a,
        "pub extern \"C\" fn puts(msg: *const i8) -> i32;\n",
        null,
    );
    try std.testing.expectEqual(Durability.medium, db.source_inputs.get(vfid_first.asInt()).?.durability);
    const cached_hit = db.lookupCImportCache("int puts(const char*);", &defines_a).?;
    try std.testing.expectEqual(vfid_first, cached_hit.virtual_file_id);
    try std.testing.expectEqual(Durability.medium, cached_hit.durability);

    // Test 128-entry LRU cap (touch slot 0 so slot 1 becomes LRU when inserting entry 128):
    var local_cache = CImportCache.init();
    defer local_cache.deinit(std.testing.allocator);
    var entry_i: usize = 0;
    while (entry_i < MAX_C_IMPORT_CACHE_ENTRIES) : (entry_i += 1) {
        var hdr_buf: [32]u8 = undefined;
        const hdr_txt = try std.fmt.bufPrint(&hdr_buf, "int fn_{d}(void);", .{entry_i});
        const cache_key = CImportCache.computeKey(hdr_txt, codegen_abi.TargetSpec.X86_64_LINUX_GNU, &.{}, &.{});
        _ = try local_cache.put(std.testing.allocator, cache_key, hdr_txt, FileId.fromInt(@intCast(1000 + entry_i)));
    }
    try std.testing.expectEqual(MAX_C_IMPORT_CACHE_ENTRIES, local_cache.entry_count);
    const key_0 = CImportCache.computeKey("int fn_0(void);", codegen_abi.TargetSpec.X86_64_LINUX_GNU, &.{}, &.{});
    const key_1 = CImportCache.computeKey("int fn_1(void);", codegen_abi.TargetSpec.X86_64_LINUX_GNU, &.{}, &.{});
    try std.testing.expect(local_cache.get(key_0) != null);
    const key_128 = CImportCache.computeKey("int fn_128(void);", codegen_abi.TargetSpec.X86_64_LINUX_GNU, &.{}, &.{});
    _ = try local_cache.put(std.testing.allocator, key_128, "int fn_128(void);", FileId.fromInt(2200));
    try std.testing.expectEqual(MAX_C_IMPORT_CACHE_ENTRIES, local_cache.entry_count);
    try std.testing.expect(local_cache.peek(key_0) != null);
    try std.testing.expect(local_cache.peek(key_1) == null);

    // Test 16 MiB byte-cap LRU eviction (five 4 MiB chunks -> at most four fit in 16 MiB):
    local_cache.clear(std.testing.allocator);
    const four_mib_chunk = try std.testing.allocator.alloc(u8, 4 * 1024 * 1024);
    defer std.testing.allocator.free(four_mib_chunk);
    @memset(four_mib_chunk, 'x');
    var chunk_keys: [5]Fingerprint128 = undefined;
    var chunk_i: usize = 0;
    while (chunk_i < 5) : (chunk_i += 1) {
        var name_buf: [24]u8 = undefined;
        const hdr_name = try std.fmt.bufPrint(&name_buf, "big_{d}.h", .{chunk_i});
        chunk_keys[chunk_i] = CImportCache.computeKey(
            hdr_name,
            codegen_abi.TargetSpec.X86_64_LINUX_GNU,
            &.{},
            &.{},
        );
        _ = try local_cache.put(
            std.testing.allocator,
            chunk_keys[chunk_i],
            four_mib_chunk,
            FileId.fromInt(@intCast(3000 + chunk_i)),
        );
    }
    try std.testing.expect(local_cache.total_bytes <= MAX_C_IMPORT_CACHE_BYTES);
    try std.testing.expectEqual(@as(usize, 4), local_cache.entry_count);
    try std.testing.expect(local_cache.peek(chunk_keys[0]) == null);
    try std.testing.expect(local_cache.peek(chunk_keys[4]) != null);
}

// ---------- Target FFI Refresh & CImport LRU Cleanup ----------

test "test_c_import_target_spec_ffi_refresh_include_dirs_and_lru_eviction_cleanup" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] `setTargetSpec` refreshes `cx.ffi.{c_char, c_long, c_ulong}` across targets:
    const ffi_file = FileId.fromInt(90);
    const ffi_src =
        \\use cx.ffi.{c_char, c_long, c_ulong};
        \\pub fn read_c_long(val: c_long) -> c_long { return val; }
        \\pub fn read_c_char(ch: c_char) -> c_char { return ch; }
    ;
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_WINDOWS_MSVC);
    _ = try db.setInput(ffi_file, ffi_src, .low);
    const ffi_tree = try db.extractItemTree(ffi_file);
    var long_def = DefId.NONE;
    var char_def = DefId.NONE;
    for (ffi_tree.entries) |item_entry| {
        if (std.mem.eql(u8, item_entry.name_text, "read_c_long")) long_def = item_entry.def_id;
        if (std.mem.eql(u8, item_entry.name_text, "read_c_char")) char_def = item_entry.def_id;
    }
    try std.testing.expectEqual(@as(u32, 0), (try db.resolveSignatures(ffi_file)).error_count);
    const win_sig = try db.getDefSignature(long_def);
    try std.testing.expectEqual(TypeId.i32_ty, db.type_pool.getFnSignatureView(win_sig.type_id).?.ret_ty);

    db.setTargetSpec(codegen_abi.TargetSpec.AARCH64_LINUX_GNU);
    try std.testing.expectEqual(@as(u32, 0), (try db.resolveSignatures(ffi_file)).error_count);
    const aarch_sig = try db.getDefSignature(long_def);
    const aarch_char_sig = try db.getDefSignature(char_def);
    try std.testing.expectEqual(TypeId.i64_ty, db.type_pool.getFnSignatureView(aarch_sig.type_id).?.ret_ty);
    try std.testing.expectEqual(TypeId.u8_ty, db.type_pool.getFnSignatureView(aarch_char_sig.type_id).?.ret_ty);

    // [2] `c_import_include_dirs` differentiates `CImportCache` keys:
    const inc_dir_a = [_][]const u8{"include/v1"};
    const inc_dir_b = [_][]const u8{"include/v2"};
    try db.setCImportConfig(&.{}, &inc_dir_a);
    const key_inc_a = db.computeCImportKey("#include \"cfg.h\"\n", &.{});
    try db.setCImportConfig(&.{}, &inc_dir_b);
    const key_inc_b = db.computeCImportKey("#include \"cfg.h\"\n", &.{});
    try std.testing.expect(!Fingerprint128.eql(key_inc_a, key_inc_b));

    // [3] Mid-query `@c_import` does NOT bump `current_revision` or clobber durability tiers:
    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(std.testing.allocator);
    try vfs_map.put(std.testing.allocator, "mid_q.h", "int mid_fn(int x);\n");
    db.setEmbedSandbox(null, &vfs_map);

    const caller_file = FileId.fromInt(91);
    _ = try db.setInput(
        caller_file,
        "const c_mod = @c_import(\"mid_q.h\");\npub fn call_mid(val: i32) -> i32 { return unsafe { c_mod.mid_fn(val) }; }\n",
        .low,
    );
    const rev_before_query = db.current_revision;
    const med_changed_before = db.last_changed_by_durability[@backingInt(Durability.medium)];
    const caller_sigs = try db.resolveSignatures(caller_file);
    try std.testing.expectEqual(@as(u32, 0), caller_sigs.error_count);
    try std.testing.expectEqual(rev_before_query, db.current_revision);
    try std.testing.expectEqual(med_changed_before, db.last_changed_by_durability[@backingInt(Durability.medium)]);

    // [4] LRU eviction purges virtual `FileId` artifacts and memos from `CompilerDb`:
    const evicted_cand_fid = try db.storeCImportTranslation(
        "int evict_me(void);",
        &.{},
        "pub extern \"C\" fn evict_me() -> i32;\n",
        null,
    );
    _ = try db.resolveSignatures(evicted_cand_fid);
    try std.testing.expect(db.source_inputs.contains(evicted_cand_fid.asInt()));
    try std.testing.expect(db.parsed_artifacts.contains(evicted_cand_fid.asInt()));
    try std.testing.expect(db.memos.contains(QueryKey.forFile(.resolve_signatures, evicted_cand_fid).asU64()));

    var fill_idx: usize = 0;
    while (fill_idx < MAX_C_IMPORT_CACHE_ENTRIES) : (fill_idx += 1) {
        var hdr_buf: [48]u8 = undefined;
        var cx_buf: [64]u8 = undefined;
        const hdr_slice = try std.fmt.bufPrint(&hdr_buf, "int filler_{d}(void);", .{fill_idx});
        const cx_slice = try std.fmt.bufPrint(&cx_buf, "pub extern \"C\" fn filler_{d}() -> i32;\n", .{fill_idx});
        _ = try db.storeCImportTranslation(hdr_slice, &.{}, cx_slice, null);
    }
    try std.testing.expect(!db.source_inputs.contains(evicted_cand_fid.asInt()));
    try std.testing.expect(!db.parsed_artifacts.contains(evicted_cand_fid.asInt()));
    try std.testing.expect(!db.resolved_signatures.contains(evicted_cand_fid.asInt()));
    try std.testing.expect(!db.memos.contains(QueryKey.forFile(.resolve_signatures, evicted_cand_fid).asU64()));
}

// ----------- ItemTree Rehash Safety in OptimizeMir ------------

test "test_optimize_mir_module_rehashes_item_trees_across_16_modules_safely" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // Register a root package (`pkg_root`) with 15 child modules (`16` unextracted files total):
    const pkg_root_fid = FileId.fromInt(200);
    var root_src_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer root_src_buf.deinit(std.testing.allocator);

    var mod_i: usize = 0;
    while (mod_i < 15) : (mod_i += 1) {
        var mod_decl_line: [32]u8 = undefined;
        const decl_txt = try std.fmt.bufPrint(&mod_decl_line, "pub mod sub_{d};\n", .{mod_i});
        try root_src_buf.appendSlice(std.testing.allocator, decl_txt);

        const child_fid = FileId.fromInt(@intCast(201 + mod_i));
        var child_src_line: [96]u8 = undefined;
        const child_src = try std.fmt.bufPrint(
            &child_src_line,
            "pub fn leaf_{d}(val: i32) -> i32 = val + {d};\n",
            .{ mod_i, mod_i },
        );
        _ = try db.setInput(child_fid, child_src, .high);

        var mod_name_buf: [16]u8 = undefined;
        const mod_name = try std.fmt.bufPrint(&mod_name_buf, "sub_{d}", .{mod_i});
        try db.bindExternalModule(pkg_root_fid, mod_name, child_fid);
    }
    _ = try db.setInput(pkg_root_fid, root_src_buf.items, .high);
    try db.registerRootModule("wide_pkg", pkg_root_fid);

    // Register caller `app_fid` while `db.item_trees` is still completely empty (`count == 0`):
    const app_fid = FileId.fromInt(199);
    const app_src =
        \\use wide_pkg.sub_0.leaf_0;
        \\use wide_pkg.sub_14.leaf_14;
        \\pub fn entry_calc(seed: i32) -> i32 {
        \\    return leaf_0(seed) + leaf_14(seed);
        \\}
    ;
    _ = try db.setInput(app_fid, app_src, .low);
    try std.testing.expectEqual(@as(u32, 0), db.item_trees.count());

    // `optimizeMirModule` resolves `wide_pkg` (`0 -> 8 -> 16 -> 32` `item_trees` growth) without dangling pointers:
    const opt_res = try db.optimizeMirModule(app_fid, true);
    try std.testing.expect(db.item_trees.count() >= 17);
    try std.testing.expectEqual(@as(usize, 1), opt_res.bodies.items.len);
}

// -------- Transitive CImport Invalidation & Cycle Mask --------

test "test_c_import_transitive_include_mutation_invalidates_cache_and_signatures" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] Mutating a transitive `#include "sub.h"` / `"leaf.h"` invalidates `CImportCache`, `evalComptimeDef`, and `typecheckBody`:
    const root_h_src = "#include \"sub.h\"\nint root_only(void);\n";
    const sub_h_v1 = "#include \"leaf.h\"\nint sub_step(int x);\n";
    const leaf_h_v1 = "#define LEAF_MAGIC 11\n";

    var vfs_headers: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_headers.deinit(std.testing.allocator);
    try vfs_headers.put(std.testing.allocator, "root.h", root_h_src);
    try vfs_headers.put(std.testing.allocator, "sub.h", sub_h_v1);
    try vfs_headers.put(std.testing.allocator, "leaf.h", leaf_h_v1);
    db.setEmbedSandbox(null, &vfs_headers);

    const caller_a_fid = FileId.fromInt(240);
    const caller_b_fid = FileId.fromInt(241);
    const caller_src =
        \\const c_hdr = @c_import("root.h");
        \\pub const COMPUTED_MAGIC: i64 = c_hdr.LEAF_MAGIC + 1;
        \\pub fn invoke_sub(arg: i32) -> i32 {
        \\    return unsafe { c_hdr.sub_step(arg) };
        \\}
    ;
    _ = try db.setInput(caller_a_fid, caller_src, .low);
    _ = try db.setInput(caller_b_fid, caller_src, .low);

    const tree_a = try db.extractItemTree(caller_a_fid);
    const tree_b = try db.extractItemTree(caller_b_fid);
    const def_magic_a = tree_a.entries[1].def_id;
    const def_invoke_a = tree_a.entries[2].def_id;
    const def_magic_b = tree_b.entries[1].def_id;
    const def_invoke_b = tree_b.entries[2].def_id;

    // Cold translation on `caller_a`, followed by `CImportCache` hit on `caller_b` (replaying transitive deps):
    try std.testing.expectEqual(@as(i128, 12), (try db.evalComptimeDef(def_magic_a)).value.int_val);
    try std.testing.expectEqual(@as(u32, 0), (try db.typecheckBody(def_invoke_a)).error_count);

    const hits_before_b = db.c_import_cache.hits;
    try std.testing.expectEqual(@as(i128, 12), (try db.evalComptimeDef(def_magic_b)).value.int_val);
    try std.testing.expectEqual(@as(u32, 0), (try db.typecheckBody(def_invoke_b)).error_count);
    try std.testing.expect(db.c_import_cache.hits > hits_before_b);

    // Mutate ONLY `"leaf.h"` and `"sub.h"` (`"root.h"` is byte-for-byte unchanged!) and advance revision via an unrelated file:
    try vfs_headers.put(std.testing.allocator, "leaf.h", "#define LEAF_MAGIC 99\n");
    try vfs_headers.put(std.testing.allocator, "sub.h", "#include \"leaf.h\"\nint sub_step(int x, int extra);\n");
    try std.testing.expect(db.lookupCImportCache(root_h_src, &.{}) == null);

    const unrelated_fid = FileId.fromInt(242);
    _ = try db.setInput(unrelated_fid, "pub const UNRELATED: i32 = 1;\n", .low);

    // Both `caller_a` (cache miss on rev 1) and `caller_b` (cache hit on rev 1) MUST invalidate and observe v2:
    try std.testing.expectEqual(@as(i128, 100), (try db.evalComptimeDef(def_magic_a)).value.int_val);
    try std.testing.expect((try db.typecheckBody(def_invoke_a)).error_count >= 1);
    try std.testing.expectEqual(@as(i128, 100), (try db.evalComptimeDef(def_magic_b)).value.int_val);
    try std.testing.expect((try db.typecheckBody(def_invoke_b)).error_count >= 1);

    // [2] Verify `makeConservativeCycleSummary` preserves `INFERRED_THREAD_LOCAL_BIT` (`0x1000`) and `INFERRED_ASYNC_NON_SEND_BIT` (`0x2000`):
    const cycle_sum = CompilerDb.makeConservativeCycleSummary(&db, .NONE, .none);
    try std.testing.expectEqual(@as(u16, 0x3FFF), cycle_sum.direct_effects_bits);
    try std.testing.expectEqual(@as(u16, 0x3FFF), cycle_sum.inferred_effects_bits);
}

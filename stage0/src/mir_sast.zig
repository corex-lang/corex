//! CoreX Phase 6 `MIR` SAST Engine, Drop Elaboration & Capability Sandbox
//!
//! Implements Phase 6 (`PLAN.md` §2.6, `DR-06`, `DR-13` §4.4, `DR-17`, and `DR-20`) bottom-up Tarjan
//! SCC static vulnerability analysis, branch-aware destructor elaboration, and capability sandboxing:
//! - Exact binary-packed `EffectCapabilityMask` (`2B`), `FnContractScratchMask` (`2B`), 40-byte
//!   `FnRegionSummary` (`34` caller-observable bytes for Salsa Early Cutoff), and 12-byte CSR
//!   `WitnessCallEdge` call-chain witness reconstruction,
//! - Pass 1 `MovePath` trie (`20B` nodes, `MAX_MOVE_PATHS = 4096`) and `DenseBitSet` (`inline_words`
//!   for `<= 64` paths, `BumpArena` slice for `> 64` paths) with strong vs. weak `is_partial` updates,
//! - Intra-body symbolic region depths, transitive NLL loan horizons across zero-`<'a>` views, Pass 2
//!   typestate (`E0301`–`E0306`, `E0313`, `E0328`, `W0308`), and block-preserving `ElaborateDrops`,
//! - Pass 4 $O(V)$ 16-byte sign-biased `Intv` solver + demand-sliced sparse ABCD Pentagon (`< 1.5 MB`
//!   peak scratch RAM, `Fix-06A` lazy 1-hop join closure) for `.narrow()` (`E0406`) and BCE (`E0307`,
//!   `W0314`), followed by Pass 3 contract (`E0316`, `E0320`–`E0323`), `Fix-06B` (`W0329`), and
//!   `Fix-17` Gates A–F (`E0324`, `E0325`, `W0330`) verification.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const hir = @import("hir.zig");
const mir = @import("mir.zig");
const query_db = @import("query_db.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const TypeId = mem_foundation.TypeId;
const BumpArena = mem_foundation.BumpArena;
const TokenKind = syntax_arenas.TokenKind;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const Diagnostic = diagnostic.Diagnostic;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const Severity = diagnostic.Severity;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolKind = symbol_resolver.SymbolKind;
const SymbolRecord = symbol_resolver.SymbolRecord;
const SymbolTable = symbol_resolver.SymbolTable;
const CapabilityBits = symbol_resolver.CapabilityBits;
const InternPool = type_system.InternPool;
const OwnershipTier = type_system.OwnershipTier;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const FnPtrContractMask = type_system.FnPtrContractMask;
const ContextFieldLayout = type_system.ContextFieldLayout;
const DefId = query_db.DefId;
const LocalId = mir.LocalId;
const PlaceId = mir.PlaceId;
const MirBlockId = mir.MirBlockId;
const MirValueId = mir.MirValueId;
const EdgeId = mir.EdgeId;
const MirOp = mir.MirOp;
const BinOpKind = mir.BinOpKind;
const UnaryOpKind = mir.UnaryOpKind;
const AggregateKind = mir.AggregateKind;
const MirIntrinsicKind = mir.MirIntrinsicKind;
const ProjKind = mir.ProjKind;
const MirProjection = mir.MirProjection;
const MirInst = mir.MirInst;
const MirBody = mir.MirBody;
const MirModuleBundle = mir.MirModuleBundle;
const DominatorTree = mir.DominatorTree;

// ---------------------------------------- TYPES ----------------------------------------

// ----------------- Effect & Region Summaries ------------------

/// Canonical 16-bit inferred effect and OS capability bitset (`DR-17` §2.5, `@sizeOf == 2`).
pub const EffectCapabilityMask = packed struct(u16) {
    /// Filesystem read/write/metadata access (`bit 0`).
    fs: bool = false,
    /// Network socket/DNS access (`bit 1`).
    net: bool = false,
    /// Process environment variable access (`bit 2`).
    env: bool = false,
    /// Child process spawn/signal execution (`bit 3`).
    process: bool = false,
    /// Foreign function interface (`extern`) invocation (`bit 4`).
    ffi: bool = false,
    /// Raw pointer dereference, `union` field read, or inline `asm` (`bit 5`).
    unsafe_op: bool = false,
    /// Dynamic heap allocation via `Context.allocator` or `SystemAllocator` (`bit 6`).
    alloc: bool = false,
    /// Residual unrecoverable trap / panic path (`bit 7`).
    may_panic: bool = false,
    /// Wall-clock or monotonic timer access (`bit 8`).
    clock: bool = false,
    /// OS cryptographic/non-deterministic entropy source (`bit 9`).
    entropy: bool = false,
    /// Blocking synchronization primitive or `SystemAllocator` lock contention (`bit 10`).
    blocking_sync: bool = false,
    /// Unannotated indirect function pointer or `dyn Trait` call (`bit 11`).
    indirect_opaque: bool = false,
    /// Reserved zero bits keeping `EffectCapabilityMask` at `16` bits.
    _reserved: u4 = 0,

    /// Empty pure effect mask (`0x0000`).
    pub const EMPTY: EffectCapabilityMask = .{};
    /// Core OS sandbox bits (`fs | net | env | process | ffi | unsafe_op` = `0x003F`).
    pub const CORE_SANDBOX_BITS: u16 = 0x003F;
    /// Lockfile & hermetic `comptime` capability bits (`CORE_SANDBOX_BITS | clock | entropy` = `0x033F`).
    pub const LOCKFILE_CAP_BITS: u16 = 0x033F;
    /// Foreign function interface and `unsafe` capability bits (`ffi | unsafe_op` = `0x0030`).
    pub const FFI_UNSAFE_BITS: u16 = 0x0030;
    /// Blocking I/O and synchronization bits (`fs | net | process | blocking_sync`).
    pub const BLOCKING_BITS: u16 = (1 << 0) | (1 << 1) | (1 << 3) | (1 << 10);
    /// Dynamic heap allocation bit (`1 << 6`).
    pub const ALLOC_BIT: u16 = 1 << 6;
    /// Residual trap / panic bit (`1 << 7`).
    pub const MAY_PANIC_BIT: u16 = 1 << 7;
    /// Unannotated indirect call bit (`1 << 11`).
    pub const INDIRECT_OPAQUE_BIT: u16 = 1 << 11;

    comptime {
        std.debug.assert(@sizeOf(EffectCapabilityMask) == 2);
        std.debug.assert(@bitSizeOf(EffectCapabilityMask) == 16);
    }

    /// Represents `self` as a raw 16-bit unsigned integer.
    pub inline fn asBits(self: EffectCapabilityMask) u16 {
        return @bitCast(self);
    }

    /// Constructs an `EffectCapabilityMask` from raw 16-bit integer `raw_bits`.
    pub inline fn fromBits(raw_bits: u16) EffectCapabilityMask {
        return @bitCast(raw_bits & 0x0FFF);
    }

    /// Returns the bitwise union (`self | other`).
    pub inline fn unionWith(self: EffectCapabilityMask, other: EffectCapabilityMask) EffectCapabilityMask {
        return fromBits(self.asBits() | other.asBits());
    }

    /// Clears all bits present in `clear_bits`.
    pub inline fn withoutBits(self: EffectCapabilityMask, clear_bits: u16) EffectCapabilityMask {
        return fromBits(self.asBits() & ~clear_bits);
    }

    /// Returns `true` if `(self.asBits() & mask_bits) != 0`.
    pub inline fn hasAnyBits(self: EffectCapabilityMask, mask_bits: u16) bool {
        return (self.asBits() & mask_bits) != 0;
    }

    /// Returns `true` when zero capability or effect bits are set.
    pub inline fn isEmpty(self: EffectCapabilityMask) bool {
        return self.asBits() == 0;
    }
};

/// 16-bit contract & `Context.scratch[0..2]` ping-pong summary mask (`DR-17` §2.5, `@sizeOf == 2`).
pub const FnContractScratchMask = packed struct(u16) {
    /// Bitmask of `Context.scratch[0..2]` arenas borrowed/allocated inside this function (`bits 0..1`).
    scratch_touch_mask: u2 = 0,
    /// Bitmask of `Context.scratch[0..2]` arenas rewound/reset inside this function (`bits 2..3`).
    scratch_rewind_mask: u2 = 0,
    /// `true` if declared with `@no_alloc`.
    has_no_alloc: bool = false,
    /// `true` if declared with `@no_panic`.
    has_no_panic: bool = false,
    /// `true` if declared with `@no_block`.
    has_no_block: bool = false,
    /// `true` if declared `comptime` / pure contract.
    has_pure_contract: bool = false,
    /// `true` if declared with `@max_stack(N)`.
    has_max_stack_attr: bool = false,
    /// `true` if part of a recursive Tarjan SCC (`|SCC| > 1` or self-edge).
    is_scc_recursive: bool = false,
    /// `true` if annotated with `@std_cap_boundary`.
    is_std_cap_boundary: bool = false,
    /// `true` if `pub` root, `main`, `@export`, `@link_name`, or `@link_section` (`Fix-17` Gate E).
    is_ambient_export_root: bool = false,
    /// `true` if body contains a vacated non-`Copy` `inout` `subscript` window (`Fix-06B`).
    has_yield_vacated_noncopy: bool = false,
    /// `true` if `max_subtree_bytes > ASYNC_INLINE_CAP_BYTES` (`16 KiB`).
    has_async_exceeded_inline_cap: bool = false,
    /// Reserved zero bits keeping `FnContractScratchMask` at `16` bits.
    _reserved: u2 = 0,

    comptime {
        std.debug.assert(@sizeOf(FnContractScratchMask) == 2);
        std.debug.assert(@bitSizeOf(FnContractScratchMask) == 16);
    }

    /// Represents `self` as a raw 16-bit unsigned integer.
    pub inline fn asBits(self: FnContractScratchMask) u16 {
        return @bitCast(self);
    }

    /// Constructs a `FnContractScratchMask` from raw 16-bit integer `raw_bits`.
    pub inline fn fromBits(raw_bits: u16) FnContractScratchMask {
        return @bitCast(raw_bits & 0x3FFF);
    }
};

/// Canonical 40-byte per-function region, effect, stack, and scratch summary (`DR-17` §2.5).
///
/// Stores `u16` backing integers for `EffectCapabilityMask` and `FnContractScratchMask` to obey
/// Zig `extern struct` layout rules while guaranteeing zero-padding `@sizeOf == 40` (`320` bits).
pub const FnRegionSummary = extern struct {
    /// Bitmask of formal parameter ordinals (`0..63`) whose regions flow into the return value (`[0..8]`).
    ret_provenance_mask: u64 = 0,
    /// `8x8` adjacency bitmatrix (`bit (src * 8 + dst) == 1` when `src` flows into `dst`, `[8..16]`).
    param_flow_matrix: u64 = 0,
    /// Bitmask of formal parameters (`0..31`) escaping into global/static storage (`[16..20]`).
    global_escape_mask: u32 = 0,
    /// Bitmask of formal `sink`/owned parameters (`0..31`) consumed by the function (`[20..24]`).
    consumed_param_mask: u32 = 0,
    /// Local stack frame byte size excluding callees (`[24..28]`, omitted from observable projection).
    own_frame_bytes: u32 = 0,
    /// Worst-case call-subtree stack bytes (`STACK_UNBOUNDED` on recursion/opaque call, `[28..32]`).
    max_subtree_bytes: u32 = 0,
    /// Raw bits of transitive `EffectCapabilityMask` (`[32..34]`).
    inferred_effects_bits: u16 = 0,
    /// Raw bits of body-local direct `EffectCapabilityMask` (`[34..36]`, omitted from projection).
    direct_effects_bits: u16 = 0,
    /// Raw bits of `FnContractScratchMask` (`[36..38]`).
    contracts_scratch_bits: u16 = 0,
    /// Bitmask of higher-order callable parameters (`0..15`) invoked inside the body (`[38..40]`).
    forwarded_cb_mask: u16 = 0,

    /// Sentinel indicating unbounded worst-case stack usage (`recursion` or unannotated indirect call).
    pub const STACK_UNBOUNDED: u32 = 0xFFFF_FFFF;
    /// Default inline async coroutine frame cap (`16 KiB`, `DR-17` §3.2).
    pub const ASYNC_INLINE_CAP_BYTES: u32 = 16_384;
    /// Exact caller-observable byte count hashed by `SAST_SUMMARY_PROJ_FLAG` Early Cutoff (`34B`).
    pub const OBSERVABLE_SUMMARY_BYTES: usize = 34;

    comptime {
        std.debug.assert(@sizeOf(FnRegionSummary) == 40);
        std.debug.assert(@sizeOf(FnRegionSummary) * 8 == 320);
    }

    /// Decodes the transitive `EffectCapabilityMask`.
    pub inline fn inferredEffects(self: FnRegionSummary) EffectCapabilityMask {
        return EffectCapabilityMask.fromBits(self.inferred_effects_bits);
    }

    /// Updates the transitive `EffectCapabilityMask`.
    pub inline fn setInferredEffects(self: *FnRegionSummary, mask: EffectCapabilityMask) void {
        self.inferred_effects_bits = mask.asBits();
    }

    /// Decodes the body-local direct `EffectCapabilityMask`.
    pub inline fn directEffects(self: FnRegionSummary) EffectCapabilityMask {
        return EffectCapabilityMask.fromBits(self.direct_effects_bits);
    }

    /// Updates the body-local direct `EffectCapabilityMask`.
    pub inline fn setDirectEffects(self: *FnRegionSummary, mask: EffectCapabilityMask) void {
        self.direct_effects_bits = mask.asBits();
    }

    /// Decodes the `FnContractScratchMask`.
    pub inline fn contractsScratch(self: FnRegionSummary) FnContractScratchMask {
        return FnContractScratchMask.fromBits(self.contracts_scratch_bits);
    }

    /// Updates the `FnContractScratchMask`.
    pub inline fn setContractsScratch(self: *FnRegionSummary, mask: FnContractScratchMask) void {
        self.contracts_scratch_bits = mask.asBits();
    }

    /// Serializes the exact 34 caller-observable bytes (`[0..24]`, `[28..34]`, `[36..40]`) in little-endian.
    pub inline fn writeObservableBytes(self: FnRegionSummary, out: *[OBSERVABLE_SUMMARY_BYTES]u8) void {
        std.mem.writeInt(u64, out[0..8], self.ret_provenance_mask, .little);
        std.mem.writeInt(u64, out[8..16], self.param_flow_matrix, .little);
        std.mem.writeInt(u32, out[16..20], self.global_escape_mask, .little);
        std.mem.writeInt(u32, out[20..24], self.consumed_param_mask, .little);
        std.mem.writeInt(u32, out[24..28], self.max_subtree_bytes, .little);
        std.mem.writeInt(u16, out[28..30], self.inferred_effects_bits, .little);
        std.mem.writeInt(u16, out[30..32], self.contracts_scratch_bits, .little);
        std.mem.writeInt(u16, out[32..34], self.forwarded_cb_mask, .little);
    }
};

// ------------------ Witness Call Graph & CSR ------------------

/// Classification of an interprocedural call or capability-transfer edge (`DR-17` §2.4).
pub const WitnessEdgeKind = enum(u4) {
    /// Direct static function or method call (`0`).
    direct_call = 0,
    /// Indirect call through a `fn(…)` pointer or closure value (`1`).
    indirect_fn_ptr = 1,
    /// Dynamic dispatch call through a `dyn Trait` vtable (`2`).
    indirect_vtable = 2,
    /// Compiler-elaborated destructor glue (`drop_in_place` / `drop_if_live`) (`3`).
    auto_drop_glue = 3,
    /// Explicit `defer` or `errdefer` cleanup edge (`4`).
    defer_cleanup = 4,
    /// Higher-order callback argument forwarded at a call site (`5`).
    forwarded_cb_arg = 5,
    /// Function item coerced to a first-class function pointer (`Fix-17` Gate A) (`6`).
    reify_fn_addr = 6,
    /// Concrete type coerced to a `dyn Trait` object (`Fix-17` Gate A) (`7`).
    reify_vtable = 7,
};

/// 32-bit packed metadata word stored on each `WitnessCallEdge` (`@sizeOf == 4`).
pub const WitnessEdgeMeta = packed struct(u32) {
    /// Kind of call, reification, or destructor edge (`bits 0..3`).
    edge_kind: WitnessEdgeKind = .direct_call,
    /// Formal parameter index (`0..15`) when `edge_kind == .forwarded_cb_arg` (`bits 4..7`).
    forwarded_arg_ordinal: u4 = 0,
    /// Direct or site-instantiated `EffectCapabilityMask` bits introduced at this edge (`bits 8..23`).
    edge_effects_bits: u16 = 0,
    /// Reserved zero bits keeping `WitnessEdgeMeta` at `32` bits (`bits 24..31`).
    _reserved: u8 = 0,

    comptime {
        std.debug.assert(@sizeOf(WitnessEdgeMeta) == 4);
    }

    /// Encodes `self` as a `u32`.
    pub inline fn asU32(self: WitnessEdgeMeta) u32 {
        return @bitCast(self);
    }

    /// Decodes a `WitnessEdgeMeta` from `raw_bits`.
    pub inline fn fromU32(raw_bits: u32) WitnessEdgeMeta {
        return @bitCast(raw_bits);
    }
};

/// 12-byte Compressed Sparse Row (`CSR`) call-graph edge (`DR-17` §2.4, `@sizeOf == 12`).
pub const WitnessCallEdge = extern struct {
    /// Target `DefId.asInt()`, module-local synthetic node key, or `NONE_U32` for opaque indirect sites.
    callee_def: u32 = mir.NONE_U32,
    /// Source `TokenIndex` of the call, coercion, or destructor site.
    site_token: TokenIndex = .none,
    /// Bit-cast `WitnessEdgeMeta` payload.
    meta_bits: u32 = 0,

    comptime {
        std.debug.assert(@sizeOf(WitnessCallEdge) == 12);
    }

    /// Constructs a `WitnessCallEdge`.
    pub inline fn init(
        callee_def: u32,
        site_token: TokenIndex,
        edge_meta: WitnessEdgeMeta,
    ) WitnessCallEdge {
        return .{
            .callee_def = callee_def,
            .site_token = site_token,
            .meta_bits = edge_meta.asU32(),
        };
    }

    /// Decodes the `WitnessEdgeMeta` of `self`.
    pub inline fn meta(self: WitnessCallEdge) WitnessEdgeMeta {
        return WitnessEdgeMeta.fromU32(self.meta_bits);
    }
};

/// Single hop in a shortest capability/effect violation witness chain (`reconstructShortestWitness`).
pub const WitnessStep = struct {
    /// Caller slot index in `FnSummaryStore`.
    caller_slot: u32,
    /// Callee slot index in `FnSummaryStore` (`mir.NONE_U32` if leaf edge is indirect/intrinsic).
    callee_slot: u32,
    /// Underlying `WitnessCallEdge` taken at this hop.
    edge: WitnessCallEdge,
};

/// Contiguous Compressed Sparse Row (`CSR`) store of `FnRegionSummary` records and `WitnessCallEdge`s.
pub const FnSummaryStore = struct {
    /// Backing allocator owning all slices and maps in `self`.
    allocator: std.mem.Allocator,
    /// Per-function 40-byte summaries (`len == fn_count`).
    summaries: []FnRegionSummary = &.{},
    /// Parallel `DefId` per function slot (`DefId.NONE` for anonymous closures/methods).
    def_ids: []DefId = &.{},
    /// Parallel `SymbolIndex` per function slot.
    symbol_indices: []SymbolIndex = &.{},
    /// Parallel owning `FileId` per function slot.
    file_ids: []FileId = &.{},
    /// Parallel interned function `SymbolId` name per function slot.
    names: []SymbolId = &.{},
    /// CSR row offsets into `edges` (`len == fn_count + 1`).
    edge_offsets: []u32 = &.{},
    /// Contiguous sorted `WitnessCallEdge` array (`edges[edge_offsets[u] .. edge_offsets[u + 1]]`).
    edges: []WitnessCallEdge = &.{},
    /// $O(1)$ map from node key (`DefId.asInt()` or synthetic slot key) to slot index (`0 .. fn_count - 1`).
    node_key_to_slot: std.AutoHashMapUnmanaged(u32, u32) = .empty,

    /// Releases all memory owned by `self`.
    pub fn deinit(self: *FnSummaryStore) void {
        if (self.summaries.len > 0) self.allocator.free(self.summaries);
        if (self.def_ids.len > 0) self.allocator.free(self.def_ids);
        if (self.symbol_indices.len > 0) self.allocator.free(self.symbol_indices);
        if (self.file_ids.len > 0) self.allocator.free(self.file_ids);
        if (self.names.len > 0) self.allocator.free(self.names);
        if (self.edge_offsets.len > 0) self.allocator.free(self.edge_offsets);
        if (self.edges.len > 0) self.allocator.free(self.edges);
        self.node_key_to_slot.deinit(self.allocator);
        self.* = undefined;
    }

    /// Returns the outgoing `WitnessCallEdge` slice for `caller_slot`.
    pub inline fn getEdges(self: *const FnSummaryStore, caller_slot: u32) []const WitnessCallEdge {
        if (caller_slot + 1 >= self.edge_offsets.len) return &.{};
        const start = self.edge_offsets[caller_slot];
        const end = self.edge_offsets[caller_slot + 1];
        return self.edges[start..end];
    }

    /// Looks up the `FnRegionSummary` for `def_id` in $O(1)$ time (`null` if absent).
    pub fn getSummaryByDef(self: *const FnSummaryStore, def_id: DefId) ?FnRegionSummary {
        if (def_id.isNone()) return null;
        const slot = self.node_key_to_slot.get(def_id.asInt()) orelse return null;
        return self.summaries[slot];
    }

    /// Reconstructs a deterministic minimum-hop witness path from `root_slot` to a `forbidden_mask` source.
    pub fn reconstructShortestWitness(
        self: *const FnSummaryStore,
        allocator: std.mem.Allocator,
        root_slot: u32,
        forbidden_mask: u16,
    ) ![]WitnessStep {
        const fn_count = self.summaries.len;
        if (root_slot >= fn_count or forbidden_mask == 0) {
            return allocator.alloc(WitnessStep, 0);
        }

        const parent_slot = try allocator.alloc(u32, fn_count);
        defer allocator.free(parent_slot);
        @memset(parent_slot, mir.NONE_U32);

        const parent_edge = try allocator.alloc(WitnessCallEdge, fn_count);
        defer allocator.free(parent_edge);

        const is_visited = try allocator.alloc(bool, fn_count);
        defer allocator.free(is_visited);
        @memset(is_visited, false);

        const queue = try allocator.alloc(u32, fn_count);
        defer allocator.free(queue);
        var q_head: usize = 0;
        var q_tail: usize = 0;

        is_visited[root_slot] = true;
        queue[q_tail] = root_slot;
        q_tail += 1;

        var leaf_caller: u32 = mir.NONE_U32;
        var leaf_callee: u32 = mir.NONE_U32;
        var leaf_edge: WitnessCallEdge = .{};

        bfs_loop: while (q_head < q_tail) : (q_head += 1) {
            const cur_slot = queue[q_head];
            const is_root_self_culprit = (cur_slot == root_slot) and
                (self.summaries[root_slot].direct_effects_bits & forbidden_mask) != 0;

            for (self.getEdges(cur_slot)) |edge| {
                const edge_meta = edge.meta();
                const eff_forbidden: u16 = if (edge_meta.edge_kind == .reify_fn_addr or
                    edge_meta.edge_kind == .reify_vtable)
                    (forbidden_mask & EffectCapabilityMask.LOCKFILE_CAP_BITS)
                else
                    forbidden_mask;
                if (eff_forbidden == 0) continue;

                if ((edge_meta.edge_effects_bits & eff_forbidden) != 0) {
                    const maybe_callee = self.node_key_to_slot.get(edge.callee_def) orelse mir.NONE_U32;
                    if (maybe_callee == mir.NONE_U32 or
                        (self.summaries[maybe_callee].direct_effects_bits & eff_forbidden) != 0 or
                        self.summaries[maybe_callee].contractsScratch().is_std_cap_boundary)
                    {
                        leaf_caller = cur_slot;
                        leaf_callee = maybe_callee;
                        leaf_edge = edge;
                        break :bfs_loop;
                    }
                }

                const next_slot = self.node_key_to_slot.get(edge.callee_def) orelse continue;
                const next_sum = self.summaries[next_slot];
                if ((next_sum.inferred_effects_bits & eff_forbidden) == 0) continue;
                if (is_root_self_culprit) continue;

                if ((next_sum.direct_effects_bits & eff_forbidden) != 0 or
                    next_sum.contractsScratch().is_std_cap_boundary)
                {
                    leaf_caller = cur_slot;
                    leaf_callee = next_slot;
                    leaf_edge = edge;
                    break :bfs_loop;
                }
                if (!is_visited[next_slot]) {
                    is_visited[next_slot] = true;
                    parent_slot[next_slot] = cur_slot;
                    parent_edge[next_slot] = edge;
                    queue[q_tail] = next_slot;
                    q_tail += 1;
                }
            }
        }

        if (leaf_caller == mir.NONE_U32) {
            return allocator.alloc(WitnessStep, 0);
        }

        var rev_steps: std.ArrayListUnmanaged(WitnessStep) = .empty;
        defer rev_steps.deinit(allocator);
        try rev_steps.append(allocator, .{
            .caller_slot = leaf_caller,
            .callee_slot = leaf_callee,
            .edge = leaf_edge,
        });

        var walk = leaf_caller;
        while (walk != root_slot and parent_slot[walk] != mir.NONE_U32) {
            const prev = parent_slot[walk];
            try rev_steps.append(allocator, .{
                .caller_slot = prev,
                .callee_slot = walk,
                .edge = parent_edge[walk],
            });
            walk = prev;
        }

        const out = try allocator.alloc(WitnessStep, rev_steps.items.len);
        for (0..rev_steps.items.len) |i| {
            out[i] = rev_steps.items[rev_steps.items.len - 1 - i];
        }
        return out;
    }
};

// ---------------- MovePath Trie & DenseBitSet -----------------

/// Strongly typed 32-bit handle into a per-function `MovePathTrie` (`@sizeOf == 4`).
pub const MovePathId = enum(u32) {
    /// Sentinel representing an absent `MovePathId` (`0xFFFF_FFFF`).
    none = std.math.maxInt(u32),
    _,

    /// Wraps `raw_id` as a `MovePathId`.
    pub inline fn fromInt(raw_id: u32) MovePathId {
        return @fromBackingInt(@intCast(raw_id));
    }

    /// Extracts the underlying `u32` index.
    pub inline fn asInt(self: MovePathId) u32 {
        return @backingInt(self);
    }

    /// Returns `true` when `self == .none`.
    pub inline fn isNone(self: MovePathId) bool {
        return self == .none;
    }
};

/// 1-byte bit-packed ownership and projection properties on a `MovePathNode`.
pub const MovePathFlags = packed struct(u8) {
    /// `true` if the projected place type is `OwnershipTier.copy_tier`.
    is_copy: bool = false,
    /// `true` if the projected place type is `OwnershipTier.linear_tier`.
    is_linear: bool = false,
    /// `true` if the projected place type is `OwnershipTier.auto_drop_tier`.
    is_auto_drop: bool = false,
    /// `true` if the projected place is a nominal struct with an explicit `Drop` / `AutoDrop` `impl`.
    is_custom_drop_struct: bool = false,
    /// `true` if the path traverses through a shared reference `&T` or shared slice `[T]`.
    is_behind_shared_ref: bool = false,
    /// `true` if the path traverses through a raw pointer `*T` / `*mut T` dereference.
    is_deref_raw_ptr: bool = false,
    /// Reserved zero bits.
    _reserved: u2 = 0,
};

/// Canonical 20-byte `MovePath` trie node (`DR-06` §2.1, `@sizeOf == 20`).
pub const MovePathNode = extern struct {
    /// Parent `MovePathId` (`.none` for root `LocalId` nodes, `4B`).
    parent: MovePathId = .none,
    /// First child `MovePathId` in intrusive sibling list (`4B`).
    first_child: MovePathId = .none,
    /// Next sibling `MovePathId` under the same `parent` (`4B`).
    next_sibling: MovePathId = .none,
    /// Root `LocalId.asInt()` anchoring this trie tree (`4B`).
    base_local: u32 = 0,
    /// `ProjKind` raw discriminant (`0xFF` for root local nodes, `1B`).
    proj_kind_raw: u8 = 0xFF,
    /// Bit-cast `MovePathFlags` (`1B`).
    flags_raw: u8 = 0,
    /// Field or variant ordinal (`0` when unprojected or `.deref`, `2B`).
    field_or_variant_ord: u16 = 0,

    comptime {
        std.debug.assert(@sizeOf(MovePathNode) == 20);
    }

    /// Decodes the `MovePathFlags` of `self`.
    pub inline fn flags(self: MovePathNode) MovePathFlags {
        return @bitCast(self.flags_raw);
    }
};

/// Result of resolving a `MirPlace` against `MovePathTrie` (`[CRITICAL-02]`).
pub const PlacePathLookup = struct {
    /// Deepest resolved `MovePathId` in the trie.
    id: MovePathId,
    /// `true` if resolution stopped early at dynamic `ProjKind.index` or `MAX_MOVE_PATHS` cap.
    is_partial: bool,
};

/// Hybrid bitset using single-register `u64` ops for `<= 64` bits and `BumpArena` words for `> 64` bits.
pub const DenseBitSet = union(enum) {
    /// Zero-allocation 64-bit register bitset when `bit_count <= 64`.
    inline_words: u64,
    /// Contiguous `u64` word slice allocated inside the per-function `BumpArena` when `bit_count > 64`.
    arena_words: []u64,

    /// Zero-allocation empty bitset constant.
    pub const EMPTY: DenseBitSet = .{ .inline_words = 0 };

    /// Allocates a zero-initialized `DenseBitSet` for `bit_count` bits from `arena_alloc`.
    pub fn initEmpty(arena_alloc: std.mem.Allocator, bit_count: usize) !DenseBitSet {
        if (bit_count <= 64) {
            return .{ .inline_words = 0 };
        }
        const word_count = (bit_count + 63) / 64;
        const words = try arena_alloc.alloc(u64, word_count);
        @memset(words, 0);
        return .{ .arena_words = words };
    }

    /// Clones `self` into a new `DenseBitSet` backed by `arena_alloc`.
    pub fn clone(self: DenseBitSet, arena_alloc: std.mem.Allocator) !DenseBitSet {
        return switch (self) {
            .inline_words => |bits| .{ .inline_words = bits },
            .arena_words => |words| .{ .arena_words = try arena_alloc.dupe(u64, words) },
        };
    }

    /// Returns the number of 64-bit backing words in `self`.
    pub inline fn wordCount(self: DenseBitSet) usize {
        return switch (self) {
            .inline_words => 1,
            .arena_words => |words| words.len,
        };
    }

    /// Reads backing 64-bit word `word_idx` (`0` when out of range).
    pub inline fn wordAt(self: DenseBitSet, word_idx: usize) u64 {
        return switch (self) {
            .inline_words => |bits| if (word_idx == 0) bits else 0,
            .arena_words => |words| if (word_idx < words.len) words[word_idx] else 0,
        };
    }

    /// Returns `true` if every bit in `self` is `0`.
    pub inline fn isEmpty(self: DenseBitSet) bool {
        return switch (self) {
            .inline_words => |bits| bits == 0,
            .arena_words => |words| blk: {
                for (words) |word| {
                    if (word != 0) break :blk false;
                }
                break :blk true;
            },
        };
    }

    /// Returns `true` if `self` and `other` contain identical set bits.
    pub inline fn eql(self: DenseBitSet, other: DenseBitSet) bool {
        if (self == .inline_words and other == .inline_words) {
            return self.inline_words == other.inline_words;
        }
        const max_words = @max(self.wordCount(), other.wordCount());
        for (0..max_words) |word_i| {
            if (self.wordAt(word_i) != other.wordAt(word_i)) return false;
        }
        return true;
    }

    /// Copies all bits from `source` into `self`.
    pub inline fn copyFrom(self: *DenseBitSet, source: DenseBitSet) void {
        switch (self.*) {
            .inline_words => |*dst_bits| dst_bits.* = source.wordAt(0),
            .arena_words => |dst_words| {
                if (source == .arena_words and source.arena_words.len == dst_words.len) {
                    @memcpy(dst_words, source.arena_words);
                } else {
                    for (dst_words, 0..) |*dst_word, word_i| {
                        dst_word.* = source.wordAt(word_i);
                    }
                }
            },
        }
    }

    /// Clears all bits in `self` to `0`.
    pub inline fn clearAll(self: *DenseBitSet) void {
        switch (self.*) {
            .inline_words => |*dst_bits| dst_bits.* = 0,
            .arena_words => |dst_words| @memset(dst_words, 0),
        }
    }

    /// Sets all bits in `0..bit_count` to `1` (used for fail-closed saturation).
    pub fn setAll(self: *DenseBitSet, bit_count: usize) void {
        if (bit_count == 0) {
            self.clearAll();
            return;
        }
        switch (self.*) {
            .inline_words => |*dst_bits| {
                dst_bits.* = if (bit_count >= 64)
                    std.math.maxInt(u64)
                else
                    (@as(u64, 1) << @intCast(bit_count)) - 1;
            },
            .arena_words => |dst_words| {
                for (dst_words, 0..) |*dst_word, word_i| {
                    const base_bit = word_i * 64;
                    if (base_bit >= bit_count) {
                        dst_word.* = 0;
                    } else if (bit_count - base_bit >= 64) {
                        dst_word.* = std.math.maxInt(u64);
                    } else {
                        dst_word.* = (@as(u64, 1) << @intCast(bit_count - base_bit)) - 1;
                    }
                }
            },
        }
    }

    /// Returns `true` if bit `index` is `1`.
    pub inline fn isSet(self: DenseBitSet, index: usize) bool {
        return switch (self) {
            .inline_words => |bits| if (index < 64) ((bits >> @intCast(index)) & 1) != 0 else false,
            .arena_words => |words| blk: {
                const word_idx = index >> 6;
                if (word_idx >= words.len) break :blk false;
                break :blk ((words[word_idx] >> @intCast(index & 63)) & 1) != 0;
            },
        };
    }

    /// Sets bit `index` to `1`.
    pub inline fn set(self: *DenseBitSet, index: usize) void {
        switch (self.*) {
            .inline_words => |*bits| {
                if (index < 64) bits.* |= (@as(u64, 1) << @intCast(index));
            },
            .arena_words => |words| {
                const word_idx = index >> 6;
                if (word_idx < words.len) words[word_idx] |= (@as(u64, 1) << @intCast(index & 63));
            },
        }
    }

    /// Clears bit `index` to `0`.
    pub inline fn unset(self: *DenseBitSet, index: usize) void {
        switch (self.*) {
            .inline_words => |*bits| {
                if (index < 64) bits.* &= ~(@as(u64, 1) << @intCast(index));
            },
            .arena_words => |words| {
                const word_idx = index >> 6;
                if (word_idx < words.len) words[word_idx] &= ~(@as(u64, 1) << @intCast(index & 63));
            },
        }
    }

    /// Performs `self |= other` and returns `true` if any bit in `self` changed from `0` to `1`.
    pub inline fn unionAssignChanged(self: *DenseBitSet, other: DenseBitSet) bool {
        switch (self.*) {
            .inline_words => |*bits| {
                const merged = bits.* | other.wordAt(0);
                const has_changed = merged != bits.*;
                bits.* = merged;
                return has_changed;
            },
            .arena_words => |words| {
                var has_changed = false;
                for (words, 0..) |*dst_word, word_i| {
                    const merged = dst_word.* | other.wordAt(word_i);
                    if (merged != dst_word.*) has_changed = true;
                    dst_word.* = merged;
                }
                return has_changed;
            },
        }
    }

    /// Performs `self |= other` in-place.
    pub inline fn unionInPlace(self: *DenseBitSet, other: DenseBitSet) void {
        _ = self.unionAssignChanged(other);
    }

    /// Returns `lhs | rhs`, allocating inside `arena_alloc` only when multi-word backing is active.
    pub fn unionAlloc(lhs: DenseBitSet, rhs: DenseBitSet, arena_alloc: std.mem.Allocator) !DenseBitSet {
        if (lhs == .inline_words and rhs == .inline_words) {
            return .{ .inline_words = lhs.inline_words | rhs.inline_words };
        }
        const word_len = @max(lhs.wordCount(), rhs.wordCount());
        const out_words = try arena_alloc.alloc(u64, word_len);
        for (out_words, 0..) |*dst_word, word_i| {
            dst_word.* = lhs.wordAt(word_i) | rhs.wordAt(word_i);
        }
        return .{ .arena_words = out_words };
    }

    /// Performs `self &= ~mask` in-place.
    pub inline fn differenceInPlace(self: *DenseBitSet, mask: DenseBitSet) void {
        switch (self.*) {
            .inline_words => |*bits| bits.* &= ~mask.wordAt(0),
            .arena_words => |words| {
                for (words, 0..) |*dst_word, word_i| {
                    dst_word.* &= ~mask.wordAt(word_i);
                }
            },
        }
    }

    /// Returns `true` if `(self & other) != 0`.
    pub inline fn intersects(self: DenseBitSet, other: DenseBitSet) bool {
        if (self == .inline_words and other == .inline_words) {
            return (self.inline_words & other.inline_words) != 0;
        }
        const min_words = @min(self.wordCount(), other.wordCount());
        for (0..min_words) |word_i| {
            if ((self.wordAt(word_i) & other.wordAt(word_i)) != 0) return true;
        }
        return false;
    }

    /// Returns the lowest bit index `>= start_index` that is `1` (`null` if none).
    pub fn nextSetBit(self: DenseBitSet, start_index: usize) ?usize {
        switch (self) {
            .inline_words => |bits| {
                if (start_index >= 64) return null;
                const shifted = bits & (@as(u64, std.math.maxInt(u64)) << @as(u6, @intCast(start_index)));
                if (shifted == 0) return null;
                return @ctz(shifted);
            },
            .arena_words => |words| {
                var word_i = start_index >> 6;
                if (word_i >= words.len) return null;
                const first_mask = @as(u64, std.math.maxInt(u64)) << @as(u6, @intCast(start_index & 63));
                const first_masked = words[word_i] & first_mask;
                if (first_masked != 0) return word_i * 64 + @ctz(first_masked);
                word_i += 1;
                while (word_i < words.len) : (word_i += 1) {
                    if (words[word_i] != 0) return word_i * 64 + @ctz(words[word_i]);
                }
                return null;
            },
        }
    }

    /// Returns the lowest bit index where `(self & other)` has a `1` (`null` if disjoint).
    pub fn firstIntersectionBit(self: DenseBitSet, other: DenseBitSet) ?usize {
        if (self == .inline_words and other == .inline_words) {
            const common = self.inline_words & other.inline_words;
            return if (common == 0) null else @ctz(common);
        }
        const min_words = @min(self.wordCount(), other.wordCount());
        for (0..min_words) |word_i| {
            const common = self.wordAt(word_i) & other.wordAt(word_i);
            if (common != 0) return word_i * 64 + @ctz(common);
        }
        return null;
    }
};

// -------------- Sign-Biased Interval & Pentagon ---------------

/// 16-byte order-preserving interval (`DR-06` §2.3 & `[CRITICAL-03]`, `@sizeOf == 16`).
///
/// Signed domains (`i8`..`i64`, `isize`) flip bit 63 (`val_u64 ^ SIGN_BIAS_U64`) so `i64.min -> 0` and
/// `i64.max -> u64.max`. Unsigned domains (`u8`..`u64`, `usize`, `bool`, `char`) store raw `u64` directly.
/// Any state with `lo_ord > hi_ord` represents unreachable bottom (`⊥`).
pub const Intv = extern struct {
    /// Order-preserving inclusive lower bound (`1` for `BOTTOM`).
    lo_ord: u64,
    /// Order-preserving inclusive upper bound (`0` for `BOTTOM`).
    hi_ord: u64,

    /// Unreachable bottom interval (`lo_ord = 1 > hi_ord = 0`).
    pub const BOTTOM: Intv = .{ .lo_ord = 1, .hi_ord = 0 };
    /// Full 64-bit order-preserving top interval (`[0, u64.max]`).
    pub const TOP_ORD: Intv = .{ .lo_ord = 0, .hi_ord = std.math.maxInt(u64) };

    comptime {
        std.debug.assert(@sizeOf(Intv) == 16);
    }

    /// Encodes a signed `i64` scalar into a monotonically ordered `u64`.
    pub inline fn encodeSigned(signed_val: i64) u64 {
        return @as(u64, @bitCast(signed_val)) ^ SIGN_BIAS_U64;
    }

    /// Decodes a sign-biased `u64` back into a signed `i64` scalar.
    pub inline fn decodeSigned(encoded_ord: u64) i64 {
        return @bitCast(encoded_ord ^ SIGN_BIAS_U64);
    }

    /// Constructs a signed interval `[min_val, max_val]` (`BOTTOM` when `min_val > max_val`).
    pub inline fn initSigned(min_val: i64, max_val: i64) Intv {
        if (min_val > max_val) return BOTTOM;
        return .{
            .lo_ord = encodeSigned(min_val),
            .hi_ord = encodeSigned(max_val),
        };
    }

    /// Constructs an unsigned interval `[min_val, max_val]` (`BOTTOM` when `min_val > max_val`).
    pub inline fn initUnsigned(min_val: u64, max_val: u64) Intv {
        if (min_val > max_val) return BOTTOM;
        return .{ .lo_ord = min_val, .hi_ord = max_val };
    }

    /// Returns `true` if `self` is empty / unreachable (`lo_ord > hi_ord`).
    pub inline fn isBottom(self: Intv) bool {
        return self.lo_ord > self.hi_ord;
    }

    /// Returns `true` if `self` and `other` have identical encoded bounds (or are both `BOTTOM`).
    pub inline fn eql(self: Intv, other: Intv) bool {
        if (self.isBottom() and other.isBottom()) return true;
        return self.lo_ord == other.lo_ord and self.hi_ord == other.hi_ord;
    }

    /// Least upper bound (`self ⊔ other`) in $O(1)$ register `min`/`max` ops.
    pub inline fn join(self: Intv, other: Intv) Intv {
        if (self.isBottom()) return other;
        if (other.isBottom()) return self;
        return .{
            .lo_ord = @min(self.lo_ord, other.lo_ord),
            .hi_ord = @max(self.hi_ord, other.hi_ord),
        };
    }

    /// Greatest lower bound (`self ⊓ other`) in $O(1)$ register `max`/`min` ops.
    pub inline fn meet(self: Intv, other: Intv) Intv {
        if (self.isBottom() or other.isBottom()) return BOTTOM;
        const lo_val = @max(self.lo_ord, other.lo_ord);
        const hi_val = @min(self.hi_ord, other.hi_ord);
        return if (lo_val > hi_val) BOTTOM else .{ .lo_ord = lo_val, .hi_ord = hi_val };
    }
};

/// 256-bit (`32B`) strict upper-bound set `sub[x] = { y | x < y }` in the Demand-Sliced Pentagon.
pub const PentagonSubRow = extern struct {
    /// Four 64-bit bitset words indexing sliced Pentagon variables `0..255`.
    words: [4]u64 = .{ 0, 0, 0, 0 },

    comptime {
        std.debug.assert(@sizeOf(PentagonSubRow) == 32);
    }

    /// Returns `true` if sliced variable `var_idx` (`< 256`) is strictly greater than this row's owner.
    pub inline fn contains(self: PentagonSubRow, var_idx: u8) bool {
        const word_i: usize = var_idx >> 6;
        const bit_i: u6 = @truncate(var_idx);
        return ((self.words[word_i] >> bit_i) & 1) != 0;
    }

    /// Inserts sliced variable `var_idx` (`< 256`) into this strict upper-bound set.
    pub inline fn insert(self: *PentagonSubRow, var_idx: u8) void {
        const word_i: usize = var_idx >> 6;
        const bit_i: u6 = @truncate(var_idx);
        self.words[word_i] |= (@as(u64, 1) << bit_i);
    }

    /// Intersects `self` with `other` (`self ∩ other`, used at control-flow joins).
    pub inline fn intersectWith(self: PentagonSubRow, other: PentagonSubRow) PentagonSubRow {
        return .{
            .words = .{
                self.words[0] & other.words[0],
                self.words[1] & other.words[1],
                self.words[2] & other.words[2],
                self.words[3] & other.words[3],
            },
        };
    }

    /// Unions `self` with `other` (`self ∪ other`, used for 1-hop transitive closure).
    pub inline fn unionWith(self: PentagonSubRow, other: PentagonSubRow) PentagonSubRow {
        return .{
            .words = .{
                self.words[0] | other.words[0],
                self.words[1] | other.words[1],
                self.words[2] | other.words[2],
                self.words[3] | other.words[3],
            },
        };
    }

    /// Returns `true` if `self` equals `other`.
    pub inline fn eql(self: PentagonSubRow, other: PentagonSubRow) bool {
        return self.words[0] == other.words[0] and
            self.words[1] == other.words[1] and
            self.words[2] == other.words[2] and
            self.words[3] == other.words[3];
    }
};

// ----------------- Package Capability Sandbox -----------------

/// Three-tier package capability roll-up (`DR-17` §3.1 & `Fix-17` Gate E).
pub const PackageCapSummary = struct {
    /// Union of capabilities across all compiled items in the package/module (`ambient_caps`).
    ambient_caps: EffectCapabilityMask = .{},
    /// Capabilities reachable from `main`, `pub` exports, `@export`, `@link_name`, or `@link_section`.
    reachable_caps: EffectCapabilityMask = .{},
    /// Capabilities reachable exclusively from `pub` surface items (`surface_caps`).
    surface_caps: EffectCapabilityMask = .{},
};

/// Scope of `E0324` package capability policy enforcement (`DR-17` §4.1).
pub const CapEnforcementScope = enum(u8) {
    /// Enforce `allowed_caps` against `pub` surface exports (`surface_caps`, default library policy).
    surface = 0,
    /// Enforce `allowed_caps` against all reachable export/entry roots (`reachable_caps`).
    all = 1,
};

/// Package capability policy declared in `corex.toml` / `corex.lock` (`DR-17` §3.1).
pub const PackageCapPolicy = struct {
    /// Package display name for `E0324` / `W0330` diagnostics.
    package_name: []const u8 = "root",
    /// Primary manifest/file span reported on policy violations.
    policy_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
    /// Allowed `LOCKFILE_CAP_BITS` granted to this package (`0xFFFF` = unrestricted root binary).
    allowed_caps: EffectCapabilityMask = EffectCapabilityMask.fromBits(0x0FFF),
    /// `true` when checking an external third-party dependency (gates `W0330` dead `ffi | unsafe_op`).
    is_third_party_dependency: bool = false,
    /// Selects whether `E0324` inspects `surface_caps` (`.surface`) or `reachable_caps` (`.all`).
    enforcement_scope: CapEnforcementScope = .surface,
};

// ---------------- SAST Configuration & Results ----------------

/// Strongly typed callback resolving cross-`DefId` `FnRegionSummary` records (`DR-17` §2.5).
pub const ExternalSummaryResolver = struct {
    /// Optional incremental `CompilerDb` backing Stage 9 cross-`DefId` summary queries.
    compiler_db: ?*query_db.CompilerDb = null,
    /// Optional precomputed `DefId.asInt() -> FnRegionSummary` map for standalone tests.
    summary_map: ?*const std.AutoHashMapUnmanaged(u32, FnRegionSummary) = null,
    /// Callback fetching a finalized 40-byte `FnRegionSummary` for `(callee_def, callee_sym)`.
    resolve_fn: *const fn (
        compiler_db: ?*query_db.CompilerDb,
        summary_map: ?*const std.AutoHashMapUnmanaged(u32, FnRegionSummary),
        callee_def: DefId,
        callee_sym: SymbolIndex,
    ) query_db.QueryError!?FnRegionSummary,
};

/// Configuration parameters driving `mir_sast` analysis and elaboration.
pub const SastConfig = struct {
    /// Optional diagnostic sink receiving `E03xx`, `E0406`, and `W03xx` diagnostics.
    diagnostic_sink: ?*DiagnosticSink = null,
    /// `true` when `--sast-strict` is enabled (emits `W0314` on unproven bounds checks outside `@no_panic`).
    is_sast_strict: bool = false,
    /// `true` when analyzing a `comptime` item (`const` / `comptime fn`, enforces Gate F `E0325`).
    is_comptime_context: bool = false,
    /// Optional source buffer for fine-grained `@std_cap_boundary` & token-span extraction.
    source_text: ?[]const u8 = null,
    /// Optional `TokenBuffer` mapping `TokenIndex` to exact byte `Span`s.
    token_buffer: ?*const TokenBuffer = null,
    /// Optional `LosslessCstArena` for fine-grained attribute inspection.
    cst_arena: ?*const LosslessCstArena = null,
    /// Optional external `FnRegionSummary` resolver for per-`DefId` incremental queries.
    external_resolver: ?ExternalSummaryResolver = null,
    /// Optional `PackageCapPolicy` checked after Pass 3 (`null` skips `E0324`/`W0330`).
    package_policy: ?PackageCapPolicy = null,
    /// Optional prefix count of primary `MirBody` slots emitting diagnostics/telemetry (used for SCC peers).
    primary_body_count: ?usize = null,
};

/// Complete result of running Phase 6 SAST and drop/BCE elaboration across one or more `MirBody` items.
pub const MirSastResult = struct {
    /// CSR summary and witness call-edge store across all analyzed functions.
    summary_store: FnSummaryStore,
    /// Aggregated `ambient_caps`, `reachable_caps`, and `surface_caps`.
    package_caps: PackageCapSummary = .{},
    /// Peak scratch bytes allocated by the Demand-Sliced Pentagon solver (`< 1.5 MB` invariant).
    peak_pentagon_bytes: usize = 0,
    /// Count of `bounds_check` and `slice_range_check` intrinsics statically proven & eliminated.
    eliminated_bounds_checks: u32 = 0,
    /// Count of `.narrow()` (`narrow_check`) intrinsics statically proven & rewritten to casts.
    eliminated_narrow_checks: u32 = 0,
    /// Count of `drop_in_place` and `drop_if_live` instructions synthesized by `ElaborateDrops`.
    emitted_drops: u32 = 0,

    /// Releases `summary_store`.
    pub fn deinit(self: *MirSastResult) void {
        self.summary_store.deinit();
        self.* = undefined;
    }
};

/// Self-contained pipeline bundle returned by `lowerAndVerifySourceMirSast`.
pub const MirSastPipelineBundle = struct {
    /// Backing allocator owning all arenas and stores in `self`.
    allocator: std.mem.Allocator,
    /// Shared string interner.
    interner: StringInterner,
    /// Lexed token buffer.
    token_buffer: TokenBuffer,
    /// Lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Lossy AST arena.
    ast_arena: AstArena,
    /// Resolved symbol table.
    sym_table: SymbolTable,
    /// Canonical type intern pool.
    pool: InternPool,
    /// Extracted semantic side tables.
    side_tables: type_system.BodySemanticSideTables,
    /// Desugared HIR store.
    hir_store: hir.HirStore,
    /// Elaborated MIR module bundle (with `drop_in_place`/`drop_if_live` and Pentagon BCE applied).
    mir_module: MirModuleBundle,
    /// Phase 6 SAST summaries, CSR witness edges, and telemetry.
    sast_result: MirSastResult,
    /// Combined frontend + HIR + MIR + SAST diagnostic sink.
    diagnostics: DiagnosticSink,

    /// Releases all arenas, tables, MIR bodies, and SAST summaries owned by `self`.
    pub fn deinit(self: *MirSastPipelineBundle) void {
        self.sast_result.deinit();
        self.mir_module.deinit();
        self.hir_store.deinit();
        self.side_tables.deinit();
        self.pool.deinit();
        self.sym_table.deinit();
        self.ast_arena.deinit();
        self.cst_arena.deinit();
        self.token_buffer.deinit();
        self.diagnostics.deinit();
        self.interner.deinit();
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard per-function `MovePath` trie node cap (`4,096 * 20B = 80 KiB`, `DR-06` §2.1).
pub const MAX_MOVE_PATHS: u32 = 4096;

/// Order-preserving sign-flip bias mapping `i64` monotonically onto `u64` (`[CRITICAL-03]`).
pub const SIGN_BIAS_U64: u64 = 0x8000_0000_0000_0000;

/// Maximum backward-sliced SSA variables tracked in the Pentagon relational sub-domain (`256`).
pub const MAX_SUB_VARS: usize = 256;

/// Maximum active RPO block relational states pooled simultaneously in Pentagon (`128 -> 1.0 MiB`).
pub const MAX_PENTAGON_BLOCKS: usize = 128;

/// Maximum tracked NLL `LoanId` entries per function (`<= 64` inline `u64`, `> 64` in `BumpArena`; `4095` = overflow).
const MAX_TRACKED_LOANS: usize = 4096;

/// Symbolic region depth `0`: `'static` constants, string literals, and global functions.
pub const DEPTH_STATIC: u16 = 0;

/// Symbolic region depth `1`: caller-supplied borrowed formal parameters (`0..7`).
pub const DEPTH_CALLER_PARAM: u16 = 1;

/// Symbolic region depth `2`: caller-supplied `&mut Arena` / `inout Arena` formal parameter.
pub const DEPTH_CALLER_ARENA: u16 = 2;

/// Symbolic region depth `3`: current function stack frame locals and `@local` closures.
pub const DEPTH_FN_FRAME: u16 = 3;

/// Base symbolic region depth `4`: body-local `Arena` / `BumpArena` and nested lexical scopes (`4 + d`).
pub const DEPTH_LOCAL_REGION_BASE: u16 = 4;

/// Synthetic node-key flag distinguishing anonymous `MirBody` indices (`DefId.NONE`) in `FnSummaryStore`.
const ANON_BODY_KEY_FLAG: u32 = 0x8000_0000;

/// $O(1)$ static map from `@std_cap_boundary` identifier names to exact 12-bit `EffectCapabilityMask` bits.
const FINE_CAPABILITY_NAME_MAP = std.StaticStringMap(u16).initComptime(.{
    .{ "Alloc", 1 << 6 },
    .{ "BlockingSync", 1 << 10 },
    .{ "Clock", 1 << 8 },
    .{ "ClockEntropy", (1 << 8) | (1 << 9) },
    .{ "Entropy", 1 << 9 },
    .{ "Env", 1 << 2 },
    .{ "Ffi", 1 << 4 },
    .{ "FfiUnsafe", (1 << 4) | (1 << 5) },
    .{ "Fs", 1 << 0 },
    .{ "HeapAlloc", 1 << 6 },
    .{ "IndirectOpaque", 1 << 11 },
    .{ "IoAsync", 1 << 10 },
    .{ "IoFs", 1 << 0 },
    .{ "IoNet", 1 << 1 },
    .{ "MayPanic", 1 << 7 },
    .{ "Net", 1 << 1 },
    .{ "Process", 1 << 3 },
    .{ "ThreadSpawn", 1 << 3 },
    .{ "UnsafeOp", 1 << 5 },
    .{ "alloc", 1 << 6 },
    .{ "block", 1 << 10 },
    .{ "blocking_sync", 1 << 10 },
    .{ "clock", 1 << 8 },
    .{ "clock_entropy", (1 << 8) | (1 << 9) },
    .{ "entropy", 1 << 9 },
    .{ "env", 1 << 2 },
    .{ "ffi", 1 << 4 },
    .{ "ffi_unsafe", (1 << 4) | (1 << 5) },
    .{ "fs", 1 << 0 },
    .{ "heap_alloc", 1 << 6 },
    .{ "indirect_opaque", 1 << 11 },
    .{ "io_async", 1 << 10 },
    .{ "io_fs", 1 << 0 },
    .{ "io_net", 1 << 1 },
    .{ "may_panic", 1 << 7 },
    .{ "net", 1 << 1 },
    .{ "panic", 1 << 7 },
    .{ "process", 1 << 3 },
    .{ "thread_spawn", 1 << 3 },
    .{ "unsafe_op", 1 << 5 },
});

/// $O(1)$ static map of explicit deallocation/close method names triggering `ever_freed` / `E0313`.
const EXPLICIT_FREE_METHOD_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "close", {} },
    .{ "commit", {} },
    .{ "dealloc", {} },
    .{ "deinit", {} },
    .{ "destroy", {} },
    .{ "free", {} },
    .{ "release", {} },
    .{ "rollback", {} },
    .{ "unlock", {} },
});

/// $O(1)$ static map of lexical arena nominal type names (`W0308` & `DEPTH_LOCAL_REGION_BASE`).
const ARENA_TYPE_NAME_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "Arena", {} },
    .{ "BumpArena", {} },
});

/// $O(1)$ static map of lifecycle-only `Arena` methods that do NOT count as arena allocation (`W0308`).
const ARENA_LIFECYCLE_METHOD_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "deinit", {} },
    .{ "destroy", {} },
    .{ "free", {} },
    .{ "init", {} },
    .{ "new", {} },
    .{ "reset", {} },
    .{ "rewind", {} },
    .{ "with_capacity", {} },
});

/// $O(1)$ static map of `Context.scratch` reset/rewind method names (`D-04` -> `scratch_rewind_mask`).
const SCRATCH_RESET_METHOD_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "clear", {} },
    .{ "reset", {} },
    .{ "rewind", {} },
    .{ "scratch_reset", {} },
    .{ "scratch_rewind", {} },
});

/// $O(1)$ static map of `Context.scratch` complement-slot selector helper names (`D-04`).
const SCRATCH_SELECT_METHOD_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "scratch_scope", {} },
    .{ "select_scratch", {} },
});

/// $O(1)$ static map of dynamic heap-growing container methods (`alloc = true` when receiver is not `Arena`).
const HEAP_GROWTH_METHOD_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "alloc", {} },
    .{ "append", {} },
    .{ "box_new", {} },
    .{ "clone_heap", {} },
    .{ "extend", {} },
    .{ "grow", {} },
    .{ "insert", {} },
    .{ "push", {} },
    .{ "push_str", {} },
    .{ "realloc", {} },
    .{ "reserve", {} },
    .{ "resize", {} },
    .{ "with_capacity", {} },
});

/// $O(1)$ static map from built-in/external prototype names to inferred `EffectCapabilityMask` bits.
const EXTERN_PROTO_EFFECT_MAP = std.StaticStringMap(EffectCapabilityMask).initComptime(.{
    .{ "abort", EffectCapabilityMask{ .may_panic = true } },
    .{ "expect", EffectCapabilityMask{ .may_panic = true } },
    .{ "getenv", EffectCapabilityMask{ .env = true } },
    .{ "monotonic_now", EffectCapabilityMask{ .clock = true } },
    .{ "mutex_lock", EffectCapabilityMask{ .blocking_sync = true } },
    .{ "now_ns", EffectCapabilityMask{ .clock = true } },
    .{ "open_file", EffectCapabilityMask{ .fs = true } },
    .{ "os_random", EffectCapabilityMask{ .entropy = true } },
    .{ "panic", EffectCapabilityMask{ .may_panic = true } },
    .{ "park_thread", EffectCapabilityMask{ .blocking_sync = true } },
    .{ "read_file", EffectCapabilityMask{ .fs = true } },
    .{ "sleep_ms", EffectCapabilityMask{ .blocking_sync = true } },
    .{ "spawn_process", EffectCapabilityMask{ .process = true } },
    .{ "spawn_thread", EffectCapabilityMask{ .process = true } },
    .{ "tcp_connect", EffectCapabilityMask{ .net = true } },
    .{ "udp_bind", EffectCapabilityMask{ .net = true } },
    .{ "unwrap", EffectCapabilityMask{ .may_panic = true } },
    .{ "write_file", EffectCapabilityMask{ .fs = true } },
});

// -------------------------------------- INTERNALS --------------------------------------

// ---------------- Capability & Span Utilities -----------------

/// Translates `symbol_resolver.CapabilityBits` into canonical 12-bit `EffectCapabilityMask`.
fn capabilityBitsToEffectMask(cap_bits: u16) EffectCapabilityMask {
    return EffectCapabilityMask.fromBits(cap_bits & 0x0FFF);
}

/// Strips outer string literal quotes (`"…"` or `r#"…"#`) without allocating.
fn stripAttrQuotes(lexeme: []const u8) []const u8 {
    if (lexeme.len >= 2 and lexeme[0] == '"' and lexeme[lexeme.len - 1] == '"') {
        return lexeme[1 .. lexeme.len - 1];
    }
    return lexeme;
}

/// Extracts exact 12-bit `(emits, clears)` masks for an `@std_cap_boundary` symbol (`DR-17` §2.3).
fn extractBoundaryMasksForSymbol(
    sym: SymbolRecord,
    active_file_id: FileId,
    config: SastConfig,
) struct { emits: u16, clears: u16 } {
    if (sym.cap_emits_mask != 0 or sym.cap_clears_mask != 0) {
        return .{
            .emits = capabilityBitsToEffectMask(sym.cap_emits_mask).asBits(),
            .clears = capabilityBitsToEffectMask(sym.cap_clears_mask).asBits(),
        };
    }

    if (!sym.decl_span.file_id.isNone() and sym.decl_span.file_id == active_file_id) {
        if (config.source_text) |src_bytes| {
            if (config.token_buffer) |tok_buf| {
                if (config.cst_arena) |cst_ar| {
                    if (!sym.cst_node.isNone() and sym.cst_node.asInt() < cst_ar.countNodes()) {
                        const start_idx: usize = sym.cst_node.asInt();
                        const root_rec = cst_ar.getNode(sym.cst_node);
                        const end_idx: usize = @min(
                            start_idx + @max(@as(usize, root_rec.subtree_size), 1),
                            cst_ar.countNodes(),
                        );
                        var has_fine_attr = false;
                        var fine_emits: u16 = 0;
                        var fine_clears: u16 = 0;

                        var cur_idx: usize = start_idx + 1;
                        while (cur_idx < end_idx) : (cur_idx += 1) {
                            const node = cst_ar.getNode(CstNodeIndex.fromInt(@intCast(cur_idx)));
                            if (node.kind != .attribute) continue;
                            const attr_end = @min(
                                cur_idx + @max(@as(usize, node.subtree_size), 1),
                                end_idx,
                            );
                            var is_boundary_attr = false;
                            var is_emits_mode = false;
                            var leaf_cur = cur_idx + 1;
                            while (leaf_cur < attr_end) : (leaf_cur += 1) {
                                const leaf = cst_ar.getNode(CstNodeIndex.fromInt(@intCast(leaf_cur)));
                                if (leaf.subtree_size > 1 or leaf.token.isNone() or
                                    leaf.token.asInt() >= tok_buf.countTokens())
                                {
                                    continue;
                                }
                                const tok = tok_buf.getToken(leaf.token);
                                if (tok.byte_offset >= src_bytes.len) continue;
                                const end_off = @min(@as(usize, tok.byte_offset) + tok.byte_len, src_bytes.len);
                                const raw_lex = src_bytes[tok.byte_offset..end_off];
                                const ident_lex = if (tok.kind == .string_lit)
                                    stripAttrQuotes(raw_lex)
                                else
                                    raw_lex;

                                if (!is_boundary_attr) {
                                    if (std.mem.eql(u8, ident_lex, "std_cap_boundary")) {
                                        is_boundary_attr = true;
                                        has_fine_attr = true;
                                    }
                                    continue;
                                }
                                if (std.mem.eql(u8, ident_lex, "emits")) {
                                    is_emits_mode = true;
                                    continue;
                                }
                                if (std.mem.eql(u8, ident_lex, "clears")) {
                                    is_emits_mode = false;
                                    continue;
                                }
                                if (FINE_CAPABILITY_NAME_MAP.get(ident_lex)) |cap_bits| {
                                    if (is_emits_mode) {
                                        fine_emits |= cap_bits;
                                    } else {
                                        fine_clears |= cap_bits;
                                    }
                                }
                            }
                        }
                        if (has_fine_attr) {
                            return .{ .emits = fine_emits, .clears = fine_clears };
                        }
                    }
                }
            }
        }
    }

    return .{ .emits = 0, .clears = 0 };
}

/// Resolves a `TokenIndex` into an exact byte `Span` when `config.token_buffer` matches `file_id`.
fn resolveTokenSpan(file_id: FileId, token_idx: TokenIndex, config: SastConfig, fallback_span: Span) Span {
    if (!token_idx.isNone()) {
        if (config.token_buffer) |tok_buf| {
            if (token_idx.asInt() < tok_buf.countTokens()) {
                return tok_buf.getTokenSpan(file_id, token_idx);
            }
        }
    }
    if (fallback_span.file_id == file_id and
        (fallback_span.start_byte != 0 or fallback_span.end_byte != 0))
    {
        return fallback_span;
    }
    return Span.init(file_id, 0, 0);
}

/// Resolves the declaration header `Span` of `body` from `sym_table` as a fallback anchor.
fn resolveBodyDeclSpan(body: *const MirBody, sym_table: *const SymbolTable) Span {
    if (!body.symbol_index.isNone() and body.symbol_index.asInt() < sym_table.symbols.items.len) {
        return sym_table.getSymbol(body.symbol_index).decl_span;
    }
    if (!body.def_id.isNone()) {
        if (sym_table.def_to_symbol.get(body.def_id.asInt())) |mapped_idx| {
            if (!mapped_idx.isNone() and mapped_idx.asInt() < sym_table.symbols.items.len) {
                return sym_table.symbols.items[mapped_idx.asInt()].decl_span;
            }
        }
    }
    return Span.init(body.file_id, 0, 0);
}

/// Emits a structured Phase 6 diagnostic with primary span, optional secondary spans, and `help:` note.
fn emitSastDiag(
    sink_opt: ?*DiagnosticSink,
    code: DiagnosticCode,
    severity: Severity,
    primary_span: Span,
    message: []const u8,
    primary_label: []const u8,
    secondary_a: ?LabeledSpan,
    secondary_b: ?LabeledSpan,
    help_note: ?[]const u8,
) !void {
    const sink = sink_opt orelse return;
    const arena_alloc = sink.arena.asAllocator();

    var label_list: [3]LabeledSpan = undefined;
    label_list[0] = .{
        .span = primary_span,
        .label = try arena_alloc.dupe(u8, primary_label),
        .style = .primary,
    };
    var label_len: usize = 1;

    if (secondary_a) |sec_first| {
        label_list[label_len] = .{
            .span = sec_first.span,
            .label = try arena_alloc.dupe(u8, sec_first.label),
            .style = .secondary,
        };
        label_len += 1;
    }
    if (secondary_b) |sec_second| {
        label_list[label_len] = .{
            .span = sec_second.span,
            .label = try arena_alloc.dupe(u8, sec_second.label),
            .style = .secondary,
        };
        label_len += 1;
    }

    var notes_slice: []const []const u8 = &.{};
    if (help_note) |note_str| {
        const note_arr = try arena_alloc.alloc([]const u8, 1);
        note_arr[0] = try arena_alloc.dupe(u8, note_str);
        notes_slice = note_arr;
    }

    _ = try sink.emit(.{
        .code = code,
        .severity = severity,
        .primary_span = primary_span,
        .message = try arena_alloc.dupe(u8, message),
        .labels = try arena_alloc.dupe(LabeledSpan, label_list[0..label_len]),
        .notes = notes_slice,
    });
}

/// Returns `true` if `type_id` (peeling `&` / `&mut`) is `Arena` or `BumpArena`.
fn isArenaType(pool: *const InternPool, sym_table: *const SymbolTable, type_id: TypeId) bool {
    if (type_id.isError()) return false;
    var cur_ty = pool.unwrapUnderlyingType(type_id);
    const cur_node = pool.getNode(cur_ty);
    if (cur_node.tag == .ref_ty or cur_node.tag == .mut_ref_ty) {
        cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
    }
    const base_node = pool.getNode(cur_ty);
    if (base_node.tag != .struct_ty) return false;
    const sym_idx = SymbolIndex.fromInt(base_node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
    return ARENA_TYPE_NAME_MAP.has(sym_table.getSymbol(sym_idx).name_text);
}

/// Returns `true` if `type_id` is an owned `Arena` or `BumpArena` value (excluding `&` / `&mut` references).
fn isOwnedArenaType(pool: *const InternPool, sym_table: *const SymbolTable, type_id: TypeId) bool {
    if (type_id.isError()) return false;
    const cur_ty = pool.unwrapUnderlyingType(type_id);
    const base_node = pool.getNode(cur_ty);
    if (base_node.tag != .struct_ty) return false;
    const sym_idx = SymbolIndex.fromInt(base_node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
    return ARENA_TYPE_NAME_MAP.has(sym_table.getSymbol(sym_idx).name_text);
}

/// Returns `true` if `type_id` (peeling `&` / `&mut`) is `PoolAllocator`.
fn isPoolAllocatorType(pool: *const InternPool, sym_table: *const SymbolTable, type_id: TypeId) bool {
    if (type_id.isError()) return false;
    var cur_ty = pool.unwrapUnderlyingType(type_id);
    const cur_node = pool.getNode(cur_ty);
    if (cur_node.tag == .ref_ty or cur_node.tag == .mut_ref_ty) {
        cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
    }
    const base_node = pool.getNode(cur_ty);
    if (base_node.tag != .struct_ty) return false;
    const sym_idx = SymbolIndex.fromInt(base_node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
    return std.mem.eql(u8, sym_table.getSymbol(sym_idx).name_text, "PoolAllocator");
}

/// Returns the `SymbolIndex` of an explicit `fn drop` on nominal `type_id` (`SymbolIndex.none` if none).
fn lookupDirectDropMethodSymbol(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    type_id: TypeId,
) SymbolIndex {
    if (type_id.isError()) return .none;
    const unwrapped = pool.unwrapUnderlyingType(type_id);
    const node = pool.getNode(unwrapped);
    if (node.tag != .struct_ty and node.tag != .enum_ty and node.tag != .union_ty) return .none;
    const type_sym_idx = SymbolIndex.fromInt(node.rhs);
    if (type_sym_idx.isNone() or type_sym_idx.asInt() >= sym_table.symbols.items.len) return .none;
    const type_sym = sym_table.getSymbol(type_sym_idx).*;
    if (type_sym.target_scope.isNone()) return .none;

    for (sym_table.getScopeMembers(type_sym.target_scope)) |mem_idx| {
        const mem_sym = sym_table.getSymbol(mem_idx).*;
        if (mem_sym.kind == .fn_sym and std.mem.eql(u8, mem_sym.name_text, "drop")) {
            return mem_idx;
        }
    }
    return .none;
}

/// Recursively collects custom `Drop::drop` symbols and built-in heap-container free flags for `type_id`.
fn collectDropGlueTargets(
    allocator: std.mem.Allocator,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    type_id: TypeId,
    depth: u8,
    drop_syms_out: *std.ArrayListUnmanaged(SymbolIndex),
    has_heap_free_out: *bool,
) !void {
    return collectDropGlueTargetsBounded(
        allocator,
        pool,
        sym_table,
        type_id,
        &type_system.NominalTypeSubst.EMPTY,
        depth,
        drop_syms_out,
        has_heap_free_out,
    );
}

/// Depth-bounded helper for `collectDropGlueTargets` propagating generic nominal substitution `subst`.
fn collectDropGlueTargetsBounded(
    allocator: std.mem.Allocator,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_type_id: TypeId,
    subst: *const type_system.NominalTypeSubst,
    depth: u8,
    drop_syms_out: *std.ArrayListUnmanaged(SymbolIndex),
    has_heap_free_out: *bool,
) !void {
    const type_id = subst.resolve(raw_type_id);
    if (type_id.isError() or depth >= 16) return;
    const unwrapped = pool.unwrapUnderlyingType(type_id);
    if (type_system.classifyOwnershipTierWithSubst(pool, sym_table, unwrapped, subst) != .auto_drop_tier) return;

    const direct_drop = lookupDirectDropMethodSymbol(pool, sym_table, unwrapped);
    if (!direct_drop.isNone()) {
        var has_seen = false;
        for (drop_syms_out.items) |existing| {
            if (existing == direct_drop) {
                has_seen = true;
                break;
            }
        }
        if (!has_seen) try drop_syms_out.append(allocator, direct_drop);
    }

    const node = pool.getNode(unwrapped);
    switch (node.tag) {
        .dyn_trait_ty => has_heap_free_out.* = true,
        .array_ty, .soa_array_ty => {
            try collectDropGlueTargetsBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                subst,
                depth + 1,
                drop_syms_out,
                has_heap_free_out,
            );
        },
        .optional_ty => {
            try collectDropGlueTargetsBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                subst,
                depth + 1,
                drop_syms_out,
                has_heap_free_out,
            );
        },
        .result_ty => {
            try collectDropGlueTargetsBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.lhs),
                subst,
                depth + 1,
                drop_syms_out,
                has_heap_free_out,
            );
            try collectDropGlueTargetsBounded(
                allocator,
                pool,
                sym_table,
                TypeId.fromInt(node.rhs),
                subst,
                depth + 1,
                drop_syms_out,
                has_heap_free_out,
            );
        },
        .tuple_ty => {
            for (pool.getTupleElements(unwrapped)) |elem_raw| {
                try collectDropGlueTargetsBounded(
                    allocator,
                    pool,
                    sym_table,
                    TypeId.fromInt(elem_raw),
                    subst,
                    depth + 1,
                    drop_syms_out,
                    has_heap_free_out,
                );
            }
        },
        .struct_ty, .union_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const sym = sym_table.getSymbol(sym_idx).*;
                if (type_system.AUTO_DROP_CONTAINER_MAP.has(sym.name_text)) {
                    has_heap_free_out.* = true;
                }
                if (!sym.target_scope.isNone()) {
                    const child_subst = type_system.NominalTypeSubst.fromNominal(
                        pool,
                        sym_table,
                        unwrapped,
                        sym,
                        subst,
                    );
                    const active_subst = if (child_subst.len > 0) &child_subst else subst;
                    for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind == .field_sym) {
                            try collectDropGlueTargetsBounded(
                                allocator,
                                pool,
                                sym_table,
                                mem_sym.type_id,
                                active_subst,
                                depth + 1,
                                drop_syms_out,
                                has_heap_free_out,
                            );
                        }
                    }
                }
            }
        },
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const sym = sym_table.getSymbol(sym_idx).*;
                if (!sym.target_scope.isNone()) {
                    const child_subst = type_system.NominalTypeSubst.fromNominal(
                        pool,
                        sym_table,
                        unwrapped,
                        sym,
                        subst,
                    );
                    const active_subst = if (child_subst.len > 0) &child_subst else subst;
                    for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind == .enum_variant_sym and mem_sym.type_id != .unit_ty) {
                            try collectDropGlueTargetsBounded(
                                allocator,
                                pool,
                                sym_table,
                                mem_sym.type_id,
                                active_subst,
                                depth + 1,
                                drop_syms_out,
                                has_heap_free_out,
                            );
                        }
                    }
                }
            }
        },
        else => {},
    }
}

/// Returns `true` when an `AutoDrop` local inside a lexical region (`region_raw != 0`) needs zero drop glue.
fn isTrivialArenaDrop(
    allocator: std.mem.Allocator,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    type_id: TypeId,
    region_raw: u16,
) !bool {
    if (region_raw == 0) return false;
    var drop_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
    defer drop_syms.deinit(allocator);
    var has_heap_free = false;
    try collectDropGlueTargets(
        allocator,
        pool,
        sym_table,
        type_id,
        0,
        &drop_syms,
        &has_heap_free,
    );
    return drop_syms.items.len == 0 and !has_heap_free;
}

// ------------ Call Graph & Tarjan SCC Construction ------------

/// Returns the canonical `FnSummaryStore` node key for `body` at `slot_idx`.
inline fn nodeKeyForBody(body: *const MirBody, slot_idx: u32) u32 {
    if (!body.def_id.isNone()) return body.def_id.asInt();
    return ANON_BODY_KEY_FLAG | slot_idx;
}

/// Compressed SCC list produced in bottom-up topological order (callees before callers).
const SccSchedule = struct {
    /// Flat array of `slot_idx` (`0 .. fn_count - 1`) grouped by SCC.
    members: []u32,
    /// Start/end offsets (`len == scc_count + 1`) slicing `members`.
    offsets: []u32,
    /// `true` per SCC when `|SCC| > 1` or a single node has a self-edge.
    is_recursive: []bool,

    /// Releases arrays owned by `self`.
    fn deinit(self: *SccSchedule, allocator: std.mem.Allocator) void {
        allocator.free(self.members);
        allocator.free(self.offsets);
        allocator.free(self.is_recursive);
        self.* = undefined;
    }
};

/// Extracts the `trait_sym` `SymbolIndex` when `raw_ty` is `dyn Trait`, `&dyn Trait`, `&mut dyn Trait`, or `*dyn Trait`.
fn extractDynTraitSymbol(pool: *const InternPool, raw_ty: TypeId) ?SymbolIndex {
    if (raw_ty.isError()) return null;
    var cur_ty = pool.unwrapUnderlyingType(raw_ty);
    if (cur_ty.isError()) return null;
    var cur_node = pool.getNode(cur_ty);
    if (cur_node.tag == .ref_ty or cur_node.tag == .mut_ref_ty or cur_node.tag == .raw_ptr_ty) {
        cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
        if (cur_ty.isError()) return null;
        cur_node = pool.getNode(cur_ty);
    }
    if (cur_node.tag != .dyn_trait_ty) return null;
    const trait_ty = pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
    if (trait_ty.isError()) return null;
    const trait_node = pool.getNode(trait_ty);
    if (trait_node.tag != .trait_ty) return null;
    const trait_sym = SymbolIndex.fromInt(trait_node.rhs);
    return if (trait_sym.isNone()) null else trait_sym;
}

/// Extracts the concrete nominal `SymbolIndex` (`struct`, `enum`, `union`) behind `raw_ty` or a reference/pointer to it.
fn extractConcreteNominalSymbol(pool: *const InternPool, raw_ty: TypeId) ?SymbolIndex {
    if (raw_ty.isError()) return null;
    var cur_ty = pool.unwrapUnderlyingType(raw_ty);
    if (cur_ty.isError()) return null;
    var cur_node = pool.getNode(cur_ty);
    if (cur_node.tag == .ref_ty or cur_node.tag == .mut_ref_ty or cur_node.tag == .raw_ptr_ty) {
        cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(cur_node.lhs));
        if (cur_ty.isError()) return null;
        cur_node = pool.getNode(cur_ty);
    }
    if (cur_node.tag != .struct_ty and cur_node.tag != .enum_ty and cur_node.tag != .union_ty) return null;
    const nom_sym = SymbolIndex.fromInt(cur_node.rhs);
    return if (nom_sym.isNone()) null else nom_sym;
}

/// Builds the module call graph (including `fn_addr`, closures, vtables, and `Drop` glue) and computes Tarjan SCCs.
fn computeBottomUpTarjanSccs(
    allocator: std.mem.Allocator,
    scratch_arena: *BumpArena,
    bodies: []const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
) !SccSchedule {
    const cp = scratch_arena.checkpoint();
    defer scratch_arena.restore(cp);
    const arena_alloc = scratch_arena.asAllocator();

    const fn_count = bodies.len;
    const adj_lists = try arena_alloc.alloc(std.ArrayListUnmanaged(u32), fn_count);
    for (adj_lists) |*list| list.* = .empty;
    const adj_seen = try arena_alloc.alloc(DenseBitSet, fn_count);
    for (adj_seen) |*seen_set| seen_set.* = try DenseBitSet.initEmpty(arena_alloc, fn_count);

    const has_self_edge = try arena_alloc.alloc(bool, fn_count);
    @memset(has_self_edge, false);

    const addUniqueEdge = struct {
        //! Deduplicated call-graph edge helper recording self-loops in `has_self_flags`.

        /// Appends `dst_slot` to `lists[src_slot]` in $O(1)$ if absent, or sets `has_self_flags[src_slot]` on self-edge.
        fn run(
            alloc: std.mem.Allocator,
            lists: []std.ArrayListUnmanaged(u32),
            seen_sets: []DenseBitSet,
            has_self_flags: []bool,
            src_slot: u32,
            dst_slot: u32,
        ) !void {
            if (src_slot == dst_slot) {
                has_self_flags[src_slot] = true;
                return;
            }
            if (seen_sets[src_slot].isSet(dst_slot)) return;
            seen_sets[src_slot].set(dst_slot);
            try lists[src_slot].append(alloc, dst_slot);
        }
    }.run;

    for (bodies, 0..) |*body, slot_usize| {
        const caller_slot: u32 = @intCast(slot_usize);

        // [1] Direct `.call` targets:
        for (body.calls.items) |call_site| {
            var target_opt: ?u32 = null;
            if (!call_site.direct_def_id.isNone()) {
                target_opt = key_to_slot.get(call_site.direct_def_id.asInt());
            }
            if (target_opt == null and !call_site.direct_symbol.isNone()) {
                target_opt = sym_to_slot.get(call_site.direct_symbol.asInt());
            }
            if (target_opt) |callee_slot| {
                try addUniqueEdge(arena_alloc, adj_lists, adj_seen, has_self_edge, caller_slot, callee_slot);
            }
        }

        // [2] Reified `fn_addr`, `closure_make`, and `dyn Trait` vtable coercion bodies:
        const ops = body.insts.items(.op);
        const aux_slice = body.insts.items(.aux_u16);
        const opnds = body.insts.items(.operands);
        const inst_tys = body.insts.items(.type_id);
        for (ops, aux_slice, opnds, inst_tys) |op, aux, opnd, inst_ty| {
            if (op == .fn_addr) {
                var target_opt: ?u32 = null;
                if (opnd.lhs != mir.NONE_U32) target_opt = key_to_slot.get(opnd.lhs);
                if (target_opt == null and opnd.rhs != mir.NONE_U32) {
                    target_opt = sym_to_slot.get(opnd.rhs);
                }
                if (target_opt) |callee_slot| {
                    try addUniqueEdge(arena_alloc, adj_lists, adj_seen, has_self_edge, caller_slot, callee_slot);
                }
            } else if (op == .aggregate_make) {
                const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(aux))));
                if (agg_kind == .closure_make) {
                    if (key_to_slot.get(opnd.lhs)) |clos_slot| {
                        try addUniqueEdge(arena_alloc, adj_lists, adj_seen, has_self_edge, caller_slot, clos_slot);
                    }
                }
            } else if ((op == .unary_op or op == .copy_val) and opnd.lhs < inst_tys.len) {
                if (extractDynTraitSymbol(pool, inst_ty)) |trait_sym_idx| {
                    const src_ty = inst_tys[opnd.lhs];
                    if (extractDynTraitSymbol(pool, src_ty) == null) {
                        if (extractConcreteNominalSymbol(pool, src_ty)) |nom_sym_idx| {
                            if (nom_sym_idx.asInt() < sym_table.symbols.items.len) {
                                const nom_sym = sym_table.getSymbol(nom_sym_idx).*;
                                if (!nom_sym.target_scope.isNone()) {
                                    for (sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                                        if (mem_sym.kind != .fn_sym) continue;
                                        if (sym_table.impl_method_trait.get(mem_idx.asInt()) != trait_sym_idx) continue;
                                        const impl_slot = (if (!mem_sym.def_id.isNone())
                                            key_to_slot.get(mem_sym.def_id.asInt())
                                        else
                                            null) orelse sym_to_slot.get(mem_idx.asInt());
                                        if (impl_slot) |callee_slot| {
                                            try addUniqueEdge(
                                                arena_alloc,
                                                adj_lists,
                                                adj_seen,
                                                has_self_edge,
                                                caller_slot,
                                                callee_slot,
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // [3] Potential `AutoDrop` destructor `Drop::drop` callees on body locals & `&mut T` pointees:
        var drop_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
        for (body.locals.items, 0..) |loc, loc_i| {
            if (loc_i == 0) continue;
            var candidate_types: [2]TypeId = .{ .err_ty, .err_ty };
            var cand_len: usize = 0;
            if (!loc.flags().is_arg or loc.mode() == .sink_mode or loc.mode() == .inout_mode) {
                candidate_types[cand_len] = loc.type_id;
                cand_len += 1;
            }
            const unwrapped_loc = pool.unwrapUnderlyingType(loc.type_id);
            if (!unwrapped_loc.isError() and pool.getNode(unwrapped_loc).tag == .mut_ref_ty) {
                candidate_types[cand_len] = TypeId.fromInt(pool.getNode(unwrapped_loc).lhs);
                cand_len += 1;
            }
            for (candidate_types[0..cand_len]) |cand_ty| {
                var has_heap = false;
                drop_syms.clearRetainingCapacity();
                try collectDropGlueTargets(
                    arena_alloc,
                    pool,
                    sym_table,
                    cand_ty,
                    0,
                    &drop_syms,
                    &has_heap,
                );
                for (drop_syms.items) |drop_sym_idx| {
                    if (sym_to_slot.get(drop_sym_idx.asInt())) |drop_slot| {
                        try addUniqueEdge(arena_alloc, adj_lists, adj_seen, has_self_edge, caller_slot, drop_slot);
                    } else {
                        const drop_def = sym_table.getSymbol(drop_sym_idx).def_id;
                        if (!drop_def.isNone()) {
                            if (key_to_slot.get(drop_def.asInt())) |drop_slot| {
                                try addUniqueEdge(arena_alloc, adj_lists, adj_seen, has_self_edge, caller_slot, drop_slot);
                            }
                        }
                    }
                }
            }
        }
    }

    // Iterative Tarjan $O(V + E)$ DFS:
    const indices = try arena_alloc.alloc(u32, fn_count);
    @memset(indices, mir.NONE_U32);

    const lowlinks = try arena_alloc.alloc(u32, fn_count);
    @memset(lowlinks, mir.NONE_U32);

    const is_on_stack = try arena_alloc.alloc(bool, fn_count);
    @memset(is_on_stack, false);

    const scc_stack = try arena_alloc.alloc(u32, fn_count);
    var scc_sp: usize = 0;

    const TarjanFrame = struct {
        //! Explicit DFS work-stack frame for non-recursive Tarjan SCC traversal.

        /// Active function slot index (`0 .. fn_count - 1`).
        node: u32,
        /// Next outgoing neighbor index in `adj_lists[node]`.
        edge_cursor: usize,
    };
    const dfs_stack = try arena_alloc.alloc(TarjanFrame, fn_count + 1);

    var scc_members: std.ArrayListUnmanaged(u32) = .empty;
    errdefer scc_members.deinit(allocator);
    var scc_offsets: std.ArrayListUnmanaged(u32) = .empty;
    errdefer scc_offsets.deinit(allocator);
    var is_scc_rec_flags: std.ArrayListUnmanaged(bool) = .empty;
    errdefer is_scc_rec_flags.deinit(allocator);
    try scc_offsets.append(allocator, 0);

    var next_dfs_idx: u32 = 0;
    for (0..fn_count) |root_usize| {
        const root_node: u32 = @intCast(root_usize);
        if (indices[root_node] != mir.NONE_U32) continue;

        indices[root_node] = next_dfs_idx;
        lowlinks[root_node] = next_dfs_idx;
        next_dfs_idx += 1;
        scc_stack[scc_sp] = root_node;
        scc_sp += 1;
        is_on_stack[root_node] = true;

        dfs_stack[0] = .{ .node = root_node, .edge_cursor = 0 };
        var dfs_sp: usize = 1;

        while (dfs_sp > 0) {
            const top = &dfs_stack[dfs_sp - 1];
            const cur_u = top.node;
            const neighbors = adj_lists[cur_u].items;
            if (top.edge_cursor < neighbors.len) {
                const succ_v = neighbors[top.edge_cursor];
                top.edge_cursor += 1;
                if (indices[succ_v] == mir.NONE_U32) {
                    indices[succ_v] = next_dfs_idx;
                    lowlinks[succ_v] = next_dfs_idx;
                    next_dfs_idx += 1;
                    scc_stack[scc_sp] = succ_v;
                    scc_sp += 1;
                    is_on_stack[succ_v] = true;
                    dfs_stack[dfs_sp] = .{ .node = succ_v, .edge_cursor = 0 };
                    dfs_sp += 1;
                } else if (is_on_stack[succ_v]) {
                    lowlinks[cur_u] = @min(lowlinks[cur_u], indices[succ_v]);
                }
            } else {
                dfs_sp -= 1;
                if (dfs_sp > 0) {
                    const parent_u = dfs_stack[dfs_sp - 1].node;
                    lowlinks[parent_u] = @min(lowlinks[parent_u], lowlinks[cur_u]);
                }
                if (lowlinks[cur_u] == indices[cur_u]) {
                    const start_len = scc_members.items.len;
                    while (scc_sp > 0) {
                        scc_sp -= 1;
                        const member_w = scc_stack[scc_sp];
                        is_on_stack[member_w] = false;
                        try scc_members.append(allocator, member_w);
                        if (member_w == cur_u) break;
                    }
                    const scc_size = scc_members.items.len - start_len;
                    const is_rec = scc_size > 1 or has_self_edge[cur_u];
                    try scc_offsets.append(allocator, @intCast(scc_members.items.len));
                    try is_scc_rec_flags.append(allocator, is_rec);
                }
            }
        }
    }

    return .{
        .members = try scc_members.toOwnedSlice(allocator),
        .offsets = try scc_offsets.toOwnedSlice(allocator),
        .is_recursive = try is_scc_rec_flags.toOwnedSlice(allocator),
    };
}

// --------- Pass 1: MovePath Trie & Region Provenance ----------

/// Per-function `MovePath` trie and precomputed `DenseBitSet` conflict masks (`DR-06` §2.1).
const MovePathTrie = struct {
    /// Contiguous `20B` trie nodes (`0 .. direct_local_limit - 1` are root `LocalId`s).
    nodes: []MovePathNode,
    /// Static `TypeId` of every `MovePathId` node in `nodes` (`len == nodes.len`).
    node_types: []TypeId,
    /// Exclusive upper bound of root `LocalId`s mapped 1-to-1 onto `MovePathId(loc_i)`.
    direct_local_limit: u32,
    /// Precomputed lookup `(id, is_partial)` for every `PlaceId` in `MirBody.places`.
    place_map: []PlacePathLookup,
    /// Precomputed `TypeId` at the leaf of every `PlaceId` in `MirBody.places`.
    place_leaf_types: []TypeId,
    /// `subtree[m]` bitset containing `m` and all trie descendants of `m`.
    subtree: []DenseBitSet,
    /// `ancestors[m]` bitset containing `m` and all trie ancestors up to the root `LocalId`.
    ancestors: []DenseBitSet,
    /// `strict_anc[m]` bitset containing strict ancestors of `m` (`ancestors[m] \ {m}`).
    strict_anc: []DenseBitSet,
    /// `conflict[m] = subtree[m] | ancestors[m]` for $O(1)$ MVS borrow conflict checks.
    conflict: []DenseBitSet,
};

/// Resolves field/element `TypeId` on `base_ty` during `MovePathTrie` construction.
fn stepProjectedType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    cur_ty_raw: TypeId,
    proj: MirProjection,
    active_subst: *type_system.NominalTypeSubst,
    active_downcast: *?u32,
    active_soa_field: *?TypeId,
) TypeId {
    if (active_soa_field.*) |soa_ty| {
        active_soa_field.* = null;
        return if (proj.kind == .slice_len) .usize_ty else active_subst.resolve(soa_ty);
    }
    const cur_ty = pool.unwrapUnderlyingType(active_subst.resolve(cur_ty_raw));
    if (cur_ty.isError()) return .err_ty;
    const node = pool.getNode(cur_ty);
    switch (proj.kind) {
        .deref => {
            active_downcast.* = null;
            if (node.tag == .ref_ty or node.tag == .mut_ref_ty or node.tag == .raw_ptr_ty) {
                return pool.unwrapUnderlyingType(active_subst.resolve(TypeId.fromInt(node.lhs)));
            }
            return .err_ty;
        },
        .downcast => {
            active_downcast.* = proj.payload;
            return cur_ty;
        },
        .field => {
            if (active_downcast.*) |tag_ord| {
                active_downcast.* = null;
                const payload_ty = switch (node.tag) {
                    .optional_ty => if (tag_ord == 1) active_subst.resolve(TypeId.fromInt(node.lhs)) else TypeId.unit_ty,
                    .result_ty => if (tag_ord == 0)
                        active_subst.resolve(TypeId.fromInt(node.lhs))
                    else
                        active_subst.resolve(TypeId.fromInt(node.rhs)),
                    .enum_ty => blk: {
                        const sym_idx = SymbolIndex.fromInt(node.rhs);
                        const sym = sym_table.getSymbol(sym_idx).*;
                        if (!sym.target_scope.isNone()) {
                            const next_subst = type_system.NominalTypeSubst.fromNominal(
                                pool,
                                sym_table,
                                cur_ty,
                                sym,
                                active_subst,
                            );
                            if (next_subst.len > 0) active_subst.* = next_subst;
                            var ord: u32 = 0;
                            for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                                const mem_sym = sym_table.getSymbol(mem_idx).*;
                                if (mem_sym.kind != .enum_variant_sym) continue;
                                if (ord == tag_ord) {
                                    break :blk active_subst.resolve(mem_sym.type_id);
                                }
                                ord += 1;
                            }
                        }
                        break :blk TypeId.unit_ty;
                    },
                    else => TypeId.unit_ty,
                };
                if (proj.payload == 0) return pool.unwrapUnderlyingType(payload_ty);
                return stepProjectedType(
                    pool,
                    sym_table,
                    payload_ty,
                    proj,
                    active_subst,
                    active_downcast,
                    active_soa_field,
                );
            }
            switch (node.tag) {
                .tuple_ty => {
                    const elems = pool.getTupleElements(cur_ty);
                    if (proj.payload < elems.len) {
                        return pool.unwrapUnderlyingType(active_subst.resolve(TypeId.fromInt(elems[proj.payload])));
                    }
                },
                .struct_ty, .union_ty => {
                    const sym_idx = SymbolIndex.fromInt(node.rhs);
                    const sym = sym_table.getSymbol(sym_idx).*;
                    if (!sym.target_scope.isNone()) {
                        const next_subst = type_system.NominalTypeSubst.fromNominal(
                            pool,
                            sym_table,
                            cur_ty,
                            sym,
                            active_subst,
                        );
                        if (next_subst.len > 0) active_subst.* = next_subst;
                        var ord: u32 = 0;
                        for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                            const mem_sym = sym_table.getSymbol(mem_idx).*;
                            if (mem_sym.kind != .field_sym) continue;
                            if (ord == proj.payload) {
                                return pool.unwrapUnderlyingType(active_subst.resolve(mem_sym.type_id));
                            }
                            ord += 1;
                        }
                    }
                },
                else => {},
            }
            return .unit_ty;
        },
        .index => {
            active_downcast.* = null;
            if (node.tag == .array_ty or node.tag == .slice_ty or
                node.tag == .soa_array_ty or node.tag == .soa_slice_ty)
            {
                return pool.unwrapUnderlyingType(active_subst.resolve(TypeId.fromInt(node.lhs)));
            }
            return .unit_ty;
        },
        .soa_elem => {
            active_downcast.* = null;
            if (node.tag == .soa_array_ty or node.tag == .soa_slice_ty) {
                const elem_ty = pool.unwrapUnderlyingType(active_subst.resolve(TypeId.fromInt(node.lhs)));
                var dummy_subst = active_subst.*;
                var dummy_dc: ?u32 = null;
                var dummy_soa: ?TypeId = null;
                active_soa_field.* = stepProjectedType(
                    pool,
                    sym_table,
                    elem_ty,
                    .{ .kind = .field, .payload = proj.payload },
                    &dummy_subst,
                    &dummy_dc,
                    &dummy_soa,
                );
            }
            return cur_ty;
        },
        .slice_len => {
            active_downcast.* = null;
            return .usize_ty;
        },
    }
}

/// Computes `MovePathFlags` for a node of `node_ty` with accumulated ref/raw-ptr markers.
fn makeMovePathFlags(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    node_ty: TypeId,
    subst: *const type_system.NominalTypeSubst,
    is_behind_shared: bool,
    is_deref_raw: bool,
) MovePathFlags {
    const resolved_ty = subst.resolve(node_ty);
    const tier = type_system.classifyOwnershipTierWithSubst(pool, sym_table, resolved_ty, subst);
    return .{
        .is_copy = tier == .copy_tier,
        .is_linear = tier == .linear_tier,
        .is_auto_drop = tier == .auto_drop_tier,
        .is_custom_drop_struct = !lookupDirectDropMethodSymbol(pool, sym_table, resolved_ty).isNone(),
        .is_behind_shared_ref = is_behind_shared,
        .is_deref_raw_ptr = is_deref_raw,
    };
}

/// Counts direct `.field` members of a `.struct_ty` or `.tuple_ty` (`0` for other types).
fn countAggregateFieldMembers(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    agg_ty_raw: TypeId,
) u32 {
    const agg_ty = pool.unwrapUnderlyingType(agg_ty_raw);
    if (agg_ty.isError()) return 0;
    const node = pool.getNode(agg_ty);
    if (node.tag == .tuple_ty) {
        return @intCast(pool.getTupleElements(agg_ty).len);
    }
    if (node.tag == .struct_ty) {
        const sym_idx = SymbolIndex.fromInt(node.rhs);
        const sym = sym_table.getSymbol(sym_idx).*;
        if (sym.target_scope.isNone()) return 0;
        var count: u32 = 0;
        for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
            if (sym_table.getSymbol(mem_idx).kind == .field_sym) count += 1;
        }
        return count;
    }
    return 0;
}

/// Pass 1: Constructs the bounded `MovePathTrie` (`MAX_MOVE_PATHS = 4096`) inside `arena_alloc`.
fn buildMovePathTrie(
    arena_alloc: std.mem.Allocator,
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) !MovePathTrie {
    const local_count = body.locals.items.len;
    const has_local_overflow = local_count >= MAX_MOVE_PATHS;
    const direct_roots: usize = if (has_local_overflow) MAX_MOVE_PATHS - 1 else local_count;
    const cap_nodes: usize = if (has_local_overflow) MAX_MOVE_PATHS else @max(direct_roots, 16);

    var node_list: std.ArrayListUnmanaged(MovePathNode) = .empty;
    try node_list.ensureTotalCapacity(arena_alloc, cap_nodes);
    var type_list: std.ArrayListUnmanaged(TypeId) = .empty;
    try type_list.ensureTotalCapacity(arena_alloc, cap_nodes);

    for (0..direct_roots) |loc_i| {
        const loc_ty = body.locals.items[loc_i].type_id;
        node_list.appendAssumeCapacity(.{
            .parent = .none,
            .first_child = .none,
            .next_sibling = .none,
            .base_local = @intCast(loc_i),
            .proj_kind_raw = 0xFF,
            .flags_raw = @bitCast(makeMovePathFlags(
                pool,
                sym_table,
                loc_ty,
                &type_system.NominalTypeSubst.EMPTY,
                false,
                false,
            )),
            .field_or_variant_ord = 0,
        });
        type_list.appendAssumeCapacity(loc_ty);
    }

    var overflow_root_id: MovePathId = .none;
    if (has_local_overflow) {
        overflow_root_id = MovePathId.fromInt(@intCast(node_list.items.len));
        node_list.appendAssumeCapacity(.{
            .parent = .none,
            .first_child = .none,
            .next_sibling = .none,
            .base_local = @intCast(direct_roots),
            .proj_kind_raw = 0xFE,
            .flags_raw = @bitCast(MovePathFlags{}),
            .field_or_variant_ord = 0,
        });
        type_list.appendAssumeCapacity(.err_ty);
    }

    const place_count = body.places.items.len;
    const place_map = try arena_alloc.alloc(PlacePathLookup, place_count);
    const place_leaf_types = try arena_alloc.alloc(TypeId, place_count);

    for (body.places.items, 0..) |place_rec, pl_i| {
        if (place_rec.base >= direct_roots) {
            place_map[pl_i] = .{
                .id = overflow_root_id,
                .is_partial = true,
            };
            place_leaf_types[pl_i] = .err_ty;
            continue;
        }

        var cur_id = MovePathId.fromInt(place_rec.base);
        var cur_ty = body.locals.items[place_rec.base].type_id;
        var is_partial = false;
        var is_behind_shared = false;
        var is_deref_raw = false;
        var active_subst: type_system.NominalTypeSubst = .{};
        var active_downcast: ?u32 = null;
        var active_soa_field: ?TypeId = null;

        for (body.getPlaceProjections(PlaceId.fromInt(@intCast(pl_i)))) |proj| {
            const unwrapped_before = pool.unwrapUnderlyingType(active_subst.resolve(cur_ty));
            const subst_before = active_subst;
            const has_downcast = active_downcast != null;
            const has_soa_elem = active_soa_field != null;
            if (!unwrapped_before.isError()) {
                const before_tag = pool.getNode(unwrapped_before).tag;
                if (proj.kind == .deref) {
                    if (before_tag == .ref_ty) is_behind_shared = true;
                    if (before_tag == .raw_ptr_ty) is_deref_raw = true;
                } else if (proj.kind == .index and before_tag == .slice_ty) {
                    is_behind_shared = true;
                } else if (proj.kind == .soa_elem and before_tag == .soa_slice_ty and
                    pool.getNode(unwrapped_before).rhs == 0)
                {
                    is_behind_shared = true;
                }
            }

            cur_ty = stepProjectedType(
                pool,
                sym_table,
                cur_ty,
                proj,
                &active_subst,
                &active_downcast,
                &active_soa_field,
            );

            // Dynamic `.index` collapses into parent with `is_partial = true` (`[CRITICAL-02]`):
            if (proj.kind == .index) {
                is_partial = true;
                continue;
            }
            if (is_partial) continue;

            const ord_u16: u16 = @intCast(@min(proj.payload, std.math.maxInt(u16)));
            const kind_raw: u8 = @backingInt(proj.kind);

            var matched_child: MovePathId = .none;
            var walk_child = node_list.items[cur_id.asInt()].first_child;
            while (!walk_child.isNone()) {
                const child_node = node_list.items[walk_child.asInt()];
                if (child_node.proj_kind_raw == kind_raw and
                    child_node.field_or_variant_ord == ord_u16)
                {
                    matched_child = walk_child;
                    break;
                }
                walk_child = child_node.next_sibling;
            }

            if (!matched_child.isNone()) {
                cur_id = matched_child;
            } else if (proj.kind == .field and !has_downcast and !has_soa_elem) {
                // Materialize all sibling `.field` children of `.struct_ty`/`.tuple_ty` together so
                // partial moves and field-by-field re-initializations track every sibling accurately:
                const total_fields = countAggregateFieldMembers(pool, sym_table, unwrapped_before);
                if (total_fields > 0 and node_list.items.len + total_fields <= MAX_MOVE_PATHS) {
                    for (0..total_fields) |f_ord| {
                        const f_u16: u16 = @intCast(@min(f_ord, std.math.maxInt(u16)));
                        var existing_f: MovePathId = .none;
                        var chk_ch = node_list.items[cur_id.asInt()].first_child;
                        while (!chk_ch.isNone()) {
                            const cn = node_list.items[chk_ch.asInt()];
                            if (cn.proj_kind_raw == kind_raw and cn.field_or_variant_ord == f_u16) {
                                existing_f = chk_ch;
                                break;
                            }
                            chk_ch = cn.next_sibling;
                        }
                        if (existing_f.isNone()) {
                            var sibling_subst = subst_before;
                            var dummy_dc: ?u32 = null;
                            var dummy_soa: ?TypeId = null;
                            const f_ty = stepProjectedType(
                                pool,
                                sym_table,
                                unwrapped_before,
                                .{ .kind = .field, .payload = @intCast(f_ord) },
                                &sibling_subst,
                                &dummy_dc,
                                &dummy_soa,
                            );
                            const new_fid = MovePathId.fromInt(@intCast(node_list.items.len));
                            const prev_first = node_list.items[cur_id.asInt()].first_child;
                            try node_list.append(arena_alloc, .{
                                .parent = cur_id,
                                .first_child = .none,
                                .next_sibling = prev_first,
                                .base_local = place_rec.base,
                                .proj_kind_raw = kind_raw,
                                .flags_raw = @bitCast(makeMovePathFlags(
                                    pool,
                                    sym_table,
                                    f_ty,
                                    &sibling_subst,
                                    is_behind_shared,
                                    is_deref_raw,
                                )),
                                .field_or_variant_ord = f_u16,
                            });
                            try type_list.append(arena_alloc, f_ty);
                            node_list.items[cur_id.asInt()].first_child = new_fid;
                            existing_f = new_fid;
                        }
                        if (f_u16 == ord_u16) matched_child = existing_f;
                    }
                    if (!matched_child.isNone()) {
                        cur_id = matched_child;
                    } else {
                        is_partial = true;
                    }
                } else if (total_fields == 0 and node_list.items.len < MAX_MOVE_PATHS) {
                    const new_id = MovePathId.fromInt(@intCast(node_list.items.len));
                    const prev_first = node_list.items[cur_id.asInt()].first_child;
                    try node_list.append(arena_alloc, .{
                        .parent = cur_id,
                        .first_child = .none,
                        .next_sibling = prev_first,
                        .base_local = place_rec.base,
                        .proj_kind_raw = kind_raw,
                        .flags_raw = @bitCast(makeMovePathFlags(
                            pool,
                            sym_table,
                            cur_ty,
                            &active_subst,
                            is_behind_shared,
                            is_deref_raw,
                        )),
                        .field_or_variant_ord = ord_u16,
                    });
                    try type_list.append(arena_alloc, cur_ty);
                    node_list.items[cur_id.asInt()].first_child = new_id;
                    cur_id = new_id;
                } else {
                    is_partial = true;
                }
            } else if (node_list.items.len < MAX_MOVE_PATHS) {
                const new_id = MovePathId.fromInt(@intCast(node_list.items.len));
                const prev_first = node_list.items[cur_id.asInt()].first_child;
                try node_list.append(arena_alloc, .{
                    .parent = cur_id,
                    .first_child = .none,
                    .next_sibling = prev_first,
                    .base_local = place_rec.base,
                    .proj_kind_raw = kind_raw,
                    .flags_raw = @bitCast(makeMovePathFlags(
                        pool,
                        sym_table,
                        cur_ty,
                        &active_subst,
                        is_behind_shared,
                        is_deref_raw,
                    )),
                    .field_or_variant_ord = ord_u16,
                });
                try type_list.append(arena_alloc, cur_ty);
                node_list.items[cur_id.asInt()].first_child = new_id;
                cur_id = new_id;
            } else {
                is_partial = true;
            }
        }

        place_map[pl_i] = .{ .id = cur_id, .is_partial = is_partial };
        place_leaf_types[pl_i] = cur_ty;
    }

    const total_paths = node_list.items.len;
    const subtree = try arena_alloc.alloc(DenseBitSet, total_paths);
    const ancestors = try arena_alloc.alloc(DenseBitSet, total_paths);
    const strict_anc = try arena_alloc.alloc(DenseBitSet, total_paths);
    const conflict = try arena_alloc.alloc(DenseBitSet, total_paths);

    for (0..total_paths) |m_idx| {
        subtree[m_idx] = try DenseBitSet.initEmpty(arena_alloc, total_paths);
        ancestors[m_idx] = try DenseBitSet.initEmpty(arena_alloc, total_paths);
        strict_anc[m_idx] = try DenseBitSet.initEmpty(arena_alloc, total_paths);
        conflict[m_idx] = try DenseBitSet.initEmpty(arena_alloc, total_paths);

        subtree[m_idx].set(m_idx);
        ancestors[m_idx].set(m_idx);
        var walk_anc = node_list.items[m_idx].parent;
        while (!walk_anc.isNone()) {
            ancestors[m_idx].set(walk_anc.asInt());
            strict_anc[m_idx].set(walk_anc.asInt());
            walk_anc = node_list.items[walk_anc.asInt()].parent;
        }
    }

    // Propagate `subtree[child]` upward into `subtree[parent]` in reverse creation order:
    var rev_i = total_paths;
    while (rev_i > 0) {
        rev_i -= 1;
        const parent_id = node_list.items[rev_i].parent;
        if (!parent_id.isNone()) {
            subtree[parent_id.asInt()].unionInPlace(subtree[rev_i]);
        }
    }

    for (0..total_paths) |m_idx| {
        conflict[m_idx].copyFrom(subtree[m_idx]);
        conflict[m_idx].unionInPlace(ancestors[m_idx]);
    }

    return .{
        .nodes = node_list.items,
        .node_types = type_list.items,
        .direct_local_limit = @intCast(direct_roots),
        .place_map = place_map,
        .place_leaf_types = place_leaf_types,
        .subtree = subtree,
        .ancestors = ancestors,
        .strict_anc = strict_anc,
        .conflict = conflict,
    };
}

/// Raw pointer validity lattice for scoped `unsafe` verification (`DR-06` §2.4).
const RawPtrState = enum(u2) {
    /// Non-raw-pointer value or uninitialized bottom (`0`).
    unknown_or_non_ptr = 0,
    /// Proven live non-null pointer derived from `&local` or guarded by `ptr != null` (`1`).
    valid_live = 1,
    /// Potentially null or unverified external raw pointer (`2` -> `E0303` on deref).
    maybe_null = 2,
    /// Explicitly freed or pointing to a dead stack frame local (`3` -> `E0301` on deref).
    freed_or_dangling = 3,

    /// Lattice join across CFG merge edges (`freed_or_dangling` > `maybe_null` > `valid_live`).
    inline fn join(lhs: RawPtrState, rhs: RawPtrState) RawPtrState {
        if (lhs == .unknown_or_non_ptr) return rhs;
        if (rhs == .unknown_or_non_ptr) return lhs;
        return if (@backingInt(lhs) >= @backingInt(rhs)) lhs else rhs;
    }
};

/// Symbolic region, NLL loan, `Context.scratch`, and raw-pointer provenance attached to SSA values & locals.
const ValueProvenance = struct {
    /// Bitmask of caller formal parameter ordinals `0..7` flowing into this value.
    param_mask: u8 = 0,
    /// Active `Context.scratch[0..2]` ping-pong borrow mask (`bits 0..1`).
    scratch_mask: u2 = 0,
    /// Raw pointer abstract validity state (for `.raw_ptr_ty` values).
    raw_ptr_state: RawPtrState = .unknown_or_non_ptr,
    /// Maximum symbolic `RegionDepth` (`0` static, `1` param, `2` caller arena, `3` frame, `4+` inner scope).
    max_depth: u16 = DEPTH_STATIC,
    /// Minimum target `RegionDepth` pointed to when this value is a mutable reference/pointer (`maxInt` = none).
    min_target_depth: u16 = std.math.maxInt(u16),
    /// Originating stack/arena `LocalId` when `max_depth >= DEPTH_FN_FRAME` (for `E0306` secondary spans).
    origin_local: LocalId = .none,
    /// Originating stack `LocalId` for `RawPtrState.valid_live` (invalidated at `ghost_storage_deinit`).
    raw_ptr_local: LocalId = .none,
    /// Bitset of active NLL `LoanId`s (`<= 64` inline `u64`, `> 64` arena-backed) carried by this value/view.
    loan_mask: DenseBitSet = DenseBitSet.EMPTY,
    /// Source token where a `Context.scratch` slice was borrowed (for `E0328` secondary span).
    scratch_open_token: TokenIndex = .none,

    /// Merges two `ValueProvenance` states conservatively inside `arena_alloc`.
    fn merge(
        lhs: ValueProvenance,
        rhs: ValueProvenance,
        arena_alloc: std.mem.Allocator,
    ) !ValueProvenance {
        const is_picking_rhs_depth = rhs.max_depth > lhs.max_depth;
        return .{
            .param_mask = lhs.param_mask | rhs.param_mask,
            .scratch_mask = lhs.scratch_mask | rhs.scratch_mask,
            .raw_ptr_state = RawPtrState.join(lhs.raw_ptr_state, rhs.raw_ptr_state),
            .max_depth = @max(lhs.max_depth, rhs.max_depth),
            .min_target_depth = @min(lhs.min_target_depth, rhs.min_target_depth),
            .origin_local = if (is_picking_rhs_depth)
                rhs.origin_local
            else if (!lhs.origin_local.isNone())
                lhs.origin_local
            else
                rhs.origin_local,
            .raw_ptr_local = if (!lhs.raw_ptr_local.isNone()) lhs.raw_ptr_local else rhs.raw_ptr_local,
            .loan_mask = try lhs.loan_mask.unionAlloc(rhs.loan_mask, arena_alloc),
            .scratch_open_token = if (!lhs.scratch_open_token.isNone())
                lhs.scratch_open_token
            else
                rhs.scratch_open_token,
        };
    }

    /// Returns `true` if `lhs` and `rhs` are identical.
    fn eql(lhs: ValueProvenance, rhs: ValueProvenance) bool {
        return lhs.param_mask == rhs.param_mask and
            lhs.scratch_mask == rhs.scratch_mask and
            lhs.raw_ptr_state == rhs.raw_ptr_state and
            lhs.max_depth == rhs.max_depth and
            lhs.min_target_depth == rhs.min_target_depth and
            lhs.origin_local == rhs.origin_local and
            lhs.raw_ptr_local == rhs.raw_ptr_local and
            lhs.loan_mask.eql(rhs.loan_mask);
    }
};

/// Metadata for a single tracked NLL borrow (`LoanId` `0..4095`) inside a `MirBody`.
const TrackedLoan = struct {
    /// Borrowed `MovePathId` in `MovePathTrie`.
    path_id: MovePathId,
    /// `true` if `PlacePathLookup.is_partial` was set at borrow creation.
    is_partial: bool,
    /// `true` for `&mut` / `inout` exclusive loans; `false` for `&` / `let` shared loans.
    is_mut: bool,
    /// `true` when `MAX_TRACKED_LOANS` saturated and this slot conservatively conflicts with every path.
    is_overflow_wildcard: bool = false,
    /// Non-zero (`0b01`/`0b10`/`0b11`) when this loan borrows a `Context.scratch[0..2]` arena slot (`D-04`).
    scratch_slot_mask: u2 = 0,
    /// Source token where the borrow was created (`&x`, `&mut x`, or view call).
    open_token: TokenIndex,
    /// Last reachable downstream SSA use token (for `E0305` secondary span!).
    last_use_token: TokenIndex = .none,
};

/// Result of intra-body region provenance and backward transitive NLL liveness analysis.
const BodyProvenanceHorizon = struct {
    /// Forward provenance per SSA `MirValueId` (`len == body.insts.len`).
    val_prov: []ValueProvenance,
    /// Forward provenance per `LocalId` (`len == body.locals.items.len`).
    local_prov: []ValueProvenance,
    /// Lexical declaration depth (`DEPTH_FN_FRAME + scope_nesting`) per `LocalId`.
    local_decl_depth: []u16,
    /// Tracked NLL loans (`0 .. loan_count - 1`, `loan_count <= MAX_TRACKED_LOANS`).
    loans: []TrackedLoan,
    /// Active NLL `loan_mask` (`DenseBitSet`) on entry to each basic block (`len == block_count`).
    live_loans_in: []DenseBitSet,
    /// Active NLL `loan_mask` (`DenseBitSet`) on exit from each basic block (`len == block_count`).
    live_loans_out: []DenseBitSet,
    /// Active `Context.scratch[0..2]` mask (`u2`) on entry to each basic block (`len == block_count`).
    live_scratch_in: []u2,
    /// Active `Context.scratch[0..2]` mask (`u2`) on exit from each basic block (`len == block_count`).
    live_scratch_out: []u2,
    /// Exact `LoanId` index minted per SSA instruction (`mir.NONE_U32` if none; `len == inst_count`).
    inst_minted_loan: []const u32,
    /// Exact `DenseBitSet` of `LoanId`s minted per `.call` site (`len == body.calls.items.len`).
    call_minted_mask: []const DenseBitSet,
};

/// Inspects `place_id` to detect `ctx.scratch[idx]` (`Context` field ordinal `1`), returning `0b01`, `0b10`, or `0b11`.
fn detectContextScratchAccess(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    place_id: PlaceId,
) u2 {
    if (place_id.asInt() >= body.places.items.len) return 0;
    const place_rec = body.places.items[place_id.asInt()];
    if (place_rec.base >= body.locals.items.len) return 0;
    if (!type_system.isContextType(pool, sym_table, body.locals.items[place_rec.base].type_id)) return 0;

    const projs = body.getPlaceProjections(place_id);
    var has_scratch_field = false;
    for (projs) |proj| {
        if (proj.kind == .field and
            proj.payload == ContextFieldLayout.CANONICAL_FIELDS[1].slot_ordinal)
        {
            has_scratch_field = true;
        } else if (has_scratch_field and proj.kind == .index) {
            if (proj.payload < body.insts.len) {
                const idx_inst = body.getInst(MirValueId.fromInt(proj.payload));
                if (idx_inst.op == .const_scalar and idx_inst.operands.lhs < body.consts.items.len) {
                    const mc = body.consts.items[idx_inst.operands.lhs];
                    if (mc == .int_val) {
                        if (mc.int_val == 0) return 0b01;
                        if (mc.int_val == 1) return 0b10;
                    }
                }
            }
            return 0b11;
        }
    }
    return if (has_scratch_field) 0b11 else 0;
}

/// Resolves the `FnRegionSummary` of a direct callee `(def_id, sym_idx)` from finalized SCC slots or `config`.
fn lookupCalleeSummary(
    def_id: DefId,
    sym_idx: SymbolIndex,
    summaries: []const FnRegionSummary,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    config: SastConfig,
) !?FnRegionSummary {
    if (!def_id.isNone()) {
        if (key_to_slot.get(def_id.asInt())) |slot| {
            return summaries[slot];
        }
    }
    if (!sym_idx.isNone()) {
        if (sym_to_slot.get(sym_idx.asInt())) |slot| {
            return summaries[slot];
        }
    }
    if (!def_id.isNone() or !sym_idx.isNone()) {
        if (config.external_resolver) |ext| {
            if (try ext.resolve_fn(ext.compiler_db, ext.summary_map, def_id, sym_idx)) |resolved| {
                return resolved;
            }
        }
    }
    return null;
}

/// Collects SSA `MirValueId` operands read by `inst` (appending up to `out_buf.len` values).
fn collectInstReadValues(body: *const MirBody, inst: MirInst, out_buf: *std.ArrayListUnmanaged(u32), alloc: std.mem.Allocator) !void {
    switch (inst.op) {
        .block_param,
        .ghost_storage_init,
        .ghost_storage_deinit,
        .const_scalar,
        .fn_addr,
        => {},
        .ghost_access_let,
        .ghost_access_inout,
        .ghost_access_set,
        .ghost_storage_move,
        .place_load,
        .place_discriminant,
        .place_set_discrim,
        .place_addr,
        .soa_column_slice,
        => {
            if (inst.operands.lhs < body.places.items.len) {
                for (body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs))) |proj| {
                    if (proj.kind == .index and proj.payload != mir.NONE_U32) {
                        try out_buf.append(alloc, proj.payload);
                    }
                }
            }
        },
        .place_store => {
            if (inst.operands.lhs < body.places.items.len) {
                for (body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs))) |proj| {
                    if (proj.kind == .index and proj.payload != mir.NONE_U32) {
                        try out_buf.append(alloc, proj.payload);
                    }
                }
            }
            if (inst.operands.rhs != mir.NONE_U32) try out_buf.append(alloc, inst.operands.rhs);
        },
        .ghost_access_end => {},
        .copy_val, .unary_op, .aggregate_extract, .bitfield_extract => {
            if (inst.operands.lhs != mir.NONE_U32) try out_buf.append(alloc, inst.operands.lhs);
        },
        .bin_op => {
            if (inst.operands.lhs != mir.NONE_U32) try out_buf.append(alloc, inst.operands.lhs);
            if (inst.operands.rhs != mir.NONE_U32) try out_buf.append(alloc, inst.operands.rhs);
        },
        .aggregate_insert => {
            if (inst.operands.lhs != mir.NONE_U32) try out_buf.append(alloc, inst.operands.lhs);
            if (inst.operands.rhs + 2 <= body.extra_args.items.len) {
                try out_buf.append(alloc, body.extra_args.items[inst.operands.rhs + 1]);
            }
        },
        .bitfield_insert => {
            if (inst.operands.lhs + 2 <= body.extra_args.items.len) {
                try out_buf.append(alloc, body.extra_args.items[inst.operands.lhs]);
                try out_buf.append(alloc, body.extra_args.items[inst.operands.lhs + 1]);
            }
        },
        .aggregate_make => {
            const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            switch (agg_kind) {
                .array_repeat => {
                    if (inst.operands.lhs != mir.NONE_U32) try out_buf.append(alloc, inst.operands.lhs);
                },
                .tagged_variant => {
                    const elem_len = inst.operands.rhs & 0xFFFF;
                    for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elem_len]) |val_raw| {
                        if (val_raw != mir.NONE_U32) try out_buf.append(alloc, val_raw);
                    }
                },
                .closure_make => {
                    if (inst.operands.rhs < body.extra_args.items.len) {
                        const cap_len = body.extra_args.items[inst.operands.rhs];
                        const cap_start = inst.operands.rhs + 1;
                        for (body.extra_args.items[cap_start .. cap_start + cap_len]) |val_raw| {
                            if (val_raw != mir.NONE_U32) try out_buf.append(alloc, val_raw);
                        }
                    }
                },
                .tuple_agg, .struct_agg, .array_elems, .str_concat => {
                    for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |val_raw| {
                        if (val_raw != mir.NONE_U32) try out_buf.append(alloc, val_raw);
                    }
                },
            }
        },
        .intrinsic_op => {
            const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
            if (ikind.hasPlaceInLhs()) {
                if (ikind.hasSsaFlagInRhs() and inst.operands.rhs != mir.NONE_U32) {
                    try out_buf.append(alloc, inst.operands.rhs);
                }
            } else if (ikind.hasExtraArgs() and inst.operands.rhs > 0) {
                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |val_raw| {
                    if (val_raw != mir.NONE_U32) try out_buf.append(alloc, val_raw);
                }
            }
        },
    }
}

/// Sets `loan_idx` inside `mask`, upgrading inline `u64` storage into `arena_alloc` when `loan_count > 64`.
fn setLoanBitAlloc(
    mask: *DenseBitSet,
    loan_idx: usize,
    loan_count: usize,
    arena_alloc: std.mem.Allocator,
) !void {
    if (mask.* == .inline_words and loan_idx >= 64) {
        var expanded = try DenseBitSet.initEmpty(arena_alloc, @max(loan_count, loan_idx + 1));
        expanded.copyFrom(mask.*);
        mask.* = expanded;
    }
    mask.set(loan_idx);
}

/// Appends a `TrackedLoan` or coalesces into the fail-closed wildcard slot when `MAX_TRACKED_LOANS` saturates.
fn mintOrCoarsenLoan(
    loan_list: *std.ArrayListUnmanaged(TrackedLoan),
    arena_alloc: std.mem.Allocator,
    lookup: PlacePathLookup,
    is_mut: bool,
    scratch_slot_mask: u2,
    open_token: TokenIndex,
) !u32 {
    if (loan_list.items.len < MAX_TRACKED_LOANS - 1) {
        const lid_idx: u32 = @intCast(loan_list.items.len);
        try loan_list.append(arena_alloc, .{
            .path_id = lookup.id,
            .is_partial = lookup.is_partial,
            .is_mut = is_mut,
            .is_overflow_wildcard = false,
            .scratch_slot_mask = scratch_slot_mask,
            .open_token = open_token,
        });
        return lid_idx;
    }
    if (loan_list.items.len == MAX_TRACKED_LOANS - 1) {
        const wild_idx: u32 = @intCast(loan_list.items.len);
        try loan_list.append(arena_alloc, .{
            .path_id = .none,
            .is_partial = true,
            .is_mut = true,
            .is_overflow_wildcard = true,
            .open_token = open_token,
        });
        return wild_idx;
    }
    loan_list.items[MAX_TRACKED_LOANS - 1].is_mut = true;
    loan_list.items[MAX_TRACKED_LOANS - 1].is_overflow_wildcard = true;
    return @intCast(MAX_TRACKED_LOANS - 1);
}

/// Computes intra-body region depths, `LoanId` provenance, and backward transitive NLL liveness.
fn computeBodyProvenanceAndNllHorizon(
    arena_alloc: std.mem.Allocator,
    body: *const MirBody,
    dom: *const DominatorTree,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    summaries: []const FnRegionSummary,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    config: SastConfig,
) !BodyProvenanceHorizon {
    const inst_count = body.insts.len;
    const local_count = body.locals.items.len;
    const block_count = body.blocks.items.len;

    const val_prov = try arena_alloc.alloc(ValueProvenance, inst_count);
    @memset(val_prov, .{});

    const local_prov = try arena_alloc.alloc(ValueProvenance, local_count);
    @memset(local_prov, .{});

    const local_decl_depth = try arena_alloc.alloc(u16, local_count);
    @memset(local_decl_depth, DEPTH_FN_FRAME);

    const has_exact_scope_depths = body.local_scope_depths.items.len == local_count;

    // [1] Initialize formal parameter provenance and true lexical `scope_depth` per local:
    for (body.locals.items, 0..) |loc, loc_i| {
        if (loc_i == 0) {
            local_decl_depth[0] = DEPTH_CALLER_PARAM;
            continue;
        }
        const lid = LocalId.fromInt(@intCast(loc_i));
        const unwrapped_ty = pool.unwrapUnderlyingType(loc.type_id);
        const is_raw_ptr = !unwrapped_ty.isError() and pool.getNode(unwrapped_ty).tag == .raw_ptr_ty;

        if (loc.flags().is_arg) {
            const param_ord: usize = loc_i - 1;
            const param_bit: u8 = if (param_ord < 8) (@as(u8, 1) << @intCast(param_ord)) else 0;
            const is_caller_arena = isArenaType(pool, sym_table, loc.type_id);
            const param_depth: u16 = if (is_caller_arena) DEPTH_CALLER_ARENA else DEPTH_CALLER_PARAM;
            local_decl_depth[loc_i] = param_depth;
            local_prov[loc_i] = .{
                .param_mask = param_bit,
                .max_depth = param_depth,
                .min_target_depth = param_depth,
                .raw_ptr_state = if (is_raw_ptr) .maybe_null else .unknown_or_non_ptr,
            };
        } else {
            var decl_d: u16 = DEPTH_FN_FRAME;
            if (has_exact_scope_depths) {
                const raw_sd = body.local_scope_depths.items[loc_i];
                if (raw_sd > 0) decl_d = (DEPTH_FN_FRAME - 1) +| raw_sd;
            } else if (loc.region_raw != 0) {
                decl_d = @max(decl_d, DEPTH_LOCAL_REGION_BASE +| (loc.region_raw - 1));
            }
            local_decl_depth[loc_i] = decl_d;
            if (loc.flags().is_local_closure) {
                local_prov[loc_i].max_depth = decl_d;
                local_prov[loc_i].origin_local = lid;
            }
        }
    }

    // Dominator-tree scope-stack fallback for synthetic `MirBody` fixtures lacking `local_scope_depths`:
    if (!has_exact_scope_depths and block_count > 0) {
        const bb_exit_depth = try arena_alloc.alloc(u16, block_count);
        @memset(bb_exit_depth, 0);
        for (dom.rpo_blocks) |bb_idx| {
            const bb_id = MirBlockId.fromInt(bb_idx);
            var cur_sd: u16 = if (bb_idx == 0)
                0
            else if (dom.idom[bb_idx] < block_count)
                bb_exit_depth[dom.idom[bb_idx]]
            else
                0;
            if (!body.blocks.items[bb_idx].isCleanupPad()) {
                for (body.getBlockInsts(bb_id)) |inst_val| {
                    const inst = body.getInst(inst_val);
                    if (inst.op == .ghost_storage_init and inst.operands.lhs < local_count) {
                        const lid_idx = inst.operands.lhs;
                        const loc = body.locals.items[lid_idx];
                        if (!loc.flags().is_arg and !loc.flags().is_return_slot and !loc.flags().is_synthetic_temp) {
                            local_decl_depth[lid_idx] = @max(local_decl_depth[lid_idx], DEPTH_FN_FRAME +| cur_sd);
                            if (loc.flags().is_local_closure) {
                                local_prov[lid_idx].max_depth = local_decl_depth[lid_idx];
                            }
                            cur_sd +|= 1;
                        }
                    } else if (inst.op == .ghost_storage_deinit and inst.operands.lhs < local_count) {
                        const loc = body.locals.items[inst.operands.lhs];
                        if (!loc.flags().is_arg and !loc.flags().is_return_slot and !loc.flags().is_synthetic_temp) {
                            if (cur_sd > 0) cur_sd -= 1;
                        }
                    }
                }
            }
            bb_exit_depth[bb_idx] = cur_sd;
        }
    }

    // [2] Mint `LoanId`s (`<= MAX_TRACKED_LOANS`) for `place_addr`, `soa_column_slice`, and view calls:
    var loan_list: std.ArrayListUnmanaged(TrackedLoan) = .empty;
    const inst_minted_loan = try arena_alloc.alloc(u32, inst_count);
    @memset(inst_minted_loan, mir.NONE_U32);

    const call_minted_mask = try arena_alloc.alloc(DenseBitSet, body.calls.items.len);
    @memset(call_minted_mask, DenseBitSet.EMPTY);

    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        for (body.getBlockInsts(bb_id)) |inst_val| {
            const inst = body.getInst(inst_val);
            const tok = body.origin_tokens.items[inst_val.asInt()];
            if ((inst.op == .place_addr or inst.op == .soa_column_slice) and
                inst.operands.lhs < trie.place_map.len)
            {
                const lookup = trie.place_map[inst.operands.lhs];
                const scratch_bits = detectContextScratchAccess(
                    body,
                    pool,
                    sym_table,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                const lid_idx = try mintOrCoarsenLoan(
                    &loan_list,
                    arena_alloc,
                    lookup,
                    inst.op == .place_addr and inst.operands.rhs != 0,
                    scratch_bits,
                    tok,
                );
                inst_minted_loan[inst_val.asInt()] = lid_idx;
            }
        }

        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .call and term.cond_or_val < body.calls.items.len) {
            const call_idx = term.cond_or_val;
            const call_site = body.calls.items[call_idx];
            const callee_sum_opt = try lookupCalleeSummary(
                call_site.direct_def_id,
                call_site.direct_symbol,
                summaries,
                key_to_slot,
                sym_to_slot,
                config,
            );
            const has_ret_prov = hasProvenanceCarrier(pool, sym_table, call_site.ret_ty);
            const ret_mask: u64 = if (callee_sum_opt) |csum|
                csum.ret_provenance_mask
            else if (has_ret_prov)
                0xFFFF_FFFF_FFFF_FFFF
            else
                0;

            if (ret_mask != 0 and call_site.call_borrows_len > 0) {
                var bor_cursor: usize = 0;
                for (0..call_site.args_len) |arg_i| {
                    if (bor_cursor >= call_site.call_borrows_len) break;
                    const ghost_raw = body.extra_args.items[call_site.call_borrows_start + bor_cursor];
                    if (ghost_raw >= inst_count) {
                        bor_cursor += 1;
                        continue;
                    }
                    const ghost_inst = body.getInst(MirValueId.fromInt(ghost_raw));
                    if (!ghost_inst.op.isGhostAccessOpen() or ghost_inst.operands.lhs >= trie.place_map.len) {
                        bor_cursor += 1;
                        continue;
                    }
                    const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                    const word = body.extra_args.items[call_site.args_start + arg_i];
                    const is_matching_arg = switch (mode) {
                        .inout_mode => ghost_inst.op == .ghost_access_inout and ghost_inst.operands.lhs == word,
                        .set_mode => ghost_inst.op == .ghost_access_set and ghost_inst.operands.lhs == word,
                        .let_mode => blk: {
                            if (ghost_inst.op != .ghost_access_let) break :blk false;
                            const peeled_w = peelCopyValId(body, word);
                            if (peeled_w >= inst_count) break :blk false;
                            const arg_inst = body.getInst(MirValueId.fromInt(peeled_w));
                            break :blk arg_inst.op == .place_load and
                                arg_inst.operands.lhs == ghost_inst.operands.lhs;
                        },
                        .sink_mode => false,
                    };
                    if (!is_matching_arg) continue;
                    bor_cursor += 1;

                    const has_arg_flow_to_ret = (arg_i < 64 and ((ret_mask >> @intCast(arg_i)) & 1) != 0) or
                        (callee_sum_opt == null and arg_i == 0 and has_ret_prov and
                            isArenaArgPlaceOrVal(body, pool, sym_table, mode, word));
                    if (!has_arg_flow_to_ret) continue;

                    const lookup = trie.place_map[ghost_inst.operands.lhs];
                    const scratch_bits = detectContextScratchAccess(
                        body,
                        pool,
                        sym_table,
                        PlaceId.fromInt(ghost_inst.operands.lhs),
                    );
                    const lid_idx = try mintOrCoarsenLoan(
                        &loan_list,
                        arena_alloc,
                        lookup,
                        ghost_inst.op == .ghost_access_inout,
                        scratch_bits,
                        call_site.origin_token,
                    );
                    try setLoanBitAlloc(&call_minted_mask[call_idx], lid_idx, loan_list.items.len, arena_alloc);
                }

                // Fallback for synthetic `MirBody` fixtures with unmatched `call_borrows` entries:
                while (bor_cursor < call_site.call_borrows_len) : (bor_cursor += 1) {
                    const is_kept = if (call_site.call_borrows_len == call_site.args_len and bor_cursor < 64)
                        ((ret_mask >> @intCast(bor_cursor)) & 1) != 0
                    else
                        callee_sum_opt == null;
                    if (!is_kept) continue;
                    const ghost_raw = body.extra_args.items[call_site.call_borrows_start + bor_cursor];
                    if (ghost_raw >= inst_count) continue;
                    const ghost_inst = body.getInst(MirValueId.fromInt(ghost_raw));
                    if (!ghost_inst.op.isGhostAccessOpen() or ghost_inst.operands.lhs >= trie.place_map.len) continue;
                    const lookup = trie.place_map[ghost_inst.operands.lhs];
                    const scratch_bits = detectContextScratchAccess(
                        body,
                        pool,
                        sym_table,
                        PlaceId.fromInt(ghost_inst.operands.lhs),
                    );
                    const lid_idx = try mintOrCoarsenLoan(
                        &loan_list,
                        arena_alloc,
                        lookup,
                        ghost_inst.op == .ghost_access_inout,
                        scratch_bits,
                        call_site.origin_token,
                    );
                    try setLoanBitAlloc(&call_minted_mask[call_idx], lid_idx, loan_list.items.len, arena_alloc);
                }
            }
        }
    }

    const loan_count = loan_list.items.len;

    // [3] Forward fixed-point propagation of `ValueProvenance` across SSA & local slots:
    const prov_iter_cap: usize = @max(@as(usize, 64), block_count * 4);
    var iter: usize = 0;
    var has_prov_changed = true;
    while (has_prov_changed and iter < prov_iter_cap) : (iter += 1) {
        has_prov_changed = false;
        for (dom.rpo_blocks) |bb_idx| {
            const bb_id = MirBlockId.fromInt(bb_idx);

            // Merge incoming edge arguments into `block_param`s:
            const params = body.getBlockParams(bb_id);
            if (params.len > 0) {
                for (body.getPredEdges(bb_id)) |pred_eid| {
                    const edge = body.extra_edges.items[pred_eid.asInt()];
                    if (!dom.isReachable(edge.src_bb)) continue;
                    const src_term = body.blocks.items[edge.src_bb.asInt()].terminator;
                    if (src_term.kind == .call) continue; // `.call` `normal_bb` param handled at `.call`.
                    const copy_n = @min(params.len, edge.args_len);
                    for (0..copy_n) |p_i| {
                        const arg_raw = body.extra_args.items[edge.args_start + p_i];
                        if (arg_raw >= inst_count) continue;
                        const merged = try ValueProvenance.merge(
                            val_prov[params[p_i].asInt()],
                            val_prov[arg_raw],
                            arena_alloc,
                        );
                        if (!ValueProvenance.eql(merged, val_prov[params[p_i].asInt()])) {
                            val_prov[params[p_i].asInt()] = merged;
                            has_prov_changed = true;
                        }
                    }
                }
            }

            for (body.getBlockInsts(bb_id)) |inst_val| {
                const val_idx = inst_val.asInt();
                const inst = body.getInst(inst_val);
                const tok = body.origin_tokens.items[val_idx];
                var next_p = val_prov[val_idx];

                switch (inst.op) {
                    .const_scalar => {
                        const unwrapped = pool.unwrapUnderlyingType(inst.type_id);
                        if (!unwrapped.isError() and pool.getNode(unwrapped).tag == .raw_ptr_ty) {
                            if (inst.operands.lhs < body.consts.items.len and
                                body.consts.items[inst.operands.lhs] == .int_val and
                                body.consts.items[inst.operands.lhs].int_val == 0)
                            {
                                next_p.raw_ptr_state = .maybe_null;
                            }
                        }
                    },
                    .copy_val => {
                        if (inst.operands.lhs < inst_count) {
                            next_p = try ValueProvenance.merge(next_p, val_prov[inst.operands.lhs], arena_alloc);
                        }
                    },
                    .unary_op => {
                        if (inst.operands.lhs < inst_count) {
                            const uop: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                            const src_p = val_prov[inst.operands.lhs];
                            if (uop == .ptr_cast or uop == .bitcast_op or uop == .ssa_variant_payload) {
                                next_p = try ValueProvenance.merge(next_p, src_p, arena_alloc);
                                const dst_unwrapped = pool.unwrapUnderlyingType(inst.type_id);
                                if (!dst_unwrapped.isError() and pool.getNode(dst_unwrapped).tag == .raw_ptr_ty and
                                    next_p.raw_ptr_state == .unknown_or_non_ptr)
                                {
                                    const src_ty = pool.unwrapUnderlyingType(
                                        body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id,
                                    );
                                    if (!src_ty.isError() and
                                        (pool.getNode(src_ty).tag == .ref_ty or pool.getNode(src_ty).tag == .mut_ref_ty))
                                    {
                                        next_p.raw_ptr_state = .valid_live;
                                        next_p.raw_ptr_local = src_p.origin_local;
                                    } else {
                                        next_p.raw_ptr_state = .maybe_null;
                                    }
                                }
                            }
                        }
                    },
                    .place_addr, .soa_column_slice => {
                        if (inst.operands.lhs < body.places.items.len) {
                            const place_rec = body.places.items[inst.operands.lhs];
                            if (place_rec.base < local_count) {
                                const base_lid = LocalId.fromInt(place_rec.base);
                                const projs = body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs));
                                const base_unwrapped = pool.unwrapUnderlyingType(
                                    body.locals.items[place_rec.base].type_id,
                                );
                                const is_base_slice = !base_unwrapped.isError() and
                                    (pool.getNode(base_unwrapped).tag == .slice_ty or
                                        pool.getNode(base_unwrapped).tag == .soa_slice_ty);
                                const is_borrowing_pointee = (projs.len > 0 and projs[0].kind == .deref) or
                                    (is_base_slice and (inst.op == .soa_column_slice or
                                        (projs.len > 0 and (projs[0].kind == .index or projs[0].kind == .soa_elem))));

                                if (is_borrowing_pointee) {
                                    next_p = try ValueProvenance.merge(
                                        next_p,
                                        local_prov[place_rec.base],
                                        arena_alloc,
                                    );
                                } else {
                                    const base_depth = local_decl_depth[place_rec.base];
                                    next_p.max_depth = @max(next_p.max_depth, base_depth);
                                    const unwrapped = pool.unwrapUnderlyingType(inst.type_id);
                                    const is_raw_ptr_addr = !unwrapped.isError() and
                                        pool.getNode(unwrapped).tag == .raw_ptr_ty;
                                    if ((inst.op == .place_addr and inst.operands.rhs != 0) or is_raw_ptr_addr) {
                                        next_p.min_target_depth = @min(next_p.min_target_depth, base_depth);
                                    }
                                    if (local_prov[place_rec.base].param_mask != 0) {
                                        next_p.param_mask |= local_prov[place_rec.base].param_mask;
                                    }
                                    if (base_depth >= DEPTH_FN_FRAME) {
                                        next_p.origin_local = base_lid;
                                    }
                                    if (is_raw_ptr_addr) {
                                        next_p.raw_ptr_state = .valid_live;
                                        next_p.raw_ptr_local = base_lid;
                                    } else {
                                        next_p.raw_ptr_local = base_lid;
                                    }
                                }

                                const scratch_m = detectContextScratchAccess(
                                    body,
                                    pool,
                                    sym_table,
                                    PlaceId.fromInt(inst.operands.lhs),
                                );
                                if (scratch_m != 0) {
                                    next_p.scratch_mask |= scratch_m;
                                    if (next_p.scratch_open_token.isNone()) next_p.scratch_open_token = tok;
                                }
                                const minted = inst_minted_loan[val_idx];
                                if (minted != mir.NONE_U32) {
                                    try setLoanBitAlloc(&next_p.loan_mask, minted, loan_count, arena_alloc);
                                }
                            }
                        }
                    },
                    .place_load => {
                        if (inst.operands.lhs < body.places.items.len and
                            hasProvenanceCarrier(pool, sym_table, inst.type_id))
                        {
                            const place_rec = body.places.items[inst.operands.lhs];
                            if (place_rec.base < local_count) {
                                next_p = try ValueProvenance.merge(
                                    next_p,
                                    local_prov[place_rec.base],
                                    arena_alloc,
                                );
                            }
                        }
                    },
                    .place_store => {
                        if (inst.operands.lhs < body.places.items.len and inst.operands.rhs < inst_count) {
                            const place_rec = body.places.items[inst.operands.lhs];
                            if (place_rec.base < local_count) {
                                const projs = body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs));
                                const has_leading_deref = projs.len > 0 and projs[0].kind == .deref;
                                if (!has_leading_deref) {
                                    const merged_loc = try ValueProvenance.merge(
                                        local_prov[place_rec.base],
                                        val_prov[inst.operands.rhs],
                                        arena_alloc,
                                    );
                                    if (!ValueProvenance.eql(merged_loc, local_prov[place_rec.base])) {
                                        local_prov[place_rec.base] = merged_loc;
                                        has_prov_changed = true;
                                    }
                                }
                            }
                        }
                    },
                    .aggregate_make => {
                        const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        if (inst.flags.is_local_closure) {
                            next_p.max_depth = @max(next_p.max_depth, DEPTH_FN_FRAME);
                        }
                        switch (agg_kind) {
                            .array_repeat => {
                                if (inst.operands.lhs < inst_count) {
                                    next_p = try ValueProvenance.merge(
                                        next_p,
                                        val_prov[inst.operands.lhs],
                                        arena_alloc,
                                    );
                                }
                            },
                            .tagged_variant => {
                                const elem_len = inst.operands.rhs & 0xFFFF;
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + elem_len]) |v_raw| {
                                    if (v_raw < inst_count) {
                                        next_p = try ValueProvenance.merge(next_p, val_prov[v_raw], arena_alloc);
                                    }
                                }
                            },
                            .closure_make => {
                                if (inst.operands.rhs < body.extra_args.items.len) {
                                    const cap_len = body.extra_args.items[inst.operands.rhs];
                                    const cap_start = inst.operands.rhs + 1;
                                    for (body.extra_args.items[cap_start .. cap_start + cap_len]) |v_raw| {
                                        if (v_raw < inst_count) {
                                            next_p = try ValueProvenance.merge(next_p, val_prov[v_raw], arena_alloc);
                                        }
                                    }
                                }
                            },
                            .tuple_agg, .struct_agg, .array_elems, .str_concat => {
                                for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |v_raw| {
                                    if (v_raw < inst_count) {
                                        next_p = try ValueProvenance.merge(next_p, val_prov[v_raw], arena_alloc);
                                    }
                                }
                            },
                        }
                    },
                    .aggregate_extract => {
                        if (inst.operands.lhs < inst_count and
                            hasProvenanceCarrier(pool, sym_table, inst.type_id))
                        {
                            next_p = try ValueProvenance.merge(next_p, val_prov[inst.operands.lhs], arena_alloc);
                        }
                    },
                    .aggregate_insert => {
                        if (inst.operands.lhs < inst_count) {
                            next_p = try ValueProvenance.merge(next_p, val_prov[inst.operands.lhs], arena_alloc);
                        }
                        if (inst.operands.rhs + 2 <= body.extra_args.items.len) {
                            const inserted_raw = body.extra_args.items[inst.operands.rhs + 1];
                            if (inserted_raw < inst_count) {
                                next_p = try ValueProvenance.merge(next_p, val_prov[inserted_raw], arena_alloc);
                            }
                        }
                    },
                    .intrinsic_op => {
                        const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                        if (ikind == .as_bytes or ikind == .view_bytes or ikind == .from_bytes) {
                            if (inst.operands.rhs > 0 and inst.operands.lhs < body.extra_args.items.len) {
                                const src_v = body.extra_args.items[inst.operands.lhs];
                                if (src_v < inst_count) {
                                    next_p = try ValueProvenance.merge(next_p, val_prov[src_v], arena_alloc);
                                }
                            }
                        }
                    },
                    else => {},
                }

                if (!ValueProvenance.eql(next_p, val_prov[val_idx])) {
                    val_prov[val_idx] = next_p;
                    has_prov_changed = true;
                }
            }

            // Propagate `.call` return provenance & `param_flow_matrix` into `normal_bb`'s `%ret_val`:
            const term = body.blocks.items[bb_idx].terminator;
            if (term.kind == .call and term.cond_or_val < body.calls.items.len and term.edge_len >= 1) {
                const call_idx = term.cond_or_val;
                const call_site = body.calls.items[call_idx];
                const normal_bb = body.extra_edges.items[term.edge_start].target_bb;
                const normal_params = body.getBlockParams(normal_bb);
                if (normal_params.len >= 1) {
                    const ret_val_id = normal_params[0];
                    var ret_p = val_prov[ret_val_id.asInt()];
                    ret_p.loan_mask = try ret_p.loan_mask.unionAlloc(call_minted_mask[call_idx], arena_alloc);

                    const callee_sum_opt = try lookupCalleeSummary(
                        call_site.direct_def_id,
                        call_site.direct_symbol,
                        summaries,
                        key_to_slot,
                        sym_to_slot,
                        config,
                    );
                    const has_ret_prov = hasProvenanceCarrier(pool, sym_table, call_site.ret_ty);
                    const ret_mask: u64 = if (callee_sum_opt) |csum|
                        csum.ret_provenance_mask
                    else if (has_ret_prov)
                        0xFFFF_FFFF_FFFF_FFFF
                    else
                        0;

                    for (0..call_site.args_len) |arg_i| {
                        const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                        const word = body.extra_args.items[call_site.args_start + arg_i];
                        var arg_p = ValueProvenance{};
                        if (mode == .let_mode or mode == .sink_mode) {
                            if (word < inst_count) arg_p = val_prov[word];
                        } else if (word < body.places.items.len) {
                            const pl_rec = body.places.items[word];
                            if (pl_rec.base < local_count) {
                                arg_p = local_prov[pl_rec.base];
                                arg_p.max_depth = @max(arg_p.max_depth, local_decl_depth[pl_rec.base]);
                                if (mode == .inout_mode or mode == .set_mode) {
                                    arg_p.min_target_depth = @min(
                                        arg_p.min_target_depth,
                                        local_decl_depth[pl_rec.base],
                                    );
                                }
                                if (local_decl_depth[pl_rec.base] >= DEPTH_FN_FRAME) {
                                    arg_p.origin_local = LocalId.fromInt(pl_rec.base);
                                }
                                const scratch_m = detectContextScratchAccess(
                                    body,
                                    pool,
                                    sym_table,
                                    PlaceId.fromInt(word),
                                );
                                if (scratch_m != 0) {
                                    arg_p.scratch_mask |= scratch_m;
                                    arg_p.scratch_open_token = call_site.origin_token;
                                }
                            }
                        }

                        if (arg_i < 64 and ((ret_mask >> @intCast(arg_i)) & 1) != 0) {
                            ret_p = try ValueProvenance.merge(ret_p, arg_p, arena_alloc);
                        } else if (arg_p.scratch_mask != 0 and
                            has_ret_prov and
                            !isScratchResetCall(sym_table, call_site))
                        {
                            ret_p.scratch_mask |= arg_p.scratch_mask;
                            if (ret_p.scratch_open_token.isNone()) {
                                ret_p.scratch_open_token = call_site.origin_token;
                            }
                        } else if (arg_i == 0 and isArenaArgPlaceOrVal(body, pool, sym_table, mode, word) and
                            has_ret_prov)
                        {
                            ret_p = try ValueProvenance.merge(ret_p, arg_p, arena_alloc);
                        }
                    }

                    // Special-case `scratch_scope(&mut ctx, conflict_mask)` -> selects complement `1 - i`:
                    if (isScratchScopeHelperCall(sym_table, call_site) and call_site.args_len >= 2) {
                        const mask_arg_mode = body.call_arg_modes.items[call_site.modes_start + 1];
                        const mask_word = body.extra_args.items[call_site.args_start + 1];
                        if ((mask_arg_mode == .let_mode or mask_arg_mode == .sink_mode) and mask_word < inst_count) {
                            const conflict_bits = extractConstSmallU2(body, MirValueId.fromInt(mask_word)) orelse
                                val_prov[mask_word].scratch_mask;
                            ret_p.scratch_mask = switch (conflict_bits) {
                                0b01 => 0b10,
                                0b10 => 0b01,
                                else => 0b01,
                            };
                            ret_p.scratch_open_token = call_site.origin_token;
                        }
                    }

                    const unwrapped_ret = pool.unwrapUnderlyingType(call_site.ret_ty);
                    if (!unwrapped_ret.isError() and pool.getNode(unwrapped_ret).tag == .raw_ptr_ty and
                        ret_p.raw_ptr_state == .unknown_or_non_ptr)
                    {
                        ret_p.raw_ptr_state = .maybe_null;
                    }

                    if (!ValueProvenance.eql(ret_p, val_prov[ret_val_id.asInt()])) {
                        val_prov[ret_val_id.asInt()] = ret_p;
                        has_prov_changed = true;
                    }
                }

                // Propagate `param_flow_matrix` (`src * 8 + dst`) from `src_arg` into local `dst_arg` containers:
                const flow_callee_opt = try lookupCalleeSummary(
                    call_site.direct_def_id,
                    call_site.direct_symbol,
                    summaries,
                    key_to_slot,
                    sym_to_slot,
                    config,
                );
                if (flow_callee_opt) |csum| {
                    if (csum.param_flow_matrix != 0) {
                        const lim = @min(@as(usize, call_site.args_len), 8);
                        for (0..lim) |dst_i| {
                            const dst_mode = body.call_arg_modes.items[call_site.modes_start + dst_i];
                            const dst_word = body.extra_args.items[call_site.args_start + dst_i];
                            const dst_base_opt: ?u32 = blk: {
                                if (dst_mode == .inout_mode or dst_mode == .set_mode) {
                                    if (dst_word < body.places.items.len) {
                                        const d_rec = body.places.items[dst_word];
                                        const d_projs = body.getPlaceProjections(PlaceId.fromInt(dst_word));
                                        if (d_projs.len == 0 or d_projs[0].kind != .deref) break :blk d_rec.base;
                                    }
                                } else if (dst_word < inst_count) {
                                    const d_inst = body.getInst(MirValueId.fromInt(dst_word));
                                    if (d_inst.op == .place_addr and d_inst.operands.rhs != 0 and
                                        d_inst.operands.lhs < body.places.items.len)
                                    {
                                        const d_rec = body.places.items[d_inst.operands.lhs];
                                        const d_projs = body.getPlaceProjections(PlaceId.fromInt(d_inst.operands.lhs));
                                        if (d_projs.len == 0 or d_projs[0].kind != .deref) break :blk d_rec.base;
                                    }
                                }
                                break :blk null;
                            };
                            const dst_base = dst_base_opt orelse continue;
                            if (dst_base >= local_count) continue;
                            for (0..lim) |src_i| {
                                if (src_i == dst_i) continue;
                                if (((csum.param_flow_matrix >> @intCast(src_i * 8 + dst_i)) & 1) == 0) continue;
                                const src_mode = body.call_arg_modes.items[call_site.modes_start + src_i];
                                const src_word = body.extra_args.items[call_site.args_start + src_i];
                                var src_p = ValueProvenance{};
                                if (src_mode == .let_mode or src_mode == .sink_mode) {
                                    if (src_word < inst_count) src_p = val_prov[src_word];
                                } else if (src_word < body.places.items.len) {
                                    const s_base = body.places.items[src_word].base;
                                    if (s_base < local_count) src_p = local_prov[s_base];
                                }
                                src_p.min_target_depth = std.math.maxInt(u16);
                                const merged_dst = try ValueProvenance.merge(
                                    local_prov[dst_base],
                                    src_p,
                                    arena_alloc,
                                );
                                if (!ValueProvenance.eql(merged_dst, local_prov[dst_base])) {
                                    local_prov[dst_base] = merged_dst;
                                    has_prov_changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Fail-closed saturation if forward provenance hit `prov_iter_cap`:
    if (has_prov_changed) {
        var sat_loans = try DenseBitSet.initEmpty(arena_alloc, loan_count);
        sat_loans.setAll(loan_count);
        for (val_prov, 0..) |*vp, v_i| {
            if (hasProvenanceCarrier(pool, sym_table, body.insts.items(.type_id)[v_i])) {
                vp.max_depth = std.math.maxInt(u16) - 1;
                vp.min_target_depth = DEPTH_STATIC;
                vp.param_mask = 0xFF;
                vp.scratch_mask = 0b11;
                vp.loan_mask = sat_loans;
            }
        }
        for (local_prov, 0..) |*lp, l_i| {
            if (hasProvenanceCarrier(pool, sym_table, body.locals.items[l_i].type_id)) {
                lp.max_depth = std.math.maxInt(u16) - 1;
                lp.min_target_depth = DEPTH_STATIC;
                lp.param_mask = 0xFF;
                lp.scratch_mask = 0b11;
                lp.loan_mask = sat_loans;
            }
        }
    }

    // [4] Backward CFG liveness for `LoanId`s (`DenseBitSet`) and `Context.scratch[0..2]` borrows (`u2`):
    const live_loans_in = try arena_alloc.alloc(DenseBitSet, block_count);
    const live_loans_out = try arena_alloc.alloc(DenseBitSet, block_count);
    for (0..block_count) |b_i| {
        live_loans_in[b_i] = try DenseBitSet.initEmpty(arena_alloc, loan_count);
        live_loans_out[b_i] = try DenseBitSet.initEmpty(arena_alloc, loan_count);
    }

    const live_scratch_in = try arena_alloc.alloc(u2, block_count);
    @memset(live_scratch_in, 0);
    const live_scratch_out = try arena_alloc.alloc(u2, block_count);
    @memset(live_scratch_out, 0);

    var out_loans = try DenseBitSet.initEmpty(arena_alloc, loan_count);
    var cur_loans = try DenseBitSet.initEmpty(arena_alloc, loan_count);
    var read_vals: std.ArrayListUnmanaged(u32) = .empty;
    const live_iter_cap: usize = @max(@as(usize, 64), block_count * 4);
    var has_liveness_changed = true;
    var live_iter: usize = 0;
    while (has_liveness_changed and live_iter < live_iter_cap) : (live_iter += 1) {
        has_liveness_changed = false;
        var rpo_rev = dom.rpo_blocks.len;
        while (rpo_rev > 0) {
            rpo_rev -= 1;
            const bb_idx = dom.rpo_blocks[rpo_rev];
            const bb_id = MirBlockId.fromInt(bb_idx);

            out_loans.clearAll();
            var out_scratch: u2 = 0;
            for (body.getOutgoingEdges(bb_id)) |edge| {
                const dst = edge.target_bb.asInt();
                if (!dom.isReachable(edge.target_bb)) continue;
                out_loans.unionInPlace(live_loans_in[dst]);
                out_scratch |= live_scratch_in[dst];
            }
            if (!out_loans.eql(live_loans_out[bb_idx]) or out_scratch != live_scratch_out[bb_idx]) {
                live_loans_out[bb_idx].copyFrom(out_loans);
                live_scratch_out[bb_idx] = out_scratch;
                has_liveness_changed = true;
            }

            cur_loans.copyFrom(out_loans);
            var cur_scratch = out_scratch;

            const term = body.blocks.items[bb_idx].terminator;
            switch (term.kind) {
                .ret => {
                    if (term.cond_or_val < inst_count) {
                        cur_loans.unionInPlace(val_prov[term.cond_or_val].loan_mask);
                        cur_scratch |= val_prov[term.cond_or_val].scratch_mask;
                        recordLastUseTokens(
                            loan_list.items,
                            val_prov[term.cond_or_val].loan_mask,
                            body.origin_tokens.items[term.cond_or_val],
                        );
                    }
                },
                .cond_br, .switch_int => {
                    if (term.cond_or_val < inst_count) {
                        cur_loans.unionInPlace(val_prov[term.cond_or_val].loan_mask);
                        cur_scratch |= val_prov[term.cond_or_val].scratch_mask;
                    }
                },
                .call => {
                    const call_idx = term.cond_or_val;
                    if (call_idx < body.calls.items.len) {
                        // Kill non-wildcard loans minted by this call itself before propagating across args:
                        const has_wild_set = loan_count == MAX_TRACKED_LOANS and
                            cur_loans.isSet(MAX_TRACKED_LOANS - 1);
                        cur_loans.differenceInPlace(call_minted_mask[call_idx]);
                        if (has_wild_set) cur_loans.set(MAX_TRACKED_LOANS - 1);

                        const call_site = body.calls.items[call_idx];
                        if (call_site.callee_val.asInt() < inst_count) {
                            cur_loans.unionInPlace(val_prov[call_site.callee_val.asInt()].loan_mask);
                            cur_scratch |= val_prov[call_site.callee_val.asInt()].scratch_mask;
                        }
                        for (0..call_site.args_len) |arg_i| {
                            const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                            const word = body.extra_args.items[call_site.args_start + arg_i];
                            if ((mode == .let_mode or mode == .sink_mode) and word < inst_count) {
                                cur_loans.unionInPlace(val_prov[word].loan_mask);
                                cur_scratch |= val_prov[word].scratch_mask;
                                recordLastUseTokens(
                                    loan_list.items,
                                    val_prov[word].loan_mask,
                                    call_site.origin_token,
                                );
                            } else if (word < body.places.items.len) {
                                for (body.getPlaceProjections(PlaceId.fromInt(word))) |proj| {
                                    if (proj.kind == .index and proj.payload < inst_count) {
                                        cur_loans.unionInPlace(val_prov[proj.payload].loan_mask);
                                    }
                                }
                                const base_loc = body.places.items[word].base;
                                if (base_loc < local_count and
                                    body.getPlaceProjections(PlaceId.fromInt(word)).len > 0 and
                                    body.getPlaceProjections(PlaceId.fromInt(word))[0].kind == .deref)
                                {
                                    cur_loans.unionInPlace(local_prov[base_loc].loan_mask);
                                    cur_scratch |= local_prov[base_loc].scratch_mask;
                                    recordLastUseTokens(
                                        loan_list.items,
                                        local_prov[base_loc].loan_mask,
                                        call_site.origin_token,
                                    );
                                }
                            }
                        }
                    }
                },
                else => {},
            }

            for (body.getOutgoingEdges(bb_id)) |edge| {
                for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |arg_raw| {
                    if (arg_raw < inst_count) {
                        cur_loans.unionInPlace(val_prov[arg_raw].loan_mask);
                        cur_scratch |= val_prov[arg_raw].scratch_mask;
                    }
                }
            }

            const inst_slice = body.getBlockInsts(bb_id);
            var pos_rev = inst_slice.len;
            while (pos_rev > 0) {
                pos_rev -= 1;
                const inst_val = inst_slice[pos_rev];
                const val_idx = inst_val.asInt();
                const inst = body.getInst(inst_val);
                const tok = body.origin_tokens.items[val_idx];

                // Kill non-wildcard loan minted at this exact instruction:
                const minted = inst_minted_loan[val_idx];
                if (minted < loan_count and !loan_list.items[minted].is_overflow_wildcard) {
                    cur_loans.unset(minted);
                }
                if (inst.op == .place_addr or inst.op == .soa_column_slice) {
                    const scratch_m = detectContextScratchAccess(
                        body,
                        pool,
                        sym_table,
                        PlaceId.fromInt(inst.operands.lhs),
                    );
                    if (scratch_m != 0) cur_scratch &= ~scratch_m;
                }

                // Dereference read/write uses loans stored in the base reference local:
                if (inst.op == .place_load or inst.op == .place_store or
                    inst.op == .place_discriminant or inst.op == .place_set_discrim)
                {
                    if (inst.operands.lhs < body.places.items.len) {
                        const pl_id = PlaceId.fromInt(inst.operands.lhs);
                        const projs = body.getPlaceProjections(pl_id);
                        const base_loc = body.places.items[inst.operands.lhs].base;
                        if (projs.len > 0 and projs[0].kind == .deref and base_loc < local_count) {
                            cur_loans.unionInPlace(local_prov[base_loc].loan_mask);
                            cur_scratch |= local_prov[base_loc].scratch_mask;
                            recordLastUseTokens(loan_list.items, local_prov[base_loc].loan_mask, tok);
                        }
                    }
                }

                // Pure propagation instructions (`copy_val`, `place_store` into non-deref local, `aggregate_make`)
                // only make a loan live if the destination itself is later read:
                const is_pure_carrier = switch (inst.op) {
                    .copy_val, .aggregate_make, .aggregate_insert => !cur_loans.intersects(val_prov[val_idx].loan_mask) and
                        (cur_scratch & val_prov[val_idx].scratch_mask) == 0,
                    .place_store => blk: {
                        if (inst.operands.lhs < body.places.items.len) {
                            const pl_id = PlaceId.fromInt(inst.operands.lhs);
                            const projs = body.getPlaceProjections(pl_id);
                            const base_loc = body.places.items[inst.operands.lhs].base;
                            // Storing into `_0` (`return_slot`) is an escaping use:
                            if (base_loc != 0 and (projs.len == 0 or projs[0].kind != .deref)) {
                                break :blk !cur_loans.intersects(local_prov[base_loc].loan_mask) and
                                    (cur_scratch & local_prov[base_loc].scratch_mask) == 0;
                            }
                        }
                        break :blk false;
                    },
                    else => false,
                };

                if (!is_pure_carrier) {
                    read_vals.clearRetainingCapacity();
                    try collectInstReadValues(body, inst, &read_vals, arena_alloc);
                    for (read_vals.items) |used_raw| {
                        if (used_raw < inst_count) {
                            cur_loans.unionInPlace(val_prov[used_raw].loan_mask);
                            cur_scratch |= val_prov[used_raw].scratch_mask;
                            recordLastUseTokens(loan_list.items, val_prov[used_raw].loan_mask, tok);
                        }
                    }
                }
            }

            if (!cur_loans.eql(live_loans_in[bb_idx]) or cur_scratch != live_scratch_in[bb_idx]) {
                live_loans_in[bb_idx].copyFrom(cur_loans);
                live_scratch_in[bb_idx] = cur_scratch;
                has_liveness_changed = true;
            }
        }
    }

    // Fail-closed saturation if backward liveness hit `live_iter_cap`:
    if (has_liveness_changed) {
        for (0..block_count) |b_i| {
            live_loans_in[b_i].setAll(loan_count);
            live_loans_out[b_i].setAll(loan_count);
            live_scratch_in[b_i] = 0b11;
            live_scratch_out[b_i] = 0b11;
        }
    }

    return .{
        .val_prov = val_prov,
        .local_prov = local_prov,
        .local_decl_depth = local_decl_depth,
        .loans = loan_list.items,
        .live_loans_in = live_loans_in,
        .live_loans_out = live_loans_out,
        .live_scratch_in = live_scratch_in,
        .live_scratch_out = live_scratch_out,
        .inst_minted_loan = inst_minted_loan,
        .call_minted_mask = call_minted_mask,
    };
}

/// Records `use_tok` as `last_use_token` for any bit set in `mask` when not yet populated.
fn recordLastUseTokens(loans: []TrackedLoan, mask: DenseBitSet, use_tok: TokenIndex) void {
    if (mask.isEmpty() or use_tok.isNone()) return;
    const words_n = mask.wordCount();
    for (0..words_n) |word_i| {
        var rem = mask.wordAt(word_i);
        while (rem != 0) {
            const bit_idx: usize = word_i * 64 + @ctz(rem);
            rem &= rem - 1;
            if (bit_idx < loans.len and loans[bit_idx].last_use_token.isNone()) {
                loans[bit_idx].last_use_token = use_tok;
            }
        }
    }
}

/// Conservative fallback checking whether an external unanalyzed callee's return type can carry a borrowed view.
fn hasMirViewReturnFallback(pool: *const InternPool, sym_table: *const SymbolTable, ret_ty: TypeId) bool {
    if (ret_ty.isError()) return false;
    const unwrapped = pool.unwrapUnderlyingType(ret_ty);
    if (unwrapped == .str_ty) return true;
    const node = pool.getNode(unwrapped);
    if (node.tag == .ref_ty or node.tag == .mut_ref_ty or node.tag == .slice_ty or node.tag == .soa_slice_ty) {
        return true;
    }
    if (node.tag == .struct_ty) {
        const sym_idx = SymbolIndex.fromInt(node.rhs);
        if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
            if (std.mem.eql(u8, sym_table.getSymbol(sym_idx).name_text, "Span16")) return true;
        }
    }
    return pool.getFlags(unwrapped).has_regions;
}

/// Bounded recursive check for whether `val_ty` can carry a borrowed loan, regional view, closure, or raw pointer.
fn hasProvenanceCarrierBounded(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_val_ty: TypeId,
    subst: *const type_system.NominalTypeSubst,
    depth: u32,
) bool {
    const val_ty = subst.resolve(raw_val_ty);
    if (val_ty.isError()) return false;
    if (depth > 16) return true;
    if (hasMirViewReturnFallback(pool, sym_table, val_ty) or isClosureType(pool, val_ty)) return true;
    const unwrapped = pool.unwrapUnderlyingType(val_ty);
    const node = pool.getNode(unwrapped);
    switch (node.tag) {
        .raw_ptr_ty, .dyn_trait_ty => return true,
        .array_ty, .soa_array_ty, .optional_ty, .refined_ty => {
            return hasProvenanceCarrierBounded(pool, sym_table, TypeId.fromInt(node.lhs), subst, depth + 1);
        },
        .result_ty => {
            return hasProvenanceCarrierBounded(pool, sym_table, TypeId.fromInt(node.lhs), subst, depth + 1) or
                hasProvenanceCarrierBounded(pool, sym_table, TypeId.fromInt(node.rhs), subst, depth + 1);
        },
        .tuple_ty => {
            for (pool.getTupleElements(unwrapped)) |elem_raw| {
                if (hasProvenanceCarrierBounded(pool, sym_table, TypeId.fromInt(elem_raw), subst, depth + 1)) {
                    return true;
                }
            }
            return false;
        },
        .struct_ty, .union_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
            const sym = sym_table.getSymbol(sym_idx).*;
            if (sym.target_scope.isNone()) return false;
            const child_subst = type_system.NominalTypeSubst.fromNominal(pool, sym_table, unwrapped, sym, subst);
            const active_subst = if (child_subst.len > 0) &child_subst else subst;
            for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .field_sym) continue;
                if (hasProvenanceCarrierBounded(pool, sym_table, mem_sym.type_id, active_subst, depth + 1)) {
                    return true;
                }
            }
            return false;
        },
        .enum_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
            const sym = sym_table.getSymbol(sym_idx).*;
            if (sym.target_scope.isNone()) return false;
            const child_subst = type_system.NominalTypeSubst.fromNominal(pool, sym_table, unwrapped, sym, subst);
            const active_subst = if (child_subst.len > 0) &child_subst else subst;
            for (sym_table.getScopeMembers(sym.target_scope)) |mem_idx| {
                const mem_sym = sym_table.getSymbol(mem_idx).*;
                if (mem_sym.kind != .enum_variant_sym or mem_sym.type_id.isNone() or
                    mem_sym.type_id == .unit_ty) continue;
                if (hasProvenanceCarrierBounded(pool, sym_table, mem_sym.type_id, active_subst, depth + 1)) {
                    return true;
                }
            }
            return false;
        },
        else => return false,
    }
}

/// Returns `true` if values of `val_ty` can retain a borrowed loan, regional view, closure, or raw pointer.
fn hasProvenanceCarrier(pool: *const InternPool, sym_table: *const SymbolTable, val_ty: TypeId) bool {
    return hasProvenanceCarrierBounded(pool, sym_table, val_ty, &type_system.NominalTypeSubst.EMPTY, 0);
}

/// Returns `true` if `call_site` invokes a scratch reset/rewind method.
fn isScratchResetCall(sym_table: *const SymbolTable, call_site: mir.MirCallSite) bool {
    if (call_site.direct_symbol.isNone() or call_site.direct_symbol.asInt() >= sym_table.symbols.items.len) {
        return false;
    }
    const name = sym_table.getSymbol(call_site.direct_symbol).name_text;
    return SCRATCH_RESET_METHOD_MAP.has(name);
}

/// Returns `true` if `call_site` is a `scratch_scope` ping-pong selector helper.
fn isScratchScopeHelperCall(sym_table: *const SymbolTable, call_site: mir.MirCallSite) bool {
    if (call_site.direct_symbol.isNone() or call_site.direct_symbol.asInt() >= sym_table.symbols.items.len) {
        return false;
    }
    const name = sym_table.getSymbol(call_site.direct_symbol).name_text;
    return SCRATCH_SELECT_METHOD_MAP.has(name);
}

/// Returns `true` if call argument `(mode, word)` has `Arena` or `BumpArena` type.
fn isArenaArgPlaceOrVal(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    mode: ParamMode,
    word: u32,
) bool {
    if (mode == .let_mode or mode == .sink_mode) {
        if (word < body.insts.len) {
            return isArenaType(pool, sym_table, body.getInst(MirValueId.fromInt(word)).type_id);
        }
    } else if (word < body.places.items.len) {
        const base = body.places.items[word].base;
        if (base < body.locals.items.len) {
            return isArenaType(pool, sym_table, body.locals.items[base].type_id);
        }
    }
    return false;
}

/// Extracts a `u2` constant (`0..3`) if `val_id` is a `MirOp.const_scalar` integer.
fn extractConstSmallU2(body: *const MirBody, val_id: MirValueId) ?u2 {
    if (val_id.asInt() >= body.insts.len) return null;
    const inst = body.getInst(val_id);
    if (inst.op != .const_scalar or inst.operands.lhs >= body.consts.items.len) return null;
    const mc = body.consts.items[inst.operands.lhs];
    if (mc != .int_val or mc.int_val < 0 or mc.int_val > 3) return null;
    return @intCast(mc.int_val);
}

// --------------- Recursive SCC Summary Pre-Pass ---------------

/// Resolves whether `type_id` unwraps to a `.closure_ty`.
fn isClosureType(pool: *const InternPool, type_id: TypeId) bool {
    if (type_id.isError()) return false;
    return pool.getNode(pool.unwrapUnderlyingType(type_id)).tag == .closure_ty;
}

/// Resolves a local variable's source identifier text (`""` for anonymous temporaries).
fn lookupLocalNameText(
    local_decl: mir.LocalDecl,
    interner_opt: ?*const StringInterner,
) []const u8 {
    if (local_decl.name == .empty) return "";
    if (interner_opt) |interner| {
        return interner.get(local_decl.name);
    }
    return "";
}

/// Converges monotone flow/scratch bitmasks across a recursive Tarjan SCC prior to Pass 2 (`[CRITICAL-01]`).
fn convergeRecursiveSccSummaries(
    scratch_arena: *BumpArena,
    bodies: []const MirBody,
    dom_trees: []const DominatorTree,
    scc_slots: []const u32,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    summaries: []FnRegionSummary,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    config: SastConfig,
) !void {
    for (scc_slots) |slot_idx| {
        var c_mask = summaries[slot_idx].contractsScratch();
        c_mask.is_scc_recursive = true;
        summaries[slot_idx].setContractsScratch(c_mask);
        summaries[slot_idx].max_subtree_bytes = FnRegionSummary.STACK_UNBOUNDED;
    }

    const scc_iter_cap: usize = @max(@as(usize, 64), scc_slots.len * 8);
    var scc_iter: usize = 0;
    var has_any_changed = true;
    while (has_any_changed and scc_iter < scc_iter_cap) : (scc_iter += 1) {
        has_any_changed = false;
        for (scc_slots) |slot_idx| {
            const checkpoint = scratch_arena.checkpoint();
            defer scratch_arena.restore(checkpoint);
            const arena_alloc = scratch_arena.asAllocator();

            const body = &bodies[slot_idx];
            const dom = &dom_trees[slot_idx];
            if (body.blocks.items.len == 0) continue;

            const trie = try buildMovePathTrie(arena_alloc, body, pool, sym_table);
            const horizon = try computeBodyProvenanceAndNllHorizon(
                arena_alloc,
                body,
                dom,
                &trie,
                pool,
                sym_table,
                summaries,
                key_to_slot,
                sym_to_slot,
                config,
            );

            var next_ret_mask = summaries[slot_idx].ret_provenance_mask;
            var next_flow_mat = summaries[slot_idx].param_flow_matrix;
            var next_glob_esc = summaries[slot_idx].global_escape_mask;
            var cur_contracts = summaries[slot_idx].contractsScratch();
            var next_touch: u2 = cur_contracts.scratch_touch_mask;
            var next_rewind: u2 = cur_contracts.scratch_rewind_mask;

            for (dom.rpo_blocks) |bb_idx| {
                const bb_id = MirBlockId.fromInt(bb_idx);
                for (body.getBlockInsts(bb_id)) |inst_val| {
                    const inst = body.getInst(inst_val);
                    if (inst.op == .place_addr or inst.op == .soa_column_slice or
                        inst.op == .place_load or inst.op == .place_store)
                    {
                        if (inst.operands.lhs < body.places.items.len) {
                            next_touch |= detectContextScratchAccess(
                                body,
                                pool,
                                sym_table,
                                PlaceId.fromInt(inst.operands.lhs),
                            );
                        }
                    }
                    if (inst.op == .place_store and
                        inst.operands.lhs < body.places.items.len and
                        inst.operands.rhs < body.insts.len)
                    {
                        const rhs_ty = body.getInst(MirValueId.fromInt(inst.operands.rhs)).type_id;
                        if (hasProvenanceCarrier(pool, sym_table, rhs_ty)) {
                            const pl_rec = body.places.items[inst.operands.lhs];
                            const projs = body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs));
                            const has_leading_deref = projs.len > 0 and projs[0].kind == .deref;
                            var dst_mask: u8 = 0;
                            if (has_leading_deref and pl_rec.base < horizon.local_prov.len) {
                                dst_mask = horizon.local_prov[pl_rec.base].param_mask;
                            } else if (!has_leading_deref and pl_rec.base >= 1 and
                                pl_rec.base <= body.param_count and pl_rec.base - 1 < 8)
                            {
                                const p_mode = body.locals.items[pl_rec.base].mode();
                                if (p_mode == .inout_mode or p_mode == .set_mode) {
                                    dst_mask = @as(u8, 1) << @intCast(pl_rec.base - 1);
                                }
                            }
                            if (dst_mask != 0) {
                                const src_mask = horizon.val_prov[inst.operands.rhs].param_mask;
                                for (0..8) |dst_ord| {
                                    if (((dst_mask >> @intCast(dst_ord)) & 1) == 0) continue;
                                    for (0..8) |src_ord| {
                                        if (src_ord != dst_ord and ((src_mask >> @intCast(src_ord)) & 1) != 0) {
                                            next_flow_mat |= (@as(u64, 1) << @intCast(src_ord * 8 + dst_ord));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                const term = body.blocks.items[bb_idx].terminator;
                if (term.kind == .ret) {
                    var ret_p = if (body.locals.items.len > 0) horizon.local_prov[0] else ValueProvenance{};
                    if (term.cond_or_val < body.insts.len) {
                        ret_p = try ValueProvenance.merge(
                            ret_p,
                            horizon.val_prov[term.cond_or_val],
                            arena_alloc,
                        );
                    }
                    if (hasProvenanceCarrier(pool, sym_table, body.ret_ty)) {
                        next_ret_mask |= @as(u64, ret_p.param_mask);
                    }
                } else if (term.kind == .call and term.cond_or_val < body.calls.items.len) {
                    const call_site = body.calls.items[term.cond_or_val];
                    const callee_opt = try lookupCalleeSummary(
                        call_site.direct_def_id,
                        call_site.direct_symbol,
                        summaries,
                        key_to_slot,
                        sym_to_slot,
                        config,
                    );
                    for (0..call_site.args_len) |arg_i| {
                        const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                        const word = body.extra_args.items[call_site.args_start + arg_i];
                        if (mode != .let_mode and mode != .sink_mode and word < body.places.items.len) {
                            const scratch_m = detectContextScratchAccess(
                                body,
                                pool,
                                sym_table,
                                PlaceId.fromInt(word),
                            );
                            next_touch |= scratch_m;
                            if (arg_i == 0 and scratch_m != 0 and isScratchResetCall(sym_table, call_site)) {
                                next_rewind |= scratch_m;
                            }
                        }
                        if (isContextArgPlaceOrVal(body, pool, sym_table, mode, word)) {
                            if (callee_opt) |csum| {
                                next_touch |= csum.contractsScratch().scratch_touch_mask;
                                next_rewind |= csum.contractsScratch().scratch_rewind_mask;
                            }
                        }
                    }
                    if (callee_opt) |csum| {
                        try accumulateCallFlowAndGlobalEscape(
                            body,
                            &horizon,
                            call_site,
                            csum,
                            &next_flow_mat,
                            &next_glob_esc,
                        );
                    }
                }
            }

            if (next_ret_mask != summaries[slot_idx].ret_provenance_mask or
                next_flow_mat != summaries[slot_idx].param_flow_matrix or
                next_glob_esc != summaries[slot_idx].global_escape_mask or
                next_touch != cur_contracts.scratch_touch_mask or
                next_rewind != cur_contracts.scratch_rewind_mask)
            {
                summaries[slot_idx].ret_provenance_mask = next_ret_mask;
                summaries[slot_idx].param_flow_matrix = next_flow_mat;
                summaries[slot_idx].global_escape_mask = next_glob_esc;
                cur_contracts.scratch_touch_mask = next_touch;
                cur_contracts.scratch_rewind_mask = next_rewind;
                summaries[slot_idx].setContractsScratch(cur_contracts);
                has_any_changed = true;
            }
        }
    }

    // Fail-closed saturation if recursive SCC summary convergence hit `scc_iter_cap`:
    if (has_any_changed) {
        for (scc_slots) |slot_idx| {
            const p_count = bodies[slot_idx].param_count;
            if (p_count > 0 and hasProvenanceCarrier(pool, sym_table, bodies[slot_idx].ret_ty)) {
                summaries[slot_idx].ret_provenance_mask = if (p_count >= 64)
                    std.math.maxInt(u64)
                else
                    (@as(u64, 1) << @intCast(p_count)) - 1;
            }
            summaries[slot_idx].param_flow_matrix = std.math.maxInt(u64);
        }
    }
}

/// Returns `true` if call argument `(mode, word)` passes a `Context` / `&Context` / `&mut Context` value.
fn isContextArgPlaceOrVal(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    mode: ParamMode,
    word: u32,
) bool {
    if (mode == .let_mode or mode == .sink_mode) {
        if (word < body.insts.len) {
            return type_system.isContextType(
                pool,
                sym_table,
                body.getInst(MirValueId.fromInt(word)).type_id,
            );
        }
    } else if (word < body.places.items.len) {
        const base = body.places.items[word].base;
        if (base < body.locals.items.len) {
            return type_system.isContextType(pool, sym_table, body.locals.items[base].type_id);
        }
    }
    return false;
}

/// Propagates `callee_sum.param_flow_matrix` (`src * 8 + dst`) and `global_escape_mask` onto caller summary masks.
fn accumulateCallFlowAndGlobalEscape(
    body: *const MirBody,
    horizon: *const BodyProvenanceHorizon,
    call_site: mir.MirCallSite,
    callee_sum: FnRegionSummary,
    flow_mat_out: *u64,
    glob_esc_out: *u32,
) !void {
    const extractArgParamMask = struct {
        //! Local helper resolving the caller parameter provenance bitmask carried by a call argument.

        /// Returns the `param_mask` of `(arg_mode, arg_word)` from `hor_ref`.
        fn run(
            body_ref: *const MirBody,
            hor_ref: *const BodyProvenanceHorizon,
            arg_mode: ParamMode,
            arg_word: u32,
        ) u8 {
            if (arg_mode == .let_mode or arg_mode == .sink_mode) {
                return if (arg_word < hor_ref.val_prov.len) hor_ref.val_prov[arg_word].param_mask else 0;
            }
            if (arg_word < body_ref.places.items.len) {
                const base = body_ref.places.items[arg_word].base;
                return if (base < hor_ref.local_prov.len) hor_ref.local_prov[base].param_mask else 0;
            }
            return 0;
        }
    }.run;

    if (callee_sum.global_escape_mask != 0) {
        const lim = @min(@as(usize, call_site.args_len), 32);
        for (0..lim) |arg_i| {
            if (((callee_sum.global_escape_mask >> @intCast(arg_i)) & 1) == 0) continue;
            const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
            const word = body.extra_args.items[call_site.args_start + arg_i];
            glob_esc_out.* |= @as(u32, extractArgParamMask(body, horizon, mode, word));
        }
    }

    if (callee_sum.param_flow_matrix != 0) {
        const lim = @min(@as(usize, call_site.args_len), 8);
        for (0..lim) |dst_arg| {
            const dst_mode = body.call_arg_modes.items[call_site.modes_start + dst_arg];
            const dst_word = body.extra_args.items[call_site.args_start + dst_arg];
            const dst_caller_params = extractArgParamMask(body, horizon, dst_mode, dst_word);
            if (dst_caller_params == 0) continue;

            for (0..lim) |src_arg| {
                if (src_arg == dst_arg) continue;
                if (((callee_sum.param_flow_matrix >> @intCast(src_arg * 8 + dst_arg)) & 1) == 0) continue;
                const src_mode = body.call_arg_modes.items[call_site.modes_start + src_arg];
                const src_word = body.extra_args.items[call_site.args_start + src_arg];
                const src_caller_params = extractArgParamMask(body, horizon, src_mode, src_word);
                if (src_caller_params == 0) continue;

                for (0..8) |caller_d| {
                    if (((dst_caller_params >> @intCast(caller_d)) & 1) == 0) continue;
                    for (0..8) |caller_s| {
                        if (caller_s != caller_d and ((src_caller_params >> @intCast(caller_s)) & 1) != 0) {
                            flow_mat_out.* |= (@as(u64, 1) << @intCast(caller_s * 8 + caller_d));
                        }
                    }
                }
            }
        }
    }
}

// ---------- Pass 2: Typestate, NLL & ElaborateDrops -----------

/// Six-bitset monotone dataflow state + raw-pointer abstract map for Pass 2 (`DR-06` §2.1 & §2.4).
const TypestateState = struct {
    /// Paths that MAY hold an initialized value on at least one incoming path.
    maybe_init: DenseBitSet,
    /// Paths that MAY be uninitialized, moved-from, or dead on at least one incoming path.
    maybe_uninit: DenseBitSet,
    /// Paths moved from (`ghost_storage_move`) without subsequent dominating re-initialization.
    ever_moved: DenseBitSet,
    /// Paths explicitly freed/closed without subsequent dominating re-initialization.
    ever_freed: DenseBitSet,
    /// Active Ghost `let` brackets (`.scoped_projection` / `.match_guard`) on `MovePathId`.
    let_loan: DenseBitSet,
    /// Active Ghost `inout`/`set` brackets (`.scoped_projection` / `.match_guard`) on `MovePathId`.
    inout_loan: DenseBitSet,
    /// Per-local abstract `RawPtrState` (`len == body.locals.items.len`).
    local_raw_ptr: []RawPtrState,

    /// Allocates an empty `TypestateState` inside `arena_alloc`.
    fn initEmpty(arena_alloc: std.mem.Allocator, path_count: usize, local_count: usize) !TypestateState {
        const ptrs = try arena_alloc.alloc(RawPtrState, local_count);
        @memset(ptrs, .unknown_or_non_ptr);
        return .{
            .maybe_init = try DenseBitSet.initEmpty(arena_alloc, path_count),
            .maybe_uninit = try DenseBitSet.initEmpty(arena_alloc, path_count),
            .ever_moved = try DenseBitSet.initEmpty(arena_alloc, path_count),
            .ever_freed = try DenseBitSet.initEmpty(arena_alloc, path_count),
            .let_loan = try DenseBitSet.initEmpty(arena_alloc, path_count),
            .inout_loan = try DenseBitSet.initEmpty(arena_alloc, path_count),
            .local_raw_ptr = ptrs,
        };
    }

    /// Resets `self` to empty bottom state in-place without allocating.
    fn resetEmpty(self: *TypestateState) void {
        self.maybe_init.clearAll();
        self.maybe_uninit.clearAll();
        self.ever_moved.clearAll();
        self.ever_freed.clearAll();
        self.let_loan.clearAll();
        self.inout_loan.clearAll();
        @memset(self.local_raw_ptr, .unknown_or_non_ptr);
    }

    /// Saturates `self` to fail-closed top state across `path_count` paths.
    fn saturateTop(self: *TypestateState, path_count: usize) void {
        self.maybe_init.setAll(path_count);
        self.maybe_uninit.setAll(path_count);
        self.let_loan.setAll(path_count);
        self.inout_loan.setAll(path_count);
        for (self.local_raw_ptr) |*ptr_st| {
            if (ptr_st.* != .unknown_or_non_ptr) ptr_st.* = .freed_or_dangling;
        }
    }

    /// Copies `src` into `self`.
    fn copyFrom(self: *TypestateState, src: TypestateState) void {
        self.maybe_init.copyFrom(src.maybe_init);
        self.maybe_uninit.copyFrom(src.maybe_uninit);
        self.ever_moved.copyFrom(src.ever_moved);
        self.ever_freed.copyFrom(src.ever_freed);
        self.let_loan.copyFrom(src.let_loan);
        self.inout_loan.copyFrom(src.inout_loan);
        @memcpy(self.local_raw_ptr, src.local_raw_ptr);
    }

    /// Pointwise union (`self |= other`), returning `true` if any bit or `RawPtrState` changed.
    fn joinAssignChanged(self: *TypestateState, other: TypestateState) bool {
        var has_changed = false;
        if (self.maybe_init.unionAssignChanged(other.maybe_init)) has_changed = true;
        if (self.maybe_uninit.unionAssignChanged(other.maybe_uninit)) has_changed = true;
        if (self.ever_moved.unionAssignChanged(other.ever_moved)) has_changed = true;
        if (self.ever_freed.unionAssignChanged(other.ever_freed)) has_changed = true;
        if (self.let_loan.unionAssignChanged(other.let_loan)) has_changed = true;
        if (self.inout_loan.unionAssignChanged(other.inout_loan)) has_changed = true;
        for (self.local_raw_ptr, other.local_raw_ptr) |*dst_ptr, src_ptr| {
            const joined = RawPtrState.join(dst_ptr.*, src_ptr);
            if (joined != dst_ptr.*) {
                dst_ptr.* = joined;
                has_changed = true;
            }
        }
        return has_changed;
    }
};

/// Planned destructor insertion emitted by Pass `2.2` and materialized in Pass `2.3` without block splitting.
const PlannedDropInsertion = struct {
    /// Owning basic block index.
    bb_idx: u32,
    /// Instruction index in `body.getBlockInsts(bb)` before which to splice (`NONE_U32` = before terminator).
    before_pos: u32,
    /// Target `MovePathId` being dropped (keys synthesized `_drop_flag` when `is_conditional`).
    path_id: MovePathId,
    /// Concrete `PlaceId` passed to `drop_in_place` / `drop_if_live`.
    place_id: PlaceId,
    /// Concrete `TypeId` of `place_id` (used to record `auto_drop_glue` witness edges).
    place_ty: TypeId,
    /// Source token attached to synthesized drop instructions.
    token: TokenIndex,
    /// `false` -> `drop_in_place`; `true` -> `_drop_flag` + `drop_if_live`.
    is_conditional: bool,
};

/// Summary and witness outputs collected during Pass 2 for a single `MirBody`.
const Pass2BodyOutcome = struct {
    /// Count of SAST errors (`E03xx`) emitted on this body.
    emitted_error_count: u32 = 0,
    /// Count of `drop_in_place` and `drop_if_live` instructions inserted into `body`.
    emitted_drops: u32 = 0,
    /// `true` if any instruction in `body` dereferenced a raw pointer or carried `InstFlags.is_unsafe`.
    has_unsafe_op: bool = false,
    /// `true` if `ElaborateDrops` synthesized a built-in heap container (`Vec`, `String`, `Map`) free.
    has_builtin_heap_drop_free: bool = false,
};

/// Returns `true` if `ghost_storage_init(lid)` at `pos` in `inst_slice` is paired with a following `place_store`.
fn hasImmediatePairedStore(body: *const MirBody, inst_slice: []const MirValueId, pos: usize, lid: u32) bool {
    const scan_end = @min(pos + 5, inst_slice.len);
    for (inst_slice[pos + 1 .. scan_end]) |next_val| {
        const next_inst = body.getInst(next_val);
        if (next_inst.op == .place_store and next_inst.operands.lhs < body.places.items.len) {
            const pl_rec = body.places.items[next_inst.operands.lhs];
            if (pl_rec.base == lid and pl_rec.proj_len == 0) return true;
        }
        if (next_inst.op == .ghost_storage_deinit and next_inst.operands.lhs == lid) return false;
    }
    return false;
}

/// Applies strong or weak initialization of `lookup` onto `state` (`[CRITICAL-02]`).
fn applyPathWriteToState(trie: *const MovePathTrie, lookup: PlacePathLookup, state: *TypestateState) void {
    if (lookup.id.isNone()) return;
    const m_idx = lookup.id.asInt();
    state.maybe_init.unionInPlace(trie.subtree[m_idx]);
    state.maybe_init.unionInPlace(trie.strict_anc[m_idx]);
    if (!lookup.is_partial) {
        state.maybe_uninit.differenceInPlace(trie.subtree[m_idx]);
        state.ever_moved.differenceInPlace(trie.subtree[m_idx]);
        state.ever_freed.differenceInPlace(trie.subtree[m_idx]);
        // Recompute strict ancestors: clear `maybe_uninit` on parent if ALL materialized children are init:
        var walk_p = trie.nodes[m_idx].parent;
        while (!walk_p.isNone()) {
            const p_idx = walk_p.asInt();
            var has_all_children_init = true;
            var has_any_child = false;
            var ch = trie.nodes[p_idx].first_child;
            while (!ch.isNone()) {
                has_any_child = true;
                if (state.maybe_uninit.isSet(ch.asInt()) or !state.maybe_init.isSet(ch.asInt())) {
                    has_all_children_init = false;
                    break;
                }
                ch = trie.nodes[ch.asInt()].next_sibling;
            }
            if (has_any_child and has_all_children_init) {
                state.maybe_uninit.unset(p_idx);
                state.ever_moved.unset(p_idx);
                state.ever_freed.unset(p_idx);
            }
            walk_p = trie.nodes[p_idx].parent;
        }
    }
}

/// Applies strong or weak move/free transition of `lookup` onto `state` (`[CRITICAL-02]`).
fn applyPathMoveOrFreeToState(
    trie: *const MovePathTrie,
    lookup: PlacePathLookup,
    is_explicit_free: bool,
    state: *TypestateState,
) void {
    if (lookup.id.isNone()) return;
    const m_idx = lookup.id.asInt();
    state.maybe_uninit.unionInPlace(trie.subtree[m_idx]);
    state.maybe_uninit.unionInPlace(trie.strict_anc[m_idx]);
    if (is_explicit_free) {
        state.ever_freed.unionInPlace(trie.subtree[m_idx]);
    } else {
        state.ever_moved.unionInPlace(trie.subtree[m_idx]);
    }
    if (!lookup.is_partial) {
        state.maybe_init.differenceInPlace(trie.subtree[m_idx]);
    }
}

/// Returns `true` if `m_idx` still holds at least one unconsumed `@linear` obligation in `state`.
fn hasLiveLinearObligation(
    trie: *const MovePathTrie,
    state: *const TypestateState,
    m_idx: usize,
) bool {
    if (m_idx >= trie.nodes.len) return false;
    const node = trie.nodes[m_idx];
    if (!node.flags().is_linear or !state.maybe_init.isSet(m_idx)) return false;

    var has_linear_field_child = false;
    var walk_ch = node.first_child;
    while (!walk_ch.isNone()) {
        const ch_idx = walk_ch.asInt();
        const ch_node = trie.nodes[ch_idx];
        if (ch_node.proj_kind_raw == @backingInt(mir.ProjKind.field) and ch_node.flags().is_linear) {
            has_linear_field_child = true;
            if (hasLiveLinearObligation(trie, state, ch_idx)) return true;
        }
        walk_ch = ch_node.next_sibling;
    }
    if (has_linear_field_child) return false;
    return true;
}

/// Returns `true` if `m_idx` or any descendant in `trie.subtree[m_idx]` was moved out and not yet re-initialized.
fn hasMovedUninitDescendant(
    trie: *const MovePathTrie,
    state: *const TypestateState,
    m_idx: usize,
) bool {
    var cursor: usize = 0;
    while (trie.subtree[m_idx].nextSetBit(cursor)) |sub_idx| : (cursor = sub_idx + 1) {
        if (state.ever_moved.isSet(sub_idx) and state.maybe_uninit.isSet(sub_idx)) {
            return true;
        }
    }
    return false;
}

/// Detects `cond_br` non-null pointer guard `ptr != null` / `ptr == null`, returning refined `(local_idx, nonnull_on_then)`.
fn detectRawPtrNullGuard(
    body: *const MirBody,
    pool: *const InternPool,
    cond_val: MirValueId,
) ?struct { local_idx: u32, is_nonnull_on_then: bool } {
    if (cond_val.asInt() >= body.insts.len) return null;
    const inst = body.getInst(cond_val);
    if (inst.op != .bin_op) return null;
    const bop: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
    if (bop != .ne and bop != .eq) return null;

    const isZeroPtrConst = struct {
        //! Local helper checking whether `val_raw` peels to a zero/null pointer constant.

        /// Returns `true` if `val_raw` in `body_ref` represents a null raw-pointer constant.
        fn isZeroVal(body_ref: *const MirBody, val_raw: u32) bool {
            if (val_raw >= body_ref.insts.len) return false;
            var cur = body_ref.getInst(MirValueId.fromInt(val_raw));
            if (cur.op == .unary_op or cur.op == .copy_val) {
                if (cur.operands.lhs < body_ref.insts.len) {
                    cur = body_ref.getInst(MirValueId.fromInt(cur.operands.lhs));
                }
            }
            if (cur.op != .const_scalar or cur.operands.lhs >= body_ref.consts.items.len) return false;
            const mc = body_ref.consts.items[cur.operands.lhs];
            return (mc == .int_val and mc.int_val == 0) or mc == .unit_val;
        }
    }.isZeroVal;

    const extractLoadedPtrLocal = struct {
        //! Local helper extracting the unprojected raw-pointer `LocalId` index loaded by `val_raw`.

        /// Returns `pl_rec.base` when `val_raw` loads directly from a `.raw_ptr_ty` local slot.
        fn check(body_ref: *const MirBody, pool_ref: *const InternPool, val_raw: u32) ?u32 {
            if (val_raw >= body_ref.insts.len) return null;
            var cur = body_ref.getInst(MirValueId.fromInt(val_raw));
            if (cur.op == .copy_val and cur.operands.lhs < body_ref.insts.len) {
                cur = body_ref.getInst(MirValueId.fromInt(cur.operands.lhs));
            }
            if (cur.op != .place_load or cur.operands.lhs >= body_ref.places.items.len) return null;
            const pl_rec = body_ref.places.items[cur.operands.lhs];
            if (pl_rec.proj_len != 0 or pl_rec.base >= body_ref.locals.items.len) return null;
            const unwrapped = pool_ref.unwrapUnderlyingType(body_ref.locals.items[pl_rec.base].type_id);
            if (unwrapped.isError() or pool_ref.getNode(unwrapped).tag != .raw_ptr_ty) return null;
            return pl_rec.base;
        }
    }.check;

    if (isZeroPtrConst(body, inst.operands.rhs)) {
        if (extractLoadedPtrLocal(body, pool, inst.operands.lhs)) |lid_idx| {
            return .{ .local_idx = lid_idx, .is_nonnull_on_then = (bop == .ne) };
        }
    }
    if (isZeroPtrConst(body, inst.operands.lhs)) {
        if (extractLoadedPtrLocal(body, pool, inst.operands.rhs)) |lid_idx| {
            return .{ .local_idx = lid_idx, .is_nonnull_on_then = (bop == .ne) };
        }
    }
    return null;
}

/// Applies the Pass 2 transfer function across a single basic block without emitting diagnostics.
fn stepTypestateBlockSilent(
    body: *const MirBody,
    bb_id: MirBlockId,
    trie: *const MovePathTrie,
    horizon: *const BodyProvenanceHorizon,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    ghost_open_places: []MovePathId,
    ghost_open_ops: []MirOp,
    state: *TypestateState,
) void {
    const inst_slice = body.getBlockInsts(bb_id);
    for (inst_slice, 0..) |inst_val, pos| {
        const val_idx = inst_val.asInt();
        const inst = body.getInst(inst_val);
        switch (inst.op) {
            .ghost_storage_init => {
                const lid = inst.operands.lhs;
                if (!hasImmediatePairedStore(body, inst_slice, pos, lid)) {
                    if (lid < trie.direct_local_limit) {
                        applyPathWriteToState(trie, .{ .id = MovePathId.fromInt(lid), .is_partial = false }, state);
                    } else if (trie.direct_local_limit < trie.nodes.len) {
                        applyPathWriteToState(
                            trie,
                            .{ .id = MovePathId.fromInt(trie.direct_local_limit), .is_partial = true },
                            state,
                        );
                    }
                }
            },
            .ghost_storage_deinit => {
                const lid = inst.operands.lhs;
                if (lid < trie.direct_local_limit) {
                    state.maybe_init.differenceInPlace(trie.subtree[lid]);
                    state.maybe_uninit.unionInPlace(trie.subtree[lid]);
                    state.ever_moved.differenceInPlace(trie.subtree[lid]);
                    state.ever_freed.differenceInPlace(trie.subtree[lid]);
                } else if (trie.direct_local_limit < trie.nodes.len) {
                    state.maybe_uninit.set(trie.direct_local_limit);
                }
                const dead_lid = LocalId.fromInt(lid);
                for (horizon.local_prov, 0..) |lp, loc_i| {
                    if (lp.raw_ptr_local == dead_lid and loc_i < state.local_raw_ptr.len) {
                        state.local_raw_ptr[loc_i] = .freed_or_dangling;
                    }
                }
            },
            .ghost_storage_move => {
                if (inst.operands.lhs < trie.place_map.len) {
                    const lookup = trie.place_map[inst.operands.lhs];
                    if (!trie.nodes[lookup.id.asInt()].flags().is_copy) {
                        applyPathMoveOrFreeToState(trie, lookup, false, state);
                    }
                }
            },
            .ghost_access_let, .ghost_access_inout, .ghost_access_set => {
                const bkind: mir.GhostBorrowKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.operands.rhs))));
                if (bkind != .addr_borrow and inst.operands.lhs < trie.place_map.len) {
                    const m_id = trie.place_map[inst.operands.lhs].id;
                    ghost_open_places[val_idx] = m_id;
                    ghost_open_ops[val_idx] = inst.op;
                    if (inst.op == .ghost_access_let) {
                        state.let_loan.set(m_id.asInt());
                    } else {
                        state.inout_loan.set(m_id.asInt());
                    }
                }
            },
            .ghost_access_end => {
                if (inst.operands.lhs < ghost_open_places.len) {
                    const closed_m = ghost_open_places[inst.operands.lhs];
                    if (!closed_m.isNone()) {
                        if (ghost_open_ops[inst.operands.lhs] == .ghost_access_let) {
                            state.let_loan.unset(closed_m.asInt());
                        } else {
                            state.inout_loan.unset(closed_m.asInt());
                        }
                    }
                }
            },
            .place_store => {
                if (inst.operands.lhs < trie.place_map.len) {
                    const lookup = trie.place_map[inst.operands.lhs];
                    applyPathWriteToState(trie, lookup, state);
                    const pl_rec = body.places.items[inst.operands.lhs];
                    if (pl_rec.proj_len == 0 and pl_rec.base < state.local_raw_ptr.len and
                        inst.operands.rhs < horizon.val_prov.len)
                    {
                        const rhs_ptr = horizon.val_prov[inst.operands.rhs].raw_ptr_state;
                        if (rhs_ptr != .unknown_or_non_ptr) {
                            state.local_raw_ptr[pl_rec.base] = rhs_ptr;
                        }
                    }
                }
            },
            .intrinsic_op => {
                const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                if (ikind == .ghost_storage_free and inst.operands.lhs < trie.place_map.len) {
                    const lookup = trie.place_map[inst.operands.lhs];
                    applyPathMoveOrFreeToState(trie, lookup, true, state);
                    const base = body.places.items[inst.operands.lhs].base;
                    if (base < state.local_raw_ptr.len) state.local_raw_ptr[base] = .freed_or_dangling;
                }
            },
            else => {},
        }
    }

    const term = body.blocks.items[bb_id.asInt()].terminator;
    if (term.kind == .call and term.cond_or_val < body.calls.items.len) {
        const call_site = body.calls.items[term.cond_or_val];
        applyCallStateTransitionSilent(body, trie, pool, sym_table, call_site, state);
    }
}

/// Applies explicit free/close and `set`-mode out-parameter initialization effects of `call_site` onto `state`.
fn applyCallStateTransitionSilent(
    body: *const MirBody,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    call_site: mir.MirCallSite,
    state: *TypestateState,
) void {
    const is_free_call = !call_site.direct_symbol.isNone() and
        call_site.direct_symbol.asInt() < sym_table.symbols.items.len and
        EXPLICIT_FREE_METHOD_MAP.has(sym_table.getSymbol(call_site.direct_symbol).name_text);

    for (0..call_site.args_len) |arg_i| {
        const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
        const word = body.extra_args.items[call_site.args_start + arg_i];
        if (mode == .set_mode and word < trie.place_map.len) {
            applyPathWriteToState(trie, trie.place_map[word], state);
        }
    }

    if (!is_free_call or call_site.args_len == 0) return;

    const arg0_mode = body.call_arg_modes.items[call_site.modes_start];
    const arg0_word = body.extra_args.items[call_site.args_start];

    // `PoolAllocator::free(&mut pool, ptr)` marks `ptr` (`arg 1`) freed:
    if (call_site.args_len >= 2 and isPoolArgPlaceOrVal(body, pool, sym_table, arg0_mode, arg0_word)) {
        const ptr_mode = body.call_arg_modes.items[call_site.modes_start + 1];
        const ptr_word = body.extra_args.items[call_site.args_start + 1];
        if ((ptr_mode == .let_mode or ptr_mode == .sink_mode) and ptr_word < body.insts.len) {
            const ptr_inst = body.getInst(MirValueId.fromInt(ptr_word));
            if (ptr_inst.op == .place_load and ptr_inst.operands.lhs < trie.place_map.len) {
                const lookup = trie.place_map[ptr_inst.operands.lhs];
                applyPathMoveOrFreeToState(trie, lookup, true, state);
                const base = body.places.items[ptr_inst.operands.lhs].base;
                if (base < state.local_raw_ptr.len) state.local_raw_ptr[base] = .freed_or_dangling;
            }
        } else if (ptr_word < trie.place_map.len) {
            const lookup = trie.place_map[ptr_word];
            applyPathMoveOrFreeToState(trie, lookup, true, state);
            const base = body.places.items[ptr_word].base;
            if (base < state.local_raw_ptr.len) state.local_raw_ptr[base] = .freed_or_dangling;
        }
        return;
    }

    // `handle.close()` / `arena.release()` on receiver `arg 0`:
    if (arg0_mode != .let_mode and arg0_mode != .sink_mode and arg0_word < trie.place_map.len) {
        const lookup = trie.place_map[arg0_word];
        applyPathMoveOrFreeToState(trie, lookup, true, state);
    } else if ((arg0_mode == .let_mode or arg0_mode == .sink_mode) and arg0_word < body.insts.len) {
        const recv_inst = body.getInst(MirValueId.fromInt(arg0_word));
        if (recv_inst.op == .place_load and recv_inst.operands.lhs < trie.place_map.len) {
            state.ever_freed.unionInPlace(trie.subtree[trie.place_map[recv_inst.operands.lhs].id.asInt()]);
        } else if (recv_inst.op == .place_addr and recv_inst.operands.lhs < trie.place_map.len) {
            // `&mut self` receiver lowered via `place_addr`:
            const lookup = trie.place_map[recv_inst.operands.lhs];
            applyPathMoveOrFreeToState(trie, lookup, true, state);
        }
    }
}

/// Returns `true` if argument `(mode, word)` has `PoolAllocator` type.
fn isPoolArgPlaceOrVal(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    mode: ParamMode,
    word: u32,
) bool {
    if (mode == .let_mode or mode == .sink_mode) {
        if (word < body.insts.len) {
            return isPoolAllocatorType(pool, sym_table, body.getInst(MirValueId.fromInt(word)).type_id);
        }
    } else if (word < body.places.items.len) {
        const base = body.places.items[word].base;
        if (base < body.locals.items.len) {
            return isPoolAllocatorType(pool, sym_table, body.locals.items[base].type_id);
        }
    }
    return false;
}

/// Finds or creates an unprojected `PlaceId` referencing `local_id` in `body.places`.
fn ensureRootPlaceForLocal(body: *MirBody, local_id: LocalId) !PlaceId {
    for (body.places.items, 0..) |pl_rec, pl_i| {
        if (pl_rec.base == local_id.asInt() and pl_rec.proj_len == 0) {
            return PlaceId.fromInt(@intCast(pl_i));
        }
    }
    const new_idx: u32 = @intCast(body.places.items.len);
    try body.places.append(body.allocator, .{
        .base = local_id.asInt(),
        .proj_start = 0,
        .proj_len = 0,
    });
    return PlaceId.fromInt(new_idx);
}

/// Reconstructs or looks up a `PlaceId` in `body` corresponding to `MovePathId(m_idx)`.
fn ensurePlaceForMovePath(body: *MirBody, trie: *const MovePathTrie, m_idx: usize) !PlaceId {
    const node = trie.nodes[m_idx];
    if (node.parent.isNone()) {
        return ensureRootPlaceForLocal(body, LocalId.fromInt(node.base_local));
    }
    for (trie.place_map, 0..) |lookup, pl_i| {
        if (!lookup.is_partial and lookup.id.asInt() == m_idx) {
            return PlaceId.fromInt(@intCast(pl_i));
        }
    }

    var rev_projs: [64]MirProjection = undefined;
    var proj_count: usize = 0;
    var cur_id = MovePathId.fromInt(@intCast(m_idx));
    while (!cur_id.isNone() and proj_count < rev_projs.len) {
        const cur_node = trie.nodes[cur_id.asInt()];
        if (cur_node.parent.isNone()) break;
        rev_projs[proj_count] = .{
            .kind = @fromBackingInt(cur_node.proj_kind_raw),
            .payload = cur_node.field_or_variant_ord,
        };
        proj_count += 1;
        cur_id = cur_node.parent;
    }

    const proj_start: u24 = @intCast(body.projections.items.len);
    var fwd_i = proj_count;
    while (fwd_i > 0) {
        fwd_i -= 1;
        try body.projections.append(body.allocator, rev_projs[fwd_i]);
    }
    const new_pl_idx: u32 = @intCast(body.places.items.len);
    try body.places.append(body.allocator, .{
        .base = node.base_local,
        .proj_start = proj_start,
        .proj_len = @intCast(proj_count),
    });
    return PlaceId.fromInt(new_pl_idx);
}

/// Computes per-instruction pre-execution `live_loans` (`DenseBitSet`) and `live_scratch` (`u2`) inside `bb_id`.
fn computeBlockStepHorizons(
    arena_alloc: std.mem.Allocator,
    body: *const MirBody,
    bb_id: MirBlockId,
    trie: *const MovePathTrie,
    horizon: *const BodyProvenanceHorizon,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    loans_before_out: []DenseBitSet,
    scratch_before_out: []u2,
    term_loans_out: *DenseBitSet,
    term_scratch_out: *u2,
) !void {
    const bb_idx = bb_id.asInt();
    const inst_count = body.insts.len;
    const local_count = body.locals.items.len;
    const loan_count = horizon.loans.len;

    var cur_loans = try DenseBitSet.initEmpty(arena_alloc, loan_count);
    cur_loans.copyFrom(horizon.live_loans_out[bb_idx]);
    var cur_scratch = horizon.live_scratch_out[bb_idx];

    for (body.getOutgoingEdges(bb_id)) |edge| {
        for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |arg_raw| {
            if (arg_raw < horizon.val_prov.len) {
                cur_loans.unionInPlace(horizon.val_prov[arg_raw].loan_mask);
                cur_scratch |= horizon.val_prov[arg_raw].scratch_mask;
            }
        }
    }

    const term = body.blocks.items[bb_idx].terminator;
    switch (term.kind) {
        .ret, .cond_br, .switch_int => {
            if (term.cond_or_val < horizon.val_prov.len) {
                cur_loans.unionInPlace(horizon.val_prov[term.cond_or_val].loan_mask);
                cur_scratch |= horizon.val_prov[term.cond_or_val].scratch_mask;
            }
        },
        .call => {
            const call_idx = term.cond_or_val;
            if (call_idx < body.calls.items.len) {
                const call_site = body.calls.items[call_idx];
                // Exclude non-wildcard loans minted by this exact call's return view:
                const has_wild_set = loan_count == MAX_TRACKED_LOANS and
                    cur_loans.isSet(MAX_TRACKED_LOANS - 1);
                cur_loans.differenceInPlace(horizon.call_minted_mask[call_idx]);
                if (has_wild_set) cur_loans.set(MAX_TRACKED_LOANS - 1);
                term_loans_out.* = try cur_loans.clone(arena_alloc);
                term_scratch_out.* = cur_scratch;

                if (call_site.callee_val.asInt() < horizon.val_prov.len) {
                    cur_loans.unionInPlace(horizon.val_prov[call_site.callee_val.asInt()].loan_mask);
                    cur_scratch |= horizon.val_prov[call_site.callee_val.asInt()].scratch_mask;
                }
                for (0..call_site.args_len) |arg_i| {
                    const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                    const word = body.extra_args.items[call_site.args_start + arg_i];
                    if ((mode == .let_mode or mode == .sink_mode) and word < horizon.val_prov.len) {
                        cur_loans.unionInPlace(horizon.val_prov[word].loan_mask);
                        cur_scratch |= horizon.val_prov[word].scratch_mask;
                    } else if (word < body.places.items.len) {
                        const projs = body.getPlaceProjections(PlaceId.fromInt(word));
                        const base_loc = body.places.items[word].base;
                        if (projs.len > 0 and projs[0].kind == .deref and base_loc < local_count) {
                            cur_loans.unionInPlace(horizon.local_prov[base_loc].loan_mask);
                            cur_scratch |= horizon.local_prov[base_loc].scratch_mask;
                        }
                    }
                }
            } else {
                term_loans_out.* = try cur_loans.clone(arena_alloc);
                term_scratch_out.* = cur_scratch;
            }
        },
        else => {},
    }
    if (term.kind != .call) {
        term_loans_out.* = try cur_loans.clone(arena_alloc);
        term_scratch_out.* = cur_scratch;
    }

    var read_vals: std.ArrayListUnmanaged(u32) = .empty;
    const inst_slice = body.getBlockInsts(bb_id);
    var pos_rev = inst_slice.len;
    while (pos_rev > 0) {
        pos_rev -= 1;
        const inst_val = inst_slice[pos_rev];
        const val_idx = inst_val.asInt();
        const inst = body.getInst(inst_val);

        if ((inst.op == .place_addr or inst.op == .soa_column_slice) and
            inst.operands.lhs < trie.place_map.len)
        {
            const minted_loan = horizon.inst_minted_loan[val_idx];
            if (minted_loan < loan_count and !horizon.loans[minted_loan].is_overflow_wildcard) {
                cur_loans.unset(minted_loan);
            }
            const scratch_m = detectContextScratchAccess(
                body,
                pool,
                sym_table,
                PlaceId.fromInt(inst.operands.lhs),
            );
            if (scratch_m != 0) cur_scratch &= ~scratch_m;
        }

        loans_before_out[pos_rev] = try cur_loans.clone(arena_alloc);
        scratch_before_out[pos_rev] = cur_scratch;

        if (inst.op == .place_load or inst.op == .place_store or
            inst.op == .place_discriminant or inst.op == .place_set_discrim)
        {
            if (inst.operands.lhs < body.places.items.len) {
                const projs = body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs));
                const base_loc = body.places.items[inst.operands.lhs].base;
                if (projs.len > 0 and projs[0].kind == .deref and base_loc < local_count) {
                    cur_loans.unionInPlace(horizon.local_prov[base_loc].loan_mask);
                    cur_scratch |= horizon.local_prov[base_loc].scratch_mask;
                }
            }
        }

        const is_pure_carrier = switch (inst.op) {
            .copy_val, .aggregate_make, .aggregate_insert => val_idx < horizon.val_prov.len and
                !cur_loans.intersects(horizon.val_prov[val_idx].loan_mask) and
                (cur_scratch & horizon.val_prov[val_idx].scratch_mask) == 0,
            .place_store => blk: {
                if (inst.operands.lhs < body.places.items.len) {
                    const projs = body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs));
                    const base_loc = body.places.items[inst.operands.lhs].base;
                    if (base_loc != 0 and base_loc < local_count and (projs.len == 0 or projs[0].kind != .deref)) {
                        break :blk !cur_loans.intersects(horizon.local_prov[base_loc].loan_mask) and
                            (cur_scratch & horizon.local_prov[base_loc].scratch_mask) == 0;
                    }
                }
                break :blk false;
            },
            else => false,
        };

        if (!is_pure_carrier) {
            read_vals.clearRetainingCapacity();
            try collectInstReadValues(body, inst, &read_vals, arena_alloc);
            for (read_vals.items) |used_raw| {
                if (used_raw < inst_count and used_raw < horizon.val_prov.len) {
                    cur_loans.unionInPlace(horizon.val_prov[used_raw].loan_mask);
                    cur_scratch |= horizon.val_prov[used_raw].scratch_mask;
                }
            }
        }
    }
}

/// Checks whether accessing `access_path` (`is_mut_or_move`) violates any live NLL `LoanId` or Ghost bracket (`E0305`).
fn findExclusivityConflict(
    trie: *const MovePathTrie,
    horizon: *const BodyProvenanceHorizon,
    state: *const TypestateState,
    live_loans_mask: DenseBitSet,
    authorized_carrier_loans: DenseBitSet,
    access_path: MovePathId,
    is_mut_or_move: bool,
    is_delegating_scratch_to_d04: bool,
) ?struct { open_tok: TokenIndex, last_use_tok: TokenIndex, is_existing_mut: bool } {
    if (access_path.isNone()) return null;
    const conflict_set = trie.conflict[access_path.asInt()];

    // [1] Check active NLL `LoanId`s whose transitive SSA uses extend past this point:
    const words_n = live_loans_mask.wordCount();
    for (0..words_n) |word_i| {
        var rem = live_loans_mask.wordAt(word_i) & ~authorized_carrier_loans.wordAt(word_i);
        while (rem != 0) {
            const l_idx: usize = word_i * 64 + @ctz(rem);
            rem &= rem - 1;
            if (l_idx >= horizon.loans.len) continue;
            const loan = horizon.loans[l_idx];
            if (is_delegating_scratch_to_d04 and loan.scratch_slot_mask != 0) continue;
            if (loan.is_overflow_wildcard) {
                if (is_mut_or_move or loan.is_mut) {
                    return .{
                        .open_tok = loan.open_token,
                        .last_use_tok = loan.last_use_token,
                        .is_existing_mut = loan.is_mut,
                    };
                }
                continue;
            }
            if (loan.path_id.isNone()) continue;
            if (!conflict_set.isSet(loan.path_id.asInt())) continue;
            if (is_mut_or_move or loan.is_mut) {
                return .{
                    .open_tok = loan.open_token,
                    .last_use_tok = loan.last_use_token,
                    .is_existing_mut = loan.is_mut,
                };
            }
        }
    }

    // [2] Check intra-statement `.scoped_projection` / `.match_guard` Ghost brackets:
    if (conflict_set.firstIntersectionBit(state.inout_loan)) |_| {
        return .{ .open_tok = .none, .last_use_tok = .none, .is_existing_mut = true };
    }
    if (is_mut_or_move) {
        if (conflict_set.firstIntersectionBit(state.let_loan)) |_| {
            return .{ .open_tok = .none, .last_use_tok = .none, .is_existing_mut = false };
        }
    }
    return null;
}

/// Queues `drop_in_place` / `drop_if_live` insertions for `m_idx` (and reverse-order fields on partial struct states).
fn planDropsForMovePath(
    arena_alloc: std.mem.Allocator,
    perm_alloc: std.mem.Allocator,
    body: *MirBody,
    bb_idx: u32,
    before_pos: u32,
    m_idx: usize,
    tok: TokenIndex,
    trie: *const MovePathTrie,
    state: *const TypestateState,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    has_drop_flag_need: []bool,
    planned_drops: *std.ArrayListUnmanaged(PlannedDropInsertion),
) !void {
    if (m_idx >= trie.nodes.len) return;
    const node = trie.nodes[m_idx];
    const fl = node.flags();
    const is_decomposed_linear_struct = !fl.is_auto_drop and fl.is_linear and
        !fl.is_custom_drop_struct and !node.first_child.isNone() and
        trie.nodes[node.first_child.asInt()].proj_kind_raw == @backingInt(mir.ProjKind.field) and
        !hasLiveLinearObligation(trie, state, m_idx);
    if (!fl.is_auto_drop and !is_decomposed_linear_struct) return;

    const base_loc = body.locals.items[node.base_local];
    const leaf_ty = trie.node_types[m_idx];
    if (leaf_ty.isError() or leaf_ty == .unit_ty) return;

    if (!is_decomposed_linear_struct and
        try isTrivialArenaDrop(perm_alloc, pool, sym_table, leaf_ty, base_loc.region_raw))
    {
        return;
    }

    // Decompose non-custom-`Drop` structs/tuples into per-field drops whenever fields have partial move or partial init:
    var has_decomposable_fields = is_decomposed_linear_struct;
    if (!has_decomposable_fields and !fl.is_custom_drop_struct and !node.first_child.isNone()) {
        const first_kind = trie.nodes[node.first_child.asInt()].proj_kind_raw;
        if (first_kind == @backingInt(mir.ProjKind.field)) {
            if (state.maybe_uninit.isSet(m_idx)) {
                has_decomposable_fields = true;
            } else {
                var walk_ch = node.first_child;
                while (!walk_ch.isNone()) {
                    const ch_idx = walk_ch.asInt();
                    if (state.ever_moved.isSet(ch_idx) or state.maybe_uninit.isSet(ch_idx)) {
                        has_decomposable_fields = true;
                        break;
                    }
                    walk_ch = trie.nodes[ch_idx].next_sibling;
                }
            }
        }
    }

    if (has_decomposable_fields) {
        // Collect direct `.field` children and sort by `field_or_variant_ord DESC` (reverse declaration order):
        var children: std.ArrayListUnmanaged(usize) = .empty;
        var ch_id = node.first_child;
        while (!ch_id.isNone()) {
            const ch_idx = ch_id.asInt();
            if (trie.nodes[ch_idx].proj_kind_raw == @backingInt(mir.ProjKind.field)) {
                try children.append(arena_alloc, ch_idx);
            }
            ch_id = trie.nodes[ch_idx].next_sibling;
        }
        std.mem.sortUnstable(usize, children.items, trie.nodes, struct {
            /// Orders child field indices in reverse field declaration order (`DESC`).
            fn isAfterFieldOrd(nodes_slice: []const MovePathNode, lhs_i: usize, rhs_i: usize) bool {
                return nodes_slice[lhs_i].field_or_variant_ord > nodes_slice[rhs_i].field_or_variant_ord;
            }
        }.isAfterFieldOrd);

        for (children.items) |ch_idx| {
            try planDropsForMovePath(
                arena_alloc,
                perm_alloc,
                body,
                bb_idx,
                before_pos,
                ch_idx,
                tok,
                trie,
                state,
                pool,
                sym_table,
                has_drop_flag_need,
                planned_drops,
            );
        }
        return;
    }

    if (!state.maybe_init.isSet(m_idx)) return;
    const pl_id = try ensurePlaceForMovePath(body, trie, m_idx);
    const is_cond = state.maybe_uninit.isSet(m_idx);
    if (is_cond) has_drop_flag_need[m_idx] = true;
    try planned_drops.append(arena_alloc, .{
        .bb_idx = bb_idx,
        .before_pos = before_pos,
        .path_id = MovePathId.fromInt(@intCast(m_idx)),
        .place_id = pl_id,
        .place_ty = leaf_ty,
        .token = tok,
        .is_conditional = is_cond,
    });
}

/// Returns `true` if `raw_ty` unwraps to a safe `&mut T` (`mut_ref_ty`) rather than raw `*mut T` or `&T`.
inline fn isSafeMutRefBase(pool: *const InternPool, raw_ty: TypeId) bool {
    const unwrapped = pool.unwrapUnderlyingType(raw_ty);
    return !unwrapped.isError() and pool.getNode(unwrapped).tag == .mut_ref_ty;
}

/// Runs Pass 2 (`Typestate` + `Transitive NLL` + `@linear` + `unsafe` + `ScratchEffect` + `ElaborateDrops`).
fn runPass2TypestateNllAndDrops(
    arena_alloc: std.mem.Allocator,
    perm_alloc: std.mem.Allocator,
    body: *MirBody,
    dom: *const DominatorTree,
    trie: *const MovePathTrie,
    horizon: *const BodyProvenanceHorizon,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner_opt: ?*const StringInterner,
    summaries: []FnRegionSummary,
    slot_idx: u32,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    out_edges: *std.ArrayListUnmanaged(WitnessCallEdge),
    config: SastConfig,
) !Pass2BodyOutcome {
    var outcome = Pass2BodyOutcome{};
    const is_primary_body = if (config.primary_body_count) |prim_cnt| slot_idx < prim_cnt else true;
    var eff_config = config;
    if (!is_primary_body) eff_config.diagnostic_sink = null;

    const block_count = body.blocks.items.len;
    const local_count = body.locals.items.len;
    const path_count = trie.nodes.len;
    const inst_count = body.insts.len;
    if (block_count == 0 or path_count == 0) return outcome;

    const decl_fallback_span = resolveBodyDeclSpan(body, sym_table);

    // [1] Allocate per-block entry/exit `TypestateState` tables and Ghost open lookup arrays:
    const in_states = try arena_alloc.alloc(TypestateState, block_count);
    const out_states = try arena_alloc.alloc(TypestateState, block_count);
    for (0..block_count) |b_i| {
        in_states[b_i] = try TypestateState.initEmpty(arena_alloc, path_count, local_count);
        out_states[b_i] = try TypestateState.initEmpty(arena_alloc, path_count, local_count);
    }

    // Seed `^bb0` entry state:
    for (0..local_count) |loc_i| {
        if (loc_i >= path_count) break;
        const loc = body.locals.items[loc_i];
        const unwrapped_ty = pool.unwrapUnderlyingType(loc.type_id);
        if (!unwrapped_ty.isError() and pool.getNode(unwrapped_ty).tag == .raw_ptr_ty) {
            in_states[0].local_raw_ptr[loc_i] = .maybe_null;
        }
        if (loc_i >= 1 and loc_i <= body.param_count and loc.mode() != .set_mode) {
            in_states[0].maybe_init.unionInPlace(trie.subtree[loc_i]);
        } else {
            in_states[0].maybe_uninit.unionInPlace(trie.subtree[loc_i]);
        }
    }

    const ghost_open_places = try arena_alloc.alloc(MovePathId, inst_count);
    @memset(ghost_open_places, .none);
    const ghost_open_ops = try arena_alloc.alloc(MirOp, inst_count);
    @memset(ghost_open_ops, .block_param);

    var work_state = try TypestateState.initEmpty(arena_alloc, path_count, local_count);
    var edge_state = try TypestateState.initEmpty(arena_alloc, path_count, local_count);

    // [2.1] Monotone RPO fixed-point iteration across reachable blocks (fail-closed on cap):
    var rpo_iter: usize = 0;
    var has_state_changed = true;
    while (has_state_changed and rpo_iter < 64) : (rpo_iter += 1) {
        has_state_changed = false;
        for (dom.rpo_blocks) |bb_idx| {
            const bb_id = MirBlockId.fromInt(bb_idx);
            if (bb_idx != 0) {
                work_state.resetEmpty();
                for (body.getPredEdges(bb_id)) |pred_eid| {
                    const edge = body.extra_edges.items[pred_eid.asInt()];
                    if (!dom.isReachable(edge.src_bb)) continue;
                    edge_state.copyFrom(out_states[edge.src_bb.asInt()]);

                    // Refine `local_raw_ptr` across `if ptr != null` / `if ptr == null` branch edges:
                    const src_term = body.blocks.items[edge.src_bb.asInt()].terminator;
                    if (src_term.kind == .cond_br and src_term.edge_len == 2) {
                        if (detectRawPtrNullGuard(body, pool, MirValueId.fromInt(src_term.cond_or_val))) |guard| {
                            const is_then_edge = (pred_eid.asInt() == src_term.edge_start);
                            const is_refining_nonnull = (is_then_edge == guard.is_nonnull_on_then);
                            if (is_refining_nonnull and guard.local_idx < edge_state.local_raw_ptr.len and
                                edge_state.local_raw_ptr[guard.local_idx] == .maybe_null)
                            {
                                edge_state.local_raw_ptr[guard.local_idx] = .valid_live;
                            }
                        }
                    }
                    _ = work_state.joinAssignChanged(edge_state);
                }
                if (in_states[bb_idx].joinAssignChanged(work_state)) {
                    has_state_changed = true;
                }
            }

            work_state.copyFrom(in_states[bb_idx]);
            stepTypestateBlockSilent(
                body,
                bb_id,
                trie,
                horizon,
                pool,
                sym_table,
                ghost_open_places,
                ghost_open_ops,
                &work_state,
            );
            if (out_states[bb_idx].joinAssignChanged(work_state)) {
                has_state_changed = true;
            }
        }
    }
    if (has_state_changed) {
        for (dom.rpo_blocks) |bb_idx| {
            in_states[bb_idx].saturateTop(path_count);
            out_states[bb_idx].saturateTop(path_count);
        }
    }

    // [2.2] Diagnostic & Drop-Planning Replay Pass:
    const has_reported_path_diag = try arena_alloc.alloc(bool, path_count);
    @memset(has_reported_path_diag, false);
    const has_drop_flag_need = try arena_alloc.alloc(bool, path_count);
    @memset(has_drop_flag_need, false);
    const is_arena_local_used = try arena_alloc.alloc(bool, local_count);
    @memset(is_arena_local_used, false);
    for (body.locals.items, 0..) |loc, loc_i| {
        if (loc.region_raw != 0) {
            if (loc.region_raw < local_count and isArenaType(pool, sym_table, body.locals.items[loc.region_raw].type_id)) {
                is_arena_local_used[loc.region_raw] = true;
            } else {
                var rev_loc = loc_i;
                while (rev_loc > 0) {
                    rev_loc -= 1;
                    if (isArenaType(pool, sym_table, body.locals.items[rev_loc].type_id)) {
                        is_arena_local_used[rev_loc] = true;
                        break;
                    }
                }
            }
        }
    }
    // Pre-scan all reachable `.call` terminators before `[2.2]` so loop-body arena allocations dominate exit blocks:
    for (dom.rpo_blocks) |pre_bb_idx| {
        const pre_term = body.blocks.items[pre_bb_idx].terminator;
        if (pre_term.kind != .call or pre_term.cond_or_val >= body.calls.items.len) continue;
        const pre_call = body.calls.items[pre_term.cond_or_val];
        const is_lifecycle_call = !pre_call.direct_symbol.isNone() and
            pre_call.direct_symbol.asInt() < sym_table.symbols.items.len and
            ARENA_LIFECYCLE_METHOD_MAP.has(sym_table.getSymbol(pre_call.direct_symbol).name_text);
        if (is_lifecycle_call) continue;
        for (0..pre_call.args_len) |arg_i| {
            const mode = body.call_arg_modes.items[pre_call.modes_start + arg_i];
            const word = body.extra_args.items[pre_call.args_start + arg_i];
            if (extractArgBaseLocal(body, mode, word)) |arg_base| {
                if (arg_base < local_count and isArenaType(pool, sym_table, body.locals.items[arg_base].type_id)) {
                    is_arena_local_used[arg_base] = true;
                }
            }
        }
    }

    var planned_drops: std.ArrayListUnmanaged(PlannedDropInsertion) = .empty;
    var summary = summaries[slot_idx];
    var cur_contracts = summary.contractsScratch();
    var scratch_touch: u2 = cur_contracts.scratch_touch_mask;
    var scratch_rewind: u2 = cur_contracts.scratch_rewind_mask;

    for (dom.rpo_blocks) |bb_idx| {
        const bb_id = MirBlockId.fromInt(bb_idx);
        const inst_slice = body.getBlockInsts(bb_id);
        const loans_before = try arena_alloc.alloc(DenseBitSet, inst_slice.len);
        const scratch_before = try arena_alloc.alloc(u2, inst_slice.len);
        var term_loans: DenseBitSet = DenseBitSet.EMPTY;
        var term_scratch: u2 = 0;

        try computeBlockStepHorizons(
            arena_alloc,
            body,
            bb_id,
            trie,
            horizon,
            pool,
            sym_table,
            loans_before,
            scratch_before,
            &term_loans,
            &term_scratch,
        );

        work_state.copyFrom(in_states[bb_idx]);

        for (inst_slice, 0..) |inst_val, pos| {
            const val_idx = inst_val.asInt();
            const inst = body.getInst(inst_val);
            const tok = body.origin_tokens.items[val_idx];
            const inst_span = resolveTokenSpan(body.file_id, tok, eff_config, decl_fallback_span);
            if (inst.flags.is_unsafe) outcome.has_unsafe_op = true;

            // Check raw-pointer dereference safety (`*raw_ptr`) on place operations:
            if (inst.op == .place_load or inst.op == .place_store or
                inst.op == .place_addr or inst.op == .place_discriminant)
            {
                if (inst.operands.lhs < trie.place_map.len) {
                    const lookup = trie.place_map[inst.operands.lhs];
                    const pl_rec = body.places.items[inst.operands.lhs];
                    if (trie.nodes[lookup.id.asInt()].flags().is_deref_raw_ptr and pl_rec.base < local_count) {
                        outcome.has_unsafe_op = true;
                        const ptr_st = work_state.local_raw_ptr[pl_rec.base];
                        if (ptr_st == .freed_or_dangling and !has_reported_path_diag[pl_rec.base]) {
                            has_reported_path_diag[pl_rec.base] = true;
                            outcome.emitted_error_count += 1;
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0301_use_after_free,
                                .err,
                                inst_span,
                                "dereference of freed or dangling raw pointer inside `unsafe` block",
                                "pointer points to deallocated or out-of-scope storage here",
                                null,
                                null,
                                "ensure the pointed-to allocation or stack variable outlives every raw pointer dereference",
                            );
                        } else if (ptr_st == .maybe_null and !has_reported_path_diag[pl_rec.base]) {
                            has_reported_path_diag[pl_rec.base] = true;
                            outcome.emitted_error_count += 1;
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0303_uninitialized_memory_read,
                                .err,
                                inst_span,
                                "dereference of potentially null raw pointer without prior non-null check",
                                "raw pointer may be null here",
                                null,
                                null,
                                "guard the dereference with `if ptr != (0 as *T) { … }` before accessing `*ptr`",
                            );
                        }
                    }
                }
            }

            switch (inst.op) {
                .ghost_storage_init => {
                    const lid = inst.operands.lhs;
                    if (!hasImmediatePairedStore(body, inst_slice, pos, lid)) {
                        if (lid < trie.direct_local_limit) {
                            applyPathWriteToState(
                                trie,
                                .{ .id = MovePathId.fromInt(lid), .is_partial = false },
                                &work_state,
                            );
                        } else if (trie.direct_local_limit < path_count) {
                            applyPathWriteToState(
                                trie,
                                .{ .id = MovePathId.fromInt(trie.direct_local_limit), .is_partial = true },
                                &work_state,
                            );
                        }
                    }
                },
                .ghost_storage_deinit => {
                    const lid = inst.operands.lhs;
                    const eff_lid = if (lid < trie.direct_local_limit) lid else trie.direct_local_limit;
                    if (eff_lid < path_count) {
                        // [a] Check inner-region borrow escaping past `ghost_storage_deinit(lid)` (`E0306`):
                        const deinit_term = body.blocks.items[bb_idx].terminator;
                        const has_ret_prov_carrier = deinit_term.kind == .ret and
                            hasProvenanceCarrier(pool, sym_table, body.ret_ty);
                        var bit_cursor: usize = 0;
                        while (loans_before[pos].nextSetBit(bit_cursor)) |l_idx| : (bit_cursor = l_idx + 1) {
                            if (l_idx >= horizon.loans.len) break;
                            if (has_ret_prov_carrier) {
                                const is_escaping_via_ret = (deinit_term.cond_or_val < horizon.val_prov.len and
                                    horizon.val_prov[deinit_term.cond_or_val].loan_mask.isSet(l_idx)) or
                                    (local_count > 0 and horizon.local_prov[0].loan_mask.isSet(l_idx));
                                if (is_escaping_via_ret) continue;
                            }
                            const loan = horizon.loans[l_idx];
                            const is_hitting_local = loan.is_overflow_wildcard or
                                (!loan.path_id.isNone() and trie.subtree[eff_lid].isSet(loan.path_id.asInt()));
                            if (is_hitting_local and !has_reported_path_diag[eff_lid]) {
                                has_reported_path_diag[eff_lid] = true;
                                outcome.emitted_error_count += 1;
                                const open_sp = resolveTokenSpan(
                                    body.file_id,
                                    loan.open_token,
                                    eff_config,
                                    inst_span,
                                );
                                const use_sp = if (!loan.last_use_token.isNone())
                                    resolveTokenSpan(body.file_id, loan.last_use_token, eff_config, inst_span)
                                else
                                    inst_span;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0306_region_escape_violation,
                                    .err,
                                    open_sp,
                                    "borrowed value does not live long enough; escapes lexical scope exit",
                                    "borrow originates from inner-scope variable here",
                                    .{ .span = inst_span, .label = "value is dropped at scope exit here", .style = .secondary },
                                    .{ .span = use_sp, .label = "borrow later used outside scope here", .style = .secondary },
                                    "move the binding to the outer scope or pass an outer `Arena` / region parameter",
                                );
                                break;
                            }
                        }

                        // [a2] Check local `&mut T` binding leaving pointee moved-from without re-initialization (`E0303`):
                        if (lid < local_count and lid < trie.direct_local_limit) {
                            const loc_unwrapped = pool.unwrapUnderlyingType(body.locals.items[lid].type_id);
                            if (!loc_unwrapped.isError() and pool.getNode(loc_unwrapped).tag == .mut_ref_ty) {
                                var walk_ch = trie.nodes[lid].first_child;
                                while (!walk_ch.isNone()) {
                                    const ch_i = walk_ch.asInt();
                                    if (trie.subtree[ch_i].intersects(work_state.ever_moved) and
                                        trie.subtree[ch_i].intersects(work_state.maybe_uninit) and
                                        !has_reported_path_diag[lid])
                                    {
                                        has_reported_path_diag[lid] = true;
                                        outcome.emitted_error_count += 1;
                                        try emitSastDiag(
                                            eff_config.diagnostic_sink,
                                            .e0303_uninitialized_memory_read,
                                            .err,
                                            inst_span,
                                            "value moved out through `&mut` reference without re-initialization before borrow ends",
                                            "`&mut` binding goes out of scope leaving referent uninitialized",
                                            null,
                                            null,
                                            "re-initialize `*ref` on all paths after moving out of it",
                                        );
                                        break;
                                    }
                                    walk_ch = trie.nodes[ch_i].next_sibling;
                                }
                            }
                        }

                        // [b] `@linear` Completeness Law (`E0304`):
                        if (lid < trie.direct_local_limit and
                            hasLiveLinearObligation(trie, &work_state, lid) and
                            !has_reported_path_diag[lid])
                        {
                            has_reported_path_diag[lid] = true;
                            outcome.emitted_error_count += 1;
                            const decl_tok = body.locals.items[lid].origin_token;
                            const decl_sp = resolveTokenSpan(body.file_id, decl_tok, eff_config, inst_span);
                            const is_err_pad = body.blocks.items[bb_idx].isCleanupPad();
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0304_resource_or_memory_leak,
                                .err,
                                decl_sp,
                                if (is_err_pad)
                                    "`@linear` resource may leak along early `?` / error unwind path"
                                else
                                    "`@linear` resource goes out of scope without being consumed",
                                "`@linear` value declared here must be explicitly consumed on all paths",
                                .{
                                    .span = inst_span,
                                    .label = if (is_err_pad)
                                        "resource remains unconsumed on error unwind here"
                                    else
                                        "scope exits without consuming `@linear` resource here",
                                    .style = .secondary,
                                },
                                null,
                                "register `defer res.close()` / `errdefer res.rollback()` or pass `res` to a `sink` consumer",
                            );
                        }

                        // [c] `W0308` Unused local `Arena` / `BumpArena`:
                        if (lid < local_count and lid < trie.direct_local_limit and
                            !body.blocks.items[bb_idx].isCleanupPad() and
                            !body.locals.items[lid].flags().is_arg and
                            !body.locals.items[lid].flags().is_synthetic_temp and
                            isOwnedArenaType(pool, sym_table, body.locals.items[lid].type_id) and
                            !is_arena_local_used[lid] and !has_reported_path_diag[lid])
                        {
                            const name_txt = lookupLocalNameText(body.locals.items[lid], interner_opt);
                            if (name_txt.len > 0 and name_txt[0] != '_') {
                                has_reported_path_diag[lid] = true;
                                const decl_sp = resolveTokenSpan(
                                    body.file_id,
                                    body.locals.items[lid].origin_token,
                                    eff_config,
                                    inst_span,
                                );
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .w0308_unused_region_allocation,
                                    .warning,
                                    decl_sp,
                                    "lexical arena / region is initialized but performs zero allocations",
                                    "unused `Arena` binding declared here",
                                    null,
                                    null,
                                    "remove the unused arena or prefix its binding name with `_` if intentional",
                                );
                            }
                        }

                        // [d] Plan `ElaborateDrops` right before `ghost_storage_deinit(lid)`:
                        if (lid < trie.direct_local_limit) {
                            try planDropsForMovePath(
                                arena_alloc,
                                perm_alloc,
                                body,
                                bb_idx,
                                @intCast(pos),
                                lid,
                                tok,
                                trie,
                                &work_state,
                                pool,
                                sym_table,
                                has_drop_flag_need,
                                &planned_drops,
                            );

                            work_state.maybe_init.differenceInPlace(trie.subtree[lid]);
                            work_state.maybe_uninit.unionInPlace(trie.subtree[lid]);
                            work_state.ever_moved.differenceInPlace(trie.subtree[lid]);
                            work_state.ever_freed.differenceInPlace(trie.subtree[lid]);
                        } else {
                            work_state.maybe_uninit.set(eff_lid);
                        }
                    }
                    const dead_lid = LocalId.fromInt(lid);
                    for (horizon.local_prov, 0..) |lp, loc_i| {
                        if (lp.raw_ptr_local == dead_lid and loc_i < work_state.local_raw_ptr.len) {
                            work_state.local_raw_ptr[loc_i] = .freed_or_dangling;
                        }
                    }
                },
                .place_load, .place_discriminant, .place_addr, .soa_column_slice => {
                    if (inst.operands.lhs < trie.place_map.len) {
                        const pl_id = PlaceId.fromInt(inst.operands.lhs);
                        const lookup = trie.place_map[inst.operands.lhs];
                        const m_idx = lookup.id.asInt();
                        const m_flags = trie.nodes[m_idx].flags();
                        const projs = body.getPlaceProjections(pl_id);
                        const base_loc = body.places.items[inst.operands.lhs].base;
                        const has_leading_deref = projs.len > 0 and projs[0].kind == .deref;
                        const is_safe_mut_deref = has_leading_deref and
                            !m_flags.is_behind_shared_ref and !m_flags.is_deref_raw_ptr;
                        const is_mut_addr = (inst.op == .place_addr and inst.operands.rhs != 0);

                        scratch_touch |= detectContextScratchAccess(body, pool, sym_table, pl_id);

                        // Typestate read validity (`E0301` / `E0302` / `E0303`; defer to `E0313` on free/`@linear` sink):
                        const is_deferring_to_e0313 = isBlockFeedingFreeOrLinearSink(
                            body,
                            trie,
                            pool,
                            sym_table,
                            bb_id,
                            pos + 1,
                            lookup.id,
                        );
                        if ((!has_leading_deref or is_safe_mut_deref) and !is_deferring_to_e0313 and !has_reported_path_diag[m_idx]) {
                            if (work_state.ever_freed.isSet(m_idx)) {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0301_use_after_free,
                                    .err,
                                    inst_span,
                                    "use of freed or closed resource",
                                    "value accessed here after explicit free/close",
                                    null,
                                    null,
                                    "do not read or borrow a handle or allocation after freeing/closing it",
                                );
                            } else if (work_state.ever_moved.isSet(m_idx) or
                                hasMovedUninitDescendant(trie, &work_state, m_idx))
                            {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0302_use_after_move,
                                    .err,
                                    inst_span,
                                    "use of moved value",
                                    "value used here after ownership was moved",
                                    null,
                                    null,
                                    "re-initialize the binding before reading it, or borrow with `&` instead of moving",
                                );
                            } else if (!has_leading_deref and work_state.maybe_uninit.isSet(m_idx) and
                                !body.locals.items[base_loc].flags().is_synthetic_temp)
                            {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0303_uninitialized_memory_read,
                                    .err,
                                    inst_span,
                                    "read or borrow of possibly uninitialized binding",
                                    "binding is not definitely initialized on all paths reaching this point",
                                    null,
                                    null,
                                    "initialize the binding on every control-flow branch before reading it",
                                );
                            }
                        }

                        // MVS Law of Exclusivity (`E0305`):
                        const carrier_loans: DenseBitSet = if (has_leading_deref and base_loc < horizon.local_prov.len)
                            horizon.local_prov[base_loc].loan_mask
                        else
                            DenseBitSet.EMPTY;
                        // Skip self-conflict with the `.scoped_projection` bracket opened 1 inst prior for `loadPlaceValue`:
                        var has_prior_self_let = false;
                        if (inst.op == .place_load and pos > 0) {
                            const prev_inst = body.getInst(inst_slice[pos - 1]);
                            if (prev_inst.op == .ghost_access_let and prev_inst.operands.lhs == inst.operands.lhs and
                                work_state.let_loan.isSet(m_idx))
                            {
                                has_prior_self_let = true;
                                work_state.let_loan.unset(m_idx);
                            }
                        }
                        defer if (has_prior_self_let) work_state.let_loan.set(m_idx);
                        if (!has_leading_deref and !has_reported_path_diag[m_idx]) {
                            const is_scratch_access = detectContextScratchAccess(body, pool, sym_table, pl_id) != 0;
                            if (findExclusivityConflict(
                                trie,
                                horizon,
                                &work_state,
                                loans_before[pos],
                                carrier_loans,
                                lookup.id,
                                is_mut_addr,
                                is_scratch_access,
                            )) |conf| {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                const open_sp = if (!conf.open_tok.isNone())
                                    resolveTokenSpan(body.file_id, conf.open_tok, eff_config, inst_span)
                                else
                                    inst_span;
                                const sec_use: ?LabeledSpan = if (!conf.last_use_tok.isNone()) .{
                                    .span = resolveTokenSpan(body.file_id, conf.last_use_tok, eff_config, inst_span),
                                    .label = "conflicting borrow remains live until used here",
                                    .style = .secondary,
                                } else null;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0305_exclusivity_violation,
                                    .err,
                                    inst_span,
                                    if (is_mut_addr)
                                        "cannot borrow value as mutable while another borrow is active"
                                    else
                                        "cannot borrow/read value while an exclusive mutable borrow is active",
                                    if (is_mut_addr) "mutable borrow occurs here" else "shared access occurs here",
                                    .{
                                        .span = open_sp,
                                        .label = if (conf.is_existing_mut)
                                            "active mutable borrow opened here"
                                        else
                                            "active shared borrow opened here",
                                        .style = .secondary,
                                    },
                                    sec_use,
                                    "finish using the active borrow before mutating or exclusively borrowing the same value",
                                );
                            }
                        }
                    }
                },
                .ghost_storage_move => {
                    if (inst.operands.lhs < trie.place_map.len) {
                        const pl_id = PlaceId.fromInt(inst.operands.lhs);
                        const lookup = trie.place_map[inst.operands.lhs];
                        const m_idx = lookup.id.asInt();
                        const node_fl = trie.nodes[m_idx].flags();

                        // Duplicate `@linear` consumption (`E0313`) when already moved/freed and not handled by free-call terminator:
                        if (node_fl.is_linear and
                            (work_state.ever_moved.isSet(m_idx) or work_state.ever_freed.isSet(m_idx)) and
                            !isBlockTerminatedByExplicitFreeOf(body, trie, pool, sym_table, bb_id, lookup.id) and
                            !has_reported_path_diag[m_idx])
                        {
                            has_reported_path_diag[m_idx] = true;
                            outcome.emitted_error_count += 1;
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0313_double_free_or_close,
                                .err,
                                inst_span,
                                "double free or duplicate `@linear` resource consumption",
                                "`@linear` resource consumed a second time here",
                                null,
                                null,
                                "remove the duplicate consumption (check active `defer` / `errdefer` cleanups)",
                            );
                        }

                        // Forbid moving a field out of a nominal struct implementing custom `Drop` (`E0302`):
                        var walk_anc = trie.nodes[m_idx].parent;
                        var has_custom_drop_anc = false;
                        while (!walk_anc.isNone()) {
                            if (trie.nodes[walk_anc.asInt()].flags().is_custom_drop_struct) {
                                has_custom_drop_anc = true;
                                break;
                            }
                            walk_anc = trie.nodes[walk_anc.asInt()].parent;
                        }
                        // Also forbid moving out of a shared reference (`&T`) or dynamic index (`is_partial`) on non-`Copy`:
                        if (!node_fl.is_copy and (has_custom_drop_anc or node_fl.is_behind_shared_ref or lookup.is_partial) and
                            !has_reported_path_diag[m_idx])
                        {
                            has_reported_path_diag[m_idx] = true;
                            outcome.emitted_error_count += 1;
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0302_use_after_move,
                                .err,
                                inst_span,
                                if (has_custom_drop_anc)
                                    "cannot move non-`Copy` field out of a type implementing custom `Drop`"
                                else if (lookup.is_partial)
                                    "cannot move non-`Copy` element out of an indexed array or slice"
                                else
                                    "cannot move non-`Copy` value out of a shared reference",
                                "illegal partial or borrowed move occurs here",
                                null,
                                null,
                                "borrow the element/field with `&` or swap a replacement in via mutable access",
                            );
                        }

                        // Moving a borrowed value while an NLL loan is active violates exclusivity (`E0305`):
                        if (!node_fl.is_copy and !has_reported_path_diag[m_idx]) {
                            const projs = body.getPlaceProjections(pl_id);
                            const has_leading_deref = projs.len > 0 and projs[0].kind == .deref;
                            if (!has_leading_deref) {
                                if (findExclusivityConflict(
                                    trie,
                                    horizon,
                                    &work_state,
                                    loans_before[pos],
                                    DenseBitSet.EMPTY,
                                    lookup.id,
                                    true,
                                    false,
                                )) |conf| {
                                    has_reported_path_diag[m_idx] = true;
                                    outcome.emitted_error_count += 1;
                                    const open_sp = if (!conf.open_tok.isNone())
                                        resolveTokenSpan(body.file_id, conf.open_tok, eff_config, inst_span)
                                    else
                                        inst_span;
                                    try emitSastDiag(
                                        eff_config.diagnostic_sink,
                                        .e0305_exclusivity_violation,
                                        .err,
                                        inst_span,
                                        "cannot move out of value while it is borrowed",
                                        "move out of borrowed value occurs here",
                                        .{
                                            .span = open_sp,
                                            .label = "borrow opened here",
                                            .style = .secondary,
                                        },
                                        null,
                                        "ensure all borrows of this value finish before moving ownership",
                                    );
                                }
                            }
                        }

                        const base = body.places.items[inst.operands.lhs].base;
                        if (base >= 1 and base <= body.param_count and base - 1 < 32 and
                            body.locals.items[base].mode() == .sink_mode and !node_fl.is_copy)
                        {
                            summary.consumed_param_mask |= (@as(u32, 1) << @intCast(base - 1));
                        }

                        if (!node_fl.is_copy) {
                            applyPathMoveOrFreeToState(trie, lookup, false, &work_state);
                        }
                    }
                },
                .ghost_access_let, .ghost_access_inout, .ghost_access_set => {
                    if (inst.operands.lhs < trie.place_map.len) {
                        const pl_id = PlaceId.fromInt(inst.operands.lhs);
                        const lookup = trie.place_map[inst.operands.lhs];
                        const m_idx = lookup.id.asInt();
                        const base_loc = body.places.items[inst.operands.lhs].base;
                        const projs = body.getPlaceProjections(pl_id);
                        const has_leading_deref = projs.len > 0 and projs[0].kind == .deref;
                        const is_safe_mut_deref = has_leading_deref and base_loc < local_count and
                            isSafeMutRefBase(pool, body.locals.items[base_loc].type_id);
                        const bkind: mir.GhostBorrowKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.operands.rhs))));
                        const is_mut_open = (inst.op != .ghost_access_let);

                        scratch_touch |= detectContextScratchAccess(body, pool, sym_table, pl_id);

                        // Check read/inout on freed/moved/uninit (`set` opens uninitialized out-params validly!):
                        const is_deferring_open_to_e0313 = isBlockFeedingFreeOrLinearSink(
                            body,
                            trie,
                            pool,
                            sym_table,
                            bb_id,
                            pos + 1,
                            lookup.id,
                        );
                        if (inst.op != .ghost_access_set and (!has_leading_deref or is_safe_mut_deref) and
                            !is_deferring_open_to_e0313 and !has_reported_path_diag[m_idx])
                        {
                            if (work_state.ever_freed.isSet(m_idx)) {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0301_use_after_free,
                                    .err,
                                    inst_span,
                                    "cannot borrow freed or closed resource",
                                    "borrow after free/close occurs here",
                                    null,
                                    null,
                                    "do not access a handle after closing or freeing it",
                                );
                            } else if (work_state.ever_moved.isSet(m_idx) or
                                hasMovedUninitDescendant(trie, &work_state, m_idx))
                            {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0302_use_after_move,
                                    .err,
                                    inst_span,
                                    "cannot borrow value after it was moved",
                                    "borrow of moved value occurs here",
                                    null,
                                    null,
                                    "re-initialize the binding before borrowing it again",
                                );
                            }
                        }

                        if (bkind != .addr_borrow and !has_leading_deref and !has_reported_path_diag[m_idx]) {
                            if (findExclusivityConflict(
                                trie,
                                horizon,
                                &work_state,
                                loans_before[pos],
                                DenseBitSet.EMPTY,
                                lookup.id,
                                is_mut_open,
                                true,
                            )) |conf| {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                const open_sp = if (!conf.open_tok.isNone())
                                    resolveTokenSpan(body.file_id, conf.open_tok, eff_config, inst_span)
                                else
                                    inst_span;
                                const sec_use: ?LabeledSpan = if (!conf.last_use_tok.isNone()) .{
                                    .span = resolveTokenSpan(body.file_id, conf.last_use_tok, eff_config, inst_span),
                                    .label = "active borrow later used here",
                                    .style = .secondary,
                                } else null;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0305_exclusivity_violation,
                                    .err,
                                    inst_span,
                                    "conflicting simultaneous borrows violate the Law of Exclusivity",
                                    if (is_mut_open) "exclusive access requested here" else "shared access requested here",
                                    .{
                                        .span = open_sp,
                                        .label = if (conf.is_existing_mut)
                                            "active mutable borrow opened here"
                                        else
                                            "active shared borrow opened here",
                                        .style = .secondary,
                                    },
                                    sec_use,
                                    "split the accesses into sequential statements so the earlier borrow ends before mutation",
                                );
                            }
                        }

                        if (bkind != .addr_borrow) {
                            ghost_open_places[val_idx] = lookup.id;
                            ghost_open_ops[val_idx] = inst.op;
                            if (inst.op == .ghost_access_let) {
                                work_state.let_loan.set(m_idx);
                            } else {
                                work_state.inout_loan.set(m_idx);
                            }
                        }
                    }
                },
                .ghost_access_end => {
                    if (inst.operands.lhs < ghost_open_places.len) {
                        const closed_m = ghost_open_places[inst.operands.lhs];
                        if (!closed_m.isNone()) {
                            if (ghost_open_ops[inst.operands.lhs] == .ghost_access_let) {
                                work_state.let_loan.unset(closed_m.asInt());
                            } else {
                                work_state.inout_loan.unset(closed_m.asInt());
                            }
                        }
                    }
                },
                .place_store => {
                    if (inst.operands.lhs < trie.place_map.len) {
                        const pl_id = PlaceId.fromInt(inst.operands.lhs);
                        const lookup = trie.place_map[inst.operands.lhs];
                        const m_idx = lookup.id.asInt();
                        const pl_rec = body.places.items[inst.operands.lhs];
                        const projs = body.getPlaceProjections(pl_id);
                        const has_leading_deref = projs.len > 0 and projs[0].kind == .deref;
                        const is_safe_mut_deref = has_leading_deref and pl_rec.base < local_count and
                            isSafeMutRefBase(pool, body.locals.items[pl_rec.base].type_id);

                        scratch_touch |= detectContextScratchAccess(body, pool, sym_table, pl_id);

                        // [a] Exclusivity check on direct mutation (`E0305`, ignoring own `ghost_access_set` 1-2 insts prior):
                        if (!has_leading_deref and pl_rec.base != 0 and !has_reported_path_diag[m_idx]) {
                            const has_prior_self_inout = work_state.inout_loan.isSet(m_idx);
                            if (has_prior_self_inout) work_state.inout_loan.unset(m_idx);
                            defer if (has_prior_self_inout) work_state.inout_loan.set(m_idx);
                            if (findExclusivityConflict(
                                trie,
                                horizon,
                                &work_state,
                                loans_before[pos],
                                DenseBitSet.EMPTY,
                                lookup.id,
                                true,
                                false,
                            )) |conf| {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                const open_sp = if (!conf.open_tok.isNone())
                                    resolveTokenSpan(body.file_id, conf.open_tok, eff_config, inst_span)
                                else
                                    inst_span;
                                const sec_use: ?LabeledSpan = if (!conf.last_use_tok.isNone()) .{
                                    .span = resolveTokenSpan(body.file_id, conf.last_use_tok, eff_config, inst_span),
                                    .label = "borrow later used here",
                                    .style = .secondary,
                                } else null;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0305_exclusivity_violation,
                                    .err,
                                    inst_span,
                                    "cannot assign to binding while it is borrowed",
                                    "assignment to borrowed binding occurs here",
                                    .{
                                        .span = open_sp,
                                        .label = "borrow opened here",
                                        .style = .secondary,
                                    },
                                    sec_use,
                                    "complete all uses of the borrow before reassigning the underlying variable",
                                );
                            }
                        }

                        // [b] Region escape check on deref/out-param/closure store (`Depth(dst) < Depth(src)` -> `E0306`):
                        if (inst.operands.rhs < horizon.val_prov.len and pl_rec.base < local_count) {
                            const rhs_prov = horizon.val_prov[inst.operands.rhs];
                            const rhs_ty = body.getInst(MirValueId.fromInt(inst.operands.rhs)).type_id;
                            if (hasProvenanceCarrier(pool, sym_table, rhs_ty)) {
                                const is_outer_ref_write = has_leading_deref or
                                    (pl_rec.base >= 1 and pl_rec.base <= body.param_count and
                                        (body.locals.items[pl_rec.base].mode() == .inout_mode or
                                            body.locals.items[pl_rec.base].mode() == .set_mode));
                                const unwrapped_rhs = pool.unwrapUnderlyingType(rhs_ty);
                                const is_closure_store = !unwrapped_rhs.isError() and
                                    (pool.getNode(unwrapped_rhs).tag == .closure_ty or
                                        pool.getNode(unwrapped_rhs).tag == .fn_ty);
                                const is_unloaned_local_escape = !has_leading_deref and pl_rec.base != 0 and
                                    (rhs_prov.loan_mask.isEmpty() or is_closure_store) and
                                    rhs_prov.max_depth > horizon.local_decl_depth[pl_rec.base];
                                if (is_outer_ref_write or is_unloaned_local_escape) {
                                    const dst_depth = if (has_leading_deref)
                                        @min(horizon.local_decl_depth[pl_rec.base], horizon.local_prov[pl_rec.base].min_target_depth)
                                    else
                                        horizon.local_decl_depth[pl_rec.base];
                                    if (rhs_prov.max_depth > dst_depth and !has_reported_path_diag[pl_rec.base]) {
                                        has_reported_path_diag[pl_rec.base] = true;
                                        outcome.emitted_error_count += 1;
                                        try emitSastDiag(
                                            eff_config.diagnostic_sink,
                                            .e0306_region_escape_violation,
                                            .err,
                                            inst_span,
                                            "inner-region reference or view cannot escape into outer reference/parameter",
                                            "value with shorter lifetime stored into longer-lived target here",
                                            null,
                                            null,
                                            "allocate in the destination's arena or avoid storing local references into outer slots",
                                        );
                                    }
                                }

                                var dst_mask: u8 = 0;
                                if (has_leading_deref) {
                                    dst_mask = horizon.local_prov[pl_rec.base].param_mask;
                                } else if (pl_rec.base >= 1 and pl_rec.base <= body.param_count and pl_rec.base - 1 < 8) {
                                    const param_mode = body.locals.items[pl_rec.base].mode();
                                    if (param_mode == .inout_mode or param_mode == .set_mode) {
                                        dst_mask = @as(u8, 1) << @intCast(pl_rec.base - 1);
                                    }
                                }
                                if (dst_mask != 0) {
                                    for (0..8) |dst_ord| {
                                        if (((dst_mask >> @intCast(dst_ord)) & 1) == 0) continue;
                                        for (0..8) |src_ord| {
                                            if (src_ord != dst_ord and ((rhs_prov.param_mask >> @intCast(src_ord)) & 1) != 0) {
                                                summary.param_flow_matrix |= (@as(u64, 1) << @intCast(src_ord * 8 + dst_ord));
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // [c] Live `@linear` overwrite (`E0304`) & live `AutoDrop` reassignment (`ElaborateDrops`):
                        if (!lookup.is_partial and (!has_leading_deref or is_safe_mut_deref) and pl_rec.base != 0) {
                            const m_flags = trie.nodes[m_idx].flags();
                            if (hasLiveLinearObligation(trie, &work_state, m_idx) and !has_reported_path_diag[m_idx]) {
                                has_reported_path_diag[m_idx] = true;
                                outcome.emitted_error_count += 1;
                                try emitSastDiag(
                                    eff_config.diagnostic_sink,
                                    .e0304_resource_or_memory_leak,
                                    .err,
                                    inst_span,
                                    "overwriting a live `@linear` binding leaks its previous unconsumed value",
                                    "`@linear` binding overwritten before previous resource was consumed",
                                    null,
                                    null,
                                    "consume or close the existing `@linear` value before reassigning this variable",
                                );
                            } else if ((m_flags.is_auto_drop or m_flags.is_linear) and work_state.maybe_init.isSet(m_idx)) {
                                try planDropsForMovePath(
                                    arena_alloc,
                                    perm_alloc,
                                    body,
                                    bb_idx,
                                    @intCast(pos),
                                    m_idx,
                                    tok,
                                    trie,
                                    &work_state,
                                    pool,
                                    sym_table,
                                    has_drop_flag_need,
                                    &planned_drops,
                                );
                            }
                        }

                        applyPathWriteToState(trie, lookup, &work_state);
                        if (pl_rec.proj_len == 0 and pl_rec.base < work_state.local_raw_ptr.len and
                            inst.operands.rhs < horizon.val_prov.len)
                        {
                            const rhs_ptr = horizon.val_prov[inst.operands.rhs].raw_ptr_state;
                            if (rhs_ptr != .unknown_or_non_ptr) {
                                work_state.local_raw_ptr[pl_rec.base] = rhs_ptr;
                            }
                        }
                    }
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    if (ikind == .ghost_storage_free and inst.operands.lhs < trie.place_map.len) {
                        const lookup = trie.place_map[inst.operands.lhs];
                        const m_idx = lookup.id.asInt();
                        if (work_state.ever_freed.isSet(m_idx) and !has_reported_path_diag[m_idx]) {
                            has_reported_path_diag[m_idx] = true;
                            outcome.emitted_error_count += 1;
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0313_double_free_or_close,
                                .err,
                                inst_span,
                                "double free or duplicate deallocation of storage",
                                "value freed a second time here",
                                null,
                                null,
                                "remove the redundant deallocation or guard cleanup with ownership transfer",
                            );
                        }
                        applyPathMoveOrFreeToState(trie, lookup, true, &work_state);
                        const base = body.places.items[inst.operands.lhs].base;
                        if (base < work_state.local_raw_ptr.len) {
                            work_state.local_raw_ptr[base] = .freed_or_dangling;
                        }
                    }
                },
                else => {},
            }
        }

        // Terminator checks (`.ret` completeness/escape/sink-drops & `.call` scratch/escape/free):
        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .ret) {
            const ret_tok = if (term.cond_or_val < body.origin_tokens.items.len)
                body.origin_tokens.items[term.cond_or_val]
            else
                TokenIndex.none;
            const ret_span = resolveTokenSpan(body.file_id, ret_tok, eff_config, decl_fallback_span);
            const is_error_ret = isCleanupOrErrorReturnBlock(body, pool, bb_idx, term);

            // [a] Check return provenance & stack/local-arena/`@local`-closure non-escape (`E0306`):
            var ret_prov = if (local_count > 0) horizon.local_prov[0] else ValueProvenance{};
            if (term.cond_or_val < horizon.val_prov.len) {
                ret_prov = try ValueProvenance.merge(ret_prov, horizon.val_prov[term.cond_or_val], arena_alloc);
            }
            if (hasProvenanceCarrier(pool, sym_table, body.ret_ty)) {
                summary.ret_provenance_mask |= @as(u64, ret_prov.param_mask);
                if (ret_prov.max_depth >= DEPTH_FN_FRAME and !has_reported_path_diag[0]) {
                    has_reported_path_diag[0] = true;
                    outcome.emitted_error_count += 1;
                    const sec_origin: ?LabeledSpan = if (!ret_prov.origin_local.isNone() and
                        ret_prov.origin_local.asInt() < local_count)
                        .{
                            .span = resolveTokenSpan(
                                body.file_id,
                                body.locals.items[ret_prov.origin_local.asInt()].origin_token,
                                eff_config,
                                ret_span,
                            ),
                            .label = "local stack or lexical `Arena` storage originates here",
                            .style = .secondary,
                        }
                    else
                        null;
                    try emitSastDiag(
                        eff_config.diagnostic_sink,
                        .e0306_region_escape_violation,
                        .err,
                        ret_span,
                        "cannot return reference, slice, view, or `@local` closure tied to stack or local `Arena`",
                        "local-region value escapes function frame on `return` here",
                        sec_origin,
                        null,
                        "return an owned value (`Vec`, `String`) or accept a caller `inout Arena` parameter",
                    );
                }
            }

            // [b] Check formal parameters (`inout`/`&mut` re-init, `set` normal-return init, `sink` `@linear` & `AutoDrop` drops):
            var param_rev: usize = body.param_count;
            while (param_rev > 0) {
                param_rev -= 1;
                const slot_i = 1 + param_rev;
                if (slot_i >= local_count or slot_i >= path_count) continue;
                const param_loc = body.locals.items[slot_i];
                const param_mode = param_loc.mode();
                const param_sp = resolveTokenSpan(body.file_id, param_loc.origin_token, eff_config, ret_span);

                if (param_mode == .inout_mode) {
                    if (trie.subtree[slot_i].intersects(work_state.maybe_uninit) and !has_reported_path_diag[slot_i]) {
                        has_reported_path_diag[slot_i] = true;
                        outcome.emitted_error_count += 1;
                        try emitSastDiag(
                            eff_config.diagnostic_sink,
                            .e0303_uninitialized_memory_read,
                            .err,
                            ret_span,
                            "`inout` parameter moved from without dominating re-initialization before return",
                            "function exits while `inout` parameter may be uninitialized",
                            .{ .span = param_sp, .label = "`inout` parameter declared here", .style = .secondary },
                            null,
                            "re-initialize the `inout` parameter on all normal and `?` return paths",
                        );
                    }
                } else if (slot_i < trie.direct_local_limit and isSafeMutRefBase(pool, param_loc.type_id)) {
                    var walk_ch = trie.nodes[slot_i].first_child;
                    while (!walk_ch.isNone()) {
                        const ch_i = walk_ch.asInt();
                        if (trie.nodes[ch_i].proj_kind_raw == @backingInt(mir.ProjKind.deref) and
                            trie.subtree[ch_i].intersects(work_state.ever_moved) and
                            trie.subtree[ch_i].intersects(work_state.maybe_uninit) and
                            !has_reported_path_diag[ch_i])
                        {
                            has_reported_path_diag[ch_i] = true;
                            outcome.emitted_error_count += 1;
                            try emitSastDiag(
                                eff_config.diagnostic_sink,
                                .e0303_uninitialized_memory_read,
                                .err,
                                ret_span,
                                "`&mut` parameter referent moved from without dominating re-initialization before return",
                                "function exits while `*param` may remain uninitialized",
                                .{ .span = param_sp, .label = "`&mut` parameter declared here", .style = .secondary },
                                null,
                                "re-initialize `*param` on all normal and `?` return paths",
                            );
                            break;
                        }
                        walk_ch = trie.nodes[ch_i].next_sibling;
                    }
                } else if (param_mode == .set_mode and !is_error_ret) {
                    if (work_state.maybe_uninit.isSet(slot_i) and !has_reported_path_diag[slot_i]) {
                        has_reported_path_diag[slot_i] = true;
                        outcome.emitted_error_count += 1;
                        try emitSastDiag(
                            eff_config.diagnostic_sink,
                            .e0303_uninitialized_memory_read,
                            .err,
                            ret_span,
                            "`set` out-parameter is not definitely initialized before normal return",
                            "normal return reached while `set` parameter may still be uninitialized",
                            .{ .span = param_sp, .label = "`set` parameter declared here", .style = .secondary },
                            null,
                            "assign a value to the `set` parameter on every non-error return path",
                        );
                    }
                } else if (param_mode == .sink_mode) {
                    const p_flags = trie.nodes[slot_i].flags();
                    if (hasLiveLinearObligation(trie, &work_state, slot_i) and !has_reported_path_diag[slot_i]) {
                        has_reported_path_diag[slot_i] = true;
                        outcome.emitted_error_count += 1;
                        try emitSastDiag(
                            eff_config.diagnostic_sink,
                            .e0304_resource_or_memory_leak,
                            .err,
                            ret_span,
                            "`sink` `@linear` parameter is not consumed before function return",
                            "function returns while `sink` `@linear` parameter remains live",
                            .{ .span = param_sp, .label = "`sink` `@linear` parameter declared here", .style = .secondary },
                            null,
                            "consume or close the `sink` parameter on all normal and `?` return paths",
                        );
                    } else if ((p_flags.is_auto_drop or p_flags.is_linear) and work_state.maybe_init.isSet(slot_i)) {
                        try planDropsForMovePath(
                            arena_alloc,
                            perm_alloc,
                            body,
                            bb_idx,
                            mir.NONE_U32,
                            slot_i,
                            ret_tok,
                            trie,
                            &work_state,
                            pool,
                            sym_table,
                            has_drop_flag_need,
                            &planned_drops,
                        );
                    }
                }
            }
        } else if (term.kind == .call and term.cond_or_val < body.calls.items.len) {
            const call_site = body.calls.items[term.cond_or_val];
            const call_span = resolveTokenSpan(body.file_id, call_site.origin_token, eff_config, decl_fallback_span);
            const callee_opt = try lookupCalleeSummary(
                call_site.direct_def_id,
                call_site.direct_symbol,
                summaries,
                key_to_slot,
                sym_to_slot,
                eff_config,
            );

            // [a] Mark `Arena` locals used if invoked with non-lifecycle allocation methods (`W0308`):
            const is_lifecycle_call = !call_site.direct_symbol.isNone() and
                call_site.direct_symbol.asInt() < sym_table.symbols.items.len and
                ARENA_LIFECYCLE_METHOD_MAP.has(sym_table.getSymbol(call_site.direct_symbol).name_text);
            if (!is_lifecycle_call) {
                for (0..call_site.args_len) |arg_i| {
                    const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                    const word = body.extra_args.items[call_site.args_start + arg_i];
                    if (extractArgBaseLocal(body, mode, word)) |arg_base| {
                        if (arg_base < local_count and isArenaType(pool, sym_table, body.locals.items[arg_base].type_id)) {
                            is_arena_local_used[arg_base] = true;
                        }
                    }
                }
            }

            // [b] `D-04` `Context.scratch[0..2]` ping-pong aliasing conflict (`E0328`):
            var call_rewind_mask: u2 = 0;
            var arg_live_scratch: u2 = 0;
            var is_forwarding_ctx = false;
            const is_reset_call = isScratchResetCall(sym_table, call_site);
            for (0..call_site.args_len) |arg_i| {
                const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                const word = body.extra_args.items[call_site.args_start + arg_i];
                const is_ctx_arg = isContextArgPlaceOrVal(body, pool, sym_table, mode, word);
                if (is_ctx_arg) is_forwarding_ctx = true;
                if (mode != .let_mode and mode != .sink_mode and word < body.places.items.len) {
                    const sm = detectContextScratchAccess(body, pool, sym_table, PlaceId.fromInt(word));
                    scratch_touch |= sm;
                    if (arg_i == 0 and sm != 0 and is_reset_call) {
                        call_rewind_mask |= sm;
                    } else if (!is_ctx_arg) {
                        const projs = body.getPlaceProjections(PlaceId.fromInt(word));
                        const base_loc = body.places.items[word].base;
                        if (projs.len > 0 and projs[0].kind == .deref and base_loc < local_count) {
                            arg_live_scratch |= horizon.local_prov[base_loc].scratch_mask;
                        }
                    }
                } else if ((mode == .let_mode or mode == .sink_mode) and word < horizon.val_prov.len) {
                    const sm = horizon.val_prov[word].scratch_mask;
                    if (arg_i == 0 and sm != 0 and is_reset_call) {
                        call_rewind_mask |= sm;
                    } else if (!is_ctx_arg) {
                        arg_live_scratch |= sm;
                    }
                }
            }
            if (is_forwarding_ctx) {
                if (callee_opt) |csum| {
                    scratch_touch |= csum.contractsScratch().scratch_touch_mask;
                    call_rewind_mask |= csum.contractsScratch().scratch_rewind_mask;
                }
            }
            scratch_rewind |= call_rewind_mask;

            if ((call_rewind_mask & (term_scratch | arg_live_scratch)) != 0) {
                outcome.emitted_error_count += 1;
                var open_tok: TokenIndex = .none;
                for (horizon.val_prov) |vp| {
                    if ((vp.scratch_mask & call_rewind_mask) != 0 and !vp.scratch_open_token.isNone()) {
                        open_tok = vp.scratch_open_token;
                        break;
                    }
                }
                const sec_open: ?LabeledSpan = if (!open_tok.isNone()) .{
                    .span = resolveTokenSpan(body.file_id, open_tok, eff_config, call_span),
                    .label = "live `Context.scratch` allocation borrowed here",
                    .style = .secondary,
                } else null;
                try emitSastDiag(
                    eff_config.diagnostic_sink,
                    .e0328_scratch_arena_ping_pong_conflict,
                    .err,
                    call_span,
                    "callee rewinds a `Context.scratch` arena slot while a slice from that slot is still live",
                    "call rewinds active scratch arena slot here",
                    sec_open,
                    null,
                    "pass the active scratch arena to `ctx.scratch_scope(…)` so the callee uses complement slot `1 - i`",
                );
            }

            // [c] Callee `param_flow_matrix` & `global_escape_mask` region escape checks (`E0306`):
            if (callee_opt) |csum| {
                try accumulateCallFlowAndGlobalEscape(
                    body,
                    horizon,
                    call_site,
                    csum,
                    &summary.param_flow_matrix,
                    &summary.global_escape_mask,
                );
                try verifyCalleeRegionFlowEscape(
                    body,
                    horizon,
                    call_site,
                    csum,
                    call_span,
                    eff_config,
                    &outcome,
                );
            }

            // [d] Explicit free / duplicate `@linear` close check (`E0313`):
            try checkAndApplyCallFreeDiagnostics(
                body,
                trie,
                pool,
                sym_table,
                call_site,
                call_span,
                eff_config,
                has_reported_path_diag,
                &work_state,
                &outcome,
            );
        }
    }

    cur_contracts.scratch_touch_mask = scratch_touch;
    cur_contracts.scratch_rewind_mask = scratch_rewind;
    summary.setContractsScratch(cur_contracts);
    summaries[slot_idx] = summary;

    // [2.3] Materialize `planned_drops` & `_drop_flag` locals without splitting basic blocks:
    if (planned_drops.items.len > 0 and !body.is_sast_elaborated) {
        try materializePlannedDrops(
            arena_alloc,
            perm_alloc,
            body,
            trie,
            pool,
            sym_table,
            has_drop_flag_need,
            planned_drops.items,
            key_to_slot,
            sym_to_slot,
            out_edges,
            &outcome,
        );
    }
    body.is_sast_elaborated = true;

    return outcome;
}

/// Returns `true` if `bb_idx` is a cleanup pad or returns an `Err`/`None` variant (`set` param exemption).
fn isCleanupOrErrorReturnBlock(
    body: *const MirBody,
    pool: *const InternPool,
    bb_idx: u32,
    term: mir.MirTerminator,
) bool {
    if (body.blocks.items[bb_idx].isCleanupPad()) return true;
    if (term.cond_or_val >= body.insts.len) return false;
    const ret_inst = body.getInst(MirValueId.fromInt(term.cond_or_val));
    if (ret_inst.op != .aggregate_make) return false;
    const agg_kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(ret_inst.aux_u16))));
    if (agg_kind != .tagged_variant) return false;
    const tag_ord = ret_inst.operands.rhs >> 16;
    const unwrapped_ret = pool.unwrapUnderlyingType(body.ret_ty);
    if (unwrapped_ret.isError()) return false;
    const ret_tag = pool.getNode(unwrapped_ret).tag;
    return (ret_tag == .result_ty and tag_ord == 1) or (ret_tag == .optional_ty and tag_ord == 0);
}

/// Extracts the base `LocalId.asInt()` of a call argument `(mode, word)` (`null` if pure rvalue).
fn extractArgBaseLocal(body: *const MirBody, mode: ParamMode, word: u32) ?u32 {
    if (mode == .let_mode or mode == .sink_mode) {
        if (word >= body.insts.len) return null;
        const inst = body.getInst(MirValueId.fromInt(word));
        if ((inst.op == .place_load or inst.op == .place_addr) and inst.operands.lhs < body.places.items.len) {
            return body.places.items[inst.operands.lhs].base;
        }
        return null;
    }
    if (word < body.places.items.len) {
        return body.places.items[word].base;
    }
    return null;
}

/// Enforces `Depth(dst) <= Depth(src)` across `csum.param_flow_matrix` and `csum.global_escape_mask` (`E0306`).
fn verifyCalleeRegionFlowEscape(
    body: *const MirBody,
    horizon: *const BodyProvenanceHorizon,
    call_site: mir.MirCallSite,
    csum: FnRegionSummary,
    call_span: Span,
    config: SastConfig,
    outcome: *Pass2BodyOutcome,
) !void {
    const getArgDepthAndOrigin = struct {
        //! Local helper extracting the effective lexical region depth and origin local of a call argument.

        /// Returns `(depth, origin)` for `(arg_mode, arg_word)` as either destination (`is_dst`) or source.
        fn run(
            body_ref: *const MirBody,
            hor_ref: *const BodyProvenanceHorizon,
            arg_mode: ParamMode,
            arg_word: u32,
            is_dst: bool,
        ) struct { depth: u16, origin: LocalId } {
            if (arg_mode == .let_mode or arg_mode == .sink_mode) {
                if (arg_word < hor_ref.val_prov.len) {
                    const vp = hor_ref.val_prov[arg_word];
                    return .{
                        .depth = if (is_dst and vp.min_target_depth != std.math.maxInt(u16))
                            @min(vp.max_depth, vp.min_target_depth)
                        else
                            vp.max_depth,
                        .origin = vp.origin_local,
                    };
                }
                return .{ .depth = DEPTH_STATIC, .origin = .none };
            }
            if (arg_word < body_ref.places.items.len) {
                const base = body_ref.places.items[arg_word].base;
                if (base < hor_ref.local_decl_depth.len) {
                    return .{ .depth = hor_ref.local_decl_depth[base], .origin = LocalId.fromInt(base) };
                }
            }
            return .{ .depth = DEPTH_STATIC, .origin = .none };
        }
    }.run;

    if (csum.global_escape_mask != 0) {
        const lim = @min(@as(usize, call_site.args_len), 32);
        for (0..lim) |arg_i| {
            if (((csum.global_escape_mask >> @intCast(arg_i)) & 1) == 0) continue;
            const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
            const word = body.extra_args.items[call_site.args_start + arg_i];
            const src_info = getArgDepthAndOrigin(body, horizon, mode, word, false);
            if (src_info.depth > DEPTH_STATIC) {
                outcome.emitted_error_count += 1;
                try emitSastDiag(
                    config.diagnostic_sink,
                    .e0306_region_escape_violation,
                    .err,
                    call_span,
                    "non-`'static` reference or view escapes into global/static storage via callee",
                    "local or caller-scoped borrow passed to global-escaping parameter here",
                    null,
                    null,
                    "only `'static` data may be stored into global/static variables",
                );
                return;
            }
        }
    }

    if (csum.param_flow_matrix != 0) {
        const lim = @min(@as(usize, call_site.args_len), 8);
        for (0..lim) |dst_i| {
            const dst_mode = body.call_arg_modes.items[call_site.modes_start + dst_i];
            const dst_word = body.extra_args.items[call_site.args_start + dst_i];
            const dst_info = getArgDepthAndOrigin(body, horizon, dst_mode, dst_word, true);
            for (0..lim) |src_i| {
                if (dst_i == src_i) continue;
                if (((csum.param_flow_matrix >> @intCast(src_i * 8 + dst_i)) & 1) == 0) continue;
                const src_mode = body.call_arg_modes.items[call_site.modes_start + src_i];
                const src_word = body.extra_args.items[call_site.args_start + src_i];
                const src_info = getArgDepthAndOrigin(body, horizon, src_mode, src_word, false);
                if (src_info.depth > dst_info.depth) {
                    outcome.emitted_error_count += 1;
                    try emitSastDiag(
                        config.diagnostic_sink,
                        .e0306_region_escape_violation,
                        .err,
                        call_span,
                        "inner-region borrow flows into longer-lived container argument via callee",
                        "callee stores shorter-lived argument into longer-lived destination argument here",
                        null,
                        null,
                        "ensure the source argument's region outlives the destination container's region",
                    );
                    return;
                }
            }
        }
    }
}

/// Extracts the `PlacePathLookup` freed or closed by `call_site` when it invokes `EXPLICIT_FREE_METHOD_MAP`.
fn extractExplicitFreeCallTarget(
    body: *const MirBody,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    call_site: mir.MirCallSite,
) ?PlacePathLookup {
    const is_free_call = !call_site.direct_symbol.isNone() and
        call_site.direct_symbol.asInt() < sym_table.symbols.items.len and
        EXPLICIT_FREE_METHOD_MAP.has(sym_table.getSymbol(call_site.direct_symbol).name_text);
    if (!is_free_call or call_site.args_len == 0) return null;

    const arg0_mode = body.call_arg_modes.items[call_site.modes_start];
    const arg0_word = body.extra_args.items[call_site.args_start];

    if (call_site.args_len >= 2 and isPoolArgPlaceOrVal(body, pool, sym_table, arg0_mode, arg0_word)) {
        const ptr_mode = body.call_arg_modes.items[call_site.modes_start + 1];
        const ptr_word = body.extra_args.items[call_site.args_start + 1];
        if ((ptr_mode == .let_mode or ptr_mode == .sink_mode) and ptr_word < body.insts.len) {
            const ptr_inst = body.getInst(MirValueId.fromInt(ptr_word));
            if (ptr_inst.op == .place_load and ptr_inst.operands.lhs < trie.place_map.len) {
                return trie.place_map[ptr_inst.operands.lhs];
            }
        } else if (ptr_word < trie.place_map.len) {
            return trie.place_map[ptr_word];
        }
    } else if (arg0_mode != .let_mode and arg0_mode != .sink_mode and arg0_word < trie.place_map.len) {
        return trie.place_map[arg0_word];
    } else if ((arg0_mode == .let_mode or arg0_mode == .sink_mode) and arg0_word < body.insts.len) {
        const recv_inst = body.getInst(MirValueId.fromInt(arg0_word));
        if ((recv_inst.op == .place_load or recv_inst.op == .place_addr) and
            recv_inst.operands.lhs < trie.place_map.len)
        {
            return trie.place_map[recv_inst.operands.lhs];
        }
    }
    return null;
}

/// Checks whether `bb_id` terminates in an explicit `.free()` / `.close()` call targeting `target_path`.
fn isBlockTerminatedByExplicitFreeOf(
    body: *const MirBody,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    bb_id: MirBlockId,
    target_path: MovePathId,
) bool {
    if (target_path.isNone() or bb_id.asInt() >= body.blocks.items.len) return false;
    const term = body.blocks.items[bb_id.asInt()].terminator;
    if (term.kind != .call or term.cond_or_val >= body.calls.items.len) return false;
    if (extractExplicitFreeCallTarget(body, trie, pool, sym_table, body.calls.items[term.cond_or_val])) |lookup| {
        return lookup.id == target_path;
    }
    return false;
}

/// Checks whether instructions from `start_pos` in `bb_id` feed `target_path` into an explicit free or `@linear` sink.
fn isBlockFeedingFreeOrLinearSink(
    body: *const MirBody,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    bb_id: MirBlockId,
    start_pos: usize,
    target_path: MovePathId,
) bool {
    if (target_path.isNone()) return false;
    if (isBlockTerminatedByExplicitFreeOf(body, trie, pool, sym_table, bb_id, target_path)) return true;
    if (!trie.nodes[target_path.asInt()].flags().is_linear) return false;

    const inst_slice = body.getBlockInsts(bb_id);
    if (start_pos >= inst_slice.len) return false;
    for (inst_slice[start_pos..]) |rem_vid| {
        const rem_inst = body.getInst(rem_vid);
        if (rem_inst.op == .ghost_storage_move and rem_inst.operands.lhs < trie.place_map.len) {
            if (trie.place_map[rem_inst.operands.lhs].id == target_path) return true;
        }
    }
    return false;
}

/// Checks for double free / duplicate `@linear` close at `call_site` (`E0313`) and updates `work_state`.
fn checkAndApplyCallFreeDiagnostics(
    body: *const MirBody,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    call_site: mir.MirCallSite,
    call_span: Span,
    config: SastConfig,
    has_reported_path_diag: []bool,
    work_state: *TypestateState,
    outcome: *Pass2BodyOutcome,
) !void {
    for (0..call_site.args_len) |arg_i| {
        const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
        const word = body.extra_args.items[call_site.args_start + arg_i];
        if (mode == .set_mode and word < trie.place_map.len) {
            applyPathWriteToState(trie, trie.place_map[word], work_state);
        }
    }

    if (extractExplicitFreeCallTarget(body, trie, pool, sym_table, call_site)) |lookup| {
        const m_idx = lookup.id.asInt();
        // Note: if `recv` was passed by consuming `sink self`, `ghost_storage_move` ran right before `.call`,
        // so only `ever_freed` (from an earlier free/close) indicates a duplicate close:
        if (work_state.ever_freed.isSet(m_idx)) {
            outcome.emitted_error_count += 1;
            has_reported_path_diag[m_idx] = true;
            try emitSastDiag(
                config.diagnostic_sink,
                .e0313_double_free_or_close,
                .err,
                call_span,
                "double free or duplicate `@linear` resource consumption",
                "resource closed or freed a second time here",
                null,
                null,
                "remove the duplicate `.close()` / `.free()` call (check active `defer` / `errdefer` cleanups)",
            );
        }
        applyPathMoveOrFreeToState(trie, lookup, true, work_state);
        const base = trie.nodes[m_idx].base_local;
        if (base < work_state.local_raw_ptr.len) {
            work_state.local_raw_ptr[base] = .freed_or_dangling;
        }
    }
}

/// Rewrites `body.block_insts` in-place to splice `drop_in_place`, `drop_if_live`, and `_drop_flag` updates.
fn materializePlannedDrops(
    arena_alloc: std.mem.Allocator,
    perm_alloc: std.mem.Allocator,
    body: *MirBody,
    trie: *const MovePathTrie,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    has_drop_flag_need: []const bool,
    planned_drops: []const PlannedDropInsertion,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    out_edges: *std.ArrayListUnmanaged(WitnessCallEdge),
    outcome: *Pass2BodyOutcome,
) !void {
    const path_count = trie.nodes.len;
    const flag_places = try arena_alloc.alloc(PlaceId, path_count);
    @memset(flag_places, PlaceId.fromInt(mir.NONE_U32));
    const flag_locals = try arena_alloc.alloc(LocalId, path_count);
    @memset(flag_locals, .none);

    var flagged_paths: std.ArrayListUnmanaged(usize) = .empty;
    for (has_drop_flag_need, 0..) |is_needed, m_idx| {
        if (!is_needed) continue;
        const flag_lid = LocalId.fromInt(@intCast(body.locals.items.len));
        try body.locals.append(
            body.allocator,
            mir.LocalDecl.init(
                .empty,
                .bool_ty,
                .none,
                0,
                .let_mode,
                .{ .is_mut = true, .is_synthetic_temp = true, .is_address_taken = true },
            ),
        );
        const flag_pl = try ensureRootPlaceForLocal(body, flag_lid);
        flag_locals[m_idx] = flag_lid;
        flag_places[m_idx] = flag_pl;
        try flagged_paths.append(arena_alloc, m_idx);
    }

    var false_const_opt: ?u32 = null;
    var true_const_opt: ?u32 = null;
    if (flagged_paths.items.len > 0) {
        false_const_opt = try body.appendConst(.{ .bool_val = false });
        true_const_opt = try body.appendConst(.{ .bool_val = true });
    }

    const emitFlagStore = struct {
        //! Local helper appending a synthetic boolean constant load and `_drop_flag` store into `dest_list`.

        /// Emits `const_scalar(c_idx)` followed by `place_store(f_pl, b_val)`.
        fn run(
            body_ref: *MirBody,
            dest_list: *std.ArrayListUnmanaged(MirValueId),
            alloc: std.mem.Allocator,
            f_pl: PlaceId,
            c_idx: u32,
            tok: TokenIndex,
        ) !void {
            const b_val = try body_ref.appendInst(.{
                .op = .const_scalar,
                .flags = .{ .is_synthetic = true },
                .type_id = .bool_ty,
                .operands = .{ .lhs = c_idx, .rhs = 0 },
            }, tok);
            try dest_list.append(alloc, b_val);
            const st_val = try body_ref.appendInst(.{
                .op = .place_store,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .type_id = .unit_ty,
                .operands = .{ .lhs = f_pl.asInt(), .rhs = b_val.asInt() },
            }, tok);
            try dest_list.append(alloc, st_val);
        }
    }.run;

    const emitDropItem = struct {
        //! Local helper materializing a single unconditional (`drop_in_place`) or conditional (`drop_if_live`) drop.

        /// Appends the synthesized drop instructions for `item` and records `auto_drop_glue` witness edges.
        fn run(
            body_ref: *MirBody,
            dest_list: *std.ArrayListUnmanaged(MirValueId),
            alloc: std.mem.Allocator,
            perm: std.mem.Allocator,
            item: PlannedDropInsertion,
            f_places: []const PlaceId,
            false_c: ?u32,
            pool_ref: *const InternPool,
            sym_tab: *const SymbolTable,
            k2s: *const std.AutoHashMapUnmanaged(u32, u32),
            s2s: *const std.AutoHashMapUnmanaged(u32, u32),
            edges_out: *std.ArrayListUnmanaged(WitnessCallEdge),
            out_res: *Pass2BodyOutcome,
        ) !void {
            if (item.is_conditional) {
                const f_pl = f_places[item.path_id.asInt()];
                const open_tok = try body_ref.appendInst(.{
                    .op = .ghost_access_let,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{
                        .lhs = f_pl.asInt(),
                        .rhs = @backingInt(mir.GhostBorrowKind.scoped_projection),
                    },
                }, item.token);
                try dest_list.append(alloc, open_tok);
                const loaded_flag = try body_ref.appendInst(.{
                    .op = .place_load,
                    .flags = .{ .is_synthetic = true },
                    .type_id = .bool_ty,
                    .operands = .{ .lhs = f_pl.asInt(), .rhs = 0 },
                }, item.token);
                try dest_list.append(alloc, loaded_flag);
                const end_tok = try body_ref.appendInst(.{
                    .op = .ghost_access_end,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = open_tok.asInt(), .rhs = 0 },
                }, item.token);
                try dest_list.append(alloc, end_tok);
                const drop_inst = try body_ref.appendInst(.{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.drop_if_live),
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = item.place_id.asInt(), .rhs = loaded_flag.asInt() },
                }, item.token);
                try dest_list.append(alloc, drop_inst);
                if (false_c) |fc| {
                    try emitFlagStore(body_ref, dest_list, alloc, f_pl, fc, item.token);
                }
            } else {
                const drop_inst = try body_ref.appendInst(.{
                    .op = .intrinsic_op,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .aux_u16 = @backingInt(MirIntrinsicKind.drop_in_place),
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = item.place_id.asInt(), .rhs = mir.NONE_U32 },
                }, item.token);
                try dest_list.append(alloc, drop_inst);
            }
            out_res.emitted_drops += 1;

            // Record `auto_drop_glue` witness edges (`DR-17` §2.4):
            var drop_syms: std.ArrayListUnmanaged(SymbolIndex) = .empty;
            defer drop_syms.deinit(perm);
            var has_heap = false;
            try collectDropGlueTargets(perm, pool_ref, sym_tab, item.place_ty, 0, &drop_syms, &has_heap);
            if (has_heap) {
                out_res.has_builtin_heap_drop_free = true;
                const heap_eff = EffectCapabilityMask{ .blocking_sync = true };
                try edges_out.append(perm, WitnessCallEdge.init(
                    mir.NONE_U32,
                    item.token,
                    .{ .edge_kind = .auto_drop_glue, .edge_effects_bits = heap_eff.asBits() },
                ));
            }
            for (drop_syms.items) |dsym| {
                var target_key: u32 = mir.NONE_U32;
                const sym_rec = sym_tab.getSymbol(dsym).*;
                if (!sym_rec.def_id.isNone() and k2s.contains(sym_rec.def_id.asInt())) {
                    target_key = sym_rec.def_id.asInt();
                } else if (s2s.get(dsym.asInt())) |d_slot| {
                    target_key = ANON_BODY_KEY_FLAG | d_slot;
                } else if (!sym_rec.def_id.isNone()) {
                    target_key = sym_rec.def_id.asInt();
                }
                try edges_out.append(perm, WitnessCallEdge.init(
                    target_key,
                    item.token,
                    .{ .edge_kind = .auto_drop_glue },
                ));
            }
        }
    }.run;

    const CallSetFlagEntry = struct {
        //! Deferred `_drop_flag` update injected on a normal-return block after a `set` or explicit-free call.

        /// Normal-return successor block index where `flag_path` changes state.
        target_bb: u32,
        /// `MovePathId` index of the `_drop_flag`-tracked path updated by the call.
        flag_path: usize,
        /// Call-site origin token attached to the synthesized flag store.
        token: TokenIndex,
        /// `true` for `set`-mode initialization; `false` for explicit `.free()` / `.close()` / `.deinit()`.
        is_value_true: bool,
    };
    var call_set_entries: std.ArrayListUnmanaged(CallSetFlagEntry) = .empty;
    if (flagged_paths.items.len > 0) {
        for (body.blocks.items, 0..) |blk_rec, src_bb_usize| {
            const term = blk_rec.terminator;
            if (term.kind != .call or term.cond_or_val >= body.calls.items.len) continue;
            const out_edges_slice = body.getOutgoingEdges(MirBlockId.fromInt(@intCast(src_bb_usize)));
            if (out_edges_slice.len == 0) continue;
            const normal_target_bb = out_edges_slice[0].target_bb.asInt();
            const call_site = body.calls.items[term.cond_or_val];
            for (0..call_site.args_len) |arg_i| {
                const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
                const word = body.extra_args.items[call_site.args_start + arg_i];
                if (mode == .set_mode and word < trie.place_map.len) {
                    const lk = trie.place_map[word];
                    for (flagged_paths.items) |fm| {
                        if (trie.subtree[lk.id.asInt()].isSet(fm)) {
                            try call_set_entries.append(arena_alloc, .{
                                .target_bb = normal_target_bb,
                                .flag_path = fm,
                                .token = call_site.origin_token,
                                .is_value_true = true,
                            });
                        }
                    }
                }
            }
            if (extractExplicitFreeCallTarget(body, trie, pool, sym_table, call_site)) |free_lk| {
                for (flagged_paths.items) |fm| {
                    if (trie.conflict[free_lk.id.asInt()].isSet(fm)) {
                        try call_set_entries.append(arena_alloc, .{
                            .target_bb = normal_target_bb,
                            .flag_path = fm,
                            .token = call_site.origin_token,
                            .is_value_true = false,
                        });
                    }
                }
            }
        }
    }

    var rebuilt_insts: std.ArrayListUnmanaged(MirValueId) = .empty;
    try rebuilt_insts.ensureTotalCapacity(
        arena_alloc,
        body.block_insts.items.len + planned_drops.len * 4 + call_set_entries.items.len * 2,
    );

    var drop_cursor: usize = 0;
    // Sort `planned_drops` by `(bb_idx ASC, before_pos ASC)` while preserving intra-site LIFO order:
    const sorted_drops = try arena_alloc.dupe(PlannedDropInsertion, planned_drops);
    std.mem.sort(PlannedDropInsertion, sorted_drops, {}, struct {
        /// Orders planned drops ascending by `(bb_idx, before_pos)`, preserving LIFO ties via stable sort.
        fn lessThan(_: void, lhs: PlannedDropInsertion, rhs: PlannedDropInsertion) bool {
            if (lhs.bb_idx != rhs.bb_idx) return lhs.bb_idx < rhs.bb_idx;
            return lhs.before_pos < rhs.before_pos;
        }
    }.lessThan);

    for (0..body.blocks.items.len) |bb_usize| {
        const bb_idx: u32 = @intCast(bb_usize);
        const old_slice = body.getBlockInsts(MirBlockId.fromInt(bb_idx));
        const new_start: u32 = @intCast(rebuilt_insts.items.len);

        // Advance `drop_cursor` to `bb_idx`:
        while (drop_cursor < sorted_drops.len and sorted_drops[drop_cursor].bb_idx < bb_idx) : (drop_cursor += 1) {}

        // Emit all leading `.block_param` instructions first (`MirVerifier` Invariant V2):
        var param_prefix_len: usize = 0;
        while (param_prefix_len < old_slice.len and
            body.getInst(old_slice[param_prefix_len]).op == .block_param) : (param_prefix_len += 1)
        {
            try rebuilt_insts.append(arena_alloc, old_slice[param_prefix_len]);
        }

        // Prepend `_drop_flag` initializers at top of `^bb0` and call-return flag writes:
        if (flagged_paths.items.len > 0) {
            if (bb_idx == 0) {
                for (flagged_paths.items) |m_idx| {
                    const f_lid = flag_locals[m_idx];
                    const f_pl = flag_places[m_idx];
                    const init_inst = try body.appendInst(.{
                        .op = .ghost_storage_init,
                        .flags = .{ .has_side_effects = true, .is_synthetic = true },
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = f_lid.asInt(), .rhs = 0 },
                    }, .none);
                    try rebuilt_insts.append(arena_alloc, init_inst);
                    const base_loc = trie.nodes[m_idx].base_local;
                    const is_init_param = base_loc >= 1 and base_loc <= body.param_count and
                        (body.locals.items[base_loc].mode() == .sink_mode or
                            body.locals.items[base_loc].mode() == .inout_mode);
                    const init_c = if (is_init_param) true_const_opt.? else false_const_opt.?;
                    try emitFlagStore(body, &rebuilt_insts, arena_alloc, f_pl, init_c, .none);
                }
            }
            for (call_set_entries.items) |set_entry| {
                if (set_entry.target_bb == bb_idx) {
                    const flag_c = if (set_entry.is_value_true) true_const_opt.? else false_const_opt.?;
                    try emitFlagStore(
                        body,
                        &rebuilt_insts,
                        arena_alloc,
                        flag_places[set_entry.flag_path],
                        flag_c,
                        set_entry.token,
                    );
                }
            }
        }

        for (old_slice[param_prefix_len..], param_prefix_len..) |orig_val, pos| {
            while (drop_cursor < sorted_drops.len and
                sorted_drops[drop_cursor].bb_idx == bb_idx and
                sorted_drops[drop_cursor].before_pos == @as(u32, @intCast(pos))) : (drop_cursor += 1)
            {
                try emitDropItem(
                    body,
                    &rebuilt_insts,
                    arena_alloc,
                    perm_alloc,
                    sorted_drops[drop_cursor],
                    flag_places,
                    false_const_opt,
                    pool,
                    sym_table,
                    key_to_slot,
                    sym_to_slot,
                    out_edges,
                    outcome,
                );
            }

            const orig_inst = body.getInst(orig_val);
            const orig_tok = body.origin_tokens.items[orig_val.asInt()];
            try rebuilt_insts.append(arena_alloc, orig_val);

            // Update `_drop_flag` after init/store/move/free touching `m_idx`:
            if (flagged_paths.items.len > 0) {
                if (orig_inst.op == .ghost_storage_init and orig_inst.operands.lhs < path_count and
                    !hasImmediatePairedStore(body, old_slice, pos, orig_inst.operands.lhs))
                {
                    for (flagged_paths.items) |fm| {
                        if (trie.subtree[orig_inst.operands.lhs].isSet(fm)) {
                            try emitFlagStore(
                                body,
                                &rebuilt_insts,
                                arena_alloc,
                                flag_places[fm],
                                true_const_opt.?,
                                orig_tok,
                            );
                        }
                    }
                } else if (orig_inst.op == .place_store and orig_inst.operands.lhs < trie.place_map.len) {
                    const lk = trie.place_map[orig_inst.operands.lhs];
                    for (flagged_paths.items) |fm| {
                        if (trie.subtree[lk.id.asInt()].isSet(fm)) {
                            try emitFlagStore(
                                body,
                                &rebuilt_insts,
                                arena_alloc,
                                flag_places[fm],
                                true_const_opt.?,
                                orig_tok,
                            );
                        }
                    }
                } else if (orig_inst.op == .ghost_storage_move and orig_inst.operands.lhs < trie.place_map.len) {
                    const lk = trie.place_map[orig_inst.operands.lhs];
                    if (!trie.nodes[lk.id.asInt()].flags().is_copy) {
                        for (flagged_paths.items) |fm| {
                            if (trie.conflict[lk.id.asInt()].isSet(fm)) {
                                try emitFlagStore(
                                    body,
                                    &rebuilt_insts,
                                    arena_alloc,
                                    flag_places[fm],
                                    false_const_opt.?,
                                    orig_tok,
                                );
                            }
                        }
                    }
                } else if (orig_inst.op == .intrinsic_op and
                    @as(MirIntrinsicKind, @fromBackingInt(orig_inst.aux_u16)) == .ghost_storage_free and
                    orig_inst.operands.lhs < trie.place_map.len)
                {
                    const lk = trie.place_map[orig_inst.operands.lhs];
                    for (flagged_paths.items) |fm| {
                        if (trie.conflict[lk.id.asInt()].isSet(fm)) {
                            try emitFlagStore(
                                body,
                                &rebuilt_insts,
                                arena_alloc,
                                flag_places[fm],
                                false_const_opt.?,
                                orig_tok,
                            );
                        }
                    }
                }
            }
        }

        // Emit pre-terminator (`before_pos == NONE_U32`) drops:
        while (drop_cursor < sorted_drops.len and
            sorted_drops[drop_cursor].bb_idx == bb_idx and
            sorted_drops[drop_cursor].before_pos == mir.NONE_U32) : (drop_cursor += 1)
        {
            try emitDropItem(
                body,
                &rebuilt_insts,
                arena_alloc,
                perm_alloc,
                sorted_drops[drop_cursor],
                flag_places,
                false_const_opt,
                pool,
                sym_table,
                key_to_slot,
                sym_to_slot,
                out_edges,
                outcome,
            );
        }

        const new_len: u32 = @intCast(rebuilt_insts.items.len - new_start);
        body.blocks.items[bb_usize].inst_start = new_start;
        body.blocks.items[bb_usize].inst_len = new_len;
    }

    body.block_insts.clearRetainingCapacity();
    try body.block_insts.appendSlice(body.allocator, rebuilt_insts.items);
}

// ---------- Pass 4: Sign-Biased Intv & Pentagon BCE -----------

/// Scalar integer/boolean/character domain descriptor for Pass 4 `Intv` abstract interpretation.
const ScalarIntDomain = struct {
    /// Scalar bit width (`1..64`).
    bits: u16,
    /// `true` if two's-complement signed (`i8`..`i64`, `isize`).
    is_signed: bool,
    /// Legal type-domain top interval (incorporating `wasm32` pointer width and `refined_ty` bounds).
    top_intv: Intv,
};

/// Result of Pass 4 (`Intv` + Demand-Sliced Pentagon BCE + `.narrow()` cast rewriting) on one `MirBody`.
const Pass4BodyOutcome = struct {
    /// Per-block post-BCE panic flag (`len == body.blocks.items.len`, allocated in `perm_alloc`).
    block_may_panic: []bool = &.{},
    /// `true` if any reachable block in `body` retains a residual trap or unproven check/arithmetic op.
    has_residual_may_panic: bool = false,
    /// Count of `bounds_check` and `slice_range_check` intrinsics eliminated in `body`.
    eliminated_bounds_checks: u32 = 0,
    /// Count of `narrow_check` intrinsics rewritten to casts in `body`.
    eliminated_narrow_checks: u32 = 0,
    /// Peak scratch bytes used by the Demand-Sliced Pentagon on `body` (`0` when Step 1 proves all).
    peak_pentagon_bytes: usize = 0,
    /// Count of `E0307` and `E0406` errors emitted on `body`.
    emitted_error_count: u32 = 0,
};

/// Classifies `raw_ty` into a `ScalarIntDomain` (`null` for non-scalars or 128-bit integers).
fn classifyScalarIntDomain(
    pool: *const InternPool,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) ?ScalarIntDomain {
    if (raw_ty.isError()) return null;

    var cur_ty = raw_ty;
    var refined_opt: ?type_system.RefinementBounds = null;
    var peel_depth: usize = 0;
    while (peel_depth < 16 and !cur_ty.isError()) : (peel_depth += 1) {
        const node = pool.getNode(cur_ty);
        if (node.tag == .refined_ty) {
            if (refined_opt == null) refined_opt = pool.getRefinementBounds(cur_ty);
            if (refined_opt) |rb| {
                cur_ty = rb.base_ty;
                continue;
            }
            break;
        }
        if (node.tag == .distinct_ty or node.tag == .bit_field_ty) {
            cur_ty = TypeId.fromInt(node.lhs);
            continue;
        }
        break;
    }

    const base_ty = pool.unwrapUnderlyingType(cur_ty);
    var domain: ScalarIntDomain = switch (base_ty) {
        .bool_ty => .{ .bits = 1, .is_signed = false, .top_intv = Intv.initUnsigned(0, 1) },
        .char_ty => .{ .bits = 32, .is_signed = false, .top_intv = Intv.initUnsigned(0, 0x10FFFF) },
        .i8_ty => .{
            .bits = 8,
            .is_signed = true,
            .top_intv = Intv.initSigned(std.math.minInt(i8), std.math.maxInt(i8)),
        },
        .i16_ty => .{
            .bits = 16,
            .is_signed = true,
            .top_intv = Intv.initSigned(std.math.minInt(i16), std.math.maxInt(i16)),
        },
        .i32_ty => .{
            .bits = 32,
            .is_signed = true,
            .top_intv = Intv.initSigned(std.math.minInt(i32), std.math.maxInt(i32)),
        },
        .i64_ty, .untyped_int_ty => .{
            .bits = 64,
            .is_signed = true,
            .top_intv = Intv.initSigned(std.math.minInt(i64), std.math.maxInt(i64)),
        },
        .isize_ty => if (target_layout.ptr_byte_size == 4) .{
            .bits = 32,
            .is_signed = true,
            .top_intv = Intv.initSigned(std.math.minInt(i32), std.math.maxInt(i32)),
        } else .{
            .bits = 64,
            .is_signed = true,
            .top_intv = Intv.initSigned(std.math.minInt(i64), std.math.maxInt(i64)),
        },
        .u8_ty => .{
            .bits = 8,
            .is_signed = false,
            .top_intv = Intv.initUnsigned(0, std.math.maxInt(u8)),
        },
        .u16_ty => .{
            .bits = 16,
            .is_signed = false,
            .top_intv = Intv.initUnsigned(0, std.math.maxInt(u16)),
        },
        .u32_ty => .{
            .bits = 32,
            .is_signed = false,
            .top_intv = Intv.initUnsigned(0, std.math.maxInt(u32)),
        },
        .u64_ty => .{
            .bits = 64,
            .is_signed = false,
            .top_intv = Intv.initUnsigned(0, std.math.maxInt(u64)),
        },
        .usize_ty => if (target_layout.ptr_byte_size == 4) .{
            .bits = 32,
            .is_signed = false,
            .top_intv = Intv.initUnsigned(0, std.math.maxInt(u32)),
        } else .{
            .bits = 64,
            .is_signed = false,
            .top_intv = Intv.initUnsigned(0, std.math.maxInt(u64)),
        },
        else => return null,
    };

    if (refined_opt) |rb| {
        if (domain.is_signed) {
            const clamped_lo: i64 = @intCast(std.math.clamp(rb.min_val, std.math.minInt(i64), std.math.maxInt(i64)));
            const clamped_hi: i64 = @intCast(std.math.clamp(rb.max_val, std.math.minInt(i64), std.math.maxInt(i64)));
            domain.top_intv = domain.top_intv.meet(Intv.initSigned(clamped_lo, clamped_hi));
        } else if (rb.max_val >= 0) {
            const clamped_lo: u64 = if (rb.min_val <= 0)
                0
            else
                @intCast(@min(@as(u128, @intCast(rb.min_val)), std.math.maxInt(u64)));
            const clamped_hi: u64 = @intCast(@min(@as(u128, @intCast(rb.max_val)), std.math.maxInt(u64)));
            domain.top_intv = domain.top_intv.meet(Intv.initUnsigned(clamped_lo, clamped_hi));
        }
    }
    return domain;
}

/// Decodes the inclusive `[lo_i128, hi_i128]` mathematical bounds of a non-bottom `Intv`.
fn decodeIntvToI128(intv: Intv, domain: ScalarIntDomain) struct { lo: i128, hi: i128 } {
    if (domain.is_signed) {
        return .{
            .lo = Intv.decodeSigned(intv.lo_ord),
            .hi = Intv.decodeSigned(intv.hi_ord),
        };
    }
    return .{
        .lo = intv.lo_ord,
        .hi = intv.hi_ord,
    };
}

/// Encodes an `[lo_i128, hi_i128]` range back into `domain`, clamping to `domain.top_intv`.
fn encodeClippedI128ToIntv(lo_val: i128, hi_val: i128, domain: ScalarIntDomain) Intv {
    if (lo_val > hi_val) return Intv.BOTTOM;
    const dom_bounds = decodeIntvToI128(domain.top_intv, domain);
    if (hi_val < dom_bounds.lo or lo_val > dom_bounds.hi) return Intv.BOTTOM;
    const clipped_lo = @max(lo_val, dom_bounds.lo);
    const clipped_hi = @min(hi_val, dom_bounds.hi);
    if (domain.is_signed) {
        return Intv.initSigned(@intCast(clipped_lo), @intCast(clipped_hi));
    }
    return Intv.initUnsigned(@intCast(clipped_lo), @intCast(clipped_hi));
}

/// Evaluates `const_scalar` into an exact singleton `Intv` (`top_intv` fallback for non-64-bit scalars).
fn evalConstScalarIntv(body: *const MirBody, inst: MirInst, dom_opt: ?ScalarIntDomain) Intv {
    const dom = dom_opt orelse return Intv.TOP_ORD;
    if (inst.operands.lhs >= body.consts.items.len) return dom.top_intv;
    const mc = body.consts.items[inst.operands.lhs];
    return switch (mc) {
        .bool_val => |flag| Intv.initUnsigned(@intFromBool(flag), @intFromBool(flag)),
        .char_val => |ch| Intv.initUnsigned(ch, ch),
        .int_val => |iv| blk: {
            if (dom.is_signed) {
                const mask_bits: u7 = @intCast(dom.bits);
                const truncated: i64 = if (dom.bits == 64)
                    @truncate(iv)
                else shift_blk: {
                    const raw_u64: u64 = @truncate(@as(u128, @bitCast(iv)));
                    const sh: u6 = @intCast(64 - mask_bits);
                    break :shift_blk @as(i64, @bitCast(raw_u64 << sh)) >> sh;
                };
                break :blk Intv.initSigned(truncated, truncated);
            }
            const raw_u64: u64 = @truncate(@as(u128, @bitCast(iv)));
            const masked: u64 = if (dom.bits == 64)
                raw_u64
            else
                raw_u64 & ((@as(u64, 1) << @intCast(dom.bits)) - 1);
            break :blk Intv.initUnsigned(masked, masked);
        },
        else => dom.top_intv,
    };
}

/// Extracts a static `[T; N]` / `#soa [T; N]` length when `place_id` ends in `.slice_len` over a fixed array.
fn extractStaticArrayLenPlace(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    place_id: PlaceId,
) ?u64 {
    if (place_id.asInt() >= body.places.items.len) return null;
    const pl_rec = body.places.items[place_id.asInt()];
    if (pl_rec.base >= body.locals.items.len or pl_rec.proj_len == 0) return null;
    const projs = body.getPlaceProjections(place_id);
    if (projs[projs.len - 1].kind != .slice_len) return null;

    var cur_ty = pool.unwrapUnderlyingType(body.locals.items[pl_rec.base].type_id);
    var active_subst: type_system.NominalTypeSubst = .{};
    var active_dc: ?u32 = null;
    var active_soa: ?TypeId = null;
    for (projs[0 .. projs.len - 1]) |proj| {
        cur_ty = stepProjectedType(pool, sym_table, cur_ty, proj, &active_subst, &active_dc, &active_soa);
    }
    cur_ty = pool.unwrapUnderlyingType(active_subst.resolve(cur_ty));
    if (cur_ty.isError()) return null;
    var node = pool.getNode(cur_ty);
    if (node.tag == .ref_ty or node.tag == .mut_ref_ty) {
        cur_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
        if (cur_ty.isError()) return null;
        node = pool.getNode(cur_ty);
    }
    if ((node.tag == .array_ty or node.tag == .soa_array_ty) and
        (node.rhs & type_system.SYMBOLIC_ARRAY_LEN_FLAG) == 0)
    {
        return node.rhs;
    }
    return null;
}

/// Evaluates a `UnaryOpKind` over an abstract `Intv`.
fn evalUnaryOpIntv(
    kind: UnaryOpKind,
    src_intv: Intv,
    src_dom_opt: ?ScalarIntDomain,
    dst_dom_opt: ?ScalarIntDomain,
) Intv {
    if (src_intv.isBottom()) return Intv.BOTTOM;
    const dst_dom = dst_dom_opt orelse return Intv.TOP_ORD;
    const src_dom = src_dom_opt orelse return dst_dom.top_intv;
    const sb = decodeIntvToI128(src_intv, src_dom);

    return switch (kind) {
        .bool_not => blk: {
            if (sb.lo == 0 and sb.hi == 0) break :blk Intv.initUnsigned(1, 1);
            if (sb.lo == 1 and sb.hi == 1) break :blk Intv.initUnsigned(0, 0);
            break :blk dst_dom.top_intv;
        },
        .int_zext, .int_sext => blk: {
            const db = decodeIntvToI128(dst_dom.top_intv, dst_dom);
            if (sb.lo >= db.lo and sb.hi <= db.hi) {
                break :blk encodeClippedI128ToIntv(sb.lo, sb.hi, dst_dom);
            }
            break :blk dst_dom.top_intv;
        },
        .int_trunc, .bitcast_op => blk: {
            const db = decodeIntvToI128(dst_dom.top_intv, dst_dom);
            if (sb.lo >= db.lo and sb.hi <= db.hi) {
                break :blk encodeClippedI128ToIntv(sb.lo, sb.hi, dst_dom);
            }
            break :blk dst_dom.top_intv;
        },
        .sneg_checked => blk: {
            const db = decodeIntvToI128(dst_dom.top_intv, dst_dom);
            const neg_lo = -sb.hi;
            const neg_hi = -sb.lo;
            break :blk encodeClippedI128ToIntv(@max(neg_lo, db.lo), @min(neg_hi, db.hi), dst_dom);
        },
        else => dst_dom.top_intv,
    };
}

/// Evaluates a `BinOpKind` over abstract `Intv` operands `(lhs_intv, rhs_intv)`.
fn evalBinOpIntv(
    kind: BinOpKind,
    lhs_intv: Intv,
    rhs_intv: Intv,
    lhs_dom_opt: ?ScalarIntDomain,
    rhs_dom_opt: ?ScalarIntDomain,
    dst_dom_opt: ?ScalarIntDomain,
) Intv {
    if (lhs_intv.isBottom() or rhs_intv.isBottom()) return Intv.BOTTOM;
    const dst_dom = dst_dom_opt orelse return Intv.TOP_ORD;
    const lhs_dom = lhs_dom_opt orelse return dst_dom.top_intv;
    const rhs_dom = rhs_dom_opt orelse lhs_dom;

    const lb = decodeIntvToI128(lhs_intv, lhs_dom);
    const rb = decodeIntvToI128(rhs_intv, rhs_dom);
    const db = decodeIntvToI128(dst_dom.top_intv, dst_dom);

    switch (kind) {
        .sadd_checked, .uadd_checked, .sadd_sat, .uadd_sat => {
            return encodeClippedI128ToIntv(@max(lb.lo + rb.lo, db.lo), @min(lb.hi + rb.hi, db.hi), dst_dom);
        },
        .add_wrap => {
            const sum_lo = lb.lo + rb.lo;
            const sum_hi = lb.hi + rb.hi;
            if (sum_lo >= db.lo and sum_hi <= db.hi) {
                return encodeClippedI128ToIntv(sum_lo, sum_hi, dst_dom);
            }
            return dst_dom.top_intv;
        },
        .ssub_checked, .usub_checked, .ssub_sat, .usub_sat => {
            return encodeClippedI128ToIntv(@max(lb.lo - rb.hi, db.lo), @min(lb.hi - rb.lo, db.hi), dst_dom);
        },
        .sub_wrap => {
            const diff_lo = lb.lo - rb.hi;
            const diff_hi = lb.hi - rb.lo;
            if (diff_lo >= db.lo and diff_hi <= db.hi) {
                return encodeClippedI128ToIntv(diff_lo, diff_hi, dst_dom);
            }
            return dst_dom.top_intv;
        },
        .umul_checked, .umul_sat => {
            const lo_mul = @mulWithOverflow(lb.lo, rb.lo);
            const hi_mul = @mulWithOverflow(lb.hi, rb.hi);
            const prod_lo: i128 = if (lo_mul[1] != 0) db.hi + 1 else lo_mul[0];
            const prod_hi: i128 = if (hi_mul[1] != 0) db.hi else hi_mul[0];
            if (kind == .umul_checked and prod_lo > db.hi) return Intv.BOTTOM;
            return encodeClippedI128ToIntv(@max(@min(prod_lo, db.hi), db.lo), @min(prod_hi, db.hi), dst_dom);
        },
        .smul_checked, .smul_sat, .mul_wrap => {
            const clampedMul = struct {
                //! Overflow-safe `i128` multiplication clamping extreme `u64`/`i64` products just outside `[lo_lim, hi_lim]`.

                /// Multiplies `lhs_v * rhs_v`, mapping `i128` overflow to `lo_lim - 1` (negative) or `hi_lim + 1` (positive).
                fn eval(lhs_v: i128, rhs_v: i128, lo_lim: i128, hi_lim: i128) i128 {
                    const mul_res = @mulWithOverflow(lhs_v, rhs_v);
                    if (mul_res[1] != 0) {
                        return if ((lhs_v < 0) != (rhs_v < 0)) lo_lim - 1 else hi_lim + 1;
                    }
                    return mul_res[0];
                }
            }.eval;
            const p1 = clampedMul(lb.lo, rb.lo, db.lo, db.hi);
            const p2 = clampedMul(lb.lo, rb.hi, db.lo, db.hi);
            const p3 = clampedMul(lb.hi, rb.lo, db.lo, db.hi);
            const p4 = clampedMul(lb.hi, rb.hi, db.lo, db.hi);
            const min_p = @min(@min(p1, p2), @min(p3, p4));
            const max_p = @max(@max(p1, p2), @max(p3, p4));
            if (kind == .mul_wrap and (min_p < db.lo or max_p > db.hi)) return dst_dom.top_intv;
            if (kind == .smul_checked and (min_p > db.hi or max_p < db.lo)) return Intv.BOTTOM;
            return encodeClippedI128ToIntv(@max(min_p, db.lo), @min(max_p, db.hi), dst_dom);
        },
        .udiv_checked => {
            if (rb.hi <= 0) return Intv.BOTTOM;
            const denom_lo = @max(rb.lo, 1);
            return encodeClippedI128ToIntv(@divTrunc(lb.lo, rb.hi), @divTrunc(lb.hi, denom_lo), dst_dom);
        },
        .sdiv_checked => {
            if (rb.lo == 0 and rb.hi == 0) return Intv.BOTTOM;
            if (rb.lo > 0 and lb.lo >= 0) {
                return encodeClippedI128ToIntv(@divTrunc(lb.lo, rb.hi), @divTrunc(lb.hi, rb.lo), dst_dom);
            }
            return dst_dom.top_intv;
        },
        .urem_checked => {
            if (rb.hi <= 0) return Intv.BOTTOM;
            return encodeClippedI128ToIntv(0, @min(lb.hi, rb.hi - 1), dst_dom);
        },
        .srem_checked => {
            if (rb.lo == 0 and rb.hi == 0) return Intv.BOTTOM;
            const max_div_mag = @max(@abs(rb.lo), @abs(rb.hi));
            if (max_div_mag == 0) return Intv.BOTTOM;
            const bound: i128 = @intCast(max_div_mag - 1);
            if (lb.lo >= 0) return encodeClippedI128ToIntv(0, @min(lb.hi, bound), dst_dom);
            return encodeClippedI128ToIntv(@max(-bound, db.lo), @min(bound, db.hi), dst_dom);
        },
        .bit_and => {
            if (!dst_dom.is_signed or (lb.lo >= 0 and rb.lo >= 0)) {
                return encodeClippedI128ToIntv(0, @min(lb.hi, rb.hi), dst_dom);
            }
            return dst_dom.top_intv;
        },
        .lshr_checked => {
            if (rb.hi < 0 or rb.lo >= dst_dom.bits) return Intv.BOTTOM;
            const sh_lo: u7 = @intCast(@max(rb.lo, 0));
            const sh_hi: u7 = @intCast(@min(rb.hi, dst_dom.bits - 1));
            const lo_u: u128 = @intCast(@max(lb.lo, 0));
            const hi_u: u128 = @intCast(@max(lb.hi, 0));
            return encodeClippedI128ToIntv(@intCast(lo_u >> sh_hi), @intCast(hi_u >> sh_lo), dst_dom);
        },
        .shl_checked => {
            if (rb.hi < 0 or rb.lo >= dst_dom.bits) return Intv.BOTTOM;
            if (lb.lo >= 0 and rb.hi < 63) {
                const sh_lo: u7 = @intCast(@max(rb.lo, 0));
                const sh_hi: u7 = @intCast(rb.hi);
                const prod_lo = lb.lo << sh_lo;
                const prod_hi = lb.hi << sh_hi;
                if (prod_hi <= db.hi) return encodeClippedI128ToIntv(prod_lo, prod_hi, dst_dom);
            }
            return dst_dom.top_intv;
        },
        .slt, .ult => {
            if (lb.hi < rb.lo) return Intv.initUnsigned(1, 1);
            if (lb.lo >= rb.hi) return Intv.initUnsigned(0, 0);
            return Intv.initUnsigned(0, 1);
        },
        .sle, .ule => {
            if (lb.hi <= rb.lo) return Intv.initUnsigned(1, 1);
            if (lb.lo > rb.hi) return Intv.initUnsigned(0, 0);
            return Intv.initUnsigned(0, 1);
        },
        .sgt, .ugt => {
            if (lb.lo > rb.hi) return Intv.initUnsigned(1, 1);
            if (lb.hi <= rb.lo) return Intv.initUnsigned(0, 0);
            return Intv.initUnsigned(0, 1);
        },
        .sge, .uge => {
            if (lb.lo >= rb.hi) return Intv.initUnsigned(1, 1);
            if (lb.hi < rb.lo) return Intv.initUnsigned(0, 0);
            return Intv.initUnsigned(0, 1);
        },
        .eq => {
            if (lb.lo == lb.hi and rb.lo == rb.hi and lb.lo == rb.lo) return Intv.initUnsigned(1, 1);
            if (lb.hi < rb.lo or rb.hi < lb.lo) return Intv.initUnsigned(0, 0);
            return Intv.initUnsigned(0, 1);
        },
        .ne => {
            if (lb.hi < rb.lo or rb.hi < lb.lo) return Intv.initUnsigned(1, 1);
            if (lb.lo == lb.hi and rb.lo == rb.hi and lb.lo == rb.lo) return Intv.initUnsigned(0, 0);
            return Intv.initUnsigned(0, 1);
        },
        else => return dst_dom.top_intv,
    }
}

/// Peels `copy_val` chains to find the underlying defining `MirValueId`.
fn peelCopyValId(body: *const MirBody, raw_val: u32) u32 {
    var cur = raw_val;
    var guard: usize = 0;
    while (cur < body.insts.len and guard < 16) : (guard += 1) {
        const inst = body.getInst(MirValueId.fromInt(cur));
        if (inst.op == .copy_val and inst.operands.lhs < body.insts.len) {
            cur = inst.operands.lhs;
        } else {
            break;
        }
    }
    return cur;
}

/// Decoded relational comparison from a dominating `cond_br` terminator.
const DecodedBranchCmp = struct {
    /// Comparison operator (`slt`, `ult`, `sle`, `ule`, `sgt`, `ugt`, `sge`, `uge`, `eq`, `ne`).
    op: BinOpKind,
    /// Peeled LHS `MirValueId`.
    lhs_val: u32,
    /// Peeled RHS `MirValueId`.
    rhs_val: u32,
    /// `true` when the active branch asserts `op` holds; `false` when it asserts `!op`.
    is_positive: bool,
};

/// Refines `(lhs_intv, rhs_intv)` under `cmp` (`is_positive` flips `<` <-> `>=`, `<=` <-> `>`, `==` <-> `!=`).
fn refineIntvPairFromCmp(
    cmp: DecodedBranchCmp,
    lhs_in: Intv,
    rhs_in: Intv,
    dom: ScalarIntDomain,
) struct { lhs_out: Intv, rhs_out: Intv } {
    if (lhs_in.isBottom() or rhs_in.isBottom()) {
        return .{ .lhs_out = Intv.BOTTOM, .rhs_out = Intv.BOTTOM };
    }
    const eff_op: BinOpKind = if (cmp.is_positive) cmp.op else switch (cmp.op) {
        .slt => .sge,
        .ult => .uge,
        .sle => .sgt,
        .ule => .ugt,
        .sgt => .sle,
        .ugt => .ule,
        .sge => .slt,
        .uge => .ult,
        .eq => .ne,
        .ne => .eq,
        else => cmp.op,
    };

    var lhs_out = lhs_in;
    var rhs_out = rhs_in;
    switch (eff_op) {
        .slt, .ult => {
            if (rhs_in.hi_ord == 0) {
                return .{ .lhs_out = Intv.BOTTOM, .rhs_out = Intv.BOTTOM };
            }
            lhs_out = lhs_out.meet(.{ .lo_ord = dom.top_intv.lo_ord, .hi_ord = rhs_in.hi_ord - 1 });
            if (lhs_in.lo_ord == std.math.maxInt(u64)) {
                return .{ .lhs_out = Intv.BOTTOM, .rhs_out = Intv.BOTTOM };
            }
            rhs_out = rhs_out.meet(.{ .lo_ord = lhs_in.lo_ord + 1, .hi_ord = dom.top_intv.hi_ord });
        },
        .sle, .ule => {
            lhs_out = lhs_out.meet(.{ .lo_ord = dom.top_intv.lo_ord, .hi_ord = rhs_in.hi_ord });
            rhs_out = rhs_out.meet(.{ .lo_ord = lhs_in.lo_ord, .hi_ord = dom.top_intv.hi_ord });
        },
        .sgt, .ugt => {
            if (rhs_in.lo_ord == std.math.maxInt(u64)) {
                return .{ .lhs_out = Intv.BOTTOM, .rhs_out = Intv.BOTTOM };
            }
            lhs_out = lhs_out.meet(.{ .lo_ord = rhs_in.lo_ord + 1, .hi_ord = dom.top_intv.hi_ord });
            if (lhs_in.hi_ord == 0) {
                return .{ .lhs_out = Intv.BOTTOM, .rhs_out = Intv.BOTTOM };
            }
            rhs_out = rhs_out.meet(.{ .lo_ord = dom.top_intv.lo_ord, .hi_ord = lhs_in.hi_ord - 1 });
        },
        .sge, .uge => {
            lhs_out = lhs_out.meet(.{ .lo_ord = rhs_in.lo_ord, .hi_ord = dom.top_intv.hi_ord });
            rhs_out = rhs_out.meet(.{ .lo_ord = dom.top_intv.lo_ord, .hi_ord = lhs_in.hi_ord });
        },
        .eq => {
            const met = lhs_out.meet(rhs_out);
            lhs_out = met;
            rhs_out = met;
        },
        .ne => {
            if (rhs_in.lo_ord == rhs_in.hi_ord) {
                const k_ord = rhs_in.lo_ord;
                if (lhs_out.lo_ord == k_ord and lhs_out.hi_ord == k_ord) {
                    return .{ .lhs_out = Intv.BOTTOM, .rhs_out = Intv.BOTTOM };
                }
                if (lhs_out.lo_ord == k_ord) lhs_out.lo_ord += 1;
                if (lhs_out.hi_ord == k_ord) lhs_out.hi_ord -= 1;
            }
            if (lhs_in.lo_ord == lhs_in.hi_ord) {
                const k_ord = lhs_in.lo_ord;
                if (rhs_out.lo_ord == k_ord) rhs_out.lo_ord += 1;
                if (rhs_out.hi_ord == k_ord) rhs_out.hi_ord -= 1;
            }
        },
        else => {},
    }
    return .{ .lhs_out = lhs_out, .rhs_out = rhs_out };
}

/// Discriminates direct root-local loads from direct vs. dereferenced `.slice_len` loads.
const LoadedPlaceKind = enum(u8) {
    /// Unprojected `place_load` of `base_local`.
    root_local,
    /// `base_local.len` (`proj_len == 1 and kind == .slice_len`).
    direct_slice_len,
    /// `(*base_local).len` (`proj_len == 2 and projs[0] == .deref and projs[1] == .slice_len`).
    deref_slice_len,
};

/// Identifies an unprojected local or `.slice_len` projection loaded by `val_raw` (`null` otherwise).
const LoadedPlaceKey = struct {
    /// Root `LocalId.asInt()`.
    base_local: u32,
    /// Classification of the loaded place projection.
    kind: LoadedPlaceKind,

    /// Returns `true` if `self` represents either a direct or dereferenced `.slice_len` load.
    inline fn isSliceLen(self: LoadedPlaceKey) bool {
        return self.kind != .root_local;
    }
};

/// Returns `true` if `base_local` in `body` is a shared immutable reference (`&T` / `.ref_ty`).
inline fn isSharedRefLocal(body: *const MirBody, pool: *const InternPool, base_local: u32) bool {
    if (base_local >= body.locals.items.len) return false;
    const unwrapped = pool.unwrapUnderlyingType(body.locals.items[base_local].type_id);
    return !unwrapped.isError() and pool.getNode(unwrapped).tag == .ref_ty;
}

/// Extracts a `LoadedPlaceKey` when `val_raw` is a `place_load` of a root local or `.slice_len`.
fn extractLoadedPlaceKey(body: *const MirBody, val_raw: u32) ?LoadedPlaceKey {
    const peeled = peelCopyValId(body, val_raw);
    if (peeled >= body.insts.len) return null;
    const inst = body.getInst(MirValueId.fromInt(peeled));
    if (inst.op != .place_load or inst.operands.lhs >= body.places.items.len) return null;
    const pl_rec = body.places.items[inst.operands.lhs];
    if (pl_rec.proj_len == 0) {
        return .{ .base_local = pl_rec.base, .kind = .root_local };
    }
    const projs = body.getPlaceProjections(PlaceId.fromInt(inst.operands.lhs));
    if (projs.len == 1 and projs[0].kind == .slice_len) {
        return .{ .base_local = pl_rec.base, .kind = .direct_slice_len };
    }
    if (projs.len == 2 and projs[0].kind == .deref and projs[1].kind == .slice_len) {
        return .{ .base_local = pl_rec.base, .kind = .deref_slice_len };
    }
    return null;
}

/// Evaluates `val_raw` as a compile-time `bool` constant when statically known (`null` otherwise).
fn evalConstBoolVal(body: *const MirBody, val_raw: u32) ?bool {
    const peeled = peelCopyValId(body, val_raw);
    if (peeled >= body.insts.len) return null;
    const inst = body.getInst(MirValueId.fromInt(peeled));
    if (inst.op != .const_scalar or inst.operands.lhs >= body.consts.items.len) return null;
    return switch (body.consts.items[inst.operands.lhs]) {
        .bool_val => |flag| flag,
        .int_val => |num| if (num == 0) false else if (num == 1) true else null,
        else => null,
    };
}

/// Locates the owning `(MirBlockId, param_ordinal)` of `block_param` instruction `bp_raw`.
fn findBlockParamOwner(
    body: *const MirBody,
    bp_raw: u32,
) ?struct { bb_id: MirBlockId, param_ord: usize } {
    for (0..body.blocks.items.len) |bb_i| {
        const bb_id = MirBlockId.fromInt(@intCast(bb_i));
        for (body.getBlockParams(bb_id), 0..) |param_vid, param_ord| {
            if (param_vid.asInt() == bp_raw) {
                return .{ .bb_id = bb_id, .param_ord = param_ord };
            }
        }
    }
    return null;
}

/// Returns `true` if `p_term`'s `then` edge strictly dominates `target_bb`, `false` if its `else`
/// edge strictly dominates `target_bb`, or `null` when neither branch edge dominates `target_bb`.
fn resolveDominatingCondBranchPolarity(
    body: *const MirBody,
    dom: *const DominatorTree,
    p_term: mir.MirTerminator,
    target_bb: MirBlockId,
) ?bool {
    if (p_term.kind != .cond_br or p_term.edge_len < 2 or
        p_term.edge_start + 1 >= body.extra_edges.items.len)
    {
        return null;
    }
    const then_bb = body.extra_edges.items[p_term.edge_start].target_bb;
    const else_bb = body.extra_edges.items[p_term.edge_start + 1].target_bb;
    if (then_bb == else_bb) return null;

    const is_dom_then = then_bb.asInt() < body.blocks.items.len and
        body.getPredEdges(then_bb).len == 1 and
        dom.isDominatorOf(then_bb, target_bb);
    const is_dom_else = else_bb.asInt() < body.blocks.items.len and
        body.getPredEdges(else_bb).len == 1 and
        dom.isDominatorOf(else_bb, target_bb);
    if (is_dom_then == is_dom_else) return null;
    return is_dom_then;
}

/// Extracts all relational `DecodedBranchCmp` guards implied by `cond_raw == is_holding_true`
/// (including `bool_not`, `bit_and` / `bit_or` on `bool`, and short-circuit `and` / `or` join diamonds).
fn collectDerivedCmpGuards(
    body: *const MirBody,
    dom: *const DominatorTree,
    cond_raw: u32,
    is_holding_true: bool,
    depth: u8,
    out_buf: *[32]DecodedBranchCmp,
    out_len: *usize,
) void {
    if (depth > 8 or out_len.* >= out_buf.len) return;
    var cur = peelCopyValId(body, cond_raw);
    var is_positive_polarity = is_holding_true;
    var step_guard: u32 = 0;

    while (cur < body.insts.len and step_guard < 16) : (step_guard += 1) {
        const inst = body.getInst(MirValueId.fromInt(cur));
        if (inst.op == .copy_val) {
            cur = inst.operands.lhs;
            continue;
        }
        if (inst.op == .unary_op) {
            const uk: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (uk == .bool_not and inst.operands.lhs < body.insts.len) {
                is_positive_polarity = !is_positive_polarity;
                cur = inst.operands.lhs;
                continue;
            }
            return;
        }
        if (inst.op == .bin_op) {
            const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            switch (bk) {
                .slt, .ult, .sle, .ule, .sgt, .ugt, .sge, .uge, .eq, .ne => {
                    if (out_len.* < out_buf.len) {
                        out_buf[out_len.*] = .{
                            .op = bk,
                            .lhs_val = peelCopyValId(body, inst.operands.lhs),
                            .rhs_val = peelCopyValId(body, inst.operands.rhs),
                            .is_positive = is_positive_polarity,
                        };
                        out_len.* += 1;
                    }
                    return;
                },
                .bit_and => {
                    if (inst.type_id == .bool_ty and is_positive_polarity) {
                        collectDerivedCmpGuards(body, dom, inst.operands.lhs, true, depth + 1, out_buf, out_len);
                        collectDerivedCmpGuards(body, dom, inst.operands.rhs, true, depth + 1, out_buf, out_len);
                    }
                    return;
                },
                .bit_or => {
                    if (inst.type_id == .bool_ty and !is_positive_polarity) {
                        collectDerivedCmpGuards(body, dom, inst.operands.lhs, false, depth + 1, out_buf, out_len);
                        collectDerivedCmpGuards(body, dom, inst.operands.rhs, false, depth + 1, out_buf, out_len);
                    }
                    return;
                },
                else => return,
            }
        }
        if (inst.op == .block_param) {
            const owner = findBlockParamOwner(body, cur) orelse return;
            const preds = body.getPredEdges(owner.bb_id);
            if (preds.len != 2) return;
            if (preds[0].asInt() >= body.extra_edges.items.len or
                preds[1].asInt() >= body.extra_edges.items.len) return;

            const edge0 = body.extra_edges.items[preds[0].asInt()];
            const edge1 = body.extra_edges.items[preds[1].asInt()];
            if (owner.param_ord >= edge0.args_len or owner.param_ord >= edge1.args_len) return;
            if (edge0.args_start + owner.param_ord >= body.extra_args.items.len or
                edge1.args_start + owner.param_ord >= body.extra_args.items.len) return;

            const arg0 = body.extra_args.items[edge0.args_start + owner.param_ord];
            const arg1 = body.extra_args.items[edge1.args_start + owner.param_ord];
            const edge_pair = [2]struct { src_bb: MirBlockId, arg_val: u32 }{
                .{ .src_bb = edge0.src_bb, .arg_val = arg0 },
                .{ .src_bb = edge1.src_bb, .arg_val = arg1 },
            };

            for (0..2) |dead_side| {
                const dead_entry = edge_pair[dead_side];
                const live_entry = edge_pair[1 - dead_side];
                if (evalConstBoolVal(body, dead_entry.arg_val)) |const_flag| {
                    if (const_flag == !is_positive_polarity) {
                        if (dead_entry.src_bb.asInt() < body.blocks.items.len and
                            live_entry.src_bb.asInt() < body.blocks.items.len)
                        {
                            const dead_term = body.blocks.items[dead_entry.src_bb.asInt()].terminator;
                            if (resolveDominatingCondBranchPolarity(body, dom, dead_term, live_entry.src_bb)) |is_dom_pol| {
                                collectDerivedCmpGuards(
                                    body,
                                    dom,
                                    dead_term.cond_or_val,
                                    is_dom_pol,
                                    depth + 1,
                                    out_buf,
                                    out_len,
                                );
                            }
                        }
                        collectDerivedCmpGuards(
                            body,
                            dom,
                            live_entry.arg_val,
                            is_positive_polarity,
                            depth + 1,
                            out_buf,
                            out_len,
                        );
                        return;
                    }
                }
            }
            return;
        }
        return;
    }
}

/// Reads the interval of `val_raw` refined by active dominating `cond_br` overrides in the current block.
fn readDomRefinedIntv(
    body: *const MirBody,
    val_raw: u32,
    val_intv: []const Intv,
    val_overrides: []const ?Intv,
    local_overrides: []const ?Intv,
    slice_len_overrides: []const ?Intv,
    local_store_counts: []const u32,
) Intv {
    if (val_raw >= val_intv.len) return Intv.TOP_ORD;
    const peeled = peelCopyValId(body, val_raw);
    var cur_iv = val_intv[val_raw];
    if (peeled < val_intv.len and peeled != val_raw) {
        cur_iv = cur_iv.meet(val_intv[peeled]);
    }
    if (val_overrides[val_raw]) |ov| {
        cur_iv = cur_iv.meet(ov);
    }
    if (peeled < val_overrides.len) {
        if (val_overrides[peeled]) |ov_peeled| {
            cur_iv = cur_iv.meet(ov_peeled);
        }
    }
    if (extractLoadedPlaceKey(body, peeled)) |pkey| {
        if (pkey.isSliceLen() and pkey.base_local < slice_len_overrides.len and
            local_store_counts[pkey.base_local] <= 1)
        {
            if (slice_len_overrides[pkey.base_local]) |sl_ov| {
                cur_iv = cur_iv.meet(sl_ov);
            }
        } else if (!pkey.isSliceLen() and pkey.base_local < local_overrides.len and
            local_store_counts[pkey.base_local] <= 1)
        {
            if (local_overrides[pkey.base_local]) |loc_ov| {
                cur_iv = cur_iv.meet(loc_ov);
            }
        }
    }
    return cur_iv;
}

/// Populates dominating `cond_br` refinements for `bb_idx` into `val_overrides`, `local_overrides`, and `slice_len_overrides`.
fn populateBlockDomOverrides(
    body: *const MirBody,
    pool: *const InternPool,
    dom: *const DominatorTree,
    bb_idx: u32,
    val_domains: []const ?ScalarIntDomain,
    val_intv: []const Intv,
    local_store_counts: []const u32,
    val_overrides: []?Intv,
    local_overrides: []?Intv,
    slice_len_overrides: []?Intv,
) void {
    const block_count = body.blocks.items.len;
    const inst_count = body.insts.len;
    const local_count = body.locals.items.len;

    @memset(val_overrides, null);
    @memset(local_overrides, null);
    @memset(slice_len_overrides, null);

    var all_cmps: [32]DecodedBranchCmp = undefined;
    var cmp_len: usize = 0;

    var walk_bb = bb_idx;
    var dom_guard: usize = 0;
    while (walk_bb != 0 and dom_guard < block_count) : (dom_guard += 1) {
        const parent_dom = dom.idom[walk_bb];
        if (parent_dom == mir.NONE_U32 or parent_dom == walk_bb) break;
        const p_term = body.blocks.items[parent_dom].terminator;
        if (resolveDominatingCondBranchPolarity(body, dom, p_term, MirBlockId.fromInt(walk_bb))) |is_dom_pol| {
            collectDerivedCmpGuards(body, dom, p_term.cond_or_val, is_dom_pol, 0, &all_cmps, &cmp_len);
        }
        walk_bb = parent_dom;
    }

    if (cmp_len == 0) return;

    for (0..2) |_| {
        var rev_i = cmp_len;
        while (rev_i > 0) {
            rev_i -= 1;
            const cmp = all_cmps[rev_i];
            if (cmp.lhs_val < inst_count and cmp.rhs_val < inst_count) {
                if (val_domains[cmp.lhs_val]) |cdom| {
                    const base_l = readDomRefinedIntv(
                        body,
                        cmp.lhs_val,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    const base_r = readDomRefinedIntv(
                        body,
                        cmp.rhs_val,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    const refined = refineIntvPairFromCmp(cmp, base_l, base_r, cdom);
                    val_overrides[cmp.lhs_val] = if (val_overrides[cmp.lhs_val]) |prev|
                        prev.meet(refined.lhs_out)
                    else
                        refined.lhs_out;
                    val_overrides[cmp.rhs_val] = if (val_overrides[cmp.rhs_val]) |prev|
                        prev.meet(refined.rhs_out)
                    else
                        refined.rhs_out;

                    if (extractLoadedPlaceKey(body, cmp.lhs_val)) |lkey| {
                        const is_immut_len = (lkey.kind == .direct_slice_len) or
                            (lkey.kind == .deref_slice_len and isSharedRefLocal(body, pool, lkey.base_local));
                        if (is_immut_len and lkey.base_local < local_count and
                            local_store_counts[lkey.base_local] <= 1)
                        {
                            slice_len_overrides[lkey.base_local] = if (slice_len_overrides[lkey.base_local]) |prev|
                                prev.meet(refined.lhs_out)
                            else
                                refined.lhs_out;
                        } else if (!lkey.isSliceLen() and lkey.base_local < local_count and
                            local_store_counts[lkey.base_local] <= 1)
                        {
                            local_overrides[lkey.base_local] = if (local_overrides[lkey.base_local]) |prev|
                                prev.meet(refined.lhs_out)
                            else
                                refined.lhs_out;
                        }
                    }
                    if (extractLoadedPlaceKey(body, cmp.rhs_val)) |rkey| {
                        const is_immut_len = (rkey.kind == .direct_slice_len) or
                            (rkey.kind == .deref_slice_len and isSharedRefLocal(body, pool, rkey.base_local));
                        if (is_immut_len and rkey.base_local < local_count and
                            local_store_counts[rkey.base_local] <= 1)
                        {
                            slice_len_overrides[rkey.base_local] = if (slice_len_overrides[rkey.base_local]) |prev|
                                prev.meet(refined.rhs_out)
                            else
                                refined.rhs_out;
                        } else if (!rkey.isSliceLen() and rkey.base_local < local_count and
                            local_store_counts[rkey.base_local] <= 1)
                        {
                            local_overrides[rkey.base_local] = if (local_overrides[rkey.base_local]) |prev|
                                prev.meet(refined.rhs_out)
                            else
                                refined.rhs_out;
                        }
                    }
                }
            }
        }
    }
}

/// Checks whether `CheckedArith` / division / shift `inst` is statically proven non-trapping by `lhs_iv` and `rhs_iv`.
fn isCheckedInstProvenSafeByIntv(
    inst: MirInst,
    lhs_iv: Intv,
    rhs_iv: Intv,
    val_domains: []const ?ScalarIntDomain,
) bool {
    switch (inst.op) {
        .unary_op => {
            const uk: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (uk != .sneg_checked) return true;
            if (inst.operands.lhs >= val_domains.len) return false;
            const dom = val_domains[inst.operands.lhs] orelse return false;
            if (lhs_iv.isBottom()) return true;
            const sb = decodeIntvToI128(lhs_iv, dom);
            const db = decodeIntvToI128(dom.top_intv, dom);
            return sb.lo > db.lo;
        },
        .bin_op => {
            const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
            if (inst.operands.lhs >= val_domains.len or inst.operands.rhs >= val_domains.len) return false;
            if (lhs_iv.isBottom() or rhs_iv.isBottom()) return true;
            const lhs_dom = val_domains[inst.operands.lhs] orelse return false;
            const rhs_dom = val_domains[inst.operands.rhs] orelse lhs_dom;
            const lb = decodeIntvToI128(lhs_iv, lhs_dom);
            const rb = decodeIntvToI128(rhs_iv, rhs_dom);
            const db = decodeIntvToI128(lhs_dom.top_intv, lhs_dom);

            return switch (bk) {
                .sadd_checked, .uadd_checked => (lb.lo + rb.lo >= db.lo) and (lb.hi + rb.hi <= db.hi),
                .ssub_checked, .usub_checked => (lb.lo - rb.hi >= db.lo) and (lb.hi - rb.lo <= db.hi),
                .umul_checked => blk: {
                    const hi_mul = @mulWithOverflow(lb.hi, rb.hi);
                    break :blk hi_mul[1] == 0 and hi_mul[0] <= db.hi;
                },
                .smul_checked => blk: {
                    const m1 = @mulWithOverflow(lb.lo, rb.lo);
                    const m2 = @mulWithOverflow(lb.lo, rb.hi);
                    const m3 = @mulWithOverflow(lb.hi, rb.lo);
                    const m4 = @mulWithOverflow(lb.hi, rb.hi);
                    if ((m1[1] | m2[1] | m3[1] | m4[1]) != 0) break :blk false;
                    const min_p = @min(@min(m1[0], m2[0]), @min(m3[0], m4[0]));
                    const max_p = @max(@max(m1[0], m2[0]), @max(m3[0], m4[0]));
                    break :blk min_p >= db.lo and max_p <= db.hi;
                },
                .udiv_checked, .urem_checked => rb.lo >= 1,
                .sdiv_checked, .srem_checked => blk: {
                    const is_zero_free = rb.lo > 0 or rb.hi < 0;
                    if (!is_zero_free) break :blk false;
                    const has_possible_min_neg1 = (lb.lo <= db.lo) and (rb.lo <= -1 and rb.hi >= -1);
                    break :blk !has_possible_min_neg1;
                },
                .shl_checked, .ashr_checked, .lshr_checked => rb.lo >= 0 and rb.hi < lhs_dom.bits,
                else => true,
            };
        },
        else => return true,
    }
}

/// Unproven bounds or slice-range check queued from Step 1 `Intv` into Step 2 Pentagon.
const PendingBceCheck = struct {
    /// Owning basic block index.
    bb_idx: u32,
    /// `MirValueId` of the `.intrinsic_op` instruction.
    inst_val: MirValueId,
    /// `.bounds_check` or `.slice_range_check`.
    kind: MirIntrinsicKind,
};

/// Rewrites a proven `bounds_check` or `slice_range_check` in-place into `const_scalar(.unit_val)`.
fn rewriteProvenBoundsCheckInPlace(body: *MirBody, inst_val: MirValueId, unit_const_idx: u32) void {
    body.insts.set(inst_val.asInt(), .{
        .op = .const_scalar,
        .flags = .{ .is_synthetic = true },
        .aux_u16 = 0,
        .type_id = .unit_ty,
        .operands = .{ .lhs = unit_const_idx, .rhs = 0 },
    });
}

/// Rewrites a proven `narrow_check` intrinsic in-place into a pure `int_trunc` / `int_sext` / `int_zext` / `copy_val`.
fn rewriteProvenNarrowCheckInPlace(
    body: *MirBody,
    pool: *const InternPool,
    inst_val: MirValueId,
    src_val: u32,
    dst_ty: TypeId,
) void {
    const src_ty = body.getInst(MirValueId.fromInt(src_val)).type_id;
    const src_dom_opt = classifyScalarIntDomain(pool, src_ty, body.target_layout);
    const dst_dom_opt = classifyScalarIntDomain(pool, dst_ty, body.target_layout);
    const src_bits: u16 = if (src_dom_opt) |sd| sd.bits else 64;
    const dst_bits: u16 = if (dst_dom_opt) |dd| dd.bits else 64;
    const is_src_signed = if (src_dom_opt) |sd| sd.is_signed else true;

    if (dst_bits < src_bits) {
        body.insts.set(inst_val.asInt(), .{
            .op = .unary_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(UnaryOpKind.int_trunc),
            .type_id = dst_ty,
            .operands = .{ .lhs = src_val, .rhs = 0 },
        });
    } else if (dst_bits > src_bits) {
        const ext_op: UnaryOpKind = if (is_src_signed) .int_sext else .int_zext;
        body.insts.set(inst_val.asInt(), .{
            .op = .unary_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(ext_op),
            .type_id = dst_ty,
            .operands = .{ .lhs = src_val, .rhs = 0 },
        });
    } else if (src_ty == dst_ty) {
        body.insts.set(inst_val.asInt(), .{
            .op = .copy_val,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = 0,
            .type_id = dst_ty,
            .operands = .{ .lhs = src_val, .rhs = 0 },
        });
    } else {
        body.insts.set(inst_val.asInt(), .{
            .op = .unary_op,
            .flags = .{ .is_synthetic = true },
            .aux_u16 = @backingInt(UnaryOpKind.bitcast_op),
            .type_id = dst_ty,
            .operands = .{ .lhs = src_val, .rhs = 0 },
        });
    }
}

/// Applies `Fix-06A` lazy 1-hop closure (`row[x] ∪ ⋃_{z ∈ row[x]} row[z]`) into `out_rows`.
fn closePentagonRowsOneHop(in_rows: []const PentagonSubRow, out_rows: []PentagonSubRow) void {
    const var_count = in_rows.len;
    for (0..var_count) |x_idx| {
        var closed = in_rows[x_idx];
        for (0..4) |word_i| {
            var rem = in_rows[x_idx].words[word_i];
            while (rem != 0) {
                const bit_i: usize = @ctz(rem);
                rem &= rem - 1;
                const z_idx = word_i * 64 + bit_i;
                if (z_idx < var_count) {
                    closed = closed.unionWith(in_rows[z_idx]);
                }
            }
        }
        out_rows[x_idx] = closed;
    }
}

/// Runs Pass 4 (`Intv` + Demand-Sliced Sparse ABCD Pentagon + `.narrow()` & BCE rewriting) on `body`.
fn runPass4IntervalsAndPentagonBce(
    arena_alloc: std.mem.Allocator,
    perm_alloc: std.mem.Allocator,
    body: *MirBody,
    dom: *const DominatorTree,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    has_body_no_panic: bool,
    config: SastConfig,
) !Pass4BodyOutcome {
    const block_count = body.blocks.items.len;
    const inst_count = body.insts.len;
    const local_count = body.locals.items.len;

    var outcome = Pass4BodyOutcome{
        .block_may_panic = try perm_alloc.alloc(bool, block_count),
    };
    @memset(outcome.block_may_panic, false);
    errdefer if (outcome.block_may_panic.len > 0) perm_alloc.free(outcome.block_may_panic);
    if (block_count == 0) return outcome;

    const decl_fallback_span = resolveBodyDeclSpan(body, sym_table);

    // [1] Pre-classify `ScalarIntDomain` per SSA instruction & track unmutated locals:
    const val_domains = try arena_alloc.alloc(?ScalarIntDomain, inst_count);
    for (0..inst_count) |v_idx| {
        val_domains[v_idx] = classifyScalarIntDomain(
            pool,
            body.insts.items(.type_id)[v_idx],
            body.target_layout,
        );
    }

    const local_store_counts = try arena_alloc.alloc(u32, local_count);
    @memset(local_store_counts, 0);
    const local_unique_val = try arena_alloc.alloc(u32, local_count);
    @memset(local_unique_val, mir.NONE_U32);
    const local_unique_bb = try arena_alloc.alloc(u32, local_count);
    @memset(local_unique_bb, mir.NONE_U32);

    // Count caller-initialized formal parameters (`mode != .set_mode`) as 1 entry store:
    for (1..local_count) |loc_i| {
        const loc = body.locals.items[loc_i];
        if (loc.flags().is_arg and loc.mode() != .set_mode) {
            local_store_counts[loc_i] = 1;
        }
    }

    for (0..block_count) |b_usize| {
        const b_u32: u32 = @intCast(b_usize);
        for (body.getBlockInsts(MirBlockId.fromInt(b_u32))) |inst_vid| {
            const inst = body.getInst(inst_vid);
            if (inst.op == .place_store and inst.operands.lhs < body.places.items.len) {
                const pl_rec = body.places.items[inst.operands.lhs];
                if (pl_rec.base < local_count) {
                    local_store_counts[pl_rec.base] +|= 1;
                    if (pl_rec.proj_len == 0 and local_store_counts[pl_rec.base] == 1) {
                        local_unique_val[pl_rec.base] = inst.operands.rhs;
                        local_unique_bb[pl_rec.base] = b_u32;
                    } else {
                        local_unique_val[pl_rec.base] = mir.NONE_U32;
                        local_unique_bb[pl_rec.base] = mir.NONE_U32;
                    }
                }
            } else if (inst.op == .place_addr and inst.operands.lhs < body.places.items.len) {
                const unwrapped = pool.unwrapUnderlyingType(inst.type_id);
                if (!unwrapped.isError() and pool.getNode(unwrapped).tag != .ref_ty) {
                    const base = body.places.items[inst.operands.lhs].base;
                    if (base < local_count) {
                        local_store_counts[base] = 2;
                        local_unique_val[base] = mir.NONE_U32;
                        local_unique_bb[base] = mir.NONE_U32;
                    }
                }
            }
        }
    }
    for (body.calls.items) |call_site| {
        for (0..call_site.args_len) |arg_i| {
            const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
            const word = body.extra_args.items[call_site.args_start + arg_i];
            if ((mode == .inout_mode or mode == .set_mode) and word < body.places.items.len) {
                const base = body.places.items[word].base;
                if (base < local_count) {
                    local_store_counts[base] = 2;
                    local_unique_val[base] = mir.NONE_U32;
                    local_unique_bb[base] = mir.NONE_U32;
                }
            }
        }
    }

    // [2] Step 1: $O(V)$ 16-byte Sign-Biased `Intv` RPO Dataflow with Widening:
    const val_intv = try arena_alloc.alloc(Intv, inst_count);
    @memset(val_intv, Intv.BOTTOM);
    const is_intv_reachable = try arena_alloc.alloc(bool, block_count);
    @memset(is_intv_reachable, false);
    is_intv_reachable[0] = true;

    const is_loop_header = try arena_alloc.alloc(bool, block_count);
    @memset(is_loop_header, false);
    for (dom.rpo_blocks) |bb_idx| {
        const cur_rpo = dom.rpo_index[bb_idx];
        for (body.getPredEdges(MirBlockId.fromInt(bb_idx))) |pred_eid| {
            if (pred_eid.asInt() >= body.extra_edges.items.len) continue;
            const src_bb = body.extra_edges.items[pred_eid.asInt()].src_bb.asInt();
            if (src_bb < block_count and dom.rpo_index[src_bb] != mir.NONE_U32 and
                dom.rpo_index[src_bb] >= cur_rpo)
            {
                is_loop_header[bb_idx] = true;
            }
        }
    }

    const val_overrides = try arena_alloc.alloc(?Intv, inst_count);
    const local_overrides = try arena_alloc.alloc(?Intv, local_count);
    const slice_len_overrides = try arena_alloc.alloc(?Intv, local_count);

    var has_intv_changed = true;
    var intv_iters: usize = 0;
    while (has_intv_changed and intv_iters < 24) : (intv_iters += 1) {
        has_intv_changed = false;
        for (dom.rpo_blocks) |bb_idx| {
            if (!is_intv_reachable[bb_idx]) continue;
            const bb_id = MirBlockId.fromInt(bb_idx);

            // Join block-parameter intervals across `is_intv_reachable` incoming edges:
            const params = body.getBlockParams(bb_id);
            if (params.len > 0) {
                const preds = body.getPredEdges(bb_id);
                for (params, 0..) |param_vid, p_ord| {
                    const p_idx = param_vid.asInt();
                    const p_dom_opt = val_domains[p_idx];
                    var joined = Intv.BOTTOM;
                    for (preds) |pred_eid| {
                        if (pred_eid.asInt() >= body.extra_edges.items.len) continue;
                        const edge = body.extra_edges.items[pred_eid.asInt()];
                        const src_bb = edge.src_bb.asInt();
                        if (src_bb >= block_count or !is_intv_reachable[src_bb]) continue;

                        // Check if `src_bb` `cond_br` statically pruned this specific edge:
                        const src_term = body.blocks.items[src_bb].terminator;
                        if (src_term.kind == .cond_br and src_term.cond_or_val < inst_count) {
                            const c_iv = val_intv[src_term.cond_or_val];
                            const is_then_edge = (pred_eid.asInt() == src_term.edge_start);
                            if (!c_iv.isBottom()) {
                                if (is_then_edge and c_iv.lo_ord == 0 and c_iv.hi_ord == 0) continue;
                                if (!is_then_edge and c_iv.lo_ord == 1 and c_iv.hi_ord == 1) continue;
                            }
                        }

                        if (p_ord < edge.args_len and edge.args_start + p_ord < body.extra_args.items.len) {
                            const arg_v = body.extra_args.items[edge.args_start + p_ord];
                            if (arg_v < inst_count) {
                                var edge_iv = val_intv[arg_v];
                                if (src_term.kind == .cond_br and src_term.cond_or_val < inst_count) {
                                    const is_then = (pred_eid.asInt() == src_term.edge_start);
                                    var edge_cmps: [32]DecodedBranchCmp = undefined;
                                    var edge_cmp_len: usize = 0;
                                    collectDerivedCmpGuards(
                                        body,
                                        dom,
                                        src_term.cond_or_val,
                                        is_then,
                                        0,
                                        &edge_cmps,
                                        &edge_cmp_len,
                                    );
                                    const peeled_arg = peelCopyValId(body, arg_v);
                                    for (edge_cmps[0..edge_cmp_len]) |cmp| {
                                        if (cmp.lhs_val == peeled_arg and cmp.rhs_val < inst_count) {
                                            if (val_domains[cmp.lhs_val]) |cdom| {
                                                edge_iv = refineIntvPairFromCmp(
                                                    cmp,
                                                    edge_iv,
                                                    val_intv[cmp.rhs_val],
                                                    cdom,
                                                ).lhs_out;
                                            }
                                        } else if (cmp.rhs_val == peeled_arg and cmp.lhs_val < inst_count) {
                                            if (val_domains[cmp.rhs_val]) |cdom| {
                                                edge_iv = refineIntvPairFromCmp(
                                                    cmp,
                                                    val_intv[cmp.lhs_val],
                                                    edge_iv,
                                                    cdom,
                                                ).rhs_out;
                                            }
                                        }
                                    }
                                }
                                joined = joined.join(edge_iv);
                            }
                        } else if (src_term.kind == .call and p_ord == 0) {
                            joined = if (p_dom_opt) |pd| pd.top_intv else Intv.TOP_ORD;
                        }
                    }

                    // Apply loop-header widening $\nabla$ after 3 iterations to guarantee quick convergence:
                    const old_iv = val_intv[p_idx];
                    if (is_loop_header[bb_idx] and intv_iters >= 3 and !old_iv.isBottom() and !joined.isBottom()) {
                        const top_iv = if (p_dom_opt) |pd| pd.top_intv else Intv.TOP_ORD;
                        if (joined.lo_ord < old_iv.lo_ord) joined.lo_ord = top_iv.lo_ord;
                        if (joined.hi_ord > old_iv.hi_ord) joined.hi_ord = top_iv.hi_ord;
                    }
                    if (!joined.eql(old_iv)) {
                        val_intv[p_idx] = joined;
                        has_intv_changed = true;
                    }
                }
            }

            // Collect dominating `cond_br` interval refinements active on entry to `bb_idx`:
            populateBlockDomOverrides(
                body,
                pool,
                dom,
                bb_idx,
                val_domains,
                val_intv,
                local_store_counts,
                val_overrides,
                local_overrides,
                slice_len_overrides,
            );

            // Evaluate block instructions sequentially:
            for (body.getBlockInsts(bb_id)) |inst_vid| {
                const v_idx = inst_vid.asInt();
                const inst = body.getInst(inst_vid);
                const dst_dom_opt = val_domains[v_idx];

                var new_iv: Intv = if (dst_dom_opt) |dd| dd.top_intv else Intv.TOP_ORD;
                switch (inst.op) {
                    .block_param => continue,
                    .const_scalar => {
                        new_iv = evalConstScalarIntv(body, inst, dst_dom_opt);
                    },
                    .copy_val => {
                        new_iv = readDomRefinedIntv(
                            body,
                            inst.operands.lhs,
                            val_intv,
                            val_overrides,
                            local_overrides,
                            slice_len_overrides,
                            local_store_counts,
                        );
                    },
                    .place_load => {
                        const pl_id = PlaceId.fromInt(inst.operands.lhs);
                        if (extractStaticArrayLenPlace(body, pool, sym_table, pl_id)) |arr_len| {
                            new_iv = Intv.initUnsigned(arr_len, arr_len);
                        } else if (extractLoadedPlaceKey(body, v_idx)) |pkey| {
                            if (pkey.isSliceLen() and pkey.base_local < local_count and
                                local_store_counts[pkey.base_local] <= 1)
                            {
                                if (slice_len_overrides[pkey.base_local]) |sl_ov| {
                                    new_iv = new_iv.meet(sl_ov);
                                }
                            } else if (!pkey.isSliceLen() and pkey.base_local < local_count) {
                                const uniq_v = local_unique_val[pkey.base_local];
                                const uniq_bb = local_unique_bb[pkey.base_local];
                                if (uniq_v < inst_count and uniq_bb < block_count and
                                    dom.isDominatorOf(MirBlockId.fromInt(uniq_bb), bb_id) and
                                    !val_intv[uniq_v].isBottom())
                                {
                                    new_iv = readDomRefinedIntv(
                                        body,
                                        uniq_v,
                                        val_intv,
                                        val_overrides,
                                        local_overrides,
                                        slice_len_overrides,
                                        local_store_counts,
                                    );
                                }
                                if (local_overrides[pkey.base_local]) |loc_ov| {
                                    new_iv = new_iv.meet(loc_ov);
                                }
                            }
                        }
                    },
                    .place_store => {
                        if (inst.operands.lhs < body.places.items.len) {
                            const pl_rec = body.places.items[inst.operands.lhs];
                            if (pl_rec.base < local_count) {
                                local_overrides[pl_rec.base] = null;
                                slice_len_overrides[pl_rec.base] = null;
                                if (pl_rec.proj_len == 0 and inst.operands.rhs < inst_count) {
                                    local_overrides[pl_rec.base] = readDomRefinedIntv(
                                        body,
                                        inst.operands.rhs,
                                        val_intv,
                                        val_overrides,
                                        local_overrides,
                                        slice_len_overrides,
                                        local_store_counts,
                                    );
                                }
                            }
                        }
                    },
                    .unary_op => {
                        const uk: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        const src_iv = readDomRefinedIntv(
                            body,
                            inst.operands.lhs,
                            val_intv,
                            val_overrides,
                            local_overrides,
                            slice_len_overrides,
                            local_store_counts,
                        );
                        const src_dom = if (inst.operands.lhs < inst_count) val_domains[inst.operands.lhs] else null;
                        new_iv = evalUnaryOpIntv(uk, src_iv, src_dom, dst_dom_opt);
                    },
                    .bin_op => {
                        const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                        const lhs_iv = readDomRefinedIntv(
                            body,
                            inst.operands.lhs,
                            val_intv,
                            val_overrides,
                            local_overrides,
                            slice_len_overrides,
                            local_store_counts,
                        );
                        const rhs_iv = readDomRefinedIntv(
                            body,
                            inst.operands.rhs,
                            val_intv,
                            val_overrides,
                            local_overrides,
                            slice_len_overrides,
                            local_store_counts,
                        );
                        const l_dom = if (inst.operands.lhs < inst_count) val_domains[inst.operands.lhs] else null;
                        const r_dom = if (inst.operands.rhs < inst_count) val_domains[inst.operands.rhs] else null;
                        new_iv = evalBinOpIntv(bk, lhs_iv, rhs_iv, l_dom, r_dom, dst_dom_opt);
                    },
                    .intrinsic_op => {
                        const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                        if (ikind == .narrow_check and inst.operands.rhs >= 3 and
                            inst.operands.lhs + 3 <= body.extra_args.items.len)
                        {
                            const src_v = body.extra_args.items[inst.operands.lhs];
                            const min_v = body.extra_args.items[inst.operands.lhs + 1];
                            const max_v = body.extra_args.items[inst.operands.lhs + 2];
                            if (dst_dom_opt) |dd| {
                                var narrowed = dd.top_intv;
                                if (min_v < inst_count and max_v < inst_count) {
                                    const min_inst = body.getInst(MirValueId.fromInt(min_v));
                                    const max_inst = body.getInst(MirValueId.fromInt(max_v));
                                    if (min_inst.op == .const_scalar and max_inst.op == .const_scalar and
                                        min_inst.operands.lhs < body.consts.items.len and
                                        max_inst.operands.lhs < body.consts.items.len)
                                    {
                                        const min_mc = body.consts.items[min_inst.operands.lhs];
                                        const max_mc = body.consts.items[max_inst.operands.lhs];
                                        if (min_mc == .int_val and max_mc == .int_val) {
                                            narrowed = narrowed.meet(
                                                encodeClippedI128ToIntv(min_mc.int_val, max_mc.int_val, dd),
                                            );
                                        }
                                    }
                                }
                                if (src_v < inst_count) {
                                    if (val_domains[src_v]) |sd| {
                                        const src_iv = readDomRefinedIntv(
                                            body,
                                            src_v,
                                            val_intv,
                                            val_overrides,
                                            local_overrides,
                                            slice_len_overrides,
                                            local_store_counts,
                                        );
                                        if (!src_iv.isBottom()) {
                                            const sb = decodeIntvToI128(src_iv, sd);
                                            narrowed = narrowed.meet(encodeClippedI128ToIntv(sb.lo, sb.hi, dd));
                                        }
                                    }
                                }
                                new_iv = narrowed;
                            }
                        }
                    },
                    else => {},
                }

                if (val_overrides[v_idx]) |ov| {
                    new_iv = new_iv.meet(ov);
                }
                if (!new_iv.eql(val_intv[v_idx])) {
                    val_intv[v_idx] = new_iv;
                    has_intv_changed = true;
                }
            }

            // Propagate block reachability across outgoing terminator edges:
            const term = body.blocks.items[bb_idx].terminator;
            if (term.kind == .cond_br and term.edge_len >= 2 and
                term.cond_or_val < inst_count and
                term.edge_start + 1 < body.extra_edges.items.len)
            {
                const cond_iv = readDomRefinedIntv(
                    body,
                    term.cond_or_val,
                    val_intv,
                    val_overrides,
                    local_overrides,
                    slice_len_overrides,
                    local_store_counts,
                );
                const then_dst = body.extra_edges.items[term.edge_start].target_bb.asInt();
                const else_dst = body.extra_edges.items[term.edge_start + 1].target_bb.asInt();
                if (!cond_iv.isBottom()) {
                    if (!(cond_iv.lo_ord == 0 and cond_iv.hi_ord == 0) and then_dst < block_count and !is_intv_reachable[then_dst]) {
                        is_intv_reachable[then_dst] = true;
                        has_intv_changed = true;
                    }
                    if (!(cond_iv.lo_ord == 1 and cond_iv.hi_ord == 1) and else_dst < block_count and !is_intv_reachable[else_dst]) {
                        is_intv_reachable[else_dst] = true;
                        has_intv_changed = true;
                    }
                }
            } else {
                for (body.getOutgoingEdges(bb_id)) |edge| {
                    const dst = edge.target_bb.asInt();
                    if (dst < block_count and !is_intv_reachable[dst]) {
                        is_intv_reachable[dst] = true;
                        has_intv_changed = true;
                    }
                }
            }
        }
    }

    // Fail-closed soundness guard if the 24-iteration `Intv` RPO loop did not converge:
    if (has_intv_changed) {
        for (0..block_count) |b_i| {
            is_intv_reachable[b_i] = dom.isReachable(MirBlockId.fromInt(@intCast(b_i)));
        }
        for (0..inst_count) |v_i| {
            val_intv[v_i] = if (val_domains[v_i]) |vd| vd.top_intv else Intv.TOP_ORD;
        }
    }

    // [3] Step 1 Discharge: rewrite proven `.narrow_check`, `.bounds_check`, `.slice_range_check` & emit `E0406`/`E0307`:
    var unit_const_opt: ?u32 = null;
    var unproven_checks: std.ArrayListUnmanaged(PendingBceCheck) = .empty;

    for (dom.rpo_blocks) |bb_idx| {
        if (!is_intv_reachable[bb_idx]) continue;
        populateBlockDomOverrides(
            body,
            pool,
            dom,
            bb_idx,
            val_domains,
            val_intv,
            local_store_counts,
            val_overrides,
            local_overrides,
            slice_len_overrides,
        );
        for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_vid| {
            const v_idx = inst_vid.asInt();
            const inst = body.getInst(inst_vid);
            if (inst.op != .intrinsic_op) continue;
            const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
            const tok = body.origin_tokens.items[v_idx];

            if (ikind == .narrow_check and inst.operands.rhs >= 3 and
                inst.operands.lhs + 3 <= body.extra_args.items.len)
            {
                const src_v = body.extra_args.items[inst.operands.lhs];
                const min_v = body.extra_args.items[inst.operands.lhs + 1];
                const max_v = body.extra_args.items[inst.operands.lhs + 2];
                if (src_v < inst_count and min_v < inst_count and max_v < inst_count) {
                    const min_inst = body.getInst(MirValueId.fromInt(min_v));
                    const max_inst = body.getInst(MirValueId.fromInt(max_v));
                    if (min_inst.op == .const_scalar and max_inst.op == .const_scalar and
                        min_inst.operands.lhs < body.consts.items.len and
                        max_inst.operands.lhs < body.consts.items.len)
                    {
                        const min_mc = body.consts.items[min_inst.operands.lhs];
                        const max_mc = body.consts.items[max_inst.operands.lhs];
                        if (min_mc == .int_val and max_mc == .int_val) {
                            if (val_domains[src_v]) |src_dom| {
                                const src_iv = readDomRefinedIntv(
                                    body,
                                    src_v,
                                    val_intv,
                                    val_overrides,
                                    local_overrides,
                                    slice_len_overrides,
                                    local_store_counts,
                                );
                                if (!src_iv.isBottom()) {
                                    const sb = decodeIntvToI128(src_iv, src_dom);
                                    if (sb.hi < min_mc.int_val or sb.lo > max_mc.int_val) {
                                        try emitSastDiag(
                                            config.diagnostic_sink,
                                            .e0406_range_refinement_violation,
                                            .err,
                                            resolveTokenSpan(body.file_id, tok, config, decl_fallback_span),
                                            "value interval cannot satisfy target `.narrow()` refinement bounds",
                                            "statically unsatisfiable `.narrow()` conversion",
                                            null,
                                            null,
                                            "use `.try_narrow()` or clamp the value into the target range first",
                                        );
                                        outcome.emitted_error_count += 1;
                                    } else if (sb.lo >= min_mc.int_val and sb.hi <= max_mc.int_val) {
                                        rewriteProvenNarrowCheckInPlace(body, pool, inst_vid, src_v, inst.type_id);
                                        outcome.eliminated_narrow_checks += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            } else if (ikind == .bounds_check and inst.operands.rhs >= 3 and
                inst.operands.lhs + 3 <= body.extra_args.items.len)
            {
                const idx_v = body.extra_args.items[inst.operands.lhs];
                const len_v = body.extra_args.items[inst.operands.lhs + 1];
                if (idx_v < inst_count and len_v < inst_count) {
                    const idx_dom = val_domains[idx_v];
                    const len_dom = val_domains[len_v];
                    const idx_iv = readDomRefinedIntv(
                        body,
                        idx_v,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    const len_iv = readDomRefinedIntv(
                        body,
                        len_v,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    if (idx_dom != null and len_dom != null and !idx_iv.isBottom() and !len_iv.isBottom()) {
                        const ib = decodeIntvToI128(idx_iv, idx_dom.?);
                        const lb = decodeIntvToI128(len_iv, len_dom.?);
                        if (ib.hi < 0 or ib.lo >= lb.hi) {
                            try emitSastDiag(
                                config.diagnostic_sink,
                                .e0307_static_buffer_overflow,
                                .err,
                                resolveTokenSpan(body.file_id, tok, config, decl_fallback_span),
                                "index access is statically proven out of bounds",
                                "index exceeds proven container length here",
                                null,
                                null,
                                "ensure `0 <= index < container.len` before indexing",
                            );
                            outcome.emitted_error_count += 1;
                            continue;
                        }
                        if (ib.lo >= 0 and ib.hi < lb.lo) {
                            if (unit_const_opt == null) {
                                unit_const_opt = try body.appendConst(.{ .unit_val = {} });
                            }
                            rewriteProvenBoundsCheckInPlace(body, inst_vid, unit_const_opt.?);
                            outcome.eliminated_bounds_checks += 1;
                            continue;
                        }
                    }
                }
                try unproven_checks.append(arena_alloc, .{
                    .bb_idx = bb_idx,
                    .inst_val = inst_vid,
                    .kind = .bounds_check,
                });
            } else if (ikind == .slice_range_check and inst.operands.rhs >= 3 and
                inst.operands.lhs + 3 <= body.extra_args.items.len)
            {
                const lo_v = body.extra_args.items[inst.operands.lhs];
                const hi_v = body.extra_args.items[inst.operands.lhs + 1];
                const len_v = body.extra_args.items[inst.operands.lhs + 2];
                if (lo_v < inst_count and hi_v < inst_count and len_v < inst_count) {
                    const lo_dom = val_domains[lo_v];
                    const hi_dom = val_domains[hi_v];
                    const len_dom = val_domains[len_v];
                    const lo_iv = readDomRefinedIntv(
                        body,
                        lo_v,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    const hi_iv = readDomRefinedIntv(
                        body,
                        hi_v,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    const len_iv = readDomRefinedIntv(
                        body,
                        len_v,
                        val_intv,
                        val_overrides,
                        local_overrides,
                        slice_len_overrides,
                        local_store_counts,
                    );
                    if (lo_dom != null and hi_dom != null and len_dom != null and
                        !lo_iv.isBottom() and !hi_iv.isBottom() and !len_iv.isBottom())
                    {
                        const lob = decodeIntvToI128(lo_iv, lo_dom.?);
                        const hib = decodeIntvToI128(hi_iv, hi_dom.?);
                        const lenb = decodeIntvToI128(len_iv, len_dom.?);
                        if (lob.hi < 0 or lob.lo > hib.hi or hib.lo > lenb.hi) {
                            try emitSastDiag(
                                config.diagnostic_sink,
                                .e0307_static_buffer_overflow,
                                .err,
                                resolveTokenSpan(body.file_id, tok, config, decl_fallback_span),
                                "slice sub-range is statically proven out of bounds (`lo <= hi <= len` violated)",
                                "out-of-bounds slice range here",
                                null,
                                null,
                                "ensure `0 <= start <= end <= slice.len` before slicing",
                            );
                            outcome.emitted_error_count += 1;
                            continue;
                        }
                        if (lob.lo >= 0 and lob.hi <= hib.lo and hib.hi <= lenb.lo) {
                            if (unit_const_opt == null) {
                                unit_const_opt = try body.appendConst(.{ .unit_val = {} });
                            }
                            rewriteProvenBoundsCheckInPlace(body, inst_vid, unit_const_opt.?);
                            outcome.eliminated_bounds_checks += 1;
                            continue;
                        }
                    }
                }
                try unproven_checks.append(arena_alloc, .{
                    .bb_idx = bb_idx,
                    .inst_val = inst_vid,
                    .kind = .slice_range_check,
                });
            }
        }
    }

    // [4] Step 2 & Step 3: Demand-Sliced Sparse ABCD Pentagon (`< 1.5 MB` peak scratch RAM):
    if (unproven_checks.items.len > 0 and outcome.emitted_error_count == 0) {
        // Canonicalize `copy_val`, single-store local `place_load`, and `.slice_len` `place_load` roots:
        const canon_val = try arena_alloc.alloc(u32, inst_count);
        for (0..inst_count) |v_idx| {
            canon_val[v_idx] = peelCopyValId(body, @intCast(v_idx));
        }
        const first_slice_len_val = try arena_alloc.alloc(u32, local_count);
        @memset(first_slice_len_val, mir.NONE_U32);
        const first_unmut_load_val = try arena_alloc.alloc(u32, local_count);
        @memset(first_unmut_load_val, mir.NONE_U32);

        for (0..block_count) |b_usize| {
            const load_bb = MirBlockId.fromInt(@intCast(b_usize));
            for (body.getBlockInsts(load_bb)) |inst_vid| {
                const v_idx = inst_vid.asInt();
                const peeled = canon_val[v_idx];
                if (extractLoadedPlaceKey(body, peeled)) |pkey| {
                    const is_immut_len = (pkey.kind == .direct_slice_len) or
                        (pkey.kind == .deref_slice_len and isSharedRefLocal(body, pool, pkey.base_local));
                    if (is_immut_len and pkey.base_local < local_count and
                        local_store_counts[pkey.base_local] <= 1)
                    {
                        if (first_slice_len_val[pkey.base_local] == mir.NONE_U32) {
                            first_slice_len_val[pkey.base_local] = peeled;
                        }
                        canon_val[v_idx] = first_slice_len_val[pkey.base_local];
                    } else if (!pkey.isSliceLen() and pkey.base_local < local_count and
                        local_store_counts[pkey.base_local] <= 1)
                    {
                        const uniq_v = local_unique_val[pkey.base_local];
                        const uniq_bb = local_unique_bb[pkey.base_local];
                        if (uniq_v < inst_count and uniq_bb < block_count and
                            dom.isDominatorOf(MirBlockId.fromInt(uniq_bb), load_bb))
                        {
                            canon_val[v_idx] = peelCopyValId(body, uniq_v);
                        } else if (uniq_v == mir.NONE_U32) {
                            if (first_unmut_load_val[pkey.base_local] == mir.NONE_U32) {
                                first_unmut_load_val[pkey.base_local] = peeled;
                            }
                            canon_val[v_idx] = first_unmut_load_val[pkey.base_local];
                        }
                    }
                }
            }
        }

        // Backward demand slice from `unproven_checks` + dominating `cond_br` predicates (`MAX_SUB_VARS = 256`):
        const val_to_pent = try arena_alloc.alloc(u16, inst_count);
        @memset(val_to_pent, std.math.maxInt(u16));
        var pent_vars: std.ArrayListUnmanaged(u32) = .empty;
        try pent_vars.ensureTotalCapacity(arena_alloc, MAX_SUB_VARS);

        const enqueuePentVar = struct {
            //! Local helper registering the canonical root of `raw_v` in `pent_vars` up to `MAX_SUB_VARS`.

            /// Assigns a dense Pentagon variable ID (`0..255`) to `c_map[raw_v]` if not yet mapped.
            fn add(
                raw_v: u32,
                c_map: []const u32,
                v2p: []u16,
                vars_list: *std.ArrayListUnmanaged(u32),
            ) void {
                if (raw_v >= c_map.len or vars_list.items.len >= MAX_SUB_VARS) return;
                const root_v = c_map[raw_v];
                if (root_v >= v2p.len or v2p[root_v] != std.math.maxInt(u16)) return;
                const new_pid: u16 = @intCast(vars_list.items.len);
                v2p[root_v] = new_pid;
                vars_list.appendAssumeCapacity(root_v);
            }
        }.add;

        for (unproven_checks.items) |chk| {
            const inst = body.getInst(chk.inst_val);
            if (chk.kind == .bounds_check) {
                enqueuePentVar(body.extra_args.items[inst.operands.lhs], canon_val, val_to_pent, &pent_vars);
                enqueuePentVar(body.extra_args.items[inst.operands.lhs + 1], canon_val, val_to_pent, &pent_vars);
            } else {
                enqueuePentVar(body.extra_args.items[inst.operands.lhs], canon_val, val_to_pent, &pent_vars);
                enqueuePentVar(body.extra_args.items[inst.operands.lhs + 1], canon_val, val_to_pent, &pent_vars);
                enqueuePentVar(body.extra_args.items[inst.operands.lhs + 2], canon_val, val_to_pent, &pent_vars);
            }
        }

        for (dom.rpo_blocks) |bb_idx| {
            if (!is_intv_reachable[bb_idx]) continue;
            const term = body.blocks.items[bb_idx].terminator;
            if (term.kind == .cond_br and term.cond_or_val < inst_count) {
                var seed_cmps: [32]DecodedBranchCmp = undefined;
                var seed_len: usize = 0;
                collectDerivedCmpGuards(body, dom, term.cond_or_val, true, 0, &seed_cmps, &seed_len);
                collectDerivedCmpGuards(body, dom, term.cond_or_val, false, 0, &seed_cmps, &seed_len);
                for (seed_cmps[0..seed_len]) |cmp| {
                    enqueuePentVar(cmp.lhs_val, canon_val, val_to_pent, &pent_vars);
                    enqueuePentVar(cmp.rhs_val, canon_val, val_to_pent, &pent_vars);
                }
            }
        }

        var bfs_cursor: usize = 0;
        while (bfs_cursor < pent_vars.items.len and pent_vars.items.len < MAX_SUB_VARS) : (bfs_cursor += 1) {
            const cur_v = pent_vars.items[bfs_cursor];
            const inst = body.getInst(MirValueId.fromInt(cur_v));
            switch (inst.op) {
                .unary_op => enqueuePentVar(inst.operands.lhs, canon_val, val_to_pent, &pent_vars),
                .bin_op => {
                    enqueuePentVar(inst.operands.lhs, canon_val, val_to_pent, &pent_vars);
                    enqueuePentVar(inst.operands.rhs, canon_val, val_to_pent, &pent_vars);
                },
                .block_param => {
                    for (0..block_count) |b_i| {
                        const b_params = body.getBlockParams(MirBlockId.fromInt(@intCast(b_i)));
                        for (b_params, 0..) |bp_vid, bp_ord| {
                            if (bp_vid.asInt() == cur_v) {
                                for (body.getPredEdges(MirBlockId.fromInt(@intCast(b_i)))) |peid| {
                                    if (peid.asInt() < body.extra_edges.items.len) {
                                        const ed = body.extra_edges.items[peid.asInt()];
                                        if (bp_ord < ed.args_len and ed.args_start + bp_ord < body.extra_args.items.len) {
                                            enqueuePentVar(
                                                body.extra_args.items[ed.args_start + bp_ord],
                                                canon_val,
                                                val_to_pent,
                                                &pent_vars,
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
                else => {},
            }
        }

        const sub_var_count = pent_vars.items.len;
        if (sub_var_count > 0) {
            const pool_slots = @min(dom.rpo_blocks.len, MAX_PENTAGON_BLOCKS);
            const total_sub_rows = pool_slots * sub_var_count;
            const pentagon_pool = try arena_alloc.alloc(PentagonSubRow, total_sub_rows);
            @memset(pentagon_pool, .{});

            const closed_scratch_a = try arena_alloc.alloc(PentagonSubRow, sub_var_count);
            const closed_scratch_b = try arena_alloc.alloc(PentagonSubRow, sub_var_count);
            outcome.peak_pentagon_bytes = (total_sub_rows + 2 * sub_var_count) * @sizeOf(PentagonSubRow);
            std.debug.assert(outcome.peak_pentagon_bytes < 1_500_000);

            const block_slot_map = try arena_alloc.alloc(u16, block_count);
            @memset(block_slot_map, std.math.maxInt(u16));
            const is_slot_in_use = try arena_alloc.alloc(bool, pool_slots);
            @memset(is_slot_in_use, false);
            const rem_succ_uses = try arena_alloc.alloc(u16, block_count);
            @memset(rem_succ_uses, 0);

            for (dom.rpo_blocks) |bb_idx| {
                if (!is_intv_reachable[bb_idx]) continue;
                for (body.getOutgoingEdges(MirBlockId.fromInt(bb_idx))) |edge| {
                    const dst = edge.target_bb.asInt();
                    if (dst < block_count and is_intv_reachable[dst] and dom.rpo_index[dst] > dom.rpo_index[bb_idx]) {
                        rem_succ_uses[bb_idx] +|= 1;
                    }
                }
            }

            // Pre-populate check block lookup so we can test checks right as each block finishes:
            for (dom.rpo_blocks) |bb_idx| {
                if (!is_intv_reachable[bb_idx]) continue;
                const bb_id = MirBlockId.fromInt(bb_idx);

                populateBlockDomOverrides(
                    body,
                    pool,
                    dom,
                    bb_idx,
                    val_domains,
                    val_intv,
                    local_store_counts,
                    val_overrides,
                    local_overrides,
                    slice_len_overrides,
                );

                var chosen_slot: ?usize = null;
                for (0..pool_slots) |s_idx| {
                    if (!is_slot_in_use[s_idx]) {
                        is_slot_in_use[s_idx] = true;
                        chosen_slot = s_idx;
                        break;
                    }
                }

                const cur_rows = if (chosen_slot) |s_idx| blk: {
                    block_slot_map[bb_idx] = @intCast(s_idx);
                    break :blk pentagon_pool[s_idx * sub_var_count .. (s_idx + 1) * sub_var_count];
                } else closed_scratch_a;
                @memset(cur_rows, .{});

                // Join forward RPO predecessors with `Fix-06A` lazy 1-hop closure before intersection:
                const preds = body.getPredEdges(bb_id);
                var has_seeded_pred = false;
                for (preds) |pred_eid| {
                    if (pred_eid.asInt() >= body.extra_edges.items.len) continue;
                    const edge = body.extra_edges.items[pred_eid.asInt()];
                    const src_bb = edge.src_bb.asInt();
                    if (src_bb >= block_count or !is_intv_reachable[src_bb]) continue;
                    if (dom.rpo_index[src_bb] >= dom.rpo_index[bb_idx]) continue;

                    const src_slot = block_slot_map[src_bb];
                    if (src_slot >= pool_slots) {
                        @memset(cur_rows, .{});
                        has_seeded_pred = true;
                        break;
                    }
                    const src_rows = pentagon_pool[@as(usize, src_slot) * sub_var_count .. (@as(usize, src_slot) + 1) * sub_var_count];
                    closePentagonRowsOneHop(src_rows, closed_scratch_b);

                    // Apply incoming `cond_br` edge inequality (`x < y`, `x <= y`, etc.):
                    const src_term = body.blocks.items[src_bb].terminator;
                    if (src_term.kind == .cond_br and src_term.cond_or_val < inst_count) {
                        const is_then = (pred_eid.asInt() == src_term.edge_start);
                        var in_cmps: [32]DecodedBranchCmp = undefined;
                        var in_cmp_len: usize = 0;
                        collectDerivedCmpGuards(
                            body,
                            dom,
                            src_term.cond_or_val,
                            is_then,
                            0,
                            &in_cmps,
                            &in_cmp_len,
                        );
                        for (in_cmps[0..in_cmp_len]) |cmp| {
                            applyPentagonBranchGuard(
                                cmp,
                                canon_val,
                                val_to_pent,
                                val_intv,
                                val_domains,
                                closed_scratch_b,
                            );
                        }
                    }

                    // Propagate across block-parameter edge arguments (`bp_pid` inherits `arg_pid`):
                    const b_params = body.getBlockParams(bb_id);
                    for (b_params, 0..) |bp_vid, bp_ord| {
                        if (bp_ord < edge.args_len and edge.args_start + bp_ord < body.extra_args.items.len) {
                            const arg_raw = body.extra_args.items[edge.args_start + bp_ord];
                            if (bp_vid.asInt() < inst_count and arg_raw < inst_count) {
                                const bp_pid = val_to_pent[canon_val[bp_vid.asInt()]];
                                const arg_pid = val_to_pent[canon_val[arg_raw]];
                                if (bp_pid < sub_var_count and arg_pid < sub_var_count) {
                                    closed_scratch_b[bp_pid] = closed_scratch_b[bp_pid].unionWith(closed_scratch_b[arg_pid]);
                                }
                            }
                        }
                    }

                    if (!has_seeded_pred) {
                        @memcpy(cur_rows, closed_scratch_b);
                        has_seeded_pred = true;
                    } else {
                        for (0..sub_var_count) |v_i| {
                            cur_rows[v_i] = cur_rows[v_i].intersectWith(closed_scratch_b[v_i]);
                        }
                    }
                }

                // For loop headers, retain only guards enforced by dominating `cond_br` edges:
                if (is_loop_header[bb_idx]) {
                    @memset(cur_rows, .{});
                }

                // Also inject any dominating `cond_br` guards along `idom` chain into `cur_rows`:
                var dom_walk = bb_idx;
                var d_steps: usize = 0;
                while (dom_walk != 0 and d_steps < block_count) : (d_steps += 1) {
                    const idom_bb = dom.idom[dom_walk];
                    if (idom_bb == mir.NONE_U32 or idom_bb == dom_walk) break;
                    const p_term = body.blocks.items[idom_bb].terminator;
                    if (resolveDominatingCondBranchPolarity(body, dom, p_term, MirBlockId.fromInt(dom_walk))) |is_dom_pol| {
                        var dom_cmps: [32]DecodedBranchCmp = undefined;
                        var dom_cmp_len: usize = 0;
                        collectDerivedCmpGuards(
                            body,
                            dom,
                            p_term.cond_or_val,
                            is_dom_pol,
                            0,
                            &dom_cmps,
                            &dom_cmp_len,
                        );
                        for (dom_cmps[0..dom_cmp_len]) |cmp| {
                            applyPentagonBranchGuard(
                                cmp,
                                canon_val,
                                val_to_pent,
                                val_intv,
                                val_domains,
                                cur_rows,
                            );
                        }
                    }
                    dom_walk = idom_bb;
                }

                // Step relational transfer rules across instructions in `bb_idx`:
                for (body.getBlockInsts(bb_id)) |inst_vid| {
                    const v_idx = inst_vid.asInt();
                    const root_v = canon_val[v_idx];
                    const dst_pid = val_to_pent[root_v];
                    if (dst_pid >= sub_var_count) continue;
                    const inst = body.getInst(inst_vid);
                    switch (inst.op) {
                        .unary_op => {
                            const uk: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                            if ((uk == .int_zext or uk == .int_sext) and inst.operands.lhs < inst_count) {
                                const src_raw = inst.operands.lhs;
                                const src_pid = val_to_pent[canon_val[src_raw]];
                                if (src_pid < sub_var_count) {
                                    const src_iv = readDomRefinedIntv(
                                        body,
                                        src_raw,
                                        val_intv,
                                        val_overrides,
                                        local_overrides,
                                        slice_len_overrides,
                                        local_store_counts,
                                    );
                                    const is_preserving_math_val = if (val_domains[src_raw]) |s_dom| blk: {
                                        if (uk == .int_zext) {
                                            break :blk !s_dom.is_signed or
                                                (!src_iv.isBottom() and decodeIntvToI128(src_iv, s_dom).lo >= 0);
                                        }
                                        const sign_lim = @as(i128, 1) << @intCast(s_dom.bits - 1);
                                        break :blk s_dom.is_signed or
                                            (!src_iv.isBottom() and decodeIntvToI128(src_iv, s_dom).hi < sign_lim);
                                    } else false;
                                    if (is_preserving_math_val) {
                                        cur_rows[dst_pid] = cur_rows[dst_pid].unionWith(cur_rows[src_pid]);
                                    }
                                }
                            }
                        },
                        .bin_op => {
                            const bk: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                            const lhs_raw = inst.operands.lhs;
                            const rhs_raw = inst.operands.rhs;
                            if (lhs_raw < inst_count and rhs_raw < inst_count) {
                                const lhs_pid = val_to_pent[canon_val[lhs_raw]];
                                const rhs_pid = val_to_pent[canon_val[rhs_raw]];
                                const l_iv = readDomRefinedIntv(
                                    body,
                                    lhs_raw,
                                    val_intv,
                                    val_overrides,
                                    local_overrides,
                                    slice_len_overrides,
                                    local_store_counts,
                                );
                                const r_iv = readDomRefinedIntv(
                                    body,
                                    rhs_raw,
                                    val_intv,
                                    val_overrides,
                                    local_overrides,
                                    slice_len_overrides,
                                    local_store_counts,
                                );
                                const d_iv = readDomRefinedIntv(
                                    body,
                                    v_idx,
                                    val_intv,
                                    val_overrides,
                                    local_overrides,
                                    slice_len_overrides,
                                    local_store_counts,
                                );
                                if (bk == .urem_checked and rhs_pid < sub_var_count) {
                                    // Soundness guard (`[CRITICAL-01]`): `a % d < d` ONLY when `0 ∉ Intv(d)`:
                                    if (val_domains[rhs_raw]) |r_dom| {
                                        if (!r_iv.isBottom() and decodeIntvToI128(r_iv, r_dom).lo >= 1) {
                                            cur_rows[dst_pid].insert(@intCast(rhs_pid));
                                            cur_rows[dst_pid] = cur_rows[dst_pid].unionWith(cur_rows[rhs_pid]);
                                        }
                                    }
                                } else if ((bk == .ssub_checked or bk == .usub_checked or bk == .sub_wrap) and
                                    lhs_pid < sub_var_count)
                                {
                                    if (val_domains[rhs_raw]) |r_dom| {
                                        if (!r_iv.isBottom() and !d_iv.isBottom() and !l_iv.isBottom()) {
                                            const rb = decodeIntvToI128(r_iv, r_dom);
                                            const lb = decodeIntvToI128(l_iv, val_domains[lhs_raw] orelse r_dom);
                                            if (rb.lo >= 1 and (bk != .sub_wrap or lb.lo >= rb.hi)) {
                                                cur_rows[dst_pid].insert(@intCast(lhs_pid));
                                                cur_rows[dst_pid] = cur_rows[dst_pid].unionWith(cur_rows[lhs_pid]);
                                            }
                                        }
                                    }
                                } else if ((bk == .sadd_checked or bk == .uadd_checked or bk == .add_wrap) and
                                    lhs_pid < sub_var_count)
                                {
                                    if (val_domains[rhs_raw]) |r_dom| {
                                        const d_dom = val_domains[v_idx] orelse r_dom;
                                        if (!r_iv.isBottom() and !l_iv.isBottom()) {
                                            const rb = decodeIntvToI128(r_iv, r_dom);
                                            const lb = decodeIntvToI128(l_iv, val_domains[lhs_raw] orelse r_dom);
                                            const db = decodeIntvToI128(d_dom.top_intv, d_dom);
                                            if (rb.lo >= 1 and lb.hi + rb.hi <= db.hi) {
                                                cur_rows[lhs_pid].insert(@intCast(dst_pid));
                                                cur_rows[lhs_pid] = cur_rows[lhs_pid].unionWith(cur_rows[dst_pid]);
                                            }
                                        }
                                    }
                                } else if (bk == .bit_and and rhs_pid < sub_var_count) {
                                    // `x & (len - 1) < len` when `rhs < z` for any `z ∈ sub[rhs]`:
                                    if (val_domains[v_idx]) |d_dom| {
                                        if (!d_dom.is_signed or (!d_iv.isBottom() and decodeIntvToI128(d_iv, d_dom).lo >= 0)) {
                                            cur_rows[dst_pid] = cur_rows[dst_pid].unionWith(cur_rows[rhs_pid]);
                                        }
                                    }
                                }
                            }
                        },
                        else => {},
                    }
                }

                // Close 1-hop and test all pending checks residing in `bb_idx`:
                closePentagonRowsOneHop(cur_rows, closed_scratch_b);
                for (unproven_checks.items) |chk| {
                    if (chk.bb_idx != bb_idx) continue;
                    const c_inst = body.getInst(chk.inst_val);
                    const c_tok = body.origin_tokens.items[chk.inst_val.asInt()];
                    var is_proven = false;

                    if (chk.kind == .bounds_check) {
                        const idx_v = body.extra_args.items[c_inst.operands.lhs];
                        const len_v = body.extra_args.items[c_inst.operands.lhs + 1];
                        if (idx_v < inst_count and len_v < inst_count) {
                            const idx_pid = val_to_pent[canon_val[idx_v]];
                            const len_pid = val_to_pent[canon_val[len_v]];
                            const idx_iv = readDomRefinedIntv(
                                body,
                                idx_v,
                                val_intv,
                                val_overrides,
                                local_overrides,
                                slice_len_overrides,
                                local_store_counts,
                            );
                            const is_non_neg = if (val_domains[idx_v]) |id_dom|
                                (!id_dom.is_signed or (!idx_iv.isBottom() and decodeIntvToI128(idx_iv, id_dom).lo >= 0))
                            else
                                false;
                            if (is_non_neg and idx_pid < sub_var_count and len_pid < sub_var_count and
                                closed_scratch_b[idx_pid].contains(@intCast(len_pid)))
                            {
                                is_proven = true;
                            }
                        }
                    } else if (chk.kind == .slice_range_check) {
                        const lo_v = body.extra_args.items[c_inst.operands.lhs];
                        const hi_v = body.extra_args.items[c_inst.operands.lhs + 1];
                        const len_v = body.extra_args.items[c_inst.operands.lhs + 2];
                        if (lo_v < inst_count and hi_v < inst_count and len_v < inst_count) {
                            const lo_pid = val_to_pent[canon_val[lo_v]];
                            const hi_pid = val_to_pent[canon_val[hi_v]];
                            const len_pid = val_to_pent[canon_val[len_v]];
                            const lo_iv = readDomRefinedIntv(
                                body,
                                lo_v,
                                val_intv,
                                val_overrides,
                                local_overrides,
                                slice_len_overrides,
                                local_store_counts,
                            );
                            const hi_iv = readDomRefinedIntv(
                                body,
                                hi_v,
                                val_intv,
                                val_overrides,
                                local_overrides,
                                slice_len_overrides,
                                local_store_counts,
                            );
                            const len_iv = readDomRefinedIntv(
                                body,
                                len_v,
                                val_intv,
                                val_overrides,
                                local_overrides,
                                slice_len_overrides,
                                local_store_counts,
                            );
                            const is_lo_non_neg = if (val_domains[lo_v]) |ld|
                                (!ld.is_signed or (!lo_iv.isBottom() and decodeIntvToI128(lo_iv, ld).lo >= 0))
                            else
                                false;
                            const is_lo_le_hi = (canon_val[lo_v] == canon_val[hi_v]) or
                                (lo_pid < sub_var_count and hi_pid < sub_var_count and closed_scratch_b[lo_pid].contains(@intCast(hi_pid))) or
                                blk: {
                                    if (val_domains[lo_v] != null and val_domains[hi_v] != null and
                                        !lo_iv.isBottom() and !hi_iv.isBottom())
                                    {
                                        break :blk decodeIntvToI128(lo_iv, val_domains[lo_v].?).hi <=
                                            decodeIntvToI128(hi_iv, val_domains[hi_v].?).lo;
                                    }
                                    break :blk false;
                                };
                            const is_hi_le_len = (canon_val[hi_v] == canon_val[len_v]) or
                                (hi_pid < sub_var_count and len_pid < sub_var_count and closed_scratch_b[hi_pid].contains(@intCast(len_pid))) or
                                blk: {
                                    if (val_domains[hi_v] != null and val_domains[len_v] != null and
                                        !hi_iv.isBottom() and !len_iv.isBottom())
                                    {
                                        break :blk decodeIntvToI128(hi_iv, val_domains[hi_v].?).hi <=
                                            decodeIntvToI128(len_iv, val_domains[len_v].?).lo;
                                    }
                                    break :blk false;
                                };
                            if (is_lo_non_neg and is_lo_le_hi and is_hi_le_len) {
                                is_proven = true;
                            }
                        }
                    }

                    if (is_proven) {
                        if (unit_const_opt == null) {
                            unit_const_opt = try body.appendConst(.{ .unit_val = {} });
                        }
                        rewriteProvenBoundsCheckInPlace(body, chk.inst_val, unit_const_opt.?);
                        outcome.eliminated_bounds_checks += 1;
                    } else if (config.is_sast_strict and !has_body_no_panic) {
                        try emitSastDiag(
                            config.diagnostic_sink,
                            .w0314_unproven_bounds_access,
                            .warning,
                            resolveTokenSpan(body.file_id, c_tok, config, decl_fallback_span),
                            "slice or array bounds check could not be statically discharged under `--sast-strict`",
                            "runtime bounds check retained here",
                            null,
                            null,
                            "guard the index with `if idx < slice.len` or use fallible `.get(idx)`",
                        );
                    }
                }

                // Recycle dead predecessor slots as soon as all forward RPO successors finish:
                if (rem_succ_uses[bb_idx] == 0) {
                    const self_s = block_slot_map[bb_idx];
                    if (self_s < pool_slots) {
                        is_slot_in_use[self_s] = false;
                        block_slot_map[bb_idx] = std.math.maxInt(u16);
                    }
                }
                for (preds) |pred_eid| {
                    if (pred_eid.asInt() >= body.extra_edges.items.len) continue;
                    const src_bb = body.extra_edges.items[pred_eid.asInt()].src_bb.asInt();
                    if (src_bb < block_count and dom.rpo_index[src_bb] < dom.rpo_index[bb_idx] and rem_succ_uses[src_bb] > 0) {
                        rem_succ_uses[src_bb] -= 1;
                        if (rem_succ_uses[src_bb] == 0) {
                            const old_s = block_slot_map[src_bb];
                            if (old_s < pool_slots) {
                                is_slot_in_use[old_s] = false;
                                block_slot_map[src_bb] = std.math.maxInt(u16);
                            }
                        }
                    }
                }
            }
        }
    }

    // [5] Post-BCE per-block `may_panic` scan (for Pass 3 `@no_panic` `E0321` & `Fix-06B` `W0329`):
    for (dom.rpo_blocks) |bb_idx| {
        if (!is_intv_reachable[bb_idx]) continue;
        populateBlockDomOverrides(
            body,
            pool,
            dom,
            bb_idx,
            val_domains,
            val_intv,
            local_store_counts,
            val_overrides,
            local_overrides,
            slice_len_overrides,
        );
        var has_block_panic = false;
        const term = body.blocks.items[bb_idx].terminator;
        if (term.kind == .trap) {
            has_block_panic = true;
        }
        for (body.getBlockInsts(MirBlockId.fromInt(bb_idx))) |inst_vid| {
            const inst = body.getInst(inst_vid);
            if (inst.op == .intrinsic_op) {
                const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                switch (ikind) {
                    .bounds_check,
                    .slice_range_check,
                    .narrow_check,
                    .compile_assert,
                    .compile_error,
                    .abort_vacated_panic,
                    => has_block_panic = true,
                    else => {},
                }
            } else if (inst.flags.has_trap_risk) {
                const lhs_iv = readDomRefinedIntv(
                    body,
                    inst.operands.lhs,
                    val_intv,
                    val_overrides,
                    local_overrides,
                    slice_len_overrides,
                    local_store_counts,
                );
                const rhs_iv = readDomRefinedIntv(
                    body,
                    inst.operands.rhs,
                    val_intv,
                    val_overrides,
                    local_overrides,
                    slice_len_overrides,
                    local_store_counts,
                );
                if (!isCheckedInstProvenSafeByIntv(inst, lhs_iv, rhs_iv, val_domains)) {
                    has_block_panic = true;
                }
            }
        }
        if (has_block_panic) {
            outcome.block_may_panic[bb_idx] = true;
            outcome.has_residual_may_panic = true;
        }
    }

    return outcome;
}

/// Applies a decoded `cond_br` relational guard (`<`, `<=`, `>`, `>=`, `==`) onto `rows`.
fn applyPentagonBranchGuard(
    cmp: DecodedBranchCmp,
    canon_val: []const u32,
    val_to_pent: []const u16,
    val_intv: []const Intv,
    val_domains: []const ?ScalarIntDomain,
    rows: []PentagonSubRow,
) void {
    const var_count = rows.len;
    if (cmp.lhs_val >= canon_val.len or cmp.rhs_val >= canon_val.len) return;
    const lhs_pid = val_to_pent[canon_val[cmp.lhs_val]];
    const rhs_pid = val_to_pent[canon_val[cmp.rhs_val]];
    if (lhs_pid >= var_count or rhs_pid >= var_count or lhs_pid == rhs_pid) return;

    const eff_op: BinOpKind = if (cmp.is_positive) cmp.op else switch (cmp.op) {
        .slt => .sge,
        .ult => .uge,
        .sle => .sgt,
        .ule => .ugt,
        .sgt => .sle,
        .ugt => .ule,
        .sge => .slt,
        .uge => .ult,
        .eq => .ne,
        .ne => .eq,
        else => return,
    };

    // Verify mathematical $\mathbb{Z}$ order preservation when signedness of `eff_op` differs from operand domains:
    const is_unsigned_cmp = switch (eff_op) {
        .ult, .ule, .ugt, .uge => true,
        else => false,
    };
    const is_signed_cmp = switch (eff_op) {
        .slt, .sle, .sgt, .sge => true,
        else => false,
    };
    if (is_unsigned_cmp or is_signed_cmp) {
        for ([2]u32{ cmp.lhs_val, cmp.rhs_val }) |op_val| {
            if (op_val >= val_intv.len or op_val >= val_domains.len) return;
            const dom = val_domains[op_val] orelse return;
            const iv = val_intv[op_val];
            if (is_unsigned_cmp and dom.is_signed) {
                if (iv.isBottom() or decodeIntvToI128(iv, dom).lo < 0) return;
            } else if (is_signed_cmp and !dom.is_signed) {
                const sign_lim = @as(i128, 1) << @intCast(dom.bits - 1);
                if (iv.isBottom() or decodeIntvToI128(iv, dom).hi >= sign_lim) return;
            }
        }
    }

    switch (eff_op) {
        .slt, .ult => {
            rows[lhs_pid].insert(@intCast(rhs_pid));
            rows[lhs_pid] = rows[lhs_pid].unionWith(rows[rhs_pid]);
        },
        .sle, .ule => {
            rows[lhs_pid] = rows[lhs_pid].unionWith(rows[rhs_pid]);
        },
        .sgt, .ugt => {
            rows[rhs_pid].insert(@intCast(lhs_pid));
            rows[rhs_pid] = rows[rhs_pid].unionWith(rows[lhs_pid]);
        },
        .sge, .uge => {
            rows[rhs_pid] = rows[rhs_pid].unionWith(rows[lhs_pid]);
        },
        .eq => {
            const merged = rows[lhs_pid].unionWith(rows[rhs_pid]);
            rows[lhs_pid] = merged;
            rows[rhs_pid] = merged;
        },
        else => {},
    }
}

// ----------- Pass 3: Summaries, Contracts & Sandbox -----------

/// Detects whether `place_id` accesses `Context.allocator` (`slot_ordinal == 0`).
fn isContextAllocatorPlace(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    place_id: PlaceId,
) bool {
    if (place_id.asInt() >= body.places.items.len) return false;
    const pl_rec = body.places.items[place_id.asInt()];
    if (pl_rec.base >= body.locals.items.len) return false;
    if (!type_system.isContextType(pool, sym_table, body.locals.items[pl_rec.base].type_id)) return false;
    for (body.getPlaceProjections(place_id)) |proj| {
        if (proj.kind == .field and
            proj.payload == ContextFieldLayout.CANONICAL_FIELDS[0].slot_ordinal)
        {
            return true;
        }
    }
    return false;
}

/// Infers capabilities on prototype-only/intrinsic callees lacking a `MirBody` or `@std_cap_boundary`.
fn inferExternalPrototypeEffects(sym: SymbolRecord) EffectCapabilityMask {
    var base = EffectCapabilityMask.EMPTY;
    if (sym.flags.is_extern) {
        base.ffi = true;
        base.unsafe_op = true;
        if (!sym.contract_flags.is_no_alloc) base.alloc = true;
        if (!sym.contract_flags.is_no_panic) base.may_panic = true;
        if (!sym.contract_flags.is_no_block) base.blocking_sync = true;
        return base;
    }

    const name = sym.name_text;
    if (EXTERN_PROTO_EFFECT_MAP.get(name)) |eff| base = base.unionWith(eff);
    if (std.mem.startsWith(u8, name, "fs_")) {
        base.fs = true;
    } else if (std.mem.startsWith(u8, name, "net_")) {
        base.net = true;
    } else if (std.mem.startsWith(u8, name, "env_")) {
        base.env = true;
    } else if (std.mem.startsWith(u8, name, "proc_")) {
        base.process = true;
    } else if (std.mem.startsWith(u8, name, "clock_")) {
        base.clock = true;
    } else if (std.mem.startsWith(u8, name, "entropy_")) {
        base.entropy = true;
    }
    if (HEAP_GROWTH_METHOD_MAP.has(name)) {
        base.alloc = true;
    }
    if (sym.contract_flags.is_no_alloc) base.alloc = false;
    if (sym.contract_flags.is_no_panic) base.may_panic = false;
    if (sym.contract_flags.is_no_block) {
        base = base.withoutBits(EffectCapabilityMask.BLOCKING_BITS);
    }
    return base;
}

/// Computes aligned stack frame byte size (`16B`-aligned) for all locals in `body`.
fn computeOwnStackFrameBytes(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) u32 {
    var total_bytes: u64 = 0;
    for (body.locals.items) |loc| {
        if (loc.type_id.isError() or loc.type_id == .unit_ty or loc.type_id == .never_ty) continue;
        const lay = type_system.computeTypeLayoutWithPool(
            pool,
            sym_table,
            loc.type_id,
            body.target_layout,
        );
        const align_u64: u64 = @max(@as(u64, lay.align_bytes), 1);
        total_bytes = std.mem.alignForward(u64, total_bytes, align_u64);
        total_bytes +|= lay.byte_size;
    }
    total_bytes = std.mem.alignForward(u64, total_bytes, 16);
    return @intCast(@min(total_bytes, FnRegionSummary.STACK_UNBOUNDED - 1));
}

/// Returns `true` if `base_local` in `body` has `<= max_stores` stores and zero mutable borrows/out-args.
fn isUnmutatedCallableLocal(
    body: *const MirBody,
    pool: *const InternPool,
    base_local: u32,
    max_stores: u32,
) bool {
    if (base_local >= body.locals.items.len) return false;
    const base_decl = body.locals.items[base_local];
    var store_count: u32 = if (base_decl.flags().is_arg and base_decl.mode() != .set_mode) 1 else 0;
    if (store_count > max_stores) return false;
    for (0..body.insts.len) |scan_i| {
        const inst = body.getInst(MirValueId.fromInt(@intCast(scan_i)));
        if (inst.op == .place_store and inst.operands.lhs < body.places.items.len) {
            if (body.places.items[inst.operands.lhs].base == base_local) {
                store_count +|= 1;
                if (store_count > max_stores) return false;
            }
        } else if (inst.op == .place_addr and inst.operands.lhs < body.places.items.len) {
            if (body.places.items[inst.operands.lhs].base == base_local) {
                const unwrapped = pool.unwrapUnderlyingType(inst.type_id);
                if (unwrapped.isError() or pool.getNode(unwrapped).tag != .ref_ty) return false;
            }
        }
    }
    for (body.calls.items) |call_site| {
        for (0..call_site.args_len) |arg_i| {
            const mode = body.call_arg_modes.items[call_site.modes_start + arg_i];
            const word = body.extra_args.items[call_site.args_start + arg_i];
            if ((mode == .inout_mode or mode == .set_mode) and word < body.places.items.len) {
                if (body.places.items[word].base == base_local) return false;
            }
        }
    }
    return true;
}

/// Infers conservative indirect call effects from a callable SSA value's `FnSignatureView` or `dyn Trait` ceiling.
fn inferCallableTypeIndirectEffects(
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    val_raw: u32,
) EffectCapabilityMask {
    var ind_eff = EffectCapabilityMask{
        .alloc = true,
        .may_panic = true,
        .blocking_sync = true,
        .indirect_opaque = true,
    };
    if (val_raw < body.insts.len) {
        const raw_ty = body.getInst(MirValueId.fromInt(val_raw)).type_id;
        if (extractDynTraitSymbol(pool, raw_ty)) |trait_sym_idx| {
            if (trait_sym_idx.asInt() < sym_table.symbols.items.len) {
                const trait_sym = sym_table.getSymbol(trait_sym_idx).*;
                var has_no_alloc = trait_sym.contract_flags.is_no_alloc;
                var has_no_panic = trait_sym.contract_flags.is_no_panic;
                var has_no_block = trait_sym.contract_flags.is_no_block;
                if (!trait_sym.target_scope.isNone()) {
                    var has_any_fn = false;
                    var is_all_no_alloc = true;
                    var is_all_no_panic = true;
                    var is_all_no_block = true;
                    for (sym_table.getScopeMembers(trait_sym.target_scope)) |t_mem_idx| {
                        const t_mem = sym_table.getSymbol(t_mem_idx).*;
                        if (t_mem.kind != .fn_sym) continue;
                        has_any_fn = true;
                        if (!t_mem.contract_flags.is_no_alloc) is_all_no_alloc = false;
                        if (!t_mem.contract_flags.is_no_panic) is_all_no_panic = false;
                        if (!t_mem.contract_flags.is_no_block) is_all_no_block = false;
                    }
                    if (has_any_fn) {
                        has_no_alloc = has_no_alloc or is_all_no_alloc;
                        has_no_panic = has_no_panic or is_all_no_panic;
                        has_no_block = has_no_block or is_all_no_block;
                    }
                }
                ind_eff.alloc = !has_no_alloc;
                ind_eff.may_panic = !has_no_panic;
                ind_eff.blocking_sync = !has_no_block;
                ind_eff.indirect_opaque = !(has_no_alloc or has_no_panic or has_no_block);
            }
        } else {
            var c_ty = pool.unwrapUnderlyingType(raw_ty);
            if (!c_ty.isError() and (pool.getNode(c_ty).tag == .ref_ty or pool.getNode(c_ty).tag == .mut_ref_ty)) {
                c_ty = pool.unwrapUnderlyingType(TypeId.fromInt(pool.getNode(c_ty).lhs));
            }
            if (!c_ty.isError()) {
                if (pool.getFnSignatureView(c_ty)) |sig_v| {
                    ind_eff.alloc = !sig_v.contracts.has_no_alloc;
                    ind_eff.may_panic = !sig_v.contracts.has_no_panic;
                    ind_eff.blocking_sync = !sig_v.contracts.has_no_block;
                    ind_eff.indirect_opaque = !sig_v.contracts.hasAny();
                }
            }
        }
    }
    return ind_eff;
}

/// Resolves whether `callee_val` loads or copies an unmutated formal callable parameter (`0..15`).
fn extractFormalCallbackParamOrd(
    body: *const MirBody,
    pool: *const InternPool,
    callee_val: MirValueId,
) ?u4 {
    const peeled = peelCopyValId(body, callee_val.asInt());
    if (peeled >= body.insts.len) return null;
    const inst = body.getInst(MirValueId.fromInt(peeled));
    if (inst.op != .place_load or inst.operands.lhs >= body.places.items.len) return null;
    const pl_rec = body.places.items[inst.operands.lhs];
    if (pl_rec.proj_len != 0) return null;
    if (pl_rec.base >= 1 and pl_rec.base <= body.param_count) {
        const param_ord = pl_rec.base - 1;
        if (param_ord < 16 and isUnmutatedCallableLocal(body, pool, pl_rec.base, 1)) {
            return @intCast(param_ord);
        }
    }
    return null;
}

/// Extracts a callable target `(def_id, sym_idx)` when `arg_val_raw` is an unmutated `fn_addr` or `closure_make`.
fn extractPassedCallableTarget(
    body: *const MirBody,
    pool: *const InternPool,
    arg_val_raw: u32,
) ?struct { def_id: DefId, sym_idx: SymbolIndex } {
    var cur_raw = peelCopyValId(body, arg_val_raw);
    if (cur_raw >= body.insts.len) return null;
    var inst = body.getInst(MirValueId.fromInt(cur_raw));
    if (inst.op == .place_load and inst.operands.lhs < body.places.items.len) {
        const pl_rec = body.places.items[inst.operands.lhs];
        if (pl_rec.proj_len == 0 and isUnmutatedCallableLocal(body, pool, pl_rec.base, 1)) {
            for (0..body.insts.len) |scan_i| {
                const s_inst = body.getInst(MirValueId.fromInt(@intCast(scan_i)));
                if (s_inst.op == .place_store and s_inst.operands.lhs == inst.operands.lhs and
                    s_inst.operands.rhs < body.insts.len)
                {
                    cur_raw = peelCopyValId(body, s_inst.operands.rhs);
                    inst = body.getInst(MirValueId.fromInt(cur_raw));
                    break;
                }
            }
        } else {
            return null;
        }
    }
    if (inst.op == .fn_addr) {
        return .{
            .def_id = if (inst.operands.lhs != mir.NONE_U32) DefId.fromInt(inst.operands.lhs) else .NONE,
            .sym_idx = if (inst.operands.rhs != mir.NONE_U32) SymbolIndex.fromInt(inst.operands.rhs) else .none,
        };
    }
    if (inst.op == .aggregate_make) {
        const agg_k: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
        if (agg_k == .closure_make) {
            return .{
                .def_id = DefId.fromInt(inst.operands.lhs),
                .sym_idx = .none,
            };
        }
    }
    return null;
}

/// Formats a human-readable capability list (`fs, net, alloc`) into `alloc`.
fn formatEffectBitsList(alloc: std.mem.Allocator, bits: u16) ![]const u8 {
    const Entry = struct {
        //! Mapping between a single `EffectCapabilityMask` bit and its canonical diagnostic name.

        /// Bitmask position in `EffectCapabilityMask`.
        bit: u16,
        /// Canonical human-readable capability label.
        label: []const u8,
    };
    const table = [_]Entry{
        .{ .bit = 1 << 0, .label = "fs" },
        .{ .bit = 1 << 1, .label = "net" },
        .{ .bit = 1 << 2, .label = "env" },
        .{ .bit = 1 << 3, .label = "process" },
        .{ .bit = 1 << 4, .label = "ffi" },
        .{ .bit = 1 << 5, .label = "unsafe_op" },
        .{ .bit = 1 << 6, .label = "alloc" },
        .{ .bit = 1 << 7, .label = "may_panic" },
        .{ .bit = 1 << 8, .label = "clock" },
        .{ .bit = 1 << 9, .label = "entropy" },
        .{ .bit = 1 << 10, .label = "blocking_sync" },
        .{ .bit = 1 << 11, .label = "indirect_opaque" },
    };

    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(alloc);
    var is_first = true;
    for (table) |entry| {
        if ((bits & entry.bit) != 0) {
            if (!is_first) try out.appendSlice(alloc, ", ");
            try out.appendSlice(alloc, entry.label);
            is_first = false;
        }
    }
    if (is_first) try out.appendSlice(alloc, "none");
    return out.toOwnedSlice(alloc);
}

/// Formats a `WitnessStep` chain (`caller ▸ hop ▸ leaf`) using monochrome `▸` (`AGENTS.md` §5).
fn formatWitnessChainNote(
    alloc: std.mem.Allocator,
    store: *const FnSummaryStore,
    sym_table: *const SymbolTable,
    interner_opt: ?*const StringInterner,
    root_slot: u32,
    steps: []const WitnessStep,
) !?[]const u8 {
    if (steps.len == 0) return null;

    const slotName = struct {
        //! Local helper resolving the display name of a summary store slot for witness chain notes.

        /// Returns the source symbol, interned closure name, or `<indirect>` / `<closure>` fallback for `slot`.
        fn resolve(
            st: *const FnSummaryStore,
            syms: *const SymbolTable,
            int_opt: ?*const StringInterner,
            slot: u32,
        ) []const u8 {
            if (slot >= st.summaries.len) return "<indirect>";
            const sym_i = st.symbol_indices[slot];
            if (!sym_i.isNone() and sym_i.asInt() < syms.symbols.items.len) {
                return syms.getSymbol(sym_i).name_text;
            }
            if (int_opt) |interner| {
                if (st.names[slot] != .empty) return interner.get(st.names[slot]);
            }
            return "<closure>";
        }
    }.resolve;

    var buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer buf.deinit(alloc);
    try buf.appendSlice(alloc, "call witness: `");
    try buf.appendSlice(alloc, slotName(store, sym_table, interner_opt, root_slot));

    for (steps) |step| {
        try buf.appendSlice(alloc, "` ▸ `");
        if (step.callee_slot != mir.NONE_U32) {
            try buf.appendSlice(alloc, slotName(store, sym_table, interner_opt, step.callee_slot));
        } else {
            const ek = step.edge.meta().edge_kind;
            const label = switch (ek) {
                .indirect_fn_ptr => "<indirect fn ptr>",
                .indirect_vtable => "<dyn Trait vtable>",
                .auto_drop_glue => "<auto-drop glue>",
                .forwarded_cb_arg => "<callback arg>",
                else => "<external op>",
            };
            try buf.appendSlice(alloc, label);
        }
    }
    try buf.append(alloc, '`');
    return try buf.toOwnedSlice(alloc);
}

/// Descriptor for a single basic block slice inside a vacated non-`Copy` `inout` `subscript` window.
const VacatedWindowBlockSlice = struct {
    /// Index of the basic block covered by this vacated window slice.
    bb_idx: u32,
    /// Inclusive starting instruction index within `body.getBlockInsts(bb_idx)`.
    inst_lo: usize,
    /// Exclusive ending instruction index within `body.getBlockInsts(bb_idx)`.
    inst_hi: usize,
    /// `true` when the block terminator executes before the vacated window closes.
    has_terminator: bool,
};

/// Collects CFG-reachable basic block instruction slices inside `win` via bounded BFS (`Fix-06B`).
fn collectVacatedWindowSlices(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    win: mir.VacatedProjectionWindow,
) ![]VacatedWindowBlockSlice {
    const block_count = body.blocks.items.len;
    if (block_count == 0 or win.start_block.asInt() >= block_count) return &.{};

    const start_bb = win.start_block.asInt();
    const end_bb = win.end_block.asInt();

    var start_pos: usize = 0;
    if (!win.access_token.isNone()) {
        const start_insts = body.getBlockInsts(win.start_block);
        for (start_insts, 0..) |vid, pos| {
            if (vid == win.access_token) {
                start_pos = pos + 1;
                break;
            }
        }
    }

    var end_close_pos: ?usize = null;
    if (!win.access_token.isNone() and end_bb < block_count) {
        const end_insts = body.getBlockInsts(win.end_block);
        for (end_insts, 0..) |vid, pos| {
            const inst = body.getInst(vid);
            if (inst.op == .ghost_access_end and inst.operands.lhs == win.access_token.asInt()) {
                end_close_pos = pos;
                break;
            }
        }
    }

    const is_visited = try allocator.alloc(bool, block_count);
    defer allocator.free(is_visited);
    @memset(is_visited, false);

    var queue: std.ArrayListUnmanaged(u32) = .empty;
    defer queue.deinit(allocator);
    var out_slices: std.ArrayListUnmanaged(VacatedWindowBlockSlice) = .empty;
    errdefer out_slices.deinit(allocator);

    is_visited[start_bb] = true;
    try queue.append(allocator, start_bb);

    var q_head: usize = 0;
    while (q_head < queue.items.len) : (q_head += 1) {
        const cur_bb = queue.items[q_head];
        const cur_insts = body.getBlockInsts(MirBlockId.fromInt(cur_bb));
        const slice_lo: usize = if (cur_bb == start_bb) @min(start_pos, cur_insts.len) else 0;
        var local_close_pos: ?usize = if (cur_bb == end_bb) end_close_pos else null;
        if (local_close_pos == null and !win.access_token.isNone() and slice_lo < cur_insts.len) {
            for (cur_insts[slice_lo..], slice_lo..) |vid, pos| {
                const inst = body.getInst(vid);
                if (inst.op == .ghost_access_end and inst.operands.lhs == win.access_token.asInt()) {
                    local_close_pos = pos;
                    break;
                }
            }
        }
        const is_stopping_in_cur = (local_close_pos != null) or
            (cur_bb == end_bb and (end_bb != start_bb or cur_insts.len > slice_lo));
        const slice_hi: usize = if (local_close_pos) |close_pos|
            @min(close_pos, cur_insts.len)
        else
            cur_insts.len;
        const has_terminator = (local_close_pos == null) and !(cur_bb == end_bb and end_close_pos != null);

        try out_slices.append(allocator, .{
            .bb_idx = cur_bb,
            .inst_lo = slice_lo,
            .inst_hi = @max(slice_lo, slice_hi),
            .has_terminator = has_terminator,
        });

        if (is_stopping_in_cur and local_close_pos != null) continue;
        if (cur_bb == end_bb and cur_bb != start_bb) continue;

        for (body.getOutgoingEdges(MirBlockId.fromInt(cur_bb))) |edge| {
            const dst_bb = edge.target_bb.asInt();
            if (dst_bb < block_count and !is_visited[dst_bb]) {
                is_visited[dst_bb] = true;
                try queue.append(allocator, dst_bb);
            }
        }
    }

    return out_slices.toOwnedSlice(allocator);
}

/// Marks instructions, calls, and `.trap` blocks inside `win_slices` with `is_abort_on_panic` and `abort_vacated_panic`.
fn insertVacatedPanicAbortGuard(
    body: *MirBody,
    win_slices: []const VacatedWindowBlockSlice,
    site_tok: TokenIndex,
) !void {
    var has_inserted_in_trap = false;

    for (win_slices) |wslice| {
        if (wslice.bb_idx >= body.blocks.items.len) continue;
        const cur_insts = body.getBlockInsts(MirBlockId.fromInt(wslice.bb_idx));
        const hi = @min(wslice.inst_hi, cur_insts.len);
        const lo = @min(wslice.inst_lo, hi);
        for (cur_insts[lo..hi]) |vid| {
            var inst = body.getInst(vid);
            inst.flags.is_abort_on_panic = true;
            body.insts.set(vid.asInt(), inst);
        }

        if (!wslice.has_terminator) continue;
        const term = body.blocks.items[wslice.bb_idx].terminator;
        if (term.kind == .call and term.cond_or_val < body.calls.items.len) {
            body.calls.items[term.cond_or_val].is_abort_on_panic = true;
        } else if (term.kind == .trap) {
            body.blocks.items[wslice.bb_idx].terminator.aux_u8 |= mir.TRAP_ABORT_ON_PANIC_FLAG;

            var has_existing_slice = false;
            for (cur_insts) |iv| {
                const inst = body.getInst(iv);
                if (inst.op == .intrinsic_op and
                    @as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .abort_vacated_panic)
                {
                    has_existing_slice = true;
                    break;
                }
            }
            if (has_existing_slice) {
                has_inserted_in_trap = true;
                continue;
            }

            const abort_vid = try body.appendInst(.{
                .op = .intrinsic_op,
                .flags = .{ .has_side_effects = true, .is_synthetic = true, .is_abort_on_panic = true },
                .aux_u16 = @backingInt(MirIntrinsicKind.abort_vacated_panic),
                .type_id = .unit_ty,
                .operands = .{ .lhs = mir.NONE_U32, .rhs = mir.NONE_U32 },
            }, site_tok);

            const old_insts = body.getBlockInsts(MirBlockId.fromInt(wslice.bb_idx));
            const new_start: u32 = @intCast(body.block_insts.items.len);
            try body.block_insts.ensureUnusedCapacity(body.allocator, old_insts.len + 1);
            for (old_insts) |old_v| {
                body.block_insts.appendAssumeCapacity(old_v);
            }
            body.block_insts.appendAssumeCapacity(abort_vid);
            body.blocks.items[wslice.bb_idx].inst_start = new_start;
            body.blocks.items[wslice.bb_idx].inst_len = @intCast(old_insts.len + 1);
            has_inserted_in_trap = true;
        }
    }

    if (!has_inserted_in_trap) {
        const abort_vid = try body.appendInst(.{
            .op = .intrinsic_op,
            .flags = .{ .has_side_effects = true, .is_synthetic = true, .is_abort_on_panic = true },
            .aux_u16 = @backingInt(MirIntrinsicKind.abort_vacated_panic),
            .type_id = .unit_ty,
            .operands = .{ .lhs = mir.NONE_U32, .rhs = mir.NONE_U32 },
        }, site_tok);
        const inst_start: u32 = @intCast(body.block_insts.items.len);
        try body.block_insts.append(body.allocator, abort_vid);
        try body.blocks.append(body.allocator, .{
            .param_start = @intCast(body.block_params.items.len),
            .inst_start = inst_start,
            .inst_len = 1,
            .pred_start = @intCast(body.pred_edges.items.len),
            .pred_len = 0,
            .meta_bits = (1 << 14) | (1 << 15),
            .terminator = .{
                .kind = .trap,
                .aux_u8 = @backingInt(mir.MirTrapReason.assertion_failed) | mir.TRAP_ABORT_ON_PANIC_FLAG,
                .edge_len = 0,
                .cond_or_val = mir.NONE_U32,
                .edge_start = @intCast(body.extra_edges.items.len),
            },
        });
    }
}

/// Runs `MirVerifier` (`V1`–`V6`) on an SAST-elaborated `MirBody`, tolerating NLL-relaxed Ghost spans.
fn verifyElaboratedMirBody(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) !void {
    if (body.has_overflowed_limits) return;
    if (!body.symbol_index.isNone() and body.symbol_index.asInt() < sym_table.symbols.items.len) {
        const fn_sym = sym_table.getSymbol(body.symbol_index).*;
        if (!fn_sym.type_id.isError() and pool.getFlags(fn_sym.type_id).has_type_vars) return;
    }

    mir.verifyMirBody(allocator, body, pool, sym_table, null) catch |ver_err| switch (ver_err) {
        error.V4GhostExclusivityConflict => {
            // NLL allows a lexical `.addr_borrow` Ghost bracket to overlap a post-last-use write;
            // re-verify `V1`–`V3` and `V6` structurally with `has_ghost_instructions = false`:
            const has_saved_ghost = body.has_ghost_instructions;
            body.has_ghost_instructions = false;
            defer body.has_ghost_instructions = has_saved_ghost;
            mir.verifyMirBody(allocator, body, pool, sym_table, null) catch |inner_err| switch (inner_err) {
                error.V5ReadUninitializedOrMoved, error.V5IncompleteExitInitialization => {},
                else => return inner_err,
            };
        },
        error.V5ReadUninitializedOrMoved, error.V5IncompleteExitInitialization => {
            // `V1`–`V4` already executed before step `[5]` in `mir.verifyMirBody`; verify `V6` holds:
            if (body.is_contextless) {
                for (0..body.insts.len) |v_i| {
                    const inst = body.getInst(MirValueId.fromInt(@intCast(v_i)));
                    if (inst.op == .place_load or inst.op == .place_addr) {
                        if (inst.operands.lhs < body.places.items.len) {
                            const base = body.places.items[inst.operands.lhs].base;
                            if (base < body.locals.items.len and
                                type_system.isContextType(pool, sym_table, body.locals.items[base].type_id))
                            {
                                return error.V6ContextlessReadsContext;
                            }
                        }
                    }
                }
            }
        },
        else => return ver_err,
    };
}

/// Runs Pass 3 across all `bodies` in bottom-up Tarjan SCC order, populating `FnSummaryStore` & `PackageCapSummary`.
fn runPass3SummaryContractsAndSandbox(
    allocator: std.mem.Allocator,
    scratch_arena: *BumpArena,
    bodies: []MirBody,
    scc_sched: *const SccSchedule,
    pass2_outcomes: []const Pass2BodyOutcome,
    pass4_outcomes: []const Pass4BodyOutcome,
    per_body_edges: []std.ArrayListUnmanaged(WitnessCallEdge),
    summaries: []FnRegionSummary,
    key_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    sym_to_slot: *const std.AutoHashMapUnmanaged(u32, u32),
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner_opt: ?*const StringInterner,
    config: SastConfig,
    out_package_caps: *PackageCapSummary,
) !FnSummaryStore {
    const fn_count = bodies.len;

    // [1] Compute body-local direct effects, `own_frame_bytes`, `forwarded_cb_mask`, and outgoing edges:
    for (bodies, 0..) |*body, slot_usize| {
        const cp = scratch_arena.checkpoint();
        defer scratch_arena.restore(cp);
        const slot_idx: u32 = @intCast(slot_usize);
        var direct_eff = EffectCapabilityMask.EMPTY;
        var contracts = summaries[slot_idx].contractsScratch();

        var sym_opt: ?SymbolRecord = null;
        if (!body.symbol_index.isNone() and body.symbol_index.asInt() < sym_table.symbols.items.len) {
            sym_opt = sym_table.getSymbol(body.symbol_index).*;
        } else if (!body.def_id.isNone()) {
            if (sym_table.def_to_symbol.get(body.def_id.asInt())) |mapped_sym| {
                sym_opt = sym_table.getSymbol(mapped_sym).*;
            }
        }

        if (sym_opt) |sym| {
            contracts.has_no_alloc = sym.contract_flags.is_no_alloc;
            contracts.has_no_panic = sym.contract_flags.is_no_panic;
            contracts.has_no_block = sym.contract_flags.is_no_block;
            contracts.has_pure_contract = sym.flags.is_comptime or sym.kind == .const_sym;
            contracts.has_max_stack_attr = sym.contract_flags.has_max_stack;
            contracts.is_std_cap_boundary = sym.contract_flags.is_std_cap_boundary;
            contracts.is_ambient_export_root = (sym.visibility == .public) or
                std.mem.eql(u8, sym.name_text, "main") or
                sym.contract_flags.is_export or
                sym.contract_flags.has_link_name or
                sym.contract_flags.has_link_section;
            if (sym.flags.is_extern or
                sym.contract_flags.is_export or
                sym.contract_flags.has_link_name or
                sym.contract_flags.has_link_section)
            {
                direct_eff.ffi = true;
                direct_eff.unsafe_op = true;
            }
        }
        if (config.is_comptime_context) {
            contracts.has_pure_contract = true;
        }

        if (pass2_outcomes[slot_usize].has_unsafe_op) {
            direct_eff.unsafe_op = true;
        }
        if (pass4_outcomes[slot_usize].has_residual_may_panic) {
            direct_eff.may_panic = true;
        }

        // Track direct `fn_addr` instructions used purely as `.call` callees in $O(1)$ via `DenseBitSet`:
        var direct_call_callee_vals = try DenseBitSet.initEmpty(scratch_arena.asAllocator(), body.insts.len);
        for (body.calls.items) |cs| {
            if ((!cs.direct_def_id.isNone() or !cs.direct_symbol.isNone()) and
                cs.callee_val.asInt() < body.insts.len)
            {
                direct_call_callee_vals.set(cs.callee_val.asInt());
            }
        }

        for (0..body.insts.len) |v_idx| {
            const inst = body.getInst(MirValueId.fromInt(@intCast(v_idx)));
            const tok = body.origin_tokens.items[v_idx];
            switch (inst.op) {
                .place_load, .place_addr => {
                    if (isContextAllocatorPlace(body, pool, sym_table, PlaceId.fromInt(inst.operands.lhs))) {
                        direct_eff.alloc = true;
                    }
                },
                .aggregate_make => {
                    const agg_k: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    if (agg_k == .str_concat and inst.operands.rhs > 0) {
                        direct_eff.alloc = true;
                    } else if (agg_k == .closure_make) {
                        var clos_node_key = inst.operands.lhs;
                        if (key_to_slot.get(inst.operands.lhs)) |clos_slot| {
                            clos_node_key = nodeKeyForBody(&bodies[clos_slot], clos_slot);
                        }
                        try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                            clos_node_key,
                            tok,
                            .{ .edge_kind = .reify_fn_addr },
                        ));
                    }
                },
                .fn_addr => {
                    if (!direct_call_callee_vals.isSet(v_idx)) {
                        var target_key: u32 = inst.operands.lhs;
                        var reify_eff: u16 = 0;
                        const fn_def = if (inst.operands.lhs != mir.NONE_U32)
                            DefId.fromInt(inst.operands.lhs)
                        else
                            DefId.NONE;
                        const fn_sym = if (inst.operands.rhs != mir.NONE_U32)
                            SymbolIndex.fromInt(inst.operands.rhs)
                        else
                            SymbolIndex.none;
                        if (target_key == mir.NONE_U32 and !fn_sym.isNone()) {
                            if (sym_to_slot.get(fn_sym.asInt())) |s_slot| {
                                target_key = nodeKeyForBody(&bodies[s_slot], s_slot);
                            }
                        }
                        if (key_to_slot.get(target_key) == null) {
                            if (try lookupCalleeSummary(
                                fn_def,
                                fn_sym,
                                summaries,
                                key_to_slot,
                                sym_to_slot,
                                config,
                            )) |ext_fn_sum| {
                                reify_eff = ext_fn_sum.inferred_effects_bits &
                                    EffectCapabilityMask.LOCKFILE_CAP_BITS;
                            } else if (!fn_sym.isNone() and fn_sym.asInt() < sym_table.symbols.items.len) {
                                const t_sym = sym_table.getSymbol(fn_sym).*;
                                if (t_sym.contract_flags.is_std_cap_boundary) {
                                    reify_eff = extractBoundaryMasksForSymbol(t_sym, body.file_id, config).emits &
                                        EffectCapabilityMask.LOCKFILE_CAP_BITS;
                                } else {
                                    reify_eff = inferExternalPrototypeEffects(t_sym).asBits() &
                                        EffectCapabilityMask.LOCKFILE_CAP_BITS;
                                }
                                if (target_key == mir.NONE_U32 and !t_sym.def_id.isNone()) {
                                    target_key = t_sym.def_id.asInt();
                                }
                            }
                        }
                        try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                            target_key,
                            tok,
                            .{
                                .edge_kind = .reify_fn_addr,
                                .edge_effects_bits = reify_eff,
                            },
                        ));
                    }
                },
                .copy_val, .unary_op => {
                    if (inst.operands.lhs < body.insts.len) {
                        if (extractDynTraitSymbol(pool, inst.type_id)) |trait_sym_idx| {
                            const src_ty = body.getInst(MirValueId.fromInt(inst.operands.lhs)).type_id;
                            if (extractDynTraitSymbol(pool, src_ty) == null) {
                                if (extractConcreteNominalSymbol(pool, src_ty)) |nom_sym_idx| {
                                    if (nom_sym_idx.asInt() < sym_table.symbols.items.len) {
                                        const nom_sym = sym_table.getSymbol(nom_sym_idx).*;
                                        if (!nom_sym.target_scope.isNone()) {
                                            for (sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                                                const mem_sym = sym_table.getSymbol(mem_idx).*;
                                                if (mem_sym.kind != .fn_sym) continue;
                                                if (sym_table.impl_method_trait.get(mem_idx.asInt()) != trait_sym_idx) continue;
                                                var vtbl_key: u32 = mem_sym.def_id.asInt();
                                                var vtbl_eff: u16 = 0;
                                                if (sym_to_slot.get(mem_idx.asInt())) |m_slot| {
                                                    vtbl_key = nodeKeyForBody(&bodies[m_slot], m_slot);
                                                }
                                                if (key_to_slot.get(vtbl_key) == null) {
                                                    if (try lookupCalleeSummary(
                                                        mem_sym.def_id,
                                                        mem_idx,
                                                        summaries,
                                                        key_to_slot,
                                                        sym_to_slot,
                                                        config,
                                                    )) |ext_vt_sum| {
                                                        vtbl_eff = ext_vt_sum.inferred_effects_bits &
                                                            EffectCapabilityMask.LOCKFILE_CAP_BITS;
                                                    } else if (mem_sym.contract_flags.is_std_cap_boundary) {
                                                        vtbl_eff = extractBoundaryMasksForSymbol(
                                                            mem_sym,
                                                            body.file_id,
                                                            config,
                                                        ).emits & EffectCapabilityMask.LOCKFILE_CAP_BITS;
                                                    } else {
                                                        vtbl_eff = inferExternalPrototypeEffects(mem_sym).asBits() &
                                                            EffectCapabilityMask.LOCKFILE_CAP_BITS;
                                                    }
                                                }
                                                try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                                                    vtbl_key,
                                                    tok,
                                                    .{
                                                        .edge_kind = .reify_vtable,
                                                        .edge_effects_bits = vtbl_eff,
                                                    },
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
                else => {},
            }
        }

        // Inspect all `.call` sites for direct, indirect, external, and `forwarded_cb_mask` edges:
        var cb_mask: u16 = 0;
        for (body.calls.items) |cs| {
            var resolved_slot: ?u32 = null;
            if (!cs.direct_def_id.isNone()) {
                resolved_slot = key_to_slot.get(cs.direct_def_id.asInt());
            }
            if (resolved_slot == null and !cs.direct_symbol.isNone()) {
                resolved_slot = sym_to_slot.get(cs.direct_symbol.asInt());
            }

            if (resolved_slot) |c_slot| {
                const callee_key = nodeKeyForBody(&bodies[c_slot], c_slot);
                try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                    callee_key,
                    cs.origin_token,
                    .{ .edge_kind = .direct_call },
                ));
            } else if (!cs.direct_def_id.isNone() or !cs.direct_symbol.isNone()) {
                // Cross-`DefId` external resolver or prototype-only/built-in symbol:
                var ext_eff = EffectCapabilityMask.EMPTY;
                var callee_key = if (!cs.direct_def_id.isNone()) cs.direct_def_id.asInt() else mir.NONE_U32;
                if (try lookupCalleeSummary(
                    cs.direct_def_id,
                    cs.direct_symbol,
                    summaries,
                    key_to_slot,
                    sym_to_slot,
                    config,
                )) |ext_sum| {
                    ext_eff = ext_sum.inferredEffects();
                    for (0..cs.args_len) |arg_i| {
                        if (arg_i < 16 and ((ext_sum.forwarded_cb_mask >> @intCast(arg_i)) & 1) != 0) {
                            const mode = body.call_arg_modes.items[cs.modes_start + arg_i];
                            const word = body.extra_args.items[cs.args_start + arg_i];
                            if (mode == .let_mode or mode == .sink_mode) {
                                if (extractPassedCallableTarget(body, pool, word)) |cb_t| {
                                    if (try lookupCalleeSummary(
                                        cb_t.def_id,
                                        cb_t.sym_idx,
                                        summaries,
                                        key_to_slot,
                                        sym_to_slot,
                                        config,
                                    )) |cb_s| {
                                        ext_eff = ext_eff.unionWith(cb_s.inferredEffects());
                                    }
                                } else if (extractFormalCallbackParamOrd(body, pool, MirValueId.fromInt(word))) |caller_cb_ord| {
                                    cb_mask |= (@as(u16, 1) << caller_cb_ord);
                                } else {
                                    ext_eff = ext_eff.unionWith(
                                        inferCallableTypeIndirectEffects(body, pool, sym_table, word),
                                    );
                                }
                            }
                        }
                    }
                } else if (!cs.direct_symbol.isNone() and cs.direct_symbol.asInt() < sym_table.symbols.items.len) {
                    const c_sym = sym_table.getSymbol(cs.direct_symbol).*;
                    if (c_sym.contract_flags.is_std_cap_boundary) {
                        ext_eff = EffectCapabilityMask.fromBits(
                            extractBoundaryMasksForSymbol(c_sym, body.file_id, config).emits,
                        );
                    } else {
                        const is_recv_arena = cs.args_len > 0 and isArenaArgPlaceOrVal(
                            body,
                            pool,
                            sym_table,
                            body.call_arg_modes.items[cs.modes_start],
                            body.extra_args.items[cs.args_start],
                        );
                        ext_eff = inferExternalPrototypeEffects(c_sym);
                        if (is_recv_arena) ext_eff.alloc = false;
                    }
                    if (!c_sym.def_id.isNone()) callee_key = c_sym.def_id.asInt();
                }
                direct_eff = direct_eff.unionWith(ext_eff);
                try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                    callee_key,
                    cs.origin_token,
                    .{
                        .edge_kind = .direct_call,
                        .edge_effects_bits = ext_eff.asBits(),
                    },
                ));
            } else {
                // Indirect `fn(…)`, closure, or `dyn Trait` call:
                const cb_ord_opt = extractFormalCallbackParamOrd(body, pool, cs.callee_val);
                if (cb_ord_opt) |cb_ord| {
                    cb_mask |= (@as(u16, 1) << cb_ord);
                }

                // Check if `callee_val` resolves to a concrete local closure in this module:
                var concrete_clos_slot: ?u32 = null;
                if (extractPassedCallableTarget(body, pool, cs.callee_val.asInt())) |ct| {
                    if (!ct.def_id.isNone()) concrete_clos_slot = key_to_slot.get(ct.def_id.asInt());
                    if (concrete_clos_slot == null and !ct.sym_idx.isNone()) {
                        concrete_clos_slot = sym_to_slot.get(ct.sym_idx.asInt());
                    }
                }

                if (concrete_clos_slot) |c_slot| {
                    try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                        nodeKeyForBody(&bodies[c_slot], c_slot),
                        cs.origin_token,
                        .{ .edge_kind = .direct_call },
                    ));
                } else {
                    const ind_eff = inferCallableTypeIndirectEffects(body, pool, sym_table, cs.callee_val.asInt());
                    var e_kind: WitnessEdgeKind = .indirect_fn_ptr;
                    if (cs.callee_val.asInt() < body.insts.len and
                        extractDynTraitSymbol(pool, body.getInst(cs.callee_val).type_id) != null)
                    {
                        e_kind = .indirect_vtable;
                    }

                    if (cb_ord_opt != null) {
                        // Formal callback parameters forward caller-supplied effects via `forwarded_cb_mask`;
                        // only taint the helper itself when the helper declares `@no_*` stronger than the callback type:
                        var cb_violation_eff = EffectCapabilityMask.EMPTY;
                        if (contracts.has_no_alloc and ind_eff.alloc) cb_violation_eff.alloc = true;
                        if (contracts.has_no_panic and ind_eff.may_panic) cb_violation_eff.may_panic = true;
                        if (contracts.has_no_block and ind_eff.hasAnyBits(EffectCapabilityMask.BLOCKING_BITS)) {
                            cb_violation_eff.blocking_sync = true;
                        }
                        if (cb_violation_eff.asBits() != 0) {
                            direct_eff = direct_eff.unionWith(cb_violation_eff);
                            try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                                mir.NONE_U32,
                                cs.origin_token,
                                .{
                                    .edge_kind = e_kind,
                                    .edge_effects_bits = cb_violation_eff.asBits(),
                                },
                            ));
                        }
                    } else {
                        direct_eff = direct_eff.unionWith(ind_eff);
                        try per_body_edges[slot_usize].append(allocator, WitnessCallEdge.init(
                            mir.NONE_U32,
                            cs.origin_token,
                            .{
                                .edge_kind = e_kind,
                                .edge_effects_bits = ind_eff.asBits(),
                            },
                        ));
                    }
                }
            }
        }

        summaries[slot_usize].own_frame_bytes = computeOwnStackFrameBytes(body, pool, sym_table);
        summaries[slot_usize].forwarded_cb_mask = cb_mask;
        summaries[slot_usize].setDirectEffects(direct_eff);
        summaries[slot_usize].setInferredEffects(direct_eff);
        summaries[slot_usize].setContractsScratch(contracts);
    }

    // [2] Propagate transitive effects, callback instantiations, `@std_cap_boundary`, & stack sizes bottom-up:
    const scc_count = scc_sched.is_recursive.len;
    for (0..scc_count) |scc_i| {
        const m_start = scc_sched.offsets[scc_i];
        const m_end = scc_sched.offsets[scc_i + 1];
        const scc_slots = scc_sched.members[m_start..m_end];
        const is_rec = scc_sched.is_recursive[scc_i];

        // Materialize `forwarded_cb_arg` edges on callers in `scc_slots` now that callees below are finalized:
        for (scc_slots) |slot_u32| {
            const body = &bodies[slot_u32];
            for (body.calls.items) |cs| {
                const callee_sum_opt = try lookupCalleeSummary(
                    cs.direct_def_id,
                    cs.direct_symbol,
                    summaries,
                    key_to_slot,
                    sym_to_slot,
                    config,
                );
                const callee_sum = callee_sum_opt orelse continue;
                if (callee_sum.forwarded_cb_mask == 0) continue;

                for (0..cs.args_len) |arg_i| {
                    if (arg_i >= 16) break;
                    if (((callee_sum.forwarded_cb_mask >> @intCast(arg_i)) & 1) == 0) continue;
                    const mode = body.call_arg_modes.items[cs.modes_start + arg_i];
                    if (mode != .let_mode and mode != .sink_mode) continue;
                    const word = body.extra_args.items[cs.args_start + arg_i];
                    if (extractPassedCallableTarget(body, pool, word)) |cb_target| {
                        var cb_slot_opt: ?u32 = null;
                        if (!cb_target.def_id.isNone()) cb_slot_opt = key_to_slot.get(cb_target.def_id.asInt());
                        if (cb_slot_opt == null and !cb_target.sym_idx.isNone()) {
                            cb_slot_opt = sym_to_slot.get(cb_target.sym_idx.asInt());
                        }
                        if (cb_slot_opt) |cb_slot| {
                            try per_body_edges[slot_u32].append(allocator, WitnessCallEdge.init(
                                nodeKeyForBody(&bodies[cb_slot], cb_slot),
                                cs.origin_token,
                                .{
                                    .edge_kind = .forwarded_cb_arg,
                                    .forwarded_arg_ordinal = @intCast(arg_i),
                                    .edge_effects_bits = summaries[cb_slot].inferred_effects_bits,
                                },
                            ));
                        } else if (try lookupCalleeSummary(
                            cb_target.def_id,
                            cb_target.sym_idx,
                            summaries,
                            key_to_slot,
                            sym_to_slot,
                            config,
                        )) |ext_cb_sum| {
                            try per_body_edges[slot_u32].append(allocator, WitnessCallEdge.init(
                                cb_target.def_id.asInt(),
                                cs.origin_token,
                                .{
                                    .edge_kind = .forwarded_cb_arg,
                                    .forwarded_arg_ordinal = @intCast(arg_i),
                                    .edge_effects_bits = ext_cb_sum.inferred_effects_bits,
                                },
                            ));
                        } else if (!cb_target.sym_idx.isNone() and
                            cb_target.sym_idx.asInt() < sym_table.symbols.items.len)
                        {
                            const cb_sym = sym_table.getSymbol(cb_target.sym_idx).*;
                            const cb_eff = if (cb_sym.contract_flags.is_std_cap_boundary)
                                extractBoundaryMasksForSymbol(cb_sym, body.file_id, config).emits
                            else
                                inferExternalPrototypeEffects(cb_sym).asBits();
                            try per_body_edges[slot_u32].append(allocator, WitnessCallEdge.init(
                                cb_sym.def_id.asInt(),
                                cs.origin_token,
                                .{
                                    .edge_kind = .forwarded_cb_arg,
                                    .forwarded_arg_ordinal = @intCast(arg_i),
                                    .edge_effects_bits = cb_eff,
                                },
                            ));
                        }
                    } else if (extractFormalCallbackParamOrd(body, pool, MirValueId.fromInt(word))) |caller_cb_ord| {
                        summaries[slot_u32].forwarded_cb_mask |= (@as(u16, 1) << caller_cb_ord);
                    } else {
                        const opaque_eff = inferCallableTypeIndirectEffects(body, pool, sym_table, word);
                        summaries[slot_u32].direct_effects_bits |= opaque_eff.asBits();
                        try per_body_edges[slot_u32].append(allocator, WitnessCallEdge.init(
                            mir.NONE_U32,
                            cs.origin_token,
                            .{
                                .edge_kind = .forwarded_cb_arg,
                                .forwarded_arg_ordinal = @intCast(arg_i),
                                .edge_effects_bits = opaque_eff.asBits(),
                            },
                        ));
                    }
                }
            }
        }

        // Fixed-point union across `scc_slots` (`1` pass on DAG nodes, `<= |SCC| + 1` on recursive cycles):
        var has_scc_changed = true;
        var scc_iters: usize = 0;
        while (has_scc_changed and scc_iters < scc_slots.len + 2) : (scc_iters += 1) {
            has_scc_changed = false;
            for (scc_slots) |slot_u32| {
                const body = &bodies[slot_u32];
                var raw_bits: u16 = summaries[slot_u32].direct_effects_bits;
                var max_callee_stack: u32 = 0;
                var has_unbounded_callee = is_rec or (summaries[slot_u32].forwarded_cb_mask != 0);

                for (per_body_edges[slot_u32].items) |edge| {
                    const em = edge.meta();
                    raw_bits |= em.edge_effects_bits;
                    if (em.edge_kind == .indirect_fn_ptr or em.edge_kind == .indirect_vtable) {
                        has_unbounded_callee = true;
                    }
                    if (key_to_slot.get(edge.callee_def)) |target_slot| {
                        if (em.edge_kind == .reify_fn_addr or em.edge_kind == .reify_vtable) {
                            raw_bits |= (summaries[target_slot].inferred_effects_bits &
                                EffectCapabilityMask.LOCKFILE_CAP_BITS);
                        } else {
                            raw_bits |= summaries[target_slot].inferred_effects_bits;
                            if (summaries[target_slot].max_subtree_bytes == FnRegionSummary.STACK_UNBOUNDED) {
                                has_unbounded_callee = true;
                            } else {
                                max_callee_stack = @max(max_callee_stack, summaries[target_slot].max_subtree_bytes);
                            }
                        }
                    } else if (edge.callee_def != mir.NONE_U32 and
                        em.edge_kind != .reify_fn_addr and
                        em.edge_kind != .reify_vtable)
                    {
                        if (try lookupCalleeSummary(
                            DefId.fromInt(edge.callee_def),
                            .none,
                            summaries,
                            key_to_slot,
                            sym_to_slot,
                            config,
                        )) |ext_edge_sum| {
                            if (ext_edge_sum.max_subtree_bytes == FnRegionSummary.STACK_UNBOUNDED) {
                                has_unbounded_callee = true;
                            } else {
                                max_callee_stack = @max(max_callee_stack, ext_edge_sum.max_subtree_bytes);
                            }
                        }
                    }
                }

                // Apply `@std_cap_boundary` `(raw & ~clears) | emits` firewall (`DR-17` §2.3):
                var final_bits = raw_bits;
                var cs_mask = summaries[slot_u32].contractsScratch();
                cs_mask.is_scc_recursive = is_rec;
                if (cs_mask.is_std_cap_boundary) {
                    var sym_rec_opt: ?SymbolRecord = null;
                    if (!body.symbol_index.isNone() and body.symbol_index.asInt() < sym_table.symbols.items.len) {
                        sym_rec_opt = sym_table.getSymbol(body.symbol_index).*;
                    } else if (!body.def_id.isNone()) {
                        if (sym_table.def_to_symbol.get(body.def_id.asInt())) |ms| {
                            sym_rec_opt = sym_table.getSymbol(ms).*;
                        }
                    }
                    if (sym_rec_opt) |srec| {
                        const b_masks = extractBoundaryMasksForSymbol(srec, body.file_id, config);
                        final_bits = (raw_bits & ~b_masks.clears) | b_masks.emits;
                    }
                }

                const new_subtree: u32 = if (has_unbounded_callee)
                    FnRegionSummary.STACK_UNBOUNDED
                else blk: {
                    const sum64: u64 = @as(u64, summaries[slot_u32].own_frame_bytes) + max_callee_stack;
                    break :blk @intCast(@min(sum64, FnRegionSummary.STACK_UNBOUNDED - 1));
                };
                cs_mask.has_async_exceeded_inline_cap = (new_subtree > FnRegionSummary.ASYNC_INLINE_CAP_BYTES);

                if (final_bits != summaries[slot_u32].inferred_effects_bits or
                    new_subtree != summaries[slot_u32].max_subtree_bytes or
                    cs_mask.asBits() != summaries[slot_u32].contracts_scratch_bits)
                {
                    summaries[slot_u32].inferred_effects_bits = final_bits;
                    summaries[slot_u32].max_subtree_bytes = new_subtree;
                    summaries[slot_u32].setContractsScratch(cs_mask);
                    has_scc_changed = true;
                }
            }
            if (!is_rec) break;
        }
    }

    // [3] Sort per-caller `WitnessCallEdge` slices deterministically & pack CSR `FnSummaryStore`:
    const out_summaries = try allocator.dupe(FnRegionSummary, summaries);
    errdefer if (out_summaries.len > 0) allocator.free(out_summaries);

    const out_defs = try allocator.alloc(DefId, fn_count);
    errdefer if (out_defs.len > 0) allocator.free(out_defs);
    const out_syms = try allocator.alloc(SymbolIndex, fn_count);
    errdefer if (out_syms.len > 0) allocator.free(out_syms);
    const out_files = try allocator.alloc(FileId, fn_count);
    errdefer if (out_files.len > 0) allocator.free(out_files);
    const out_names = try allocator.alloc(SymbolId, fn_count);
    errdefer if (out_names.len > 0) allocator.free(out_names);

    var total_edges: usize = 0;
    for (bodies, 0..) |*body, s_i| {
        out_defs[s_i] = body.def_id;
        out_syms[s_i] = body.symbol_index;
        out_files[s_i] = body.file_id;
        out_names[s_i] = body.name;
        std.mem.sort(WitnessCallEdge, per_body_edges[s_i].items, {}, struct {
            /// Orders witness edges deterministically by `(site_token ASC, callee_def ASC)`.
            fn lessThan(_: void, lhs: WitnessCallEdge, rhs: WitnessCallEdge) bool {
                if (lhs.site_token.asInt() != rhs.site_token.asInt()) {
                    return lhs.site_token.asInt() < rhs.site_token.asInt();
                }
                return lhs.callee_def < rhs.callee_def;
            }
        }.lessThan);
        total_edges += per_body_edges[s_i].items.len;
    }

    const edge_offsets = try allocator.alloc(u32, fn_count + 1);
    errdefer allocator.free(edge_offsets);
    const flat_edges = try allocator.alloc(WitnessCallEdge, total_edges);
    errdefer if (flat_edges.len > 0) allocator.free(flat_edges);

    var cursor: u32 = 0;
    for (0..fn_count) |s_i| {
        edge_offsets[s_i] = cursor;
        const row = per_body_edges[s_i].items;
        if (row.len > 0) {
            @memcpy(flat_edges[cursor .. cursor + row.len], row);
            cursor += @intCast(row.len);
        }
    }
    edge_offsets[fn_count] = cursor;

    var cloned_key_map = std.AutoHashMapUnmanaged(u32, u32){};
    errdefer cloned_key_map.deinit(allocator);
    var map_it = key_to_slot.iterator();
    while (map_it.next()) |kv| {
        try cloned_key_map.put(allocator, kv.key_ptr.*, kv.value_ptr.*);
    }

    var store = FnSummaryStore{
        .allocator = allocator,
        .summaries = out_summaries,
        .def_ids = out_defs,
        .symbol_indices = out_syms,
        .file_ids = out_files,
        .names = out_names,
        .edge_offsets = edge_offsets,
        .edges = flat_edges,
        .node_key_to_slot = cloned_key_map,
    };
    errdefer store.deinit();

    // [4] Roll up `PackageCapSummary` (`ambient_caps`, `reachable_caps`, `surface_caps`) & emit contract diags:
    var pkg_caps = PackageCapSummary{};
    for (bodies, 0..) |*body, s_usize| {
        const slot_idx: u32 = @intCast(s_usize);
        var sum = store.summaries[s_usize];
        var cs_mask = sum.contractsScratch();
        const inferred = sum.inferredEffects();
        if (body.vacated_windows.items.len > 0) {
            cs_mask.has_yield_vacated_noncopy = true;
            sum.setContractsScratch(cs_mask);
            store.summaries[s_usize] = sum;
        }
        if (config.primary_body_count) |pc| {
            if (s_usize >= pc) continue;
        }

        pkg_caps.ambient_caps = pkg_caps.ambient_caps.unionWith(inferred);
        if (cs_mask.is_ambient_export_root) {
            pkg_caps.reachable_caps = pkg_caps.reachable_caps.unionWith(inferred);
        }

        var sym_opt: ?SymbolRecord = null;
        if (!body.symbol_index.isNone() and body.symbol_index.asInt() < sym_table.symbols.items.len) {
            sym_opt = sym_table.getSymbol(body.symbol_index).*;
        } else if (!body.def_id.isNone()) {
            if (sym_table.def_to_symbol.get(body.def_id.asInt())) |ms| {
                sym_opt = sym_table.getSymbol(ms).*;
            }
        }
        if (sym_opt) |srec| {
            if (srec.visibility == .public) {
                pkg_caps.surface_caps = pkg_caps.surface_caps.unionWith(inferred);
            }
        }

        const decl_span = resolveBodyDeclSpan(body, sym_table);
        var has_emitted_e0321 = false;

        // `E0316` `@max_stack(N)` verification:
        if (cs_mask.has_max_stack_attr) {
            const budget: u32 = if (sym_opt) |sr| sr.max_stack_bytes else 0;
            if (sum.max_subtree_bytes == FnRegionSummary.STACK_UNBOUNDED or sum.max_subtree_bytes > budget) {
                const msg = if (sum.max_subtree_bytes == FnRegionSummary.STACK_UNBOUNDED)
                    try std.fmt.allocPrint(
                        allocator,
                        "function has unbounded stack usage (recursion or indirect call), exceeding `@max_stack({d})`",
                        .{budget},
                    )
                else
                    try std.fmt.allocPrint(
                        allocator,
                        "worst-case call-tree stack usage ({d} B) exceeds `@max_stack({d})` budget",
                        .{ sum.max_subtree_bytes, budget },
                    );
                defer allocator.free(msg);
                try emitSastDiag(
                    config.diagnostic_sink,
                    .e0316_max_stack_budget_exceeded,
                    .err,
                    decl_span,
                    msg,
                    "`@max_stack` budget exceeded here",
                    null,
                    null,
                    "eliminate recursion/indirect dispatch or reduce large stack locals",
                );
            }
        }

        // `E0320` `@no_alloc` verification:
        if (cs_mask.has_no_alloc and inferred.alloc) {
            const steps = try store.reconstructShortestWitness(
                allocator,
                slot_idx,
                EffectCapabilityMask.ALLOC_BIT,
            );
            defer allocator.free(steps);
            const note_opt = try formatWitnessChainNote(
                allocator,
                &store,
                sym_table,
                interner_opt,
                slot_idx,
                steps,
            );
            defer if (note_opt) |ns| allocator.free(ns);
            const prim_span = if (steps.len > 0)
                resolveTokenSpan(body.file_id, steps[0].edge.site_token, config, decl_span)
            else
                decl_span;
            try emitSastDiag(
                config.diagnostic_sink,
                .e0320_no_alloc_contract_violation,
                .err,
                prim_span,
                "`@no_alloc` function performs or transitively reaches dynamic heap allocation",
                "heap allocation reachable from `@no_alloc` body",
                if (steps.len > 0) .{ .span = decl_span, .label = "`@no_alloc` contract declared here", .style = .secondary } else null,
                null,
                note_opt orelse "use a caller-provided `BumpArena` or `Context.scratch` instead of `Context.allocator`",
            );
        }

        // `E0321` `@no_panic` verification:
        if (cs_mask.has_no_panic and inferred.may_panic) {
            const steps = try store.reconstructShortestWitness(
                allocator,
                slot_idx,
                EffectCapabilityMask.MAY_PANIC_BIT,
            );
            defer allocator.free(steps);
            const note_opt = try formatWitnessChainNote(
                allocator,
                &store,
                sym_table,
                interner_opt,
                slot_idx,
                steps,
            );
            defer if (note_opt) |ns| allocator.free(ns);
            const prim_span = if (steps.len > 0)
                resolveTokenSpan(body.file_id, steps[0].edge.site_token, config, decl_span)
            else
                decl_span;
            try emitSastDiag(
                config.diagnostic_sink,
                .e0321_no_panic_contract_violation,
                .err,
                prim_span,
                "`@no_panic` function contains an uneliminated trap, bounds check, or panicking call",
                "potential panic path in `@no_panic` function",
                if (steps.len > 0) .{ .span = decl_span, .label = "`@no_panic` contract declared here", .style = .secondary } else null,
                null,
                note_opt orelse "prove bounds/overflow checks statically or use wrapping/checked `Result` APIs",
            );
            has_emitted_e0321 = true;
        }

        // `E0322` `@no_block` verification:
        if (cs_mask.has_no_block and inferred.hasAnyBits(EffectCapabilityMask.BLOCKING_BITS)) {
            const steps = try store.reconstructShortestWitness(
                allocator,
                slot_idx,
                EffectCapabilityMask.BLOCKING_BITS,
            );
            defer allocator.free(steps);
            const note_opt = try formatWitnessChainNote(
                allocator,
                &store,
                sym_table,
                interner_opt,
                slot_idx,
                steps,
            );
            defer if (note_opt) |ns| allocator.free(ns);
            const prim_span = if (steps.len > 0)
                resolveTokenSpan(body.file_id, steps[0].edge.site_token, config, decl_span)
            else
                decl_span;
            try emitSastDiag(
                config.diagnostic_sink,
                .e0322_no_block_contract_violation,
                .err,
                prim_span,
                "`@no_block` function performs or reaches blocking I/O, process, or synchronization operations",
                "blocking operation reachable from `@no_block` body",
                if (steps.len > 0) .{ .span = decl_span, .label = "`@no_block` contract declared here", .style = .secondary } else null,
                null,
                note_opt orelse "move blocking operations off the non-blocking path",
            );
        }

        // `E0323` Trait `impl` method body effect escalation against trait method contracts:
        if (sym_opt) |srec| {
            var method_sym_idx = body.symbol_index;
            if (method_sym_idx.isNone() and !body.def_id.isNone()) {
                method_sym_idx = sym_table.def_to_symbol.get(body.def_id.asInt()) orelse .none;
            }
            if (!method_sym_idx.isNone()) {
                if (sym_table.impl_method_trait.get(method_sym_idx.asInt())) |trait_sym_idx| {
                    if (!trait_sym_idx.isNone() and trait_sym_idx.asInt() < sym_table.symbols.items.len) {
                        const cand_trait = sym_table.getSymbol(trait_sym_idx).*;
                        if (cand_trait.kind == .trait_sym and !cand_trait.target_scope.isNone()) {
                            for (sym_table.getScopeMembers(cand_trait.target_scope)) |t_mem_idx| {
                                const t_mem = sym_table.getSymbol(t_mem_idx).*;
                                if (t_mem.kind != .fn_sym or t_mem.name != srec.name) continue;
                                const is_violating_trait = (t_mem.contract_flags.is_no_alloc and inferred.alloc) or
                                    (t_mem.contract_flags.is_no_panic and inferred.may_panic) or
                                    (t_mem.contract_flags.is_no_block and inferred.hasAnyBits(EffectCapabilityMask.BLOCKING_BITS));
                                if (is_violating_trait and !hasExistingDiagAtSpan(
                                    config.diagnostic_sink,
                                    .e0323_trait_impl_effect_escalation,
                                    decl_span,
                                )) {
                                    try emitSastDiag(
                                        config.diagnostic_sink,
                                        .e0323_trait_impl_effect_escalation,
                                        .err,
                                        decl_span,
                                        "`impl` method body violates effect contract declared on trait method",
                                        "`impl` method escalates trait effect contract",
                                        .{
                                            .span = t_mem.decl_span,
                                            .label = "trait method contract defined here",
                                            .style = .secondary,
                                        },
                                        null,
                                        "remove the forbidden allocation/panic/blocking effect from the `impl` body",
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        // `Fix-06B` Vacated non-`Copy` `inout` `subscript` window check (`W0329` / `E0321` + `abort_vacated_panic`):
        if (body.vacated_windows.items.len > 0) {
            for (body.vacated_windows.items) |win| {
                const win_slices = try collectVacatedWindowSlices(allocator, body, win);
                defer allocator.free(win_slices);

                var has_window_panic = false;
                for (win_slices) |wslice| {
                    if (wslice.bb_idx >= body.blocks.items.len) continue;
                    const cur_insts = body.getBlockInsts(MirBlockId.fromInt(wslice.bb_idx));
                    const is_block_flagged = wslice.bb_idx < pass4_outcomes[s_usize].block_may_panic.len and
                        pass4_outcomes[s_usize].block_may_panic[wslice.bb_idx];
                    if (is_block_flagged) {
                        if (wslice.inst_lo == 0 and wslice.inst_hi >= cur_insts.len and wslice.has_terminator) {
                            has_window_panic = true;
                            break;
                        }
                        const hi = @min(wslice.inst_hi, cur_insts.len);
                        const lo = @min(wslice.inst_lo, hi);
                        for (cur_insts[lo..hi]) |iv| {
                            const inst = body.getInst(iv);
                            if (inst.flags.has_trap_risk) {
                                has_window_panic = true;
                                break;
                            }
                            if (inst.op == .intrinsic_op) {
                                const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                                switch (ikind) {
                                    .bounds_check,
                                    .slice_range_check,
                                    .narrow_check,
                                    .compile_assert,
                                    .compile_error,
                                    .abort_vacated_panic,
                                    => {
                                        has_window_panic = true;
                                        break;
                                    },
                                    else => {},
                                }
                            }
                        }
                        if (has_window_panic) break;
                    }

                    if (!wslice.has_terminator) continue;
                    const b_term = body.blocks.items[wslice.bb_idx].terminator;
                    if (b_term.kind == .trap) {
                        has_window_panic = true;
                        break;
                    }
                    if (b_term.kind == .call and b_term.cond_or_val < body.calls.items.len) {
                        const cs = body.calls.items[b_term.cond_or_val];
                        if (try lookupCalleeSummary(
                            cs.direct_def_id,
                            cs.direct_symbol,
                            store.summaries,
                            key_to_slot,
                            sym_to_slot,
                            config,
                        )) |c_sum| {
                            if (c_sum.inferredEffects().may_panic) {
                                has_window_panic = true;
                                break;
                            }
                        } else if (!cs.direct_symbol.isNone() and
                            cs.direct_symbol.asInt() < sym_table.symbols.items.len)
                        {
                            const c_sym = sym_table.getSymbol(cs.direct_symbol).*;
                            const c_eff = if (c_sym.contract_flags.is_std_cap_boundary)
                                EffectCapabilityMask.fromBits(
                                    extractBoundaryMasksForSymbol(c_sym, body.file_id, config).emits,
                                )
                            else
                                inferExternalPrototypeEffects(c_sym);
                            if (c_eff.may_panic) {
                                has_window_panic = true;
                                break;
                            }
                        } else if (inferCallableTypeIndirectEffects(
                            body,
                            pool,
                            sym_table,
                            cs.callee_val.asInt(),
                        ).may_panic) {
                            has_window_panic = true;
                            break;
                        }
                    }
                }

                if (has_window_panic) {
                    const site_span = resolveTokenSpan(body.file_id, win.site_token, config, decl_span);
                    if (cs_mask.has_no_panic) {
                        if (!has_emitted_e0321) {
                            try emitSastDiag(
                                config.diagnostic_sink,
                                .e0321_no_panic_contract_violation,
                                .err,
                                site_span,
                                "potentially panicking operation inside vacated non-`Copy` `inout` `subscript` in `@no_panic` fn",
                                "panic inside vacated `inout` `subscript` window",
                                null,
                                null,
                                "prove inner operations panic-free before mutating through a non-`Copy` `subscript`",
                            );
                            has_emitted_e0321 = true;
                        }
                    } else {
                        try insertVacatedPanicAbortGuard(body, win_slices, win.site_token);
                        try emitSastDiag(
                            config.diagnostic_sink,
                            .w0329_vacated_projection_panic_abort,
                            .warning,
                            site_span,
                            "potential panic inside vacated non-`Copy` `inout` `subscript` window inserts immediate abort guard",
                            "`abort_vacated_panic` guard inserted for this `subscript` window",
                            null,
                            null,
                            "extract fallible/panicking computations before opening the `inout` `subscript` projection",
                        );
                    }
                }
            }
        }

        // `Fix-17` Gate F: Hermetic `comptime` capability check (`E0325`):
        if (cs_mask.has_pure_contract) {
            const forbidden_ct = inferred.asBits() & EffectCapabilityMask.LOCKFILE_CAP_BITS;
            if (forbidden_ct != 0) {
                const steps = try store.reconstructShortestWitness(allocator, slot_idx, forbidden_ct);
                defer allocator.free(steps);
                const note_opt = try formatWitnessChainNote(
                    allocator,
                    &store,
                    sym_table,
                    interner_opt,
                    slot_idx,
                    steps,
                );
                defer if (note_opt) |ns| allocator.free(ns);
                const cap_str = try formatEffectBitsList(allocator, forbidden_ct);
                defer allocator.free(cap_str);
                const msg = try std.fmt.allocPrint(
                    allocator,
                    "hermetic `comptime` item reaches forbidden host capability `{s}`",
                    .{cap_str},
                );
                defer allocator.free(msg);
                const prim_span = if (steps.len > 0)
                    resolveTokenSpan(body.file_id, steps[0].edge.site_token, config, decl_span)
                else
                    decl_span;
                try emitSastDiag(
                    config.diagnostic_sink,
                    .e0325_comptime_sandbox_violation,
                    .err,
                    prim_span,
                    msg,
                    "non-hermetic capability reachable during compile-time evaluation",
                    null,
                    null,
                    note_opt orelse "remove `fs`, `net`, `env`, `process`, `ffi`, `unsafe`, `clock`, and `entropy` from `comptime`",
                );
            }
        }

        // [5] Post-SAST `MirVerifier` (`V1`–`V6`) structural verification on clean bodies:
        if (pass2_outcomes[s_usize].emitted_error_count == 0 and
            pass4_outcomes[s_usize].emitted_error_count == 0)
        {
            try verifyElaboratedMirBody(allocator, body, pool, sym_table);
        }
    }

    // Clamp caller-observable contract bits on exported summaries for `CompilerDb` Early Cutoff (`DR-17` §2.2):
    for (store.summaries) |*sum_entry| {
        const cs_mask = sum_entry.contractsScratch();
        if (cs_mask.has_no_alloc) sum_entry.inferred_effects_bits &= ~EffectCapabilityMask.ALLOC_BIT;
        if (cs_mask.has_no_panic) sum_entry.inferred_effects_bits &= ~EffectCapabilityMask.MAY_PANIC_BIT;
        if (cs_mask.has_no_block) sum_entry.inferred_effects_bits &= ~EffectCapabilityMask.BLOCKING_BITS;
    }

    out_package_caps.* = pkg_caps;
    if (config.package_policy) |policy| {
        try verifyPackageCapPolicy(allocator, pkg_caps, policy, config.diagnostic_sink);
    }

    return store;
}

/// Returns `true` if `sink_opt` already contains a diagnostic with `code` and `span`.
fn hasExistingDiagAtSpan(sink_opt: ?*const DiagnosticSink, code: DiagnosticCode, span: Span) bool {
    const sink = sink_opt orelse return false;
    for (sink.diagnostics.items) |item| {
        if (item.code == code and item.primary_span.file_id == span.file_id and
            item.primary_span.start_byte == span.start_byte)
        {
            return true;
        }
    }
    return false;
}

/// Lowers top-level `hir_const_decl` initializers in `source_store` into zero-arg `MirBody`s for Gate F (`E0325`).
fn appendConstInitializerMirBodiesForSast(
    allocator: std.mem.Allocator,
    source_store: *const hir.HirStore,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    interner: *const StringInterner,
    diagnostic_sink: ?*DiagnosticSink,
    out_bodies: *std.ArrayListUnmanaged(MirBody),
) !void {
    var node_idx: usize = 0;
    while (node_idx < source_store.nodes.len) : (node_idx += 1) {
        const decl_node = source_store.nodes.get(node_idx);
        if (decl_node.tag != .hir_const_decl) continue;
        const init_hir = hir.HirIndex.fromInt(decl_node.data.rhs);
        if (init_hir.isNone() or init_hir.asInt() >= source_store.nodes.len) continue;
        if (source_store.getNode(init_hir).tag == .hir_const_val) continue;

        var const_def: DefId = .NONE;
        var const_sym_idx: SymbolIndex = .none;
        if (sym_table.def_to_symbol.get(decl_node.data.lhs)) |mapped_sym| {
            const_def = DefId.fromInt(decl_node.data.lhs);
            const_sym_idx = mapped_sym;
        } else if (decl_node.data.lhs < sym_table.symbols.items.len and
            sym_table.getSymbol(SymbolIndex.fromInt(decl_node.data.lhs)).kind == .const_sym)
        {
            const_sym_idx = SymbolIndex.fromInt(decl_node.data.lhs);
            const_def = sym_table.getSymbol(const_sym_idx).def_id;
        }
        if (const_sym_idx.isNone()) continue;

        var temp_store = hir.HirStore.init(allocator, source_store.file_id);
        temp_store.target_layout = source_store.target_layout;
        defer temp_store.deinit();

        try temp_store.nodes.ensureTotalCapacity(allocator, source_store.nodes.len);
        var copy_i: usize = 0;
        while (copy_i < source_store.nodes.len) : (copy_i += 1) {
            temp_store.nodes.appendAssumeCapacity(source_store.nodes.get(copy_i));
        }
        try temp_store.origin_ast.appendSlice(allocator, source_store.origin_ast.items);
        try temp_store.extra_data.appendSlice(allocator, source_store.extra_data.items);
        try temp_store.patterns.appendSlice(allocator, source_store.patterns.items);
        try temp_store.match_arms.appendSlice(allocator, source_store.match_arms.items);
        try temp_store.functions.appendSlice(allocator, source_store.functions.items);
        try temp_store.const_pool.appendSlice(allocator, source_store.const_pool.items);
        try temp_store.const_elements.appendSlice(allocator, source_store.const_elements.items);

        // Slot `0` is `_return_slot`; collect only locals declared inside `init_hir` so other functions don't leak:
        try temp_store.locals.append(allocator, .{
            .name = .empty,
            .type_id = decl_node.type_id,
            .decl_span = sym_table.getSymbol(const_sym_idx).decl_span,
            .mode = .let_mode,
            .is_mut = true,
            .is_temp = true,
        });

        var local_remap = std.AutoHashMapUnmanaged(u32, u32){};
        defer local_remap.deinit(allocator);

        var visit_stack: std.ArrayListUnmanaged(u32) = .empty;
        defer visit_stack.deinit(allocator);
        try visit_stack.append(allocator, init_hir.asInt());

        const is_visited_node = try allocator.alloc(bool, temp_store.nodes.len);
        defer allocator.free(is_visited_node);
        @memset(is_visited_node, false);

        while (visit_stack.items.len > 0) {
            const cur_raw = visit_stack.pop().?;
            if (cur_raw >= temp_store.nodes.len or is_visited_node[cur_raw]) continue;
            is_visited_node[cur_raw] = true;
            var cur_node = temp_store.nodes.get(cur_raw);

            switch (cur_node.tag) {
                .hir_local_decl => {
                    const old_slot = cur_node.data.lhs;
                    const gop = try local_remap.getOrPut(allocator, old_slot);
                    if (!gop.found_existing) {
                        const new_slot: u32 = @intCast(temp_store.locals.items.len);
                        gop.value_ptr.* = new_slot;
                        if (old_slot < source_store.locals.items.len) {
                            var cloned_loc = source_store.locals.items[old_slot];
                            cloned_loc.is_param = false;
                            try temp_store.locals.append(allocator, cloned_loc);
                        }
                    }
                    cur_node.data.lhs = gop.value_ptr.*;
                    temp_store.nodes.set(cur_raw, cur_node);
                    if (cur_node.data.rhs != mir.NONE_U32) {
                        try visit_stack.append(allocator, cur_node.data.rhs);
                    }
                },
                .hir_var_ref => {
                    if (local_remap.get(cur_node.data.lhs)) |mapped_slot| {
                        cur_node.data.lhs = mapped_slot;
                        temp_store.nodes.set(cur_raw, cur_node);
                    }
                },
                .hir_block => {
                    if (cur_node.data.rhs != mir.NONE_U32) {
                        try visit_stack.append(allocator, cur_node.data.rhs);
                    }
                    if (cur_node.data.lhs < temp_store.extra_data.items.len) {
                        const stmt_len = temp_store.extra_data.items[cur_node.data.lhs];
                        const stmt_start = cur_node.data.lhs + 1;
                        const safe_end = @min(stmt_start + stmt_len, temp_store.extra_data.items.len);
                        var rev_i = safe_end;
                        while (rev_i > stmt_start) {
                            rev_i -= 1;
                            try visit_stack.append(allocator, temp_store.extra_data.items[rev_i]);
                        }
                    }
                },
                .hir_call => {
                    try visit_stack.append(allocator, cur_node.data.lhs);
                    if (cur_node.data.rhs + 1 <= temp_store.extra_data.items.len) {
                        const arg_len = temp_store.extra_data.items[cur_node.data.rhs];
                        const arg_start = cur_node.data.rhs + 1;
                        const safe_end = @min(arg_start + arg_len, temp_store.extra_data.items.len);
                        var arg_i = arg_start;
                        while (arg_i < safe_end) : (arg_i += 1) {
                            try visit_stack.append(allocator, temp_store.extra_data.items[arg_i]);
                        }
                    }
                },
                .hir_if => {
                    try visit_stack.append(allocator, cur_node.data.lhs);
                    if (cur_node.data.rhs + 2 <= temp_store.extra_data.items.len) {
                        try visit_stack.append(allocator, temp_store.extra_data.items[cur_node.data.rhs]);
                        try visit_stack.append(allocator, temp_store.extra_data.items[cur_node.data.rhs + 1]);
                    }
                },
                .hir_unary_op, .hir_project_arg, .hir_defer => {
                    try visit_stack.append(allocator, cur_node.data.rhs);
                },
                .hir_cast, .hir_field_proj, .hir_loop, .hir_return, .hir_yield => {
                    if (cur_node.data.lhs != mir.NONE_U32) {
                        try visit_stack.append(allocator, cur_node.data.lhs);
                    }
                },
                .hir_binary_op => {
                    if (cur_node.data.lhs + 2 <= temp_store.extra_data.items.len) {
                        try visit_stack.append(allocator, temp_store.extra_data.items[cur_node.data.lhs]);
                        try visit_stack.append(allocator, temp_store.extra_data.items[cur_node.data.lhs + 1]);
                    }
                },
                .hir_assign, .hir_index_proj => {
                    try visit_stack.append(allocator, cur_node.data.lhs);
                    try visit_stack.append(allocator, cur_node.data.rhs);
                },
                else => {},
            }
        }

        const wrapper_fn_ty = try pool.internFn(.fn_ty, &.{}, &.{}, decl_node.type_id, false);
        const const_sym = sym_table.getSymbol(const_sym_idx).*;
        const fn_meta = hir.HirFnMeta{
            .def_id = const_def,
            .symbol_index = const_sym_idx,
            .name = const_sym.name,
            .fn_ty = wrapper_fn_ty,
            .ret_ty = decl_node.type_id,
            .return_local_id = 0,
            .param_local_start = 1,
            .param_len = 0,
            .total_local_len = @intCast(temp_store.locals.items.len),
            .body_hir = init_hir,
            .is_comptime = true,
        };
        var init_body = try mir.lowerHirFnToMirForSast(
            allocator,
            &temp_store,
            fn_meta,
            pool,
            sym_table,
            interner,
            diagnostic_sink,
        );
        errdefer init_body.deinit();
        try out_bodies.append(allocator, init_body);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Verifies `PackageCapSummary` against `PackageCapPolicy` (`Fix-17` Gate E: `E0324` & `W0330`).
pub fn verifyPackageCapPolicy(
    allocator: std.mem.Allocator,
    pkg_caps: PackageCapSummary,
    policy: PackageCapPolicy,
    diagnostic_sink: ?*DiagnosticSink,
) !void {
    const active_caps = switch (policy.enforcement_scope) {
        .surface => pkg_caps.surface_caps,
        .all => pkg_caps.reachable_caps,
    };
    const unauthorized_bits = (active_caps.asBits() & ~policy.allowed_caps.asBits()) &
        EffectCapabilityMask.LOCKFILE_CAP_BITS;
    if (unauthorized_bits != 0) {
        const cap_names = try formatEffectBitsList(allocator, unauthorized_bits);
        defer allocator.free(cap_names);
        const msg = try std.fmt.allocPrint(
            allocator,
            "package `{s}` reaches unauthorized capability `{s}` not granted in `corex.toml` / `corex.lock`",
            .{ policy.package_name, cap_names },
        );
        defer allocator.free(msg);
        try emitSastDiag(
            diagnostic_sink,
            .e0324_package_capability_violation,
            .err,
            policy.policy_span,
            msg,
            "unauthorized capability reachable from package export/entry root",
            null,
            null,
            "grant the capability in `[dependencies]` policy or remove the offending call chain",
        );
    }

    if (policy.is_third_party_dependency) {
        const dead_ffi_unsafe = (pkg_caps.ambient_caps.asBits() & ~pkg_caps.reachable_caps.asBits()) &
            EffectCapabilityMask.FFI_UNSAFE_BITS & ~policy.allowed_caps.asBits();
        if (dead_ffi_unsafe != 0) {
            const cap_names = try formatEffectBitsList(allocator, dead_ffi_unsafe);
            defer allocator.free(cap_names);
            const msg = try std.fmt.allocPrint(
                allocator,
                "dependency `{s}` contains unreachable ambient `{s}` code outside exported call graph",
                .{ policy.package_name, cap_names },
            );
            defer allocator.free(msg);
            try emitSastDiag(
                diagnostic_sink,
                .w0330_ambient_dead_capability_in_dep,
                .warning,
                policy.policy_span,
                msg,
                "dead `ffi` / `unsafe` capability present in dependency source",
                null,
                null,
                "audit unreachable `extern`/`unsafe` items in this third-party dependency",
            );
        }
    }
}

/// Runs the complete Phase 6 SAST & Elaboration pipeline (`Pass 1`, `Pass 2`, `Pass 4`, `Pass 3`) in-place on `bodies`.
pub fn analyzeAndElaborateMirModule(
    allocator: std.mem.Allocator,
    bodies: []MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner_opt: ?*const StringInterner,
    config: SastConfig,
) !MirSastResult {
    const fn_count = bodies.len;
    if (fn_count == 0) {
        const empty_offsets = try allocator.alloc(u32, 1);
        empty_offsets[0] = 0;
        var res = MirSastResult{
            .summary_store = .{
                .allocator = allocator,
                .edge_offsets = empty_offsets,
            },
        };
        errdefer res.deinit();
        if (config.package_policy) |policy| {
            try verifyPackageCapPolicy(allocator, res.package_caps, policy, config.diagnostic_sink);
        }
        return res;
    }

    // [1] Build $O(1)$ `(node_key -> slot)` and `(SymbolIndex -> slot)` maps:
    var key_to_slot = std.AutoHashMapUnmanaged(u32, u32){};
    defer key_to_slot.deinit(allocator);
    var sym_to_slot = std.AutoHashMapUnmanaged(u32, u32){};
    defer sym_to_slot.deinit(allocator);

    for (bodies, 0..) |*body, s_i| {
        const slot_u32: u32 = @intCast(s_i);
        try key_to_slot.put(allocator, nodeKeyForBody(body, slot_u32), slot_u32);
        if (!body.symbol_index.isNone()) {
            try sym_to_slot.put(allocator, body.symbol_index.asInt(), slot_u32);
        } else if (!body.def_id.isNone()) {
            if (sym_table.def_to_symbol.get(body.def_id.asInt())) |mapped_sym| {
                try sym_to_slot.put(allocator, mapped_sym.asInt(), slot_u32);
            }
        }
    }

    // [2] Compute Cooper-Harvey-Kennedy dominator trees & bottom-up Tarjan SCC schedule:
    var dom_trees = try allocator.alloc(DominatorTree, fn_count);
    var dom_init_count: usize = 0;
    defer {
        for (dom_trees[0..dom_init_count]) |*dt| dt.deinit();
        allocator.free(dom_trees);
    }
    for (bodies, 0..) |*body, s_i| {
        dom_trees[s_i] = try mir.computeDominators(allocator, body);
        dom_init_count += 1;
    }

    // Reusable per-function `BumpArena` reclaimed in $O(1)$ after each stage (`AGENTS.md` §2):
    var scratch_arena = BumpArena.init(allocator);
    defer scratch_arena.deinit();

    var scc_sched = try computeBottomUpTarjanSccs(
        allocator,
        &scratch_arena,
        bodies,
        pool,
        sym_table,
        &key_to_slot,
        &sym_to_slot,
    );
    defer scc_sched.deinit(allocator);

    const summaries = try allocator.alloc(FnRegionSummary, fn_count);
    defer allocator.free(summaries);
    @memset(summaries, .{});

    const pass2_outcomes = try allocator.alloc(Pass2BodyOutcome, fn_count);
    defer allocator.free(pass2_outcomes);
    @memset(pass2_outcomes, .{});

    const pass4_outcomes = try allocator.alloc(Pass4BodyOutcome, fn_count);
    @memset(pass4_outcomes, .{});
    defer {
        for (pass4_outcomes) |p4| {
            if (p4.block_may_panic.len > 0) allocator.free(p4.block_may_panic);
        }
        allocator.free(pass4_outcomes);
    }

    const per_body_edges = try allocator.alloc(std.ArrayListUnmanaged(WitnessCallEdge), fn_count);
    for (per_body_edges) |*el| el.* = .empty;
    defer {
        for (per_body_edges) |*el| el.deinit(allocator);
        allocator.free(per_body_edges);
    }

    var total_elim_bce: u32 = 0;
    var total_elim_narrow: u32 = 0;
    var total_emitted_drops: u32 = 0;
    var max_pentagon_bytes: usize = 0;

    // [3] Bottom-up SCC execution: Recursive Pre-Pass -> Pass 1 -> Horizon -> Pass 2 -> Pass 4:
    const primary_limit = config.primary_body_count orelse fn_count;
    for (0..scc_sched.is_recursive.len) |scc_i| {
        const m_start = scc_sched.offsets[scc_i];
        const m_end = scc_sched.offsets[scc_i + 1];
        const scc_slots = scc_sched.members[m_start..m_end];

        if (scc_sched.is_recursive[scc_i]) {
            try convergeRecursiveSccSummaries(
                &scratch_arena,
                bodies,
                dom_trees,
                scc_slots,
                pool,
                sym_table,
                summaries,
                &key_to_slot,
                &sym_to_slot,
                config,
            );
        }

        for (scc_slots) |slot_u32| {
            const cp = scratch_arena.checkpoint();
            defer scratch_arena.restore(cp);
            const arena_alloc = scratch_arena.asAllocator();
            const is_primary_slot = slot_u32 < primary_limit;
            var body_cfg = config;
            if (!is_primary_slot) body_cfg.diagnostic_sink = null;

            const body = &bodies[slot_u32];
            const trie = try buildMovePathTrie(arena_alloc, body, pool, sym_table);
            const horizon = try computeBodyProvenanceAndNllHorizon(
                arena_alloc,
                body,
                &dom_trees[slot_u32],
                &trie,
                pool,
                sym_table,
                summaries,
                &key_to_slot,
                &sym_to_slot,
                body_cfg,
            );

            pass2_outcomes[slot_u32] = try runPass2TypestateNllAndDrops(
                arena_alloc,
                allocator,
                body,
                &dom_trees[slot_u32],
                &trie,
                &horizon,
                pool,
                sym_table,
                interner_opt,
                summaries,
                slot_u32,
                &key_to_slot,
                &sym_to_slot,
                &per_body_edges[slot_u32],
                body_cfg,
            );
            if (is_primary_slot) {
                total_emitted_drops += pass2_outcomes[slot_u32].emitted_drops;
            }

            var has_no_panic_attr = false;
            if (!body.symbol_index.isNone() and body.symbol_index.asInt() < sym_table.symbols.items.len) {
                has_no_panic_attr = sym_table.getSymbol(body.symbol_index).contract_flags.is_no_panic;
            } else if (!body.def_id.isNone()) {
                if (sym_table.def_to_symbol.get(body.def_id.asInt())) |ms| {
                    has_no_panic_attr = sym_table.getSymbol(ms).contract_flags.is_no_panic;
                }
            }

            // Recompute dominators if `ElaborateDrops` altered blocks (`Fix-06B` runs in Pass 3):
            pass4_outcomes[slot_u32] = try runPass4IntervalsAndPentagonBce(
                arena_alloc,
                allocator,
                body,
                &dom_trees[slot_u32],
                pool,
                sym_table,
                has_no_panic_attr,
                body_cfg,
            );
            if (is_primary_slot) {
                total_elim_bce += pass4_outcomes[slot_u32].eliminated_bounds_checks;
                total_elim_narrow += pass4_outcomes[slot_u32].eliminated_narrow_checks;
                max_pentagon_bytes = @max(max_pentagon_bytes, pass4_outcomes[slot_u32].peak_pentagon_bytes);
            }
        }
    }

    // [4] Pass 3: Bottom-up effect/stack/sandbox roll-up, witness CSR, `Fix-06B`, and `V1`–`V6`:
    var pkg_caps = PackageCapSummary{};
    const store = try runPass3SummaryContractsAndSandbox(
        allocator,
        &scratch_arena,
        bodies,
        &scc_sched,
        pass2_outcomes,
        pass4_outcomes,
        per_body_edges,
        summaries,
        &key_to_slot,
        &sym_to_slot,
        pool,
        sym_table,
        interner_opt,
        config,
        &pkg_caps,
    );

    return .{
        .summary_store = store,
        .package_caps = pkg_caps,
        .peak_pentagon_bytes = max_pentagon_bytes,
        .eliminated_bounds_checks = total_elim_bce,
        .eliminated_narrow_checks = total_elim_narrow,
        .emitted_drops = total_emitted_drops,
    };
}

/// Convenience single-body Phase 6 SAST & Elaboration entrypoint (used by `CompilerDb` Stage 9).
pub fn analyzeSingleMirBody(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    interner_opt: ?*const StringInterner,
    config: SastConfig,
) !MirSastResult {
    return analyzeAndElaborateMirModule(
        allocator,
        body[0..1],
        pool,
        sym_table,
        interner_opt,
        config,
    );
}

/// Parses, resolves, type-checks, lowers to `HIR` + `MIR`, and executes Phase 6 `mir_sast` end-to-end.
pub fn lowerAndVerifySourceMirSast(
    allocator: std.mem.Allocator,
    file_id: FileId,
    source: []const u8,
    target_layout: TargetLayout,
    sast_config: SastConfig,
) !MirSastPipelineBundle {
    var is_moved = false;
    var interner = try StringInterner.init(allocator);
    errdefer if (!is_moved) interner.deinit();
    var diagnostics = DiagnosticSink.init(allocator);
    errdefer if (!is_moved) diagnostics.deinit();
    var token_buffer = TokenBuffer.init(allocator);
    errdefer if (!is_moved) token_buffer.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    errdefer if (!is_moved) cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    errdefer if (!is_moved) ast_arena.deinit();

    const active_sink: *DiagnosticSink = sast_config.diagnostic_sink orelse &diagnostics;

    _ = try parser.parseSource(
        source,
        file_id,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        active_sink,
        &interner,
    );

    var sym_table = try SymbolTable.init(allocator, &interner);
    errdefer if (!is_moved) sym_table.deinit();
    _ = try symbol_resolver.collectFileModuleItems(
        &sym_table,
        &interner,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        active_sink,
    );
    try symbol_resolver.resolveFileUseImports(
        &sym_table,
        &interner,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        active_sink,
    );

    var pool = try InternPool.init(allocator);
    errdefer if (!is_moved) pool.deinit();

    var checker = try type_system.TypeChecker.init(
        allocator,
        &interner,
        &pool,
        &sym_table,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        active_sink,
    );
    defer checker.deinit();
    checker.target_layout = target_layout;
    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();

    var side_tables = try checker.extractFileSemanticSideTables(allocator);
    errdefer if (!is_moved) side_tables.deinit();

    var hir_store = try hir.lowerFileToHir(
        allocator,
        file_id,
        source,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &interner,
        &pool,
        &sym_table,
        &side_tables,
        active_sink,
        target_layout,
        .{},
    );
    errdefer if (!is_moved) hir_store.deinit();

    var mir_module = if (!active_sink.hasErrors())
        try mir.lowerHirToMirForSast(
            allocator,
            &hir_store,
            &pool,
            &sym_table,
            &interner,
            active_sink,
        )
    else
        MirModuleBundle{ .allocator = allocator };
    errdefer if (!is_moved) mir_module.deinit();

    if (!active_sink.hasErrors()) {
        try appendConstInitializerMirBodiesForSast(
            allocator,
            &hir_store,
            &pool,
            &sym_table,
            &interner,
            active_sink,
            &mir_module.bodies,
        );
    }

    var merged_cfg = sast_config;
    merged_cfg.diagnostic_sink = active_sink;
    if (merged_cfg.source_text == null) merged_cfg.source_text = source;
    if (merged_cfg.token_buffer == null) merged_cfg.token_buffer = &token_buffer;
    if (merged_cfg.cst_arena == null) merged_cfg.cst_arena = &cst_arena;

    var sast_result = if (!active_sink.hasErrors())
        try analyzeAndElaborateMirModule(
            allocator,
            mir_module.bodies.items,
            &pool,
            &sym_table,
            &interner,
            merged_cfg,
        )
    else
        try analyzeAndElaborateMirModule(
            allocator,
            &.{},
            &pool,
            &sym_table,
            &interner,
            .{},
        );
    errdefer if (!is_moved) sast_result.deinit();

    is_moved = true;
    return .{
        .allocator = allocator,
        .interner = interner,
        .token_buffer = token_buffer,
        .cst_arena = cst_arena,
        .ast_arena = ast_arena,
        .sym_table = sym_table,
        .pool = pool,
        .side_tables = side_tables,
        .hir_store = hir_store,
        .mir_module = mir_module,
        .sast_result = sast_result,
        .diagnostics = diagnostics,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_phase6_binary_layout_invariants_summary_witness_and_intv" {
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(EffectCapabilityMask));
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(FnContractScratchMask));
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(FnRegionSummary));
    try std.testing.expectEqual(@as(usize, 320), @sizeOf(FnRegionSummary) * 8);
    try std.testing.expectEqual(@as(usize, 34), FnRegionSummary.OBSERVABLE_SUMMARY_BYTES);
    try std.testing.expectEqual(@as(usize, 12), @sizeOf(WitnessCallEdge));
    try std.testing.expectEqual(@as(usize, 20), @sizeOf(MovePathNode));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(Intv));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(PentagonSubRow));

    var sum_a = FnRegionSummary{
        .ret_provenance_mask = 0x05,
        .param_flow_matrix = 0x12,
        .global_escape_mask = 0x01,
        .consumed_param_mask = 0x02,
        .own_frame_bytes = 64,
        .max_subtree_bytes = 256,
        .inferred_effects_bits = 0x0041,
        .direct_effects_bits = 0x0001,
        .contracts_scratch_bits = 0x0013,
        .forwarded_cb_mask = 0x0002,
    };
    var sum_b = sum_a;
    // Mutating internal-only `own_frame_bytes` and `direct_effects_bits` MUST NOT change the 34-byte projection:
    sum_b.own_frame_bytes = 512;
    sum_b.direct_effects_bits = 0x0041;

    var proj_a: [34]u8 = undefined;
    var proj_b: [34]u8 = undefined;
    sum_a.writeObservableBytes(&proj_a);
    sum_b.writeObservableBytes(&proj_b);
    try std.testing.expectEqualSlices(u8, &proj_a, &proj_b);

    // Mutating caller-observable `inferred_effects_bits` MUST change the 34-byte projection:
    sum_b.inferred_effects_bits = 0x0043;
    sum_b.writeObservableBytes(&proj_b);
    try std.testing.expect(!std.mem.eql(u8, &proj_a, &proj_b));
}

test "test_phase6_intv_sign_biased_encoding_and_dense_bitset_modes" {
    const neg_iv = Intv.initSigned(-100, -10);
    const pos_iv = Intv.initSigned(5, 50);
    try std.testing.expect(!neg_iv.isBottom());
    try std.testing.expect(neg_iv.hi_ord < pos_iv.lo_ord);

    const joined = neg_iv.join(pos_iv);
    try std.testing.expectEqual(@as(i64, -100), Intv.decodeSigned(joined.lo_ord));
    try std.testing.expectEqual(@as(i64, 50), Intv.decodeSigned(joined.hi_ord));
    try std.testing.expect(neg_iv.meet(pos_iv).isBottom());

    var arena = BumpArena.init(std.testing.allocator);
    defer arena.deinit();
    const a_alloc = arena.asAllocator();

    var small_bs = try DenseBitSet.initEmpty(a_alloc, 40);
    try std.testing.expect(small_bs == .inline_words);
    small_bs.set(39);
    try std.testing.expect(small_bs.isSet(39));
    small_bs.unset(39);
    try std.testing.expect(!small_bs.isSet(39));

    var large_bs = try DenseBitSet.initEmpty(a_alloc, 200);
    try std.testing.expect(large_bs == .arena_words);
    large_bs.set(150);
    try std.testing.expect(large_bs.isSet(150));
    try std.testing.expectEqual(@as(?usize, 150), large_bs.firstIntersectionBit(large_bs));
}

test "test_phase6_sast_use_after_move_linear_leak_nll_and_pentagon_bce" {
    const allocator = std.testing.allocator;

    // [1] Valid Pentagon BCE (`if idx < data.len { data[idx] }`) + sequential NLL borrow release:
    {
        const ok_src =
            \\@no_panic
            \\pub fn safe_read(data: &[i64], idx: usize) -> i64 {
            \\    if idx < data.len {
            \\        return data[idx];
            \\    }
            \\    return 0;
            \\}
        ;
        var ok_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(1),
            ok_src,
            TargetLayout.NATIVE_64,
            .{ .is_sast_strict = true },
        );
        defer ok_bundle.deinit();
        try std.testing.expect(!ok_bundle.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(usize, 0), ok_bundle.diagnostics.diagnostics.items.len);
        try std.testing.expectEqual(@as(u32, 1), ok_bundle.sast_result.eliminated_bounds_checks);
        try std.testing.expect(ok_bundle.sast_result.peak_pentagon_bytes < 1_500_000);
    }

    // [2] Static OOB (`E0307`) on fixed array `[i64; 3]`:
    {
        const oob_src =
            \\pub fn bad_oob() -> i64 {
            \\    let arr: [i64; 3] = [10, 20, 30];
            \\    return arr[3];
            \\}
        ;
        var oob_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(2),
            oob_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer oob_bundle.deinit();
        var has_seen_e0307 = false;
        for (oob_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0307_static_buffer_overflow) has_seen_e0307 = true;
        }
        try std.testing.expect(has_seen_e0307);
    }

    // [3] `@linear` resource leak (`E0304`) when neither consumed nor closed in `defer`:
    {
        const leak_src =
            \\@linear
            \\pub struct TxHandle {
            \\    pub id: i64,
            \\}
            \\
            \\pub fn leak_tx() -> i64 {
            \\    let tx = TxHandle { id: 7 };
            \\    return 42;
            \\}
        ;
        var leak_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(3),
            leak_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer leak_bundle.deinit();
        var has_seen_e0304 = false;
        for (leak_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0304_resource_or_memory_leak) has_seen_e0304 = true;
        }
        try std.testing.expect(has_seen_e0304);
    }
}

test "test_phase6_sast_defer_linear_set_param_double_free_and_drop_if_live" {
    const allocator = std.testing.allocator;

    // [1] `@linear` consumed inside `defer` satisfies Completeness Law (`0` errors), while empty `sink` leaks (`E0304`):
    {
        const defer_ok_src =
            \\@linear
            \\pub struct TxGuard {
            \\    pub code: i64,
            \\}
            \\pub fn close_guard(own guard: sink TxGuard) {
            \\    let TxGuard { code: _ } = guard;
            \\}
            \\pub fn run_tx(flag: bool) -> i64 {
            \\    let guard = TxGuard { code: 11 };
            \\    defer { close_guard(guard); }
            \\    if flag {
            \\        return 1;
            \\    }
            \\    return 2;
            \\}
        ;
        var ok_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(10),
            defer_ok_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer ok_bundle.deinit();
        try std.testing.expect(!ok_bundle.diagnostics.hasErrors());

        const unconsumed_sink_src =
            \\@linear
            \\pub struct TxGuard {
            \\    pub code: i64,
            \\}
            \\pub fn bad_sink_leak(own guard: sink TxGuard) {}
        ;
        var sink_leak_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(19),
            unconsumed_sink_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer sink_leak_bundle.deinit();
        var has_seen_sink_e0304 = false;
        for (sink_leak_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0304_resource_or_memory_leak) has_seen_sink_e0304 = true;
        }
        try std.testing.expect(has_seen_sink_e0304);
    }

    // [2] Duplicate `@linear` consumption emits `E0313`, and `AutoDrop` use-after-move emits `E0302`:
    {
        const double_src =
            \\@linear
            \\pub struct FileDesc {
            \\    pub fd: i32,
            \\}
            \\pub struct Vec[T] {
            \\    pub len: usize,
            \\}
            \\pub fn close_fd(own desc: sink FileDesc) {
            \\    let FileDesc { fd: _ } = desc;
            \\}
            \\pub fn take_vec(own items: sink Vec[i64]) {}
            \\pub fn bad_double_and_move() {
            \\    let desc = FileDesc { fd: 3 };
            \\    close_fd(desc);
            \\    close_fd(desc);
            \\    let items = Vec { len: 4 };
            \\    take_vec(items);
            \\    let _ = items.len;
            \\}
        ;
        var dbl_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(11),
            double_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer dbl_bundle.deinit();
        var has_seen_e0313 = false;
        var has_seen_e0302 = false;
        for (dbl_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0313_double_free_or_close) has_seen_e0313 = true;
            if (d_item.code == .e0302_use_after_move) has_seen_e0302 = true;
        }
        try std.testing.expect(has_seen_e0313);
        try std.testing.expect(has_seen_e0302);
    }

    // [3] Uninitialized `set` out-parameter on one branch emits `E0303`:
    {
        const set_src =
            \\pub fn maybe_init_out(mut out_slot: set i64, cond: bool) {
            \\    if cond {
            \\        out_slot = 99;
            \\    }
            \\}
        ;
        var set_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(12),
            set_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer set_bundle.deinit();
        var has_seen_e0303 = false;
        for (set_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0303_uninitialized_memory_read) has_seen_e0303 = true;
        }
        try std.testing.expect(has_seen_e0303);
    }

    // [4] Branch-divergent `AutoDrop` move synthesizes `drop_if_live` without splitting blocks (`V1`–`V6` clean):
    {
        const cond_drop_src =
            \\pub struct Vec[T] {
            \\    pub len: usize,
            \\}
            \\pub fn consume_vec(own buf: sink Vec[i64]) {}
            \\pub fn branch_drop(cond: bool) -> i64 {
            \\    let buf = Vec { len: 8 };
            \\    if cond {
            \\        consume_vec(buf);
            \\    }
            \\    return 5;
            \\}
        ;
        var drop_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(13),
            cond_drop_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer drop_bundle.deinit();
        try std.testing.expect(!drop_bundle.diagnostics.hasErrors());
        try std.testing.expect(drop_bundle.sast_result.emitted_drops >= 1);

        const branch_body = drop_bundle.mir_module.findBodyByName(&drop_bundle.interner, "branch_drop").?;
        var has_seen_drop_if_live = false;
        for (branch_body.block_insts.items) |inst_val| {
            const inst = branch_body.getInst(inst_val);
            if (inst.op == .intrinsic_op) {
                const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                if (ikind == .drop_if_live) has_seen_drop_if_live = true;
            }
        }
        try std.testing.expect(has_seen_drop_if_live);
    }
}

test "test_phase6_sast_transitive_nll_stack_escape_narrow_and_contracts" {
    const allocator = std.testing.allocator;

    // [1] Sequential zero-`<'a>` view borrow closes after last SSA use (`0` errors), while interleaved emits `E0305`:
    {
        const seq_ok_src =
            \\pub fn head_slice(items: &[i64]) -> &[i64] {
            \\    return items;
            \\}
            \\pub fn mutate_arr(mut arr: inout [i64; 4]) {
            \\    arr[0] = 99;
            \\}
            \\pub fn sequential_ok() -> usize {
            \\    var arr: [i64; 4] = [1, 2, 3, 4];
            \\    let view = head_slice(&arr);
            \\    let count = view.len;
            \\    mutate_arr(arr);
            \\    return count;
            \\}
        ;
        var seq_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(20),
            seq_ok_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer seq_bundle.deinit();
        try std.testing.expect(!seq_bundle.diagnostics.hasErrors());

        const conflict_src =
            \\pub fn head_slice(items: &[i64]) -> &[i64] {
            \\    return items;
            \\}
            \\pub fn mutate_arr(mut arr: inout [i64; 4]) {
            \\    arr[0] = 99;
            \\}
            \\pub fn interleaved_conflict() -> usize {
            \\    var arr: [i64; 4] = [1, 2, 3, 4];
            \\    let view = head_slice(&arr);
            \\    mutate_arr(arr);
            \\    return view.len;
            \\}
        ;
        var conf_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(21),
            conflict_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer conf_bundle.deinit();
        var has_seen_e0305 = false;
        for (conf_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0305_exclusivity_violation) has_seen_e0305 = true;
        }
        try std.testing.expect(has_seen_e0305);
    }

    // [2] Returning reference to stack local emits `E0306`:
    {
        const escape_src =
            \\pub fn bad_return_ref() -> &i64 {
            \\    let local_num: i64 = 77;
            \\    return &local_num;
            \\}
        ;
        var esc_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(22),
            escape_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer esc_bundle.deinit();
        var has_seen_e0306 = false;
        for (esc_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0306_region_escape_violation) has_seen_e0306 = true;
        }
        try std.testing.expect(has_seen_e0306);
    }

    // [3] Pentagon `rem_u` (`raw % data.len`) + `.narrow[u8]()` elision vs `E0406` compile-time narrowing error:
    {
        const pent_ok_src =
            \\@no_panic
            \\pub fn mod_and_narrow(data: &[u8], raw_idx: usize, bounded_val: i32) -> u8 {
            \\    if data.len > 0 and bounded_val >= 0 and bounded_val <= 200 {
            \\        let elem = data[raw_idx % data.len];
            \\        let narrowed: u8 = bounded_val.narrow[u8]();
            \\        return elem & narrowed;
            \\    }
            \\    return 0;
            \\}
        ;
        var pent_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(23),
            pent_ok_src,
            TargetLayout.NATIVE_64,
            .{ .is_sast_strict = true },
        );
        defer pent_bundle.deinit();
        try std.testing.expect(!pent_bundle.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(u32, 1), pent_bundle.sast_result.eliminated_bounds_checks);
        try std.testing.expectEqual(@as(u32, 1), pent_bundle.sast_result.eliminated_narrow_checks);

        const bad_narrow_src =
            \\pub fn always_bad_narrow() -> u8 {
            \\    let too_big: i32 = 512;
            \\    return too_big.narrow[u8]();
            \\}
        ;
        var nar_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(24),
            bad_narrow_src,
            TargetLayout.NATIVE_64,
            .{},
        );
        defer nar_bundle.deinit();
        var has_seen_e0406 = false;
        for (nar_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0406_range_refinement_violation) has_seen_e0406 = true;
        }
        try std.testing.expect(has_seen_e0406);
    }

    // [4] `@max_stack(32)` recursion (`E0316`), `@no_block` + witness BFS (`E0322`), & `PackageCapPolicy` (`E0324`/`W0330`):
    {
        const cap_src =
            \\extern "C" fn host_ffi_op() -> i32;
            \\
            \\@max_stack(32)
            \\pub fn rec_climb(depth: i32) -> i32 {
            \\    if depth <= 0 {
            \\        return 0;
            \\    }
            \\    return rec_climb(depth - 1) + 1;
            \\}
            \\
            \\@no_block
            \\pub fn non_blocking_entry() -> i32 {
            \\    return unsafe { host_ffi_op() };
            \\}
            \\
            \\fn dead_private_ffi() -> i32 {
            \\    return unsafe { host_ffi_op() };
            \\}
        ;
        var cap_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(25),
            cap_src,
            TargetLayout.NATIVE_64,
            .{
                .package_policy = .{
                    .package_name = "demo_dep",
                    .allowed_caps = EffectCapabilityMask.EMPTY,
                    .is_third_party_dependency = true,
                    .policy_span = Span.init(FileId.fromInt(25), 0, 10),
                },
            },
        );
        defer cap_bundle.deinit();

        var has_seen_e0316 = false;
        var has_seen_e0322 = false;
        var has_seen_e0324 = false;
        for (cap_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .e0316_max_stack_budget_exceeded) has_seen_e0316 = true;
            if (d_item.code == .e0322_no_block_contract_violation) has_seen_e0322 = true;
            if (d_item.code == .e0324_package_capability_violation) has_seen_e0324 = true;
        }
        try std.testing.expect(has_seen_e0316);
        try std.testing.expect(has_seen_e0322);
        try std.testing.expect(has_seen_e0324);

        // Also verify `W0330` when ONLY dead private FFI exists in a third-party dependency:
        const dead_only_src =
            \\extern "C" fn raw_c_sym() -> i32;
            \\pub fn pure_public_api(val: i32) -> i32 {
            \\    return val + 1;
            \\}
            \\fn unreachable_ffi_helper() -> i32 {
            \\    return unsafe { raw_c_sym() };
            \\}
        ;
        var dead_bundle = try lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(26),
            dead_only_src,
            TargetLayout.NATIVE_64,
            .{
                .package_policy = .{
                    .package_name = "dead_ffi_pkg",
                    .allowed_caps = EffectCapabilityMask.EMPTY,
                    .is_third_party_dependency = true,
                    .policy_span = Span.init(FileId.fromInt(26), 0, 10),
                },
            },
        );
        defer dead_bundle.deinit();
        var has_seen_w0330 = false;
        for (dead_bundle.diagnostics.diagnostics.items) |d_item| {
            if (d_item.code == .w0330_ambient_dead_capability_in_dep) has_seen_w0330 = true;
        }
        try std.testing.expect(has_seen_w0330);
    }
}

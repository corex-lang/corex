//! Stackless Coroutine State-Machine Analysis, Liveness Coloring & Frame Layout
//!
//! Defines the canonical `comptime`-verified binary metadata records (`CoroStateTag`, `SuspendPointMeta`,
//! `CoroLocalSlot`, `CoroFrameLayout`, and `ClosureEnvSlot`), performs `Pass D5.5` cross-block SSA spill
//! demotion, computes reverse-dataflow local liveness and greedy frame-slot coloring across `.coro_suspend`,
//! and enforces the `16 KiB` (`ASYNC_INLINE_FRAME_CAP_BYTES`) inline coroutine frame cap (`E0317`).
//!
//! Greedy frame coloring sorts candidates by descending `align_bytes`, descending `byte_size`, and ascending
//! `local_id` for deterministic cross-platform layouts, while `FramePinned` locals (`is_address_taken` or
//! `place_addr` targets) stay live across all blocks and conflict with all non-ZST locals so borrows never alias.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const diagnostic = @import("diag/diagnostic.zig");
const query_db = @import("query_db.zig");
const type_system = @import("type_system.zig");
const mir = @import("mir.zig");

const SymbolId = mem_foundation.SymbolId;
const TokenIndex = mem_foundation.TokenIndex;
const TypeId = mem_foundation.TypeId;
const MirBlockId = mem_foundation.MirBlockId;
const MirValueId = mem_foundation.MirValueId;
const DefId = query_db.DefId;
const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;
const DiagnosticSink = diagnostic.DiagnosticSink;
const InternPool = type_system.InternPool;
const TargetLayout = type_system.TargetLayout;
const LocalId = mir.LocalId;
const PlaceId = mir.PlaceId;
const LocalDecl = mir.LocalDecl;
const LocalFlags = mir.LocalFlags;
const MirPlace = mir.MirPlace;
const MirProjection = mir.MirProjection;
const MirOp = mir.MirOp;
const MirInst = mir.MirInst;
const MirIntrinsicKind = mir.MirIntrinsicKind;
const AggregateKind = mir.AggregateKind;
const MirBody = mir.MirBody;

// ---------------------------------------- TYPES ----------------------------------------

/// Discriminant stored at byte offset `0` of every stackless coroutine frame (`DR-08` §2.2).
pub const CoroStateTag = enum(u32) {
    /// Initial unpolled state constructed lazily by `async_future_make` (`0`).
    unpolled = 0,
    /// Terminal state after `poll` produces `Ready(output)` (`0xFFFF_FFFE`).
    completed = 0xFFFF_FFFE,
    /// Terminal state after cancellation runs `cancel_bb` or drops unpolled arguments (`0xFFFF_FFFF`).
    canceled = 0xFFFF_FFFF,
    _,

    /// Encodes zero-based suspend-point ordinal `suspend_index` (`0 .. K - 1`) into state tag `1 .. K`.
    pub inline fn fromSuspendIndex(suspend_index: u32) CoroStateTag {
        return @fromBackingInt(suspend_index + 1);
    }

    /// Extracts the raw `u32` state tag value.
    pub inline fn asInt(self: CoroStateTag) u32 {
        return @backingInt(self);
    }

    /// Returns `true` when `self` represents an active suspension point (`1 .. 0xFFFF_FFFD`).
    pub inline fn isSuspended(self: CoroStateTag) bool {
        const raw = @backingInt(self);
        return raw >= 1 and raw < @backingInt(CoroStateTag.completed);
    }
};

/// 24-byte canonical per-`.await` suspension descriptor (`DR-08` §2.2).
pub const SuspendPointMeta = extern struct {
    /// Basic block terminated by `TerminatorKind.coro_suspend` (`4B`).
    suspend_block: MirBlockId,
    /// Continuation basic block receiving `%ready_val` on `Poll.Ready` (`4B`).
    resume_block: MirBlockId,
    /// Cold cleanup basic block (`isCleanupPad()`) executed on task cancellation (`4B`).
    cancel_block: MirBlockId,
    /// Non-zero `CoroStateTag` (`1 .. K`) stored while suspended at this `.await` (`4B`).
    state_tag: u32,
    /// Byte offset inside the parent coroutine frame holding the active child `Future[T]` (`4B`).
    child_frame_offset: u32,
    /// Byte size reserved for the awaited `Future[T]` descriptor + inline child state (`4B`).
    child_frame_bytes: u32,
};

/// 16-byte liveness-colored coroutine frame slot assignment for a `LocalDecl` (`DR-08` §2.3).
pub const CoroLocalSlot = extern struct {
    /// Zero-based `LocalId` (or spilled SSA value slot) inside `MirBody.locals` (`4B`).
    local_or_val_id: u32,
    /// Aligned byte offset relative to the base of the coroutine frame (`4B`).
    byte_offset: u32,
    /// Exact storage size in bytes (`4B`).
    byte_size: u32,
    /// Required power-of-two byte alignment (`4B`).
    align_bytes: u32,
};

/// 16-byte stackless coroutine frame layout summary (`DR-08` §2.3).
pub const CoroFrameLayout = extern struct {
    /// Frame header byte size (`state`, `body_idx`, `ctx_override_mask`, `flags`, `4B`-aligned to `16B`).
    header_bytes: u32,
    /// Total byte span occupied by liveness-colored locals and pinned closure environments (`4B`).
    colored_locals_bytes: u32,
    /// Maximum inline child `Future` / sub-coroutine byte footprint across all `.await` sites (`4B`).
    max_child_bytes: u32,
    /// Total aligned coroutine frame size (`<= ASYNC_INLINE_FRAME_CAP_BYTES` for inline frames, `4B`).
    total_frame_bytes: u32,
};

/// 16-byte persistent coroutine-frame environment slot for a 2-word `@local` `closure_make`.
pub const ClosureEnvSlot = extern struct {
    /// `MirValueId` raw index of the `MirOp.aggregate_make` (`closure_make`) instruction (`4B`).
    inst_val_id: u32,
    /// Aligned byte offset inside the coroutine frame (`4B`).
    byte_offset: u32,
    /// Environment capture buffer byte size (`4B`).
    byte_size: u32,
    /// Environment capture buffer byte alignment (`4B`).
    align_bytes: u32,
};

/// Complete lowered state-machine & frame-coloring plan for a single `MirBody`.
pub const AsyncBodyPlan = struct {
    /// Zero-based index of this body in `module.bodies`.
    body_index: u32 = 0,
    /// `true` when `body.is_async` is set.
    is_async: bool = false,
    /// Required power-of-two byte alignment of the coroutine frame (`>= 8` on 64-bit, `>= 4` on `wasm32`).
    frame_align: u32 = 8,
    /// 10-bit mask of `ContextFieldKind` slots (`0..9`) written via `ctx_set` in this body.
    ctx_override_mask: u16 = 0,
    /// `true` if `frame_layout.total_frame_bytes > ASYNC_INLINE_FRAME_CAP_BYTES`.
    has_exceeded_inline_cap: bool = false,
    /// `true` if this `is_async` body participates in an unboxed async recursion cycle (`E0317`).
    has_unboxed_recursion: bool = false,
    /// Number of non-ZST locals that reused an earlier local's frame bytes via graph coloring.
    reused_slot_count: u32 = 0,
    /// Computed 16-byte `CoroFrameLayout`.
    frame_layout: CoroFrameLayout = .{
        .header_bytes = 0,
        .colored_locals_bytes = 0,
        .max_child_bytes = 0,
        .total_frame_bytes = 0,
    },
    /// Ordered `.coro_suspend` descriptors (`state_tag == idx + 1`).
    suspend_points: []SuspendPointMeta = &.{},
    /// Parallel `Future[T]` `TypeId` awaited at each entry in `suspend_points`.
    suspend_future_types: []TypeId = &.{},
    /// Parallel unwrapped output `T` `TypeId` delivered to `resume_block` at each suspend point.
    suspend_ready_types: []TypeId = &.{},
    /// Colored local slot records sorted by ascending `local_or_val_id`.
    local_slots: []CoroLocalSlot = &.{},
    /// Dense `0 .. body.locals.len - 1` frame byte offset table (`0` for ZST slots).
    local_offsets: []u32 = &.{},
    /// Frame-resident environment buffers for 2-word `@local` closures constructed in this body.
    closure_env_slots: []ClosureEnvSlot = &.{},
    /// Deduplicated `body_index` list of statically resolved `is_async` callees awaited by this body.
    awaited_callees: []u32 = &.{},
    /// $O(1)$ lookup map from `suspend_block.asInt()` to its zero-based index in `suspend_points`.
    suspend_block_map: std.AutoHashMapUnmanaged(u32, usize) = .empty,
    /// $O(1)$ lookup map from `closure_make` `inst_val_id` to its frame `byte_offset`.
    closure_env_map: std.AutoHashMapUnmanaged(u32, u32) = .empty,

    /// Releases all slices and lookup maps owned by `self`.
    pub fn deinit(self: *AsyncBodyPlan, allocator: std.mem.Allocator) void {
        if (self.suspend_points.len > 0) allocator.free(self.suspend_points);
        if (self.suspend_future_types.len > 0) allocator.free(self.suspend_future_types);
        if (self.suspend_ready_types.len > 0) allocator.free(self.suspend_ready_types);
        if (self.local_slots.len > 0) allocator.free(self.local_slots);
        if (self.local_offsets.len > 0) allocator.free(self.local_offsets);
        if (self.closure_env_slots.len > 0) allocator.free(self.closure_env_slots);
        if (self.awaited_callees.len > 0) allocator.free(self.awaited_callees);
        self.suspend_block_map.deinit(allocator);
        self.closure_env_map.deinit(allocator);
        self.* = undefined;
    }

    /// Returns the coroutine frame byte offset for `local_id` in $O(1)$ time.
    pub inline fn getLocalOffset(self: *const AsyncBodyPlan, local_id: u32) u32 {
        if (local_id < self.local_offsets.len) return self.local_offsets[local_id];
        return self.frame_layout.header_bytes;
    }

    /// Looks up the zero-based suspend-point index (`0 .. K - 1`) for `suspend_block` in $O(1)$ time.
    pub fn findSuspendByBlock(self: *const AsyncBodyPlan, suspend_block: MirBlockId) ?usize {
        return self.suspend_block_map.get(suspend_block.asInt());
    }

    /// Looks up the frame byte offset reserved for `closure_make` instruction `inst_val_id` in $O(1)$ time.
    pub fn findClosureEnvOffset(self: *const AsyncBodyPlan, inst_val_id: u32) ?u32 {
        return self.closure_env_map.get(inst_val_id);
    }
};

/// Whole-module coroutine frame and call-hierarchy plan across `module.bodies`.
pub const AsyncModulePlan = struct {
    /// Allocator owning `body_plans` and all nested slices.
    allocator: std.mem.Allocator,
    /// Per-body `AsyncBodyPlan` slice (`&.{}` when `!has_any_async_ops`, else `len == module.bodies.len`).
    body_plans: []AsyncBodyPlan,
    /// `true` when at least one `is_async` body or async intrinsic (`44..51`) exists in the module.
    has_any_async_ops: bool = false,

    /// Releases all memory owned by `self`.
    pub fn deinit(self: *AsyncModulePlan) void {
        for (self.body_plans) |*plan| {
            plan.deinit(self.allocator);
        }
        if (self.body_plans.len > 0) self.allocator.free(self.body_plans);
        self.* = undefined;
    }

    /// Returns the `AsyncBodyPlan` for `body_idx`.
    pub inline fn getBodyPlan(self: *const AsyncModulePlan, body_idx: usize) *const AsyncBodyPlan {
        return &self.body_plans[body_idx];
    }
};

/// Candidate local entry used during deterministic greedy frame-slot coloring.
const ColorCandidate = struct {
    /// Zero-based `LocalId` in `MirBody.locals`.
    local_id: u32,
    /// Storage byte size (`> 0`).
    byte_size: u32,
    /// Power-of-two byte alignment (`>= 1`).
    align_bytes: u32,
};

/// Storage byte size and alignment of a `LocalDecl` inside a coroutine frame.
const LocalFrameMetrics = struct {
    /// Exact storage size in bytes (`0` for ZSTs).
    byte_size: u32,
    /// Required power-of-two byte alignment (`>= 1`).
    align_bytes: u32,
};

/// Precomputed $O(1)$ lookup tables resolving `(DefId, SymbolIndex)` callees to `body_index`.
const CalleeBodyIndexMap = struct {
    /// Maps non-`NONE` `DefId.asInt()` to the first matching `body_index` in `bodies`.
    def_to_body: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Maps non-`none` `SymbolIndex.asInt()` to the first matching `body_index` in `bodies`.
    sym_to_body: std.AutoHashMapUnmanaged(u32, u32) = .empty,

    /// Builds $O(1)$ `def_to_body` and `sym_to_body` lookup indices over `bodies`.
    fn init(allocator: std.mem.Allocator, bodies: []const MirBody) !CalleeBodyIndexMap {
        var map: CalleeBodyIndexMap = .{};
        errdefer map.deinit(allocator);
        for (bodies, 0..) |*cand, idx| {
            const body_idx: u32 = @intCast(idx);
            if (!cand.def_id.isNone()) {
                const gop = try map.def_to_body.getOrPut(allocator, cand.def_id.asInt());
                if (!gop.found_existing) gop.value_ptr.* = body_idx;
            }
            if (!cand.symbol_index.isNone()) {
                const gop = try map.sym_to_body.getOrPut(allocator, cand.symbol_index.asInt());
                if (!gop.found_existing) gop.value_ptr.* = body_idx;
            }
        }
        return map;
    }

    /// Releases hash map storage owned by `self`.
    fn deinit(self: *CalleeBodyIndexMap, allocator: std.mem.Allocator) void {
        self.def_to_body.deinit(allocator);
        self.sym_to_body.deinit(allocator);
    }

    /// Resolves `(def_id, sym_idx)` to its `body_index` in $O(1)$ time, or `null` if external.
    inline fn find(self: *const CalleeBodyIndexMap, def_id: DefId, sym_idx: SymbolIndex) ?u32 {
        if (!def_id.isNone()) {
            if (self.def_to_body.get(def_id.asInt())) |found_idx| return found_idx;
        }
        if (!sym_idx.isNone()) {
            if (self.sym_to_body.get(sym_idx.asInt())) |found_idx| return found_idx;
        }
        return null;
    }
};

/// Unplaced 2-word `@local` closure environment capture buffer discovered during block scanning.
const RawClosureEnv = struct {
    /// `MirValueId` raw index of the `closure_make` instruction.
    inst_val_id: u32,
    /// Total byte size of captured values (`> 0`).
    byte_size: u32,
    /// Required byte alignment of the environment buffer.
    align_bytes: u32,
};

/// Half-open coroutine frame byte range `[start .. end)` occupied by an interfering local.
const Interval = struct {
    /// Inclusive starting frame byte offset.
    start: u32,
    /// Exclusive ending frame byte offset.
    end: u32,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum inline stackless coroutine frame subtree size (`16 KiB`, `DR-08` §2.3, `E0317`).
pub const ASYNC_INLINE_FRAME_CAP_BYTES: u32 = 16_384;
/// Fixed 16-byte header (`[0..4]` `state`, `[4..8]` `body_idx`, `[8..10]` `ctx_mask`, `[10..16]` flags/pad).
pub const CORO_HEADER_BYTES: u32 = 16;
/// Canonical 10-slot `Context` count (`ContextFieldLayout.CANONICAL_FIELDS.len`).
pub const CORO_CTX_SLOT_COUNT: u32 = type_system.ContextFieldLayout.CANONICAL_FIELDS.len;
/// First async `MirIntrinsicKind` backing integer (`async_future_make = 44`).
const FIRST_ASYNC_INTRINSIC: u16 = @backingInt(MirIntrinsicKind.async_future_make);
/// Last async `MirIntrinsicKind` backing integer (`async_block_on = 51`).
const LAST_ASYNC_INTRINSIC: u16 = @backingInt(MirIntrinsicKind.async_block_on);
/// Maximum call-chain depth when tracing `Future` returns through synchronous forwarding wrappers.
const MAX_SYNC_WRAPPER_DEPTH: u8 = 8;

// -------------------------------------- INTERNALS --------------------------------------

// --------------------- Alignment & Bitset ---------------------

/// Aligns `value` upward to the next multiple of power-of-two `align_bytes`.
inline fn alignUpU32(value: u32, align_bytes: u32) u32 {
    const safe_align = @max(align_bytes, 1);
    return (value + safe_align - 1) & ~(safe_align - 1);
}

/// Returns `true` when bit `bit_idx` is set inside a `u64`-word bitset row.
inline fn isBitSet(words: []const u64, bit_idx: usize) bool {
    return (words[bit_idx >> 6] & (@as(u64, 1) << @as(u6, @truncate(bit_idx)))) != 0;
}

/// Sets bit `bit_idx` inside a `u64`-word bitset row and returns `true` if newly set.
inline fn setBit(words: []u64, bit_idx: usize) bool {
    const word_ptr = &words[bit_idx >> 6];
    const mask = @as(u64, 1) << @as(u6, @truncate(bit_idx));
    if ((word_ptr.* & mask) != 0) return false;
    word_ptr.* |= mask;
    return true;
}

/// Clears bit `bit_idx` inside a `u64`-word bitset row.
inline fn clearBit(words: []u64, bit_idx: usize) void {
    words[bit_idx >> 6] &= ~(@as(u64, 1) << @as(u6, @truncate(bit_idx)));
}

/// Computes the storage byte size and alignment of `loc_decl` inside a coroutine frame.
fn computeLocalFrameSizeAndAlign(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    loc_decl: LocalDecl,
    target_layout: TargetLayout,
) LocalFrameMetrics {
    if (loc_decl.flags().is_arg and (loc_decl.mode() == .inout_mode or loc_decl.mode() == .set_mode)) {
        return .{
            .byte_size = target_layout.ptr_byte_size,
            .align_bytes = target_layout.ptrAlignBytes(),
        };
    }
    const type_layout = type_system.computeTypeLayoutWithPool(pool, sym_table, loc_decl.type_id, target_layout);
    return .{
        .byte_size = @intCast(@min(type_layout.byte_size, ASYNC_INLINE_FRAME_CAP_BYTES * 2)),
        .align_bytes = @max(type_layout.align_bytes, 1),
    };
}

// --------------------- SSA Spill Demotion ---------------------

/// Records `val_raw` if `val_raw` is used in `bb_idx` outside its defining basic block.
fn markIfCrossBlockUse(
    val_raw: u32,
    bb_idx: u32,
    def_bb_of_val: []const u32,
    is_demote_needed: []bool,
) void {
    if (val_raw >= def_bb_of_val.len) return;
    const def_bb = def_bb_of_val[val_raw];
    if (def_bb != mir.NONE_U32 and def_bb != bb_idx) {
        is_demote_needed[val_raw] = true;
    }
}

/// Scans dynamic `.index` projections on `place_id` for cross-block SSA uses in `bb_idx`.
fn scanPlaceIndexUses(
    body: *const MirBody,
    place_id: PlaceId,
    bb_idx: u32,
    def_bb_of_val: []const u32,
    is_demote_needed: []bool,
) void {
    if (place_id.isNone() or place_id.asInt() >= body.places.items.len) return;
    for (body.getPlaceProjections(place_id)) |proj| {
        if (proj.kind == .index) {
            markIfCrossBlockUse(proj.payload, bb_idx, def_bb_of_val, is_demote_needed);
        }
    }
}

/// Rewrites dynamic `.index` projections on `place_id` in `bb_idx`, cloning `MirPlace` when needed.
fn rewritePlaceIndexUses(
    body: *MirBody,
    place_id: PlaceId,
    bb_idx: u32,
    def_bb_of_val: []const u32,
    spill_places: []const PlaceId,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    block_reload_cache: *std.AutoHashMapUnmanaged(u32, MirValueId),
    emit_list: *std.ArrayListUnmanaged(MirValueId),
    origin_tok: TokenIndex,
) !PlaceId {
    if (place_id.isNone() or place_id.asInt() >= body.places.items.len) return place_id;
    const place_rec = body.places.items[place_id.asInt()];
    if (place_rec.proj_len == 0) return place_id;

    var has_cross_idx = false;
    for (body.getPlaceProjections(place_id)) |proj| {
        if (proj.kind == .index and proj.payload < def_bb_of_val.len and
            def_bb_of_val[proj.payload] != mir.NONE_U32 and def_bb_of_val[proj.payload] != bb_idx)
        {
            has_cross_idx = true;
            break;
        }
    }
    if (!has_cross_idx) return place_id;

    const proj_len: usize = place_rec.proj_len;
    const new_proj_start: u32 = @intCast(body.projections.items.len);
    try body.projections.ensureUnusedCapacity(body.allocator, proj_len);
    for (0..proj_len) |step_i| {
        var proj_copy = body.projections.items[place_rec.proj_start + step_i];
        if (proj_copy.kind == .index) {
            const mapped = try reloadOrRematValueInBlock(
                body,
                proj_copy.payload,
                bb_idx,
                def_bb_of_val,
                spill_places,
                pool,
                sym_table,
                block_reload_cache,
                emit_list,
                origin_tok,
            );
            proj_copy.payload = mapped.asInt();
        }
        body.projections.appendAssumeCapacity(proj_copy);
    }

    const new_pid = PlaceId.fromInt(@intCast(body.places.items.len));
    try body.places.append(body.allocator, .{
        .base = place_rec.base,
        .proj_start = @intCast(new_proj_start),
        .proj_len = place_rec.proj_len,
    });
    return new_pid;
}

/// Appends a synthesized `MirInst` to `body` and `emit_list`, returning its `MirValueId`.
fn appendSynthInstToList(
    body: *MirBody,
    emit_list: *std.ArrayListUnmanaged(MirValueId),
    inst_rec: MirInst,
    tok: TokenIndex,
) !MirValueId {
    const new_vid = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(body.allocator, inst_rec);
    try body.origin_tokens.append(body.allocator, tok);
    try emit_list.append(body.allocator, new_vid);
    return new_vid;
}

/// Reloads or rematerializes `val_raw` inside `bb_idx` when `val_raw` was defined in another block.
fn reloadOrRematValueInBlock(
    body: *MirBody,
    val_raw: u32,
    bb_idx: u32,
    def_bb_of_val: []const u32,
    spill_places: []const PlaceId,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    block_reload_cache: *std.AutoHashMapUnmanaged(u32, MirValueId),
    emit_list: *std.ArrayListUnmanaged(MirValueId),
    fallback_tok: TokenIndex,
) !MirValueId {
    const orig_vid = MirValueId.fromInt(val_raw);
    if (val_raw >= def_bb_of_val.len) return orig_vid;
    const def_bb = def_bb_of_val[val_raw];
    if (def_bb == mir.NONE_U32 or def_bb == bb_idx) return orig_vid;
    if (block_reload_cache.get(val_raw)) |cached_vid| return cached_vid;

    const orig_inst = body.insts.get(val_raw);
    const tok = if (val_raw < body.origin_tokens.items.len) body.origin_tokens.items[val_raw] else fallback_tok;

    // [1] Rematerialize pure constants and function addresses with zero frame storage:
    if (orig_inst.op == .const_scalar or orig_inst.op == .fn_addr) {
        var cloned_inst = orig_inst;
        cloned_inst.flags.is_synthetic = true;
        const remat_vid = try appendSynthInstToList(body, emit_list, cloned_inst, tok);
        try block_reload_cache.put(body.allocator, val_raw, remat_vid);
        return remat_vid;
    }

    // [2] Rematerialize zero-sized values (`unit`, empty tuple/struct/array) without frame loads:
    if (type_system.computeTypeLayoutWithPool(pool, sym_table, orig_inst.type_id, body.target_layout).byte_size == 0) {
        const unit_c_idx: u32 = @intCast(body.consts.items.len);
        try body.consts.append(body.allocator, .unit_val);
        const zst_vid = try appendSynthInstToList(body, emit_list, .{
            .op = .const_scalar,
            .flags = .{ .is_synthetic = true },
            .type_id = orig_inst.type_id,
            .operands = .{ .lhs = unit_c_idx, .rhs = 0 },
        }, tok);
        try block_reload_cache.put(body.allocator, val_raw, zst_vid);
        return zst_vid;
    }

    // [3] Reload spilled non-ZST SSA value from its dedicated `LocalDecl` slot:
    const spill_pid = spill_places[val_raw];
    if (spill_pid.isNone()) return orig_vid;
    const load_vid = try appendSynthInstToList(body, emit_list, .{
        .op = .place_load,
        .flags = .{ .is_synthetic = true },
        .type_id = orig_inst.type_id,
        .operands = .{ .lhs = spill_pid.asInt(), .rhs = 0 },
    }, tok);
    try block_reload_cache.put(body.allocator, val_raw, load_vid);
    return load_vid;
}

// ----------------- Liveness & Frame Coloring ------------------

/// Ordering predicate sorting `ColorCandidate`s by descending alignment, descending size, then ascending ID.
fn compareColorCandidate(_: void, lhs_cand: ColorCandidate, rhs_cand: ColorCandidate) bool {
    if (lhs_cand.align_bytes != rhs_cand.align_bytes) return lhs_cand.align_bytes > rhs_cand.align_bytes;
    if (lhs_cand.byte_size != rhs_cand.byte_size) return lhs_cand.byte_size > rhs_cand.byte_size;
    return lhs_cand.local_id < rhs_cand.local_id;
}

/// Ordering predicate sorting `CoroLocalSlot`s by ascending `local_or_val_id`.
fn compareLocalSlotById(_: void, lhs_slot: CoroLocalSlot, rhs_slot: CoroLocalSlot) bool {
    return lhs_slot.local_or_val_id < rhs_slot.local_or_val_id;
}

/// Extracts an integer constant `u32` from `val_raw` in `body`, returning `null` if non-constant.
fn extractConstU32(body: *const MirBody, val_raw: u32) ?u32 {
    if (val_raw >= body.insts.len) return null;
    const inst = body.insts.get(val_raw);
    if (inst.op != .const_scalar or inst.operands.lhs >= body.consts.items.len) return null;
    return switch (body.consts.items[inst.operands.lhs]) {
        .int_val => |int_v| if (int_v >= 0 and int_v <= std.math.maxInt(u32)) @intCast(int_v) else null,
        else => null,
    };
}

/// Marks read/kill effects of an instruction on `live_row` and records `conflict_matrix` edges.
fn applyBackwardInstLiveness(
    body: *const MirBody,
    inst: MirInst,
    is_pinned_local: []const bool,
    live_row: []u64,
    conflict_matrix: []u64,
    words_per_row: usize,
) void {
    switch (inst.op) {
        .place_store => {
            const pid = PlaceId.fromInt(inst.operands.lhs);
            if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                const place = body.places.items[pid.asInt()];
                if (place.base < is_pinned_local.len) {
                    addConflictsWithLiveSet(place.base, live_row, conflict_matrix, words_per_row);
                    if (place.proj_len == 0 and !is_pinned_local[place.base]) {
                        clearBit(live_row, place.base);
                    } else {
                        _ = setBit(live_row, place.base);
                    }
                }
            }
        },
        .place_load,
        .place_discriminant,
        .place_set_discrim,
        .place_addr,
        .soa_column_slice,
        .ghost_access_let,
        .ghost_access_inout,
        .ghost_access_set,
        .ghost_storage_move,
        => {
            const pid = PlaceId.fromInt(inst.operands.lhs);
            if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                const base_loc = body.places.items[pid.asInt()].base;
                if (base_loc < is_pinned_local.len) {
                    addConflictsWithLiveSet(base_loc, live_row, conflict_matrix, words_per_row);
                    _ = setBit(live_row, base_loc);
                }
            }
        },
        .intrinsic_op => {
            if (@as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)).hasPlaceInLhs()) {
                const pid = PlaceId.fromInt(inst.operands.lhs);
                if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                    const base_loc = body.places.items[pid.asInt()].base;
                    if (base_loc < is_pinned_local.len) {
                        addConflictsWithLiveSet(base_loc, live_row, conflict_matrix, words_per_row);
                        _ = setBit(live_row, base_loc);
                    }
                }
            }
        },
        else => {},
    }
}

/// Adds undirected interference edges between `local_id` and every bit currently set in `live_row`.
fn addConflictsWithLiveSet(
    local_id: u32,
    live_row: []const u64,
    conflict_matrix: []u64,
    words_per_row: usize,
) void {
    const loc_usize: usize = local_id;
    const row_slice = conflict_matrix[loc_usize * words_per_row .. (loc_usize + 1) * words_per_row];
    for (live_row, 0..) |word_bits, word_i| {
        if (word_bits == 0) continue;
        row_slice[word_i] |= word_bits;
        var rem_bits = word_bits;
        while (rem_bits != 0) {
            const other_loc = (word_i << 6) + @as(usize, @ctz(rem_bits));
            _ = setBit(conflict_matrix[other_loc * words_per_row .. (other_loc + 1) * words_per_row], loc_usize);
            rem_bits &= rem_bits - 1;
        }
    }
    clearBit(row_slice, loc_usize);
}

// ------------------ Child Frame Aggregation -------------------

/// Appends `callee_idx` to `callee_list` in $O(1)$ when `bodies[callee_idx].is_async` and unseen.
fn appendUniqueAsyncCallee(
    allocator: std.mem.Allocator,
    bodies: []const MirBody,
    callee_list: *std.ArrayListUnmanaged(u32),
    seen_callees: *std.AutoHashMapUnmanaged(u32, void),
    callee_idx: u32,
) !void {
    if (callee_idx >= bodies.len or !bodies[callee_idx].is_async) return;
    if (!(try seen_callees.getOrPut(allocator, callee_idx)).found_existing) {
        try callee_list.append(allocator, callee_idx);
    }
}

/// Resolves an `InternPool` `Future[T]` `producer_id` (`SymbolIndex` first, then non-`FileId(0)` `DefId`).
fn resolveFutureProducerBodyIndex(callee_map: *const CalleeBodyIndexMap, prod_id: u32) ?u32 {
    if (prod_id == 0) return null;
    return callee_map.find(DefId.NONE, SymbolIndex.fromInt(prod_id)) orelse
        if ((prod_id & 0xFFFF_0000) != 0)
            callee_map.find(DefId.fromInt(prod_id), .none)
        else
            null;
}

/// Resolves a direct or `fn_addr`/`closure_make` `async_future_make` instruction to its target `body_index`.
fn resolveAsyncFutureMakeTarget(
    cur_body: *const MirBody,
    callee_map: *const CalleeBodyIndexMap,
    inst: MirInst,
) ?u32 {
    if (inst.operands.rhs < 3 or inst.operands.lhs + inst.operands.rhs > cur_body.extra_args.items.len) return null;
    const args = cur_body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
    const raw_def = extractConstU32(cur_body, args[0]) orelse DefId.NONE.asInt();
    const raw_sym = extractConstU32(cur_body, args[1]) orelse SymbolIndex.none.asInt();
    var target_idx = callee_map.find(DefId.fromInt(raw_def), SymbolIndex.fromInt(raw_sym));
    if (target_idx == null and args[2] < cur_body.insts.len) {
        const cal_inst = cur_body.insts.get(args[2]);
        if (cal_inst.op == .fn_addr) {
            target_idx = callee_map.find(
                DefId.fromInt(cal_inst.operands.lhs),
                SymbolIndex.fromInt(cal_inst.operands.rhs),
            );
        } else if (cal_inst.op == .aggregate_make and
            @as(AggregateKind, @fromBackingInt(@intCast(@as(u8, @truncate(cal_inst.aux_u16))))) == .closure_make)
        {
            target_idx = callee_map.find(DefId.fromInt(cal_inst.operands.lhs), .none);
        }
    }
    return target_idx;
}

/// Traces `root_val` backward through SSA copies, locals, and synchronous helper returns (`depth <= 8`).
fn traceAwaitedValueToAsyncCallees(
    allocator: std.mem.Allocator,
    cur_body: *const MirBody,
    bodies: []const MirBody,
    callee_map: *const CalleeBodyIndexMap,
    pool: *const InternPool,
    root_val: u32,
    wrapper_depth: u8,
    callee_list: *std.ArrayListUnmanaged(u32),
    seen_callees: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    if (root_val >= cur_body.insts.len) return;

    var worklist: std.ArrayListUnmanaged(u32) = .empty;
    defer worklist.deinit(allocator);
    var visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited.deinit(allocator);
    try worklist.append(allocator, root_val);

    var step_count: usize = 0;
    while (worklist.pop()) |val_raw| {
        if (val_raw >= cur_body.insts.len or step_count >= 64) continue;
        if ((try visited.getOrPut(allocator, val_raw)).found_existing) continue;
        step_count += 1;

        const inst = cur_body.insts.get(val_raw);
        if (resolveFutureProducerBodyIndex(
            callee_map,
            pool.getFutureProducerId(pool.unwrapUnderlyingType(inst.type_id)),
        )) |prod_b_idx| {
            try appendUniqueAsyncCallee(allocator, bodies, callee_list, seen_callees, prod_b_idx);
        }

        switch (inst.op) {
            .copy_val, .unary_op => {
                if (inst.operands.lhs < cur_body.insts.len) {
                    try worklist.append(allocator, inst.operands.lhs);
                }
            },
            .intrinsic_op => {
                if (@as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .async_future_make) {
                    if (resolveAsyncFutureMakeTarget(cur_body, callee_map, inst)) |target_b_idx| {
                        try appendUniqueAsyncCallee(allocator, bodies, callee_list, seen_callees, target_b_idx);
                    }
                }
            },
            .place_load => {
                if (inst.operands.lhs < cur_body.places.items.len) {
                    const target_base = cur_body.places.items[inst.operands.lhs].base;
                    for (0..cur_body.insts.len) |scan_i| {
                        const scan_inst = cur_body.insts.get(scan_i);
                        if (scan_inst.op == .place_store and
                            scan_inst.operands.lhs < cur_body.places.items.len and
                            cur_body.places.items[scan_inst.operands.lhs].base == target_base)
                        {
                            try worklist.append(allocator, scan_inst.operands.rhs);
                        }
                    }
                }
            },
            .block_param => {
                const owner_bb = inst.operands.lhs;
                const param_ord = inst.operands.rhs;
                for (cur_body.extra_edges.items, 0..) |edge, edge_idx| {
                    if (edge.target_bb.asInt() != owner_bb or edge.src_bb.asInt() >= cur_body.blocks.items.len) {
                        continue;
                    }
                    const src_term = cur_body.blocks.items[edge.src_bb.asInt()].terminator;
                    if (src_term.kind != .call and src_term.kind != .coro_suspend and param_ord < edge.args_len) {
                        try worklist.append(allocator, cur_body.extra_args.items[edge.args_start + param_ord]);
                    } else if (src_term.kind == .call and
                        param_ord == 0 and
                        edge_idx == src_term.edge_start and
                        src_term.cond_or_val < cur_body.calls.items.len)
                    {
                        const csite = cur_body.calls.items[src_term.cond_or_val];
                        var helper_idx = callee_map.find(csite.direct_def_id, csite.direct_symbol);
                        if (helper_idx == null and !csite.callee_val.isNone() and
                            csite.callee_val.asInt() < cur_body.insts.len)
                        {
                            const cal_inst = cur_body.insts.get(csite.callee_val.asInt());
                            if (cal_inst.op == .fn_addr) {
                                helper_idx = callee_map.find(
                                    DefId.fromInt(cal_inst.operands.lhs),
                                    SymbolIndex.fromInt(cal_inst.operands.rhs),
                                );
                            } else if (cal_inst.op == .aggregate_make and
                                @as(AggregateKind, @fromBackingInt(@intCast(@as(u8, @truncate(cal_inst.aux_u16))))) == .closure_make)
                            {
                                helper_idx = callee_map.find(DefId.fromInt(cal_inst.operands.lhs), .none);
                            }
                        }
                        if (helper_idx) |cal_b_idx| {
                            if (bodies[cal_b_idx].is_async) {
                                try appendUniqueAsyncCallee(allocator, bodies, callee_list, seen_callees, cal_b_idx);
                            } else if (wrapper_depth < MAX_SYNC_WRAPPER_DEPTH) {
                                const helper_body = &bodies[cal_b_idx];
                                for (helper_body.blocks.items) |h_bb| {
                                    if (h_bb.terminator.kind != .ret) continue;
                                    if (h_bb.terminator.cond_or_val < helper_body.insts.len) {
                                        try traceAwaitedValueToAsyncCallees(
                                            allocator,
                                            helper_body,
                                            bodies,
                                            callee_map,
                                            pool,
                                            h_bb.terminator.cond_or_val,
                                            wrapper_depth + 1,
                                            callee_list,
                                            seen_callees,
                                        );
                                    } else if (h_bb.terminator.cond_or_val == mir.NONE_U32) {
                                        for (0..helper_body.insts.len) |h_inst_i| {
                                            const h_inst = helper_body.insts.get(h_inst_i);
                                            if (h_inst.op == .place_store and
                                                h_inst.operands.lhs < helper_body.places.items.len and
                                                helper_body.places.items[h_inst.operands.lhs].base == 0)
                                            {
                                                try traceAwaitedValueToAsyncCallees(
                                                    allocator,
                                                    helper_body,
                                                    bodies,
                                                    callee_map,
                                                    pool,
                                                    h_inst.operands.rhs,
                                                    wrapper_depth + 1,
                                                    callee_list,
                                                    seen_callees,
                                                );
                                            }
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
}

/// Collects statically resolvable `is_async` callee `body_index` targets constructed or awaited in `body`.
fn collectAwaitedCalleesForBody(
    allocator: std.mem.Allocator,
    body: *const MirBody,
    bodies: []const MirBody,
    callee_map: *const CalleeBodyIndexMap,
    pool: *const InternPool,
) ![]u32 {
    var callee_list: std.ArrayListUnmanaged(u32) = .empty;
    errdefer callee_list.deinit(allocator);
    var seen_callees: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer seen_callees.deinit(allocator);

    for (body.blocks.items) |blk_rec| {
        for (0..blk_rec.inst_len) |inst_k| {
            const inst = body.insts.get(body.block_insts.items[blk_rec.inst_start + inst_k].asInt());
            if (inst.op == .intrinsic_op and
                @as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .async_future_make)
            {
                if (resolveAsyncFutureMakeTarget(body, callee_map, inst)) |b_idx| {
                    try appendUniqueAsyncCallee(allocator, bodies, &callee_list, &seen_callees, b_idx);
                }
            }
        }
        if (blk_rec.terminator.kind == .coro_suspend and blk_rec.terminator.cond_or_val < body.insts.len) {
            try traceAwaitedValueToAsyncCallees(
                allocator,
                body,
                bodies,
                callee_map,
                pool,
                blk_rec.terminator.cond_or_val,
                0,
                &callee_list,
                &seen_callees,
            );
            if (resolveFutureProducerBodyIndex(
                callee_map,
                pool.getFutureProducerId(pool.unwrapUnderlyingType(body.insts.get(blk_rec.terminator.cond_or_val).type_id)),
            )) |b_idx| {
                try appendUniqueAsyncCallee(allocator, bodies, &callee_list, &seen_callees, b_idx);
            }
        }
    }
    return callee_list.toOwnedSlice(allocator);
}

/// DFS post-order walk computing transitive inline child subtree sizes and detecting unboxed cycles (`E0317`).
fn computeSubtreeFrameBytesDfs(
    body_idx: u32,
    plans: []AsyncBodyPlan,
    visit_state: []u8,
    inline_subtree_bytes: []u32,
) u32 {
    if (visit_state[body_idx] == 2) return inline_subtree_bytes[body_idx];
    if (visit_state[body_idx] == 1) {
        plans[body_idx].has_unboxed_recursion = true;
        return ASYNC_INLINE_FRAME_CAP_BYTES + 1;
    }
    visit_state[body_idx] = 1;

    var max_callee_subtree: u32 = 0;
    for (plans[body_idx].awaited_callees) |callee_idx| {
        const sub_bytes = computeSubtreeFrameBytesDfs(callee_idx, plans, visit_state, inline_subtree_bytes);
        if (plans[callee_idx].has_unboxed_recursion or callee_idx == body_idx) {
            plans[body_idx].has_unboxed_recursion = true;
        }
        if (sub_bytes > max_callee_subtree) max_callee_subtree = sub_bytes;
    }

    const effective_child = @max(plans[body_idx].frame_layout.max_child_bytes, max_callee_subtree);
    const own_prefix = plans[body_idx].frame_layout.header_bytes + plans[body_idx].frame_layout.colored_locals_bytes;
    const total_sub = alignUpU32(own_prefix +| effective_child, plans[body_idx].frame_align);
    if (total_sub > ASYNC_INLINE_FRAME_CAP_BYTES or plans[body_idx].has_unboxed_recursion) {
        plans[body_idx].has_exceeded_inline_cap = true;
    }
    inline_subtree_bytes[body_idx] = total_sub;
    visit_state[body_idx] = 2;
    return total_sub;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Demotes all cross-block SSA values in an `is_async` `MirBody` into `LocalDecl` frame slots so
/// state-machine entry dispatch preserves SSA dominance across LLVM, C99, and `MirVm`.
pub fn demoteCrossSuspendSsaValues(
    allocator: std.mem.Allocator,
    body: *MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
) !void {
    if (!body.is_async or body.blocks.items.len <= 1 or body.insts.len == 0) return;

    const orig_inst_len = body.insts.len;
    const def_bb_of_val = try allocator.alloc(u32, orig_inst_len);
    defer allocator.free(def_bb_of_val);
    @memset(def_bb_of_val, mir.NONE_U32);

    for (body.blocks.items, 0..) |blk_rec, bb_i| {
        const bb_u32: u32 = @intCast(bb_i);
        const p_len: usize = blk_rec.paramLen();
        for (0..p_len) |param_k| {
            const p_vid = body.block_params.items[blk_rec.param_start + param_k];
            if (p_vid.asInt() < orig_inst_len) def_bb_of_val[p_vid.asInt()] = bb_u32;
        }
        for (0..blk_rec.inst_len) |inst_k| {
            const inst_vid = body.block_insts.items[blk_rec.inst_start + inst_k];
            if (inst_vid.asInt() < orig_inst_len) def_bb_of_val[inst_vid.asInt()] = bb_u32;
        }
    }

    // [1] Identify every SSA value referenced outside its defining basic block:
    const is_demote_needed = try allocator.alloc(bool, orig_inst_len);
    defer allocator.free(is_demote_needed);
    @memset(is_demote_needed, false);

    for (body.blocks.items, 0..) |blk_rec, bb_i| {
        const bb_u32: u32 = @intCast(bb_i);
        for (0..blk_rec.inst_len) |inst_k| {
            const inst_vid = body.block_insts.items[blk_rec.inst_start + inst_k];
            const inst = body.insts.get(inst_vid.asInt());
            switch (inst.op) {
                .block_param, .const_scalar, .fn_addr => {},
                .ghost_access_let, .ghost_access_inout, .ghost_access_set => {
                    scanPlaceIndexUses(body, PlaceId.fromInt(inst.operands.lhs), bb_u32, def_bb_of_val, is_demote_needed);
                },
                .ghost_access_end => {
                    markIfCrossBlockUse(inst.operands.lhs, bb_u32, def_bb_of_val, is_demote_needed);
                },
                .ghost_storage_init, .ghost_storage_deinit => {},
                .ghost_storage_move,
                .place_load,
                .place_discriminant,
                .place_set_discrim,
                .place_addr,
                .soa_column_slice,
                => {
                    scanPlaceIndexUses(body, PlaceId.fromInt(inst.operands.lhs), bb_u32, def_bb_of_val, is_demote_needed);
                },
                .place_store => {
                    scanPlaceIndexUses(body, PlaceId.fromInt(inst.operands.lhs), bb_u32, def_bb_of_val, is_demote_needed);
                    markIfCrossBlockUse(inst.operands.rhs, bb_u32, def_bb_of_val, is_demote_needed);
                },
                .copy_val, .unary_op, .aggregate_extract, .bitfield_extract => {
                    markIfCrossBlockUse(inst.operands.lhs, bb_u32, def_bb_of_val, is_demote_needed);
                },
                .bin_op => {
                    markIfCrossBlockUse(inst.operands.lhs, bb_u32, def_bb_of_val, is_demote_needed);
                    markIfCrossBlockUse(inst.operands.rhs, bb_u32, def_bb_of_val, is_demote_needed);
                },
                .aggregate_make => {
                    const akind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    switch (akind) {
                        .array_repeat => markIfCrossBlockUse(inst.operands.lhs, bb_u32, def_bb_of_val, is_demote_needed),
                        .closure_make => {
                            const cap_len = body.extra_args.items[inst.operands.rhs];
                            for (0..cap_len) |cap_i| {
                                markIfCrossBlockUse(
                                    body.extra_args.items[inst.operands.rhs + 1 + cap_i],
                                    bb_u32,
                                    def_bb_of_val,
                                    is_demote_needed,
                                );
                            }
                        },
                        .tagged_variant => {
                            const extra_len = inst.operands.rhs & 0xFFFF;
                            for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + extra_len]) |word_val| {
                                markIfCrossBlockUse(word_val, bb_u32, def_bb_of_val, is_demote_needed);
                            }
                        },
                        .tuple_agg, .struct_agg, .array_elems, .str_concat, .fmt_args_make => {
                            for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |word_val| {
                                markIfCrossBlockUse(word_val, bb_u32, def_bb_of_val, is_demote_needed);
                            }
                        },
                    }
                },
                .aggregate_insert => {
                    markIfCrossBlockUse(inst.operands.lhs, bb_u32, def_bb_of_val, is_demote_needed);
                    markIfCrossBlockUse(body.extra_args.items[inst.operands.rhs + 1], bb_u32, def_bb_of_val, is_demote_needed);
                },
                .bitfield_insert => {
                    markIfCrossBlockUse(body.extra_args.items[inst.operands.lhs], bb_u32, def_bb_of_val, is_demote_needed);
                    markIfCrossBlockUse(body.extra_args.items[inst.operands.lhs + 1], bb_u32, def_bb_of_val, is_demote_needed);
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    if (ikind.hasPlaceInLhs()) {
                        scanPlaceIndexUses(body, PlaceId.fromInt(inst.operands.lhs), bb_u32, def_bb_of_val, is_demote_needed);
                        if (ikind.hasSsaFlagInRhs()) {
                            markIfCrossBlockUse(inst.operands.rhs, bb_u32, def_bb_of_val, is_demote_needed);
                        }
                    } else if (ikind.hasExtraArgs()) {
                        for (body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]) |word_val| {
                            markIfCrossBlockUse(word_val, bb_u32, def_bb_of_val, is_demote_needed);
                        }
                    }
                },
            }
        }

        const term = blk_rec.terminator;
        switch (term.kind) {
            .ret => {
                if (term.cond_or_val != mir.NONE_U32) {
                    markIfCrossBlockUse(term.cond_or_val, bb_u32, def_bb_of_val, is_demote_needed);
                }
            },
            .cond_br, .switch_int, .coro_suspend => {
                markIfCrossBlockUse(term.cond_or_val, bb_u32, def_bb_of_val, is_demote_needed);
            },
            .call => {
                const csite = body.calls.items[term.cond_or_val];
                if (!csite.callee_val.isNone()) {
                    markIfCrossBlockUse(csite.callee_val.asInt(), bb_u32, def_bb_of_val, is_demote_needed);
                }
                for (0..csite.args_len) |arg_i| {
                    const mode = body.call_arg_modes.items[csite.modes_start + arg_i];
                    const word = body.extra_args.items[csite.args_start + arg_i];
                    if (mode == .inout_mode or mode == .set_mode) {
                        scanPlaceIndexUses(body, PlaceId.fromInt(word), bb_u32, def_bb_of_val, is_demote_needed);
                    } else {
                        markIfCrossBlockUse(word, bb_u32, def_bb_of_val, is_demote_needed);
                    }
                }
            },
            .unreachable_term, .br, .trap => {},
        }
        for (0..term.edge_len) |edge_k| {
            const edge = body.extra_edges.items[term.edge_start + edge_k];
            for (0..edge.args_len) |ea_i| {
                markIfCrossBlockUse(body.extra_args.items[edge.args_start + ea_i], bb_u32, def_bb_of_val, is_demote_needed);
            }
        }
    }

    var has_any_demote = false;
    for (is_demote_needed) |flag| {
        if (flag) {
            has_any_demote = true;
            break;
        }
    }
    if (!has_any_demote) return;

    // [2] Allocate spill `LocalDecl` + unprojected `MirPlace` for non-ZST, non-const demoted values:
    const spill_places = try allocator.alloc(PlaceId, orig_inst_len);
    defer allocator.free(spill_places);
    @memset(spill_places, .none);

    for (0..orig_inst_len) |val_i| {
        if (!is_demote_needed[val_i]) continue;
        const inst = body.insts.get(val_i);
        if (inst.op.isGhost() or inst.op == .const_scalar or inst.op == .fn_addr) continue;
        if (type_system.computeTypeLayoutWithPool(pool, sym_table, inst.type_id, body.target_layout).byte_size == 0) {
            continue;
        }

        const tok = if (val_i < body.origin_tokens.items.len) body.origin_tokens.items[val_i] else TokenIndex.none;
        const spill_lid = LocalId.fromInt(@intCast(body.locals.items.len));
        try body.locals.append(
            body.allocator,
            LocalDecl.init(.empty, inst.type_id, tok, 0, .let_mode, .{
                .is_mut = true,
                .is_synthetic_temp = true,
            }),
        );
        if (body.local_scope_depths.items.len > 0) {
            try body.local_scope_depths.append(body.allocator, 1);
        }
        const spill_pid = PlaceId.fromInt(@intCast(body.places.items.len));
        try body.places.append(body.allocator, .{ .base = spill_lid.asInt(), .proj_start = 0, .proj_len = 0 });
        spill_places[val_i] = spill_pid;
    }

    // [3] Rebuild `block_insts` per block with immediate spill stores & localized per-block reloads:
    var new_block_insts: std.ArrayListUnmanaged(MirValueId) = .empty;
    errdefer new_block_insts.deinit(body.allocator);
    var block_reload_cache: std.AutoHashMapUnmanaged(u32, MirValueId) = .empty;
    defer block_reload_cache.deinit(body.allocator);

    for (body.blocks.items, 0..) |*blk_ptr, bb_i| {
        const bb_u32: u32 = @intCast(bb_i);
        block_reload_cache.clearRetainingCapacity();
        const new_start: u32 = @intCast(new_block_insts.items.len);

        // Spill any `block_param` of `bb_i` that is read outside `bb_i`:
        const p_len: usize = blk_ptr.paramLen();
        for (0..p_len) |param_k| {
            const p_vid = body.block_params.items[blk_ptr.param_start + param_k];
            if (p_vid.asInt() < orig_inst_len and !spill_places[p_vid.asInt()].isNone()) {
                const p_tok = if (p_vid.asInt() < body.origin_tokens.items.len)
                    body.origin_tokens.items[p_vid.asInt()]
                else
                    TokenIndex.none;
                _ = try appendSynthInstToList(body, &new_block_insts, .{
                    .op = .place_store,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = spill_places[p_vid.asInt()].asInt(), .rhs = p_vid.asInt() },
                }, p_tok);
            }
        }

        const old_start = blk_ptr.inst_start;
        const old_len = blk_ptr.inst_len;
        for (0..old_len) |inst_k| {
            const inst_vid = body.block_insts.items[old_start + inst_k];
            const val_raw = inst_vid.asInt();
            var inst = body.insts.get(val_raw);
            const tok = if (val_raw < body.origin_tokens.items.len) body.origin_tokens.items[val_raw] else .none;

            switch (inst.op) {
                .block_param, .const_scalar, .fn_addr, .ghost_storage_init, .ghost_storage_deinit => {},
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
                    const new_pid = try rewritePlaceIndexUses(
                        body,
                        PlaceId.fromInt(inst.operands.lhs),
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    inst.operands.lhs = new_pid.asInt();
                },
                .ghost_access_end => {},
                .place_store => {
                    const new_pid = try rewritePlaceIndexUses(
                        body,
                        PlaceId.fromInt(inst.operands.lhs),
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    const new_rhs = try reloadOrRematValueInBlock(
                        body,
                        inst.operands.rhs,
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    inst.operands.lhs = new_pid.asInt();
                    inst.operands.rhs = new_rhs.asInt();
                },
                .copy_val, .unary_op, .aggregate_extract, .bitfield_extract => {
                    const new_lhs = try reloadOrRematValueInBlock(
                        body,
                        inst.operands.lhs,
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    inst.operands.lhs = new_lhs.asInt();
                },
                .bin_op => {
                    const new_lhs = try reloadOrRematValueInBlock(
                        body,
                        inst.operands.lhs,
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    const new_rhs = try reloadOrRematValueInBlock(
                        body,
                        inst.operands.rhs,
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    inst.operands.lhs = new_lhs.asInt();
                    inst.operands.rhs = new_rhs.asInt();
                },
                .aggregate_make => {
                    const akind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                    if (akind == .array_repeat) {
                        const new_lhs = try reloadOrRematValueInBlock(
                            body,
                            inst.operands.lhs,
                            bb_u32,
                            def_bb_of_val,
                            spill_places,
                            pool,
                            sym_table,
                            &block_reload_cache,
                            &new_block_insts,
                            tok,
                        );
                        inst.operands.lhs = new_lhs.asInt();
                    } else if (akind == .closure_make) {
                        const cap_len = body.extra_args.items[inst.operands.rhs];
                        for (0..cap_len) |cap_i| {
                            const old_w = body.extra_args.items[inst.operands.rhs + 1 + cap_i];
                            const new_w = try reloadOrRematValueInBlock(
                                body,
                                old_w,
                                bb_u32,
                                def_bb_of_val,
                                spill_places,
                                pool,
                                sym_table,
                                &block_reload_cache,
                                &new_block_insts,
                                tok,
                            );
                            body.extra_args.items[inst.operands.rhs + 1 + cap_i] = new_w.asInt();
                        }
                    } else {
                        const extra_len = if (akind == .tagged_variant) inst.operands.rhs & 0xFFFF else inst.operands.rhs;
                        for (0..extra_len) |elem_i| {
                            const old_w = body.extra_args.items[inst.operands.lhs + elem_i];
                            const new_w = try reloadOrRematValueInBlock(
                                body,
                                old_w,
                                bb_u32,
                                def_bb_of_val,
                                spill_places,
                                pool,
                                sym_table,
                                &block_reload_cache,
                                &new_block_insts,
                                tok,
                            );
                            body.extra_args.items[inst.operands.lhs + elem_i] = new_w.asInt();
                        }
                    }
                },
                .aggregate_insert => {
                    const new_lhs = try reloadOrRematValueInBlock(
                        body,
                        inst.operands.lhs,
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    const new_ins = try reloadOrRematValueInBlock(
                        body,
                        body.extra_args.items[inst.operands.rhs + 1],
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        tok,
                    );
                    inst.operands.lhs = new_lhs.asInt();
                    body.extra_args.items[inst.operands.rhs + 1] = new_ins.asInt();
                },
                .bitfield_insert => {
                    for (0..2) |pair_i| {
                        const old_w = body.extra_args.items[inst.operands.lhs + pair_i];
                        const new_w = try reloadOrRematValueInBlock(
                            body,
                            old_w,
                            bb_u32,
                            def_bb_of_val,
                            spill_places,
                            pool,
                            sym_table,
                            &block_reload_cache,
                            &new_block_insts,
                            tok,
                        );
                        body.extra_args.items[inst.operands.lhs + pair_i] = new_w.asInt();
                    }
                },
                .intrinsic_op => {
                    const ikind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                    if (ikind.hasPlaceInLhs()) {
                        const new_pid = try rewritePlaceIndexUses(
                            body,
                            PlaceId.fromInt(inst.operands.lhs),
                            bb_u32,
                            def_bb_of_val,
                            spill_places,
                            pool,
                            sym_table,
                            &block_reload_cache,
                            &new_block_insts,
                            tok,
                        );
                        inst.operands.lhs = new_pid.asInt();
                        if (ikind.hasSsaFlagInRhs()) {
                            const new_flag = try reloadOrRematValueInBlock(
                                body,
                                inst.operands.rhs,
                                bb_u32,
                                def_bb_of_val,
                                spill_places,
                                pool,
                                sym_table,
                                &block_reload_cache,
                                &new_block_insts,
                                tok,
                            );
                            inst.operands.rhs = new_flag.asInt();
                        }
                    } else if (ikind.hasExtraArgs()) {
                        for (0..inst.operands.rhs) |arg_i| {
                            const old_w = body.extra_args.items[inst.operands.lhs + arg_i];
                            const new_w = try reloadOrRematValueInBlock(
                                body,
                                old_w,
                                bb_u32,
                                def_bb_of_val,
                                spill_places,
                                pool,
                                sym_table,
                                &block_reload_cache,
                                &new_block_insts,
                                tok,
                            );
                            body.extra_args.items[inst.operands.lhs + arg_i] = new_w.asInt();
                        }
                    }
                },
            }

            body.insts.set(val_raw, inst);
            try new_block_insts.append(body.allocator, inst_vid);

            if (val_raw < orig_inst_len and !spill_places[val_raw].isNone()) {
                _ = try appendSynthInstToList(body, &new_block_insts, .{
                    .op = .place_store,
                    .flags = .{ .has_side_effects = true, .is_synthetic = true },
                    .type_id = .unit_ty,
                    .operands = .{ .lhs = spill_places[val_raw].asInt(), .rhs = val_raw },
                }, tok);
            }
        }

        // Rewrite terminator & outgoing edge SSA operands in `bb_i`:
        var term = blk_ptr.terminator;
        switch (term.kind) {
            .ret => {
                if (term.cond_or_val != mir.NONE_U32) {
                    const mapped = try reloadOrRematValueInBlock(
                        body,
                        term.cond_or_val,
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        .none,
                    );
                    term.cond_or_val = mapped.asInt();
                }
            },
            .cond_br, .switch_int, .coro_suspend => {
                const mapped = try reloadOrRematValueInBlock(
                    body,
                    term.cond_or_val,
                    bb_u32,
                    def_bb_of_val,
                    spill_places,
                    pool,
                    sym_table,
                    &block_reload_cache,
                    &new_block_insts,
                    .none,
                );
                term.cond_or_val = mapped.asInt();
            },
            .call => {
                var csite = body.calls.items[term.cond_or_val];
                if (!csite.callee_val.isNone()) {
                    csite.callee_val = try reloadOrRematValueInBlock(
                        body,
                        csite.callee_val.asInt(),
                        bb_u32,
                        def_bb_of_val,
                        spill_places,
                        pool,
                        sym_table,
                        &block_reload_cache,
                        &new_block_insts,
                        csite.origin_token,
                    );
                }
                for (0..csite.args_len) |arg_i| {
                    const mode = body.call_arg_modes.items[csite.modes_start + arg_i];
                    const old_w = body.extra_args.items[csite.args_start + arg_i];
                    if (mode == .inout_mode or mode == .set_mode) {
                        const new_pid = try rewritePlaceIndexUses(
                            body,
                            PlaceId.fromInt(old_w),
                            bb_u32,
                            def_bb_of_val,
                            spill_places,
                            pool,
                            sym_table,
                            &block_reload_cache,
                            &new_block_insts,
                            csite.origin_token,
                        );
                        body.extra_args.items[csite.args_start + arg_i] = new_pid.asInt();
                    } else {
                        const new_v = try reloadOrRematValueInBlock(
                            body,
                            old_w,
                            bb_u32,
                            def_bb_of_val,
                            spill_places,
                            pool,
                            sym_table,
                            &block_reload_cache,
                            &new_block_insts,
                            csite.origin_token,
                        );
                        body.extra_args.items[csite.args_start + arg_i] = new_v.asInt();
                    }
                }
                body.calls.items[term.cond_or_val] = csite;
            },
            .unreachable_term, .br, .trap => {},
        }
        for (0..term.edge_len) |edge_k| {
            const edge = body.extra_edges.items[term.edge_start + edge_k];
            for (0..edge.args_len) |ea_i| {
                const old_w = body.extra_args.items[edge.args_start + ea_i];
                const new_v = try reloadOrRematValueInBlock(
                    body,
                    old_w,
                    bb_u32,
                    def_bb_of_val,
                    spill_places,
                    pool,
                    sym_table,
                    &block_reload_cache,
                    &new_block_insts,
                    .none,
                );
                body.extra_args.items[edge.args_start + ea_i] = new_v.asInt();
            }
        }
        blk_ptr.terminator = term;
        blk_ptr.inst_start = new_start;
        blk_ptr.inst_len = @intCast(new_block_insts.items.len - new_start);
    }

    body.block_insts.deinit(body.allocator);
    body.block_insts = new_block_insts;
}

/// Returns `true` if `body` is `is_async` or invokes any async intrinsic (`44..51`) or `.coro_suspend`.
pub fn hasBodyAsyncOperations(body: *const MirBody) bool {
    if (body.is_async) return true;
    for (body.blocks.items) |blk_rec| {
        if (blk_rec.terminator.kind == .coro_suspend) return true;
        for (0..blk_rec.inst_len) |inst_k| {
            const inst = body.insts.get(body.block_insts.items[blk_rec.inst_start + inst_k].asInt());
            if (inst.op == .intrinsic_op and
                inst.aux_u16 >= FIRST_ASYNC_INTRINSIC and
                inst.aux_u16 <= LAST_ASYNC_INTRINSIC)
            {
                return true;
            }
        }
    }
    return false;
}

/// Computes the exact liveness-colored `AsyncBodyPlan` (`CoroFrameLayout`, `CoroLocalSlot`s, and
/// `SuspendPointMeta`s) for a single `MirBody` (`DR-08` §2–§3).
pub fn analyzeAsyncBody(
    allocator: std.mem.Allocator,
    body_index: u32,
    body: *const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
) !AsyncBodyPlan {
    if (!body.is_async) {
        return .{
            .body_index = body_index,
            .is_async = false,
            .frame_align = target_layout.ptrAlignBytes(),
        };
    }

    const ptr_align = target_layout.ptrAlignBytes();
    var max_align: u32 = @max(ptr_align, 8);
    var ctx_override_mask: u16 = 0;

    // [1] Index all `.coro_suspend` points and `closure_make` environments in `body`:
    var suspends: std.ArrayListUnmanaged(SuspendPointMeta) = .empty;
    errdefer suspends.deinit(allocator);
    var suspend_fut_tys: std.ArrayListUnmanaged(TypeId) = .empty;
    errdefer suspend_fut_tys.deinit(allocator);
    var suspend_ready_tys: std.ArrayListUnmanaged(TypeId) = .empty;
    errdefer suspend_ready_tys.deinit(allocator);
    var suspend_block_map: std.AutoHashMapUnmanaged(u32, usize) = .empty;
    errdefer suspend_block_map.deinit(allocator);

    const local_count = body.locals.items.len;
    const is_pinned_local = try allocator.alloc(bool, local_count);
    defer allocator.free(is_pinned_local);
    @memset(is_pinned_local, false);
    for (body.locals.items, 0..) |loc_decl, loc_i| {
        if (loc_i == 0 or (loc_i <= body.param_count) or loc_decl.flags().is_address_taken) {
            is_pinned_local[loc_i] = true;
        }
    }

    var raw_closure_envs: std.ArrayListUnmanaged(RawClosureEnv) = .empty;
    defer raw_closure_envs.deinit(allocator);

    var max_child_fut_bytes: u32 = 0;
    var max_child_fut_align: u32 = ptr_align;

    for (body.blocks.items, 0..) |blk_rec, bb_i| {
        for (0..blk_rec.inst_len) |inst_k| {
            const inst_vid = body.block_insts.items[blk_rec.inst_start + inst_k];
            const inst = body.insts.get(inst_vid.asInt());
            if (inst.op == .place_addr) {
                const pid = PlaceId.fromInt(inst.operands.lhs);
                if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                    const base_loc = body.places.items[pid.asInt()].base;
                    if (base_loc < local_count) is_pinned_local[base_loc] = true;
                }
            } else if (inst.op == .intrinsic_op) {
                if (@as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == .ctx_set and inst.operands.rhs >= 1) {
                    if (extractConstU32(body, body.extra_args.items[inst.operands.lhs])) |slot_ord| {
                        if (slot_ord < CORO_CTX_SLOT_COUNT) {
                            ctx_override_mask |= @as(u16, 1) << @intCast(slot_ord);
                        }
                    }
                }
            } else if (inst.op == .aggregate_make and
                @as(AggregateKind, @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))))) == .closure_make)
            {
                const is_three_word = if (pool.getFnSignatureView(pool.unwrapUnderlyingType(inst.type_id))) |sv|
                    (sv.capture_tier != .copy_tier or sv.has_linear_capture)
                else
                    false;
                if (!is_three_word) {
                    const cap_len = body.extra_args.items[inst.operands.rhs];
                    var env_sz: u32 = 0;
                    var env_al: u32 = ptr_align;
                    for (0..cap_len) |cap_i| {
                        const cap_lay = type_system.computeTypeLayoutWithPool(
                            pool,
                            sym_table,
                            body.insts.get(body.extra_args.items[inst.operands.rhs + 1 + cap_i]).type_id,
                            target_layout,
                        );
                        if (cap_lay.byte_size == 0) continue;
                        env_al = @max(env_al, cap_lay.align_bytes);
                        env_sz = alignUpU32(env_sz, cap_lay.align_bytes) + @as(u32, @intCast(cap_lay.byte_size));
                    }
                    if (env_sz > 0) {
                        max_align = @max(max_align, env_al);
                        try raw_closure_envs.append(allocator, .{
                            .inst_val_id = inst_vid.asInt(),
                            .byte_size = env_sz,
                            .align_bytes = env_al,
                        });
                    }
                }
            }
        }

        const term = blk_rec.terminator;
        if (term.kind == .call and term.cond_or_val < body.calls.items.len) {
            const csite = body.calls.items[term.cond_or_val];
            for (0..csite.args_len) |arg_i| {
                const mode = body.call_arg_modes.items[csite.modes_start + arg_i];
                if (mode == .inout_mode or mode == .set_mode) {
                    const pid = PlaceId.fromInt(body.extra_args.items[csite.args_start + arg_i]);
                    if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                        const base_loc = body.places.items[pid.asInt()].base;
                        if (base_loc < local_count) is_pinned_local[base_loc] = true;
                    }
                }
            }
        } else if (term.kind == .coro_suspend and term.edge_len >= 2) {
            const resume_bb = body.extra_edges.items[term.edge_start].target_bb;
            const cancel_bb = body.extra_edges.items[term.edge_start + 1].target_bb;
            const fut_ty = if (term.cond_or_val < body.insts.len)
                pool.unwrapUnderlyingType(body.insts.get(term.cond_or_val).type_id)
            else
                TypeId.unit_ty;
            const ready_ty = if (pool.getFutureOutputType(fut_ty)) |out_t|
                pool.unwrapUnderlyingType(out_t)
            else if (resume_bb.asInt() < body.blocks.items.len and body.blocks.items[resume_bb.asInt()].paramLen() >= 1)
                body.insts.get(body.block_params.items[body.blocks.items[resume_bb.asInt()].param_start].asInt()).type_id
            else
                TypeId.unit_ty;
            const fut_lay = type_system.computeTypeLayoutWithPool(pool, sym_table, fut_ty, target_layout);
            const fut_sz: u32 = @max(@as(u32, @intCast(fut_lay.byte_size)), @as(u32, target_layout.ptr_byte_size) * 4);
            const fut_al: u32 = @max(fut_lay.align_bytes, ptr_align);
            max_child_fut_bytes = @max(max_child_fut_bytes, fut_sz);
            max_child_fut_align = @max(max_child_fut_align, fut_al);
            max_align = @max(max_align, fut_al);

            const sp_ord: u32 = @intCast(suspends.items.len);
            const gop_sp = try suspend_block_map.getOrPut(allocator, @intCast(bb_i));
            if (!gop_sp.found_existing) gop_sp.value_ptr.* = sp_ord;
            try suspends.append(allocator, .{
                .suspend_block = MirBlockId.fromInt(@intCast(bb_i)),
                .resume_block = resume_bb,
                .cancel_block = cancel_bb,
                .state_tag = CoroStateTag.fromSuspendIndex(sp_ord).asInt(),
                .child_frame_offset = 0,
                .child_frame_bytes = fut_sz,
            });
            try suspend_fut_tys.append(allocator, fut_ty);
            try suspend_ready_tys.append(allocator, ready_ty);
        }
    }

    // [2] Reverse-dataflow local liveness & pairwise interference graph construction:
    const block_count = body.blocks.items.len;
    const words_per_row: usize = (local_count + 63) / 64;
    const live_in = try allocator.alloc(u64, block_count * words_per_row);
    defer allocator.free(live_in);
    @memset(live_in, 0);
    const live_out = try allocator.alloc(u64, block_count * words_per_row);
    defer allocator.free(live_out);
    @memset(live_out, 0);
    const conflict_matrix = try allocator.alloc(u64, local_count * words_per_row);
    defer allocator.free(conflict_matrix);
    @memset(conflict_matrix, 0);
    const scratch_row = try allocator.alloc(u64, words_per_row);
    defer allocator.free(scratch_row);

    if (local_count > 0 and block_count > 0) {
        var has_changed = true;
        while (has_changed) {
            has_changed = false;
            var rev_bb = block_count;
            while (rev_bb > 0) {
                rev_bb -= 1;
                const blk_rec = body.blocks.items[rev_bb];
                const out_row = live_out[rev_bb * words_per_row .. (rev_bb + 1) * words_per_row];
                @memset(scratch_row, 0);

                // Union `live_in` across ALL outgoing edges (including `.coro_suspend` `resume_bb` AND `cancel_bb`):
                for (0..blk_rec.terminator.edge_len) |edge_k| {
                    const succ_bb = body.extra_edges.items[blk_rec.terminator.edge_start + edge_k].target_bb.asInt();
                    if (succ_bb < block_count) {
                        const succ_in = live_in[succ_bb * words_per_row .. (succ_bb + 1) * words_per_row];
                        for (0..words_per_row) |w_i| scratch_row[w_i] |= succ_in[w_i];
                    }
                }
                // `FramePinned` locals (`_0`, args, `&x` / `&mut x`) stay live across every block so borrows never alias:
                for (0..local_count) |loc_i| {
                    if (is_pinned_local[loc_i]) _ = setBit(scratch_row, loc_i);
                }
                for (0..words_per_row) |w_i| {
                    if (out_row[w_i] != scratch_row[w_i]) {
                        out_row[w_i] = scratch_row[w_i];
                        has_changed = true;
                    }
                }

                if (blk_rec.terminator.kind == .call and blk_rec.terminator.cond_or_val < body.calls.items.len) {
                    const csite = body.calls.items[blk_rec.terminator.cond_or_val];
                    for (0..csite.args_len) |arg_i| {
                        const mode = body.call_arg_modes.items[csite.modes_start + arg_i];
                        if (mode == .inout_mode or mode == .set_mode) {
                            const pid = PlaceId.fromInt(body.extra_args.items[csite.args_start + arg_i]);
                            if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                                const base_loc = body.places.items[pid.asInt()].base;
                                if (base_loc < local_count) _ = setBit(scratch_row, base_loc);
                            }
                        }
                    }
                }

                var rev_inst = blk_rec.inst_len;
                while (rev_inst > 0) {
                    rev_inst -= 1;
                    const inst = body.insts.get(body.block_insts.items[blk_rec.inst_start + rev_inst].asInt());
                    applyBackwardInstLiveness(
                        body,
                        inst,
                        is_pinned_local,
                        scratch_row,
                        conflict_matrix,
                        words_per_row,
                    );
                }

                const in_row = live_in[rev_bb * words_per_row .. (rev_bb + 1) * words_per_row];
                for (0..words_per_row) |w_i| {
                    if (in_row[w_i] != scratch_row[w_i]) {
                        in_row[w_i] = scratch_row[w_i];
                        has_changed = true;
                    }
                }
            }
        }

        // Final backward pass recording complete pairwise conflicts against converged `live_out`:
        for (body.blocks.items, 0..) |blk_rec, bb_i| {
            @memcpy(scratch_row, live_out[bb_i * words_per_row .. (bb_i + 1) * words_per_row]);
            for (0..local_count) |loc_a| {
                if (isBitSet(scratch_row, loc_a)) {
                    addConflictsWithLiveSet(@intCast(loc_a), scratch_row, conflict_matrix, words_per_row);
                }
            }
            if (blk_rec.terminator.kind == .call and blk_rec.terminator.cond_or_val < body.calls.items.len) {
                const csite = body.calls.items[blk_rec.terminator.cond_or_val];
                for (0..csite.args_len) |arg_i| {
                    const mode = body.call_arg_modes.items[csite.modes_start + arg_i];
                    if (mode == .inout_mode or mode == .set_mode) {
                        const pid = PlaceId.fromInt(body.extra_args.items[csite.args_start + arg_i]);
                        if (!pid.isNone() and pid.asInt() < body.places.items.len) {
                            const base_loc = body.places.items[pid.asInt()].base;
                            if (base_loc < local_count) {
                                addConflictsWithLiveSet(base_loc, scratch_row, conflict_matrix, words_per_row);
                                _ = setBit(scratch_row, base_loc);
                            }
                        }
                    }
                }
            }
            var rev_inst = blk_rec.inst_len;
            while (rev_inst > 0) {
                rev_inst -= 1;
                const inst = body.insts.get(body.block_insts.items[blk_rec.inst_start + rev_inst].asInt());
                applyBackwardInstLiveness(
                    body,
                    inst,
                    is_pinned_local,
                    scratch_row,
                    conflict_matrix,
                    words_per_row,
                );
            }
        }

        // Entry parameters (`0 .. param_count`) are simultaneously live on entry:
        const entry_pinned_end = @min(@as(usize, body.param_count) + 1, local_count);
        for (0..entry_pinned_end) |loc_a| {
            for (loc_a + 1..entry_pinned_end) |loc_b| {
                _ = setBit(conflict_matrix[loc_a * words_per_row .. (loc_a + 1) * words_per_row], loc_b);
                _ = setBit(conflict_matrix[loc_b * words_per_row .. (loc_b + 1) * words_per_row], loc_a);
            }
        }
    }

    // [3] Deterministic greedy interval coloring across non-interfering `LocalDecl`s:
    var candidates: std.ArrayListUnmanaged(ColorCandidate) = .empty;
    defer candidates.deinit(allocator);
    for (body.locals.items, 0..) |loc_decl, loc_i| {
        const sz_al = computeLocalFrameSizeAndAlign(pool, sym_table, loc_decl, target_layout);
        if (sz_al.byte_size == 0) continue;
        max_align = @max(max_align, sz_al.align_bytes);
        try candidates.append(allocator, .{
            .local_id = @intCast(loc_i),
            .byte_size = sz_al.byte_size,
            .align_bytes = sz_al.align_bytes,
        });
    }
    std.mem.sort(ColorCandidate, candidates.items, {}, compareColorCandidate);

    // Pin every `is_pinned_local` against all other non-ZST locals:
    for (candidates.items, 0..) |cand_a, idx_a| {
        for (candidates.items[idx_a + 1 ..]) |cand_b| {
            if (is_pinned_local[cand_a.local_id] or is_pinned_local[cand_b.local_id]) {
                const row_a = conflict_matrix[@as(usize, cand_a.local_id) * words_per_row ..][0..words_per_row];
                const row_b = conflict_matrix[@as(usize, cand_b.local_id) * words_per_row ..][0..words_per_row];
                _ = setBit(row_a, cand_b.local_id);
                _ = setBit(row_b, cand_a.local_id);
            }
        }
    }

    const header_bytes = alignUpU32(CORO_HEADER_BYTES, max_align);
    const local_offsets = try allocator.alloc(u32, local_count);
    errdefer allocator.free(local_offsets);
    @memset(local_offsets, header_bytes);

    var placed_slots: std.ArrayListUnmanaged(CoroLocalSlot) = .empty;
    errdefer placed_slots.deinit(allocator);
    const is_placed = try allocator.alloc(bool, local_count);
    defer allocator.free(is_placed);
    @memset(is_placed, false);

    var forbidden: std.ArrayListUnmanaged(Interval) = .empty;
    defer forbidden.deinit(allocator);

    var locals_end_offset: u32 = header_bytes;
    var reused_slot_count: u32 = 0;

    for (candidates.items) |cand| {
        forbidden.clearRetainingCapacity();
        const row_words = conflict_matrix[@as(usize, cand.local_id) * words_per_row ..][0..words_per_row];
        for (placed_slots.items) |existing| {
            if (isBitSet(row_words, existing.local_or_val_id)) {
                try forbidden.append(allocator, .{
                    .start = existing.byte_offset,
                    .end = existing.byte_offset + existing.byte_size,
                });
            }
        }

        var chosen_off = alignUpU32(header_bytes, cand.align_bytes);
        scan_loop: while (true) {
            const chosen_end = chosen_off + cand.byte_size;
            for (forbidden.items) |interval| {
                if (chosen_off < interval.end and interval.start < chosen_end) {
                    chosen_off = alignUpU32(interval.end, cand.align_bytes);
                    continue :scan_loop;
                }
            }
            break;
        }

        if (chosen_off + cand.byte_size <= locals_end_offset) {
            reused_slot_count += 1;
        } else {
            locals_end_offset = chosen_off + cand.byte_size;
        }
        local_offsets[cand.local_id] = chosen_off;
        is_placed[cand.local_id] = true;
        try placed_slots.append(allocator, .{
            .local_or_val_id = cand.local_id,
            .byte_offset = chosen_off,
            .byte_size = cand.byte_size,
            .align_bytes = cand.align_bytes,
        });
    }
    std.mem.sort(CoroLocalSlot, placed_slots.items, {}, compareLocalSlotById);

    // [4] Append pinned 2-word `@local` closure environment buffers after colored locals:
    var closure_env_slots = try allocator.alloc(ClosureEnvSlot, raw_closure_envs.items.len);
    errdefer if (closure_env_slots.len > 0) allocator.free(closure_env_slots);
    var closure_env_map: std.AutoHashMapUnmanaged(u32, u32) = .empty;
    errdefer closure_env_map.deinit(allocator);
    if (raw_closure_envs.items.len > 0) {
        try closure_env_map.ensureTotalCapacity(allocator, @intCast(raw_closure_envs.items.len));
    }
    for (raw_closure_envs.items, 0..) |raw_env, env_i| {
        const env_off = alignUpU32(locals_end_offset, raw_env.align_bytes);
        locals_end_offset = env_off + raw_env.byte_size;
        closure_env_slots[env_i] = .{
            .inst_val_id = raw_env.inst_val_id,
            .byte_offset = env_off,
            .byte_size = raw_env.byte_size,
            .align_bytes = raw_env.align_bytes,
        };
        const gop_env = closure_env_map.getOrPutAssumeCapacity(raw_env.inst_val_id);
        if (!gop_env.found_existing) gop_env.value_ptr.* = env_off;
    }

    const child_offset = if (suspends.items.len > 0)
        alignUpU32(locals_end_offset, max_child_fut_align)
    else
        locals_end_offset;
    for (suspends.items) |*sp_meta| {
        sp_meta.child_frame_offset = child_offset;
    }

    const colored_locals_bytes = child_offset - header_bytes;
    const total_frame_bytes = alignUpU32(child_offset +| max_child_fut_bytes, max_align);

    return .{
        .body_index = body_index,
        .is_async = true,
        .frame_align = max_align,
        .ctx_override_mask = ctx_override_mask,
        .has_exceeded_inline_cap = total_frame_bytes > ASYNC_INLINE_FRAME_CAP_BYTES,
        .reused_slot_count = reused_slot_count,
        .frame_layout = .{
            .header_bytes = header_bytes,
            .colored_locals_bytes = colored_locals_bytes,
            .max_child_bytes = max_child_fut_bytes,
            .total_frame_bytes = total_frame_bytes,
        },
        .suspend_points = try suspends.toOwnedSlice(allocator),
        .suspend_future_types = try suspend_fut_tys.toOwnedSlice(allocator),
        .suspend_ready_types = try suspend_ready_tys.toOwnedSlice(allocator),
        .local_slots = try placed_slots.toOwnedSlice(allocator),
        .local_offsets = local_offsets,
        .closure_env_slots = closure_env_slots,
        .suspend_block_map = suspend_block_map,
        .closure_env_map = closure_env_map,
    };
}

/// Analyzes an entire `MirBody` slice (`bodies`) without mutating instructions, aggregating
/// transitive inline child sizes and emitting `E0317` when `diagnostic_sink` is provided.
pub fn analyzeAsyncModule(
    allocator: std.mem.Allocator,
    bodies: []const MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
    diagnostic_sink: ?*DiagnosticSink,
) !AsyncModulePlan {
    var has_any_async_ops = false;
    for (bodies) |*body_ptr| {
        if (hasBodyAsyncOperations(body_ptr)) {
            has_any_async_ops = true;
            break;
        }
    }
    if (!has_any_async_ops) {
        return .{
            .allocator = allocator,
            .body_plans = &.{},
            .has_any_async_ops = false,
        };
    }

    var callee_map = try CalleeBodyIndexMap.init(allocator, bodies);
    defer callee_map.deinit(allocator);

    const body_plans = try allocator.alloc(AsyncBodyPlan, bodies.len);
    var initialized_count: usize = 0;
    errdefer {
        for (body_plans[0..initialized_count]) |*plan| plan.deinit(allocator);
        if (body_plans.len > 0) allocator.free(body_plans);
    }

    for (bodies, 0..) |*body_ptr, body_i| {
        body_plans[body_i] = try analyzeAsyncBody(
            allocator,
            @intCast(body_i),
            body_ptr,
            pool,
            sym_table,
            target_layout,
        );
        if (body_ptr.is_async) {
            body_plans[body_i].awaited_callees = try collectAwaitedCalleesForBody(
                allocator,
                body_ptr,
                bodies,
                &callee_map,
                pool,
            );
        }
        initialized_count += 1;
    }

    if (bodies.len > 0) {
        const visit_state = try allocator.alloc(u8, bodies.len);
        defer allocator.free(visit_state);
        @memset(visit_state, 0);
        const inline_subtree_bytes = try allocator.alloc(u32, bodies.len);
        defer allocator.free(inline_subtree_bytes);
        @memset(inline_subtree_bytes, 0);

        for (0..bodies.len) |body_i| {
            if (!body_plans[body_i].is_async) continue;
            _ = computeSubtreeFrameBytesDfs(@intCast(body_i), body_plans, visit_state, inline_subtree_bytes);
            if (body_plans[body_i].has_exceeded_inline_cap) {
                if (diagnostic_sink) |sink| {
                    var span: mem_foundation.Span = .{
                        .file_id = bodies[body_i].file_id,
                        .start_byte = 0,
                        .end_byte = 0,
                    };
                    const sym_idx = bodies[body_i].symbol_index;
                    if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                        span = sym_table.getSymbol(sym_idx).decl_span;
                    }
                    const msg = if (body_plans[body_i].has_unboxed_recursion)
                        "unboxed recursive `async` call cycle cannot fit inside an inline coroutine frame"
                    else
                        "inline `async` coroutine frame subtree exceeds the 16 KiB (`16384` byte) cap";
                    try sink.emit(.{
                        .code = .e0317_async_inline_frame_exceeded,
                        .severity = .err,
                        .primary_span = span,
                        .message = msg,
                        .notes = &.{"box or spawn inner `Future` onto a `TaskGroup` to bound inline frame size"},
                    });
                }
            }
        }
    }

    return .{
        .allocator = allocator,
        .body_plans = body_plans,
        .has_any_async_ops = has_any_async_ops,
    };
}

/// Runs `Pass D5.5` (`demoteCrossSuspendSsaValues` + `analyzeAsyncModule`) in-place on `bodies`.
pub fn prepareAndAnalyzeAsyncModule(
    allocator: std.mem.Allocator,
    bodies: []MirBody,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    target_layout: TargetLayout,
    diagnostic_sink: ?*DiagnosticSink,
) !AsyncModulePlan {
    for (bodies) |*body_ptr| {
        if (body_ptr.is_async) {
            try demoteCrossSuspendSsaValues(allocator, body_ptr, pool, sym_table);
        }
    }
    return analyzeAsyncModule(allocator, bodies, pool, sym_table, target_layout, diagnostic_sink);
}

// ---------------------------------------- MAIN -----------------------------------------

// Enforce binary coroutine metadata byte sizes and alignments at compile time:
comptime {
    std.debug.assert(@sizeOf(SuspendPointMeta) == 24);
    std.debug.assert(@alignOf(SuspendPointMeta) == 4);
    std.debug.assert(@sizeOf(CoroLocalSlot) == 16);
    std.debug.assert(@alignOf(CoroLocalSlot) == 4);
    std.debug.assert(@sizeOf(CoroFrameLayout) == 16);
    std.debug.assert(@alignOf(CoroFrameLayout) == 4);
    std.debug.assert(@sizeOf(ClosureEnvSlot) == 16);
    std.debug.assert(@alignOf(ClosureEnvSlot) == 4);
}

test "test_mir_async_sequential_await_liveness_coloring_reuses_frame_slots" {
    const allocator = std.testing.allocator;
    var interner = try mem_foundation.StringInterner.init(allocator);
    defer interner.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();

    const arr_u8_64 = try pool.internArray(.u8_ty, 64, false);
    const fut_unit = try pool.internFuture(.unit_ty, 0);

    var body = MirBody.init(allocator, .fromInt(0), .fromInt(1));
    defer body.deinit();
    body.is_async = true;
    body.is_ghost_stripped = true;
    body.has_ghost_instructions = false;
    body.ret_ty = .u8_ty;

    // `_0` (`u8`), `_1` (`[u8; 64]` live across suspend 1), `_2` (`[u8; 64]` live across suspend 2):
    try body.locals.append(allocator, LocalDecl.init(.empty, .u8_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_return_slot = true,
    }));
    try body.locals.append(allocator, LocalDecl.init(.empty, arr_u8_64, .none, 0, .let_mode, .{ .is_mut = true }));
    try body.locals.append(allocator, LocalDecl.init(.empty, arr_u8_64, .none, 0, .let_mode, .{ .is_mut = true }));

    try body.places.append(allocator, .{ .base = 0 });
    try body.places.append(allocator, .{ .base = 1 });
    try body.places.append(allocator, .{ .base = 2 });

    const c_unit = try body.appendConst(.unit_val);
    const c_arr = try body.appendConst(.{ .int_val = 7 });

    // Five blocks; `bb0 --suspend1--> bb1 --suspend2--> bb2(ret)` + `bb3(cancel1)` + `bb4(cancel2)`:
    for (0..5) |bb_k| {
        var blk = mir.MirBasicBlock{};
        blk.setSealed(true);
        if (bb_k >= 3) blk.setCleanupPad(true);
        try body.blocks.append(allocator, blk);
    }

    // `bb0`; store `_1`, create `yield_now()` fut, `.coro_suspend` -> `[bb1, bb3]`:
    const v_byte = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .const_scalar, .type_id = .u8_ty, .operands = .{ .lhs = c_arr } });
    try body.origin_tokens.append(allocator, .none);
    const v_arr1 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .aggregate_make,
        .aux_u16 = @backingInt(AggregateKind.array_repeat),
        .type_id = arr_u8_64,
        .operands = .{ .lhs = v_byte.asInt(), .rhs = 64 },
    });
    try body.origin_tokens.append(allocator, .none);
    const v_st1 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 1, .rhs = v_arr1.asInt() },
    });
    try body.origin_tokens.append(allocator, .none);
    const v_fut1 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .intrinsic_op,
        .aux_u16 = @backingInt(MirIntrinsicKind.async_yield),
        .type_id = fut_unit,
        .operands = .{ .lhs = 0, .rhs = 0 },
    });
    try body.origin_tokens.append(allocator, .none);

    body.blocks.items[0].inst_start = 0;
    body.blocks.items[0].inst_len = 4;
    try body.block_insts.appendSlice(allocator, &.{ v_byte, v_arr1, v_st1, v_fut1 });

    // `bb1`; param `%ready1`, read `_1` (last use of `_1`!), then write `_2`, `.coro_suspend` -> `[bb2, bb4]`:
    const v_p1 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .block_param, .type_id = .unit_ty, .operands = .{ .lhs = 1, .rhs = 0 } });
    try body.origin_tokens.append(allocator, .none);
    body.blocks.items[1].param_start = @intCast(body.block_params.items.len);
    body.blocks.items[1].setParamLen(1);
    try body.block_params.append(allocator, v_p1);

    const v_ld1 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .place_load, .type_id = arr_u8_64, .operands = .{ .lhs = 1 } });
    try body.origin_tokens.append(allocator, .none);
    const v_b2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .const_scalar, .type_id = .u8_ty, .operands = .{ .lhs = c_arr } });
    try body.origin_tokens.append(allocator, .none);
    const v_arr2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .aggregate_make,
        .aux_u16 = @backingInt(AggregateKind.array_repeat),
        .type_id = arr_u8_64,
        .operands = .{ .lhs = v_b2.asInt(), .rhs = 64 },
    });
    try body.origin_tokens.append(allocator, .none);
    const v_st2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 2, .rhs = v_arr2.asInt() },
    });
    try body.origin_tokens.append(allocator, .none);
    const v_fut2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .intrinsic_op,
        .aux_u16 = @backingInt(MirIntrinsicKind.async_yield),
        .type_id = fut_unit,
        .operands = .{ .lhs = 0, .rhs = 0 },
    });
    try body.origin_tokens.append(allocator, .none);

    body.blocks.items[1].inst_start = @intCast(body.block_insts.items.len);
    body.blocks.items[1].inst_len = 5;
    try body.block_insts.appendSlice(allocator, &.{ v_ld1, v_b2, v_arr2, v_st2, v_fut2 });

    // `bb2`; param `%ready2`, read `_2`, return `u8`:
    const v_p2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .block_param, .type_id = .unit_ty, .operands = .{ .lhs = 2, .rhs = 0 } });
    try body.origin_tokens.append(allocator, .none);
    body.blocks.items[2].param_start = @intCast(body.block_params.items.len);
    body.blocks.items[2].setParamLen(1);
    try body.block_params.append(allocator, v_p2);

    const v_ld2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .place_load, .type_id = arr_u8_64, .operands = .{ .lhs = 2 } });
    try body.origin_tokens.append(allocator, .none);
    const v_ret = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .aggregate_extract,
        .type_id = .u8_ty,
        .operands = .{ .lhs = v_ld2.asInt(), .rhs = 0 },
    });
    try body.origin_tokens.append(allocator, .none);
    body.blocks.items[2].inst_start = @intCast(body.block_insts.items.len);
    body.blocks.items[2].inst_len = 2;
    try body.block_insts.appendSlice(allocator, &.{ v_ld2, v_ret });
    body.blocks.items[2].terminator = .{ .kind = .ret, .cond_or_val = v_ret.asInt() };

    // `bb3` and `bb4`; cancel pads returning dummy `u8`:
    for (3..5) |cancel_bb| {
        const v_cret = MirValueId.fromInt(@intCast(body.insts.len));
        try body.insts.append(allocator, .{ .op = .const_scalar, .type_id = .u8_ty, .operands = .{ .lhs = c_arr } });
        try body.origin_tokens.append(allocator, .none);
        body.blocks.items[cancel_bb].inst_start = @intCast(body.block_insts.items.len);
        body.blocks.items[cancel_bb].inst_len = 1;
        try body.block_insts.append(allocator, v_cret);
        body.blocks.items[cancel_bb].terminator = .{ .kind = .ret, .cond_or_val = v_cret.asInt() };
    }
    _ = c_unit;

    try body.extra_edges.appendSlice(allocator, &.{
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(1) },
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(3) },
        .{ .src_bb = .fromInt(1), .target_bb = .fromInt(2) },
        .{ .src_bb = .fromInt(1), .target_bb = .fromInt(4) },
    });
    body.blocks.items[0].terminator = .{
        .kind = .coro_suspend,
        .edge_len = 2,
        .cond_or_val = v_fut1.asInt(),
        .edge_start = 0,
    };
    body.blocks.items[1].terminator = .{
        .kind = .coro_suspend,
        .edge_len = 2,
        .cond_or_val = v_fut2.asInt(),
        .edge_start = 2,
    };

    var plan = try analyzeAsyncBody(allocator, 0, &body, &pool, &sym_table, TargetLayout.NATIVE_64);
    defer plan.deinit(allocator);

    try std.testing.expectEqual(@as(usize, 2), plan.suspend_points.len);
    try std.testing.expectEqual(@as(u32, 1), plan.suspend_points[0].state_tag);
    try std.testing.expectEqual(@as(u32, 2), plan.suspend_points[1].state_tag);
    try std.testing.expectEqual(@as(?usize, 0), plan.findSuspendByBlock(.fromInt(0)));
    try std.testing.expectEqual(@as(?usize, 1), plan.findSuspendByBlock(.fromInt(1)));
    // Disjoint sequential `[u8; 64]` locals `_1` and `_2` MUST share the exact same byte offset:
    try std.testing.expectEqual(plan.getLocalOffset(1), plan.getLocalOffset(2));
    try std.testing.expect(plan.reused_slot_count >= 1);
    try std.testing.expect(!plan.has_exceeded_inline_cap);

    // Synchronous modules execute the zero-allocation fast path (`failing_allocator` proves 0 allocs):
    var sync_body = MirBody.init(allocator, .fromInt(0), .fromInt(2));
    defer sync_body.deinit();
    var sync_mod = try analyzeAsyncModule(
        std.testing.failing_allocator,
        (&sync_body)[0..1],
        &pool,
        &sym_table,
        TargetLayout.NATIVE_64,
        null,
    );
    defer sync_mod.deinit();
    try std.testing.expect(!sync_mod.has_any_async_ops);
    try std.testing.expectEqual(@as(usize, 0), sync_mod.body_plans.len);
}

test "test_mir_async_e0317_rejects_oversized_inline_frames_and_unboxed_recursion" {
    const allocator = std.testing.allocator;
    var interner = try mem_foundation.StringInterner.init(allocator);
    defer interner.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();

    // [1] Oversized `[u8; 20_000]` local in an `is_async` body triggers `E0317`:
    const huge_arr = try pool.internArray(.u8_ty, 20_000, false);
    var huge_body = MirBody.init(allocator, .fromInt(0), .fromInt(10));
    defer huge_body.deinit();
    huge_body.is_async = true;
    huge_body.ret_ty = .unit_ty;
    try huge_body.locals.append(allocator, LocalDecl.init(.empty, .unit_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_return_slot = true,
    }));
    try huge_body.locals.append(allocator, LocalDecl.init(.empty, huge_arr, .none, 0, .let_mode, .{}));

    var sink_huge = DiagnosticSink.init(allocator);
    defer sink_huge.deinit();
    var mod_huge = try analyzeAsyncModule(
        allocator,
        (&huge_body)[0..1],
        &pool,
        &sym_table,
        TargetLayout.NATIVE_64,
        &sink_huge,
    );
    defer mod_huge.deinit();
    try std.testing.expect(mod_huge.body_plans[0].has_exceeded_inline_cap);
    try std.testing.expect(sink_huge.hasErrors());
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0317_async_inline_frame_exceeded,
        sink_huge.diagnostics.items[0].code,
    );

    // [2] Unboxed self-recursive `async` call cycle triggers `has_unboxed_recursion` + `E0317`:
    const rec_def = DefId.fromInt(77);
    const fut_rec = try pool.internFuture(.unit_ty, rec_def.asInt());
    var rec_body = MirBody.init(allocator, .fromInt(0), rec_def);
    defer rec_body.deinit();
    rec_body.symbol_index = .fromInt(77);
    rec_body.is_async = true;
    rec_body.ret_ty = .unit_ty;
    try rec_body.locals.append(allocator, LocalDecl.init(.empty, .unit_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_return_slot = true,
    }));
    var blk0 = mir.MirBasicBlock{};
    blk0.setSealed(true);
    var blk1 = mir.MirBasicBlock{};
    blk1.setSealed(true);
    var blk2 = mir.MirBasicBlock{};
    blk2.setSealed(true);
    blk2.setCleanupPad(true);
    try rec_body.blocks.appendSlice(allocator, &.{ blk0, blk1, blk2 });
    const v_self_fut = MirValueId.fromInt(@intCast(rec_body.insts.len));
    try rec_body.insts.append(allocator, .{
        .op = .intrinsic_op,
        .aux_u16 = @backingInt(MirIntrinsicKind.async_yield),
        .type_id = fut_rec,
    });
    try rec_body.origin_tokens.append(allocator, .none);
    try rec_body.extra_edges.appendSlice(allocator, &.{
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(1) },
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(2) },
    });
    rec_body.blocks.items[0].inst_start = 0;
    rec_body.blocks.items[0].inst_len = 1;
    try rec_body.block_insts.append(allocator, v_self_fut);
    rec_body.blocks.items[0].terminator = .{
        .kind = .coro_suspend,
        .edge_len = 2,
        .cond_or_val = v_self_fut.asInt(),
        .edge_start = 0,
    };

    var sink_rec = DiagnosticSink.init(allocator);
    defer sink_rec.deinit();
    var mod_rec = try analyzeAsyncModule(
        allocator,
        (&rec_body)[0..1],
        &pool,
        &sym_table,
        TargetLayout.NATIVE_64,
        &sink_rec,
    );
    defer mod_rec.deinit();
    try std.testing.expect(mod_rec.body_plans[0].has_unboxed_recursion);
    try std.testing.expect(mod_rec.body_plans[0].has_exceeded_inline_cap);
    try std.testing.expect(sink_rec.hasErrors());
}

test "test_mir_async_frame_pinned_local_in_diverging_loop_never_aliases" {
    const allocator = std.testing.allocator;
    var interner = try mem_foundation.StringInterner.init(allocator);
    defer interner.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();

    const arr_u8_64 = try pool.internArray(.u8_ty, 64, false);
    const ref_arr = try pool.internRef(arr_u8_64, false);
    const fut_unit = try pool.internFuture(.unit_ty, 0);

    var body = MirBody.init(allocator, .fromInt(0), .fromInt(90));
    defer body.deinit();
    body.is_async = true;
    body.ret_ty = .unit_ty;

    // `_0` (`unit`), `_1` (`FramePinned` via `place_addr`), `_2` (written across `.await` inside diverging `loop`):
    try body.locals.append(allocator, LocalDecl.init(.empty, .unit_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_return_slot = true,
    }));
    try body.locals.append(allocator, LocalDecl.init(.empty, arr_u8_64, .none, 0, .let_mode, .{ .is_mut = true }));
    try body.locals.append(allocator, LocalDecl.init(.empty, arr_u8_64, .none, 0, .let_mode, .{ .is_mut = true }));

    try body.places.append(allocator, .{ .base = 0 });
    try body.places.append(allocator, .{ .base = 1 });
    try body.places.append(allocator, .{ .base = 2 });

    const c_seven = try body.appendConst(.{ .int_val = 7 });

    // `bb0 -> bb1` (`loop` header), `bb1 --coro_suspend--> [bb1, bb2(trap)]` (zero reachable `.ret` blocks!):
    for (0..3) |bb_k| {
        var blk = mir.MirBasicBlock{};
        blk.setSealed(true);
        if (bb_k == 2) blk.setCleanupPad(true);
        try body.blocks.append(allocator, blk);
    }

    const v_addr = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .place_addr, .type_id = ref_arr, .operands = .{ .lhs = 1 } });
    try body.origin_tokens.append(allocator, .none);
    body.blocks.items[0].inst_start = 0;
    body.blocks.items[0].inst_len = 1;
    try body.block_insts.append(allocator, v_addr);

    const v_p1 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .block_param, .type_id = .unit_ty, .operands = .{ .lhs = 1, .rhs = 0 } });
    try body.origin_tokens.append(allocator, .none);
    body.blocks.items[1].param_start = @intCast(body.block_params.items.len);
    body.blocks.items[1].setParamLen(1);
    try body.block_params.append(allocator, v_p1);

    const v_byte = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{ .op = .const_scalar, .type_id = .u8_ty, .operands = .{ .lhs = c_seven } });
    try body.origin_tokens.append(allocator, .none);
    const v_arr2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .aggregate_make,
        .aux_u16 = @backingInt(AggregateKind.array_repeat),
        .type_id = arr_u8_64,
        .operands = .{ .lhs = v_byte.asInt(), .rhs = 64 },
    });
    try body.origin_tokens.append(allocator, .none);
    const v_st2 = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .place_store,
        .type_id = .unit_ty,
        .operands = .{ .lhs = 2, .rhs = v_arr2.asInt() },
    });
    try body.origin_tokens.append(allocator, .none);
    const v_fut = MirValueId.fromInt(@intCast(body.insts.len));
    try body.insts.append(allocator, .{
        .op = .intrinsic_op,
        .aux_u16 = @backingInt(MirIntrinsicKind.async_yield),
        .type_id = fut_unit,
    });
    try body.origin_tokens.append(allocator, .none);

    body.blocks.items[1].inst_start = @intCast(body.block_insts.items.len);
    body.blocks.items[1].inst_len = 4;
    try body.block_insts.appendSlice(allocator, &.{ v_byte, v_arr2, v_st2, v_fut });
    body.blocks.items[2].terminator = .{ .kind = .trap };

    try body.extra_edges.appendSlice(allocator, &.{
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(1) },
        .{ .src_bb = .fromInt(1), .target_bb = .fromInt(1) },
        .{ .src_bb = .fromInt(1), .target_bb = .fromInt(2) },
    });
    body.blocks.items[0].terminator = .{ .kind = .br, .edge_len = 1, .edge_start = 0 };
    body.blocks.items[1].terminator = .{
        .kind = .coro_suspend,
        .edge_len = 2,
        .cond_or_val = v_fut.asInt(),
        .edge_start = 1,
    };

    var plan = try analyzeAsyncBody(allocator, 0, &body, &pool, &sym_table, TargetLayout.NATIVE_64);
    defer plan.deinit(allocator);

    const off_pinned = plan.getLocalOffset(1);
    const off_loop = plan.getLocalOffset(2);
    try std.testing.expect(off_pinned != off_loop);
    try std.testing.expect(off_pinned + 64 <= off_loop or off_loop + 64 <= off_pinned);
}

test "test_mir_async_file0_producer_id_and_sync_wrapper_recursion_detection" {
    const allocator = std.testing.allocator;
    var interner = try mem_foundation.StringInterner.init(allocator);
    defer interner.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();

    // [1] `FileId(0)` `DefId.init(0, 5)` (`asInt() == 5`) MUST NOT collide with `SymbolIndex(5)` on another `async fn`:
    const caller_def = DefId.init(.fromInt(0), 5);
    const leaf_def = DefId.init(.fromInt(0), 6);
    const leaf_sym = SymbolIndex.fromInt(5);
    const fut_leaf = try pool.internFuture(.unit_ty, leaf_sym.asInt());

    var caller_body = MirBody.init(allocator, .fromInt(0), caller_def);
    defer caller_body.deinit();
    caller_body.symbol_index = .fromInt(20);
    caller_body.is_async = true;
    caller_body.ret_ty = .unit_ty;
    try caller_body.locals.append(allocator, LocalDecl.init(.empty, .unit_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_return_slot = true,
    }));
    for (0..3) |bb_k| {
        var blk = mir.MirBasicBlock{};
        blk.setSealed(true);
        if (bb_k == 2) blk.setCleanupPad(true);
        try caller_body.blocks.append(allocator, blk);
    }
    const v_leaf_fut = MirValueId.fromInt(@intCast(caller_body.insts.len));
    try caller_body.insts.append(allocator, .{
        .op = .intrinsic_op,
        .aux_u16 = @backingInt(MirIntrinsicKind.async_yield),
        .type_id = fut_leaf,
    });
    try caller_body.origin_tokens.append(allocator, .none);
    caller_body.blocks.items[0].inst_start = 0;
    caller_body.blocks.items[0].inst_len = 1;
    try caller_body.block_insts.append(allocator, v_leaf_fut);
    try caller_body.extra_edges.appendSlice(allocator, &.{
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(1) },
        .{ .src_bb = .fromInt(0), .target_bb = .fromInt(2) },
    });
    caller_body.blocks.items[0].terminator = .{
        .kind = .coro_suspend,
        .edge_len = 2,
        .cond_or_val = v_leaf_fut.asInt(),
        .edge_start = 0,
    };

    var leaf_body = MirBody.init(allocator, .fromInt(0), leaf_def);
    defer leaf_body.deinit();
    leaf_body.symbol_index = leaf_sym;
    leaf_body.is_async = true;
    leaf_body.ret_ty = .unit_ty;
    try leaf_body.locals.append(allocator, LocalDecl.init(.empty, .unit_ty, .none, 0, .set_mode, .{
        .is_mut = true,
        .is_return_slot = true,
    }));

    const pair_bodies = [_]MirBody{ caller_body, leaf_body };
    var sink_ok = DiagnosticSink.init(allocator);
    defer sink_ok.deinit();
    var mod_ok = try analyzeAsyncModule(allocator, &pair_bodies, &pool, &sym_table, TargetLayout.NATIVE_64, &sink_ok);
    defer mod_ok.deinit();
    try std.testing.expect(!mod_ok.body_plans[0].has_unboxed_recursion);
    try std.testing.expect(!sink_ok.hasErrors());

    // [2] Synchronous wrapper `fn bounce() -> Future[i32] { return async_rec(); }` MUST trigger `E0317`:
    const wrapper_src =
        \\fn bounce() -> Future[i32] {
        \\    return async_rec();
        \\}
        \\
        \\async fn async_rec() -> i32 {
        \\    return bounce().await;
        \\}
    ;
    var bundle = try mir.lowerSourceToMir(allocator, .fromInt(0), wrapper_src, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var sink_wrap = DiagnosticSink.init(allocator);
    defer sink_wrap.deinit();
    var mod_wrap = try prepareAndAnalyzeAsyncModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        TargetLayout.NATIVE_64,
        &sink_wrap,
    );
    defer mod_wrap.deinit();
    try std.testing.expect(sink_wrap.hasErrors());
    try std.testing.expectEqual(
        diagnostic.DiagnosticCode.e0317_async_inline_frame_exceeded,
        sink_wrap.diagnostics.items[0].code,
    );
}

test "test_mir_async_over_aligned_64b_local_computes_aligned_frame_layout" {
    const allocator = std.testing.allocator;
    const aligned_src =
        \\use cx.async.yield_now;
        \\
        \\@repr(align: 64)
        \\pub struct CacheLineBlock {
        \\    pub lanes: [u64; 8],
        \\}
        \\
        \\pub async fn compute_aligned(seed: u64) -> u64 {
        \\    let block = CacheLineBlock { lanes: [seed; 8] };
        \\    yield_now().await;
        \\    return block.lanes[0] + block.lanes[7];
        \\}
    ;
    var bundle = try mir.lowerSourceToMir(allocator, .fromInt(1), aligned_src, TargetLayout.NATIVE_64, .{});
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var mod_plan = try prepareAndAnalyzeAsyncModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        TargetLayout.NATIVE_64,
        &sink,
    );
    defer mod_plan.deinit();
    try std.testing.expect(!sink.hasErrors());

    var has_found_async = false;
    for (bundle.mir_bundle.bodies.items, 0..) |*cand_body, idx| {
        if (!cand_body.is_async) continue;
        if (!std.mem.eql(u8, bundle.hir_bundle.interner.get(cand_body.name), "compute_aligned")) continue;
        has_found_async = true;
        const plan = mod_plan.getBodyPlan(idx);
        try std.testing.expectEqual(@as(u32, 64), plan.frame_align);
        try std.testing.expectEqual(@as(u32, 64), plan.frame_layout.header_bytes);
        try std.testing.expectEqual(@as(u32, 0), plan.frame_layout.total_frame_bytes % 64);
        for (plan.local_slots) |slot| {
            if (slot.align_bytes == 64) {
                try std.testing.expectEqual(@as(u32, 0), slot.byte_offset % 64);
            }
        }
    }
    try std.testing.expect(has_found_async);
}

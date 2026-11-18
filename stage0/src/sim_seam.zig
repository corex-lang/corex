//! Context Simulation Seam, Reactor VTable & Completion Reaper
//!
//! Defines the Stage-0 `ReactorVTable` proactor/clock/entropy seam (`DR-18` §2.1), `InFlightOpSlot` (`DR-08` §5.3), and `CompletionReaper`.
//!
//! All reactor context pointers use the strongly typed opaque `ReactorCtx` handle (`*ReactorCtx`) across native OS rings, `wasm32`, and `SimWorld`.

const std = @import("std");

// ---------------------------------------- TYPES ----------------------------------------

/// Strongly typed opaque handle representing either a native OS reactor or a deterministic `SimWorld`.
pub const ReactorCtx = opaque {};
/// Lifecycle state of an `InFlightOpSlot` in the completion proactor table (`DR-08` §5.3).
pub const SlotState = enum(u8) { free = 0, in_flight = 1, completed = 2, cancel_requested = 3, quarantined = 4 };
/// Resource cleanup action executed if a cancelled operation completes after task exit (`Fix-08B`).
pub const ReaperAction = enum(u8) { none = 0, release_buffer = 1, close_fd = 2, release_buf_and_close_fd = 3 };
/// Packed 32-bit generation counter, `SlotState`, and `Fix-08B` `ReaperAction` header (`4B`).
pub const GenStateReaper = packed struct(u32) {
    generation: u16 = 0,
    state: SlotState = .free,
    reaper_action: ReaperAction = .none,
    /// Returns this `GenStateReaper` header in its raw 32-bit integer representation.
    pub inline fn asU32(self: GenStateReaper) u32 {
        return @bitCast(self);
    }
    /// Decodes a raw 32-bit integer into a typed `GenStateReaper` header.
    pub inline fn fromU32(raw_bits: u32) GenStateReaper {
        return @bitCast(raw_bits);
    }
};
/// Packed 64-bit correlation key carried in `io_uring`, `IOCP`, `kqueue`, and `wasm32` `user_data` (`8B`).
pub const IoUserData = packed struct(u64) {
    slot_index: u32 = 0,
    generation: u16 = 0,
    worker_id: u16 = 0,
    /// Returns this `IoUserData` correlation key in its raw 64-bit integer representation.
    pub inline fn asU64(self: IoUserData) u64 {
        return @bitCast(self);
    }
    /// Decodes a 64-bit completion `user_data` payload into `IoUserData`.
    pub inline fn fromU64(raw_bits: u64) IoUserData {
        return @bitCast(raw_bits);
    }
};
/// 24-byte `@linear` DMA buffer descriptor invariant across 64-bit and 32-bit `wasm32` targets.
pub const IoBuf = extern struct {
    base: ?[*]u8 = null,
    len: usize = 0,
    _pad32: if (@sizeOf(usize) == 4) [8]u8 else [0]u8 = if (@sizeOf(usize) == 4) @splat(0) else .{},
    capacity: u32 = 0,
    owned_pool_id: u32 = 0,
};
/// 64-byte cache-line-aligned in-flight completion slot (`[0..4]` header, `[4..8]` fd, `[8..32]` buf, `[32..64]` OS state).
pub const InFlightOpSlot = extern struct {
    gen_state_reaper: u32 align(64) = 0,
    fd_or_handle: i32 = -1,
    buf: IoBuf = .{},
    platform_overlapped: [4]u64 = @splat(0),
};
/// Normalized 16-byte completion queue entry shared across all OS reactors and `SimWorld`.
pub const ReactorCqe = extern struct { user_data: u64 = 0, result: i32 = 0, flags: u32 = 0 };
/// Canonical proactor I/O operation opcode submitted via `ReactorVTable.submit_io`.
pub const IoOpKind = enum(u8) { nop = 0, read = 1, write = 2, accept = 3, connect = 4, timer = 5, close = 6 };
/// C-ABI proactor submission descriptor passed to `ReactorVTable.submit_io`.
pub const IoSubmission = extern struct {
    kind: IoOpKind = .nop,
    flags: u8 = 0,
    worker_id: u16 = 0,
    fd_or_handle: i32 = -1,
    offset_or_ns: u64 = 0,
    buf_ptr: ?[*]u8 = null,
    buf_len: u32 = 0,
    slot_index: u32 = 0,
};
/// Completion retirement result preserving orphaned buffer/descriptor state before slot recycling (`Fix-08B`).
pub const ReapOutcome = extern struct {
    state: SlotState = .free,
    orphan_action: ReaperAction = .none,
    orphan_fd: i32 = -1,
    cqe_result: i32 = 0,
    orphan_buf: IoBuf = .{},
};
/// C-ABI callback invoked by `drainQuarantinedBarrier` to reclaim orphaned DMA buffers and OS descriptors.
pub const ReapOrphanFn = *const fn (ctx: *ReactorCtx, outcome: ReapOutcome) callconv(.c) void;
/// C-ABI vtable routing clock, entropy, proactor I/O, and `buggify` hooks (`DR-18` §2.1).
pub const ReactorVTable = extern struct {
    monotonic_ns: *const fn (ctx: *ReactorCtx) callconv(.c) u64 = &noopMonotonicNs,
    wall_epoch_ns: *const fn (ctx: *ReactorCtx) callconv(.c) i64 = &noopWallEpochNs,
    fill_rng: *const fn (ctx: *ReactorCtx, out_ptr: [*]u8, out_len: usize) callconv(.c) void = &noopFillRng,
    submit_io: *const fn (ctx: *ReactorCtx, sub: *const IoSubmission) callconv(.c) i64 = &noopSubmitIo,
    cancel_io: *const fn (ctx: *ReactorCtx, slot_index: u32, generation: u16) callconv(.c) void = &noopCancelIo,
    poll_or_park: *const fn (ctx: *ReactorCtx, cqes: [*]ReactorCqe, cap: usize, is_blocking: bool) callconv(.c) usize = &noopPollOrPark,
    yield_task: *const fn (ctx: *ReactorCtx, reason_tag: u8) callconv(.c) void = &noopYieldTask,
    buggify_gate: *const fn (ctx: *ReactorCtx, site_hash: u64, prob_ppm: u32) callconv(.c) bool = &noopBuggifyGate,
};
/// Two-phase DMA quarantine and zombie-CQE slot manager (`DR-08` §4.3, `DR-18` `Fix-08B`).
pub const CompletionReaper = struct {
    slots: []InFlightOpSlot,
    free_head: u32 = FREE_SLOT_SENTINEL,
    active_in_flight_count: u32 = 0,
    quarantined_count: u32 = 0,
    /// Initializes an intrusive free list across `slots` with generation `0`.
    pub fn init(slots: []InFlightOpSlot) CompletionReaper {
        std.debug.assert(slots.len < FREE_SLOT_SENTINEL);
        for (slots, 0..) |*slot, i| {
            slot.* = .{ .gen_state_reaper = (GenStateReaper{}).asU32() };
            slot.platform_overlapped[0] = if (i + 1 < slots.len) @intCast(i + 1) else FREE_SLOT_SENTINEL;
        }
        return .{ .slots = slots, .free_head = if (slots.len > 0) 0 else FREE_SLOT_SENTINEL };
    }
    /// Pops a `.free` slot index from `free_head`, or returns `null` when full.
    pub fn acquireSlot(self: *CompletionReaper) ?u32 {
        if (self.free_head == FREE_SLOT_SENTINEL) return null;
        const slot_index = self.free_head;
        self.free_head = @intCast(self.slots[slot_index].platform_overlapped[0]);
        self.slots[slot_index] = .{ .gen_state_reaper = self.slots[slot_index].gen_state_reaper };
        return slot_index;
    }
    /// Marks `slot_index` as `.in_flight` and returns its packed 64-bit `IoUserData` correlation key.
    pub fn markSubmitted(self: *CompletionReaper, slot_index: u32, worker_id: u16, fd: i32, buf: IoBuf, action: ReaperAction) IoUserData {
        const slot = &self.slots[slot_index];
        const header = GenStateReaper.fromU32(slot.gen_state_reaper);
        std.debug.assert(header.state == .free);
        slot.gen_state_reaper = (GenStateReaper{ .generation = header.generation, .state = .in_flight, .reaper_action = action }).asU32();
        slot.fd_or_handle = fd;
        slot.buf = buf;
        self.active_in_flight_count += 1;
        return .{ .slot_index = slot_index, .generation = header.generation, .worker_id = worker_id };
    }
    /// ABA-checked cancellation transitioning `.in_flight -> .quarantined` and invoking `vtable.cancel_io`.
    pub fn requestCancel(self: *CompletionReaper, key: IoUserData, vtable: ?*const ReactorVTable, ctx: ?*ReactorCtx) bool {
        if (key.slot_index >= self.slots.len) return false;
        const slot = &self.slots[key.slot_index];
        var header = GenStateReaper.fromU32(slot.gen_state_reaper);
        if (header.generation != key.generation or header.state != .in_flight) return false;
        header.state = .quarantined;
        slot.gen_state_reaper = header.asU32();
        self.active_in_flight_count -= 1;
        self.quarantined_count += 1;
        if (vtable) |reactor_vt| if (ctx) |reactor_ctx| reactor_vt.cancel_io(reactor_ctx, key.slot_index, header.generation);
        return true;
    }
    /// Validates `cqe.user_data` generation and retires `.in_flight -> .completed` or `.quarantined -> .free`.
    pub fn reapCompletion(self: *CompletionReaper, cqe: ReactorCqe) ?ReapOutcome {
        const key = IoUserData.fromU64(cqe.user_data);
        if (key.slot_index >= self.slots.len) return null;
        const slot = &self.slots[key.slot_index];
        var header = GenStateReaper.fromU32(slot.gen_state_reaper);
        if (header.generation != key.generation) return null;
        if (header.state == .in_flight) {
            header.state = .completed;
            slot.gen_state_reaper = header.asU32();
            self.active_in_flight_count -= 1;
            return .{ .state = .completed, .cqe_result = cqe.result };
        } else if (header.state == .quarantined or header.state == .cancel_requested) {
            if (header.state == .quarantined) self.quarantined_count -= 1 else self.active_in_flight_count -= 1;
            defer recycleSlotToFree(self, key.slot_index, header.generation);
            return .{ .orphan_action = header.reaper_action, .orphan_fd = slot.fd_or_handle, .cqe_result = cqe.result, .orphan_buf = slot.buf };
        }
        return null;
    }
    /// ABA-checked release of a `.completed` slot back to `.free` (`generation +%= 1`), returning its `IoBuf`.
    pub fn releaseCompletedSlot(self: *CompletionReaper, key: IoUserData) ?IoBuf {
        if (key.slot_index >= self.slots.len) return null;
        const header = GenStateReaper.fromU32(self.slots[key.slot_index].gen_state_reaper);
        if (header.generation != key.generation or header.state != .completed) return null;
        defer recycleSlotToFree(self, key.slot_index, header.generation);
        return self.slots[key.slot_index].buf;
    }
    /// Polls `vtable.poll_or_park` in 16-CQE batches until `quarantined_count == 0`, EOF/error, or `max_polls`.
    pub fn drainQuarantinedBarrier(
        self: *CompletionReaper,
        vtable: *const ReactorVTable,
        ctx: *ReactorCtx,
        max_polls: u32,
        on_orphan: ?ReapOrphanFn,
    ) bool {
        var cqe_batch: [16]ReactorCqe = @splat(.{});
        var poll_count: u32 = 0;
        while (self.quarantined_count > 0 and poll_count < max_polls) : (poll_count += 1) {
            const polled_count = vtable.poll_or_park(ctx, &cqe_batch, cqe_batch.len, true);
            if (polled_count == 0 or polled_count > cqe_batch.len) break;
            for (cqe_batch[0..polled_count]) |cqe| if (self.reapCompletion(cqe)) |out| {
                if (out.state == .free and out.orphan_action != .none) if (on_orphan) |cb| cb(ctx, out);
            };
        }
        return self.quarantined_count == 0;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Sentinel `u32` index marking the end of `CompletionReaper`'s intrusive free list.
pub const FREE_SLOT_SENTINEL: u32 = std.math.maxInt(u32);
/// Deterministic loopback/host no-op `ReactorVTable` when no OS completion ring is attached.
pub const DEFAULT_NOOP_REACTOR_VTABLE: ReactorVTable = .{};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns deterministic `1.0 s` (`1_000_000_000` ns) monotonic origin for the no-op reactor.
fn noopMonotonicNs(_: *ReactorCtx) callconv(.c) u64 {
    return 1_000_000_000;
}
/// Returns deterministic `2026-01-01T00:00:00Z` wall-clock origin (ns) for the no-op reactor.
fn noopWallEpochNs(_: *ReactorCtx) callconv(.c) i64 {
    return 1_767_225_600_000_000_000;
}
/// Zero-fills `out_ptr[0..out_len]` deterministically when no entropy source is attached.
fn noopFillRng(_: *ReactorCtx, out_ptr: [*]u8, out_len: usize) callconv(.c) void {
    @memset(out_ptr[0..out_len], 0);
}
/// Synchronous no-op submission returning `0`.
fn noopSubmitIo(_: *ReactorCtx, _: *const IoSubmission) callconv(.c) i64 {
    return 0;
}
/// Synchronous no-op cancellation hook.
fn noopCancelIo(_: *ReactorCtx, _: u32, _: u16) callconv(.c) void {}
/// Synchronous no-op poller returning `0` completion events.
fn noopPollOrPark(_: *ReactorCtx, _: [*]ReactorCqe, _: usize, _: bool) callconv(.c) usize {
    return 0;
}
/// Synchronous no-op cooperative yield hook.
fn noopYieldTask(_: *ReactorCtx, _: u8) callconv(.c) void {}
/// Always disables `buggify` fault injection outside active `--sim` worlds.
fn noopBuggifyGate(_: *ReactorCtx, _: u64, _: u32) callconv(.c) bool {
    return false;
}
/// Resets `reaper.slots[slot_index]` to `.free` (`generation +%= 1`) and links it onto `free_head`.
fn recycleSlotToFree(reaper: *CompletionReaper, slot_index: u32, generation: u16) void {
    reaper.slots[slot_index] = .{ .gen_state_reaper = (GenStateReaper{ .generation = generation +% 1 }).asU32() };
    reaper.slots[slot_index].platform_overlapped[0] = reaper.free_head;
    reaper.free_head = slot_index;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Initializes a two-phase DMA quarantine and zombie-CQE slot manager over `slots`.
pub fn initCompletionReaper(slots: []InFlightOpSlot) CompletionReaper {
    return CompletionReaper.init(slots);
}

// ---------------------------------------- MAIN -----------------------------------------

comptime {
    std.debug.assert(@sizeOf(GenStateReaper) == 4 and @sizeOf(IoUserData) == 8 and @sizeOf(IoBuf) == 24);
    std.debug.assert(@sizeOf(InFlightOpSlot) == 64 and @alignOf(InFlightOpSlot) == 64 and @sizeOf(ReactorCqe) == 16);
    std.debug.assert(@offsetOf(InFlightOpSlot, "platform_overlapped") == 32 and @sizeOf(ReactorVTable) == 8 * @sizeOf(usize));
}

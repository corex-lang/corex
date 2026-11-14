//! Sandboxed 64-Bit Register `MirVm`, Reflection Intrinsics, Memoization & `.rodata` Promotion.
//!
//! Architectural Role:
//! - Executes target-independent Block-Argument SSA `MirBody` graphs at compile time (`DR-05`
//!   Deliverable 3) using fixed 8-byte `RegSlot` registers, 4-byte tagged `ComptimeAllocId`
//!   handles (`[CRITICAL-02]`), out-of-band `init_mask` bitsets, and sorted `ProvenanceEntry`
//!   pointer provenance tables (`[CRITICAL-10]`).
//! - Supports arbitrary scalar, pointer, and `> 8B` by-value SSA values (`i128`, `u128`, `str`,
//!   `[T]`, `#soa [T]`, structs, tuples, payload enums/`Option`/`Result`, `[T; N]`) via a 3-way
//!   `VmValueRepr` (`[CRITICAL-04]`) parameterized by `TargetLayout` (`NATIVE_64` vs `WASM32`,
//!   `[MAJOR-06]`).
//! - Enforces deterministic compile-time UB traps (`E0501`–`E0510`) with ordered call-stack
//!   `LabeledSpan` traces, canonical IEEE-754 quiet NaNs, all 9 `DR-05` reflection intrinsics
//!   (including VFS-sandboxed `@embed_bytes`), bounded `Wyhash(0)` pure-call memoization with
//!   `BumpArena` rewind, and deduplicated `.rodata` `RodataBlob` constant promotion.
//!
//! Key Design Choices:
//! - Host allocations inside `BumpArena` clamp alignment to `<= 16` bytes while checking exact
//!   virtual `align_log2` on `SymbolicPtr.byte_offset` (`[CRITICAL-03]`).
//! - Pure `comptime` calls serialize canonical argument bytes + transitive provenance into a
//!   `Wyhash(0)` key and restore `BumpArena` checkpoints on completion when no mutable allocation
//!   escapes, bounding memory across recursive `comptime` metaprogramming.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const router = @import("cli/router.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const query_db = @import("query_db.zig");
const hir = @import("hir.zig");
const mir = @import("mir.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const SymbolId = mem_foundation.SymbolId;
const StringInterner = mem_foundation.StringInterner;
const BumpArena = mem_foundation.BumpArena;
const TokenIndex = mem_foundation.TokenIndex;
const MirBlockId = mem_foundation.MirBlockId;
const MirValueId = mem_foundation.MirValueId;
const TypeId = mem_foundation.TypeId;
const DefId = query_db.DefId;

const TokenBuffer = syntax_arenas.TokenBuffer;
const DiagnosticSink = diagnostic.DiagnosticSink;
const DiagnosticCode = diagnostic.DiagnosticCode;
const LabeledSpan = diagnostic.LabeledSpan;

const SymbolIndex = symbol_resolver.SymbolIndex;
const SymbolTable = symbol_resolver.SymbolTable;

const InternPool = type_system.InternPool;
const ParamMode = type_system.ParamMode;
const TargetLayout = type_system.TargetLayout;
const TypeLayout = type_system.TypeLayout;
const IntrinsicKind = type_system.IntrinsicKind;
const AttrArgValue = type_system.AttrArgValue;

const HirIndex = hir.HirIndex;
const HirStore = hir.HirStore;
const HirFnMeta = hir.HirFnMeta;
const ComptimeValue = hir.ComptimeValue;
const ComptimeEvalHook = hir.ComptimeEvalHook;
const BitSpec = hir.BitSpec;

const LocalId = mir.LocalId;
const PlaceId = mir.PlaceId;
const ProjKind = mir.ProjKind;
const MirOp = mir.MirOp;
const BinOpKind = mir.BinOpKind;
const UnaryOpKind = mir.UnaryOpKind;
const AggregateKind = mir.AggregateKind;
const MirIntrinsicKind = mir.MirIntrinsicKind;
const MirTrapReason = mir.MirTrapReason;
const MirBody = mir.MirBody;

// ---------------------------------------- TYPES ----------------------------------------

// ---------------- Comptime Allocation Handles -----------------

/// Disjoint 2-bit top tag partitioning the 32-bit `ComptimeAllocId` space (`[CRITICAL-02]`).
pub const AllocDomain = enum(u2) {
    /// `0b00`: Mutable, stack-frame, or value-snapshot `MirVm` allocation (`0` = null pointer).
    vm_alloc = 0,
    /// `0b01`: Immutable promoted `.rodata` `RodataBlob` (`0x4000_0000 | blob_idx`).
    rodata_blob = 1,
    /// `0b10`: Immutable `StringInterner` UTF-8 / byte literal (`0x8000_0000 | sym_id`).
    string_lit = 2,
    /// `0b11`: Callable `fn_addr` handle (`0xC000_0000 | fn_idx`) or `.none` (`0xFFFF_FFFF`).
    fn_or_none = 3,
};

/// Strongly typed 4-byte allocation handle with disjoint 2-bit domain tags (`[CRITICAL-02]`).
pub const ComptimeAllocId = enum(u32) {
    /// Null pointer sentinel (`0x0000_0000`, traps `E0506` on dereference).
    null_ptr = 0,
    /// Absent / uninitialized sentinel (`0xFFFF_FFFF`, traps `E0506` on dereference).
    none = std.math.maxInt(u32),
    _,

    /// Constructs a `ComptimeAllocId` from a raw `u32`.
    pub inline fn fromInt(raw_val: u32) ComptimeAllocId {
        return @fromBackingInt(@intCast(raw_val));
    }

    /// Extracts the raw `u32` backing integer.
    pub inline fn asInt(self: ComptimeAllocId) u32 {
        return @backingInt(self);
    }

    /// Decodes the top 2-bit `AllocDomain`.
    pub inline fn domain(self: ComptimeAllocId) AllocDomain {
        return @fromBackingInt(@intCast(@as(u2, @truncate(self.asInt() >> 30))));
    }

    /// Extracts the lower 30-bit payload index (`0 .. 0x3FFF_FFFF`).
    pub inline fn payloadIndex(self: ComptimeAllocId) u32 {
        return self.asInt() & ALLOC_PAYLOAD_MASK;
    }

    /// Returns `true` if `self` is `.none` (`0xFFFF_FFFF`).
    pub inline fn isNone(self: ComptimeAllocId) bool {
        return self == .none;
    }

    /// Returns `true` if `self` is `.null_ptr` (`0`) or `.none` (`0xFFFF_FFFF`).
    pub inline fn isNullOrNone(self: ComptimeAllocId) bool {
        return self == .null_ptr or self == .none;
    }

    /// Returns `true` if `self` encodes a `fn_addr` callable (`domain == .fn_or_none` and `self != .none`).
    pub inline fn isFnAddr(self: ComptimeAllocId) bool {
        return self.domain() == .fn_or_none and self != .none;
    }

    /// Encodes a 1-based `MirVm.allocations` slot (`1 .. 0x3FFF_FFFF`) in domain `0b00`.
    pub inline fn fromVmIndex(vm_slot: u32) ComptimeAllocId {
        std.debug.assert(vm_slot > 0 and vm_slot <= ALLOC_PAYLOAD_MASK);
        return fromInt(vm_slot);
    }

    /// Encodes a 0-based `RodataPool.blobs` index in domain `0b01` (`0x4000_0000 | blob_idx`).
    pub inline fn fromRodataIndex(blob_idx: u32) ComptimeAllocId {
        std.debug.assert(blob_idx <= ALLOC_PAYLOAD_MASK);
        return fromInt((@as(u32, @backingInt(AllocDomain.rodata_blob)) << 30) | blob_idx);
    }

    /// Encodes an interned `SymbolId` literal in domain `0b10` (`0x8000_0000 | sym_id`).
    pub inline fn fromStringId(sym_id: SymbolId) ComptimeAllocId {
        const clamped = sym_id.asInt() & ALLOC_PAYLOAD_MASK;
        return fromInt((@as(u32, @backingInt(AllocDomain.string_lit)) << 30) | clamped);
    }

    /// Encodes a callable function table index in domain `0b11` (`0xC000_0000 | fn_idx`, `< 0x3FFF_FFFF`).
    pub inline fn fromFnIndex(fn_idx: u32) ComptimeAllocId {
        std.debug.assert(fn_idx < ALLOC_PAYLOAD_MASK);
        return fromInt((@as(u32, @backingInt(AllocDomain.fn_or_none)) << 30) | fn_idx);
    }
};

/// 8-byte symbolic pointer pairing a `ComptimeAllocId` base with an exact byte offset (`DR-05` §3.1).
pub const SymbolicPtr = extern struct {
    /// Target allocation or callable domain handle (`4B`).
    alloc_id: ComptimeAllocId = .none,
    /// Byte offset inside `alloc_id` (`4B`).
    byte_offset: u32 = 0,

    /// Canonical null symbolic pointer (`alloc_id = .null_ptr, byte_offset = 0`).
    pub const NULL: SymbolicPtr = .{ .alloc_id = .null_ptr, .byte_offset = 0 };
};

/// Fixed 8-byte SSA virtual register slot in `MirVm` (`DR-05` §3.1, `[CRITICAL-04]`).
pub const RegSlot = extern union {
    /// Unsigned 64-bit integer, boolean, `char`, or packed bitfield payload.
    scalar_u64: u64,
    /// Signed 64-bit two's-complement integer payload.
    scalar_i64: i64,
    /// Canonicalized IEEE-754 64-bit float (`f32` stored as `u32` bits in `scalar_u64`).
    scalar_f64: f64,
    /// Symbolic pointer (`inline_ptr`) or immutable aggregate snapshot handle (`by_value_snapshot`).
    sym_ptr: SymbolicPtr,
};

/// 8-byte out-of-band pointer provenance entry sorted by `byte_offset` (`[CRITICAL-10]`).
pub const ProvenanceEntry = extern struct {
    /// Starting byte offset of the stored pointer within the owning allocation (`4B`).
    byte_offset: u32,
    /// Provenance `ComptimeAllocId` stored at `[byte_offset .. byte_offset + ptr_byte_size)` (`4B`).
    alloc_id: ComptimeAllocId,
};

/// 3-way runtime value representation inside `MirVm` (`[CRITICAL-04]`).
pub const VmValueRepr = enum(u8) {
    /// Scalar `<= 8` bytes (`unit`, `bool`, `char`, `i8`..`i64`, `u8`..`u64`, `isize`, `usize`, `f32`, `f64`).
    inline_scalar = 0,
    /// Single pointer or function reference (`&T`, `&mut T`, `*T`, `*mut T`, `fn(…) -> R`).
    inline_ptr = 1,
    /// Composite or `16B` value (`i128`, `u128`, `str`, `[T]`, `#soa [T]`, structs, tuples, enums, arrays)
    /// stored as an immutable value-snapshot `ComptimeAllocation` pointed to by `RegSlot.sym_ptr`.
    by_value_snapshot = 2,
};

// ----------------- Memory Model & Rodata Pool -----------------

/// Tracked compile-time memory object in `MirVm` (`[CRITICAL-03]`, `[CRITICAL-10]`).
pub const ComptimeAllocation = struct {
    /// Raw backing byte slice in `MirVm.arena` (host alignment clamped to `<= 16`).
    bytes: []u8,
    /// Out-of-band initialization bitmask (`1` bit per byte; `(bytes.len + 63) / 64` `u64` words).
    init_mask: []u64,
    /// Sorted out-of-band pointer provenance table (`byte_offset` strictly ascending).
    provenance: std.ArrayListUnmanaged(ProvenanceEntry) = .empty,
    /// Virtual alignment exponent (`align_bytes = 1 << align_log2`) enforced on `SymbolicPtr`.
    align_log2: u8 = 0,
    /// `true` if writes (`place_store`, `place_set_discrim`) are permitted on this allocation.
    is_mutable: bool = false,
    /// `true` while the allocation is temporally live; `false` after frame exit (`E0506` UAF).
    is_live: bool = true,
    /// `true` if owned by an active `MirVm` stack frame (`E0506` if escaping to `.rodata` or return).
    is_stack_frame: bool = false,
    /// `true` if allocated via virtual heap/container allocation (`live_heap_allocs` leak/UAF ledger).
    is_heap_alloc: bool = false,
    /// Element capacity when this allocation backs a `#soa [S; N]` container (`0` otherwise).
    soa_elem_capacity: u32 = 0,
    /// Source span where this allocation originated (for UAF / OOB diagnostic notes).
    origin_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
};

/// Symbolic relocation inside an immutable promoted `.rodata` `RodataBlob`.
pub const RodataReloc = extern struct {
    /// Byte offset inside `RodataBlob.bytes` where the pointer resides (`4B`).
    byte_offset: u32,
    /// Target `.rodata` or `StringInterner` `ComptimeAllocId` (`4B`).
    target_alloc: ComptimeAllocId,
};

/// Deduplicated immutable constant data blob promoted out of `MirVm` (`DR-05` §3.6).
pub const RodataBlob = struct {
    /// Canonicalized byte payload (uninitialized padding bytes deterministically zeroed).
    bytes: []const u8,
    /// Sorted relocation entries for embedded pointers/slices (`str`, `&T`, `[T]`).
    relocs: []const RodataReloc,
    /// Virtual alignment exponent (`1 << align_log2`).
    align_log2: u8,
    /// `Wyhash(0)` content + relocation digest used for $O(1)$ deduplication.
    content_hash: u64,
};

/// Arena-backed `.rodata` constant pool with deterministic `Wyhash(0)` deduplication.
pub const RodataPool = struct {
    /// Backing allocator for `blobs` and `dedup_buckets`.
    allocator: std.mem.Allocator,
    /// Contiguous bump arena owning all promoted byte and relocation slices.
    arena: BumpArena,
    /// Indexed `RodataBlob` table (`ComptimeAllocId.fromRodataIndex(idx)`).
    blobs: std.ArrayListUnmanaged(RodataBlob) = .empty,
    /// Map `content_hash -> [blob_indices…]` for $O(1)$ structural deduplication.
    dedup_buckets: std.AutoHashMapUnmanaged(u64, std.ArrayListUnmanaged(u32)) = .empty,

    /// Initializes an empty `RodataPool`.
    pub fn init(allocator: std.mem.Allocator) RodataPool {
        return .{
            .allocator = allocator,
            .arena = BumpArena.init(allocator),
        };
    }

    /// Releases all promoted `.rodata` blobs and lookup tables.
    pub fn deinit(self: *RodataPool) void {
        var bucket_iter = self.dedup_buckets.valueIterator();
        while (bucket_iter.next()) |list_ptr| {
            list_ptr.deinit(self.allocator);
        }
        self.dedup_buckets.deinit(self.allocator);
        self.blobs.deinit(self.allocator);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Interns `(bytes, relocs, align_log2)` into `blobs`, deduplicating identical `.rodata` constants.
    pub fn internBlob(
        self: *RodataPool,
        raw_bytes: []const u8,
        relocs: []const RodataReloc,
        align_log2: u8,
    ) !ComptimeAllocId {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(&[1]u8{align_log2});
        var len_buf: [4]u8 = undefined;
        std.mem.writeInt(u32, &len_buf, @intCast(raw_bytes.len), .little);
        hasher.update(&len_buf);
        hasher.update(raw_bytes);
        std.mem.writeInt(u32, &len_buf, @intCast(relocs.len), .little);
        hasher.update(&len_buf);
        for (relocs) |reloc| {
            var reloc_buf: [8]u8 = undefined;
            std.mem.writeInt(u32, reloc_buf[0..4], reloc.byte_offset, .little);
            std.mem.writeInt(u32, reloc_buf[4..8], reloc.target_alloc.asInt(), .little);
            hasher.update(&reloc_buf);
        }
        const digest = hasher.final();

        const gop = try self.dedup_buckets.getOrPut(self.allocator, digest);
        if (!gop.found_existing) {
            gop.value_ptr.* = .empty;
        } else {
            for (gop.value_ptr.items) |cand_idx| {
                const cand = self.blobs.items[cand_idx];
                if (cand.align_log2 == align_log2 and
                    std.mem.eql(u8, cand.bytes, raw_bytes) and
                    isRelocSliceEqual(cand.relocs, relocs))
                {
                    return ComptimeAllocId.fromRodataIndex(cand_idx);
                }
            }
        }

        const owned_bytes = if (raw_bytes.len > 0)
            try self.arena.dupe(u8, raw_bytes)
        else
            &[_]u8{};
        const owned_relocs = if (relocs.len > 0)
            try self.arena.dupe(RodataReloc, relocs)
        else
            &[_]RodataReloc{};

        const new_idx: u32 = @intCast(self.blobs.items.len);
        try self.blobs.append(self.allocator, .{
            .bytes = owned_bytes,
            .relocs = owned_relocs,
            .align_log2 = align_log2,
            .content_hash = digest,
        });
        try gop.value_ptr.append(self.allocator, new_idx);
        return ComptimeAllocId.fromRodataIndex(new_idx);
    }

    /// Fetches a `RodataBlob` by its 0-based pool index.
    pub inline fn getBlob(self: *const RodataPool, blob_idx: u32) ?RodataBlob {
        if (blob_idx >= self.blobs.items.len) return null;
        return self.blobs.items[blob_idx];
    }
};

// ---------------- Pure-Call Memoization Cache -----------------

/// Transitive `CompilerDb` dependency recorded during a memoized pure `MirVm` call (`[CRITICAL-01]`).
const MemoQueryDep = struct {
    /// Observed `CompilerDb` `QueryKey` (`build_def_mir`, `eval_comptime_def`, or Stage-0 config/embed input).
    key: query_db.QueryKey,
    /// `MemoHeader.output_fingerprint` observed when the cached result was computed.
    output_fingerprint: query_db.Fingerprint128,
};

/// Serialized return value cached inside `PureCallMemoCache`.
const MemoCachedResult = struct {
    /// 64-bit `Wyhash(0)` lookup key.
    call_hash: u64,
    /// Callee `DefId` disambiguator.
    callee_id: u64,
    /// Return `TypeId`.
    ret_ty: TypeId,
    /// Value representation kind.
    repr: VmValueRepr,
    /// Inline `RegSlot` for `inline_scalar` or `inline_ptr`.
    inline_slot: RegSlot = .{ .scalar_u64 = 0 },
    /// Owned byte snapshot when `repr == .by_value_snapshot`.
    snapshot_bytes: []u8 = &.{},
    /// Owned `init_mask` words when `repr == .by_value_snapshot`.
    snapshot_init: []u64 = &.{},
    /// Owned `ProvenanceEntry` slice when `repr == .by_value_snapshot`.
    snapshot_prov: []ProvenanceEntry = &.{},
    /// Owned transitive `CompilerDb` query dependencies replayed on every cache hit (`[CRITICAL-01]`).
    query_deps: []MemoQueryDep = &.{},
    /// Sub-slice byte offset inside `snapshot_bytes` when `repr == .by_value_snapshot`.
    snapshot_offset: u32 = 0,
    /// Alignment exponent of `snapshot_bytes`.
    align_log2: u8 = 0,
    /// Intrusive FIFO predecessor slot index (`maxInt(u32)` when head).
    prev_fifo: u32 = std.math.maxInt(u32),
    /// Intrusive FIFO successor slot index (`maxInt(u32)` when tail).
    next_fifo: u32 = std.math.maxInt(u32),
    /// Total heap bytes accounted for by this entry.
    accounted_bytes: usize = 0,
};

/// Bounded `Wyhash(0)` memoization cache for pure `comptime` calls (`AGENTS.md` §2).
///
/// Enforces both `MAX_MEMO_ENTRIES` (`4,096`) and `MAX_MEMO_BYTES` (`16 MiB`) with $O(1)$ FIFO
/// eviction and `free_slots` index reuse so `entries` never grows unboundedly (`[MAJOR-08]`).
pub const PureCallMemoCache = struct {
    /// Backing allocator for owned snapshot buffers and slot tables.
    allocator: std.mem.Allocator,
    /// Map `call_hash -> index in entries`.
    index_by_hash: std.AutoHashMapUnmanaged(u64, u32) = .empty,
    /// Bounded slot storage of active memo entries (`null` once evicted; `len <= MAX_MEMO_ENTRIES`).
    entries: std.ArrayListUnmanaged(?MemoCachedResult) = .empty,
    /// Reusable vacant indices inside `entries` reclaimed on eviction or hash overwrite (`[MAJOR-08]`).
    free_slots: std.ArrayListUnmanaged(u32) = .empty,
    /// Oldest live slot in the intrusive FIFO doubly-linked list (`maxInt(u32)` when empty).
    fifo_head: u32 = std.math.maxInt(u32),
    /// Newest live slot in the intrusive FIFO doubly-linked list (`maxInt(u32)` when empty).
    fifo_tail: u32 = std.math.maxInt(u32),
    /// Current live entry count (`<= MAX_MEMO_ENTRIES`).
    live_count: usize = 0,
    /// Current total accounted byte footprint (`<= MAX_MEMO_BYTES`).
    live_bytes: usize = 0,
    /// Telemetry counter of pure-call cache hits.
    hit_count: u64 = 0,
    /// Telemetry counter of pure-call cache insertions.
    insert_count: u64 = 0,

    /// Initializes an empty bounded `PureCallMemoCache`.
    pub fn init(allocator: std.mem.Allocator) PureCallMemoCache {
        return .{ .allocator = allocator };
    }

    /// Releases all cached snapshot buffers, free-slot lists, and hash maps.
    pub fn deinit(self: *PureCallMemoCache) void {
        self.clear();
        self.entries.deinit(self.allocator);
        self.free_slots.deinit(self.allocator);
        self.index_by_hash.deinit(self.allocator);
        self.* = undefined;
    }

    /// Evicts all cached entries while retaining underlying table capacity across revisions.
    pub fn clear(self: *PureCallMemoCache) void {
        for (self.entries.items) |maybe_item| {
            if (maybe_item) |item| {
                self.freeEntryBuffers(item);
            }
        }
        self.entries.clearRetainingCapacity();
        self.free_slots.clearRetainingCapacity();
        self.index_by_hash.clearRetainingCapacity();
        self.fifo_head = std.math.maxInt(u32);
        self.fifo_tail = std.math.maxInt(u32);
        self.live_count = 0;
        self.live_bytes = 0;
    }

    /// Frees heap slices owned by a single `MemoCachedResult`.
    fn freeEntryBuffers(self: *PureCallMemoCache, item: MemoCachedResult) void {
        if (item.snapshot_bytes.len > 0) self.allocator.free(item.snapshot_bytes);
        if (item.snapshot_init.len > 0) self.allocator.free(item.snapshot_init);
        if (item.snapshot_prov.len > 0) self.allocator.free(item.snapshot_prov);
        if (item.query_deps.len > 0) self.allocator.free(item.query_deps);
    }

    /// Appends `slot_idx` to the tail of the intrusive FIFO eviction list.
    fn appendFifoSlot(self: *PureCallMemoCache, slot_idx: u32) void {
        const sentinel = std.math.maxInt(u32);
        if (self.entries.items[slot_idx]) |*cur_entry| {
            cur_entry.prev_fifo = self.fifo_tail;
            cur_entry.next_fifo = sentinel;
        }
        if (self.fifo_tail != sentinel) {
            if (self.entries.items[self.fifo_tail]) |*tail_entry| {
                tail_entry.next_fifo = slot_idx;
            }
        } else {
            self.fifo_head = slot_idx;
        }
        self.fifo_tail = slot_idx;
    }

    /// Unlinks `slot_idx` (`entry`) from the intrusive FIFO eviction list in $O(1)$ time.
    fn unlinkFifoSlot(self: *PureCallMemoCache, slot_idx: u32, entry: MemoCachedResult) void {
        const sentinel = std.math.maxInt(u32);
        if (entry.prev_fifo != sentinel) {
            if (self.entries.items[entry.prev_fifo]) |*prev_entry| {
                prev_entry.next_fifo = entry.next_fifo;
            }
        } else if (self.fifo_head == slot_idx) {
            self.fifo_head = entry.next_fifo;
        }
        if (entry.next_fifo != sentinel) {
            if (self.entries.items[entry.next_fifo]) |*next_entry| {
                next_entry.prev_fifo = entry.prev_fifo;
            }
        } else if (self.fifo_tail == slot_idx) {
            self.fifo_tail = entry.prev_fifo;
        }
    }

    /// Evicts the oldest live entry in $O(1)$ time and recycles its slot into `free_slots`.
    fn evictOldest(self: *PureCallMemoCache) void {
        const sentinel = std.math.maxInt(u32);
        const cur_idx = self.fifo_head;
        if (cur_idx == sentinel or cur_idx >= self.entries.items.len) {
            self.fifo_head = sentinel;
            self.fifo_tail = sentinel;
            self.live_count = 0;
            self.live_bytes = 0;
            return;
        }
        if (self.entries.items[cur_idx]) |victim| {
            self.unlinkFifoSlot(cur_idx, victim);
            if (self.index_by_hash.get(victim.call_hash)) |mapped_idx| {
                if (mapped_idx == cur_idx) {
                    _ = self.index_by_hash.remove(victim.call_hash);
                }
            }
            self.live_bytes -|= victim.accounted_bytes;
            self.live_count -|= 1;
            self.freeEntryBuffers(victim);
            self.entries.items[cur_idx] = null;
            self.free_slots.appendAssumeCapacity(cur_idx);
        }
    }

    /// Looks up `(call_hash, callee_id, ret_ty)` in $O(1)$ time.
    fn lookup(
        self: *PureCallMemoCache,
        call_hash: u64,
        callee_id: u64,
        ret_ty: TypeId,
    ) ?MemoCachedResult {
        const slot_idx = self.index_by_hash.get(call_hash) orelse return null;
        if (slot_idx >= self.entries.items.len) return null;
        const entry = self.entries.items[slot_idx] orelse return null;
        if (entry.callee_id != callee_id or entry.ret_ty != ret_ty) return null;
        return entry;
    }

    /// Inserts a serialized pure return value, evicting oldest entries and recycling vacant slots (`[MAJOR-08]`).
    fn insert(self: *PureCallMemoCache, candidate: MemoCachedResult) !void {
        var is_transferred = false;
        errdefer if (!is_transferred) self.freeEntryBuffers(candidate);

        if (candidate.accounted_bytes > MAX_MEMO_BYTES) {
            self.freeEntryBuffers(candidate);
            is_transferred = true;
            return;
        }
        try self.free_slots.ensureUnusedCapacity(self.allocator, self.live_count + 1);
        while (self.live_count >= MAX_MEMO_ENTRIES or
            self.live_bytes + candidate.accounted_bytes > MAX_MEMO_BYTES)
        {
            if (self.live_count == 0) break;
            self.evictOldest();
        }
        if (self.index_by_hash.fetchRemove(candidate.call_hash)) |prev_kv| {
            if (prev_kv.value < self.entries.items.len) {
                if (self.entries.items[prev_kv.value]) |prev_entry| {
                    self.unlinkFifoSlot(prev_kv.value, prev_entry);
                    self.live_bytes -|= prev_entry.accounted_bytes;
                    self.live_count -|= 1;
                    self.freeEntryBuffers(prev_entry);
                    self.entries.items[prev_kv.value] = null;
                    self.free_slots.appendAssumeCapacity(prev_kv.value);
                }
            }
        }
        const target_slot: u32 = if (self.free_slots.pop()) |reused_slot| blk: {
            self.entries.items[reused_slot] = candidate;
            break :blk reused_slot;
        } else blk: {
            const next_slot: u32 = @intCast(self.entries.items.len);
            try self.entries.append(self.allocator, candidate);
            break :blk next_slot;
        };
        is_transferred = true;
        errdefer {
            if (self.entries.items[target_slot]) |rollback_item| {
                self.freeEntryBuffers(rollback_item);
                self.entries.items[target_slot] = null;
                self.free_slots.appendAssumeCapacity(target_slot);
            }
        }
        try self.index_by_hash.put(self.allocator, candidate.call_hash, target_slot);
        self.appendFifoSlot(target_slot);
        self.live_count += 1;
        self.live_bytes += candidate.accounted_bytes;
        self.insert_count += 1;
    }
};

// --------------- Execution State & Call Frames ----------------

/// Execution resource limits and target environment for `MirVm` (`DR-05` §3.4).
pub const VmExecOptions = struct {
    /// Maximum instruction/terminator step budget before `E0501` (`--comptime-limit`).
    step_budget: u64 = DEFAULT_STEP_BUDGET,
    /// Maximum live + arena byte cap before `E0508` (`64 MiB` default).
    mem_limit: u64 = DEFAULT_MEM_LIMIT,
    /// Maximum nested `MirVm` call depth before `E0508` (`512` default).
    max_call_depth: u32 = MAX_CALL_DEPTH,
    /// Target pointer size and alignment (`NATIVE_64` vs `WASM32`, `[MAJOR-06]`).
    target_layout: TargetLayout = TargetLayout.NATIVE_64,
    /// Optional workspace root directory path for VFS-sandboxed `@embed_bytes`.
    workspace_root: ?[]const u8 = null,
    /// Optional Zig `Io` handle for disk-backed `@embed_bytes` inside `workspace_root`.
    io: ?std.Io = null,
    /// Optional in-memory VFS file map (`relative_path -> bytes`) for sandboxed `@embed_bytes`.
    virtual_files: ?*const std.StringHashMapUnmanaged([]const u8) = null,
    /// Optional `TokenBuffer` map (`FileId.asInt() -> *const TokenBuffer`) for exact diagnostic spans.
    file_tokens: ?*const std.AutoHashMapUnmanaged(u32, *const TokenBuffer) = null,
    /// Optional `CompilerDb` for on-demand cross-definition `buildDefMir` / `evalComptimeDef` resolution.
    compiler_db: ?*query_db.CompilerDb = null,
    /// Optional pre-materialized `MirBlobStore` for `MirConst.raw_blob` (`@embed_bytes`, `[CRITICAL-07]`).
    blob_store: ?*const mir.MirBlobStore = null,
    /// Optional `stdout` capture buffer when `is_oracle_runtime_mode` is `true` (`D-07A`).
    stdout_capture: ?*std.ArrayListUnmanaged(u8) = null,
    /// Optional `stderr` capture buffer when `is_oracle_runtime_mode` is `true` (`D-07A`).
    stderr_capture: ?*std.ArrayListUnmanaged(u8) = null,
    /// Enables differential-oracle runtime execution of `@sys_write` and `@sys_exit` (`D-07A`).
    is_oracle_runtime_mode: bool = false,
};

/// Error set returned by `MirVm` when compile-time evaluation traps or runs out of host memory.
pub const VmEvalError = error{
    /// Step budget exceeded (`E0501`).
    StepLimitExceeded,
    /// Signed/unsigned integer arithmetic or shift overflow (`E0502`).
    IntegerOverflow,
    /// Forbidden operation (`ptr as usize`, `extern` FFI, provenance punning, escaping `@embed_bytes`, `E0503`).
    ForbiddenOperation,
    /// Spatial out-of-bounds memory or slice index (`E0504`).
    OutOfBounds,
    /// Read of uninitialized memory byte (`E0505`).
    UninitializedRead,
    /// Temporal UAF, null dereference, misaligned pointer, immutable write, or stack escape (`E0506`).
    InvalidPointer,
    /// Division/remainder by zero or out-of-range/NaN float-to-int cast (`E0507`).
    ArithmeticTrap,
    /// Call-stack depth (`> 512`) or memory cap (`> 64 MiB`) exceeded (`E0508`).
    ResourceLimitExceeded,
    /// Cyclic compile-time constant evaluation (`E0509`).
    EvaluationCycle,
    /// `@compile_assert(false, …)` or `@compile_error(…)` triggered (`E0510`).
    CompileAssertionFailed,
    /// Trap inside a vacated non-`Copy` `inout` `subscript` projection window triggered immediate abort.
    AbortedVacatedPanic,
    /// Explicit `@sys_exit(code)` terminated oracle execution cleanly (`MirVm.exited_with_code`).
    ProcessExited,
    /// Target callee `MirBody` could not be resolved.
    UnresolvedCallee,
    /// Cooperative query cancellation (`DR-12` §3.3).
    Cancelled,
    /// Host allocator ran out of memory.
    OutOfMemory,
};

/// Result produced by `MirVm.evalBody`, supporting both `ComptimeValue` extraction and `.rodata` promotion.
pub const VmEvalResult = struct {
    /// Concrete `TypeId` of the evaluated return value.
    type_id: TypeId,
    /// 3-way register representation tag.
    repr: VmValueRepr,
    /// Evaluated 8-byte `RegSlot` register value.
    slot: RegSlot,
    /// Total instructions executed during evaluation.
    steps_executed: u64,
};

/// Active call-stack activation record inside `MirVm`.
const VmCallFrame = struct {
    /// Executing `MirBody`.
    body: *const MirBody,
    /// SSA register file indexed by `MirValueId.asInt()`.
    regs: []RegSlot,
    /// Local storage allocation or aliased caller `SymbolicPtr` per `LocalId.asInt()`.
    local_ptrs: []SymbolicPtr,
    /// Bitset marking which `local_ptrs` slots are owned stack allocations of this frame (invalidated on exit).
    owned_stack_allocs: []ComptimeAllocId,
    /// Call-site `Span` in caller that invoked this frame (for stack-trace `LabeledSpan` notes).
    call_site_span: Span,
};

/// Callable entry registered in `MirVm` (`ComptimeAllocId.fromFnIndex(idx)`).
const VmCallableEntry = struct {
    /// Lowered `MirBody` pointer (`null` if `is_extern`).
    body: ?*const MirBody,
    /// Optional owning `DefId`.
    def_id: DefId = .NONE,
    /// Optional `SymbolIndex` in `SymbolTable`.
    symbol_index: SymbolIndex = .none,
    /// `true` if declared `extern` FFI (traps `E0503` if called at `comptime`).
    is_extern: bool = false,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Default `--comptime-limit` step budget (`10,000,000` instructions, `DR-05` §3.4).
pub const DEFAULT_STEP_BUDGET: u64 = router.DEFAULT_COMPTIME_STEP_LIMIT;
/// Default `MirVm` memory limit (`64 MiB`, `E0508`).
pub const DEFAULT_MEM_LIMIT: u64 = 64 * 1024 * 1024;
/// Maximum `MirVm` call-stack recursion depth (`512`, `E0508`).
pub const MAX_CALL_DEPTH: u32 = 512;
/// Maximum cached entries in `PureCallMemoCache` (`4,096`).
pub const MAX_MEMO_ENTRIES: usize = 4_096;
/// Maximum total byte footprint of `PureCallMemoCache` (`16 MiB`).
pub const MAX_MEMO_BYTES: usize = 16 * 1024 * 1024;
/// Canonical IEEE-754 quiet NaN bit pattern for `f64` (`0x7FF8_0000_0000_0000`).
pub const CANONICAL_F64_QNAN_BITS: u64 = 0x7FF8_0000_0000_0000;
/// Canonical IEEE-754 quiet NaN bit pattern for `f32` (`0x7FC0_0000`).
pub const CANONICAL_F32_QNAN_BITS: u32 = 0x7FC0_0000;

/// Lower 30-bit payload mask for `ComptimeAllocId`.
const ALLOC_PAYLOAD_MASK: u32 = 0x3FFF_FFFF;
/// Maximum host alignment supported by `BumpArena.allocAligned` (`16` bytes, `[CRITICAL-03]`).
const MAX_HOST_ALIGN_BYTES: usize = 16;

comptime {
    // Enforce exact Phase 5 `MirVm` byte-size invariants (`[CRITICAL-02]`, `DR-05` §3.1):
    std.debug.assert(@sizeOf(ComptimeAllocId) == 4);
    std.debug.assert(@sizeOf(SymbolicPtr) == 8);
    std.debug.assert(@sizeOf(RegSlot) == 8);
    std.debug.assert(@sizeOf(ProvenanceEntry) == 8);
    std.debug.assert(@sizeOf(RodataReloc) == 8);
}

// -------------------------------------- INTERNALS --------------------------------------

// ------------- Type Layout & Value Classification -------------

/// Compares two `RodataReloc` slices for exact structural equality.
fn isRelocSliceEqual(lhs_slice: []const RodataReloc, rhs_slice: []const RodataReloc) bool {
    if (lhs_slice.len != rhs_slice.len) return false;
    for (lhs_slice, rhs_slice) |lhs_item, rhs_item| {
        if (lhs_item.byte_offset != rhs_item.byte_offset or
            lhs_item.target_alloc != rhs_item.target_alloc)
        {
            return false;
        }
    }
    return true;
}

/// Classifies `raw_ty` into its 3-way `VmValueRepr` (`[CRITICAL-04]`).
pub fn classifyValueRepr(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) VmValueRepr {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    switch (ty) {
        .unit_ty,
        .never_ty,
        .bool_ty,
        .char_ty,
        .i8_ty,
        .i16_ty,
        .i32_ty,
        .i64_ty,
        .isize_ty,
        .u8_ty,
        .u16_ty,
        .u32_ty,
        .u64_ty,
        .usize_ty,
        .f32_ty,
        .f64_ty,
        .untyped_int_ty,
        .untyped_float_ty,
        => return .inline_scalar,
        .i128_ty, .u128_ty, .str_ty => return .by_value_snapshot,
        else => {},
    }
    const node = pool.getNode(ty);
    return switch (node.tag) {
        .ref_ty, .mut_ref_ty, .raw_ptr_ty, .fn_ty => .inline_ptr,
        .bit_field_ty => blk: {
            const backing_ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const layout = type_system.computeTypeLayoutWithPool(pool, sym_table, backing_ty, target_layout);
            break :blk if (layout.byte_size <= 8) .inline_scalar else .by_value_snapshot;
        },
        else => .by_value_snapshot,
    };
}

/// Returns the integer bit width and signedness of `raw_ty` under `target_layout`.
fn resolveIntInfo(
    pool: *const InternPool,
    raw_ty: TypeId,
    target_layout: TargetLayout,
) ?struct { bits: u16, is_signed: bool } {
    var ty = pool.unwrapUnderlyingType(raw_ty);
    const node = pool.getNode(ty);
    if (node.tag == .bit_field_ty) {
        ty = pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
    }
    const ptr_bits: u16 = @as(u16, target_layout.ptr_byte_size) * 8;
    return switch (ty) {
        .bool_ty => .{ .bits = 1, .is_signed = false },
        .i8_ty => .{ .bits = 8, .is_signed = true },
        .u8_ty => .{ .bits = 8, .is_signed = false },
        .i16_ty => .{ .bits = 16, .is_signed = true },
        .u16_ty => .{ .bits = 16, .is_signed = false },
        .i32_ty, .untyped_int_ty => .{ .bits = 32, .is_signed = true },
        .u32_ty, .char_ty => .{ .bits = 32, .is_signed = false },
        .i64_ty => .{ .bits = 64, .is_signed = true },
        .u64_ty => .{ .bits = 64, .is_signed = false },
        .i128_ty => .{ .bits = 128, .is_signed = true },
        .u128_ty => .{ .bits = 128, .is_signed = false },
        .isize_ty => .{ .bits = ptr_bits, .is_signed = true },
        .usize_ty => .{ .bits = ptr_bits, .is_signed = false },
        else => null,
    };
}

/// Canonicalizes `f64` NaNs to deterministic `0x7FF8_0000_0000_0000` (`DR-05` §3.5).
inline fn canonicalizeF64(val: f64) f64 {
    if (std.math.isNan(val)) return @bitCast(CANONICAL_F64_QNAN_BITS);
    return val;
}

/// Canonicalizes `f32` NaNs to deterministic `0x7FC0_0000` (`DR-05` §3.5).
inline fn canonicalizeF32(val: f32) f32 {
    if (std.math.isNan(val)) return @bitCast(CANONICAL_F32_QNAN_BITS);
    return val;
}

/// Encodes an `f32` value into a `RegSlot` (canonicalizing quiet NaNs).
inline fn packF32Slot(val: f32) RegSlot {
    const clean = canonicalizeF32(val);
    const bits: u32 = @bitCast(clean);
    return .{ .scalar_u64 = bits };
}

/// Decodes an `f32` value from a `RegSlot`.
inline fn unpackF32Slot(slot: RegSlot) f32 {
    const bits: u32 = @truncate(slot.scalar_u64);
    return canonicalizeF32(@bitCast(bits));
}

/// Masks a `u128` to the lowest `bits` (`1..128`).
inline fn maskToBitsU128(val: u128, bits: u16) u128 {
    if (bits >= 128) return val;
    if (bits == 0) return 0;
    return val & ((@as(u128, 1) << @intCast(bits)) - 1);
}

/// Sign-extends the lowest `bits` (`1..128`) of `raw` into `i128`.
inline fn signExtendToI128(raw: u128, bits: u16) i128 {
    if (bits >= 128) return @bitCast(raw);
    if (bits == 0) return 0;
    const masked = maskToBitsU128(raw, bits);
    const sign_bit = @as(u128, 1) << @intCast(bits - 1);
    if ((masked & sign_bit) != 0) {
        const high_ones = ~((@as(u128, 1) << @intCast(bits)) - 1);
        return @bitCast(masked | high_ones);
    }
    return @bitCast(masked);
}

/// Computes tag width in bytes and payload byte offset for `.optional_ty`, `.result_ty`, or `.enum_ty`.
pub fn computeSumTypeTagAndPayloadLayout(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_sum_ty: TypeId,
    target_layout: TargetLayout,
) struct { tag_bytes: u32, payload_offset: u32, total_layout: TypeLayout } {
    const sum_ty = pool.unwrapUnderlyingType(raw_sum_ty);
    const total_layout = type_system.computeTypeLayoutWithPool(pool, sym_table, sum_ty, target_layout);
    const node = pool.getNode(sum_ty);
    return switch (node.tag) {
        .optional_ty, .result_ty, .enum_ty => blk: {
            const sum_lay = type_system.computeSumMemoryLayout(pool, sym_table, sum_ty, target_layout);
            break :blk .{
                .tag_bytes = sum_lay.tag_bytes,
                .payload_offset = @intCast(sum_lay.payload_offset),
                .total_layout = total_layout,
            };
        },
        else => .{ .tag_bytes = 0, .payload_offset = 0, .total_layout = total_layout },
    };
}

/// Resolves the payload `TypeId` of variant `tag_ordinal` inside `raw_sum_ty`.
fn resolveVariantPayloadType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_sum_ty: TypeId,
    tag_ordinal: u32,
) TypeId {
    const sum_ty = pool.unwrapUnderlyingType(raw_sum_ty);
    const node = pool.getNode(sum_ty);
    return switch (node.tag) {
        .optional_ty => if (tag_ordinal == 1) TypeId.fromInt(node.lhs) else .unit_ty,
        .result_ty => if (tag_ordinal == 0) TypeId.fromInt(node.lhs) else TypeId.fromInt(node.rhs),
        .enum_ty => blk: {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const enum_sym = sym_table.getSymbol(sym_idx).*;
                if (!enum_sym.target_scope.isNone()) {
                    const subst = type_system.NominalTypeSubst.init(pool, sym_table, sum_ty);
                    var ord: u32 = 0;
                    for (sym_table.getScopeMembers(enum_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .enum_variant_sym) continue;
                        if (ord == tag_ordinal) break :blk subst.resolve(mem_sym.type_id);
                        ord += 1;
                    }
                }
            }
            break :blk .unit_ty;
        },
        else => .unit_ty,
    };
}

/// Returns `true` when `raw_ty` unwraps to a `@packed` `.struct_ty` with 1-byte field alignment.
fn isPackedStructType(pool: *const InternPool, sym_table: *const SymbolTable, raw_ty: TypeId) bool {
    const ty = pool.unwrapUnderlyingType(raw_ty);
    const node = pool.getNode(ty);
    if (node.tag != .struct_ty) return false;
    const sym_idx = SymbolIndex.fromInt(node.rhs);
    if (sym_idx.isNone() or sym_idx.asInt() >= sym_table.symbols.items.len) return false;
    return sym_table.getSymbol(sym_idx).contract_flags.is_packed;
}

/// Computes the byte offset and field `TypeId` of `field_ordinal` inside a `.struct_ty`, `.tuple_ty`, or `.union_ty`.
pub fn computeCompositeFieldOffsetAndType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    raw_comp_ty: TypeId,
    field_ordinal: u32,
    target_layout: TargetLayout,
) ?struct { byte_offset: u32, field_ty: TypeId } {
    const comp_ty = pool.unwrapUnderlyingType(raw_comp_ty);
    const node = pool.getNode(comp_ty);
    switch (node.tag) {
        .tuple_ty => {
            const elems = pool.getTupleElements(comp_ty);
            if (field_ordinal >= elems.len) return null;
            const byte_off = type_system.computeTupleElemOffset(
                pool,
                sym_table,
                comp_ty,
                field_ordinal,
                target_layout,
            ) orelse return null;
            return .{ .byte_offset = @intCast(byte_off), .field_ty = TypeId.fromInt(elems[field_ordinal]) };
        },
        .struct_ty => {
            const byte_off = type_system.computeStructFieldOffset(
                pool,
                sym_table,
                comp_ty,
                field_ordinal,
                target_layout,
            ) orelse return null;
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const st_sym = sym_table.getSymbol(sym_idx).*;
                if (!st_sym.target_scope.isNone()) {
                    const subst = type_system.NominalTypeSubst.init(pool, sym_table, comp_ty);
                    var ord: u32 = 0;
                    for (sym_table.getScopeMembers(st_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym) continue;
                        if (ord == field_ordinal) {
                            return .{
                                .byte_offset = @intCast(byte_off),
                                .field_ty = subst.resolve(mem_sym.type_id),
                            };
                        }
                        ord += 1;
                    }
                }
            }
            return null;
        },
        .union_ty => {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < sym_table.symbols.items.len) {
                const un_sym = sym_table.getSymbol(sym_idx).*;
                if (!un_sym.target_scope.isNone()) {
                    const subst = type_system.NominalTypeSubst.init(pool, sym_table, comp_ty);
                    var ord: u32 = 0;
                    for (sym_table.getScopeMembers(un_sym.target_scope)) |mem_idx| {
                        const mem_sym = sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym) continue;
                        if (ord == field_ordinal) {
                            return .{ .byte_offset = 0, .field_ty = subst.resolve(mem_sym.type_id) };
                        }
                        ord += 1;
                    }
                }
            }
            return null;
        },
        else => return null,
    }
}

/// Computes the byte offset and column element `TypeId` of column `field_ordinal` inside `#soa [S; elem_capacity]`.
fn computeSoaColumnOffsetAndType(
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    elem_struct_ty: TypeId,
    field_ordinal: u32,
    elem_capacity: u32,
    target_layout: TargetLayout,
) ?struct { column_byte_offset: u32, field_ty: TypeId } {
    const col_info = type_system.computeSoaColumnInfoReadOnly(
        pool,
        sym_table,
        elem_struct_ty,
        elem_capacity,
        field_ordinal,
        target_layout,
    ) orelse return null;
    return .{
        .column_byte_offset = @intCast(col_info.byte_offset),
        .field_ty = col_info.field_ty,
    };
}

// -------------- Reflection & VFS Sandbox Helpers --------------

/// Returns `true` if `stem` matches a reserved Windows DOS device name (`CON`, `PRN`, `AUX`, `NUL`,
/// `COM1`–`COM9`, `LPT1`–`LPT9`, case-insensitive, `[CRITICAL-02]`).
fn isReservedWindowsDeviceStem(stem: []const u8) bool {
    if (stem.len == 3) {
        return std.ascii.eqlIgnoreCase(stem, "CON") or
            std.ascii.eqlIgnoreCase(stem, "PRN") or
            std.ascii.eqlIgnoreCase(stem, "AUX") or
            std.ascii.eqlIgnoreCase(stem, "NUL");
    }
    if (stem.len == 4 and stem[3] >= '1' and stem[3] <= '9') {
        return std.ascii.eqlIgnoreCase(stem[0..3], "COM") or
            std.ascii.eqlIgnoreCase(stem[0..3], "LPT");
    }
    return false;
}

/// Validates a relative `@embed_bytes(path)` string, rejecting empty paths, absolute paths, Windows
/// drive prefixes, NUL bytes, `.` or `..` segments, empty segments, and reserved Windows device stems
/// (`DR-05` §3.3, `DR-20` `Fix-17` Gate D -> `E0326`).
pub fn isValidSandboxedEmbedPath(rel_path: []const u8) bool {
    if (rel_path.len == 0) return false;
    if (rel_path[0] == '/' or rel_path[0] == '\\') return false;
    if (std.fs.path.isAbsolute(rel_path)) return false;
    for (rel_path) |byte_val| {
        if (byte_val == 0 or byte_val == ':') return false;
    }

    var start_pos: usize = 0;
    var idx: usize = 0;
    while (idx <= rel_path.len) : (idx += 1) {
        const is_sep = idx == rel_path.len or rel_path[idx] == '/' or rel_path[idx] == '\\';
        if (is_sep) {
            const segment = rel_path[start_pos..idx];
            if (segment.len == 0) return false;
            if (std.mem.eql(u8, segment, ".") or std.mem.eql(u8, segment, "..")) return false;
            const trimmed_seg = std.mem.trimEnd(u8, segment, " .");
            if (trimmed_seg.len == 0) return false;
            const dot_pos = std.mem.indexOfScalar(u8, trimmed_seg, '.') orelse trimmed_seg.len;
            const stem = std.mem.trimEnd(u8, trimmed_seg[0..dot_pos], " ");
            if (isReservedWindowsDeviceStem(stem)) return false;
            start_pos = idx + 1;
        }
    }
    return true;
}

/// Returns `true` if canonical file path `canon_target` is strictly nested inside canonical directory
/// `canon_root` on a path-component boundary (`[CRITICAL-02]`).
pub fn isCanonicalPathWithinRoot(canon_root: []const u8, canon_target: []const u8) bool {
    if (canon_root.len == 0 or canon_target.len == 0) return false;
    const root_trimmed = std.mem.trimEnd(u8, canon_root, "/\\");
    if (canon_target.len <= root_trimmed.len) return false;

    for (0..root_trimmed.len) |idx| {
        const root_byte = root_trimmed[idx];
        const target_byte = canon_target[idx];
        const is_root_sep = root_byte == '/' or root_byte == '\\';
        const is_target_sep = target_byte == '/' or target_byte == '\\';
        if (is_root_sep and is_target_sep) continue;
        if (builtin.os.tag == .windows) {
            if (std.ascii.toLower(root_byte) != std.ascii.toLower(target_byte)) return false;
        } else {
            if (root_byte != target_byte) return false;
        }
    }

    const boundary_byte = canon_target[root_trimmed.len];
    return boundary_byte == '/' or boundary_byte == '\\';
}

/// Returns `true` if the suffix of `canon_target` beneath `canon_root` matches `rel_path` segment-for-segment
/// without traversing any intermediate symlink or NTFS junction/reparse point (`DR-20` `Fix-17` Gate D).
pub fn isDirectCanonicalSubpath(canon_root: []const u8, canon_target: []const u8, rel_path: []const u8) bool {
    if (!isCanonicalPathWithinRoot(canon_root, canon_target)) return false;
    const root_trimmed = std.mem.trimEnd(u8, canon_root, "/\\");
    const target_rel = canon_target[root_trimmed.len + 1 ..];
    if (target_rel.len != rel_path.len) return false;
    for (0..rel_path.len) |i| {
        const lhs_byte = target_rel[i];
        const rhs_byte = rel_path[i];
        const is_lhs_sep = lhs_byte == '/' or lhs_byte == '\\';
        const is_rhs_sep = rhs_byte == '/' or rhs_byte == '\\';
        if (is_lhs_sep and is_rhs_sep) continue;
        if (builtin.os.tag == .windows) {
            if (std.ascii.toLower(lhs_byte) != std.ascii.toLower(rhs_byte)) return false;
        } else {
            if (lhs_byte != rhs_byte) return false;
        }
    }
    return true;
}

/// Formats the canonical monochrome CoreX type name for `@type_name[T]()` (`DR-05` §3.3).
fn formatCanonicalTypeName(
    allocator: std.mem.Allocator,
    pool: *const InternPool,
    sym_table: *const SymbolTable,
    ty: TypeId,
) ![]u8 {
    var stack_buf: [512]u8 = undefined;
    const formatted = pool.formatType(ty, sym_table, &stack_buf);
    return allocator.dupe(u8, formatted);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------- Sandboxed Register Virtual Machine -------------

/// Sandboxed 64-bit register virtual machine executing `MirBody` CFGs at compile time (`DR-05` §3).
pub const MirVm = struct {
    /// Backing host allocator for growable metadata tables.
    allocator: std.mem.Allocator,
    /// Shared string interner for string literals and `@type_name` / `Debug` output.
    interner: *StringInterner,
    /// Canonical `InternPool` for layout and type reflection queries.
    pool: *InternPool,
    /// Canonical `SymbolTable` for struct/enum/trait/attribute reflection queries.
    sym_table: *const SymbolTable,
    /// Optional `DiagnosticSink` receiving `E0501`–`E0510` diagnostics with stack traces.
    diagnostic_sink: ?*DiagnosticSink,
    /// Optional shared `.rodata` pool for constant promotion and `@embed_bytes` interning.
    rodata_pool: *RodataPool,
    /// Optional shared pure-call memoization cache.
    memo_cache: ?*PureCallMemoCache = null,
    /// Active execution limits and target layout configuration.
    options: VmExecOptions = .{},

    /// Bump arena backing `ComptimeAllocation.bytes` and `init_mask` slices (`<= 16B` host alignment).
    arena: BumpArena,
    /// 1-based table of `ComptimeAllocation`s (`index 0` is reserved `.null_ptr`).
    allocations: std.ArrayListUnmanaged(ComptimeAllocation) = .empty,
    /// Registered callable functions (`ComptimeAllocId.fromFnIndex(idx)`).
    callables: std.ArrayListUnmanaged(VmCallableEntry) = .empty,
    /// Lookup map `DefId.asInt() -> callable_idx`.
    def_to_callable: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Lookup map `SymbolIndex.asInt() -> callable_idx`.
    sym_to_callable: std.AutoHashMapUnmanaged(u32, u32) = .empty,
    /// Set of `DefId.asInt()` callables loaded on demand from `CompilerDb.buildDefMir` (`[CRITICAL-01]`).
    db_backed_defs: std.AutoHashMapUnmanaged(u32, void) = .empty,
    /// Transitive `CompilerDb` `QueryKey`s observed during frame execution (`[CRITICAL-01]`).
    observed_query_deps: std.ArrayListUnmanaged(query_db.QueryKey) = .empty,
    /// Active `MirVm` call-stack frames (`len <= options.max_call_depth`).
    call_stack: std.ArrayListUnmanaged(VmCallFrame) = .empty,
    /// Active instruction span inside the top frame (for exact trap diagnostics).
    active_inst_span: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 },
    /// Total instructions executed so far (`<= options.step_budget`).
    steps_executed: u64 = 0,
    /// Total tracked allocation bytes currently consumed (`<= options.mem_limit`).
    bytes_used: u64 = 0,
    /// Ordered `@drop_trace(id)` ledger recorded during `MirVm` execution (`DR-20` Phase 6).
    drop_trace: std.ArrayListUnmanaged(i64) = .empty,
    /// Count of currently live virtual heap/container allocations (`0` on leak-free completion).
    live_heap_allocs: u32 = 0,
    /// Nesting depth of active `[abort_on_panic]` vacated projection windows (`[MAJOR-10]`).
    abort_on_panic_depth: u32 = 0,
    /// Set to `true` when a trap inside an `[abort_on_panic]` window triggered immediate abort (`[MAJOR-10]`).
    has_aborted_vacated_panic: bool = false,
    /// Non-null dangling `0`-byte sentinel allocation for empty slices (`[CRITICAL-04]`).
    dangling_empty_alloc: ComptimeAllocId = .null_ptr,
    /// Process exit code recorded when `@sys_exit(code)` runs under `is_oracle_runtime_mode`.
    exited_with_code: ?i32 = null,

    /// Initializes a `MirVm` instance with reserved slot `0` (`.null_ptr`) in `allocations`.
    pub fn init(
        allocator: std.mem.Allocator,
        interner: *StringInterner,
        pool: *InternPool,
        sym_table: *const SymbolTable,
        rodata_pool: *RodataPool,
        memo_cache: ?*PureCallMemoCache,
        diagnostic_sink: ?*DiagnosticSink,
        options: VmExecOptions,
    ) !MirVm {
        var vm = MirVm{
            .allocator = allocator,
            .interner = interner,
            .pool = pool,
            .sym_table = sym_table,
            .diagnostic_sink = diagnostic_sink,
            .rodata_pool = rodata_pool,
            .memo_cache = memo_cache,
            .options = options,
            .arena = BumpArena.init(allocator),
        };
        errdefer vm.deinit();

        // Reserve index `0` as the unmapped `.null_ptr` sentinel (`is_live = false`):
        try vm.allocations.append(allocator, .{
            .bytes = &.{},
            .init_mask = &.{},
            .align_log2 = 0,
            .is_mutable = false,
            .is_live = false,
            .is_stack_frame = false,
        });
        // Reserve index `1` as the live, aligned, `0`-byte dangling slice sentinel (`[CRITICAL-04]`):
        try vm.allocations.append(allocator, .{
            .bytes = &.{},
            .init_mask = &.{},
            .align_log2 = 16,
            .is_mutable = false,
            .is_live = true,
            .is_stack_frame = false,
        });
        vm.dangling_empty_alloc = ComptimeAllocId.fromVmIndex(1);
        return vm;
    }

    /// Releases all `MirVm` arenas, provenance lists, callable maps, and frames.
    pub fn deinit(self: *MirVm) void {
        for (self.call_stack.items) |frame| {
            if (frame.regs.len > 0) self.allocator.free(frame.regs);
            if (frame.local_ptrs.len > 0) self.allocator.free(frame.local_ptrs);
            if (frame.owned_stack_allocs.len > 0) self.allocator.free(frame.owned_stack_allocs);
        }
        self.call_stack.deinit(self.allocator);

        for (self.allocations.items) |*alloc_rec| {
            alloc_rec.provenance.deinit(self.allocator);
        }
        self.allocations.deinit(self.allocator);
        self.callables.deinit(self.allocator);
        self.def_to_callable.deinit(self.allocator);
        self.sym_to_callable.deinit(self.allocator);
        self.db_backed_defs.deinit(self.allocator);
        self.observed_query_deps.deinit(self.allocator);
        self.drop_trace.deinit(self.allocator);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Returns the ordered slice of `@drop_trace(id)` integers recorded so far.
    pub fn asDropTraceSlice(self: *const MirVm) []const i64 {
        return self.drop_trace.items;
    }

    /// Returns the number of unfreed virtual heap/container allocations currently live in `self`.
    pub fn countUnfreedHeapAllocations(self: *const MirVm) u32 {
        return self.live_heap_allocs;
    }

    /// Allocates a mutable virtual heap/container block tracked in `live_heap_allocs`.
    pub fn allocHeapMemory(
        self: *MirVm,
        byte_size: u64,
        align_log2: u8,
        origin_span: Span,
    ) VmEvalError!SymbolicPtr {
        const alloc_id = try self.allocMemory(
            byte_size,
            align_log2,
            true,
            false,
            false,
            0,
            origin_span,
        );
        self.allocations.items[alloc_id.payloadIndex()].is_heap_alloc = true;
        self.live_heap_allocs += 1;
        return .{ .alloc_id = alloc_id, .byte_offset = 0 };
    }

    /// Frees a live virtual heap/container allocation at base offset `0`, trapping `E0506` on invalid/double-free.
    pub fn freeHeapMemory(self: *MirVm, ptr: SymbolicPtr) VmEvalError!void {
        if (ptr.alloc_id.isNullOrNone() or ptr.alloc_id.domain() != .vm_alloc) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "cannot deallocate null or non-heap pointer during `comptime` evaluation",
                "invalid deallocation pointer here",
                null,
            );
        }
        const slot_idx = ptr.alloc_id.payloadIndex();
        if (slot_idx == 0 or slot_idx >= self.allocations.items.len) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "invalid `ComptimeAllocId` handle deallocated during `comptime` evaluation",
                "invalid allocation handle",
                null,
            );
        }
        const alloc_rec = &self.allocations.items[slot_idx];
        if (!alloc_rec.is_live) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "double-free or deallocation of dead memory during `comptime` evaluation",
                "already-freed allocation deallocated here",
                null,
            );
        }
        if (ptr.byte_offset != 0 or !alloc_rec.is_heap_alloc or alloc_rec.is_stack_frame) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "cannot deallocate stack-local, snapshot, or interior pointer during `comptime` evaluation",
                "non-heap or interior pointer deallocated here",
                null,
            );
        }
        alloc_rec.is_live = false;
        self.live_heap_allocs -= 1;
    }

    /// Marks `def_id` as backed by `CompilerDb` so pure-call memoization records `.build_def_mir` invalidation.
    pub fn markDbBackedDef(self: *MirVm, def_id: DefId) !void {
        if (!def_id.isNone()) {
            try self.db_backed_defs.put(self.allocator, def_id.asInt(), {});
        }
    }

    /// Registers a lowered `MirBody` so direct and indirect calls can invoke it.
    pub fn registerBody(
        self: *MirVm,
        body: *const MirBody,
        symbol_index: SymbolIndex,
    ) !ComptimeAllocId {
        const effective_sym = if (!symbol_index.isNone()) symbol_index else body.symbol_index;
        const idx: u32 = @intCast(self.callables.items.len);
        try self.callables.append(self.allocator, .{
            .body = body,
            .def_id = body.def_id,
            .symbol_index = effective_sym,
            .is_extern = false,
        });
        if (!body.def_id.isNone()) {
            try self.def_to_callable.put(self.allocator, body.def_id.asInt(), idx);
        }
        if (!effective_sym.isNone()) {
            try self.sym_to_callable.put(self.allocator, effective_sym.asInt(), idx);
        }
        return ComptimeAllocId.fromFnIndex(idx);
    }

    /// Registers an `extern` FFI prototype so calling it at `comptime` deterministically traps `E0503`.
    pub fn registerExternFn(
        self: *MirVm,
        def_id: DefId,
        symbol_index: SymbolIndex,
    ) !ComptimeAllocId {
        const idx: u32 = @intCast(self.callables.items.len);
        try self.callables.append(self.allocator, .{
            .body = null,
            .def_id = def_id,
            .symbol_index = symbol_index,
            .is_extern = true,
        });
        if (!def_id.isNone()) {
            try self.def_to_callable.put(self.allocator, def_id.asInt(), idx);
        }
        if (!symbol_index.isNone()) {
            try self.sym_to_callable.put(self.allocator, symbol_index.asInt(), idx);
        }
        return ComptimeAllocId.fromFnIndex(idx);
    }

    /// Evaluates a zero-argument `MirBody` (e.g., `const` initializer or `comptime { … }` block)
    /// or a `MirBody` with pre-populated `arg_slots`.
    pub fn evalBody(
        self: *MirVm,
        body: *const MirBody,
        arg_slots: []const RegSlot,
    ) VmEvalError!VmEvalResult {
        self.active_inst_span = Span.init(body.file_id, 0, 0);
        const ret_slot = try self.invokeBodyInternal(
            body,
            arg_slots,
            &.{},
            Span.init(body.file_id, 0, 0),
        );
        const ret_repr = classifyValueRepr(self.pool, self.sym_table, body.ret_ty, self.options.target_layout);
        // Verify no dangling stack pointer escaped in the top-level return value (`E0506`):
        try self.verifyNoEscapingStackPointers(body.ret_ty, ret_repr, ret_slot);
        return .{
            .type_id = body.ret_ty,
            .repr = ret_repr,
            .slot = ret_slot,
            .steps_executed = self.steps_executed,
        };
    }

    // ----------- Diagnostics & Stack-Trace Construction -----------

    /// Resolves `(file_id, tok_idx)` into a concrete `Span` using `options.file_tokens` when available.
    fn resolveTokenSpan(self: *const MirVm, file_id: FileId, tok_idx: TokenIndex) Span {
        if (!tok_idx.isNone()) {
            if (self.options.file_tokens) |tok_map| {
                if (tok_map.get(file_id.asInt())) |tok_buf| {
                    if (tok_idx.asInt() < tok_buf.countTokens()) {
                        return tok_buf.getTokenSpan(file_id, tok_idx);
                    }
                }
            }
        }
        return Span.init(file_id, 0, 0);
    }

    /// Formats and emits a trap diagnostic without leaking intermediate strings, then returns `err_tag`.
    pub fn failWithTrap(
        self: *MirVm,
        err_tag: VmEvalError,
        code: DiagnosticCode,
        message: []const u8,
        primary_label: []const u8,
        help_note: ?[]const u8,
    ) VmEvalError {
        if (self.diagnostic_sink) |sink| {
            const trap_span = self.active_inst_span;
            var labels: std.ArrayListUnmanaged(LabeledSpan) = .empty;
            defer labels.deinit(self.allocator);

            labels.append(self.allocator, .{
                .span = trap_span,
                .label = primary_label,
                .style = .primary,
            }) catch return error.OutOfMemory;

            var depth_idx = self.call_stack.items.len;
            while (depth_idx > 1) {
                depth_idx -= 1;
                const frame = self.call_stack.items[depth_idx];
                const caller_frame = self.call_stack.items[depth_idx - 1];
                const caller_name = if (caller_frame.body.name != .empty)
                    self.interner.get(caller_frame.body.name)
                else
                    "<comptime>";
                var stack_buf: [160]u8 = undefined;
                const formatted = std.fmt.bufPrint(
                    &stack_buf,
                    "called at `comptime` from `{s}`",
                    .{caller_name},
                ) catch "called at `comptime`";
                const owned_lbl = sink.arena.dupe(u8, formatted) catch return error.OutOfMemory;
                labels.append(self.allocator, .{
                    .span = frame.call_site_span,
                    .label = owned_lbl,
                    .style = .secondary,
                }) catch return error.OutOfMemory;
            }

            var note_arr: [1][]const u8 = undefined;
            const notes_slice: []const []const u8 = if (help_note) |note_str| blk: {
                note_arr[0] = note_str;
                break :blk note_arr[0..1];
            } else &.{};

            sink.emit(.{
                .code = code,
                .severity = .err,
                .primary_span = trap_span,
                .message = message,
                .labels = labels.items,
                .notes = notes_slice,
            }) catch return error.OutOfMemory;
        }
        if (self.abort_on_panic_depth > 0) {
            self.has_aborted_vacated_panic = true;
            return error.AbortedVacatedPanic;
        }
        return err_tag;
    }

    // ---------- Allocation, `init_mask` & Provenance API ----------

    /// Allocates a new `ComptimeAllocation` in `self.arena` (`[CRITICAL-03]` clamped `<= 16B` host align).
    pub fn allocMemory(
        self: *MirVm,
        byte_size: u64,
        align_log2: u8,
        is_mutable: bool,
        is_stack_frame: bool,
        is_zero_initialized: bool,
        soa_elem_capacity: u32,
        origin_span: Span,
    ) VmEvalError!ComptimeAllocId {
        if (self.allocations.items.len >= ALLOC_PAYLOAD_MASK) {
            return self.failWithTrap(
                error.ResourceLimitExceeded,
                .e0508_comptime_resource_limit_exceeded,
                "`comptime` allocation count exceeded 30-bit `ComptimeAllocId` capacity",
                "allocation limit exceeded here",
                null,
            );
        }
        const next_bytes = std.math.add(u64, self.bytes_used, byte_size) catch {
            return self.failWithTrap(
                error.ResourceLimitExceeded,
                .e0508_comptime_resource_limit_exceeded,
                "`comptime` memory usage overflowed 64-bit byte counter",
                "memory cap exceeded here",
                null,
            );
        };
        if (next_bytes > self.options.mem_limit or byte_size > std.math.maxInt(u32)) {
            return self.failWithTrap(
                error.ResourceLimitExceeded,
                .e0508_comptime_resource_limit_exceeded,
                "`comptime` memory limit (`64 MiB`) exceeded during evaluation",
                "allocation exceeded memory budget here",
                null,
            );
        }

        const size_usize: usize = @intCast(byte_size);
        const clamped_shift: u4 = @intCast(@min(align_log2, 4));
        const host_align: usize = @min(@as(usize, 1) << clamped_shift, MAX_HOST_ALIGN_BYTES);
        const raw_bytes: []u8 = if (size_usize > 0)
            self.arena.allocAligned(size_usize, host_align) catch return error.OutOfMemory
        else
            &.{};
        if (size_usize > 0) @memset(raw_bytes, 0);

        const mask_words = (size_usize + 63) / 64;
        const init_mask: []u64 = if (mask_words > 0)
            self.arena.allocSlice(u64, mask_words) catch return error.OutOfMemory
        else
            &.{};
        if (mask_words > 0) {
            @memset(init_mask, if (is_zero_initialized) std.math.maxInt(u64) else 0);
        }

        const slot_idx: u32 = @intCast(self.allocations.items.len);
        self.allocations.append(self.allocator, .{
            .bytes = raw_bytes,
            .init_mask = init_mask,
            .align_log2 = align_log2,
            .is_mutable = is_mutable,
            .is_live = true,
            .is_stack_frame = is_stack_frame,
            .soa_elem_capacity = soa_elem_capacity,
            .origin_span = origin_span,
        }) catch return error.OutOfMemory;

        self.bytes_used = next_bytes;
        return ComptimeAllocId.fromVmIndex(slot_idx);
    }

    /// Returns `true` if byte `byte_idx` is marked initialized inside `alloc_rec`.
    inline fn isByteInitialized(alloc_rec: *const ComptimeAllocation, byte_idx: usize) bool {
        const word_idx = byte_idx >> 6;
        const bit_idx: u6 = @intCast(byte_idx & 63);
        return ((alloc_rec.init_mask[word_idx] >> bit_idx) & 1) != 0;
    }

    /// Sets or clears byte `byte_idx` in `alloc_rec.init_mask`.
    inline fn setByteInitialized(
        alloc_rec: *ComptimeAllocation,
        byte_idx: usize,
        is_init: bool,
    ) void {
        const word_idx = byte_idx >> 6;
        const bit_idx: u6 = @intCast(byte_idx & 63);
        if (is_init) {
            alloc_rec.init_mask[word_idx] |= (@as(u64, 1) << bit_idx);
        } else {
            alloc_rec.init_mask[word_idx] &= ~(@as(u64, 1) << bit_idx);
        }
    }

    /// Marks `[offset .. offset + len)` initialized in `alloc_rec.init_mask`.
    fn markRangeInitialized(alloc_rec: *ComptimeAllocation, offset: usize, len: usize) void {
        var idx = offset;
        while (idx < offset + len) : (idx += 1) {
            setByteInitialized(alloc_rec, idx, true);
        }
    }

    /// Removes any `ProvenanceEntry` in `alloc_rec` overlapping `[offset .. offset + len)` (`[CRITICAL-03]`).
    fn clearOverlappingProvenance(
        self: *const MirVm,
        alloc_rec: *ComptimeAllocation,
        offset: u32,
        len: u32,
    ) void {
        const items = alloc_rec.provenance.items;
        if (len == 0 or items.len == 0) return;
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        // O(1) fast-path for sequential/monotonic tail writes:
        if (@as(u64, items[items.len - 1].byte_offset) + ptr_width <= @as(u64, offset)) return;

        var low: usize = 0;
        var high: usize = items.len;
        while (low < high) {
            const mid = low + (high - low) / 2;
            if (@as(u64, items[mid].byte_offset) + ptr_width <= @as(u64, offset)) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        const first_overlap = low;
        if (first_overlap >= items.len) return;

        const write_end: u64 = @as(u64, offset) + @as(u64, len);
        var end_low: usize = first_overlap;
        var end_high: usize = items.len;
        while (end_low < end_high) {
            const mid = end_low + (end_high - end_low) / 2;
            if (@as(u64, items[mid].byte_offset) < write_end) {
                end_low = mid + 1;
            } else {
                end_high = mid;
            }
        }
        const after_overlap = end_low;
        if (after_overlap > first_overlap) {
            const remove_count = after_overlap - first_overlap;
            std.mem.copyForwards(
                ProvenanceEntry,
                items[first_overlap .. items.len - remove_count],
                items[after_overlap..],
            );
            alloc_rec.provenance.items.len = items.len - remove_count;
        }
    }

    /// Returns `true` if any `ProvenanceEntry` in `alloc_rec` overlaps `[offset .. offset + len)`.
    fn hasOverlappingProvenance(
        self: *const MirVm,
        alloc_rec: *const ComptimeAllocation,
        offset: u32,
        len: u32,
    ) bool {
        const items = alloc_rec.provenance.items;
        if (len == 0 or items.len == 0) return false;
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        if (@as(u64, items[items.len - 1].byte_offset) + ptr_width <= @as(u64, offset)) return false;

        var low: usize = 0;
        var high: usize = items.len;
        while (low < high) {
            const mid = low + (high - low) / 2;
            if (@as(u64, items[mid].byte_offset) + ptr_width <= @as(u64, offset)) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        if (low >= items.len) return false;
        const read_end: u64 = @as(u64, offset) + @as(u64, len);
        return @as(u64, items[low].byte_offset) < read_end;
    }

    /// Inserts `entry` into `alloc_rec.provenance` maintaining sorted `byte_offset` order (`[CRITICAL-03]`).
    fn insertProvenanceSorted(
        self: *MirVm,
        alloc_rec: *ComptimeAllocation,
        entry: ProvenanceEntry,
    ) !void {
        const items = alloc_rec.provenance.items;
        // O(1) fast-path for monotonic tail writes (`[&X; 200_000]`):
        if (items.len == 0 or items[items.len - 1].byte_offset < entry.byte_offset) {
            try alloc_rec.provenance.append(self.allocator, entry);
            return;
        }
        var low: usize = 0;
        var high: usize = items.len;
        while (low < high) {
            const mid = low + (high - low) / 2;
            if (items[mid].byte_offset < entry.byte_offset) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        try alloc_rec.provenance.insert(self.allocator, low, entry);
    }

    /// Looks up an exact `ProvenanceEntry` at `byte_offset` in $O(\log P)$ time.
    fn findExactProvenance(
        alloc_rec: *const ComptimeAllocation,
        byte_offset: u32,
    ) ?ComptimeAllocId {
        const items = alloc_rec.provenance.items;
        var low: usize = 0;
        var high: usize = items.len;
        while (low < high) {
            const mid = low + (high - low) / 2;
            if (items[mid].byte_offset < byte_offset) {
                low = mid + 1;
            } else if (items[mid].byte_offset > byte_offset) {
                high = mid;
            } else {
                return items[mid].alloc_id;
            }
        }
        return null;
    }

    /// Advances `base` by `delta` bytes, trapping with `E0506` on non-addressable handles and `E0504` on `u32` overflow.
    fn advanceSymbolicPtr(self: *MirVm, base: SymbolicPtr, delta: u64) VmEvalError!SymbolicPtr {
        if (delta == 0) return base;
        if (base.alloc_id.isNullOrNone() or base.alloc_id.isFnAddr()) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "cannot offset null or function pointer during `comptime` evaluation",
                "invalid base pointer for offset calculation",
                null,
            );
        }
        const next_off = std.math.add(u64, base.byte_offset, delta) catch {
            return self.failWithTrap(
                error.OutOfBounds,
                .e0504_comptime_out_of_bounds,
                "pointer byte offset overflowed 64-bit bounds during `comptime` evaluation",
                "pointer offset overflow here",
                null,
            );
        };
        if (next_off > std.math.maxInt(u32)) {
            return self.failWithTrap(
                error.OutOfBounds,
                .e0504_comptime_out_of_bounds,
                "pointer byte offset exceeded 32-bit `SymbolicPtr` range during `comptime` evaluation",
                "pointer offset exceeds `u32` limit here",
                null,
            );
        }
        return .{ .alloc_id = base.alloc_id, .byte_offset = @intCast(next_off) };
    }

    /// Multiplies `elem_index * elem_stride` with overflow checking (`E0504` on `u64` overflow).
    fn mulOffsetChecked(self: *MirVm, elem_index: u128, elem_stride: u64) VmEvalError!u64 {
        if (elem_stride == 0 or elem_index == 0) return 0;
        if (elem_index > std.math.maxInt(u64)) {
            return self.failWithTrap(
                error.OutOfBounds,
                .e0504_comptime_out_of_bounds,
                "element byte offset overflowed 64-bit bounds during `comptime` evaluation",
                "element index overflow here",
                null,
            );
        }
        return std.math.mul(u64, @intCast(elem_index), elem_stride) catch {
            return self.failWithTrap(
                error.OutOfBounds,
                .e0504_comptime_out_of_bounds,
                "element byte offset overflowed 64-bit bounds during `comptime` evaluation",
                "element byte offset overflow here",
                null,
            );
        };
    }

    /// Validates temporal liveness, virtual alignment, mutability, and spatial bounds on `ptr`.
    fn validateAccess(
        self: *MirVm,
        ptr: SymbolicPtr,
        access_size: u64,
        req_align_log2: u8,
        is_write: bool,
    ) VmEvalError!usize {
        if (ptr.alloc_id.isNullOrNone()) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "dereference of null or uninitialized pointer during `comptime` evaluation",
                "null pointer dereferenced here",
                null,
            );
        }
        if (ptr.alloc_id.isFnAddr()) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "cannot read or write memory through a function pointer at `comptime`",
                "function pointer dereferenced as data here",
                null,
            );
        }

        const req_align_bytes: u64 = @as(u64, 1) << @intCast(@min(req_align_log2, 30));
        if ((@as(u64, ptr.byte_offset) & (req_align_bytes - 1)) != 0) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "misaligned pointer dereference during `comptime` evaluation",
                "pointer offset violates required type alignment",
                null,
            );
        }

        const end_off = std.math.add(u64, ptr.byte_offset, access_size) catch {
            return self.failWithTrap(
                error.OutOfBounds,
                .e0504_comptime_out_of_bounds,
                "pointer offset + access size overflowed 64-bit bounds at `comptime`",
                "out-of-bounds memory access here",
                null,
            );
        };

        switch (ptr.alloc_id.domain()) {
            .vm_alloc => {
                const idx = ptr.alloc_id.payloadIndex();
                if (idx == 0 or idx >= self.allocations.items.len) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "invalid `ComptimeAllocId` handle dereferenced during `comptime` evaluation",
                        "invalid allocation handle",
                        null,
                    );
                }
                const alloc_rec = &self.allocations.items[idx];
                if (!alloc_rec.is_live) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "use-after-free of dead stack or deallocated memory at `comptime`",
                        "dangling pointer dereferenced here",
                        null,
                    );
                }
                if (alloc_rec.align_log2 < req_align_log2) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "underlying allocation alignment is weaker than pointer dereference alignment",
                        "under-aligned base allocation dereferenced here",
                        null,
                    );
                }
                if (is_write and !alloc_rec.is_mutable) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "cannot mutate immutable allocation during `comptime` evaluation",
                        "attempted write to read-only memory",
                        null,
                    );
                }
                if (end_off > alloc_rec.bytes.len) {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "spatial out-of-bounds memory access during `comptime` evaluation",
                        "access exceeds allocation byte length",
                        null,
                    );
                }
                return alloc_rec.bytes.len;
            },
            .rodata_blob => {
                if (is_write) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "cannot mutate promoted `.rodata` constant during `comptime` evaluation",
                        "attempted write to `.rodata` constant",
                        null,
                    );
                }
                const blob = self.rodata_pool.getBlob(ptr.alloc_id.payloadIndex()) orelse {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "invalid `.rodata` blob handle dereferenced at `comptime`",
                        "invalid `.rodata` handle",
                        null,
                    );
                };
                if (blob.align_log2 < req_align_log2) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "under-aligned `.rodata` blob dereferenced at `comptime`",
                        "misaligned `.rodata` dereference",
                        null,
                    );
                }
                if (end_off > blob.bytes.len) {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "out-of-bounds read on `.rodata` constant at `comptime`",
                        "read exceeds `.rodata` byte length",
                        null,
                    );
                }
                return blob.bytes.len;
            },
            .string_lit => {
                if (is_write) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "cannot mutate immutable string literal bytes at `comptime`",
                        "attempted write to string literal",
                        null,
                    );
                }
                if (req_align_log2 > 0) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "string literal bytes only guarantee 1-byte alignment at `comptime`",
                        "over-aligned dereference of string literal",
                        null,
                    );
                }
                const str_slice = self.interner.get(SymbolId.fromInt(ptr.alloc_id.payloadIndex()));
                if (end_off > str_slice.len) {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "out-of-bounds byte read on string literal at `comptime`",
                        "read exceeds string literal length",
                        null,
                    );
                }
                return str_slice.len;
            },
            .fn_or_none => unreachable,
        }
    }

    /// Reads `dest_buf.len` scalar bytes from `ptr`, enforcing `init_mask` (`E0505`) and zero provenance overlap (`E0503`).
    pub fn readScalarBytes(
        self: *MirVm,
        ptr: SymbolicPtr,
        req_align_log2: u8,
        dest_buf: []u8,
    ) VmEvalError!void {
        _ = try self.validateAccess(ptr, dest_buf.len, req_align_log2, false);
        if (dest_buf.len == 0) return;

        const start_off: usize = ptr.byte_offset;
        switch (ptr.alloc_id.domain()) {
            .vm_alloc => {
                const alloc_rec = &self.allocations.items[ptr.alloc_id.payloadIndex()];
                for (0..dest_buf.len) |off_i| {
                    if (!isByteInitialized(alloc_rec, start_off + off_i)) {
                        return self.failWithTrap(
                            error.UninitializedRead,
                            .e0505_comptime_uninitialized_read,
                            "read of uninitialized memory byte during `comptime` evaluation",
                            "uninitialized memory read here",
                            null,
                        );
                    }
                }
                if (self.hasOverlappingProvenance(alloc_rec, ptr.byte_offset, @intCast(dest_buf.len))) {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "cannot reinterpret pointer provenance bytes as raw scalar data at `comptime`",
                        "scalar read overlaps pointer provenance here",
                        null,
                    );
                }
                @memcpy(dest_buf, alloc_rec.bytes[start_off .. start_off + dest_buf.len]);
            },
            .rodata_blob => {
                const blob = self.rodata_pool.getBlob(ptr.alloc_id.payloadIndex()).?;
                const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
                const read_end: u64 = @as(u64, ptr.byte_offset) + dest_buf.len;
                for (blob.relocs) |reloc| {
                    const rel_start: u64 = reloc.byte_offset;
                    const rel_end: u64 = rel_start + ptr_width;
                    if (rel_start < read_end and @as(u64, ptr.byte_offset) < rel_end) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "cannot reinterpret `.rodata` relocation pointer as scalar bytes at `comptime`",
                            "scalar read overlaps `.rodata` pointer relocation",
                            null,
                        );
                    }
                }
                @memcpy(dest_buf, blob.bytes[start_off .. start_off + dest_buf.len]);
            },
            .string_lit => {
                const str_slice = self.interner.get(SymbolId.fromInt(ptr.alloc_id.payloadIndex()));
                @memcpy(dest_buf, str_slice[start_off .. start_off + dest_buf.len]);
            },
            .fn_or_none => unreachable,
        }
    }

    /// Writes `src_bytes` into `ptr`, setting `init_mask` bits and erasing overlapping provenance (`[CRITICAL-10]`).
    pub fn writeScalarBytes(
        self: *MirVm,
        ptr: SymbolicPtr,
        req_align_log2: u8,
        src_bytes: []const u8,
    ) VmEvalError!void {
        _ = try self.validateAccess(ptr, src_bytes.len, req_align_log2, true);
        if (src_bytes.len == 0) return;

        const alloc_rec = &self.allocations.items[ptr.alloc_id.payloadIndex()];
        const start_off: usize = ptr.byte_offset;
        @memcpy(alloc_rec.bytes[start_off .. start_off + src_bytes.len], src_bytes);
        markRangeInitialized(alloc_rec, start_off, src_bytes.len);
        self.clearOverlappingProvenance(alloc_rec, ptr.byte_offset, @intCast(src_bytes.len));
    }

    /// Stores `sym_ptr` at `dest_ptr` under `target_layout`, recording exact `ProvenanceEntry` (`[CRITICAL-10]`).
    pub fn writePointerAt(
        self: *MirVm,
        dest_ptr: SymbolicPtr,
        req_align_log2: u8,
        sym_ptr: SymbolicPtr,
    ) VmEvalError!void {
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        _ = try self.validateAccess(dest_ptr, ptr_width, req_align_log2, true);

        const alloc_rec = &self.allocations.items[dest_ptr.alloc_id.payloadIndex()];
        const start_off: usize = dest_ptr.byte_offset;
        if (ptr_width == 8) {
            std.mem.writeInt(u64, alloc_rec.bytes[start_off..][0..8], sym_ptr.byte_offset, .little);
        } else {
            std.mem.writeInt(u32, alloc_rec.bytes[start_off..][0..4], sym_ptr.byte_offset, .little);
        }
        markRangeInitialized(alloc_rec, start_off, ptr_width);
        self.clearOverlappingProvenance(alloc_rec, dest_ptr.byte_offset, ptr_width);
        self.insertProvenanceSorted(alloc_rec, .{
            .byte_offset = dest_ptr.byte_offset,
            .alloc_id = sym_ptr.alloc_id,
        }) catch return error.OutOfMemory;
    }

    /// Loads a `SymbolicPtr` from `src_ptr`, requiring `init_mask` all `1`s (`E0505`) and exact provenance (`E0503`).
    pub fn readPointerAt(
        self: *MirVm,
        src_ptr: SymbolicPtr,
        req_align_log2: u8,
    ) VmEvalError!SymbolicPtr {
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        _ = try self.validateAccess(src_ptr, ptr_width, req_align_log2, false);

        const start_off: usize = src_ptr.byte_offset;
        switch (src_ptr.alloc_id.domain()) {
            .vm_alloc => {
                const alloc_rec = &self.allocations.items[src_ptr.alloc_id.payloadIndex()];
                for (0..ptr_width) |off_i| {
                    if (!isByteInitialized(alloc_rec, start_off + off_i)) {
                        return self.failWithTrap(
                            error.UninitializedRead,
                            .e0505_comptime_uninitialized_read,
                            "read of uninitialized pointer bytes during `comptime` evaluation",
                            "uninitialized pointer slot read here",
                            null,
                        );
                    }
                }
                const target_alloc = findExactProvenance(alloc_rec, src_ptr.byte_offset) orelse {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "cannot forge pointer from raw integer bytes without provenance at `comptime`",
                        "pointer load lacks valid provenance entry",
                        null,
                    );
                };
                const stored_off: u64 = if (ptr_width == 8)
                    std.mem.readInt(u64, alloc_rec.bytes[start_off..][0..8], .little)
                else
                    std.mem.readInt(u32, alloc_rec.bytes[start_off..][0..4], .little);
                if (stored_off > std.math.maxInt(u32)) {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "loaded pointer offset exceeds 32-bit `SymbolicPtr` range",
                        "pointer offset out of range",
                        null,
                    );
                }
                return .{ .alloc_id = target_alloc, .byte_offset = @intCast(stored_off) };
            },
            .rodata_blob => {
                const blob = self.rodata_pool.getBlob(src_ptr.alloc_id.payloadIndex()).?;
                var matched_alloc: ?ComptimeAllocId = null;
                for (blob.relocs) |reloc| {
                    if (reloc.byte_offset == src_ptr.byte_offset) {
                        matched_alloc = reloc.target_alloc;
                        break;
                    }
                }
                const target_alloc = matched_alloc orelse {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "cannot forge pointer from `.rodata` integer bytes without relocation",
                        "missing `.rodata` pointer relocation",
                        null,
                    );
                };
                const stored_off: u64 = if (ptr_width == 8)
                    std.mem.readInt(u64, blob.bytes[start_off..][0..8], .little)
                else
                    std.mem.readInt(u32, blob.bytes[start_off..][0..4], .little);
                if (stored_off > std.math.maxInt(u32)) {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "loaded `.rodata` pointer offset exceeds 32-bit `SymbolicPtr` range",
                        "pointer offset out of range",
                        null,
                    );
                }
                return .{ .alloc_id = target_alloc, .byte_offset = @intCast(stored_off) };
            },
            .string_lit => {
                return self.failWithTrap(
                    error.ForbiddenOperation,
                    .e0503_forbidden_comptime_operation,
                    "cannot load pointer from raw string literal bytes at `comptime`",
                    "string literal has no pointer provenance",
                    null,
                );
            },
            .fn_or_none => unreachable,
        }
    }

    /// Copies `byte_len` bytes, `init_mask` bits (preserving uninitialized padding), and interior
    /// `ProvenanceEntry` records from `src_ptr` into `dst_ptr` (`[CRITICAL-10]`).
    pub fn copyMemoryRange(
        self: *MirVm,
        dst_ptr: SymbolicPtr,
        src_ptr: SymbolicPtr,
        byte_len: u64,
        req_align_log2: u8,
    ) VmEvalError!void {
        _ = try self.validateAccess(dst_ptr, byte_len, req_align_log2, true);
        _ = try self.validateAccess(src_ptr, byte_len, req_align_log2, false);
        if (byte_len == 0) return;

        const len_usize: usize = @intCast(byte_len);
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;

        // Snapshot source bytes, per-byte init status, and interior provenance first (stack-buffered <= 64B):
        var stack_bytes: [64]u8 = undefined;
        var stack_init: [64]bool = undefined;
        var heap_bytes: ?[]u8 = null;
        defer if (heap_bytes) |buf| self.allocator.free(buf);
        var heap_init: ?[]bool = null;
        defer if (heap_init) |buf| self.allocator.free(buf);

        const tmp_bytes: []u8 = if (len_usize <= stack_bytes.len)
            stack_bytes[0..len_usize]
        else blk: {
            const allocated = self.allocator.alloc(u8, len_usize) catch return error.OutOfMemory;
            heap_bytes = allocated;
            break :blk allocated;
        };
        const tmp_init: []bool = if (len_usize <= stack_init.len)
            stack_init[0..len_usize]
        else blk: {
            const allocated = self.allocator.alloc(bool, len_usize) catch return error.OutOfMemory;
            heap_init = allocated;
            break :blk allocated;
        };
        var stack_prov: [8]ProvenanceEntry = undefined;
        var stack_prov_len: usize = 0;
        var tmp_prov: std.ArrayListUnmanaged(ProvenanceEntry) = .empty;
        defer tmp_prov.deinit(self.allocator);

        const src_start: usize = src_ptr.byte_offset;
        switch (src_ptr.alloc_id.domain()) {
            .vm_alloc => {
                const src_rec = &self.allocations.items[src_ptr.alloc_id.payloadIndex()];
                @memcpy(tmp_bytes, src_rec.bytes[src_start .. src_start + len_usize]);
                for (0..len_usize) |i| {
                    tmp_init[i] = isByteInitialized(src_rec, src_start + i);
                }
                const copy_end: u64 = @as(u64, src_ptr.byte_offset) + byte_len;
                const prov_items = src_rec.provenance.items;
                var low: usize = 0;
                var high: usize = prov_items.len;
                while (low < high) {
                    const mid = low + (high - low) / 2;
                    if (@as(u64, prov_items[mid].byte_offset) + ptr_width <= @as(u64, src_ptr.byte_offset)) {
                        low = mid + 1;
                    } else {
                        high = mid;
                    }
                }
                var prov_idx = low;
                while (prov_idx < prov_items.len) : (prov_idx += 1) {
                    const entry = prov_items[prov_idx];
                    const e_start: u64 = entry.byte_offset;
                    if (e_start >= copy_end) break;
                    const e_end: u64 = e_start + ptr_width;
                    if (e_start >= src_ptr.byte_offset and e_end <= copy_end) {
                        const rel_item = ProvenanceEntry{
                            .byte_offset = entry.byte_offset - src_ptr.byte_offset,
                            .alloc_id = entry.alloc_id,
                        };
                        if (tmp_prov.items.len == 0 and stack_prov_len < stack_prov.len) {
                            stack_prov[stack_prov_len] = rel_item;
                            stack_prov_len += 1;
                        } else {
                            if (tmp_prov.items.len == 0 and stack_prov_len > 0) {
                                tmp_prov.appendSlice(self.allocator, stack_prov[0..stack_prov_len]) catch
                                    return error.OutOfMemory;
                            }
                            tmp_prov.append(self.allocator, rel_item) catch return error.OutOfMemory;
                        }
                    } else if (e_start < copy_end and @as(u64, src_ptr.byte_offset) < e_end) {
                        // Tearing a pointer across copy boundaries destroys provenance -> trap `E0503`:
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "partial byte copy tore a pointer's provenance at `comptime`",
                            "partial pointer copy here",
                            null,
                        );
                    }
                }
            },
            .rodata_blob => {
                const blob = self.rodata_pool.getBlob(src_ptr.alloc_id.payloadIndex()).?;
                @memcpy(tmp_bytes, blob.bytes[src_start .. src_start + len_usize]);
                @memset(tmp_init, true);
                const copy_end: u64 = @as(u64, src_ptr.byte_offset) + byte_len;
                for (blob.relocs) |reloc| {
                    const r_start: u64 = reloc.byte_offset;
                    const r_end: u64 = r_start + ptr_width;
                    if (r_start >= src_ptr.byte_offset and r_end <= copy_end) {
                        tmp_prov.append(self.allocator, .{
                            .byte_offset = reloc.byte_offset - src_ptr.byte_offset,
                            .alloc_id = reloc.target_alloc,
                        }) catch return error.OutOfMemory;
                    } else if (r_start < copy_end and @as(u64, src_ptr.byte_offset) < r_end) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "partial byte copy tore a `.rodata` pointer relocation at `comptime`",
                            "partial `.rodata` pointer copy here",
                            null,
                        );
                    }
                }
            },
            .string_lit => {
                const str_slice = self.interner.get(SymbolId.fromInt(src_ptr.alloc_id.payloadIndex()));
                @memcpy(tmp_bytes, str_slice[src_start .. src_start + len_usize]);
                @memset(tmp_init, true);
            },
            .fn_or_none => unreachable,
        }

        const dst_rec = &self.allocations.items[dst_ptr.alloc_id.payloadIndex()];
        const dst_start: usize = dst_ptr.byte_offset;
        @memcpy(dst_rec.bytes[dst_start .. dst_start + len_usize], tmp_bytes);
        for (0..len_usize) |i| {
            setByteInitialized(dst_rec, dst_start + i, tmp_init[i]);
        }
        self.clearOverlappingProvenance(dst_rec, dst_ptr.byte_offset, @intCast(byte_len));
        const active_prov = if (tmp_prov.items.len > 0) tmp_prov.items else stack_prov[0..stack_prov_len];
        for (active_prov) |rel_entry| {
            const shifted_ptr = try self.advanceSymbolicPtr(dst_ptr, rel_entry.byte_offset);
            self.insertProvenanceSorted(dst_rec, .{
                .byte_offset = shifted_ptr.byte_offset,
                .alloc_id = rel_entry.alloc_id,
            }) catch return error.OutOfMemory;
        }
    }

    // ------- `RegSlot` <-> Memory Load / Store Marshalling --------

    /// Allocates an immutable `by_value_snapshot` `ComptimeAllocation` for `ty`.
    fn allocSnapshotForType(self: *MirVm, ty: TypeId, is_zero_init: bool) VmEvalError!SymbolicPtr {
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            ty,
            self.options.target_layout,
        );
        const unwrapped = self.pool.unwrapUnderlyingType(ty);
        const ty_node = self.pool.getNode(unwrapped);
        const soa_cap: u32 = if (ty_node.tag == .soa_array_ty)
            (ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG)
        else
            0;
        const alloc_id = try self.allocMemory(
            lay.byte_size,
            lay.align_log2,
            true, // Mutable during construction, sealed to `false` once populated.
            false,
            is_zero_init,
            soa_cap,
            self.active_inst_span,
        );
        return .{ .alloc_id = alloc_id, .byte_offset = 0 };
    }

    /// Seals a temporary `by_value_snapshot` allocation so subsequent SSA consumers treat it as immutable.
    inline fn sealSnapshot(self: *MirVm, snap_ptr: SymbolicPtr) void {
        if (snap_ptr.alloc_id.domain() == .vm_alloc) {
            const idx = snap_ptr.alloc_id.payloadIndex();
            if (idx > 0 and idx < self.allocations.items.len) {
                self.allocations.items[idx].is_mutable = false;
            }
        }
    }

    /// Transposes an AoS struct `elem_slot` into element `elem_index` across all columns of `#soa [S; cap]`.
    fn storeSoaArrayElementFromSlot(
        self: *MirVm,
        soa_base: SymbolicPtr,
        elem_struct_ty: TypeId,
        elem_capacity: u32,
        elem_index: usize,
        elem_slot: RegSlot,
    ) VmEvalError!void {
        const src_align_override = isPackedStructType(self.pool, self.sym_table, elem_struct_ty);
        var field_ord: u32 = 0;
        while (computeCompositeFieldOffsetAndType(
            self.pool,
            self.sym_table,
            elem_struct_ty,
            field_ord,
            self.options.target_layout,
        )) |src_field| : (field_ord += 1) {
            const dst_col = computeSoaColumnOffsetAndType(
                self.pool,
                self.sym_table,
                elem_struct_ty,
                field_ord,
                elem_capacity,
                self.options.target_layout,
            ) orelse break;
            const field_lay = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                dst_col.field_ty,
                self.options.target_layout,
            );
            const src_field_ptr = try self.advanceSymbolicPtr(elem_slot.sym_ptr, src_field.byte_offset);
            const col_base_ptr = try self.advanceSymbolicPtr(soa_base, dst_col.column_byte_offset);
            const elem_delta = try self.mulOffsetChecked(elem_index, field_lay.byte_size);
            const dst_field_ptr = try self.advanceSymbolicPtr(col_base_ptr, elem_delta);
            try self.copyMemoryRange(
                dst_field_ptr,
                src_field_ptr,
                field_lay.byte_size,
                if (src_align_override) 0 else field_lay.align_log2,
            );
        }
    }

    /// Reads an arbitrary `u128` / `i128` integer value from `slot` (`inline_scalar` or `16B` snapshot).
    fn readIntBitsFromSlot(self: *MirVm, slot: RegSlot, raw_ty: TypeId) VmEvalError!u128 {
        const info = resolveIntInfo(self.pool, raw_ty, self.options.target_layout) orelse return 0;
        if (info.bits <= 64) {
            return maskToBitsU128(slot.scalar_u64, info.bits);
        }
        var buf: [16]u8 = undefined;
        try self.readScalarBytes(slot.sym_ptr, 0, &buf);
        return std.mem.readInt(u128, &buf, .little);
    }

    /// Materializes a `RegSlot` for an integer of `raw_ty` from `val_u128`.
    fn makeIntSlot(self: *MirVm, raw_ty: TypeId, val_u128: u128) VmEvalError!RegSlot {
        const info = resolveIntInfo(self.pool, raw_ty, self.options.target_layout) orelse
            return .{ .scalar_u64 = 0 };
        const masked = maskToBitsU128(val_u128, info.bits);
        if (info.bits <= 64) {
            if (info.is_signed) {
                const signed_v: i64 = @truncate(signExtendToI128(masked, info.bits));
                return .{ .scalar_i64 = signed_v };
            }
            return .{ .scalar_u64 = @truncate(masked) };
        }
        const snap = try self.allocSnapshotForType(raw_ty, false);
        var buf: [16]u8 = undefined;
        std.mem.writeInt(u128, &buf, masked, .little);
        try self.writeScalarBytes(snap, 0, &buf);
        self.sealSnapshot(snap);
        return .{ .sym_ptr = snap };
    }

    /// Loads a typed `RegSlot` from `place_ptr` (`[CRITICAL-04]`, `[CRITICAL-10]`).
    pub fn loadTypedSlotFromMemory(
        self: *MirVm,
        place_ptr: SymbolicPtr,
        raw_ty: TypeId,
    ) VmEvalError!RegSlot {
        return self.loadTypedSlotFromMemoryAligned(place_ptr, raw_ty, false);
    }

    /// Loads a typed `RegSlot` from `place_ptr`, allowing 1-byte alignment when `is_unaligned` (`@packed`).
    pub fn loadTypedSlotFromMemoryAligned(
        self: *MirVm,
        place_ptr: SymbolicPtr,
        raw_ty: TypeId,
        is_unaligned: bool,
    ) VmEvalError!RegSlot {
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            ty,
            self.options.target_layout,
        );
        const eff_align_log2: u8 = if (is_unaligned) 0 else lay.align_log2;
        const repr = classifyValueRepr(self.pool, self.sym_table, ty, self.options.target_layout);

        switch (repr) {
            .inline_scalar => {
                if (lay.byte_size == 0) return .{ .scalar_u64 = 0 };
                var buf: [8]u8 = @splat(0);
                const byte_len: usize = @intCast(lay.byte_size);
                try self.readScalarBytes(place_ptr, eff_align_log2, buf[0..byte_len]);
                if (ty == .f64_ty or ty == .untyped_float_ty) {
                    const bits = std.mem.readInt(u64, &buf, .little);
                    return .{ .scalar_f64 = canonicalizeF64(@bitCast(bits)) };
                }
                if (ty == .f32_ty) {
                    const bits = std.mem.readInt(u32, buf[0..4], .little);
                    return packF32Slot(@bitCast(bits));
                }
                if (ty == .bool_ty) {
                    return .{ .scalar_u64 = if (buf[0] != 0) 1 else 0 };
                }
                const raw_u64 = std.mem.readInt(u64, &buf, .little);
                if (resolveIntInfo(self.pool, ty, self.options.target_layout)) |info| {
                    if (info.is_signed) {
                        const sext: i64 = @truncate(signExtendToI128(raw_u64, info.bits));
                        return .{ .scalar_i64 = sext };
                    }
                    return .{ .scalar_u64 = @truncate(maskToBitsU128(raw_u64, info.bits)) };
                }
                return .{ .scalar_u64 = raw_u64 };
            },
            .inline_ptr => {
                return .{ .sym_ptr = try self.readPointerAt(place_ptr, eff_align_log2) };
            },
            .by_value_snapshot => {
                // For `i128` / `u128`, validate all 16 bytes are initialized scalar bytes (`E0505`/`E0503`):
                if (ty == .i128_ty or ty == .u128_ty) {
                    var i128_buf: [16]u8 = undefined;
                    try self.readScalarBytes(place_ptr, eff_align_log2, &i128_buf);
                    const snap = try self.allocSnapshotForType(ty, false);
                    try self.writeScalarBytes(snap, 0, &i128_buf);
                    self.sealSnapshot(snap);
                    return .{ .sym_ptr = snap };
                }
                const snap = try self.allocSnapshotForType(ty, false);
                try self.copyMemoryRange(snap, place_ptr, lay.byte_size, eff_align_log2);
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
        }
    }

    /// Stores a typed `RegSlot` into `place_ptr` (`[CRITICAL-04]`, `[CRITICAL-10]`).
    pub fn storeTypedSlotToMemory(
        self: *MirVm,
        place_ptr: SymbolicPtr,
        raw_ty: TypeId,
        slot: RegSlot,
    ) VmEvalError!void {
        return self.storeTypedSlotToMemoryAligned(place_ptr, raw_ty, slot, false);
    }

    /// Stores a typed `RegSlot` into `place_ptr`, allowing 1-byte alignment when `is_unaligned` (`@packed`).
    pub fn storeTypedSlotToMemoryAligned(
        self: *MirVm,
        place_ptr: SymbolicPtr,
        raw_ty: TypeId,
        slot: RegSlot,
        is_unaligned: bool,
    ) VmEvalError!void {
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            ty,
            self.options.target_layout,
        );
        const eff_align_log2: u8 = if (is_unaligned) 0 else lay.align_log2;
        const repr = classifyValueRepr(self.pool, self.sym_table, ty, self.options.target_layout);

        switch (repr) {
            .inline_scalar => {
                if (lay.byte_size == 0) return;
                var buf: [8]u8 = @splat(0);
                if (ty == .f64_ty or ty == .untyped_float_ty) {
                    std.mem.writeInt(u64, &buf, @bitCast(canonicalizeF64(slot.scalar_f64)), .little);
                } else if (ty == .f32_ty) {
                    std.mem.writeInt(u32, buf[0..4], @bitCast(unpackF32Slot(slot)), .little);
                } else if (ty == .bool_ty) {
                    buf[0] = if ((slot.scalar_u64 & 1) != 0) 1 else 0;
                } else {
                    std.mem.writeInt(u64, &buf, slot.scalar_u64, .little);
                }
                const byte_len: usize = @intCast(lay.byte_size);
                try self.writeScalarBytes(place_ptr, eff_align_log2, buf[0..byte_len]);
            },
            .inline_ptr => {
                try self.writePointerAt(place_ptr, eff_align_log2, slot.sym_ptr);
            },
            .by_value_snapshot => {
                try self.copyMemoryRange(place_ptr, slot.sym_ptr, lay.byte_size, eff_align_log2);
            },
        }
    }

    /// Constructs a wide fat-pointer `(data_ptr, len)` snapshot for `str`, `[T]`, or `#soa [T]`.
    pub fn makeFatSliceSlot(
        self: *MirVm,
        slice_ty: TypeId,
        data_ptr: SymbolicPtr,
        elem_len: u64,
    ) VmEvalError!RegSlot {
        const snap = try self.allocSnapshotForType(slice_ty, false);
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        const effective_ptr = if (elem_len == 0 and data_ptr.alloc_id.isNullOrNone())
            SymbolicPtr{ .alloc_id = self.dangling_empty_alloc, .byte_offset = 0 }
        else
            data_ptr;
        try self.writePointerAt(snap, self.options.target_layout.ptr_align_log2, effective_ptr);
        const len_ptr = SymbolicPtr{ .alloc_id = snap.alloc_id, .byte_offset = ptr_width };
        if (ptr_width == 8) {
            var buf: [8]u8 = undefined;
            std.mem.writeInt(u64, &buf, elem_len, .little);
            try self.writeScalarBytes(len_ptr, 3, &buf);
        } else {
            var buf: [4]u8 = undefined;
            std.mem.writeInt(u32, &buf, @truncate(elem_len), .little);
            try self.writeScalarBytes(len_ptr, 2, &buf);
        }
        self.sealSnapshot(snap);
        return .{ .sym_ptr = snap };
    }

    /// Reads the active variant ordinal (`0 .. V - 1`) of `raw_sum_ty` at `base_ptr` (`[CRITICAL-04]`).
    pub fn readSumDiscriminantAt(
        self: *MirVm,
        base_ptr: SymbolicPtr,
        raw_sum_ty: TypeId,
    ) VmEvalError!u32 {
        const sum_ty = self.pool.unwrapUnderlyingType(raw_sum_ty);
        const sum_lay = type_system.computeSumMemoryLayout(
            self.pool,
            self.sym_table,
            sum_ty,
            self.options.target_layout,
        );
        switch (sum_lay.repr) {
            .transparent_ok => return 0,
            .niche_single => {
                const zst_ord: u32 = sum_lay.zst_discriminant;
                const pay_ord: u32 = sum_lay.payload_discriminant;
                const niche_ptr = try self.advanceSymbolicPtr(base_ptr, sum_lay.niche.byte_offset);
                if (sum_lay.niche.kind == .zero_ptr) {
                    const loaded_ptr = try self.readPointerAt(
                        niche_ptr,
                        self.options.target_layout.ptr_align_log2,
                    );
                    return if (loaded_ptr.alloc_id == .null_ptr) zst_ord else pay_ord;
                }
                var scalar_buf: [8]u8 = @splat(0);
                const s_len: usize = sum_lay.niche.scalar_bytes;
                try self.readScalarBytes(niche_ptr, 0, scalar_buf[0..s_len]);
                const raw_val = std.mem.readInt(u64, &scalar_buf, .little);
                return if (raw_val == sum_lay.niche.invalid_first) zst_ord else pay_ord;
            },
            .explicit_tag => {
                if (sum_lay.tag_bytes == 0) return 0;
                var tag_buf: [4]u8 = @splat(0);
                try self.readScalarBytes(base_ptr, 0, tag_buf[0..sum_lay.tag_bytes]);
                return std.mem.readInt(u32, &tag_buf, .little);
            },
        }
    }

    /// Writes the active variant ordinal (`tag_ord`) of `raw_sum_ty` into `base_ptr` (`[CRITICAL-04]`).
    pub fn writeSumDiscriminantAt(
        self: *MirVm,
        base_ptr: SymbolicPtr,
        raw_sum_ty: TypeId,
        tag_ord: u32,
    ) VmEvalError!void {
        const sum_ty = self.pool.unwrapUnderlyingType(raw_sum_ty);
        const sum_lay = type_system.computeSumMemoryLayout(
            self.pool,
            self.sym_table,
            sum_ty,
            self.options.target_layout,
        );
        switch (sum_lay.repr) {
            .transparent_ok => {},
            .niche_single => {
                if (tag_ord != sum_lay.zst_discriminant) return;
                const niche_ptr = try self.advanceSymbolicPtr(base_ptr, sum_lay.niche.byte_offset);
                if (sum_lay.niche.kind == .zero_ptr) {
                    try self.writePointerAt(
                        niche_ptr,
                        self.options.target_layout.ptr_align_log2,
                        SymbolicPtr.NULL,
                    );
                } else {
                    var niche_buf: [8]u8 = undefined;
                    std.mem.writeInt(u64, &niche_buf, sum_lay.niche.invalid_first, .little);
                    try self.writeScalarBytes(niche_ptr, 0, niche_buf[0..sum_lay.niche.scalar_bytes]);
                }
            },
            .explicit_tag => {
                if (sum_lay.tag_bytes > 0) {
                    var tag_buf: [4]u8 = undefined;
                    std.mem.writeInt(u32, &tag_buf, tag_ord, .little);
                    try self.writeScalarBytes(base_ptr, 0, tag_buf[0..sum_lay.tag_bytes]);
                }
            },
        }
    }

    /// Reads `(data_ptr, elem_len)` out of a `str`, `[T]`, or `#soa [T]` snapshot or memory location.
    pub fn readFatSliceParts(
        self: *MirVm,
        slice_base_ptr: SymbolicPtr,
    ) VmEvalError!struct { data_ptr: SymbolicPtr, elem_len: u64 } {
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        const ptr_align = self.options.target_layout.ptr_align_log2;
        const data_ptr = try self.readPointerAt(slice_base_ptr, ptr_align);
        const len_ptr = try self.advanceSymbolicPtr(slice_base_ptr, ptr_width);
        if (ptr_width == 8) {
            var buf: [8]u8 = undefined;
            try self.readScalarBytes(len_ptr, 3, &buf);
            return .{ .data_ptr = data_ptr, .elem_len = std.mem.readInt(u64, &buf, .little) };
        }
        var buf4: [4]u8 = undefined;
        try self.readScalarBytes(len_ptr, 2, &buf4);
        return .{ .data_ptr = data_ptr, .elem_len = std.mem.readInt(u32, &buf4, .little) };
    }

    // -------- Pure-Call Memoization & Stack Escape Checks ---------

    /// Verifies that a returned `RegSlot` does not carry a dangling or stack-local `ComptimeAllocId` (`E0506`).
    fn verifyNoEscapingStackPointers(
        self: *MirVm,
        raw_ty: TypeId,
        repr: VmValueRepr,
        slot: RegSlot,
    ) VmEvalError!void {
        _ = raw_ty;
        switch (repr) {
            .inline_scalar => return,
            .inline_ptr => {
                try self.checkPointerTargetNonStack(slot.sym_ptr.alloc_id);
            },
            .by_value_snapshot => {
                if (slot.sym_ptr.alloc_id.domain() == .vm_alloc) {
                    const idx = slot.sym_ptr.alloc_id.payloadIndex();
                    if (idx > 0 and idx < self.allocations.items.len) {
                        var visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
                        defer visited.deinit(self.allocator);
                        try self.verifySnapshotProvenanceNonStack(idx, &visited);
                    }
                }
            },
        }
    }

    /// Recursively inspects embedded `ProvenanceEntry` handles inside snapshot `vm_idx` for stack escapes (`E0506`).
    fn verifySnapshotProvenanceNonStack(
        self: *MirVm,
        vm_idx: u32,
        visited: *std.AutoHashMapUnmanaged(u32, void),
    ) VmEvalError!void {
        if (visited.contains(vm_idx)) return;
        visited.put(self.allocator, vm_idx, {}) catch return error.OutOfMemory;
        const alloc_rec = &self.allocations.items[vm_idx];
        for (alloc_rec.provenance.items) |entry| {
            try self.checkPointerTargetNonStack(entry.alloc_id);
            if (entry.alloc_id.domain() == .vm_alloc) {
                const sub_idx = entry.alloc_id.payloadIndex();
                if (sub_idx > 0 and sub_idx < self.allocations.items.len) {
                    try self.verifySnapshotProvenanceNonStack(sub_idx, visited);
                }
            }
        }
    }

    /// Traps with `E0506` if `alloc_id` points to a dead or stack-frame `MirVm` allocation.
    fn checkPointerTargetNonStack(self: *MirVm, alloc_id: ComptimeAllocId) VmEvalError!void {
        if (alloc_id.domain() != .vm_alloc) return;
        const idx = alloc_id.payloadIndex();
        if (idx == 0) return;
        if (idx >= self.allocations.items.len) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "invalid pointer allocation handle escaped `comptime` evaluation",
                "invalid escaping pointer",
                null,
            );
        }
        const rec = &self.allocations.items[idx];
        if (!rec.is_live or rec.is_stack_frame) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "dangling pointer to local stack variable cannot escape `comptime` evaluation",
                "dangling stack pointer escaped here",
                null,
            );
        }
    }

    /// Records a transitive `CompilerDb` `QueryKey` observed during `MirVm` execution (`[CRITICAL-01]`).
    fn recordObservedQueryDep(self: *MirVm, key: query_db.QueryKey) VmEvalError!void {
        if (self.options.compiler_db == null) return;
        self.observed_query_deps.append(self.allocator, key) catch return error.OutOfMemory;
    }

    /// Maps a `CompilerDb` `QueryError` into the corresponding `VmEvalError` (`[MAJOR-05]`).
    fn mapDbQueryError(self: *MirVm, err: query_db.QueryError) VmEvalError {
        return switch (err) {
            error.OutOfMemory => error.OutOfMemory,
            error.Cancelled => error.Cancelled,
            error.DependencyCycle => self.failWithTrap(
                error.EvaluationCycle,
                .e0509_comptime_evaluation_cycle,
                "cyclic compile-time evaluation detected",
                "cycle re-entered here",
                null,
            ),
            error.MissingSourceInput, error.InvalidDefId => error.UnresolvedCallee,
        };
    }

    /// Returns `true` if `alloc_id` can be safely hashed and retained across `MirVm` sessions (`[CRITICAL-01]`).
    fn isMemoSafePtrTarget(self: *const MirVm, alloc_id: ComptimeAllocId, depth: u32) bool {
        if (depth > 32) return false;
        if (alloc_id == .null_ptr) return true;
        return switch (alloc_id.domain()) {
            .vm_alloc, .fn_or_none => false,
            .string_lit => true,
            .rodata_blob => blk: {
                const blob = self.rodata_pool.getBlob(alloc_id.payloadIndex()) orelse break :blk false;
                for (blob.relocs) |reloc| {
                    if (!self.isMemoSafePtrTarget(reloc.target_alloc, depth + 1)) break :blk false;
                }
                break :blk true;
            },
        };
    }

    /// Hashes the canonical cross-session content and relocations of `alloc_id` into `hasher` (`[CRITICAL-01]`).
    fn hashMemoPtrTarget(
        self: *const MirVm,
        hasher: *std.hash.Wyhash,
        alloc_id: ComptimeAllocId,
        depth: u32,
    ) void {
        if (alloc_id == .null_ptr or depth > 32) {
            hasher.update(&[1]u8{0});
            return;
        }
        var buf8: [8]u8 = undefined;
        switch (alloc_id.domain()) {
            .rodata_blob => {
                hasher.update(&[1]u8{1});
                if (self.rodata_pool.getBlob(alloc_id.payloadIndex())) |blob| {
                    hasher.update(&[1]u8{blob.align_log2});
                    std.mem.writeInt(u64, &buf8, blob.bytes.len, .little);
                    hasher.update(&buf8);
                    hasher.update(blob.bytes);
                    std.mem.writeInt(u64, &buf8, blob.relocs.len, .little);
                    hasher.update(&buf8);
                    for (blob.relocs) |reloc| {
                        std.mem.writeInt(u32, buf8[0..4], reloc.byte_offset, .little);
                        hasher.update(buf8[0..4]);
                        self.hashMemoPtrTarget(hasher, reloc.target_alloc, depth + 1);
                    }
                }
            },
            .string_lit => {
                hasher.update(&[1]u8{2});
                const str_bytes = self.interner.get(SymbolId.fromInt(alloc_id.payloadIndex()));
                std.mem.writeInt(u64, &buf8, str_bytes.len, .little);
                hasher.update(&buf8);
                hasher.update(str_bytes);
            },
            .vm_alloc, .fn_or_none => {
                hasher.update(&[1]u8{3});
                std.mem.writeInt(u32, buf8[0..4], alloc_id.asInt(), .little);
                hasher.update(buf8[0..4]);
            },
        }
    }

    /// Resolves the owning `DefId` of `body` (`body.def_id` or its `SymbolRecord.owner_def_id`).
    fn resolveBodyOwnerDef(self: *const MirVm, body: *const MirBody) DefId {
        if (!body.def_id.isNone()) return body.def_id;
        if (!body.symbol_index.isNone() and body.symbol_index.asInt() < self.sym_table.symbols.items.len) {
            const sym = self.sym_table.getSymbol(body.symbol_index).*;
            return if (!sym.def_id.isNone()) sym.def_id else sym.owner_def_id;
        }
        return .NONE;
    }

    /// Deterministically hashes the structural instruction/terminator/constant signature of `body`
    /// when `compiler_db == null` (zero pointer-address dependence across ASLR or heap layouts).
    fn hashBodyStructureForMemo(hasher: *std.hash.Wyhash, body: *const MirBody) void {
        var buf16: [16]u8 = undefined;
        std.mem.writeInt(u32, buf16[0..4], body.def_id.asInt(), .little);
        std.mem.writeInt(u32, buf16[4..8], body.symbol_index.asInt(), .little);
        std.mem.writeInt(u32, buf16[8..12], body.file_id.asInt(), .little);
        std.mem.writeInt(u32, buf16[12..16], body.name.asInt(), .little);
        hasher.update(&buf16);

        std.mem.writeInt(u32, buf16[0..4], body.ret_ty.asInt(), .little);
        std.mem.writeInt(u32, buf16[4..8], body.param_count, .little);
        std.mem.writeInt(u32, buf16[8..12], @intCast(body.insts.len), .little);
        std.mem.writeInt(u32, buf16[12..16], @intCast(body.blocks.items.len), .little);
        hasher.update(&buf16);

        for (0..body.insts.len) |inst_i| {
            const inst = body.insts.get(inst_i);
            buf16[0] = @backingInt(inst.op);
            buf16[1] = @bitCast(inst.flags);
            std.mem.writeInt(u16, buf16[2..4], inst.aux_u16, .little);
            std.mem.writeInt(u32, buf16[4..8], inst.type_id.asInt(), .little);
            std.mem.writeInt(u32, buf16[8..12], inst.operands.lhs, .little);
            std.mem.writeInt(u32, buf16[12..16], inst.operands.rhs, .little);
            hasher.update(&buf16);
        }

        for (body.blocks.items) |bb| {
            const term = bb.terminator;
            buf16[0] = @backingInt(term.kind);
            buf16[1] = term.aux_u8;
            std.mem.writeInt(u16, buf16[2..4], term.edge_len, .little);
            std.mem.writeInt(u32, buf16[4..8], term.cond_or_val, .little);
            std.mem.writeInt(u32, buf16[8..12], term.edge_start, .little);
            std.mem.writeInt(u32, buf16[12..16], bb.inst_len, .little);
            hasher.update(&buf16);
        }

        for (body.consts.items) |konst| {
            switch (konst) {
                .unit_val => hasher.update(&[1]u8{0}),
                .bool_val => |is_true| hasher.update(&[2]u8{ 1, @intFromBool(is_true) }),
                .char_val => |ch_code| {
                    hasher.update(&[1]u8{2});
                    std.mem.writeInt(u32, buf16[0..4], ch_code, .little);
                    hasher.update(buf16[0..4]);
                },
                .int_val => |int_scalar| {
                    hasher.update(&[1]u8{3});
                    std.mem.writeInt(i128, &buf16, int_scalar, .little);
                    hasher.update(&buf16);
                },
                .float_val => |flt_scalar| {
                    hasher.update(&[1]u8{4});
                    std.mem.writeInt(u64, buf16[0..8], @bitCast(flt_scalar), .little);
                    hasher.update(buf16[0..8]);
                },
                .str_val => |sym_id| {
                    hasher.update(&[1]u8{5});
                    std.mem.writeInt(u32, buf16[0..4], sym_id.asInt(), .little);
                    hasher.update(buf16[0..4]);
                },
                .bytes_val => |sym_id| {
                    hasher.update(&[1]u8{6});
                    std.mem.writeInt(u32, buf16[0..4], sym_id.asInt(), .little);
                    hasher.update(buf16[0..4]);
                },
                .raw_blob => |rb| {
                    hasher.update(&[2]u8{ 7, rb.align_log2 });
                    std.mem.writeInt(u32, buf16[0..4], rb.blob_id, .little);
                    std.mem.writeInt(u64, buf16[4..12], rb.byte_len, .little);
                    hasher.update(buf16[0..12]);
                },
            }
        }
    }

    /// Returns `true` if `body` + `arg_slots` is eligible for `Wyhash(0)` pure-call memoization (`[CRITICAL-01]`).
    fn isPureMemoizableCall(
        self: *const MirVm,
        body: *const MirBody,
        arg_slots: []const RegSlot,
        alias_places: []const SymbolicPtr,
    ) bool {
        const owner_def = self.resolveBodyOwnerDef(body);
        if (self.options.compiler_db != null and owner_def.isNone()) return false;
        if (alias_places.len > 0) return false;
        if (body.param_count != arg_slots.len) return false;
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;

        for (0..body.param_count) |param_i| {
            const loc = body.locals.items[1 + param_i];
            if (loc.mode() == .inout_mode or loc.mode() == .set_mode) return false;
            const repr = classifyValueRepr(
                self.pool,
                self.sym_table,
                loc.type_id,
                self.options.target_layout,
            );
            if (repr == .inline_ptr) {
                if (!self.isMemoSafePtrTarget(arg_slots[param_i].sym_ptr.alloc_id, 0)) return false;
            } else if (repr == .by_value_snapshot) {
                const snap_ptr = arg_slots[param_i].sym_ptr;
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    loc.type_id,
                    self.options.target_layout,
                );
                if (lay.byte_size == 0) continue;
                const end_off = std.math.add(u64, snap_ptr.byte_offset, lay.byte_size) catch return false;
                switch (snap_ptr.alloc_id.domain()) {
                    .vm_alloc => {
                        if (snap_ptr.alloc_id == .null_ptr or
                            snap_ptr.alloc_id.payloadIndex() >= self.allocations.items.len)
                        {
                            return false;
                        }
                        const snap_rec = &self.allocations.items[snap_ptr.alloc_id.payloadIndex()];
                        if (!snap_rec.is_live or end_off > snap_rec.bytes.len) return false;
                        for (snap_rec.provenance.items) |prov| {
                            const prov_start: u64 = prov.byte_offset;
                            const prov_end: u64 = prov_start + ptr_width;
                            if (prov_start < end_off and @as(u64, snap_ptr.byte_offset) < prov_end) {
                                if (prov_start < snap_ptr.byte_offset or prov_end > end_off) return false;
                                if (!self.isMemoSafePtrTarget(prov.alloc_id, 0)) return false;
                            }
                        }
                    },
                    .rodata_blob => {
                        const blob = self.rodata_pool.getBlob(snap_ptr.alloc_id.payloadIndex()) orelse return false;
                        if (end_off > blob.bytes.len) return false;
                        for (blob.relocs) |reloc| {
                            const rel_start: u64 = reloc.byte_offset;
                            const rel_end: u64 = rel_start + ptr_width;
                            if (rel_start < end_off and @as(u64, snap_ptr.byte_offset) < rel_end) {
                                if (rel_start < snap_ptr.byte_offset or rel_end > end_off) return false;
                                if (!self.isMemoSafePtrTarget(reloc.target_alloc, 0)) return false;
                            }
                        }
                    },
                    .string_lit => {
                        const str_bytes = self.interner.get(SymbolId.fromInt(snap_ptr.alloc_id.payloadIndex()));
                        if (end_off > str_bytes.len) return false;
                    },
                    .fn_or_none => return false,
                }
            }
        }
        return true;
    }

    /// Computes a deterministic `Wyhash(0)` digest over `(callee_key, target_layout, arg_slots)` (`[CRITICAL-01]`).
    fn computePureCallHash(
        self: *const MirVm,
        callee_key: u64,
        body: *const MirBody,
        arg_slots: []const RegSlot,
    ) u64 {
        var hasher = std.hash.Wyhash.init(0);
        var buf8: [8]u8 = undefined;
        std.mem.writeInt(u64, &buf8, callee_key, .little);
        hasher.update(&buf8);
        hasher.update(&[5]u8{
            self.options.target_layout.ptr_byte_size,
            self.options.target_layout.ptr_align_log2,
            self.options.target_layout.cache_line_align_log2,
            self.options.target_layout.simd_align_log2,
            @intFromBool(self.options.compiler_db != null),
        });
        if (self.options.compiler_db == null) {
            hashBodyStructureForMemo(&hasher, body);
        }
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;

        for (0..arg_slots.len) |arg_i| {
            const param_ty = body.locals.items[1 + arg_i].type_id;
            std.mem.writeInt(u32, buf8[0..4], param_ty.asInt(), .little);
            hasher.update(buf8[0..4]);
            const repr = classifyValueRepr(
                self.pool,
                self.sym_table,
                param_ty,
                self.options.target_layout,
            );
            switch (repr) {
                .inline_scalar => {
                    hasher.update(&[1]u8{0});
                    std.mem.writeInt(u64, &buf8, arg_slots[arg_i].scalar_u64, .little);
                    hasher.update(&buf8);
                },
                .inline_ptr => {
                    hasher.update(&[1]u8{1});
                    std.mem.writeInt(u32, buf8[0..4], arg_slots[arg_i].sym_ptr.byte_offset, .little);
                    hasher.update(buf8[0..4]);
                    self.hashMemoPtrTarget(&hasher, arg_slots[arg_i].sym_ptr.alloc_id, 0);
                },
                .by_value_snapshot => {
                    const sym_ptr = arg_slots[arg_i].sym_ptr;
                    const lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        param_ty,
                        self.options.target_layout,
                    );
                    const byte_off: usize = sym_ptr.byte_offset;
                    const byte_len: usize = @intCast(lay.byte_size);
                    hasher.update(&[2]u8{ 2, @backingInt(sym_ptr.alloc_id.domain()) });
                    std.mem.writeInt(u32, buf8[0..4], sym_ptr.byte_offset, .little);
                    hasher.update(buf8[0..4]);
                    std.mem.writeInt(u64, &buf8, lay.byte_size, .little);
                    hasher.update(&buf8);
                    if (byte_len == 0) continue;

                    switch (sym_ptr.alloc_id.domain()) {
                        .vm_alloc => {
                            const snap_rec = &self.allocations.items[sym_ptr.alloc_id.payloadIndex()];
                            hasher.update(snap_rec.bytes[byte_off .. byte_off + byte_len]);
                            var init_chunk: [64]u8 = undefined;
                            var rem_idx: usize = 0;
                            while (rem_idx < byte_len) {
                                const take = @min(byte_len - rem_idx, init_chunk.len);
                                for (0..take) |i| {
                                    init_chunk[i] = @intFromBool(isByteInitialized(snap_rec, byte_off + rem_idx + i));
                                }
                                hasher.update(init_chunk[0..take]);
                                rem_idx += take;
                            }
                            const end_off: u64 = @as(u64, sym_ptr.byte_offset) + lay.byte_size;
                            for (snap_rec.provenance.items) |prov| {
                                if (prov.byte_offset >= sym_ptr.byte_offset and
                                    @as(u64, prov.byte_offset) + ptr_width <= end_off)
                                {
                                    std.mem.writeInt(u32, buf8[0..4], prov.byte_offset - sym_ptr.byte_offset, .little);
                                    hasher.update(buf8[0..4]);
                                    self.hashMemoPtrTarget(&hasher, prov.alloc_id, 0);
                                }
                            }
                        },
                        .rodata_blob => {
                            const blob = self.rodata_pool.getBlob(sym_ptr.alloc_id.payloadIndex()).?;
                            hasher.update(blob.bytes[byte_off .. byte_off + byte_len]);
                            const end_off: u64 = @as(u64, sym_ptr.byte_offset) + lay.byte_size;
                            for (blob.relocs) |reloc| {
                                if (reloc.byte_offset >= sym_ptr.byte_offset and
                                    @as(u64, reloc.byte_offset) + ptr_width <= end_off)
                                {
                                    std.mem.writeInt(u32, buf8[0..4], reloc.byte_offset - sym_ptr.byte_offset, .little);
                                    hasher.update(buf8[0..4]);
                                    self.hashMemoPtrTarget(&hasher, reloc.target_alloc, 0);
                                }
                            }
                        },
                        .string_lit => {
                            const str_bytes = self.interner.get(SymbolId.fromInt(sym_ptr.alloc_id.payloadIndex()));
                            hasher.update(str_bytes[byte_off .. byte_off + byte_len]);
                        },
                        .fn_or_none => {},
                    }
                },
            }
        }
        return hasher.final();
    }

    /// Materializes a cached `MemoCachedResult` into an active `RegSlot` in `self`.
    fn materializeMemoResult(self: *MirVm, cached: MemoCachedResult) VmEvalError!RegSlot {
        if (cached.repr != .by_value_snapshot) return cached.inline_slot;
        const alloc_id = try self.allocMemory(
            cached.snapshot_bytes.len,
            cached.align_log2,
            false,
            false,
            false,
            0,
            self.active_inst_span,
        );
        const rec = &self.allocations.items[alloc_id.payloadIndex()];
        @memcpy(rec.bytes, cached.snapshot_bytes);
        @memcpy(rec.init_mask, cached.snapshot_init);
        rec.provenance.appendSlice(self.allocator, cached.snapshot_prov) catch return error.OutOfMemory;
        return .{ .sym_ptr = .{ .alloc_id = alloc_id, .byte_offset = cached.snapshot_offset } };
    }

    /// Deduplicates observed `QueryKey`s in `observed_slice` and snapshots their `MemoHeader` fingerprints.
    fn serializeObservedQueryDeps(
        self: *const MirVm,
        cache_alloc: std.mem.Allocator,
        observed_slice: []const query_db.QueryKey,
    ) !?[]MemoQueryDep {
        const db = self.options.compiler_db orelse return &.{};
        if (observed_slice.len == 0) return &.{};

        var deduped: std.ArrayListUnmanaged(MemoQueryDep) = .empty;
        errdefer deduped.deinit(cache_alloc);
        for (observed_slice) |dep_key| {
            var is_seen = false;
            for (deduped.items) |existing| {
                if (existing.key.asU64() == dep_key.asU64()) {
                    is_seen = true;
                    break;
                }
            }
            if (is_seen) continue;
            const dep_hdr = db.memos.get(dep_key.asU64()) orelse return null;
            try deduped.append(cache_alloc, .{
                .key = dep_key,
                .output_fingerprint = dep_hdr.output_fingerprint,
            });
        }
        return try deduped.toOwnedSlice(cache_alloc);
    }

    /// Attempts to serialize a pure call's return `RegSlot` for `PureCallMemoCache` (returns `null` if it
    /// references session-local `.vm_alloc` or `.fn_or_none` handles, `[CRITICAL-01]`).
    fn trySerializeMemoResult(
        self: *const MirVm,
        cache_alloc: std.mem.Allocator,
        call_hash: u64,
        callee_key: u64,
        ret_ty: TypeId,
        repr: VmValueRepr,
        ret_slot: RegSlot,
        observed_deps: []const query_db.QueryKey,
    ) !?MemoCachedResult {
        switch (repr) {
            .inline_scalar => {
                const deps_copy = (try self.serializeObservedQueryDeps(cache_alloc, observed_deps)) orelse return null;
                return MemoCachedResult{
                    .call_hash = call_hash,
                    .callee_id = callee_key,
                    .ret_ty = ret_ty,
                    .repr = .inline_scalar,
                    .inline_slot = ret_slot,
                    .query_deps = deps_copy,
                    .accounted_bytes = @sizeOf(MemoCachedResult) + deps_copy.len * @sizeOf(MemoQueryDep),
                };
            },
            .inline_ptr => {
                if (!self.isMemoSafePtrTarget(ret_slot.sym_ptr.alloc_id, 0)) return null;
                const deps_copy = (try self.serializeObservedQueryDeps(cache_alloc, observed_deps)) orelse return null;
                return MemoCachedResult{
                    .call_hash = call_hash,
                    .callee_id = callee_key,
                    .ret_ty = ret_ty,
                    .repr = .inline_ptr,
                    .inline_slot = ret_slot,
                    .query_deps = deps_copy,
                    .accounted_bytes = @sizeOf(MemoCachedResult) + deps_copy.len * @sizeOf(MemoQueryDep),
                };
            },
            .by_value_snapshot => {
                const aid = ret_slot.sym_ptr.alloc_id;
                if (aid.domain() != .vm_alloc or aid == .null_ptr or aid.payloadIndex() >= self.allocations.items.len) {
                    return null;
                }
                const rec = &self.allocations.items[aid.payloadIndex()];
                for (rec.provenance.items) |prov| {
                    if (!self.isMemoSafePtrTarget(prov.alloc_id, 0)) return null;
                }
                const deps_copy = (try self.serializeObservedQueryDeps(cache_alloc, observed_deps)) orelse return null;
                errdefer if (deps_copy.len > 0) cache_alloc.free(deps_copy);

                const bytes_copy: []u8 = if (rec.bytes.len > 0)
                    try cache_alloc.dupe(u8, rec.bytes)
                else
                    &.{};
                errdefer if (bytes_copy.len > 0) cache_alloc.free(bytes_copy);
                const init_copy: []u64 = if (rec.init_mask.len > 0)
                    try cache_alloc.dupe(u64, rec.init_mask)
                else
                    &.{};
                errdefer if (init_copy.len > 0) cache_alloc.free(init_copy);
                const prov_copy: []ProvenanceEntry = if (rec.provenance.items.len > 0)
                    try cache_alloc.dupe(ProvenanceEntry, rec.provenance.items)
                else
                    &.{};

                const total_bytes = @sizeOf(MemoCachedResult) +
                    bytes_copy.len +
                    init_copy.len * @sizeOf(u64) +
                    prov_copy.len * @sizeOf(ProvenanceEntry) +
                    deps_copy.len * @sizeOf(MemoQueryDep);
                return MemoCachedResult{
                    .call_hash = call_hash,
                    .callee_id = callee_key,
                    .ret_ty = ret_ty,
                    .repr = .by_value_snapshot,
                    .snapshot_bytes = bytes_copy,
                    .snapshot_init = init_copy,
                    .snapshot_prov = prov_copy,
                    .query_deps = deps_copy,
                    .snapshot_offset = ret_slot.sym_ptr.byte_offset,
                    .align_log2 = rec.align_log2,
                    .accounted_bytes = total_bytes,
                };
            },
        }
    }

    /// Rewinds `self.arena`, `self.allocations`, and `self.bytes_used` back to a pre-call checkpoint.
    fn restoreVmArenaCheckpoint(
        self: *MirVm,
        arena_cp: mem_foundation.Checkpoint,
        alloc_count_cp: usize,
        bytes_used_cp: u64,
    ) void {
        var idx = alloc_count_cp;
        while (idx < self.allocations.items.len) : (idx += 1) {
            self.allocations.items[idx].provenance.deinit(self.allocator);
        }
        self.allocations.items.len = alloc_count_cp;
        self.arena.restore(arena_cp);
        self.bytes_used = bytes_used_cp;
    }

    // ----------- Place & Projection Address Evaluation ------------

    /// Outcome of evaluating a `MirPlace` inside `MirVm`.
    const PlaceEvalOutcome = union(enum) {
        /// Resolved concrete `SymbolicPtr` and pointee `TypeId`.
        memory_ptr: struct {
            /// Concrete symbolic address within `MirVm` memory.
            ptr: SymbolicPtr,
            /// Pointee `TypeId` stored at `ptr`.
            pointee_ty: TypeId,
            /// Whether `ptr` projects through a `@packed` struct and allows 1-byte alignment.
            is_unaligned: bool = false,
        },
        /// Compile-time constant `usize` length from `.slice_len` on fixed `[T; N]` / `#soa [T; N]`.
        constant_usize: u64,
    };

    /// Temporary aligned bounce buffer record for an `inout`/`set` `@packed` field argument.
    const UnalignedBounceWriteback = struct {
        /// Unaligned caller place address inside the `@packed` aggregate.
        orig_ptr: SymbolicPtr,
        /// Aligned temporary bounce allocation passed to the callee.
        bounce_ptr: SymbolicPtr,
        /// Byte width copied back after a non-trapping call completes.
        byte_size: u64,
    };

    /// Allocates a fresh uninitialized stack `ComptimeAllocId` for `local_idx` inside `call_stack[frame_idx]`
    /// after a scope/loop-iteration `ghost_storage_deinit` invalidated the prior slot (`[MAJOR-06]`).
    fn ensureLocalStackAllocation(self: *MirVm, frame_idx: usize, local_idx: usize) VmEvalError!void {
        const body = self.call_stack.items[frame_idx].body;
        if (local_idx <= body.param_count or local_idx >= self.call_stack.items[frame_idx].owned_stack_allocs.len) {
            return;
        }
        if (self.call_stack.items[frame_idx].owned_stack_allocs[local_idx] != .none) return;

        const loc_decl = body.locals.items[local_idx];
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            loc_decl.type_id,
            self.options.target_layout,
        );
        const unwrapped_loc = self.pool.unwrapUnderlyingType(loc_decl.type_id);
        const loc_node = self.pool.getNode(unwrapped_loc);
        const soa_cap: u32 = if (loc_node.tag == .soa_array_ty)
            (loc_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG)
        else
            0;
        const loc_span = self.resolveTokenSpan(body.file_id, loc_decl.origin_token);
        const fresh_id = try self.allocMemory(
            lay.byte_size,
            lay.align_log2,
            true,
            true,
            false,
            soa_cap,
            loc_span,
        );
        self.call_stack.items[frame_idx].local_ptrs[local_idx] = .{ .alloc_id = fresh_id, .byte_offset = 0 };
        self.call_stack.items[frame_idx].owned_stack_allocs[local_idx] = fresh_id;
    }

    /// Evaluates `place_id` inside `call_stack[frame_idx]`, enforcing `E0504` spatial bounds (`[CRITICAL-04]`).
    fn evalPlace(
        self: *MirVm,
        frame_idx: usize,
        place_id: PlaceId,
    ) VmEvalError!PlaceEvalOutcome {
        const body = self.call_stack.items[frame_idx].body;
        const place = body.places.items[place_id.asInt()];
        if (place.base > body.param_count and
            place.base < self.call_stack.items[frame_idx].owned_stack_allocs.len and
            self.call_stack.items[frame_idx].owned_stack_allocs[place.base] == .none)
        {
            try self.ensureLocalStackAllocation(frame_idx, place.base);
        }
        const frame = &self.call_stack.items[frame_idx];
        var cur_ptr = frame.local_ptrs[place.base];
        var cur_ty = self.pool.unwrapUnderlyingType(body.locals.items[place.base].type_id);
        var is_unaligned = false;
        var active_downcast: ?u32 = null;
        var soa_col_view: ?struct {
            data_ptr: SymbolicPtr,
            elem_len: u64,
            field_ty: TypeId,
        } = null;

        for (body.getPlaceProjections(place_id)) |proj| {
            if (soa_col_view) |col_info| {
                soa_col_view = null;
                if (proj.kind == .index) {
                    const idx_slot = frame.regs[proj.payload];
                    const idx_ty = body.getInst(MirValueId.fromInt(proj.payload)).type_id;
                    const idx_u128 = try self.readIntBitsFromSlot(idx_slot, idx_ty);
                    const idx_info = resolveIntInfo(self.pool, idx_ty, self.options.target_layout);
                    if (idx_info != null and idx_info.?.is_signed and signExtendToI128(idx_u128, idx_info.?.bits) < 0) {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "negative index on `#soa` column slice during `comptime` evaluation",
                            "negative `#soa` index here",
                            null,
                        );
                    }
                    if (idx_u128 >= col_info.elem_len) {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "`#soa` column index out of bounds during `comptime` evaluation",
                            "`#soa` index exceeds length",
                            null,
                        );
                    }
                    const elem_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        col_info.field_ty,
                        self.options.target_layout,
                    );
                    const byte_delta = try self.mulOffsetChecked(idx_u128, elem_lay.byte_size);
                    cur_ptr = try self.advanceSymbolicPtr(col_info.data_ptr, byte_delta);
                    cur_ty = self.pool.unwrapUnderlyingType(col_info.field_ty);
                    continue;
                } else if (proj.kind == .slice_len) {
                    return .{ .constant_usize = col_info.elem_len };
                }
            }

            const ty_node = self.pool.getNode(cur_ty);
            switch (proj.kind) {
                .deref => {
                    active_downcast = null;
                    cur_ptr = try self.readPointerAt(
                        cur_ptr,
                        if (is_unaligned) 0 else self.options.target_layout.ptr_align_log2,
                    );
                    cur_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                    is_unaligned = false;
                },
                .downcast => {
                    active_downcast = proj.payload;
                },
                .field => {
                    if (active_downcast) |tag_ord| {
                        active_downcast = null;
                        const sum_info = computeSumTypeTagAndPayloadLayout(
                            self.pool,
                            self.sym_table,
                            cur_ty,
                            self.options.target_layout,
                        );
                        const var_pay_ty = self.pool.unwrapUnderlyingType(
                            resolveVariantPayloadType(self.pool, self.sym_table, cur_ty, tag_ord),
                        );
                        cur_ptr = try self.advanceSymbolicPtr(cur_ptr, sum_info.payload_offset);
                        if (proj.payload > 0) {
                            const sub_field = computeCompositeFieldOffsetAndType(
                                self.pool,
                                self.sym_table,
                                var_pay_ty,
                                proj.payload,
                                self.options.target_layout,
                            ) orelse return self.failWithTrap(
                                error.OutOfBounds,
                                .e0504_comptime_out_of_bounds,
                                "invalid variant tuple field projection at `comptime`",
                                "invalid variant field projection",
                                null,
                            );
                            if (isPackedStructType(self.pool, self.sym_table, var_pay_ty)) {
                                is_unaligned = true;
                            }
                            cur_ptr = try self.advanceSymbolicPtr(cur_ptr, sub_field.byte_offset);
                            cur_ty = self.pool.unwrapUnderlyingType(sub_field.field_ty);
                        } else {
                            cur_ty = var_pay_ty;
                        }
                    } else {
                        if (isPackedStructType(self.pool, self.sym_table, cur_ty)) {
                            is_unaligned = true;
                        }
                        const field_info = computeCompositeFieldOffsetAndType(
                            self.pool,
                            self.sym_table,
                            cur_ty,
                            proj.payload,
                            self.options.target_layout,
                        ) orelse return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "invalid struct or tuple field projection at `comptime`",
                            "invalid field projection",
                            null,
                        );
                        cur_ptr = try self.advanceSymbolicPtr(cur_ptr, field_info.byte_offset);
                        cur_ty = self.pool.unwrapUnderlyingType(field_info.field_ty);
                    }
                },
                .index => {
                    active_downcast = null;
                    const idx_slot = frame.regs[proj.payload];
                    const idx_ty = body.getInst(MirValueId.fromInt(proj.payload)).type_id;
                    const idx_u128 = try self.readIntBitsFromSlot(idx_slot, idx_ty);
                    const idx_info = resolveIntInfo(self.pool, idx_ty, self.options.target_layout);
                    if (idx_info != null and idx_info.?.is_signed and signExtendToI128(idx_u128, idx_info.?.bits) < 0) {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "negative array or slice index during `comptime` evaluation",
                            "negative index here",
                            null,
                        );
                    }
                    const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                    const elem_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        elem_ty,
                        self.options.target_layout,
                    );
                    if (ty_node.tag == .array_ty) {
                        const arr_len: u64 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        if (idx_u128 >= arr_len) {
                            return self.failWithTrap(
                                error.OutOfBounds,
                                .e0504_comptime_out_of_bounds,
                                "array index out of bounds during `comptime` evaluation",
                                "index exceeds fixed array length",
                                null,
                            );
                        }
                        const delta = try self.mulOffsetChecked(idx_u128, elem_lay.byte_size);
                        cur_ptr = try self.advanceSymbolicPtr(cur_ptr, delta);
                        cur_ty = elem_ty;
                    } else if (ty_node.tag == .slice_ty) {
                        const fat = try self.readFatSliceParts(cur_ptr);
                        if (idx_u128 >= fat.elem_len) {
                            return self.failWithTrap(
                                error.OutOfBounds,
                                .e0504_comptime_out_of_bounds,
                                "slice index out of bounds during `comptime` evaluation",
                                "index exceeds slice length",
                                null,
                            );
                        }
                        const delta = try self.mulOffsetChecked(idx_u128, elem_lay.byte_size);
                        cur_ptr = try self.advanceSymbolicPtr(fat.data_ptr, delta);
                        cur_ty = elem_ty;
                        is_unaligned = false;
                    } else {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "unsupported indexed container during `comptime` evaluation",
                            "invalid index base",
                            null,
                        );
                    }
                },
                .soa_elem => {
                    active_downcast = null;
                    const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                    if (ty_node.tag == .soa_array_ty) {
                        const cap: u32 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        const col = computeSoaColumnOffsetAndType(
                            self.pool,
                            self.sym_table,
                            elem_struct_ty,
                            proj.payload,
                            cap,
                            self.options.target_layout,
                        ) orelse return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "invalid `#soa` column projection at `comptime`",
                            "invalid `#soa` column",
                            null,
                        );
                        soa_col_view = .{
                            .data_ptr = try self.advanceSymbolicPtr(cur_ptr, col.column_byte_offset),
                            .elem_len = cap,
                            .field_ty = col.field_ty,
                        };
                    } else if (ty_node.tag == .soa_slice_ty) {
                        const fat = try self.readFatSliceParts(cur_ptr);
                        var backing_cap: u32 = @truncate(fat.elem_len);
                        if (fat.data_ptr.alloc_id.domain() == .vm_alloc) {
                            const backing_rec = &self.allocations.items[fat.data_ptr.alloc_id.payloadIndex()];
                            if (backing_rec.soa_elem_capacity > 0) {
                                backing_cap = backing_rec.soa_elem_capacity;
                            }
                        }
                        const col = computeSoaColumnOffsetAndType(
                            self.pool,
                            self.sym_table,
                            elem_struct_ty,
                            proj.payload,
                            backing_cap,
                            self.options.target_layout,
                        ) orelse return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "invalid `#soa` slice column projection at `comptime`",
                            "invalid `#soa` slice column",
                            null,
                        );
                        soa_col_view = .{
                            .data_ptr = try self.advanceSymbolicPtr(fat.data_ptr, col.column_byte_offset),
                            .elem_len = fat.elem_len,
                            .field_ty = col.field_ty,
                        };
                    }
                },
                .slice_len => {
                    active_downcast = null;
                    if (ty_node.tag == .array_ty or ty_node.tag == .soa_array_ty) {
                        return .{ .constant_usize = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG };
                    }
                    cur_ptr = try self.advanceSymbolicPtr(cur_ptr, self.options.target_layout.ptr_byte_size);
                    cur_ty = .usize_ty;
                },
            }
        }
        return .{ .memory_ptr = .{ .ptr = cur_ptr, .pointee_ty = cur_ty, .is_unaligned = is_unaligned } };
    }

    // -------- Instruction, Operator & Terminator Dispatch ---------

    /// Increments `steps_executed` and emits `E0501` if `options.step_budget` is exceeded.
    inline fn tickStepBudget(self: *MirVm) VmEvalError!void {
        self.steps_executed += 1;
        if (self.steps_executed > self.options.step_budget) {
            return self.failWithTrap(
                error.StepLimitExceeded,
                .e0501_comptime_step_limit_exceeded,
                "`comptime` evaluation exceeded step budget",
                "step limit exceeded here",
                "increase the step budget via `--comptime-limit=<steps>`",
            );
        }
    }

    /// Attempts to resolve `(def_id, sym_idx)` without trapping when the body is not registered (`[MAJOR-05]`).
    fn tryResolveOrLoadCallable(
        self: *MirVm,
        def_id: DefId,
        sym_idx: SymbolIndex,
    ) VmEvalError!?u32 {
        const resolved_def = if (!def_id.isNone())
            def_id
        else if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) blk: {
            const sym = self.sym_table.getSymbol(sym_idx).*;
            break :blk if (!sym.def_id.isNone()) sym.def_id else sym.owner_def_id;
        } else DefId.NONE;

        if (!sym_idx.isNone()) {
            if (self.sym_to_callable.get(sym_idx.asInt())) |found_idx| {
                if (!resolved_def.isNone() and self.db_backed_defs.contains(resolved_def.asInt())) {
                    try self.recordObservedQueryDep(query_db.QueryKey.forDef(.build_def_mir, resolved_def));
                }
                return found_idx;
            }
            if (sym_idx.asInt() < self.sym_table.symbols.items.len) {
                const sym = self.sym_table.getSymbol(sym_idx).*;
                if (sym.flags.is_extern) {
                    const ext_id = self.registerExternFn(sym.def_id, sym_idx) catch return error.OutOfMemory;
                    return ext_id.payloadIndex();
                }
                if (!sym.def_id.isNone()) {
                    if (self.def_to_callable.get(sym.def_id.asInt())) |found_by_sym_def| {
                        if (self.db_backed_defs.contains(sym.def_id.asInt())) {
                            try self.recordObservedQueryDep(query_db.QueryKey.forDef(.build_def_mir, sym.def_id));
                        }
                        return found_by_sym_def;
                    }
                }
            }
        }
        if (!def_id.isNone()) {
            if (self.def_to_callable.get(def_id.asInt())) |found_idx| {
                if (self.db_backed_defs.contains(def_id.asInt())) {
                    try self.recordObservedQueryDep(query_db.QueryKey.forDef(.build_def_mir, def_id));
                }
                return found_idx;
            }
        }

        if (!resolved_def.isNone()) {
            if (self.options.compiler_db) |db| {
                const bodies_slice = db.getComptimeElaboratedMirBodies(resolved_def) catch |err| switch (err) {
                    error.MissingSourceInput, error.InvalidDefId => return null,
                    else => return self.mapDbQueryError(err),
                };
                if (bodies_slice.len > 0) {
                    self.db_backed_defs.put(self.allocator, resolved_def.asInt(), {}) catch
                        return error.OutOfMemory;
                    try self.recordObservedQueryDep(query_db.QueryKey.forDef(.build_def_mir, resolved_def));
                    for (bodies_slice) |*body_item| {
                        const item_sym = if (!body_item.symbol_index.isNone())
                            body_item.symbol_index
                        else
                            db.symbol_table.def_to_symbol.get(body_item.def_id.asInt()) orelse .none;
                        _ = self.registerBody(body_item, item_sym) catch return error.OutOfMemory;
                    }
                    if (!sym_idx.isNone()) {
                        if (self.sym_to_callable.get(sym_idx.asInt())) |loaded_sym_idx| {
                            return loaded_sym_idx;
                        }
                    }
                    if (self.def_to_callable.get(resolved_def.asInt())) |loaded_def_idx| {
                        return loaded_def_idx;
                    }
                }
            }
        }
        return null;
    }

    /// Resolves `(def_id, sym_idx)` to a registered callable index, trapping with `E0503` if unavailable.
    fn resolveOrLoadCallable(
        self: *MirVm,
        def_id: DefId,
        sym_idx: SymbolIndex,
    ) VmEvalError!u32 {
        if (try self.tryResolveOrLoadCallable(def_id, sym_idx)) |found_idx| {
            return found_idx;
        }
        return self.failWithTrap(
            error.UnresolvedCallee,
            .e0503_forbidden_comptime_operation,
            "target function body is unavailable for `comptime` execution",
            "cannot resolve `comptime` callee body here",
            null,
        );
    }

    /// Executes `body` inside a new activation record with `Wyhash(0)` memoization and stack-frame invalidation.
    fn invokeBodyInternal(
        self: *MirVm,
        body: *const MirBody,
        arg_slots: []const RegSlot,
        alias_places: []const SymbolicPtr,
        call_site_span: Span,
    ) VmEvalError!RegSlot {
        if (self.call_stack.items.len >= self.options.max_call_depth) {
            return self.failWithTrap(
                error.ResourceLimitExceeded,
                .e0508_comptime_resource_limit_exceeded,
                "`comptime` call-stack depth exceeded maximum recursion limit (`512`)",
                "call-stack overflow here",
                null,
            );
        }

        const ret_repr = classifyValueRepr(self.pool, self.sym_table, body.ret_ty, self.options.target_layout);
        const is_pure_call = self.isPureMemoizableCall(body, arg_slots, alias_places);
        const body_owner_def = self.resolveBodyOwnerDef(body);
        var callee_key: u64 = (@as(u64, body_owner_def.asInt()) << 32) | @as(u64, body.name.asInt());
        var call_hash: u64 = 0;

        if (is_pure_call) {
            if (self.options.compiler_db == null) {
                var body_hasher = std.hash.Wyhash.init(0);
                hashBodyStructureForMemo(&body_hasher, body);
                callee_key = body_hasher.final();
            }
            call_hash = self.computePureCallHash(callee_key, body, arg_slots);
            if (self.memo_cache) |cache| {
                if (cache.lookup(call_hash, callee_key, body.ret_ty)) |cached| {
                    var is_valid_hit = true;
                    if (self.options.compiler_db) |db| {
                        for (cached.query_deps) |dep_item| {
                            const fetched_hdr = db.fetchQuery(dep_item.key) catch |err| {
                                return self.mapDbQueryError(err);
                            };
                            try self.recordObservedQueryDep(dep_item.key);
                            if (!query_db.Fingerprint128.eql(fetched_hdr.output_fingerprint, dep_item.output_fingerprint)) {
                                is_valid_hit = false;
                                break;
                            }
                        }
                    } else if (cached.query_deps.len > 0) {
                        is_valid_hit = false;
                    }
                    if (is_valid_hit) {
                        cache.hit_count += 1;
                        return self.materializeMemoResult(cached);
                    }
                }
            }
        }

        const arena_cp = self.arena.checkpoint();
        const alloc_cp = self.allocations.items.len;
        const bytes_cp = self.bytes_used;
        const dep_checkpoint = self.observed_query_deps.items.len;
        const drop_trace_cp = self.drop_trace.items.len;
        const heap_cp = self.live_heap_allocs;

        if (is_pure_call and !body_owner_def.isNone() and self.db_backed_defs.contains(body_owner_def.asInt())) {
            try self.recordObservedQueryDep(query_db.QueryKey.forDef(.build_def_mir, body_owner_def));
        }

        const raw_ret_slot = try self.executeStackFrame(body, arg_slots, alias_places, call_site_span);

        var has_heap_or_drop_effect = self.drop_trace.items.len != drop_trace_cp or
            self.live_heap_allocs != heap_cp;
        if (!has_heap_or_drop_effect) {
            for (self.allocations.items[alloc_cp..]) |alloc_item| {
                if (alloc_item.is_heap_alloc) {
                    has_heap_or_drop_effect = true;
                    break;
                }
            }
        }

        if (is_pure_call and !has_heap_or_drop_effect) {
            var maybe_memo: ?MemoCachedResult = null;
            errdefer if (maybe_memo) |leaked_memo| {
                self.memo_cache.?.freeEntryBuffers(leaked_memo);
            };
            if (self.memo_cache) |cache| {
                maybe_memo = self.trySerializeMemoResult(
                    cache.allocator,
                    call_hash,
                    callee_key,
                    body.ret_ty,
                    ret_repr,
                    raw_ret_slot,
                    self.observed_query_deps.items[dep_checkpoint..],
                ) catch return error.OutOfMemory;
            }

            // Rewind transient `BumpArena` allocations if return value has no live `vm_alloc` provenance:
            var is_rewindable = false;
            switch (ret_repr) {
                .inline_scalar => is_rewindable = true,
                .inline_ptr => {
                    is_rewindable = raw_ret_slot.sym_ptr.alloc_id.domain() != .vm_alloc or
                        raw_ret_slot.sym_ptr.alloc_id == .null_ptr;
                },
                .by_value_snapshot => {
                    const aid = raw_ret_slot.sym_ptr.alloc_id;
                    if (aid.domain() == .vm_alloc and aid != .null_ptr and aid.payloadIndex() < self.allocations.items.len) {
                        var has_vm_prov = false;
                        for (self.allocations.items[aid.payloadIndex()].provenance.items) |prov| {
                            if (prov.alloc_id.domain() == .vm_alloc and prov.alloc_id != .null_ptr) {
                                has_vm_prov = true;
                                break;
                            }
                        }
                        is_rewindable = !has_vm_prov;
                    } else if (aid.domain() == .rodata_blob or aid.domain() == .string_lit) {
                        is_rewindable = true;
                    }
                },
            }

            var final_slot = raw_ret_slot;
            if (is_rewindable) {
                if (ret_repr == .by_value_snapshot and raw_ret_slot.sym_ptr.alloc_id.domain() == .vm_alloc) {
                    const snap_idx = raw_ret_slot.sym_ptr.alloc_id.payloadIndex();
                    const snap_rec = &self.allocations.items[snap_idx];
                    const saved_align = snap_rec.align_log2;
                    const saved_offset = raw_ret_slot.sym_ptr.byte_offset;
                    const tmp_bytes = self.allocator.dupe(u8, snap_rec.bytes) catch return error.OutOfMemory;
                    defer self.allocator.free(tmp_bytes);
                    const tmp_init = self.allocator.dupe(u64, snap_rec.init_mask) catch return error.OutOfMemory;
                    defer self.allocator.free(tmp_init);
                    const tmp_prov = self.allocator.dupe(
                        ProvenanceEntry,
                        snap_rec.provenance.items,
                    ) catch return error.OutOfMemory;
                    defer self.allocator.free(tmp_prov);

                    self.restoreVmArenaCheckpoint(arena_cp, alloc_cp, bytes_cp);

                    const fresh_id = try self.allocMemory(
                        tmp_bytes.len,
                        saved_align,
                        false,
                        false,
                        false,
                        0,
                        self.active_inst_span,
                    );
                    const fresh_rec = &self.allocations.items[fresh_id.payloadIndex()];
                    @memcpy(fresh_rec.bytes, tmp_bytes);
                    @memcpy(fresh_rec.init_mask, tmp_init);
                    fresh_rec.provenance.appendSlice(self.allocator, tmp_prov) catch return error.OutOfMemory;
                    final_slot = .{ .sym_ptr = .{ .alloc_id = fresh_id, .byte_offset = saved_offset } };
                } else {
                    self.restoreVmArenaCheckpoint(arena_cp, alloc_cp, bytes_cp);
                }
            }

            if (maybe_memo) |memo_item| {
                maybe_memo = null;
                self.memo_cache.?.insert(memo_item) catch return error.OutOfMemory;
            }
            return final_slot;
        }

        return raw_ret_slot;
    }

    /// Allocates frame registers and local stack slots, runs the `MirBody` basic-block loop, and
    /// marks all frame-owned stack allocations dead (`is_live = false`) on exit (`E0506` UAF).
    fn executeStackFrame(
        self: *MirVm,
        body: *const MirBody,
        arg_slots: []const RegSlot,
        alias_places: []const SymbolicPtr,
        call_site_span: Span,
    ) VmEvalError!RegSlot {
        const reg_count = body.insts.len;
        const local_count = body.locals.items.len;

        const regs: []RegSlot = if (reg_count > 0)
            self.allocator.alloc(RegSlot, reg_count) catch return error.OutOfMemory
        else
            &.{};
        if (regs.len > 0) @memset(regs, .{ .scalar_u64 = 0 });

        const local_ptrs: []SymbolicPtr = if (local_count > 0)
            self.allocator.alloc(SymbolicPtr, local_count) catch {
                if (regs.len > 0) self.allocator.free(regs);
                return error.OutOfMemory;
            }
        else
            &.{};
        if (local_ptrs.len > 0) @memset(local_ptrs, SymbolicPtr.NULL);

        const owned_stack_allocs: []ComptimeAllocId = if (local_count > 0)
            self.allocator.alloc(ComptimeAllocId, local_count) catch {
                if (local_ptrs.len > 0) self.allocator.free(local_ptrs);
                if (regs.len > 0) self.allocator.free(regs);
                return error.OutOfMemory;
            }
        else
            &.{};
        if (owned_stack_allocs.len > 0) @memset(owned_stack_allocs, .none);

        // Identify which local slots are referenced by at least one `MirPlace`:
        const is_local_in_place: []bool = if (local_count > 0)
            self.allocator.alloc(bool, local_count) catch {
                if (owned_stack_allocs.len > 0) self.allocator.free(owned_stack_allocs);
                if (local_ptrs.len > 0) self.allocator.free(local_ptrs);
                if (regs.len > 0) self.allocator.free(regs);
                return error.OutOfMemory;
            }
        else
            &.{};
        defer if (is_local_in_place.len > 0) self.allocator.free(is_local_in_place);
        if (is_local_in_place.len > 0) {
            @memset(is_local_in_place, false);
            is_local_in_place[0] = true;
            for (body.places.items) |pl_item| {
                if (pl_item.base < local_count) is_local_in_place[pl_item.base] = true;
            }
        }

        self.call_stack.append(self.allocator, .{
            .body = body,
            .regs = regs,
            .local_ptrs = local_ptrs,
            .owned_stack_allocs = owned_stack_allocs,
            .call_site_span = call_site_span,
        }) catch {
            if (owned_stack_allocs.len > 0) self.allocator.free(owned_stack_allocs);
            if (local_ptrs.len > 0) self.allocator.free(local_ptrs);
            if (regs.len > 0) self.allocator.free(regs);
            return error.OutOfMemory;
        };
        defer {
            const popped = self.call_stack.pop().?;
            for (popped.owned_stack_allocs) |owned_aid| {
                if (owned_aid != .none and owned_aid.domain() == .vm_alloc) {
                    const slot_i = owned_aid.payloadIndex();
                    if (slot_i > 0 and slot_i < self.allocations.items.len) {
                        self.allocations.items[slot_i].is_live = false;
                    }
                }
            }
            if (popped.owned_stack_allocs.len > 0) self.allocator.free(popped.owned_stack_allocs);
            if (popped.local_ptrs.len > 0) self.allocator.free(popped.local_ptrs);
            if (popped.regs.len > 0) self.allocator.free(popped.regs);
        }

        var val_arg_cursor: usize = 0;
        var alias_arg_cursor: usize = 0;

        for (body.locals.items, 0..) |loc_decl, loc_i| {
            const is_param = loc_i >= 1 and loc_i <= body.param_count;
            if (is_param and (loc_decl.mode() == .inout_mode or loc_decl.mode() == .set_mode) and
                alias_arg_cursor < alias_places.len)
            {
                local_ptrs[loc_i] = alias_places[alias_arg_cursor];
                alias_arg_cursor += 1;
                continue;
            }

            if (!is_param and !is_local_in_place[loc_i]) continue;

            const lay = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                loc_decl.type_id,
                self.options.target_layout,
            );
            const unwrapped_loc = self.pool.unwrapUnderlyingType(loc_decl.type_id);
            const loc_node = self.pool.getNode(unwrapped_loc);
            const soa_cap: u32 = if (loc_node.tag == .soa_array_ty)
                (loc_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG)
            else
                0;
            const loc_span = self.resolveTokenSpan(body.file_id, loc_decl.origin_token);
            const stack_id = try self.allocMemory(
                lay.byte_size,
                lay.align_log2,
                true,
                true,
                false,
                soa_cap,
                loc_span,
            );
            local_ptrs[loc_i] = .{ .alloc_id = stack_id, .byte_offset = 0 };
            owned_stack_allocs[loc_i] = stack_id;

            if (is_param and val_arg_cursor < arg_slots.len) {
                if (loc_decl.mode() != .set_mode) {
                    try self.storeTypedSlotToMemory(
                        local_ptrs[loc_i],
                        loc_decl.type_id,
                        arg_slots[val_arg_cursor],
                    );
                }
                val_arg_cursor += 1;
                if (!loc_decl.flags().is_mut and
                    loc_decl.mode() != .inout_mode and
                    loc_decl.mode() != .set_mode)
                {
                    self.allocations.items[stack_id.payloadIndex()].is_mutable = false;
                }
            }
        }

        if (body.blocks.items.len == 0) return .{ .scalar_u64 = 0 };

        var cur_bb = MirBlockId.fromInt(0);
        var edge_arg_scratch: std.ArrayListUnmanaged(RegSlot) = .empty;
        defer edge_arg_scratch.deinit(self.allocator);

        while (true) {
            const frame_idx = self.call_stack.items.len - 1;
            const bb_rec = body.blocks.items[cur_bb.asInt()];

            for (body.getBlockInsts(cur_bb)) |inst_val| {
                try self.tickStepBudget();
                if (inst_val.asInt() < body.origin_tokens.items.len) {
                    const tok = body.origin_tokens.items[inst_val.asInt()];
                    if (!tok.isNone()) {
                        self.active_inst_span = self.resolveTokenSpan(body.file_id, tok);
                    }
                }
                const inst_rec = body.getInst(inst_val);
                if (inst_rec.flags.is_abort_on_panic) self.abort_on_panic_depth += 1;
                defer if (inst_rec.flags.is_abort_on_panic) {
                    self.abort_on_panic_depth -= 1;
                };
                const res_slot = try self.evalInst(frame_idx, inst_val);
                self.call_stack.items[frame_idx].regs[inst_val.asInt()] = res_slot;
            }

            try self.tickStepBudget();
            const term = bb_rec.terminator;
            switch (term.kind) {
                .unreachable_term => {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "reached statically `unreachable` control-flow point during `comptime` evaluation",
                        "`unreachable` executed here",
                        null,
                    );
                },
                .trap => {
                    const is_abort_trap = (term.aux_u8 & mir.TRAP_ABORT_ON_PANIC_FLAG) != 0;
                    if (is_abort_trap) self.abort_on_panic_depth += 1;
                    defer if (is_abort_trap) {
                        self.abort_on_panic_depth -= 1;
                    };
                    const reason: MirTrapReason = @fromBackingInt(@intCast(@as(u2, @truncate(term.aux_u8))));
                    return switch (reason) {
                        .assertion_failed => if (self.abort_on_panic_depth > 0) blk: {
                            self.has_aborted_vacated_panic = true;
                            break :blk error.AbortedVacatedPanic;
                        } else error.CompileAssertionFailed,
                        .bounds_check => self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "bounds check failed during `comptime` evaluation",
                            "out-of-bounds access here",
                            null,
                        ),
                        .arithmetic_overflow => self.failWithTrap(
                            error.IntegerOverflow,
                            .e0502_integer_constant_overflow,
                            "integer overflow trapped during `comptime` evaluation",
                            "arithmetic trap here",
                            null,
                        ),
                        .unreachable_reached => self.failWithTrap(
                            error.ArithmeticTrap,
                            .e0507_comptime_arithmetic_trap,
                            "trap instruction executed during `comptime` evaluation",
                            "trap reached here",
                            null,
                        ),
                    };
                },
                .ret => {
                    if (term.cond_or_val != mir.NONE_U32) {
                        return self.call_stack.items[frame_idx].regs[term.cond_or_val];
                    }
                    return self.loadTypedSlotFromMemory(
                        self.call_stack.items[frame_idx].local_ptrs[0],
                        body.ret_ty,
                    );
                },
                .br => {
                    const edge = body.extra_edges.items[term.edge_start];
                    try self.transferEdgeArgs(frame_idx, edge, &edge_arg_scratch);
                    cur_bb = edge.target_bb;
                },
                .cond_br => {
                    const cond_slot = self.call_stack.items[frame_idx].regs[term.cond_or_val];
                    const edge_offset: u32 = if ((cond_slot.scalar_u64 & 1) != 0) 0 else 1;
                    const edge = body.extra_edges.items[term.edge_start + edge_offset];
                    try self.transferEdgeArgs(frame_idx, edge, &edge_arg_scratch);
                    cur_bb = edge.target_bb;
                },
                .switch_int => {
                    const discr_val = MirValueId.fromInt(term.cond_or_val);
                    const discr_ty = body.getInst(discr_val).type_id;
                    const discr_slot = self.call_stack.items[frame_idx].regs[term.cond_or_val];
                    const raw_bits = try self.readIntBitsFromSlot(discr_slot, discr_ty);
                    const int_info = resolveIntInfo(self.pool, discr_ty, self.options.target_layout);
                    const discr_i128: i128 = if (int_info != null and int_info.?.is_signed)
                        signExtendToI128(raw_bits, int_info.?.bits)
                    else
                        @bitCast(raw_bits);

                    var chosen_edge_idx: u32 = term.edge_start + term.edge_len - 1;
                    var case_i: u32 = 0;
                    while (case_i + 1 < term.edge_len) : (case_i += 1) {
                        const cand_edge = body.extra_edges.items[term.edge_start + case_i];
                        if (cand_edge.case_tag_idx < body.switch_values.items.len) {
                            if (body.switch_values.items[cand_edge.case_tag_idx] == discr_i128) {
                                chosen_edge_idx = term.edge_start + case_i;
                                break;
                            }
                        }
                    }
                    const chosen_edge = body.extra_edges.items[chosen_edge_idx];
                    try self.transferEdgeArgs(frame_idx, chosen_edge, &edge_arg_scratch);
                    cur_bb = chosen_edge.target_bb;
                },
                .call => {
                    const call_site = body.calls.items[term.cond_or_val];
                    if (!call_site.origin_token.isNone()) {
                        self.active_inst_span = self.resolveTokenSpan(body.file_id, call_site.origin_token);
                    }
                    const call_span = self.active_inst_span;
                    if (call_site.is_abort_on_panic) self.abort_on_panic_depth += 1;
                    defer if (call_site.is_abort_on_panic) {
                        self.abort_on_panic_depth -= 1;
                    };
                    const ret_slot = try self.evalCallSite(frame_idx, call_site, call_span);

                    const normal_edge = body.extra_edges.items[term.edge_start];
                    const dst_params = body.getBlockParams(normal_edge.target_bb);
                    if (dst_params.len >= 1) {
                        self.call_stack.items[frame_idx].regs[dst_params[0].asInt()] = ret_slot;
                    }
                    cur_bb = normal_edge.target_bb;
                },
            }
        }
    }

    /// Evaluates outgoing SSA edge arguments in parallel and assigns them to `edge.target_bb`'s `block_param`s.
    fn transferEdgeArgs(
        self: *MirVm,
        frame_idx: usize,
        edge: mir.MirOutgoingEdge,
        scratch: *std.ArrayListUnmanaged(RegSlot),
    ) VmEvalError!void {
        if (edge.args_len == 0) return;
        const frame = &self.call_stack.items[frame_idx];
        const body = frame.body;
        scratch.clearRetainingCapacity();
        scratch.ensureTotalCapacity(self.allocator, edge.args_len) catch return error.OutOfMemory;
        for (body.extra_args.items[edge.args_start .. edge.args_start + edge.args_len]) |arg_raw| {
            scratch.appendAssumeCapacity(frame.regs[arg_raw]);
        }
        const dst_params = body.getBlockParams(edge.target_bb);
        const assign_count = @min(dst_params.len, scratch.items.len);
        for (0..assign_count) |param_i| {
            frame.regs[dst_params[param_i].asInt()] = scratch.items[param_i];
        }
    }

    /// Resolves and invokes a direct, indirect, or closure `MirCallSite` (`E0503` on `extern` FFI).
    fn evalCallSite(
        self: *MirVm,
        frame_idx: usize,
        call_site: mir.MirCallSite,
        call_span: Span,
    ) VmEvalError!RegSlot {
        const caller_body = self.call_stack.items[frame_idx].body;

        var val_args: std.ArrayListUnmanaged(RegSlot) = .empty;
        defer val_args.deinit(self.allocator);
        var alias_args: std.ArrayListUnmanaged(SymbolicPtr) = .empty;
        defer alias_args.deinit(self.allocator);

        // Resolve target callable and optional closure environment captures first:
        var callable_idx: ?u32 = null;
        if (!call_site.direct_def_id.isNone() or !call_site.direct_symbol.isNone()) {
            callable_idx = try self.resolveOrLoadCallable(call_site.direct_def_id, call_site.direct_symbol);
        } else {
            const callee_slot = self.call_stack.items[frame_idx].regs[call_site.callee_val.asInt()];
            const callee_ty = self.pool.unwrapUnderlyingType(
                caller_body.getInst(call_site.callee_val).type_id,
            );
            if (callee_slot.sym_ptr.alloc_id.isFnAddr()) {
                callable_idx = callee_slot.sym_ptr.alloc_id.payloadIndex();
            } else if (self.pool.getNode(callee_ty).tag == .closure_ty and
                (callee_slot.sym_ptr.alloc_id.domain() == .vm_alloc or
                    callee_slot.sym_ptr.alloc_id.domain() == .rodata_blob))
            {
                const env_ptr = callee_slot.sym_ptr;
                const fn_ptr = try self.readPointerAt(env_ptr, self.options.target_layout.ptr_align_log2);
                if (!fn_ptr.alloc_id.isFnAddr()) {
                    return self.failWithTrap(
                        error.InvalidPointer,
                        .e0506_comptime_invalid_pointer,
                        "corrupted closure target function pointer at `comptime`",
                        "invalid closure function handle",
                        null,
                    );
                }
                callable_idx = fn_ptr.alloc_id.payloadIndex();
                const target_entry = self.callables.items[callable_idx.?];
                if (target_entry.body) |closure_body| {
                    const capture_count = closure_body.param_count -| call_site.args_len;
                    if (capture_count > 0) {
                        const cap_env_ptr = try self.readPointerAt(
                            try self.advanceSymbolicPtr(env_ptr, self.options.target_layout.ptr_byte_size),
                            self.options.target_layout.ptr_align_log2,
                        );
                        var cur_off: u64 = 0;
                        for (0..capture_count) |cap_i| {
                            const cap_ty = closure_body.locals.items[1 + cap_i].type_id;
                            const cap_lay = type_system.computeTypeLayoutWithPool(
                                self.pool,
                                self.sym_table,
                                cap_ty,
                                self.options.target_layout,
                            );
                            if (cap_lay.byte_size == 0) {
                                val_args.append(self.allocator, .{ .scalar_u64 = 0 }) catch return error.OutOfMemory;
                                continue;
                            }
                            cur_off = std.mem.alignForward(u64, cur_off, @max(@as(u64, cap_lay.align_bytes), 1));
                            const cap_ptr = try self.advanceSymbolicPtr(cap_env_ptr, cur_off);
                            const cap_slot = try self.loadTypedSlotFromMemory(cap_ptr, cap_ty);
                            val_args.append(self.allocator, cap_slot) catch return error.OutOfMemory;
                            cur_off += cap_lay.byte_size;
                        }
                    }
                }
            } else {
                return self.failWithTrap(
                    error.InvalidPointer,
                    .e0506_comptime_invalid_pointer,
                    "indirect call through null or non-function pointer during `comptime` evaluation",
                    "invalid indirect callee pointer",
                    null,
                );
            }
        }

        const fn_idx = callable_idx.?;
        if (fn_idx == ALLOC_PAYLOAD_MASK - 1) {
            return self.failWithTrap(
                error.UnresolvedCallee,
                .e0503_forbidden_comptime_operation,
                "target function body is unavailable for `comptime` execution",
                "cannot resolve `comptime` callee body here",
                null,
            );
        }
        if (fn_idx >= self.callables.items.len) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "out-of-range callable table index at `comptime`",
                "invalid callable handle",
                null,
            );
        }
        const entry = self.callables.items[fn_idx];
        if (entry.is_extern) {
            return self.failWithTrap(
                error.ForbiddenOperation,
                .e0503_forbidden_comptime_operation,
                "cannot call `extern` FFI function during `comptime` evaluation",
                "`extern` FFI call is forbidden at `comptime`",
                null,
            );
        }
        const target_body = entry.body orelse {
            return self.failWithTrap(
                error.ForbiddenOperation,
                .e0503_forbidden_comptime_operation,
                "callee has no `MIR` body for `comptime` execution",
                "missing callee body",
                null,
            );
        };

        var unaligned_bounces: std.ArrayListUnmanaged(UnalignedBounceWriteback) = .empty;
        defer {
            for (unaligned_bounces.items) |wb| {
                const slot_idx = wb.bounce_ptr.alloc_id.payloadIndex();
                if (slot_idx > 0 and slot_idx < self.allocations.items.len) {
                    self.allocations.items[slot_idx].is_live = false;
                }
            }
            unaligned_bounces.deinit(self.allocator);
        }

        // Evaluate arguments (preserving caller frame lookup across `evalPlace`):
        for (0..call_site.args_len) |arg_i| {
            const mode = caller_body.call_arg_modes.items[call_site.modes_start + arg_i];
            const word = caller_body.extra_args.items[call_site.args_start + arg_i];
            if (mode == .let_mode or mode == .sink_mode) {
                val_args.append(
                    self.allocator,
                    self.call_stack.items[frame_idx].regs[word],
                ) catch return error.OutOfMemory;
            } else {
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(word),
                );
                switch (outcome) {
                    .memory_ptr => |mp| {
                        _ = try self.validateAccess(mp.ptr, 0, 0, true);
                        if (mp.is_unaligned) {
                            const bounce_lay = type_system.computeTypeLayoutWithPool(
                                self.pool,
                                self.sym_table,
                                mp.pointee_ty,
                                self.options.target_layout,
                            );
                            const bounce_id = try self.allocMemory(
                                bounce_lay.byte_size,
                                bounce_lay.align_log2,
                                true,
                                true,
                                false,
                                0,
                                call_span,
                            );
                            const bounce_ptr = SymbolicPtr{ .alloc_id = bounce_id, .byte_offset = 0 };
                            if (mode == .inout_mode and bounce_lay.byte_size > 0) {
                                try self.copyMemoryRange(bounce_ptr, mp.ptr, bounce_lay.byte_size, 0);
                            }
                            unaligned_bounces.append(self.allocator, .{
                                .orig_ptr = mp.ptr,
                                .bounce_ptr = bounce_ptr,
                                .byte_size = bounce_lay.byte_size,
                            }) catch return error.OutOfMemory;
                            alias_args.append(self.allocator, bounce_ptr) catch return error.OutOfMemory;
                        } else {
                            alias_args.append(self.allocator, mp.ptr) catch return error.OutOfMemory;
                        }
                    },
                    .constant_usize => {
                        return self.failWithTrap(
                            error.InvalidPointer,
                            .e0506_comptime_invalid_pointer,
                            "cannot pass constant `.len` metadata as `inout` or `set` place",
                            "immutable length metadata projected here",
                            null,
                        );
                    },
                }
            }
        }

        const call_res = try self.invokeBodyInternal(target_body, val_args.items, alias_args.items, call_span);
        for (unaligned_bounces.items) |wb| {
            if (wb.byte_size > 0) {
                try self.copyMemoryRange(wb.orig_ptr, wb.bounce_ptr, wb.byte_size, 0);
            }
        }
        return call_res;
    }

    /// Evaluates a single `MirInst` inside `call_stack[frame_idx]`.
    fn evalInst(self: *MirVm, frame_idx: usize, inst_val: MirValueId) VmEvalError!RegSlot {
        const body = self.call_stack.items[frame_idx].body;
        const inst = body.getInst(inst_val);

        switch (inst.op) {
            .block_param => return self.call_stack.items[frame_idx].regs[inst_val.asInt()],
            .ghost_access_let,
            .ghost_access_inout,
            .ghost_access_set,
            .ghost_access_end,
            .ghost_storage_move,
            => return .{ .scalar_u64 = 0 },
            .ghost_storage_init => {
                const lid = inst.operands.lhs;
                if (lid > body.param_count and lid < self.call_stack.items[frame_idx].owned_stack_allocs.len) {
                    try self.ensureLocalStackAllocation(frame_idx, lid);
                }
                return .{ .scalar_u64 = 0 };
            },
            .ghost_storage_deinit => {
                const lid = inst.operands.lhs;
                if (lid > body.param_count and lid < self.call_stack.items[frame_idx].local_ptrs.len) {
                    const old_aid = self.call_stack.items[frame_idx].owned_stack_allocs[lid];
                    if (old_aid != .none and old_aid.domain() == .vm_alloc and old_aid != .null_ptr) {
                        const slot_idx = old_aid.payloadIndex();
                        if (slot_idx > 0 and slot_idx < self.allocations.items.len) {
                            self.allocations.items[slot_idx].is_live = false;
                        }
                    }
                    self.call_stack.items[frame_idx].owned_stack_allocs[lid] = .none;
                    self.call_stack.items[frame_idx].local_ptrs[lid] = SymbolicPtr.NULL;
                }
                return .{ .scalar_u64 = 0 };
            },
            .const_scalar => return self.evalConstScalar(body.consts.items[inst.operands.lhs], inst.type_id),
            .copy_val => return self.call_stack.items[frame_idx].regs[inst.operands.lhs],
            .bin_op => {
                const kind: BinOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                return self.evalBinOp(
                    frame_idx,
                    kind,
                    MirValueId.fromInt(inst.operands.lhs),
                    MirValueId.fromInt(inst.operands.rhs),
                    inst.type_id,
                );
            },
            .unary_op => {
                const kind: UnaryOpKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                return self.evalUnaryOp(
                    frame_idx,
                    kind,
                    MirValueId.fromInt(inst.operands.lhs),
                    inst.operands.rhs,
                    inst.type_id,
                );
            },
            .aggregate_make => {
                const kind: AggregateKind = @fromBackingInt(@intCast(@as(u8, @truncate(inst.aux_u16))));
                return self.evalAggregateMake(frame_idx, kind, inst);
            },
            .aggregate_extract => {
                const agg_val = MirValueId.fromInt(inst.operands.lhs);
                const agg_ty = body.getInst(agg_val).type_id;
                const agg_slot = self.call_stack.items[frame_idx].regs[agg_val.asInt()];
                return self.evalAggregateExtract(agg_slot, agg_ty, inst.operands.rhs, inst.type_id);
            },
            .aggregate_insert => {
                const agg_val = MirValueId.fromInt(inst.operands.lhs);
                const agg_ty = body.getInst(agg_val).type_id;
                const agg_slot = self.call_stack.items[frame_idx].regs[agg_val.asInt()];
                const ordinal = body.extra_args.items[inst.operands.rhs];
                const new_elem_val = body.extra_args.items[inst.operands.rhs + 1];
                const new_elem_slot = self.call_stack.items[frame_idx].regs[new_elem_val];
                return self.evalAggregateInsert(agg_slot, agg_ty, ordinal, new_elem_slot);
            },
            .bitfield_extract => {
                const spec = BitSpec.fromU32(inst.operands.rhs);
                const src_val = MirValueId.fromInt(inst.operands.lhs);
                const src_ty = body.getInst(src_val).type_id;
                const src_bits = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[src_val.asInt()],
                    src_ty,
                );
                const shifted = if (spec.bit_offset < 128)
                    src_bits >> @intCast(spec.bit_offset)
                else
                    0;
                const extracted = maskToBitsU128(shifted, spec.bit_width);
                if (spec.is_signed) {
                    const sext = signExtendToI128(extracted, spec.bit_width);
                    return self.makeIntSlot(inst.type_id, @bitCast(sext));
                }
                return self.makeIntSlot(inst.type_id, extracted);
            },
            .bitfield_insert => {
                const spec = BitSpec.fromU32(inst.operands.rhs);
                const back_val = MirValueId.fromInt(body.extra_args.items[inst.operands.lhs]);
                const ins_val = MirValueId.fromInt(body.extra_args.items[inst.operands.lhs + 1]);
                const back_ty = body.getInst(back_val).type_id;
                const ins_ty = body.getInst(ins_val).type_id;
                const back_bits = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[back_val.asInt()],
                    back_ty,
                );
                const ins_bits = maskToBitsU128(
                    try self.readIntBitsFromSlot(
                        self.call_stack.items[frame_idx].regs[ins_val.asInt()],
                        ins_ty,
                    ),
                    spec.bit_width,
                );
                const width_mask = if (spec.bit_width >= 128)
                    std.math.maxInt(u128)
                else
                    (@as(u128, 1) << @intCast(spec.bit_width)) - 1;
                const shifted_mask = width_mask << @intCast(spec.bit_offset);
                const updated = (back_bits & ~shifted_mask) | (ins_bits << @intCast(spec.bit_offset));
                return self.makeIntSlot(inst.type_id, updated);
            },
            .fn_addr => {
                const target_def = DefId.fromInt(inst.operands.lhs);
                const target_sym = SymbolIndex.fromInt(inst.operands.rhs);
                if (!target_sym.isNone() and target_sym.asInt() < self.sym_table.symbols.items.len and
                    self.sym_table.getSymbol(target_sym).kind == .const_sym)
                {
                    if (self.options.compiler_db) |db| {
                        const loaded_slot = try db.loadEvaluatedConstInVm(self, target_def, inst.type_id);
                        try self.recordObservedQueryDep(query_db.QueryKey.forDef(.eval_comptime_def, target_def));
                        return loaded_slot;
                    }
                    const const_fn_idx = try self.resolveOrLoadCallable(target_def, target_sym);
                    if (self.callables.items[const_fn_idx].body) |const_body| {
                        return self.invokeBodyInternal(const_body, &.{}, &.{}, self.active_inst_span);
                    }
                    return error.UnresolvedCallee;
                }
                const fn_idx = (try self.tryResolveOrLoadCallable(target_def, target_sym)) orelse
                    (ALLOC_PAYLOAD_MASK - 1);
                return .{
                    .sym_ptr = .{
                        .alloc_id = ComptimeAllocId.fromFnIndex(fn_idx),
                        .byte_offset = 0,
                    },
                };
            },
            .place_load => {
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                return switch (outcome) {
                    .constant_usize => |len_val| self.makeIntSlot(inst.type_id, len_val),
                    .memory_ptr => |mp| self.loadTypedSlotFromMemoryAligned(mp.ptr, inst.type_id, mp.is_unaligned),
                };
            },
            .place_store => {
                const rhs_slot = self.call_stack.items[frame_idx].regs[inst.operands.rhs];
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                switch (outcome) {
                    .memory_ptr => |mp| {
                        try self.storeTypedSlotToMemoryAligned(mp.ptr, mp.pointee_ty, rhs_slot, mp.is_unaligned);
                    },
                    .constant_usize => {
                        return self.failWithTrap(
                            error.InvalidPointer,
                            .e0506_comptime_invalid_pointer,
                            "cannot overwrite immutable `.len` slice property at `comptime`",
                            "attempted store to `.len`",
                            null,
                        );
                    },
                }
                return .{ .scalar_u64 = 0 };
            },
            .place_discriminant => {
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                const mp = outcome.memory_ptr;
                const tag_ord = try self.readSumDiscriminantAt(mp.ptr, mp.pointee_ty);
                return self.makeIntSlot(inst.type_id, tag_ord);
            },
            .place_set_discrim => {
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                const mp = outcome.memory_ptr;
                try self.writeSumDiscriminantAt(mp.ptr, mp.pointee_ty, inst.operands.rhs);
                return .{ .scalar_u64 = 0 };
            },
            .place_addr => {
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                const mp = outcome.memory_ptr;
                const is_mut_addr = inst.operands.rhs != 0;
                _ = try self.validateAccess(mp.ptr, 0, 0, is_mut_addr);
                const res_unwrapped = self.pool.unwrapUnderlyingType(inst.type_id);
                const res_node = self.pool.getNode(res_unwrapped);
                if (res_node.tag == .slice_ty or res_node.tag == .soa_slice_ty) {
                    const src_node = self.pool.getNode(mp.pointee_ty);
                    const arr_len: u64 = src_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    return self.makeFatSliceSlot(inst.type_id, mp.ptr, arr_len);
                }
                if (res_node.tag == .ref_ty or res_node.tag == .mut_ref_ty or res_node.tag == .raw_ptr_ty) {
                    const dst_pointee = self.pool.unwrapUnderlyingType(TypeId.fromInt(res_node.lhs));
                    const dst_pointee_tag = self.pool.getNode(dst_pointee).tag;
                    const src_node = self.pool.getNode(mp.pointee_ty);
                    if ((dst_pointee_tag == .slice_ty or dst_pointee_tag == .soa_slice_ty) and
                        (src_node.tag == .array_ty or src_node.tag == .soa_array_ty))
                    {
                        const arr_len: u64 = src_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        return self.makeFatSliceSlot(dst_pointee, mp.ptr, arr_len);
                    }
                }
                return .{ .sym_ptr = mp.ptr };
            },
            .soa_column_slice => {
                const outcome = try self.evalPlace(
                    frame_idx,
                    PlaceId.fromInt(inst.operands.lhs),
                );
                var base_ptr = outcome.memory_ptr.ptr;
                var base_ty = outcome.memory_ptr.pointee_ty;
                const maybe_ref = self.pool.getNode(base_ty);
                if (maybe_ref.tag == .ref_ty or maybe_ref.tag == .mut_ref_ty or maybe_ref.tag == .raw_ptr_ty) {
                    base_ptr = try self.readPointerAt(base_ptr, self.options.target_layout.ptr_align_log2);
                    base_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(maybe_ref.lhs));
                }
                const soa_node = self.pool.getNode(base_ty);
                const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(soa_node.lhs));
                if (soa_node.tag == .soa_array_ty) {
                    const cap: u32 = soa_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    const col = computeSoaColumnOffsetAndType(
                        self.pool,
                        self.sym_table,
                        elem_struct_ty,
                        inst.operands.rhs,
                        cap,
                        self.options.target_layout,
                    ) orelse return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "invalid `#soa` column slice ordinal at `comptime`",
                        "invalid `#soa` column",
                        null,
                    );
                    const col_ptr = try self.advanceSymbolicPtr(base_ptr, col.column_byte_offset);
                    return self.makeFatSliceSlot(inst.type_id, col_ptr, cap);
                } else {
                    const fat = try self.readFatSliceParts(base_ptr);
                    var backing_cap: u32 = @truncate(fat.elem_len);
                    if (fat.data_ptr.alloc_id.domain() == .vm_alloc) {
                        const rec = &self.allocations.items[fat.data_ptr.alloc_id.payloadIndex()];
                        if (rec.soa_elem_capacity > 0) backing_cap = rec.soa_elem_capacity;
                    }
                    const col = computeSoaColumnOffsetAndType(
                        self.pool,
                        self.sym_table,
                        elem_struct_ty,
                        inst.operands.rhs,
                        backing_cap,
                        self.options.target_layout,
                    ) orelse return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "invalid `#soa` slice column ordinal at `comptime`",
                        "invalid `#soa` column",
                        null,
                    );
                    const col_ptr = try self.advanceSymbolicPtr(fat.data_ptr, col.column_byte_offset);
                    return self.makeFatSliceSlot(inst.type_id, col_ptr, fat.elem_len);
                }
            },
            .intrinsic_op => {
                const intr_kind: MirIntrinsicKind = @fromBackingInt(inst.aux_u16);
                return self.evalIntrinsicOp(frame_idx, intr_kind, inst);
            },
        }
    }

    /// Materializes a `MirConst` into a typed `RegSlot`.
    fn evalConstScalar(self: *MirVm, mir_const: mir.MirConst, raw_ty: TypeId) VmEvalError!RegSlot {
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        switch (mir_const) {
            .unit_val => return .{ .scalar_u64 = 0 },
            .bool_val => |flag| return .{ .scalar_u64 = @intFromBool(flag) },
            .char_val => |cp| return .{ .scalar_u64 = cp },
            .int_val => |int_v| return self.makeIntSlot(ty, @bitCast(int_v)),
            .float_val => |flt_v| {
                if (ty == .f32_ty) return packF32Slot(@floatCast(flt_v));
                return .{ .scalar_f64 = canonicalizeF64(flt_v) };
            },
            .str_val => |sym_id| {
                const text = self.interner.get(sym_id);
                const data_ptr = SymbolicPtr{
                    .alloc_id = ComptimeAllocId.fromStringId(sym_id),
                    .byte_offset = 0,
                };
                return self.makeFatSliceSlot(ty, data_ptr, text.len);
            },
            .bytes_val => |sym_id| {
                const bytes = self.interner.get(sym_id);
                const data_ptr = SymbolicPtr{
                    .alloc_id = ComptimeAllocId.fromStringId(sym_id),
                    .byte_offset = 0,
                };
                const ty_node = self.pool.getNode(ty);
                if (ty_node.tag == .ref_ty or ty_node.tag == .raw_ptr_ty) {
                    const pointee_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                    if (self.pool.getNode(pointee_ty).tag == .slice_ty) {
                        const slice_slot = try self.makeFatSliceSlot(pointee_ty, data_ptr, bytes.len);
                        const rodata_id = try self.promoteSnapshotToRodata(slice_slot.sym_ptr, pointee_ty);
                        return .{ .sym_ptr = .{ .alloc_id = rodata_id, .byte_offset = 0 } };
                    }
                    return .{ .sym_ptr = data_ptr };
                }
                return self.makeFatSliceSlot(ty, data_ptr, bytes.len);
            },
            .raw_blob => |rb| {
                const store = self.options.blob_store orelse {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "`MirConst.raw_blob` executed without an attached `MirBlobStore`",
                        "missing `MirBlobStore` for `@embed_bytes` blob",
                        null,
                    );
                };
                const raw_bytes = store.getBytes(rb.blob_id) orelse {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "`MirConst.raw_blob` references out-of-range blob index",
                        "invalid `blob_id` here",
                        null,
                    );
                };
                const blob_aid = self.rodata_pool.internBlob(raw_bytes, &.{}, rb.align_log2) catch
                    return error.OutOfMemory;
                const data_ptr = SymbolicPtr{ .alloc_id = blob_aid, .byte_offset = 0 };
                const ty_node = self.pool.getNode(ty);
                if (ty_node.tag == .ref_ty or ty_node.tag == .raw_ptr_ty) {
                    const pointee_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                    if (self.pool.getNode(pointee_ty).tag == .slice_ty) {
                        const slice_slot = try self.makeFatSliceSlot(pointee_ty, data_ptr, raw_bytes.len);
                        const rodata_id = try self.promoteSnapshotToRodata(slice_slot.sym_ptr, pointee_ty);
                        return .{ .sym_ptr = .{ .alloc_id = rodata_id, .byte_offset = 0 } };
                    }
                    return .{ .sym_ptr = data_ptr };
                }
                return self.makeFatSliceSlot(ty, data_ptr, raw_bytes.len);
            },
        }
    }

    /// Reads the UTF-8 byte slice of a `str` or `[u8]` fat-slice `RegSlot`.
    pub fn readStrSlotBytes(self: *MirVm, slot: RegSlot) VmEvalError![]u8 {
        const fat = try self.readFatSliceParts(slot.sym_ptr);
        if (fat.elem_len == 0) return self.allocator.alloc(u8, 0) catch return error.OutOfMemory;
        if (fat.elem_len > self.options.mem_limit) {
            return self.failWithTrap(
                error.ResourceLimitExceeded,
                .e0508_comptime_resource_limit_exceeded,
                "string slice length exceeds `comptime` memory budget",
                "oversized string slice",
                null,
            );
        }
        const len_usize: usize = @intCast(fat.elem_len);
        const out_buf = self.allocator.alloc(u8, len_usize) catch return error.OutOfMemory;
        errdefer self.allocator.free(out_buf);
        try self.readScalarBytes(fat.data_ptr, 0, out_buf);
        return out_buf;
    }

    /// Recursively evaluates structural equality between two typed `RegSlot` values (capped at depth 64).
    fn areTypedSlotsEqual(
        self: *MirVm,
        raw_ty: TypeId,
        lhs_slot: RegSlot,
        rhs_slot: RegSlot,
        depth: u32,
    ) VmEvalError!bool {
        if (depth > 64) return false;
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            ty,
            self.options.target_layout,
        );
        if (lay.byte_size == 0) return true;

        if (ty == .str_ty) {
            const lhs_bytes = try self.readStrSlotBytes(lhs_slot);
            defer self.allocator.free(lhs_bytes);
            const rhs_bytes = try self.readStrSlotBytes(rhs_slot);
            defer self.allocator.free(rhs_bytes);
            return std.mem.eql(u8, lhs_bytes, rhs_bytes);
        }
        if (ty == .f32_ty) {
            return unpackF32Slot(lhs_slot) == unpackF32Slot(rhs_slot);
        }
        if (ty == .f64_ty or ty == .untyped_float_ty) {
            return canonicalizeF64(lhs_slot.scalar_f64) == canonicalizeF64(rhs_slot.scalar_f64);
        }
        if (resolveIntInfo(self.pool, ty, self.options.target_layout) != null) {
            return (try self.readIntBitsFromSlot(lhs_slot, ty)) ==
                (try self.readIntBitsFromSlot(rhs_slot, ty));
        }
        const repr = classifyValueRepr(self.pool, self.sym_table, ty, self.options.target_layout);
        if (repr == .inline_ptr) {
            return lhs_slot.sym_ptr.alloc_id == rhs_slot.sym_ptr.alloc_id and
                lhs_slot.sym_ptr.byte_offset == rhs_slot.sym_ptr.byte_offset;
        }

        const node = self.pool.getNode(ty);
        switch (node.tag) {
            .enum_ty, .optional_ty, .result_ty => {
                const lhs_tag = try self.readSumDiscriminantAt(lhs_slot.sym_ptr, ty);
                const rhs_tag = try self.readSumDiscriminantAt(rhs_slot.sym_ptr, ty);
                if (lhs_tag != rhs_tag) return false;
                const var_pay_ty = self.pool.unwrapUnderlyingType(
                    resolveVariantPayloadType(self.pool, self.sym_table, ty, lhs_tag),
                );
                const pay_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    var_pay_ty,
                    self.options.target_layout,
                );
                if (pay_lay.byte_size == 0) return true;
                const sum_info = computeSumTypeTagAndPayloadLayout(
                    self.pool,
                    self.sym_table,
                    ty,
                    self.options.target_layout,
                );
                const lhs_pay = try self.loadTypedSlotFromMemoryAligned(
                    try self.advanceSymbolicPtr(lhs_slot.sym_ptr, sum_info.payload_offset),
                    var_pay_ty,
                    true,
                );
                const rhs_pay = try self.loadTypedSlotFromMemoryAligned(
                    try self.advanceSymbolicPtr(rhs_slot.sym_ptr, sum_info.payload_offset),
                    var_pay_ty,
                    true,
                );
                return self.areTypedSlotsEqual(var_pay_ty, lhs_pay, rhs_pay, depth + 1);
            },
            .struct_ty, .tuple_ty => {
                const is_packed_st = isPackedStructType(self.pool, self.sym_table, ty);
                var ord: u32 = 0;
                while (computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    ty,
                    ord,
                    self.options.target_layout,
                )) |f_info| : (ord += 1) {
                    const lhs_f = try self.loadTypedSlotFromMemoryAligned(
                        try self.advanceSymbolicPtr(lhs_slot.sym_ptr, f_info.byte_offset),
                        f_info.field_ty,
                        is_packed_st,
                    );
                    const rhs_f = try self.loadTypedSlotFromMemoryAligned(
                        try self.advanceSymbolicPtr(rhs_slot.sym_ptr, f_info.byte_offset),
                        f_info.field_ty,
                        is_packed_st,
                    );
                    if (!(try self.areTypedSlotsEqual(f_info.field_ty, lhs_f, rhs_f, depth + 1))) {
                        return false;
                    }
                }
                return true;
            },
            .array_ty => {
                const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const arr_len: u32 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const elem_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    elem_ty,
                    self.options.target_layout,
                );
                var elem_i: u32 = 0;
                while (elem_i < arr_len) : (elem_i += 1) {
                    const off = try self.mulOffsetChecked(elem_i, elem_lay.byte_size);
                    const lhs_e = try self.loadTypedSlotFromMemoryAligned(
                        try self.advanceSymbolicPtr(lhs_slot.sym_ptr, off),
                        elem_ty,
                        true,
                    );
                    const rhs_e = try self.loadTypedSlotFromMemoryAligned(
                        try self.advanceSymbolicPtr(rhs_slot.sym_ptr, off),
                        elem_ty,
                        true,
                    );
                    if (!(try self.areTypedSlotsEqual(elem_ty, lhs_e, rhs_e, depth + 1))) {
                        return false;
                    }
                }
                return true;
            },
            .soa_array_ty => {
                const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const cap: u32 = node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                var col_ord: u32 = 0;
                while (computeSoaColumnOffsetAndType(
                    self.pool,
                    self.sym_table,
                    elem_struct_ty,
                    col_ord,
                    cap,
                    self.options.target_layout,
                )) |col| : (col_ord += 1) {
                    const f_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        col.field_ty,
                        self.options.target_layout,
                    );
                    var elem_i: u32 = 0;
                    while (elem_i < cap) : (elem_i += 1) {
                        const off = col.column_byte_offset + (try self.mulOffsetChecked(elem_i, f_lay.byte_size));
                        const lhs_e = try self.loadTypedSlotFromMemoryAligned(
                            try self.advanceSymbolicPtr(lhs_slot.sym_ptr, off),
                            col.field_ty,
                            true,
                        );
                        const rhs_e = try self.loadTypedSlotFromMemoryAligned(
                            try self.advanceSymbolicPtr(rhs_slot.sym_ptr, off),
                            col.field_ty,
                            true,
                        );
                        if (!(try self.areTypedSlotsEqual(col.field_ty, lhs_e, rhs_e, depth + 1))) {
                            return false;
                        }
                    }
                }
                return true;
            },
            .slice_ty => {
                const lhs_fat = try self.readFatSliceParts(lhs_slot.sym_ptr);
                const rhs_fat = try self.readFatSliceParts(rhs_slot.sym_ptr);
                if (lhs_fat.elem_len != rhs_fat.elem_len) return false;
                const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                const elem_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    elem_ty,
                    self.options.target_layout,
                );
                var elem_i: u64 = 0;
                while (elem_i < lhs_fat.elem_len) : (elem_i += 1) {
                    const off = try self.mulOffsetChecked(elem_i, elem_lay.byte_size);
                    const lhs_e = try self.loadTypedSlotFromMemoryAligned(
                        try self.advanceSymbolicPtr(lhs_fat.data_ptr, off),
                        elem_ty,
                        true,
                    );
                    const rhs_e = try self.loadTypedSlotFromMemoryAligned(
                        try self.advanceSymbolicPtr(rhs_fat.data_ptr, off),
                        elem_ty,
                        true,
                    );
                    if (!(try self.areTypedSlotsEqual(elem_ty, lhs_e, rhs_e, depth + 1))) {
                        return false;
                    }
                }
                return true;
            },
            .soa_slice_ty => {
                const lhs_fat = try self.readFatSliceParts(lhs_slot.sym_ptr);
                const rhs_fat = try self.readFatSliceParts(rhs_slot.sym_ptr);
                if (lhs_fat.elem_len != rhs_fat.elem_len) return false;
                const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
                var lhs_cap: u32 = @truncate(lhs_fat.elem_len);
                if (lhs_fat.data_ptr.alloc_id.domain() == .vm_alloc) {
                    const rec = &self.allocations.items[lhs_fat.data_ptr.alloc_id.payloadIndex()];
                    if (rec.soa_elem_capacity > 0) lhs_cap = rec.soa_elem_capacity;
                }
                var rhs_cap: u32 = @truncate(rhs_fat.elem_len);
                if (rhs_fat.data_ptr.alloc_id.domain() == .vm_alloc) {
                    const rec = &self.allocations.items[rhs_fat.data_ptr.alloc_id.payloadIndex()];
                    if (rec.soa_elem_capacity > 0) rhs_cap = rec.soa_elem_capacity;
                }
                var col_ord: u32 = 0;
                while (true) : (col_ord += 1) {
                    const lhs_col = computeSoaColumnOffsetAndType(
                        self.pool,
                        self.sym_table,
                        elem_struct_ty,
                        col_ord,
                        lhs_cap,
                        self.options.target_layout,
                    ) orelse break;
                    const rhs_col = computeSoaColumnOffsetAndType(
                        self.pool,
                        self.sym_table,
                        elem_struct_ty,
                        col_ord,
                        rhs_cap,
                        self.options.target_layout,
                    ) orelse break;
                    const f_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        lhs_col.field_ty,
                        self.options.target_layout,
                    );
                    var elem_i: u64 = 0;
                    while (elem_i < lhs_fat.elem_len) : (elem_i += 1) {
                        const elem_off = try self.mulOffsetChecked(elem_i, f_lay.byte_size);
                        const lhs_e = try self.loadTypedSlotFromMemoryAligned(
                            try self.advanceSymbolicPtr(lhs_fat.data_ptr, lhs_col.column_byte_offset + elem_off),
                            lhs_col.field_ty,
                            true,
                        );
                        const rhs_e = try self.loadTypedSlotFromMemoryAligned(
                            try self.advanceSymbolicPtr(rhs_fat.data_ptr, rhs_col.column_byte_offset + elem_off),
                            rhs_col.field_ty,
                            true,
                        );
                        if (!(try self.areTypedSlotsEqual(lhs_col.field_ty, lhs_e, rhs_e, depth + 1))) {
                            return false;
                        }
                    }
                }
                return true;
            },
            .closure_ty => {
                const ptr_align = self.options.target_layout.ptr_align_log2;
                const ptr_width = self.options.target_layout.ptr_byte_size;
                const lhs_fn = try self.readPointerAt(lhs_slot.sym_ptr, ptr_align);
                const rhs_fn = try self.readPointerAt(rhs_slot.sym_ptr, ptr_align);
                const lhs_env = try self.readPointerAt(try self.advanceSymbolicPtr(lhs_slot.sym_ptr, ptr_width), ptr_align);
                const rhs_env = try self.readPointerAt(try self.advanceSymbolicPtr(rhs_slot.sym_ptr, ptr_width), ptr_align);
                return lhs_fn.alloc_id == rhs_fn.alloc_id and lhs_fn.byte_offset == rhs_fn.byte_offset and
                    lhs_env.alloc_id == rhs_env.alloc_id and lhs_env.byte_offset == rhs_env.byte_offset;
            },
            else => return false,
        }
    }

    /// Evaluates a typed binary `BinOpKind` instruction (`E0502` on overflow, `E0507` on div-by-zero).
    fn evalBinOp(
        self: *MirVm,
        frame_idx: usize,
        kind: BinOpKind,
        lhs_val: MirValueId,
        rhs_val: MirValueId,
        res_ty: TypeId,
    ) VmEvalError!RegSlot {
        const body = self.call_stack.items[frame_idx].body;
        const lhs_slot = self.call_stack.items[frame_idx].regs[lhs_val.asInt()];
        const rhs_slot = self.call_stack.items[frame_idx].regs[rhs_val.asInt()];
        const op_ty = self.pool.unwrapUnderlyingType(body.getInst(lhs_val).type_id);

        // [1] String equality (`str == str`, `str != str`):
        if (op_ty == .str_ty and (kind == .eq or kind == .ne)) {
            const lhs_bytes = try self.readStrSlotBytes(lhs_slot);
            defer self.allocator.free(lhs_bytes);
            const rhs_bytes = try self.readStrSlotBytes(rhs_slot);
            defer self.allocator.free(rhs_bytes);
            const is_eq = std.mem.eql(u8, lhs_bytes, rhs_bytes);
            return .{ .scalar_u64 = @intFromBool(if (kind == .eq) is_eq else !is_eq) };
        }

        // [2] Pointer equality & same-allocation relational comparison:
        const op_repr = classifyValueRepr(self.pool, self.sym_table, op_ty, self.options.target_layout);
        if (op_repr == .inline_ptr) {
            const lp = lhs_slot.sym_ptr;
            const rp = rhs_slot.sym_ptr;
            if (kind == .eq or kind == .ne) {
                const is_same = lp.alloc_id == rp.alloc_id and lp.byte_offset == rp.byte_offset;
                return .{ .scalar_u64 = @intFromBool(if (kind == .eq) is_same else !is_same) };
            }
            if (lp.alloc_id != rp.alloc_id) {
                return self.failWithTrap(
                    error.ForbiddenOperation,
                    .e0503_forbidden_comptime_operation,
                    "cannot order pointers from distinct allocations during `comptime` evaluation",
                    "unrelated pointer comparison here",
                    null,
                );
            }
            const cmp_res = switch (kind) {
                .ult, .slt => lp.byte_offset < rp.byte_offset,
                .ule, .sle => lp.byte_offset <= rp.byte_offset,
                .ugt, .sgt => lp.byte_offset > rp.byte_offset,
                .uge, .sge => lp.byte_offset >= rp.byte_offset,
                else => false,
            };
            return .{ .scalar_u64 = @intFromBool(cmp_res) };
        }

        // [3] IEEE-754 floating-point arithmetic & comparisons (with deterministic quiet NaNs):
        if (op_ty == .f32_ty) {
            const lf = unpackF32Slot(lhs_slot);
            const rf = unpackF32Slot(rhs_slot);
            return switch (kind) {
                .fadd => packF32Slot(lf + rf),
                .fsub => packF32Slot(lf - rf),
                .fmul => packF32Slot(lf * rf),
                .fdiv => packF32Slot(lf / rf),
                .frem => packF32Slot(@rem(lf, rf)),
                .eq => .{ .scalar_u64 = @intFromBool(lf == rf) },
                .ne => .{ .scalar_u64 = @intFromBool(lf != rf) },
                .flt => .{ .scalar_u64 = @intFromBool(lf < rf) },
                .fle => .{ .scalar_u64 = @intFromBool(lf <= rf) },
                .fgt => .{ .scalar_u64 = @intFromBool(lf > rf) },
                .fge => .{ .scalar_u64 = @intFromBool(lf >= rf) },
                else => .{ .scalar_u64 = 0 },
            };
        }
        if (op_ty == .f64_ty or op_ty == .untyped_float_ty) {
            const lf = canonicalizeF64(lhs_slot.scalar_f64);
            const rf = canonicalizeF64(rhs_slot.scalar_f64);
            return switch (kind) {
                .fadd => .{ .scalar_f64 = canonicalizeF64(lf + rf) },
                .fsub => .{ .scalar_f64 = canonicalizeF64(lf - rf) },
                .fmul => .{ .scalar_f64 = canonicalizeF64(lf * rf) },
                .fdiv => .{ .scalar_f64 = canonicalizeF64(lf / rf) },
                .frem => .{ .scalar_f64 = canonicalizeF64(@rem(lf, rf)) },
                .eq => .{ .scalar_u64 = @intFromBool(lf == rf) },
                .ne => .{ .scalar_u64 = @intFromBool(lf != rf) },
                .flt => .{ .scalar_u64 = @intFromBool(lf < rf) },
                .fle => .{ .scalar_u64 = @intFromBool(lf <= rf) },
                .fgt => .{ .scalar_u64 = @intFromBool(lf > rf) },
                .fge => .{ .scalar_u64 = @intFromBool(lf >= rf) },
                else => .{ .scalar_u64 = 0 },
            };
        }

        // [4] Integer & boolean arithmetic, shifts, bitwise ops, and comparisons (`1..128` bits):
        const info = resolveIntInfo(self.pool, op_ty, self.options.target_layout) orelse {
            if (kind == .eq or kind == .ne) {
                const is_eq = try self.areTypedSlotsEqual(op_ty, lhs_slot, rhs_slot, 0);
                return .{ .scalar_u64 = @intFromBool(if (kind == .eq) is_eq else !is_eq) };
            }
            return .{ .scalar_u64 = 0 };
        };
        const rhs_ty = body.getInst(rhs_val).type_id;
        const rhs_info = resolveIntInfo(self.pool, rhs_ty, self.options.target_layout) orelse info;

        const lu = try self.readIntBitsFromSlot(lhs_slot, op_ty);
        const ru = try self.readIntBitsFromSlot(rhs_slot, rhs_ty);
        const ls = signExtendToI128(lu, info.bits);
        const rs = signExtendToI128(ru, rhs_info.bits);

        const max_u: u128 = if (info.bits >= 128)
            std.math.maxInt(u128)
        else
            (@as(u128, 1) << @intCast(info.bits)) - 1;
        const min_s: i128 = if (info.bits >= 128)
            std.math.minInt(i128)
        else
            -(@as(i128, 1) << @intCast(info.bits - 1));
        const max_s: i128 = if (info.bits >= 128)
            std.math.maxInt(i128)
        else
            (@as(i128, 1) << @intCast(info.bits - 1)) - 1;

        switch (kind) {
            .sadd_checked => {
                const ov = @addWithOverflow(ls, rs);
                if (ov[1] != 0 or ov[0] < min_s or ov[0] > max_s) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "signed integer addition overflowed during `comptime` evaluation",
                        "signed addition overflow here",
                        "use wrapping `+%` or saturating `+|` if modular arithmetic is intended",
                    );
                }
                return self.makeIntSlot(res_ty, @bitCast(ov[0]));
            },
            .uadd_checked => {
                const ov = @addWithOverflow(lu, ru);
                if (ov[1] != 0 or ov[0] > max_u) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "unsigned integer addition overflowed during `comptime` evaluation",
                        "unsigned addition overflow here",
                        "use wrapping `+%` or saturating `+|` if modular arithmetic is intended",
                    );
                }
                return self.makeIntSlot(res_ty, ov[0]);
            },
            .ssub_checked => {
                const ov = @subWithOverflow(ls, rs);
                if (ov[1] != 0 or ov[0] < min_s or ov[0] > max_s) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "signed integer subtraction overflowed during `comptime` evaluation",
                        "signed subtraction overflow here",
                        "use wrapping `-%` or saturating `-|` if modular arithmetic is intended",
                    );
                }
                return self.makeIntSlot(res_ty, @bitCast(ov[0]));
            },
            .usub_checked => {
                if (lu < ru) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "unsigned integer subtraction underflowed during `comptime` evaluation",
                        "unsigned subtraction underflow here",
                        "use wrapping `-%` or saturating `-|` if modular arithmetic is intended",
                    );
                }
                return self.makeIntSlot(res_ty, lu - ru);
            },
            .smul_checked => {
                const ov = @mulWithOverflow(ls, rs);
                if (ov[1] != 0 or ov[0] < min_s or ov[0] > max_s) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "signed integer multiplication overflowed during `comptime` evaluation",
                        "signed multiplication overflow here",
                        "use wrapping `*%` or saturating `*|` if modular arithmetic is intended",
                    );
                }
                return self.makeIntSlot(res_ty, @bitCast(ov[0]));
            },
            .umul_checked => {
                const ov = @mulWithOverflow(lu, ru);
                if (ov[1] != 0 or ov[0] > max_u) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "unsigned integer multiplication overflowed during `comptime` evaluation",
                        "unsigned multiplication overflow here",
                        "use wrapping `*%` or saturating `*|` if modular arithmetic is intended",
                    );
                }
                return self.makeIntSlot(res_ty, ov[0]);
            },
            .sdiv_checked => {
                if (rs == 0) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "division by zero during `comptime` evaluation",
                        "divisor is `0` here",
                        null,
                    );
                }
                if (ls == min_s and rs == -1) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "signed `MIN / -1` division overflowed during `comptime` evaluation",
                        "signed division overflow here",
                        null,
                    );
                }
                return self.makeIntSlot(res_ty, @bitCast(@divTrunc(ls, rs)));
            },
            .udiv_checked => {
                if (ru == 0) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "division by zero during `comptime` evaluation",
                        "divisor is `0` here",
                        null,
                    );
                }
                return self.makeIntSlot(res_ty, lu / ru);
            },
            .srem_checked => {
                if (rs == 0) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "remainder by zero during `comptime` evaluation",
                        "divisor is `0` here",
                        null,
                    );
                }
                if (ls == min_s and rs == -1) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "signed `MIN % -1` remainder overflowed during `comptime` evaluation",
                        "signed remainder overflow here",
                        null,
                    );
                }
                return self.makeIntSlot(res_ty, @bitCast(@rem(ls, rs)));
            },
            .urem_checked => {
                if (ru == 0) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "remainder by zero during `comptime` evaluation",
                        "divisor is `0` here",
                        null,
                    );
                }
                return self.makeIntSlot(res_ty, lu % ru);
            },
            .shl_checked, .ashr_checked, .lshr_checked => {
                if ((rhs_info.is_signed and rs < 0) or ru >= info.bits) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "bit-shift count is negative or `>=` integer bit width at `comptime`",
                        "invalid shift count here",
                        null,
                    );
                }
                const sh_amt: u7 = @intCast(ru);
                if (kind == .shl_checked) {
                    return self.makeIntSlot(res_ty, lu << sh_amt);
                } else if (kind == .ashr_checked) {
                    return self.makeIntSlot(res_ty, @bitCast(ls >> sh_amt));
                } else {
                    return self.makeIntSlot(res_ty, lu >> sh_amt);
                }
            },
            .add_wrap => return self.makeIntSlot(res_ty, lu +% ru),
            .sub_wrap => return self.makeIntSlot(res_ty, lu -% ru),
            .mul_wrap => return self.makeIntSlot(res_ty, lu *% ru),
            .shl_wrap => {
                const sh_amt: u7 = @intCast(ru & @as(u128, info.bits - 1));
                return self.makeIntSlot(res_ty, lu << sh_amt);
            },
            .ashr_wrap => {
                const sh_amt: u7 = @intCast(ru & @as(u128, info.bits - 1));
                return self.makeIntSlot(res_ty, @bitCast(ls >> sh_amt));
            },
            .lshr_wrap => {
                const sh_amt: u7 = @intCast(ru & @as(u128, info.bits - 1));
                return self.makeIntSlot(res_ty, lu >> sh_amt);
            },
            .sadd_sat => {
                const ov = @addWithOverflow(ls, rs);
                const clamped = if (ov[1] != 0)
                    (if (ls < 0) min_s else max_s)
                else
                    std.math.clamp(ov[0], min_s, max_s);
                return self.makeIntSlot(res_ty, @bitCast(clamped));
            },
            .uadd_sat => {
                const ov = @addWithOverflow(lu, ru);
                const clamped = if (ov[1] != 0 or ov[0] > max_u) max_u else ov[0];
                return self.makeIntSlot(res_ty, clamped);
            },
            .ssub_sat => {
                const ov = @subWithOverflow(ls, rs);
                const clamped = if (ov[1] != 0)
                    (if (ls < 0) min_s else max_s)
                else
                    std.math.clamp(ov[0], min_s, max_s);
                return self.makeIntSlot(res_ty, @bitCast(clamped));
            },
            .usub_sat => {
                return self.makeIntSlot(res_ty, if (lu < ru) 0 else lu - ru);
            },
            .smul_sat => {
                const ov = @mulWithOverflow(ls, rs);
                const is_neg = (ls < 0) != (rs < 0);
                const clamped = if (ov[1] != 0)
                    (if (is_neg) min_s else max_s)
                else
                    std.math.clamp(ov[0], min_s, max_s);
                return self.makeIntSlot(res_ty, @bitCast(clamped));
            },
            .umul_sat => {
                const ov = @mulWithOverflow(lu, ru);
                const clamped = if (ov[1] != 0 or ov[0] > max_u) max_u else ov[0];
                return self.makeIntSlot(res_ty, clamped);
            },
            .bit_and => return self.makeIntSlot(res_ty, lu & ru),
            .bit_or => return self.makeIntSlot(res_ty, lu | ru),
            .bit_xor => return self.makeIntSlot(res_ty, lu ^ ru),
            .eq => return .{ .scalar_u64 = @intFromBool(lu == ru) },
            .ne => return .{ .scalar_u64 = @intFromBool(lu != ru) },
            .slt => return .{ .scalar_u64 = @intFromBool(ls < rs) },
            .ult => return .{ .scalar_u64 = @intFromBool(lu < ru) },
            .sle => return .{ .scalar_u64 = @intFromBool(ls <= rs) },
            .ule => return .{ .scalar_u64 = @intFromBool(lu <= ru) },
            .sgt => return .{ .scalar_u64 = @intFromBool(ls > rs) },
            .ugt => return .{ .scalar_u64 = @intFromBool(lu > ru) },
            .sge => return .{ .scalar_u64 = @intFromBool(ls >= rs) },
            .uge => return .{ .scalar_u64 = @intFromBool(lu >= ru) },
            else => return .{ .scalar_u64 = 0 },
        }
    }

    /// Evaluates a typed unary `UnaryOpKind` instruction (`E0502`, `E0503`, `E0507`).
    fn evalUnaryOp(
        self: *MirVm,
        frame_idx: usize,
        kind: UnaryOpKind,
        src_val: MirValueId,
        rhs_aux: u32,
        res_ty: TypeId,
    ) VmEvalError!RegSlot {
        const body = self.call_stack.items[frame_idx].body;
        const src_slot = self.call_stack.items[frame_idx].regs[src_val.asInt()];
        const src_ty = self.pool.unwrapUnderlyingType(body.getInst(src_val).type_id);
        const dst_ty = self.pool.unwrapUnderlyingType(res_ty);

        switch (kind) {
            .sneg_checked => {
                const info = resolveIntInfo(self.pool, src_ty, self.options.target_layout) orelse
                    return .{ .scalar_u64 = 0 };
                const src_s = signExtendToI128(try self.readIntBitsFromSlot(src_slot, src_ty), info.bits);
                const min_s: i128 = if (info.bits >= 128)
                    std.math.minInt(i128)
                else
                    -(@as(i128, 1) << @intCast(info.bits - 1));
                if (src_s == min_s) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "signed negation of `MIN` overflowed during `comptime` evaluation",
                        "signed negation overflow here",
                        null,
                    );
                }
                return self.makeIntSlot(dst_ty, @bitCast(-src_s));
            },
            .neg_wrap => {
                const src_u = try self.readIntBitsFromSlot(src_slot, src_ty);
                return self.makeIntSlot(dst_ty, 0 -% src_u);
            },
            .fneg => {
                if (src_ty == .f32_ty) return packF32Slot(-unpackF32Slot(src_slot));
                return .{ .scalar_f64 = canonicalizeF64(-src_slot.scalar_f64) };
            },
            .bool_not => {
                return .{ .scalar_u64 = (src_slot.scalar_u64 & 1) ^ 1 };
            },
            .bit_not => {
                const src_u = try self.readIntBitsFromSlot(src_slot, src_ty);
                return self.makeIntSlot(dst_ty, ~src_u);
            },
            .int_sext => {
                const src_info = resolveIntInfo(self.pool, src_ty, self.options.target_layout) orelse
                    return .{ .scalar_u64 = 0 };
                const sext = signExtendToI128(
                    try self.readIntBitsFromSlot(src_slot, src_ty),
                    src_info.bits,
                );
                return self.makeIntSlot(dst_ty, @bitCast(sext));
            },
            .int_zext, .int_trunc => {
                const src_u = try self.readIntBitsFromSlot(src_slot, src_ty);
                return self.makeIntSlot(dst_ty, src_u);
            },
            .int_to_float_signed => {
                const src_info = resolveIntInfo(self.pool, src_ty, self.options.target_layout) orelse
                    return .{ .scalar_f64 = 0.0 };
                const sext = signExtendToI128(
                    try self.readIntBitsFromSlot(src_slot, src_ty),
                    src_info.bits,
                );
                if (dst_ty == .f32_ty) return packF32Slot(@floatFromInt(sext));
                return .{ .scalar_f64 = canonicalizeF64(@floatFromInt(sext)) };
            },
            .int_to_float_unsigned => {
                const src_u = try self.readIntBitsFromSlot(src_slot, src_ty);
                if (dst_ty == .f32_ty) return packF32Slot(@floatFromInt(src_u));
                return .{ .scalar_f64 = canonicalizeF64(@floatFromInt(src_u)) };
            },
            .float_to_int_signed => {
                const flt_v: f64 = if (src_ty == .f32_ty) unpackF32Slot(src_slot) else src_slot.scalar_f64;
                if (std.math.isNan(flt_v) or std.math.isInf(flt_v)) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "cannot convert `NaN` or `Inf` float to integer during `comptime` evaluation",
                        "invalid float-to-int cast here",
                        null,
                    );
                }
                const dst_info = resolveIntInfo(self.pool, dst_ty, self.options.target_layout) orelse
                    return .{ .scalar_u64 = 0 };
                const trunc_v = @trunc(flt_v);
                const min_f: f64 = if (dst_info.bits >= 128)
                    @floatFromInt(std.math.minInt(i128))
                else
                    -@as(f64, @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits - 1)));
                const max_excl_f: f64 = if (dst_info.bits >= 128)
                    170141183460469231731687303715884105728.0
                else
                    @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits - 1));
                if (trunc_v < min_f or trunc_v >= max_excl_f) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "float-to-signed-integer conversion overflowed target range at `comptime`",
                        "out-of-range float-to-int cast here",
                        null,
                    );
                }
                const int_s: i128 = @intFromFloat(trunc_v);
                return self.makeIntSlot(dst_ty, @bitCast(int_s));
            },
            .float_to_int_unsigned => {
                const flt_v: f64 = if (src_ty == .f32_ty) unpackF32Slot(src_slot) else src_slot.scalar_f64;
                if (std.math.isNan(flt_v) or std.math.isInf(flt_v)) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "cannot convert `NaN` or `Inf` float to unsigned integer at `comptime`",
                        "invalid float-to-uint cast here",
                        null,
                    );
                }
                const dst_info = resolveIntInfo(self.pool, dst_ty, self.options.target_layout) orelse
                    return .{ .scalar_u64 = 0 };
                const trunc_v = @trunc(flt_v);
                const max_excl_f: f64 = if (dst_info.bits >= 128)
                    340282366920938463463374607431768211456.0
                else
                    @floatFromInt(@as(u128, 1) << @intCast(dst_info.bits));
                if (trunc_v < 0.0 or trunc_v >= max_excl_f) {
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        "float-to-unsigned-integer conversion overflowed target range at `comptime`",
                        "out-of-range float-to-uint cast here",
                        null,
                    );
                }
                const int_u: u128 = @intFromFloat(trunc_v);
                return self.makeIntSlot(dst_ty, int_u);
            },
            .float_promote => {
                return .{ .scalar_f64 = canonicalizeF64(unpackF32Slot(src_slot)) };
            },
            .float_demote => {
                return packF32Slot(@floatCast(src_slot.scalar_f64));
            },
            .bitcast_op, .ptr_cast => {
                const src_repr = classifyValueRepr(self.pool, self.sym_table, src_ty, self.options.target_layout);
                const dst_repr = classifyValueRepr(self.pool, self.sym_table, dst_ty, self.options.target_layout);
                if (src_repr == .inline_ptr and dst_repr == .inline_ptr) {
                    // Check `&[T; N]` coerced to `&[T]` (materializing a 16B fat-slice snapshot) or thin pointer cast:
                    const src_node = self.pool.getNode(src_ty);
                    const dst_node = self.pool.getNode(dst_ty);
                    if ((src_node.tag == .ref_ty or src_node.tag == .mut_ref_ty or src_node.tag == .raw_ptr_ty) and
                        (dst_node.tag == .ref_ty or dst_node.tag == .mut_ref_ty or dst_node.tag == .raw_ptr_ty))
                    {
                        const src_pointee = self.pool.unwrapUnderlyingType(TypeId.fromInt(src_node.lhs));
                        const dst_pointee = self.pool.unwrapUnderlyingType(TypeId.fromInt(dst_node.lhs));
                        const src_pointee_node = self.pool.getNode(src_pointee);
                        const dst_pointee_tag = self.pool.getNode(dst_pointee).tag;
                        if ((src_pointee_node.tag == .array_ty or src_pointee_node.tag == .soa_array_ty) and
                            (dst_pointee_tag == .slice_ty or dst_pointee_tag == .soa_slice_ty))
                        {
                            const arr_len: u64 = src_pointee_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                            return self.makeFatSliceSlot(dst_pointee, src_slot.sym_ptr, arr_len);
                        }
                    }
                    return src_slot;
                }
                if (src_repr == .inline_ptr and
                    (self.pool.getNode(dst_ty).tag == .slice_ty or self.pool.getNode(dst_ty).tag == .soa_slice_ty))
                {
                    // `&[T; N]` coerced to `[T]` slice:
                    const src_node = self.pool.getNode(src_ty);
                    if (src_node.tag == .ref_ty or src_node.tag == .mut_ref_ty or src_node.tag == .raw_ptr_ty) {
                        const arr_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(src_node.lhs));
                        const arr_node = self.pool.getNode(arr_ty);
                        if (arr_node.tag == .array_ty or arr_node.tag == .soa_array_ty) {
                            const arr_len: u64 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                            return self.makeFatSliceSlot(dst_ty, src_slot.sym_ptr, arr_len);
                        }
                    }
                }
                if (src_repr == .inline_ptr or dst_repr == .inline_ptr) {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "pointer-to-integer and integer-to-pointer casts are forbidden at `comptime`",
                        "forbidden pointer/integer cast here",
                        null,
                    );
                }
                if (src_ty == dst_ty) return src_slot;
                if (kind == .bitcast_op) {
                    if (resolveIntInfo(self.pool, src_ty, self.options.target_layout)) |src_int| {
                        if (resolveIntInfo(self.pool, dst_ty, self.options.target_layout)) |dst_int| {
                            if (src_int.bits == dst_int.bits) {
                                const raw_bits = try self.readIntBitsFromSlot(src_slot, src_ty);
                                return self.makeIntSlot(dst_ty, raw_bits);
                            }
                        }
                    }
                }
                const tmp_place = try self.allocSnapshotForType(src_ty, false);
                try self.storeTypedSlotToMemory(tmp_place, src_ty, src_slot);
                return self.loadTypedSlotFromMemory(tmp_place, dst_ty);
            },
            .ssa_discriminant => {
                const tag_ord = try self.readSumDiscriminantAt(src_slot.sym_ptr, src_ty);
                return self.makeIntSlot(dst_ty, tag_ord);
            },
            .ssa_variant_payload => {
                const sum_info = computeSumTypeTagAndPayloadLayout(
                    self.pool,
                    self.sym_table,
                    src_ty,
                    self.options.target_layout,
                );
                const pay_ptr = try self.advanceSymbolicPtr(src_slot.sym_ptr, sum_info.payload_offset);
                _ = rhs_aux;
                return self.loadTypedSlotFromMemory(pay_ptr, dst_ty);
            },
        }
    }

    /// Evaluates `MirOp.aggregate_make` across tuples, structs, arrays, sum types, strings, and closures.
    fn evalAggregateMake(
        self: *MirVm,
        frame_idx: usize,
        kind: AggregateKind,
        inst: mir.MirInst,
    ) VmEvalError!RegSlot {
        const body = self.call_stack.items[frame_idx].body;
        const agg_ty = self.pool.unwrapUnderlyingType(inst.type_id);

        switch (kind) {
            .tuple_agg, .struct_agg => {
                const is_zero_pad = kind == .struct_agg and
                    mir.isZeroPadNominalType(self.pool, self.sym_table, agg_ty);
                const snap = try self.allocSnapshotForType(agg_ty, is_zero_pad);
                const elem_ids = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                if (self.pool.getNode(agg_ty).tag == .union_ty) {
                    for (elem_ids) |raw_val| {
                        const elem_ty = body.getInst(MirValueId.fromInt(raw_val)).type_id;
                        const elem_slot = self.call_stack.items[frame_idx].regs[raw_val];
                        try self.storeTypedSlotToMemory(snap, elem_ty, elem_slot);
                    }
                } else {
                    const is_packed_agg = isPackedStructType(self.pool, self.sym_table, agg_ty);
                    for (elem_ids, 0..) |raw_val, ord_i| {
                        const f_info = computeCompositeFieldOffsetAndType(
                            self.pool,
                            self.sym_table,
                            agg_ty,
                            @intCast(ord_i),
                            self.options.target_layout,
                        ) orelse continue;
                        const elem_slot = self.call_stack.items[frame_idx].regs[raw_val];
                        try self.storeTypedSlotToMemoryAligned(
                            try self.advanceSymbolicPtr(snap, f_info.byte_offset),
                            f_info.field_ty,
                            elem_slot,
                            is_packed_agg,
                        );
                    }
                }
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
            .array_elems => {
                const snap = try self.allocSnapshotForType(agg_ty, false);
                const arr_node = self.pool.getNode(agg_ty);
                const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                const elem_ids = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                if (arr_node.tag == .soa_array_ty) {
                    const soa_cap: u32 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    for (elem_ids, 0..) |raw_val, elem_i| {
                        try self.storeSoaArrayElementFromSlot(
                            snap,
                            elem_ty,
                            soa_cap,
                            elem_i,
                            self.call_stack.items[frame_idx].regs[raw_val],
                        );
                    }
                } else {
                    const elem_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        elem_ty,
                        self.options.target_layout,
                    );
                    for (elem_ids, 0..) |raw_val, elem_i| {
                        const elem_slot = self.call_stack.items[frame_idx].regs[raw_val];
                        const off = try self.mulOffsetChecked(elem_i, elem_lay.byte_size);
                        try self.storeTypedSlotToMemory(
                            try self.advanceSymbolicPtr(snap, off),
                            elem_ty,
                            elem_slot,
                        );
                    }
                }
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
            .array_repeat => {
                const snap = try self.allocSnapshotForType(agg_ty, false);
                const arr_node = self.pool.getNode(agg_ty);
                const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(arr_node.lhs));
                const elem_slot = self.call_stack.items[frame_idx].regs[inst.operands.lhs];
                const repeat_count = inst.operands.rhs;
                if (arr_node.tag == .soa_array_ty) {
                    const soa_cap: u32 = arr_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    for (0..repeat_count) |elem_i| {
                        try self.tickStepBudget();
                        try self.storeSoaArrayElementFromSlot(snap, elem_ty, soa_cap, elem_i, elem_slot);
                    }
                } else {
                    const elem_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        elem_ty,
                        self.options.target_layout,
                    );
                    for (0..repeat_count) |elem_i| {
                        try self.tickStepBudget();
                        const off = try self.mulOffsetChecked(elem_i, elem_lay.byte_size);
                        try self.storeTypedSlotToMemory(
                            try self.advanceSymbolicPtr(snap, off),
                            elem_ty,
                            elem_slot,
                        );
                    }
                }
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
            .tagged_variant => {
                const is_zero_pad = mir.isZeroPadNominalType(self.pool, self.sym_table, agg_ty);
                const snap = try self.allocSnapshotForType(agg_ty, is_zero_pad);
                const tag_ord: u32 = inst.operands.rhs >> 16;
                const elem_len: u32 = inst.operands.rhs & 0xFFFF;
                const sum_info = computeSumTypeTagAndPayloadLayout(
                    self.pool,
                    self.sym_table,
                    agg_ty,
                    self.options.target_layout,
                );
                if (elem_len == 1) {
                    const raw_val = body.extra_args.items[inst.operands.lhs];
                    const pay_ty = body.getInst(MirValueId.fromInt(raw_val)).type_id;
                    try self.storeTypedSlotToMemory(
                        try self.advanceSymbolicPtr(snap, sum_info.payload_offset),
                        pay_ty,
                        self.call_stack.items[frame_idx].regs[raw_val],
                    );
                } else if (elem_len > 1) {
                    const var_pay_ty = resolveVariantPayloadType(self.pool, self.sym_table, agg_ty, tag_ord);
                    for (0..elem_len) |sub_i| {
                        const raw_val = body.extra_args.items[inst.operands.lhs + sub_i];
                        const sub_ty = body.getInst(MirValueId.fromInt(raw_val)).type_id;
                        const sub_off: u64 = if (computeCompositeFieldOffsetAndType(
                            self.pool,
                            self.sym_table,
                            var_pay_ty,
                            @intCast(sub_i),
                            self.options.target_layout,
                        )) |fi| fi.byte_offset else 0;
                        const pay_base = try self.advanceSymbolicPtr(snap, sum_info.payload_offset);
                        try self.storeTypedSlotToMemory(
                            try self.advanceSymbolicPtr(pay_base, sub_off),
                            sub_ty,
                            self.call_stack.items[frame_idx].regs[raw_val],
                        );
                    }
                }
                try self.writeSumDiscriminantAt(snap, agg_ty, tag_ord);
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
            .str_concat => {
                var builder: std.ArrayListUnmanaged(u8) = .empty;
                defer builder.deinit(self.allocator);
                const part_ids = body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs];
                for (part_ids) |part_raw| {
                    const part_ty = self.pool.unwrapUnderlyingType(
                        body.getInst(MirValueId.fromInt(part_raw)).type_id,
                    );
                    const part_slot = self.call_stack.items[frame_idx].regs[part_raw];
                    try self.appendFormattedValue(&builder, part_ty, part_slot);
                }
                const sym_id = self.interner.intern(builder.items) catch return error.OutOfMemory;
                return self.makeFatSliceSlot(
                    agg_ty,
                    .{ .alloc_id = ComptimeAllocId.fromStringId(sym_id), .byte_offset = 0 },
                    builder.items.len,
                );
            },
            .closure_make => {
                const snap = try self.allocSnapshotForType(agg_ty, true);
                const fn_idx = try self.resolveOrLoadCallable(DefId.fromInt(inst.operands.lhs), .none);
                try self.writePointerAt(
                    snap,
                    self.options.target_layout.ptr_align_log2,
                    .{ .alloc_id = ComptimeAllocId.fromFnIndex(fn_idx), .byte_offset = 0 },
                );
                const cap_len = body.extra_args.items[inst.operands.rhs];
                const cap_start = inst.operands.rhs + 1;
                if (cap_len > 0) {
                    var env_size: u64 = 0;
                    var env_align_log2: u8 = self.options.target_layout.ptr_align_log2;
                    for (0..cap_len) |cap_i| {
                        const cap_val = MirValueId.fromInt(body.extra_args.items[cap_start + cap_i]);
                        const cap_ty = body.getInst(cap_val).type_id;
                        const cap_lay = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            cap_ty,
                            self.options.target_layout,
                        );
                        if (cap_lay.byte_size == 0) continue;
                        env_align_log2 = @max(env_align_log2, cap_lay.align_log2);
                        env_size = std.mem.alignForward(u64, env_size, @max(@as(u64, cap_lay.align_bytes), 1));
                        env_size += cap_lay.byte_size;
                    }
                    const env_alloc_id = try self.allocMemory(
                        @max(env_size, 1),
                        env_align_log2,
                        true,
                        false,
                        true,
                        0,
                        self.active_inst_span,
                    );
                    const cap_env_ptr = SymbolicPtr{ .alloc_id = env_alloc_id, .byte_offset = 0 };
                    var cur_off: u64 = 0;
                    for (0..cap_len) |cap_i| {
                        const cap_val = MirValueId.fromInt(body.extra_args.items[cap_start + cap_i]);
                        const cap_ty = body.getInst(cap_val).type_id;
                        const cap_lay = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            cap_ty,
                            self.options.target_layout,
                        );
                        if (cap_lay.byte_size == 0) continue;
                        cur_off = std.mem.alignForward(u64, cur_off, @max(@as(u64, cap_lay.align_bytes), 1));
                        try self.storeTypedSlotToMemory(
                            try self.advanceSymbolicPtr(cap_env_ptr, cur_off),
                            cap_ty,
                            self.call_stack.items[frame_idx].regs[cap_val.asInt()],
                        );
                        cur_off += cap_lay.byte_size;
                    }
                    self.sealSnapshot(cap_env_ptr);
                    try self.writePointerAt(
                        try self.advanceSymbolicPtr(snap, self.options.target_layout.ptr_byte_size),
                        self.options.target_layout.ptr_align_log2,
                        cap_env_ptr,
                    );
                }
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
        }
    }

    /// Evaluates `MirOp.aggregate_extract` at `ordinal` from an SSA aggregate snapshot.
    fn evalAggregateExtract(
        self: *MirVm,
        agg_slot: RegSlot,
        raw_agg_ty: TypeId,
        ordinal: u32,
        res_ty: TypeId,
    ) VmEvalError!RegSlot {
        const agg_ty = self.pool.unwrapUnderlyingType(raw_agg_ty);
        const node = self.pool.getNode(agg_ty);
        var byte_off: u64 = 0;
        if (node.tag == .array_ty) {
            const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const elem_lay = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                elem_ty,
                self.options.target_layout,
            );
            byte_off = try self.mulOffsetChecked(ordinal, elem_lay.byte_size);
        } else if (computeCompositeFieldOffsetAndType(
            self.pool,
            self.sym_table,
            agg_ty,
            ordinal,
            self.options.target_layout,
        )) |f_info| {
            byte_off = f_info.byte_offset;
        }
        return self.loadTypedSlotFromMemoryAligned(
            try self.advanceSymbolicPtr(agg_slot.sym_ptr, byte_off),
            res_ty,
            isPackedStructType(self.pool, self.sym_table, agg_ty),
        );
    }

    /// Evaluates functional `MirOp.aggregate_insert` producing a new sealed aggregate snapshot.
    fn evalAggregateInsert(
        self: *MirVm,
        agg_slot: RegSlot,
        raw_agg_ty: TypeId,
        ordinal: u32,
        new_elem_slot: RegSlot,
    ) VmEvalError!RegSlot {
        const agg_ty = self.pool.unwrapUnderlyingType(raw_agg_ty);
        const agg_lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            agg_ty,
            self.options.target_layout,
        );
        const is_zero_pad = mir.isZeroPadNominalType(self.pool, self.sym_table, agg_ty);
        const snap = try self.allocSnapshotForType(agg_ty, is_zero_pad);
        try self.copyMemoryRange(snap, agg_slot.sym_ptr, agg_lay.byte_size, agg_lay.align_log2);

        const node = self.pool.getNode(agg_ty);
        if (node.tag == .array_ty) {
            const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(node.lhs));
            const elem_lay = type_system.computeTypeLayoutWithPool(
                self.pool,
                self.sym_table,
                elem_ty,
                self.options.target_layout,
            );
            const off = try self.mulOffsetChecked(ordinal, elem_lay.byte_size);
            try self.storeTypedSlotToMemory(
                try self.advanceSymbolicPtr(snap, off),
                elem_ty,
                new_elem_slot,
            );
        } else if (computeCompositeFieldOffsetAndType(
            self.pool,
            self.sym_table,
            agg_ty,
            ordinal,
            self.options.target_layout,
        )) |f_info| {
            try self.storeTypedSlotToMemoryAligned(
                try self.advanceSymbolicPtr(snap, f_info.byte_offset),
                f_info.field_ty,
                new_elem_slot,
                isPackedStructType(self.pool, self.sym_table, agg_ty),
            );
        }
        self.sealSnapshot(snap);
        return .{ .sym_ptr = snap };
    }

    /// Looks up a registered `Drop::drop` / `AutoDrop::drop` callable index for unwrapped nominal `ty`.
    fn lookupDropCallableForType(self: *MirVm, ty: TypeId) VmEvalError!?u32 {
        const ty_node = self.pool.getNode(ty);
        if (ty_node.tag == .struct_ty or ty_node.tag == .enum_ty or ty_node.tag == .union_ty) {
            const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                const nom_sym = self.sym_table.getSymbol(sym_idx).*;
                if (!nom_sym.target_scope.isNone()) {
                    for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind == .fn_sym and std.mem.eql(u8, mem_sym.name_text, "drop")) {
                            if (try self.tryResolveOrLoadCallable(mem_sym.def_id, mem_idx)) |found_idx| {
                                return found_idx;
                            }
                        }
                    }
                }
            }
        }
        for (self.callables.items, 0..) |entry, callable_i| {
            if (entry.is_extern) continue;
            const cand_body = entry.body orelse continue;
            if (cand_body.param_count != 1 or cand_body.locals.items.len < 2) continue;
            const fn_name = self.interner.get(cand_body.name);
            if (!std.mem.eql(u8, fn_name, "drop") and
                !std.mem.endsWith(u8, fn_name, "::drop") and
                !std.mem.endsWith(u8, fn_name, ".drop")) continue;
            const raw_param_ty = self.pool.unwrapUnderlyingType(cand_body.locals.items[1].type_id);
            const param_node = self.pool.getNode(raw_param_ty);
            const self_ty = if (param_node.tag == .ref_ty or
                param_node.tag == .mut_ref_ty or
                param_node.tag == .raw_ptr_ty)
                self.pool.unwrapUnderlyingType(TypeId.fromInt(param_node.lhs))
            else
                raw_param_ty;
            if (self_ty == ty) return @intCast(callable_i);
        }
        return null;
    }

    /// Releases any `is_heap_alloc` virtual container buffers referenced inside `place_ptr[0..sizeof(container_ty))`.
    fn freeContainerHeapBuffersAt(
        self: *MirVm,
        place_ptr: SymbolicPtr,
        container_ty: TypeId,
    ) VmEvalError!void {
        _ = try self.validateAccess(place_ptr, 0, 0, false);
        if (place_ptr.alloc_id.domain() != .vm_alloc) return;
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            container_ty,
            self.options.target_layout,
        );
        const end_off: u64 = @as(u64, place_ptr.byte_offset) + lay.byte_size;
        var heap_handles: [4]ComptimeAllocId = undefined;
        var handle_len: usize = 0;
        var overflow_handles: std.ArrayListUnmanaged(ComptimeAllocId) = .empty;
        defer overflow_handles.deinit(self.allocator);

        const alloc_rec = &self.allocations.items[place_ptr.alloc_id.payloadIndex()];
        for (alloc_rec.provenance.items) |prov| {
            if (prov.byte_offset < place_ptr.byte_offset or @as(u64, prov.byte_offset) >= end_off) continue;
            if (prov.alloc_id.domain() != .vm_alloc) continue;
            const target_idx = prov.alloc_id.payloadIndex();
            if (target_idx == 0 or target_idx >= self.allocations.items.len) continue;
            if (!self.allocations.items[target_idx].is_heap_alloc) continue;
            if (overflow_handles.items.len == 0 and handle_len < heap_handles.len) {
                heap_handles[handle_len] = prov.alloc_id;
                handle_len += 1;
            } else {
                if (overflow_handles.items.len == 0 and handle_len > 0) {
                    overflow_handles.appendSlice(self.allocator, heap_handles[0..handle_len]) catch
                        return error.OutOfMemory;
                }
                overflow_handles.append(self.allocator, prov.alloc_id) catch return error.OutOfMemory;
            }
        }

        const to_free = if (overflow_handles.items.len > 0)
            overflow_handles.items
        else
            heap_handles[0..handle_len];
        for (to_free) |heap_aid| {
            try self.freeHeapMemory(.{ .alloc_id = heap_aid, .byte_offset = 0 });
        }
    }

    /// Recursively executes `Drop::drop` / `AutoDrop::drop`, reverse-order field drops, and container buffer frees.
    fn dropPlaceInVm(self: *MirVm, place_ptr: SymbolicPtr, raw_ty: TypeId) VmEvalError!void {
        try self.tickStepBudget();
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        if (ty.isError() or ty == .unit_ty or ty == .never_ty or ty.isPrimitive()) return;

        // [1] Invoke explicit user `Drop::drop` / `AutoDrop::drop` on outer nominal value first:
        if (try self.lookupDropCallableForType(ty)) |drop_fn_idx| {
            if (self.callables.items[drop_fn_idx].body) |drop_body| {
                const param_decl = drop_body.locals.items[1];
                if (param_decl.mode() == .inout_mode or param_decl.mode() == .set_mode) {
                    _ = try self.invokeBodyInternal(
                        drop_body,
                        &.{},
                        &[1]SymbolicPtr{place_ptr},
                        self.active_inst_span,
                    );
                } else if (classifyValueRepr(
                    self.pool,
                    self.sym_table,
                    param_decl.type_id,
                    self.options.target_layout,
                ) == .inline_ptr) {
                    _ = try self.invokeBodyInternal(
                        drop_body,
                        &[1]RegSlot{.{ .sym_ptr = place_ptr }},
                        &.{},
                        self.active_inst_span,
                    );
                } else {
                    const self_slot = try self.loadTypedSlotFromMemory(place_ptr, param_decl.type_id);
                    _ = try self.invokeBodyInternal(
                        drop_body,
                        &[1]RegSlot{self_slot},
                        &.{},
                        self.active_inst_span,
                    );
                }
            }
        }

        // [2] Release backing virtual heap allocations for built-in `AutoDrop` containers (`Vec`, `String`, etc.):
        const ty_node = self.pool.getNode(ty);
        if (ty_node.tag == .struct_ty) {
            const sym_idx = SymbolIndex.fromInt(ty_node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                const nom_sym = self.sym_table.getSymbol(sym_idx).*;
                if (nom_sym.flags.is_builtin and type_system.AUTO_DROP_CONTAINER_MAP.has(nom_sym.name_text)) {
                    try self.freeContainerHeapBuffersAt(place_ptr, ty);
                }
            }
        }

        // [3] Recursively drop constituent fields, elements, or active variant payloads in reverse order:
        switch (ty_node.tag) {
            .struct_ty, .tuple_ty => {
                var field_count: u32 = 0;
                while (computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    ty,
                    field_count,
                    self.options.target_layout,
                ) != null) : (field_count += 1) {}
                var rev_i: u32 = field_count;
                while (rev_i > 0) {
                    rev_i -= 1;
                    const field_info = computeCompositeFieldOffsetAndType(
                        self.pool,
                        self.sym_table,
                        ty,
                        rev_i,
                        self.options.target_layout,
                    ).?;
                    try self.dropPlaceInVm(
                        try self.advanceSymbolicPtr(place_ptr, field_info.byte_offset),
                        field_info.field_ty,
                    );
                }
            },
            .array_ty => {
                const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                if (!elem_ty.isPrimitive()) {
                    const arr_len: u32 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                    const elem_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        elem_ty,
                        self.options.target_layout,
                    );
                    var rev_i: u32 = arr_len;
                    while (rev_i > 0) {
                        rev_i -= 1;
                        const off = try self.mulOffsetChecked(rev_i, elem_lay.byte_size);
                        try self.dropPlaceInVm(try self.advanceSymbolicPtr(place_ptr, off), elem_ty);
                    }
                }
            },
            .soa_array_ty => {
                const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                const soa_cap: u32 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                var col_count: u32 = 0;
                while (computeSoaColumnOffsetAndType(
                    self.pool,
                    self.sym_table,
                    elem_struct_ty,
                    col_count,
                    soa_cap,
                    self.options.target_layout,
                ) != null) : (col_count += 1) {}
                var rev_elem: u32 = soa_cap;
                while (rev_elem > 0) {
                    rev_elem -= 1;
                    var rev_col: u32 = col_count;
                    while (rev_col > 0) {
                        rev_col -= 1;
                        const col_info = computeSoaColumnOffsetAndType(
                            self.pool,
                            self.sym_table,
                            elem_struct_ty,
                            rev_col,
                            soa_cap,
                            self.options.target_layout,
                        ).?;
                        if (col_info.field_ty.isPrimitive()) continue;
                        const field_lay = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            col_info.field_ty,
                            self.options.target_layout,
                        );
                        const col_ptr = try self.advanceSymbolicPtr(place_ptr, col_info.column_byte_offset);
                        const elem_off = try self.mulOffsetChecked(rev_elem, field_lay.byte_size);
                        try self.dropPlaceInVm(
                            try self.advanceSymbolicPtr(col_ptr, elem_off),
                            col_info.field_ty,
                        );
                    }
                }
            },
            .enum_ty, .optional_ty, .result_ty => {
                const sum_info = computeSumTypeTagAndPayloadLayout(
                    self.pool,
                    self.sym_table,
                    ty,
                    self.options.target_layout,
                );
                const tag_ord = try self.readSumDiscriminantAt(place_ptr, ty);
                const var_pay_ty = resolveVariantPayloadType(self.pool, self.sym_table, ty, tag_ord);
                if (var_pay_ty != .unit_ty and !var_pay_ty.isError()) {
                    try self.dropPlaceInVm(
                        try self.advanceSymbolicPtr(place_ptr, sum_info.payload_offset),
                        var_pay_ty,
                    );
                }
            },
            else => {},
        }
    }

    /// Evaluates `.narrow_check` / `.try_narrow` bounds against `dst_ty`, returning `(is_in_range, converted_bits)`.
    fn checkNarrowConversion(
        self: *MirVm,
        frame_idx: usize,
        args: []const u32,
        dst_ty: TypeId,
    ) VmEvalError!struct { is_in_range: bool, converted_bits: u128 } {
        if (args.len < 3) return .{ .is_in_range = false, .converted_bits = 0 };
        const body = self.call_stack.items[frame_idx].body;
        const src_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
        const min_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
        const max_ty = body.getInst(MirValueId.fromInt(args[2])).type_id;

        const src_bits = try self.readIntBitsFromSlot(self.call_stack.items[frame_idx].regs[args[0]], src_ty);
        const min_bits = try self.readIntBitsFromSlot(self.call_stack.items[frame_idx].regs[args[1]], min_ty);
        const max_bits = try self.readIntBitsFromSlot(self.call_stack.items[frame_idx].regs[args[2]], max_ty);
        const min_i128: i128 = @bitCast(min_bits);
        const max_i128: i128 = @bitCast(max_bits);

        const src_info = resolveIntInfo(self.pool, src_ty, self.options.target_layout) orelse
            return .{ .is_in_range = false, .converted_bits = 0 };
        const is_unrefined_u128_dst = self.pool.unwrapUnderlyingType(dst_ty) == .u128_ty and
            self.pool.getRefinementBounds(dst_ty) == null;

        if (src_info.is_signed) {
            const src_s = signExtendToI128(src_bits, src_info.bits);
            const is_ok = if (is_unrefined_u128_dst)
                src_s >= 0
            else
                (src_s >= min_i128 and src_s <= max_i128);
            return .{ .is_in_range = is_ok, .converted_bits = @bitCast(src_s) };
        }
        if (is_unrefined_u128_dst) {
            return .{ .is_in_range = true, .converted_bits = src_bits };
        }
        if (max_i128 < 0) {
            return .{ .is_in_range = false, .converted_bits = src_bits };
        }
        const min_u128: u128 = if (min_i128 <= 0) 0 else @intCast(min_i128);
        const max_u128: u128 = @intCast(max_i128);
        return .{
            .is_in_range = src_bits >= min_u128 and src_bits <= max_u128,
            .converted_bits = src_bits,
        };
    }

    /// Extracts `(data_ptr, byte_len)` from a `[u8]`, `&[u8]`, `[u8; N]`, or `&[u8; N]` `RegSlot`.
    fn extractWireBytesSpan(
        self: *MirVm,
        raw_arg_ty: TypeId,
        arg_slot: RegSlot,
    ) VmEvalError!struct { data_ptr: SymbolicPtr, byte_len: u64 } {
        const arg_ty = self.pool.unwrapUnderlyingType(raw_arg_ty);
        if (arg_ty == .str_ty) {
            const fat = try self.readFatSliceParts(arg_slot.sym_ptr);
            return .{ .data_ptr = fat.data_ptr, .byte_len = fat.elem_len };
        }
        const arg_node = self.pool.getNode(arg_ty);
        if (arg_node.tag == .slice_ty) {
            const fat = try self.readFatSliceParts(arg_slot.sym_ptr);
            return .{ .data_ptr = fat.data_ptr, .byte_len = fat.elem_len };
        }
        if (arg_node.tag == .array_ty) {
            return .{
                .data_ptr = arg_slot.sym_ptr,
                .byte_len = arg_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG,
            };
        }
        if (arg_node.tag == .ref_ty or arg_node.tag == .mut_ref_ty or arg_node.tag == .raw_ptr_ty) {
            const pointee_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(arg_node.lhs));
            if (pointee_ty == .str_ty) {
                const fat = try self.readFatSliceParts(arg_slot.sym_ptr);
                return .{ .data_ptr = fat.data_ptr, .byte_len = fat.elem_len };
            }
            const pointee_node = self.pool.getNode(pointee_ty);
            if (pointee_node.tag == .slice_ty) {
                const fat = try self.readFatSliceParts(arg_slot.sym_ptr);
                return .{ .data_ptr = fat.data_ptr, .byte_len = fat.elem_len };
            }
            if (pointee_node.tag == .array_ty) {
                return .{
                    .data_ptr = arg_slot.sym_ptr,
                    .byte_len = pointee_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG,
                };
            }
        }
        return .{ .data_ptr = SymbolicPtr.NULL, .byte_len = 0 };
    }

    /// Returns `true` if `ptr` satisfies both offset alignment and backing virtual alignment `req_align_log2`.
    fn isSymbolicPtrAlignedForView(self: *const MirVm, ptr: SymbolicPtr, req_align_log2: u8) bool {
        if (ptr.alloc_id.isNullOrNone() or ptr.alloc_id.isFnAddr()) return false;
        const req_align_bytes: u64 = @as(u64, 1) << @intCast(@min(req_align_log2, 30));
        if ((@as(u64, ptr.byte_offset) & (req_align_bytes - 1)) != 0) return false;
        return switch (ptr.alloc_id.domain()) {
            .vm_alloc => blk: {
                const idx = ptr.alloc_id.payloadIndex();
                if (idx == 0 or idx >= self.allocations.items.len) break :blk false;
                const rec = &self.allocations.items[idx];
                break :blk rec.is_live and rec.align_log2 >= req_align_log2;
            },
            .rodata_blob => blk: {
                const blob = self.rodata_pool.getBlob(ptr.alloc_id.payloadIndex()) orelse break :blk false;
                break :blk blob.align_log2 >= req_align_log2;
            },
            .string_lit => req_align_log2 == 0,
            .fn_or_none => false,
        };
    }

    /// Evaluates `MirOp.intrinsic_op` across Phase 5 and Phase 6 surface and `MIR`-internal intrinsics.
    fn evalIntrinsicOp(
        self: *MirVm,
        frame_idx: usize,
        kind: MirIntrinsicKind,
        inst: mir.MirInst,
    ) VmEvalError!RegSlot {
        const body = self.call_stack.items[frame_idx].body;
        const args: []const u32 = if (kind.hasExtraArgs() and inst.operands.rhs > 0)
            body.extra_args.items[inst.operands.lhs .. inst.operands.lhs + inst.operands.rhs]
        else
            &.{};

        switch (kind) {
            .compile_assert => {
                // `MirLowerer` emits `.compile_assert` inside `fail_bb` (or standalone with `[cond, msg?]`):
                if (args.len >= 1) {
                    const cond_slot = self.call_stack.items[frame_idx].regs[args[0]];
                    if ((cond_slot.scalar_u64 & 1) != 0) return .{ .scalar_u64 = 0 };
                }
                if (args.len >= 2) {
                    const msg_bytes = try self.readStrSlotBytes(self.call_stack.items[frame_idx].regs[args[1]]);
                    defer self.allocator.free(msg_bytes);
                    const owned_msg = if (self.diagnostic_sink) |sink|
                        (sink.arena.dupe(u8, msg_bytes) catch "@compile_assert failed")
                    else
                        "@compile_assert failed";
                    return self.failWithTrap(
                        error.CompileAssertionFailed,
                        .e0510_compile_assertion_failed,
                        owned_msg,
                        "`@compile_assert` failed here",
                        null,
                    );
                }
                return self.failWithTrap(
                    error.CompileAssertionFailed,
                    .e0510_compile_assertion_failed,
                    "`@compile_assert` failed during `comptime` evaluation",
                    "`@compile_assert` failed here",
                    null,
                );
            },
            .compile_error => {
                if (args.len >= 1) {
                    const msg_bytes = try self.readStrSlotBytes(self.call_stack.items[frame_idx].regs[args[0]]);
                    defer self.allocator.free(msg_bytes);
                    const owned_msg = if (self.diagnostic_sink) |sink|
                        (sink.arena.dupe(u8, msg_bytes) catch "@compile_error triggered")
                    else
                        "@compile_error triggered";
                    return self.failWithTrap(
                        error.CompileAssertionFailed,
                        .e0510_compile_assertion_failed,
                        owned_msg,
                        "`@compile_error` triggered here",
                        null,
                    );
                }
                return self.failWithTrap(
                    error.CompileAssertionFailed,
                    .e0510_compile_assertion_failed,
                    "`@compile_error` triggered during `comptime` evaluation",
                    "`@compile_error` triggered here",
                    null,
                );
            },
            .embed_bytes => {
                if (args.len == 0) {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "`@embed_bytes` requires a relative workspace path argument",
                        "missing `@embed_bytes` path",
                        null,
                    );
                }
                const path_bytes = try self.readStrSlotBytes(self.call_stack.items[frame_idx].regs[args[0]]);
                defer self.allocator.free(path_bytes);
                return self.evalEmbedBytesSlot(path_bytes, inst.type_id);
            },
            .derive_debug_fmt => {
                var builder: std.ArrayListUnmanaged(u8) = .empty;
                defer builder.deinit(self.allocator);
                if (args.len >= 1) {
                    const arg_ty = self.pool.unwrapUnderlyingType(
                        body.getInst(MirValueId.fromInt(args[0])).type_id,
                    );
                    try self.appendFormattedValue(
                        &builder,
                        arg_ty,
                        self.call_stack.items[frame_idx].regs[args[0]],
                    );
                }
                const sym_id = self.interner.intern(builder.items) catch return error.OutOfMemory;
                return self.makeFatSliceSlot(
                    inst.type_id,
                    .{ .alloc_id = ComptimeAllocId.fromStringId(sym_id), .byte_offset = 0 },
                    builder.items.len,
                );
            },
            .size_of => {
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    TypeId.fromInt(inst.operands.lhs),
                    self.options.target_layout,
                );
                return .{ .scalar_u64 = lay.byte_size };
            },
            .align_of => {
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    TypeId.fromInt(inst.operands.lhs),
                    self.options.target_layout,
                );
                return .{ .scalar_u64 = lay.align_bytes };
            },
            .type_name => {
                const rendered = formatCanonicalTypeName(
                    self.allocator,
                    self.pool,
                    self.sym_table,
                    TypeId.fromInt(inst.operands.lhs),
                ) catch return error.OutOfMemory;
                defer self.allocator.free(rendered);
                const sym_id = self.interner.intern(rendered) catch return error.OutOfMemory;
                return self.makeFatSliceSlot(
                    inst.type_id,
                    .{ .alloc_id = ComptimeAllocId.fromStringId(sym_id), .byte_offset = 0 },
                    rendered.len,
                );
            },
            .as_bytes => {
                if (args.len < 1) return .{ .scalar_u64 = 0 };
                const ref_val = MirValueId.fromInt(args[0]);
                const ref_ty = self.pool.unwrapUnderlyingType(body.getInst(ref_val).type_id);
                const ref_node = self.pool.getNode(ref_ty);
                const val_ty = if (ref_node.tag == .ref_ty or
                    ref_node.tag == .mut_ref_ty or
                    ref_node.tag == .raw_ptr_ty)
                    self.pool.unwrapUnderlyingType(TypeId.fromInt(ref_node.lhs))
                else
                    ref_ty;
                const data_ptr = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                const val_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    val_ty,
                    self.options.target_layout,
                );
                if (val_lay.byte_size > self.options.mem_limit) {
                    return self.failWithTrap(
                        error.ResourceLimitExceeded,
                        .e0508_comptime_resource_limit_exceeded,
                        "`@as_bytes` target exceeds `comptime` memory budget",
                        "oversized `@as_bytes` target",
                        null,
                    );
                }
                const byte_len: usize = @intCast(val_lay.byte_size);
                var stack_buf: [64]u8 = undefined;
                var heap_buf: ?[]u8 = null;
                defer if (heap_buf) |buf| self.allocator.free(buf);
                const check_buf: []u8 = if (byte_len <= stack_buf.len)
                    stack_buf[0..byte_len]
                else blk: {
                    const allocated = self.allocator.alloc(u8, byte_len) catch return error.OutOfMemory;
                    heap_buf = allocated;
                    break :blk allocated;
                };
                try self.readScalarBytes(data_ptr, 0, check_buf);

                const res_unwrapped = self.pool.unwrapUnderlyingType(inst.type_id);
                const res_node = self.pool.getNode(res_unwrapped);
                if (res_node.tag == .ref_ty or res_node.tag == .mut_ref_ty or res_node.tag == .raw_ptr_ty) {
                    const pointee_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(res_node.lhs));
                    if (self.pool.getNode(pointee_ty).tag == .slice_ty) {
                        return self.makeFatSliceSlot(pointee_ty, data_ptr, val_lay.byte_size);
                    }
                    return .{ .sym_ptr = data_ptr };
                }
                return self.makeFatSliceSlot(res_unwrapped, data_ptr, val_lay.byte_size);
            },
            .bit_cast => {
                if (args.len < 1) return .{ .scalar_u64 = 0 };
                const src_val = MirValueId.fromInt(args[0]);
                const src_ty = self.pool.unwrapUnderlyingType(body.getInst(src_val).type_id);
                const dst_ty = self.pool.unwrapUnderlyingType(inst.type_id);
                const src_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    src_ty,
                    self.options.target_layout,
                );
                const dst_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    dst_ty,
                    self.options.target_layout,
                );
                if (src_lay.byte_size != dst_lay.byte_size) {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "`@bit_cast` source and destination byte sizes must match",
                        "mismatched `@bit_cast` sizes here",
                        null,
                    );
                }
                const src_snap = try self.allocSnapshotForType(
                    src_ty,
                    mir.isZeroPadNominalType(self.pool, self.sym_table, src_ty),
                );
                try self.storeTypedSlotToMemory(
                    src_snap,
                    src_ty,
                    self.call_stack.items[frame_idx].regs[args[0]],
                );
                const byte_len: usize = @intCast(src_lay.byte_size);
                var stack_buf: [64]u8 = undefined;
                var heap_buf: ?[]u8 = null;
                defer if (heap_buf) |buf| self.allocator.free(buf);
                const raw_buf: []u8 = if (byte_len <= stack_buf.len)
                    stack_buf[0..byte_len]
                else blk: {
                    const allocated = self.allocator.alloc(u8, byte_len) catch return error.OutOfMemory;
                    heap_buf = allocated;
                    break :blk allocated;
                };
                try self.readScalarBytes(src_snap, 0, raw_buf);

                const dst_snap = try self.allocSnapshotForType(dst_ty, true);
                try self.writeScalarBytes(dst_snap, 0, raw_buf);
                self.sealSnapshot(dst_snap);
                return self.loadTypedSlotFromMemory(dst_snap, inst.type_id);
            },
            .from_bytes, .view_bytes => {
                if (args.len < 1) return .{ .scalar_u64 = 0 };
                const is_view = kind == .view_bytes;
                const bytes_val = MirValueId.fromInt(args[0]);
                const span_info = try self.extractWireBytesSpan(
                    body.getInst(bytes_val).type_id,
                    self.call_stack.items[frame_idx].regs[args[0]],
                );
                const opt_ty = self.pool.unwrapUnderlyingType(inst.type_id);
                const opt_node = self.pool.getNode(opt_ty);
                const some_pay_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(opt_node.lhs));
                const some_node = self.pool.getNode(some_pay_ty);
                const target_ty = if (is_view and
                    (some_node.tag == .ref_ty or
                        some_node.tag == .mut_ref_ty or
                        some_node.tag == .raw_ptr_ty))
                    self.pool.unwrapUnderlyingType(TypeId.fromInt(some_node.lhs))
                else
                    some_pay_ty;
                const target_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    target_ty,
                    self.options.target_layout,
                );
                const opt_snap = try self.allocSnapshotForType(opt_ty, false);
                const sum_info = computeSumTypeTagAndPayloadLayout(
                    self.pool,
                    self.sym_table,
                    opt_ty,
                    self.options.target_layout,
                );

                const is_size_ok = span_info.byte_len == target_lay.byte_size;
                const is_align_ok = !is_view or
                    self.isSymbolicPtrAlignedForView(span_info.data_ptr, target_lay.align_log2);
                if (!is_size_ok or !is_align_ok) {
                    try self.writeSumDiscriminantAt(opt_snap, opt_ty, 0);
                    self.sealSnapshot(opt_snap);
                    return .{ .sym_ptr = opt_snap };
                }

                const byte_len: usize = @intCast(target_lay.byte_size);
                var stack_buf: [64]u8 = undefined;
                var heap_buf: ?[]u8 = null;
                defer if (heap_buf) |buf| self.allocator.free(buf);
                const raw_buf: []u8 = if (byte_len <= stack_buf.len)
                    stack_buf[0..byte_len]
                else blk: {
                    const allocated = self.allocator.alloc(u8, byte_len) catch return error.OutOfMemory;
                    heap_buf = allocated;
                    break :blk allocated;
                };
                try self.readScalarBytes(span_info.data_ptr, 0, raw_buf);

                const pay_ptr = try self.advanceSymbolicPtr(opt_snap, sum_info.payload_offset);
                if (is_view) {
                    try self.writePointerAt(
                        pay_ptr,
                        self.options.target_layout.ptr_align_log2,
                        span_info.data_ptr,
                    );
                } else {
                    const val_tmp = try self.allocSnapshotForType(target_ty, true);
                    try self.writeScalarBytes(val_tmp, 0, raw_buf);
                    self.sealSnapshot(val_tmp);
                    const val_slot = try self.loadTypedSlotFromMemory(val_tmp, target_ty);
                    try self.storeTypedSlotToMemory(pay_ptr, some_pay_ty, val_slot);
                }
                try self.writeSumDiscriminantAt(opt_snap, opt_ty, 1);
                self.sealSnapshot(opt_snap);
                return .{ .sym_ptr = opt_snap };
            },
            .drop_trace => {
                if (args.len >= 1) {
                    const id_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                    const bits = try self.readIntBitsFromSlot(
                        self.call_stack.items[frame_idx].regs[args[0]],
                        id_ty,
                    );
                    const info = resolveIntInfo(self.pool, id_ty, self.options.target_layout);
                    const trace_val: i64 = if (info != null and info.?.is_signed)
                        @truncate(signExtendToI128(bits, info.?.bits))
                    else
                        @bitCast(@as(u64, @truncate(bits)));
                    self.drop_trace.append(self.allocator, trace_val) catch return error.OutOfMemory;
                }
                return .{ .scalar_u64 = 0 };
            },
            .bounds_check => {
                if (args.len < 3) return .{ .scalar_u64 = 0 };
                const idx_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const len_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
                const kind_ty = body.getInst(MirValueId.fromInt(args[2])).type_id;
                const idx_u128 = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[0]],
                    idx_ty,
                );
                const len_u128 = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[1]],
                    len_ty,
                );
                const container_kind = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[2]],
                    kind_ty,
                );
                const idx_info = resolveIntInfo(self.pool, idx_ty, self.options.target_layout);
                if (idx_info != null and idx_info.?.is_signed and
                    signExtendToI128(idx_u128, idx_info.?.bits) < 0)
                {
                    if (container_kind == 2) {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "negative index on `#soa` column slice during `comptime` evaluation",
                            "negative `#soa` index here",
                            null,
                        );
                    }
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "negative array or slice index during `comptime` evaluation",
                        "negative index here",
                        null,
                    );
                }
                if (idx_u128 >= len_u128) {
                    if (container_kind == 1) {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "array index out of bounds during `comptime` evaluation",
                            "index exceeds fixed array length",
                            null,
                        );
                    }
                    if (container_kind == 2) {
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "`#soa` column index out of bounds during `comptime` evaluation",
                            "`#soa` index exceeds length",
                            null,
                        );
                    }
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "slice index out of bounds during `comptime` evaluation",
                        "index exceeds slice length",
                        null,
                    );
                }
                return .{ .scalar_u64 = 0 };
            },
            .slice_range_check => {
                if (args.len < 3) return .{ .scalar_u64 = 0 };
                const lo_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const hi_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
                const len_ty = body.getInst(MirValueId.fromInt(args[2])).type_id;
                const lo_u128 = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[0]],
                    lo_ty,
                );
                const hi_u128 = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[1]],
                    hi_ty,
                );
                const len_u128 = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[2]],
                    len_ty,
                );
                const lo_info = resolveIntInfo(self.pool, lo_ty, self.options.target_layout);
                const hi_info = resolveIntInfo(self.pool, hi_ty, self.options.target_layout);
                const has_neg_lo = lo_info != null and lo_info.?.is_signed and
                    signExtendToI128(lo_u128, lo_info.?.bits) < 0;
                const has_neg_hi = hi_info != null and hi_info.?.is_signed and
                    signExtendToI128(hi_u128, hi_info.?.bits) < 0;
                if (has_neg_lo or has_neg_hi or lo_u128 > hi_u128 or hi_u128 > len_u128) {
                    return self.failWithTrap(
                        error.OutOfBounds,
                        .e0504_comptime_out_of_bounds,
                        "slice subrange out of bounds during `comptime` evaluation",
                        "invalid slice subrange bounds here",
                        null,
                    );
                }
                return .{ .scalar_u64 = 0 };
            },
            .narrow_check => {
                const narrow_res = try self.checkNarrowConversion(frame_idx, args, inst.type_id);
                if (!narrow_res.is_in_range) {
                    return self.failWithTrap(
                        error.IntegerOverflow,
                        .e0502_integer_constant_overflow,
                        "integer `.narrow()` value out of target range during `comptime` evaluation",
                        "value outside target range here",
                        "use `.try_narrow()` if out-of-range inputs should produce `Option.None`",
                    );
                }
                return self.makeIntSlot(inst.type_id, narrow_res.converted_bits);
            },
            .try_narrow => {
                const opt_ty = self.pool.unwrapUnderlyingType(inst.type_id);
                const dst_ty = TypeId.fromInt(self.pool.getNode(opt_ty).lhs);
                const narrow_res = try self.checkNarrowConversion(frame_idx, args, dst_ty);
                const opt_snap = try self.allocSnapshotForType(opt_ty, false);
                const sum_info = computeSumTypeTagAndPayloadLayout(
                    self.pool,
                    self.sym_table,
                    opt_ty,
                    self.options.target_layout,
                );
                if (narrow_res.is_in_range) {
                    const pay_slot = try self.makeIntSlot(dst_ty, narrow_res.converted_bits);
                    try self.storeTypedSlotToMemory(
                        try self.advanceSymbolicPtr(opt_snap, sum_info.payload_offset),
                        dst_ty,
                        pay_slot,
                    );
                    try self.writeSumDiscriminantAt(opt_snap, opt_ty, 1);
                } else {
                    try self.writeSumDiscriminantAt(opt_snap, opt_ty, 0);
                }
                self.sealSnapshot(opt_snap);
                return .{ .sym_ptr = opt_snap };
            },
            .zero_pad => {
                const outcome = try self.evalPlace(frame_idx, PlaceId.fromInt(inst.operands.lhs));
                const mp = switch (outcome) {
                    .memory_ptr => |mem_info| mem_info,
                    .constant_usize => return .{ .scalar_u64 = 0 },
                };
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    mp.pointee_ty,
                    self.options.target_layout,
                );
                _ = try self.validateAccess(mp.ptr, lay.byte_size, lay.align_log2, true);
                if (lay.byte_size > 0) {
                    const alloc_rec = &self.allocations.items[mp.ptr.alloc_id.payloadIndex()];
                    const start_off: usize = mp.ptr.byte_offset;
                    const len_usize: usize = @intCast(lay.byte_size);
                    @memset(alloc_rec.bytes[start_off .. start_off + len_usize], 0);
                    markRangeInitialized(alloc_rec, start_off, len_usize);
                    self.clearOverlappingProvenance(alloc_rec, mp.ptr.byte_offset, @intCast(lay.byte_size));
                }
                return .{ .scalar_u64 = 0 };
            },
            .drop_in_place, .drop_if_live => {
                if (kind == .drop_if_live) {
                    if (inst.operands.rhs == mir.NONE_U32) return .{ .scalar_u64 = 0 };
                    const flag_slot = self.call_stack.items[frame_idx].regs[inst.operands.rhs];
                    if ((flag_slot.scalar_u64 & 1) == 0) return .{ .scalar_u64 = 0 };
                }
                const outcome = try self.evalPlace(frame_idx, PlaceId.fromInt(inst.operands.lhs));
                const mp = switch (outcome) {
                    .memory_ptr => |mem_info| mem_info,
                    .constant_usize => return .{ .scalar_u64 = 0 },
                };
                const dropped_ty = if (inst.type_id != .unit_ty and !inst.type_id.isError())
                    inst.type_id
                else
                    mp.pointee_ty;
                try self.dropPlaceInVm(mp.ptr, dropped_ty);
                return .{ .scalar_u64 = 0 };
            },
            .abort_vacated_panic => {
                self.has_aborted_vacated_panic = true;
                return self.failWithTrap(
                    error.AbortedVacatedPanic,
                    .e0507_comptime_arithmetic_trap,
                    "panic triggered inside vacated non-`Copy` `inout` `subscript` projection window (`Fix-06B`)",
                    "immediate abort guard triggered here",
                    null,
                );
            },
            .ghost_storage_free => {
                const outcome = try self.evalPlace(frame_idx, PlaceId.fromInt(inst.operands.lhs));
                const mp = switch (outcome) {
                    .memory_ptr => |mem_info| mem_info,
                    .constant_usize => return .{ .scalar_u64 = 0 },
                };
                const ty_node = self.pool.getNode(self.pool.unwrapUnderlyingType(mp.pointee_ty));
                if (ty_node.tag == .raw_ptr_ty or ty_node.tag == .ref_ty or ty_node.tag == .mut_ref_ty) {
                    const target_ptr = try self.readPointerAt(
                        mp.ptr,
                        self.options.target_layout.ptr_align_log2,
                    );
                    try self.freeHeapMemory(target_ptr);
                } else {
                    try self.freeHeapMemory(mp.ptr);
                }
                return .{ .scalar_u64 = 0 };
            },
            .atomic_fence => return .{ .scalar_u64 = 0 },
            .atomic_load => {
                if (args.len < 1) return .{ .scalar_u64 = 0 };
                const ptr = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                return self.loadTypedSlotFromMemory(ptr, inst.type_id);
            },
            .atomic_store => {
                if (args.len < 2) return .{ .scalar_u64 = 0 };
                const ptr = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                const val_ty = body.getInst(MirValueId.fromInt(args[1])).type_id;
                try self.storeTypedSlotToMemory(ptr, val_ty, self.call_stack.items[frame_idx].regs[args[1]]);
                return .{ .scalar_u64 = 0 };
            },
            .atomic_rmw_xchg => {
                if (args.len < 2) return .{ .scalar_u64 = 0 };
                const ptr = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                const old_slot = try self.loadTypedSlotFromMemory(ptr, inst.type_id);
                try self.storeTypedSlotToMemory(
                    ptr,
                    inst.type_id,
                    self.call_stack.items[frame_idx].regs[args[1]],
                );
                return old_slot;
            },
            .atomic_rmw_add, .atomic_rmw_sub => {
                if (args.len < 2) return .{ .scalar_u64 = 0 };
                const ptr = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                const old_slot = try self.loadTypedSlotFromMemory(ptr, inst.type_id);
                const old_bits = try self.readIntBitsFromSlot(old_slot, inst.type_id);
                const rhs_bits = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[1]],
                    inst.type_id,
                );
                const next_bits = if (kind == .atomic_rmw_add) old_bits +% rhs_bits else old_bits -% rhs_bits;
                const next_slot = try self.makeIntSlot(inst.type_id, next_bits);
                try self.storeTypedSlotToMemory(ptr, inst.type_id, next_slot);
                return old_slot;
            },
            .atomic_cmpxchg => {
                if (args.len < 3) return .{ .scalar_u64 = 0 };
                const ptr = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                const val_ty = self.pool.unwrapUnderlyingType(body.getInst(MirValueId.fromInt(args[1])).type_id);
                const cur_slot = try self.loadTypedSlotFromMemory(ptr, val_ty);
                const exp_slot = self.call_stack.items[frame_idx].regs[args[1]];
                const des_slot = self.call_stack.items[frame_idx].regs[args[2]];
                const val_repr = classifyValueRepr(
                    self.pool,
                    self.sym_table,
                    val_ty,
                    self.options.target_layout,
                );
                const is_matched = if (val_repr == .inline_ptr)
                    (cur_slot.sym_ptr.alloc_id == exp_slot.sym_ptr.alloc_id and
                        cur_slot.sym_ptr.byte_offset == exp_slot.sym_ptr.byte_offset)
                else if (val_ty == .bool_ty)
                    ((cur_slot.scalar_u64 & 1) == (exp_slot.scalar_u64 & 1))
                else blk: {
                    const cur_bits = try self.readIntBitsFromSlot(cur_slot, val_ty);
                    const exp_bits = try self.readIntBitsFromSlot(exp_slot, val_ty);
                    break :blk cur_bits == exp_bits;
                };
                if (is_matched) {
                    try self.storeTypedSlotToMemory(ptr, val_ty, des_slot);
                }
                const pair_snap = try self.allocSnapshotForType(inst.type_id, false);
                if (computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    inst.type_id,
                    0,
                    self.options.target_layout,
                )) |f0| {
                    try self.storeTypedSlotToMemory(
                        try self.advanceSymbolicPtr(pair_snap, f0.byte_offset),
                        f0.field_ty,
                        cur_slot,
                    );
                }
                if (computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    inst.type_id,
                    1,
                    self.options.target_layout,
                )) |f1| {
                    try self.storeTypedSlotToMemory(
                        try self.advanceSymbolicPtr(pair_snap, f1.byte_offset),
                        f1.field_ty,
                        .{ .scalar_u64 = @intFromBool(is_matched) },
                    );
                }
                self.sealSnapshot(pair_snap);
                return .{ .sym_ptr = pair_snap };
            },
            .simd_splat => {
                if (args.len < 1) return .{ .scalar_u64 = 0 };
                const vec_ty = self.pool.unwrapUnderlyingType(inst.type_id);
                const vec_node = self.pool.getNode(vec_ty);
                const lane_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(vec_node.lhs));
                const lane_count: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const lane_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    lane_ty,
                    self.options.target_layout,
                );
                const snap = try self.allocSnapshotForType(vec_ty, false);
                const lane_slot = self.call_stack.items[frame_idx].regs[args[0]];
                for (0..@intCast(lane_count)) |lane_i| {
                    const off = try self.mulOffsetChecked(lane_i, lane_lay.byte_size);
                    try self.storeTypedSlotToMemory(
                        try self.advanceSymbolicPtr(snap, off),
                        lane_ty,
                        lane_slot,
                    );
                }
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
            .simd_add, .simd_sub, .simd_mul => {
                if (args.len < 2) return .{ .scalar_u64 = 0 };
                const vec_ty = self.pool.unwrapUnderlyingType(inst.type_id);
                const vec_node = self.pool.getNode(vec_ty);
                const lane_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(vec_node.lhs));
                const lane_count: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const lane_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    lane_ty,
                    self.options.target_layout,
                );
                const lhs_base = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                const rhs_base = self.call_stack.items[frame_idx].regs[args[1]].sym_ptr;
                const snap = try self.allocSnapshotForType(vec_ty, false);
                for (0..@intCast(lane_count)) |lane_i| {
                    const off = try self.mulOffsetChecked(lane_i, lane_lay.byte_size);
                    const lhs_lane = try self.loadTypedSlotFromMemory(
                        try self.advanceSymbolicPtr(lhs_base, off),
                        lane_ty,
                    );
                    const rhs_lane = try self.loadTypedSlotFromMemory(
                        try self.advanceSymbolicPtr(rhs_base, off),
                        lane_ty,
                    );
                    const out_lane: RegSlot = if (lane_ty == .f32_ty) blk_f32: {
                        const lv = unpackF32Slot(lhs_lane);
                        const rv = unpackF32Slot(rhs_lane);
                        const res = switch (kind) {
                            .simd_add => lv + rv,
                            .simd_sub => lv - rv,
                            else => lv * rv,
                        };
                        break :blk_f32 packF32Slot(res);
                    } else if (lane_ty == .f64_ty) blk_f64: {
                        const lv = lhs_lane.scalar_f64;
                        const rv = rhs_lane.scalar_f64;
                        const res = switch (kind) {
                            .simd_add => lv + rv,
                            .simd_sub => lv - rv,
                            else => lv * rv,
                        };
                        break :blk_f64 .{ .scalar_f64 = canonicalizeF64(res) };
                    } else blk_int: {
                        const lb = try self.readIntBitsFromSlot(lhs_lane, lane_ty);
                        const rb = try self.readIntBitsFromSlot(rhs_lane, lane_ty);
                        const res = switch (kind) {
                            .simd_add => lb +% rb,
                            .simd_sub => lb -% rb,
                            else => lb *% rb,
                        };
                        break :blk_int try self.makeIntSlot(lane_ty, res);
                    };
                    try self.storeTypedSlotToMemory(
                        try self.advanceSymbolicPtr(snap, off),
                        lane_ty,
                        out_lane,
                    );
                }
                self.sealSnapshot(snap);
                return .{ .sym_ptr = snap };
            },
            .simd_reduce_add => {
                if (args.len < 1) return .{ .scalar_u64 = 0 };
                const vec_ty = self.pool.unwrapUnderlyingType(body.getInst(MirValueId.fromInt(args[0])).type_id);
                const vec_node = self.pool.getNode(vec_ty);
                const lane_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(vec_node.lhs));
                const lane_count: u64 = vec_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const lane_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    lane_ty,
                    self.options.target_layout,
                );
                const vec_base = self.call_stack.items[frame_idx].regs[args[0]].sym_ptr;
                if (lane_ty == .f32_ty) {
                    var acc_f32: f32 = 0.0;
                    for (0..@intCast(lane_count)) |lane_i| {
                        const off = try self.mulOffsetChecked(lane_i, lane_lay.byte_size);
                        const lane_slot = try self.loadTypedSlotFromMemory(
                            try self.advanceSymbolicPtr(vec_base, off),
                            lane_ty,
                        );
                        acc_f32 += unpackF32Slot(lane_slot);
                    }
                    return packF32Slot(acc_f32);
                }
                if (lane_ty == .f64_ty) {
                    var acc_f64: f64 = 0.0;
                    for (0..@intCast(lane_count)) |lane_i| {
                        const off = try self.mulOffsetChecked(lane_i, lane_lay.byte_size);
                        const lane_slot = try self.loadTypedSlotFromMemory(
                            try self.advanceSymbolicPtr(vec_base, off),
                            lane_ty,
                        );
                        acc_f64 += lane_slot.scalar_f64;
                    }
                    return .{ .scalar_f64 = canonicalizeF64(acc_f64) };
                }
                var acc_int: u128 = 0;
                for (0..@intCast(lane_count)) |lane_i| {
                    const off = try self.mulOffsetChecked(lane_i, lane_lay.byte_size);
                    const lane_slot = try self.loadTypedSlotFromMemory(
                        try self.advanceSymbolicPtr(vec_base, off),
                        lane_ty,
                    );
                    acc_int +%= try self.readIntBitsFromSlot(lane_slot, lane_ty);
                }
                return self.makeIntSlot(inst.type_id, acc_int);
            },
            .poll_reload => return .{ .scalar_u64 = 0 },
            .panic => {
                if (args.len >= 1) {
                    const msg_bytes = try self.readStrSlotBytes(self.call_stack.items[frame_idx].regs[args[0]]);
                    defer self.allocator.free(msg_bytes);
                    if (self.options.is_oracle_runtime_mode) {
                        if (self.options.stderr_capture) |err_buf| {
                            err_buf.appendSlice(self.allocator, "panic: ") catch return error.OutOfMemory;
                            err_buf.appendSlice(self.allocator, msg_bytes) catch return error.OutOfMemory;
                            err_buf.append(self.allocator, '\n') catch return error.OutOfMemory;
                        }
                    }
                    const owned_msg = if (self.diagnostic_sink) |sink|
                        (sink.arena.dupe(u8, msg_bytes) catch "@panic triggered")
                    else
                        "@panic triggered";
                    return self.failWithTrap(
                        error.ArithmeticTrap,
                        .e0507_comptime_arithmetic_trap,
                        owned_msg,
                        "`@panic` triggered here",
                        null,
                    );
                }
                return self.failWithTrap(
                    error.ArithmeticTrap,
                    .e0507_comptime_arithmetic_trap,
                    "`@panic` triggered during `comptime` evaluation",
                    "`@panic` triggered here",
                    null,
                );
            },
            .trap => {
                return self.failWithTrap(
                    error.ArithmeticTrap,
                    .e0507_comptime_arithmetic_trap,
                    "explicit `@trap()` triggered",
                    "`@trap` triggered here",
                    null,
                );
            },
            .sys_write => {
                if (!self.options.is_oracle_runtime_mode) {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "`@sys_write` host I/O syscall is forbidden during `comptime` evaluation",
                        "`@sys_write` is forbidden at `comptime`",
                        null,
                    );
                }
                if (args.len < 2) return self.makeIntSlot(inst.type_id, @bitCast(@as(i128, -1)));
                const fd_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                const fd_bits = try self.readIntBitsFromSlot(
                    self.call_stack.items[frame_idx].regs[args[0]],
                    fd_ty,
                );
                const fd_i32: i32 = @truncate(signExtendToI128(fd_bits, 32));
                const span_info = try self.extractWireBytesSpan(
                    body.getInst(MirValueId.fromInt(args[1])).type_id,
                    self.call_stack.items[frame_idx].regs[args[1]],
                );
                if (span_info.byte_len > self.options.mem_limit) {
                    return self.failWithTrap(
                        error.ResourceLimitExceeded,
                        .e0508_comptime_resource_limit_exceeded,
                        "`@sys_write` buffer length exceeds memory limit",
                        "oversized `@sys_write` buffer",
                        null,
                    );
                }
                const target_capture = if (fd_i32 == 1)
                    self.options.stdout_capture
                else if (fd_i32 == 2)
                    self.options.stderr_capture
                else
                    return self.makeIntSlot(inst.type_id, @bitCast(@as(i128, -1)));

                const byte_len: usize = @intCast(span_info.byte_len);
                if (byte_len > 0) {
                    const tmp = self.allocator.alloc(u8, byte_len) catch return error.OutOfMemory;
                    defer self.allocator.free(tmp);
                    try self.readScalarBytes(span_info.data_ptr, 0, tmp);
                    if (target_capture) |cap_buf| {
                        cap_buf.appendSlice(self.allocator, tmp) catch return error.OutOfMemory;
                    }
                }
                return self.makeIntSlot(inst.type_id, @bitCast(@as(i128, @intCast(byte_len))));
            },
            .sys_exit => {
                if (!self.options.is_oracle_runtime_mode) {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "`@sys_exit` host process termination is forbidden during `comptime` evaluation",
                        "`@sys_exit` is forbidden at `comptime`",
                        null,
                    );
                }
                var exit_i32: i32 = 0;
                if (args.len >= 1) {
                    const code_ty = body.getInst(MirValueId.fromInt(args[0])).type_id;
                    const code_bits = try self.readIntBitsFromSlot(
                        self.call_stack.items[frame_idx].regs[args[0]],
                        code_ty,
                    );
                    exit_i32 = @truncate(signExtendToI128(code_bits, 32));
                }
                self.exited_with_code = exit_i32;
                return error.ProcessExited;
            },
        }
    }

    /// Formats a scalar, string, reference, or nominal struct/enum into `out` for interpolation / `Debug`.
    fn appendFormattedValue(
        self: *MirVm,
        out: *std.ArrayListUnmanaged(u8),
        raw_ty: TypeId,
        slot: RegSlot,
    ) VmEvalError!void {
        try self.tickStepBudget();
        var ty = self.pool.unwrapUnderlyingType(raw_ty);
        var val_slot = slot;
        const maybe_ref = self.pool.getNode(ty);
        if (maybe_ref.tag == .ref_ty or maybe_ref.tag == .mut_ref_ty) {
            const pointee_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(maybe_ref.lhs));
            val_slot = try self.loadTypedSlotFromMemory(val_slot.sym_ptr, pointee_ty);
            ty = pointee_ty;
        }

        if (ty == .str_ty) {
            const bytes = try self.readStrSlotBytes(val_slot);
            defer self.allocator.free(bytes);
            out.appendSlice(self.allocator, bytes) catch return error.OutOfMemory;
            return;
        }
        if (ty == .bool_ty) {
            const text = if ((val_slot.scalar_u64 & 1) != 0) "true" else "false";
            out.appendSlice(self.allocator, text) catch return error.OutOfMemory;
            return;
        }
        if (ty == .char_ty) {
            var utf8_buf: [4]u8 = undefined;
            const len = std.unicode.utf8Encode(@truncate(val_slot.scalar_u64), &utf8_buf) catch 0;
            out.appendSlice(self.allocator, utf8_buf[0..len]) catch return error.OutOfMemory;
            return;
        }
        if (ty == .f32_ty or ty == .f64_ty or ty == .untyped_float_ty) {
            const flt_v: f64 = if (ty == .f32_ty) unpackF32Slot(val_slot) else val_slot.scalar_f64;
            var scratch: [64]u8 = undefined;
            const text = std.fmt.bufPrint(&scratch, "{d}", .{flt_v}) catch "0";
            out.appendSlice(self.allocator, text) catch return error.OutOfMemory;
            return;
        }
        if (resolveIntInfo(self.pool, ty, self.options.target_layout)) |info| {
            const bits = try self.readIntBitsFromSlot(val_slot, ty);
            var scratch: [64]u8 = undefined;
            const text = if (info.is_signed)
                std.fmt.bufPrint(&scratch, "{d}", .{signExtendToI128(bits, info.bits)}) catch "0"
            else
                std.fmt.bufPrint(&scratch, "{d}", .{bits}) catch "0";
            out.appendSlice(self.allocator, text) catch return error.OutOfMemory;
            return;
        }
        const node = self.pool.getNode(ty);
        if (node.tag == .struct_ty) {
            const sym_idx = SymbolIndex.fromInt(node.rhs);
            if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                const st_sym = self.sym_table.getSymbol(sym_idx).*;
                out.appendSlice(self.allocator, st_sym.name_text) catch return error.OutOfMemory;
                out.appendSlice(self.allocator, " { ") catch return error.OutOfMemory;
                if (!st_sym.target_scope.isNone()) {
                    var ord: u32 = 0;
                    for (self.sym_table.getScopeMembers(st_sym.target_scope)) |mem_idx| {
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym) continue;
                        if (ord > 0) out.appendSlice(self.allocator, ", ") catch return error.OutOfMemory;
                        out.appendSlice(self.allocator, mem_sym.name_text) catch return error.OutOfMemory;
                        out.appendSlice(self.allocator, ": ") catch return error.OutOfMemory;
                        if (computeCompositeFieldOffsetAndType(
                            self.pool,
                            self.sym_table,
                            ty,
                            ord,
                            self.options.target_layout,
                        )) |f_info| {
                            const f_slot = try self.loadTypedSlotFromMemoryAligned(
                                try self.advanceSymbolicPtr(val_slot.sym_ptr, f_info.byte_offset),
                                f_info.field_ty,
                                st_sym.contract_flags.is_packed,
                            );
                            try self.appendFormattedValue(out, f_info.field_ty, f_slot);
                        }
                        ord += 1;
                    }
                }
                out.appendSlice(self.allocator, " }") catch return error.OutOfMemory;
                return;
            }
        }
        out.appendSlice(self.allocator, "<value>") catch return error.OutOfMemory;
    }

    // ---------- Reflection Intrinsics & Rodata Promotion ----------

    /// Loads sandboxed `@embed_bytes(rel_path)` from `virtual_files` or `workspace_root` (`E0326` on escape).
    pub fn evalEmbedBytesSlot(
        self: *MirVm,
        rel_path: []const u8,
        res_ty: TypeId,
    ) VmEvalError!RegSlot {
        if (self.options.compiler_db) |db| {
            const sb_key = db.recordEmbedSandboxDependency() catch |err| return self.mapDbQueryError(err);
            try self.recordObservedQueryDep(sb_key);
        }

        if (!isValidSandboxedEmbedPath(rel_path)) {
            return self.failWithTrap(
                error.ForbiddenOperation,
                .e0326_embed_path_escape,
                "`@embed_bytes` path must be a relative package path without `.`, `..`, drive prefixes, or device names",
                "`@embed_bytes` path escapes package sandbox here",
                null,
            );
        }

        var loaded_bytes: ?[]const u8 = null;
        var owned_disk_buf: ?[]u8 = null;
        defer if (owned_disk_buf) |buf| self.allocator.free(buf);

        if (self.options.virtual_files) |vfs_map| {
            if (vfs_map.get(rel_path)) |vfs_bytes| {
                loaded_bytes = vfs_bytes;
            }
        }
        if (loaded_bytes == null) {
            if (self.options.workspace_root) |ws_root| {
                if (self.options.io) |io_handle| {
                    const canon_ws = std.Io.Dir.cwd().realPathFileAlloc(
                        io_handle,
                        ws_root,
                        self.allocator,
                    ) catch {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "`@embed_bytes` workspace root could not be canonicalized",
                            "invalid workspace sandbox root",
                            null,
                        );
                    };
                    defer self.allocator.free(canon_ws);

                    const full_path = std.fs.path.join(self.allocator, &.{ canon_ws, rel_path }) catch
                        return error.OutOfMemory;
                    defer self.allocator.free(full_path);

                    // Reject leaf symlinks, junctions/reparse points, directories, and special files (`Fix-17` Gate D):
                    const opened_file = std.Io.Dir.cwd().openFile(io_handle, full_path, .{
                        .mode = .read_only,
                        .allow_directory = false,
                        .follow_symlinks = false,
                    }) catch |open_err| switch (open_err) {
                        error.SymLinkLoop, error.IsDir, error.NotDir => {
                            return self.failWithTrap(
                                error.ForbiddenOperation,
                                .e0326_embed_path_escape,
                                "`@embed_bytes` target cannot be a symlink, reparse point, or directory",
                                "`@embed_bytes` symlink or non-regular target blocked here",
                                null,
                            );
                        },
                        else => {
                            return self.failWithTrap(
                                error.ForbiddenOperation,
                                .e0503_forbidden_comptime_operation,
                                "`@embed_bytes` target file could not be opened inside workspace sandbox",
                                "unreadable `@embed_bytes` file",
                                null,
                            );
                        },
                    };
                    defer opened_file.close(io_handle);

                    const file_stat = opened_file.stat(io_handle) catch {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "`@embed_bytes` target file metadata could not be queried",
                            "unreadable `@embed_bytes` file",
                            null,
                        );
                    };
                    if (file_stat.kind != .file) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0326_embed_path_escape,
                            "`@embed_bytes` target must be a regular file inside the package sandbox",
                            "non-regular `@embed_bytes` target blocked here",
                            null,
                        );
                    }

                    const canon_target = std.Io.Dir.cwd().realPathFileAlloc(
                        io_handle,
                        full_path,
                        self.allocator,
                    ) catch {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0326_embed_path_escape,
                            "`@embed_bytes` target path could not be canonicalized inside package sandbox",
                            "`@embed_bytes` sandbox violation here",
                            null,
                        );
                    };
                    defer self.allocator.free(canon_target);

                    if (!isDirectCanonicalSubpath(canon_ws, canon_target, rel_path)) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0326_embed_path_escape,
                            "`@embed_bytes` target resolved outside package sandbox or traversed a symlink/junction",
                            "sandbox escape blocked here",
                            null,
                        );
                    }

                    const max_read_bytes: u64 = @min(self.options.mem_limit, std.math.maxInt(u32));
                    if (file_stat.size > max_read_bytes) {
                        return self.failWithTrap(
                            error.ResourceLimitExceeded,
                            .e0508_comptime_resource_limit_exceeded,
                            "`@embed_bytes` target file exceeds compile-time memory budget",
                            "oversized `@embed_bytes` file",
                            null,
                        );
                    }
                    const expected_size: usize = @intCast(file_stat.size);
                    const file_bytes = self.allocator.alloc(u8, expected_size) catch
                        return error.OutOfMemory;
                    errdefer self.allocator.free(file_bytes);
                    const actual_read = opened_file.readPositionalAll(io_handle, file_bytes, 0) catch {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "`@embed_bytes` target file could not be read from verified descriptor",
                            "unreadable `@embed_bytes` file",
                            null,
                        );
                    };
                    if (actual_read != expected_size) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "`@embed_bytes` target file changed size concurrently during read",
                            "truncated `@embed_bytes` file",
                            null,
                        );
                    }
                    owned_disk_buf = file_bytes;
                    loaded_bytes = file_bytes;
                }
            }
        }

        const raw_bytes = loaded_bytes orelse {
            return self.failWithTrap(
                error.ForbiddenOperation,
                .e0503_forbidden_comptime_operation,
                "`@embed_bytes` requires an active workspace root or virtual file mapping",
                "unavailable `@embed_bytes` file",
                null,
            );
        };

        if (self.options.compiler_db) |db| {
            const file_key = db.recordEmbeddedFileRead(rel_path, raw_bytes) catch |err| {
                return self.mapDbQueryError(err);
            };
            try self.recordObservedQueryDep(file_key);
        }

        const data_blob_id = self.rodata_pool.internBlob(raw_bytes, &.{}, 0) catch return error.OutOfMemory;
        const data_ptr = SymbolicPtr{ .alloc_id = data_blob_id, .byte_offset = 0 };

        const unwrapped = self.pool.unwrapUnderlyingType(res_ty);
        const ty_node = self.pool.getNode(unwrapped);
        if (ty_node.tag == .ref_ty or ty_node.tag == .raw_ptr_ty) {
            const pointee_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
            if (self.pool.getNode(pointee_ty).tag == .slice_ty) {
                const slice_slot = try self.makeFatSliceSlot(pointee_ty, data_ptr, raw_bytes.len);
                const slice_rodata = try self.promoteSnapshotToRodata(slice_slot.sym_ptr, pointee_ty);
                return .{ .sym_ptr = .{ .alloc_id = slice_rodata, .byte_offset = 0 } };
            }
            return .{ .sym_ptr = data_ptr };
        }
        return self.makeFatSliceSlot(unwrapped, data_ptr, raw_bytes.len);
    }

    /// Evaluates any of the 9 `DR-05` §3.3 reflection intrinsics directly inside `MirVm`.
    pub fn evalReflectionIntrinsic(
        self: *MirVm,
        intrinsic_kind: IntrinsicKind,
        type_args: []const TypeId,
        value_args: []const RegSlot,
        attr_instances: []const type_system.AttrInstance,
        out_store: ?*HirStore,
    ) VmEvalError!ComptimeValue {
        switch (intrinsic_kind) {
            .size_of => {
                if (type_args.len < 1) return .{ .int_val = 0 };
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    type_args[0],
                    self.options.target_layout,
                );
                return .{ .int_val = @as(i128, lay.byte_size) };
            },
            .align_of => {
                if (type_args.len < 1) return .{ .int_val = 1 };
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    type_args[0],
                    self.options.target_layout,
                );
                return .{ .int_val = @as(i128, lay.align_bytes) };
            },
            .type_name => {
                if (type_args.len < 1) return .{ .str_val = .empty };
                const rendered = formatCanonicalTypeName(
                    self.allocator,
                    self.pool,
                    self.sym_table,
                    type_args[0],
                ) catch return error.OutOfMemory;
                defer self.allocator.free(rendered);
                const name_id = self.interner.intern(rendered) catch return error.OutOfMemory;
                return .{ .str_val = name_id };
            },
            .type_info => {
                if (type_args.len < 1) return .unit_val;
                const target_ty = type_args[0];
                const lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    target_ty,
                    self.options.target_layout,
                );
                const rendered = formatCanonicalTypeName(
                    self.allocator,
                    self.pool,
                    self.sym_table,
                    target_ty,
                ) catch return error.OutOfMemory;
                defer self.allocator.free(rendered);
                const name_id = self.interner.intern(rendered) catch return error.OutOfMemory;
                const unwrapped = self.pool.unwrapUnderlyingType(target_ty);
                const rec = self.pool.getNode(unwrapped);
                var owner_def: DefId = .NONE;
                if (rec.tag == .struct_ty or rec.tag == .enum_ty or
                    rec.tag == .union_ty or rec.tag == .bit_field_ty)
                {
                    const sym_idx = SymbolIndex.fromInt(rec.rhs);
                    if (!sym_idx.isNone() and sym_idx.asInt() < self.sym_table.symbols.items.len) {
                        owner_def = self.sym_table.getSymbol(sym_idx).def_id;
                    }
                }
                return .{
                    .type_info_mirror = .{
                        .reflected_ty = target_ty,
                        .size_bytes = lay.byte_size,
                        .align_bytes = lay.align_bytes,
                        .type_name_id = name_id,
                        .owner_def_id = owner_def,
                    },
                };
            },
            .has_field => {
                if (type_args.len < 1 or value_args.len < 1) return .{ .bool_val = false };
                const field_name = try self.readStrSlotBytes(value_args[0]);
                defer self.allocator.free(field_name);
                return .{ .bool_val = self.lookupStructFieldByName(type_args[0], field_name) != null };
            },
            .field => {
                if (type_args.len < 1 or value_args.len < 2) return .unit_val;
                const field_name = try self.readStrSlotBytes(value_args[1]);
                defer self.allocator.free(field_name);

                var base_ty = self.pool.unwrapUnderlyingType(type_args[0]);
                var base_ptr = value_args[0].sym_ptr;
                const ty_node = self.pool.getNode(base_ty);
                if (ty_node.tag == .ref_ty or ty_node.tag == .mut_ref_ty or ty_node.tag == .raw_ptr_ty) {
                    base_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                }
                const f_info = self.lookupStructFieldByName(base_ty, field_name) orelse {
                    return self.failWithTrap(
                        error.ForbiddenOperation,
                        .e0503_forbidden_comptime_operation,
                        "`@field` requested unknown member name during `comptime` evaluation",
                        "unknown `@field` member here",
                        null,
                    );
                };
                base_ptr = try self.advanceSymbolicPtr(base_ptr, f_info.byte_offset);
                const f_slot = try self.loadTypedSlotFromMemory(base_ptr, f_info.field_ty);
                const f_repr = classifyValueRepr(
                    self.pool,
                    self.sym_table,
                    f_info.field_ty,
                    self.options.target_layout,
                );
                return self.slotToComptimeValue(f_info.field_ty, f_repr, f_slot, out_store);
            },
            .implements => {
                if (type_args.len < 2) return .{ .bool_val = false };
                const cand_ty = type_args[0];
                const bound_ty = self.pool.unwrapUnderlyingType(type_args[1]);
                if (bound_ty.isBuiltinGroup() or self.pool.getTag(bound_ty) == .user_group) {
                    const sat = type_system.checkGroupSatisfaction(
                        self.pool,
                        self.sym_table,
                        self.options.target_layout,
                        cand_ty,
                        bound_ty,
                    );
                    return .{ .bool_val = sat != .rejected and sat != .rejected_distinct_without_tilde };
                }
                const trait_node = self.pool.getNode(bound_ty);
                if (trait_node.tag == .trait_ty) {
                    const trait_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(trait_node.rhs));
                    if (self.pool.getFlags(cand_ty).is_secret and
                        (std.mem.eql(u8, trait_sym.name_text, "Debug") or
                            std.mem.eql(u8, trait_sym.name_text, "Display")))
                    {
                        return .{ .bool_val = false };
                    }
                    if (trait_sym.flags.is_builtin) {
                        if (std.mem.eql(u8, trait_sym.name_text, "Copy")) {
                            return .{
                                .bool_val = type_system.classifyOwnershipTier(
                                    self.pool,
                                    self.sym_table,
                                    cand_ty,
                                ) == .copy_tier,
                            };
                        }
                        if (std.mem.eql(u8, trait_sym.name_text, "AutoDrop")) {
                            return .{
                                .bool_val = type_system.classifyOwnershipTier(
                                    self.pool,
                                    self.sym_table,
                                    cand_ty,
                                ) == .auto_drop_tier,
                            };
                        }
                    }
                    const impl_ty = self.pool.unwrapUnderlyingType(cand_ty);
                    const unwrapped_key = (@as(u64, impl_ty.asInt()) << 32) | @as(u64, trait_node.rhs);
                    const raw_key = (@as(u64, cand_ty.asInt()) << 32) | @as(u64, trait_node.rhs);
                    return .{
                        .bool_val = self.sym_table.trait_impl_pairs.contains(unwrapped_key) or
                            self.sym_table.trait_impl_pairs.contains(raw_key),
                    };
                }
                return .{ .bool_val = false };
            },
            .field_attr_lookup => {
                if (type_args.len < 1 or value_args.len < 2) return .unit_val;
                const schema_ty = type_args[0];
                const opt_ty = self.pool.internOptional(schema_ty) catch return error.OutOfMemory;
                const target_ty = TypeId.fromInt(@truncate(value_args[0].scalar_u64));
                const member_ord: u32 = @truncate(value_args[1].scalar_u64);

                const nom_node = self.pool.getNode(self.pool.unwrapUnderlyingType(target_ty));
                if (nom_node.tag != .struct_ty and nom_node.tag != .enum_ty and
                    nom_node.tag != .union_ty and nom_node.tag != .bit_field_ty)
                {
                    return .{
                        .variant = .{
                            .type_id = opt_ty,
                            .tag_ordinal = 0,
                            .payload_const_idx = std.math.maxInt(u32),
                        },
                    };
                }
                const nom_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(nom_node.rhs)).*;
                var target_member_sym: SymbolIndex = .none;
                if (!nom_sym.target_scope.isNone()) {
                    var ord: u32 = 0;
                    for (self.sym_table.getScopeMembers(nom_sym.target_scope)) |mem_idx| {
                        const mem_sym = self.sym_table.getSymbol(mem_idx).*;
                        if (mem_sym.kind != .field_sym and mem_sym.kind != .enum_variant_sym) continue;
                        if (ord == member_ord) {
                            target_member_sym = mem_idx;
                            break;
                        }
                        ord += 1;
                    }
                }
                if (target_member_sym.isNone()) {
                    return .{
                        .variant = .{
                            .type_id = opt_ty,
                            .tag_ordinal = 0,
                            .payload_const_idx = std.math.maxInt(u32),
                        },
                    };
                }
                const unwrapped_schema = self.pool.unwrapUnderlyingType(schema_ty);
                for (attr_instances) |attr_inst| {
                    if (attr_inst.target_symbol == target_member_sym and
                        self.pool.unwrapUnderlyingType(attr_inst.schema_type_id) == unwrapped_schema)
                    {
                        if (out_store) |store_ptr| {
                            const schema_rec = self.pool.getNode(unwrapped_schema);
                            const schema_sym = self.sym_table.getSymbol(SymbolIndex.fromInt(schema_rec.rhs)).*;
                            var elem_indices: std.ArrayListUnmanaged(u32) = .empty;
                            defer elem_indices.deinit(self.allocator);
                            if (!schema_sym.target_scope.isNone()) {
                                var f_ord: usize = 0;
                                for (self.sym_table.getScopeMembers(schema_sym.target_scope)) |sf_idx| {
                                    const sf_sym = self.sym_table.getSymbol(sf_idx).*;
                                    if (sf_sym.kind != .field_sym) continue;
                                    var field_cv: ComptimeValue = .{ .int_val = 0 };
                                    for (attr_inst.fields) |init_f| {
                                        if (init_f.field_ordinal == f_ord) {
                                            field_cv = convertAttrArgValue(init_f.value, sf_sym.type_id);
                                            break;
                                        }
                                    }
                                    const c_idx = store_ptr.appendConst(field_cv) catch return error.OutOfMemory;
                                    elem_indices.append(self.allocator, c_idx) catch return error.OutOfMemory;
                                    f_ord += 1;
                                }
                            }
                            const elem_start: u32 = @intCast(store_ptr.const_elements.items.len);
                            store_ptr.const_elements.appendSlice(
                                store_ptr.allocator,
                                elem_indices.items,
                            ) catch return error.OutOfMemory;
                            const pay_idx = store_ptr.appendConst(.{
                                .aggregate = .{
                                    .type_id = schema_ty,
                                    .elem_start = elem_start,
                                    .elem_len = @intCast(elem_indices.items.len),
                                },
                            }) catch return error.OutOfMemory;
                            return .{
                                .variant = .{
                                    .type_id = opt_ty,
                                    .tag_ordinal = 1,
                                    .payload_const_idx = pay_idx,
                                },
                            };
                        }
                        return .{
                            .variant = .{
                                .type_id = opt_ty,
                                .tag_ordinal = 1,
                                .payload_const_idx = std.math.maxInt(u32),
                            },
                        };
                    }
                }
                return .{
                    .variant = .{
                        .type_id = opt_ty,
                        .tag_ordinal = 0,
                        .payload_const_idx = std.math.maxInt(u32),
                    },
                };
            },
            .embed_bytes => {
                if (value_args.len < 1) return .unit_val;
                const rel_path = try self.readStrSlotBytes(value_args[0]);
                defer self.allocator.free(rel_path);
                const slice_ty = self.pool.internSlice(.u8_ty, false) catch return error.OutOfMemory;
                const slot = try self.evalEmbedBytesSlot(rel_path, slice_ty);
                const raw = try self.readStrSlotBytes(slot);
                defer self.allocator.free(raw);
                const sym_id = self.interner.intern(raw) catch return error.OutOfMemory;
                return .{ .bytes_val = sym_id };
            },
            else => return .unit_val,
        }
    }

    /// Resolves `(ordinal, byte_offset, field_ty)` by field name on a nominal `struct` or `union`.
    fn lookupStructFieldByName(
        self: *const MirVm,
        raw_ty: TypeId,
        field_name: []const u8,
    ) ?struct { ordinal: u32, byte_offset: u32, field_ty: TypeId } {
        var ty = self.pool.unwrapUnderlyingType(raw_ty);
        const maybe_ref = self.pool.getNode(ty);
        if (maybe_ref.tag == .ref_ty or maybe_ref.tag == .mut_ref_ty or maybe_ref.tag == .raw_ptr_ty) {
            ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(maybe_ref.lhs));
        }
        const node = self.pool.getNode(ty);
        if (node.tag != .struct_ty and node.tag != .union_ty) return null;
        const sym_idx = SymbolIndex.fromInt(node.rhs);
        if (sym_idx.isNone() or sym_idx.asInt() >= self.sym_table.symbols.items.len) return null;
        const st_sym = self.sym_table.getSymbol(sym_idx).*;
        if (st_sym.target_scope.isNone()) return null;

        var ord: u32 = 0;
        for (self.sym_table.getScopeMembers(st_sym.target_scope)) |mem_idx| {
            const mem_sym = self.sym_table.getSymbol(mem_idx).*;
            if (mem_sym.kind != .field_sym) continue;
            if (std.mem.eql(u8, mem_sym.name_text, field_name)) {
                const info = computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    ty,
                    ord,
                    self.options.target_layout,
                ) orelse return null;
                return .{ .ordinal = ord, .byte_offset = info.byte_offset, .field_ty = info.field_ty };
            }
            ord += 1;
        }
        return null;
    }

    /// Promotes an evaluated `VmEvalResult` into `self.rodata_pool`, zeroing uninitialized padding bytes
    /// deterministically and rejecting escaping stack pointers (`E0506`, `DR-05` §3.6).
    pub fn promoteResultToRodata(self: *MirVm, eval_res: VmEvalResult) VmEvalError!ComptimeAllocId {
        try self.verifyNoEscapingStackPointers(eval_res.type_id, eval_res.repr, eval_res.slot);
        if (eval_res.repr == .by_value_snapshot) {
            return self.promoteSnapshotToRodata(eval_res.slot.sym_ptr, eval_res.type_id);
        }
        const snap = try self.allocSnapshotForType(eval_res.type_id, false);
        try self.storeTypedSlotToMemory(snap, eval_res.type_id, eval_res.slot);
        self.sealSnapshot(snap);
        return self.promoteSnapshotToRodata(snap, eval_res.type_id);
    }

    /// Recursively promotes a `SymbolicPtr` allocation slice of `raw_ty` into `RodataPool` (`[MAJOR-07]`).
    pub fn promoteSnapshotToRodata(
        self: *MirVm,
        src_ptr: SymbolicPtr,
        raw_ty: TypeId,
    ) VmEvalError!ComptimeAllocId {
        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            raw_ty,
            self.options.target_layout,
        );
        _ = try self.validateAccess(src_ptr, lay.byte_size, lay.align_log2, false);

        const byte_len: usize = @intCast(lay.byte_size);
        if (src_ptr.alloc_id.domain() == .rodata_blob and src_ptr.byte_offset == 0) {
            if (self.rodata_pool.getBlob(src_ptr.alloc_id.payloadIndex())) |existing_blob| {
                if (existing_blob.bytes.len == byte_len) {
                    return src_ptr.alloc_id;
                }
            }
        }
        if (src_ptr.alloc_id.domain() == .string_lit and src_ptr.byte_offset == 0) {
            const text = self.interner.get(SymbolId.fromInt(src_ptr.alloc_id.payloadIndex()));
            if (text.len == byte_len) {
                return self.rodata_pool.internBlob(text, &.{}, 0) catch return error.OutOfMemory;
            }
        }

        const canonical_bytes = self.allocator.alloc(u8, byte_len) catch return error.OutOfMemory;
        defer self.allocator.free(canonical_bytes);
        @memset(canonical_bytes, 0);

        var relocs: std.ArrayListUnmanaged(RodataReloc) = .empty;
        defer relocs.deinit(self.allocator);
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;
        const end_off: u64 = @as(u64, src_ptr.byte_offset) + lay.byte_size;

        if (src_ptr.alloc_id.domain() == .vm_alloc) {
            const rec = &self.allocations.items[src_ptr.alloc_id.payloadIndex()];
            if (!rec.is_live or rec.is_stack_frame) {
                return self.failWithTrap(
                    error.InvalidPointer,
                    .e0506_comptime_invalid_pointer,
                    "cannot promote stack-local allocation into `.rodata` constant",
                    "dangling stack allocation promoted here",
                    null,
                );
            }
            _ = try self.isTypeLeafFieldsInitialized(rec, src_ptr.byte_offset, raw_ty, true);

            const base_off: usize = src_ptr.byte_offset;
            // Deterministically zero genuine alignment padding bytes while copying initialized bytes:
            for (0..byte_len) |off_i| {
                canonical_bytes[off_i] = if (isByteInitialized(rec, base_off + off_i))
                    rec.bytes[base_off + off_i]
                else
                    0;
            }

            const raw_prov_copy = self.allocator.dupe(
                ProvenanceEntry,
                rec.provenance.items,
            ) catch return error.OutOfMemory;
            defer self.allocator.free(raw_prov_copy);

            var visited_allocs: std.AutoHashMapUnmanaged(u32, ComptimeAllocId) = .empty;
            defer visited_allocs.deinit(self.allocator);
            var in_progress_allocs: std.AutoHashMapUnmanaged(u32, void) = .empty;
            defer in_progress_allocs.deinit(self.allocator);

            for (raw_prov_copy) |entry| {
                const entry_start: u64 = entry.byte_offset;
                const entry_end: u64 = entry_start + ptr_width;
                if (entry_start < end_off and @as(u64, src_ptr.byte_offset) < entry_end) {
                    if (entry_start < src_ptr.byte_offset or entry_end > end_off) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "torn pointer provenance overlaps promoted `.rodata` slice boundary",
                            "torn pointer provenance here",
                            null,
                        );
                    }
                    try self.checkPointerTargetNonStack(entry.alloc_id);
                    var promoted_target = entry.alloc_id;
                    if (entry.alloc_id.domain() == .vm_alloc and entry.alloc_id != .null_ptr) {
                        promoted_target = try self.promoteVmAllocRawToRodata(
                            entry.alloc_id.payloadIndex(),
                            &visited_allocs,
                            &in_progress_allocs,
                        );
                    }
                    relocs.append(self.allocator, .{
                        .byte_offset = entry.byte_offset - src_ptr.byte_offset,
                        .target_alloc = promoted_target,
                    }) catch return error.OutOfMemory;
                }
            }
        } else if (src_ptr.alloc_id.domain() == .rodata_blob) {
            const blob = self.rodata_pool.getBlob(src_ptr.alloc_id.payloadIndex()).?;
            const base_off: usize = src_ptr.byte_offset;
            @memcpy(canonical_bytes, blob.bytes[base_off .. base_off + byte_len]);
            for (blob.relocs) |reloc| {
                const rel_start: u64 = reloc.byte_offset;
                const rel_end: u64 = rel_start + ptr_width;
                if (rel_start < end_off and @as(u64, src_ptr.byte_offset) < rel_end) {
                    if (rel_start < src_ptr.byte_offset or rel_end > end_off) {
                        return self.failWithTrap(
                            error.ForbiddenOperation,
                            .e0503_forbidden_comptime_operation,
                            "torn pointer relocation overlaps promoted `.rodata` slice boundary",
                            "torn pointer relocation here",
                            null,
                        );
                    }
                    relocs.append(self.allocator, .{
                        .byte_offset = reloc.byte_offset - src_ptr.byte_offset,
                        .target_alloc = reloc.target_alloc,
                    }) catch return error.OutOfMemory;
                }
            }
        } else if (src_ptr.alloc_id.domain() == .string_lit) {
            const text = self.interner.get(SymbolId.fromInt(src_ptr.alloc_id.payloadIndex()));
            const base_off: usize = src_ptr.byte_offset;
            @memcpy(canonical_bytes, text[base_off .. base_off + byte_len]);
        }

        return self.rodata_pool.internBlob(canonical_bytes, relocs.items, lay.align_log2) catch
            return error.OutOfMemory;
    }

    /// Walks non-padding leaf fields of `raw_ty` inside `alloc_rec` at `base_off`, trapping `E0505` if any
    /// non-padding byte is uninitialized when `is_emitting_diag` is `true` (`[MAJOR-07]`).
    fn isTypeLeafFieldsInitialized(
        self: *MirVm,
        alloc_rec: *const ComptimeAllocation,
        base_off: u32,
        raw_ty: TypeId,
        is_emitting_diag: bool,
    ) VmEvalError!bool {
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        if (ty == .unit_ty or ty == .never_ty or ty.isError()) return true;

        const lay = type_system.computeTypeLayoutWithPool(
            self.pool,
            self.sym_table,
            ty,
            self.options.target_layout,
        );
        if (lay.byte_size == 0) return true;

        const ty_node = self.pool.getNode(ty);
        switch (ty_node.tag) {
            .tuple_ty, .struct_ty => {
                var ord: u32 = 0;
                while (computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    ty,
                    ord,
                    self.options.target_layout,
                )) |f_info| : (ord += 1) {
                    const field_off = std.math.add(u32, base_off, f_info.byte_offset) catch {
                        if (!is_emitting_diag) return false;
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "field offset overflowed `u32` during `.rodata` promotion",
                            "out-of-bounds field offset here",
                            null,
                        );
                    };
                    if (!try self.isTypeLeafFieldsInitialized(
                        alloc_rec,
                        field_off,
                        f_info.field_ty,
                        is_emitting_diag,
                    )) {
                        return false;
                    }
                }
                return true;
            },
            .array_ty => {
                const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                const arr_len: u32 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                const elem_lay = type_system.computeTypeLayoutWithPool(
                    self.pool,
                    self.sym_table,
                    elem_ty,
                    self.options.target_layout,
                );
                if (elem_lay.byte_size == 0) return true;
                for (0..arr_len) |elem_i| {
                    try self.tickStepBudget();
                    const delta = try self.mulOffsetChecked(elem_i, elem_lay.byte_size);
                    const elem_off = std.math.add(u32, base_off, @intCast(delta)) catch {
                        if (!is_emitting_diag) return false;
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "array element offset overflowed `u32` during `.rodata` promotion",
                            "out-of-bounds element offset here",
                            null,
                        );
                    };
                    if (!try self.isTypeLeafFieldsInitialized(
                        alloc_rec,
                        elem_off,
                        elem_ty,
                        is_emitting_diag,
                    )) {
                        return false;
                    }
                }
                return true;
            },
            .soa_array_ty => {
                const elem_struct_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                const elem_cap: u32 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                if (elem_cap == 0) return true;
                var col_ord: u32 = 0;
                while (computeSoaColumnOffsetAndType(
                    self.pool,
                    self.sym_table,
                    elem_struct_ty,
                    col_ord,
                    elem_cap,
                    self.options.target_layout,
                )) |col_info| : (col_ord += 1) {
                    const col_lay = type_system.computeTypeLayoutWithPool(
                        self.pool,
                        self.sym_table,
                        col_info.field_ty,
                        self.options.target_layout,
                    );
                    if (col_lay.byte_size == 0) continue;
                    for (0..elem_cap) |elem_i| {
                        try self.tickStepBudget();
                        const elem_delta = try self.mulOffsetChecked(elem_i, col_lay.byte_size);
                        const total_delta = std.math.add(u64, col_info.column_byte_offset, elem_delta) catch
                            std.math.maxInt(u64);
                        if (total_delta > std.math.maxInt(u32)) {
                            if (!is_emitting_diag) return false;
                            return self.failWithTrap(
                                error.OutOfBounds,
                                .e0504_comptime_out_of_bounds,
                                "SoA column offset overflowed `u32` during `.rodata` promotion",
                                "out-of-bounds SoA offset here",
                                null,
                            );
                        }
                        const col_elem_off = std.math.add(u32, base_off, @intCast(total_delta)) catch {
                            if (!is_emitting_diag) return false;
                            return self.failWithTrap(
                                error.OutOfBounds,
                                .e0504_comptime_out_of_bounds,
                                "SoA column offset overflowed `u32` during `.rodata` promotion",
                                "out-of-bounds SoA offset here",
                                null,
                            );
                        };
                        if (!try self.isTypeLeafFieldsInitialized(
                            alloc_rec,
                            col_elem_off,
                            col_info.field_ty,
                            is_emitting_diag,
                        )) {
                            return false;
                        }
                    }
                }
                return true;
            },
            .optional_ty, .result_ty, .enum_ty => {
                const sum_lay = type_system.computeSumMemoryLayout(
                    self.pool,
                    self.sym_table,
                    ty,
                    self.options.target_layout,
                );
                var tag_ord: u32 = 0;
                switch (sum_lay.repr) {
                    .transparent_ok => tag_ord = 0,
                    .niche_single => {
                        const zst_ord: u32 = sum_lay.zst_discriminant;
                        const pay_ord: u32 = sum_lay.payload_discriminant;
                        const niche_off = std.math.add(u32, base_off, sum_lay.niche.byte_offset) catch {
                            if (!is_emitting_diag) return false;
                            return self.failWithTrap(
                                error.OutOfBounds,
                                .e0504_comptime_out_of_bounds,
                                "sum niche offset overflowed `u32` during `.rodata` promotion",
                                "out-of-bounds niche offset here",
                                null,
                            );
                        };
                        const niche_bytes: u64 = if (sum_lay.niche.kind == .zero_ptr)
                            self.options.target_layout.ptr_byte_size
                        else
                            sum_lay.niche.scalar_bytes;
                        if (!try self.isContiguousByteRangeInitialized(
                            alloc_rec,
                            niche_off,
                            niche_bytes,
                            is_emitting_diag,
                        )) {
                            return false;
                        }
                        if (sum_lay.niche.kind == .zero_ptr) {
                            const prov_aid = findExactProvenance(alloc_rec, niche_off) orelse {
                                if (!is_emitting_diag) return false;
                                return self.failWithTrap(
                                    error.ForbiddenOperation,
                                    .e0503_forbidden_comptime_operation,
                                    "pointer-niched sum lacks valid pointer provenance during `.rodata` promotion",
                                    "missing pointer provenance here",
                                    null,
                                );
                            };
                            tag_ord = if (prov_aid == .null_ptr) zst_ord else pay_ord;
                        } else {
                            var sbuf: [8]u8 = @splat(0);
                            const n_idx: usize = niche_off;
                            const s_len: usize = sum_lay.niche.scalar_bytes;
                            @memcpy(sbuf[0..s_len], alloc_rec.bytes[n_idx .. n_idx + s_len]);
                            const raw_val = std.mem.readInt(u64, &sbuf, .little);
                            tag_ord = if (raw_val == sum_lay.niche.invalid_first) zst_ord else pay_ord;
                        }
                    },
                    .explicit_tag => {
                        if (!try self.isContiguousByteRangeInitialized(
                            alloc_rec,
                            base_off,
                            sum_lay.tag_bytes,
                            is_emitting_diag,
                        )) {
                            return false;
                        }
                        if (sum_lay.tag_bytes > 0) {
                            var tag_buf: [4]u8 = @splat(0);
                            const start_idx: usize = base_off;
                            const tag_len: usize = sum_lay.tag_bytes;
                            @memcpy(tag_buf[0..tag_len], alloc_rec.bytes[start_idx .. start_idx + tag_len]);
                            tag_ord = std.mem.readInt(u32, &tag_buf, .little);
                        }
                    },
                }
                const pay_ty = self.pool.unwrapUnderlyingType(
                    resolveVariantPayloadType(self.pool, self.sym_table, ty, tag_ord),
                );
                if (pay_ty != .unit_ty and !pay_ty.isError()) {
                    const pay_off = std.math.add(u32, base_off, @intCast(sum_lay.payload_offset)) catch {
                        if (!is_emitting_diag) return false;
                        return self.failWithTrap(
                            error.OutOfBounds,
                            .e0504_comptime_out_of_bounds,
                            "variant payload offset overflowed `u32` during `.rodata` promotion",
                            "out-of-bounds payload offset here",
                            null,
                        );
                    };
                    return self.isTypeLeafFieldsInitialized(alloc_rec, pay_off, pay_ty, is_emitting_diag);
                }
                return true;
            },
            .union_ty => {
                var ord: u32 = 0;
                var has_non_empty_field = false;
                while (computeCompositeFieldOffsetAndType(
                    self.pool,
                    self.sym_table,
                    ty,
                    ord,
                    self.options.target_layout,
                )) |f_info| : (ord += 1) {
                    has_non_empty_field = true;
                    const field_off = std.math.add(u32, base_off, f_info.byte_offset) catch continue;
                    if (try self.isTypeLeafFieldsInitialized(alloc_rec, field_off, f_info.field_ty, false)) {
                        return true;
                    }
                }
                if (!has_non_empty_field) return true;
                if (!is_emitting_diag) return false;
                return self.failWithTrap(
                    error.UninitializedRead,
                    .e0505_comptime_uninitialized_read,
                    "cannot promote uninitialized union value into `.rodata` constant",
                    "uninitialized union promoted here",
                    null,
                );
            },
            .closure_ty => {
                return self.isContiguousByteRangeInitialized(
                    alloc_rec,
                    base_off,
                    self.options.target_layout.ptr_byte_size,
                    is_emitting_diag,
                );
            },
            else => {
                return self.isContiguousByteRangeInitialized(
                    alloc_rec,
                    base_off,
                    lay.byte_size,
                    is_emitting_diag,
                );
            },
        }
    }

    /// Checks whether all bytes in `[base_off .. base_off + byte_len)` of `alloc_rec` have `init_mask == 1`.
    fn isContiguousByteRangeInitialized(
        self: *MirVm,
        alloc_rec: *const ComptimeAllocation,
        base_off: u32,
        byte_len: u64,
        is_emitting_diag: bool,
    ) VmEvalError!bool {
        if (byte_len == 0) return true;
        const end_off = std.math.add(u64, base_off, byte_len) catch std.math.maxInt(u64);
        if (end_off > alloc_rec.bytes.len) {
            if (!is_emitting_diag) return false;
            return self.failWithTrap(
                error.OutOfBounds,
                .e0504_comptime_out_of_bounds,
                "out-of-bounds leaf field encountered during `.rodata` promotion",
                "out-of-bounds `.rodata` promotion here",
                null,
            );
        }
        const start_usize: usize = base_off;
        const len_usize: usize = @intCast(byte_len);
        for (0..len_usize) |rel_i| {
            if (!isByteInitialized(alloc_rec, start_usize + rel_i)) {
                if (!is_emitting_diag) return false;
                return self.failWithTrap(
                    error.UninitializedRead,
                    .e0505_comptime_uninitialized_read,
                    "cannot promote value with uninitialized leaf field into `.rodata` constant",
                    "uninitialized byte promoted into `.rodata` here",
                    null,
                );
            }
        }
        return true;
    }

    /// Promotes an untyped nested `vm_alloc` (e.g., slice backing buffer) into `RodataPool` (`[MAJOR-07]`).
    fn promoteVmAllocRawToRodata(
        self: *MirVm,
        vm_idx: u32,
        visited_allocs: *std.AutoHashMapUnmanaged(u32, ComptimeAllocId),
        in_progress_allocs: *std.AutoHashMapUnmanaged(u32, void),
    ) VmEvalError!ComptimeAllocId {
        if (visited_allocs.get(vm_idx)) |cached_blob| return cached_blob;
        if (in_progress_allocs.contains(vm_idx)) {
            return self.failWithTrap(
                error.ForbiddenOperation,
                .e0503_forbidden_comptime_operation,
                "cyclic pointer provenance graph cannot be promoted into `.rodata` constant",
                "cyclic `.rodata` pointer provenance here",
                null,
            );
        }
        in_progress_allocs.put(self.allocator, vm_idx, {}) catch return error.OutOfMemory;
        errdefer _ = in_progress_allocs.remove(vm_idx);

        const rec = &self.allocations.items[vm_idx];
        if (!rec.is_live or rec.is_stack_frame) {
            return self.failWithTrap(
                error.InvalidPointer,
                .e0506_comptime_invalid_pointer,
                "cannot promote stack-local pointee into `.rodata` constant",
                "dangling stack pointer in `.rodata`",
                null,
            );
        }
        const byte_len = rec.bytes.len;
        const align_log2 = rec.align_log2;
        const ptr_width: u32 = self.options.target_layout.ptr_byte_size;

        const canonical_bytes = self.allocator.alloc(u8, byte_len) catch return error.OutOfMemory;
        defer self.allocator.free(canonical_bytes);
        for (0..byte_len) |off_i| {
            canonical_bytes[off_i] = if (isByteInitialized(rec, off_i)) rec.bytes[off_i] else 0;
        }

        var relocs: std.ArrayListUnmanaged(RodataReloc) = .empty;
        defer relocs.deinit(self.allocator);
        const prov_snapshot = self.allocator.dupe(
            ProvenanceEntry,
            rec.provenance.items,
        ) catch return error.OutOfMemory;
        defer self.allocator.free(prov_snapshot);

        for (prov_snapshot) |entry| {
            if (@as(u64, entry.byte_offset) + ptr_width > byte_len) {
                return self.failWithTrap(
                    error.ForbiddenOperation,
                    .e0503_forbidden_comptime_operation,
                    "out-of-bounds pointer provenance encountered during `.rodata` promotion",
                    "torn pointer provenance here",
                    null,
                );
            }
            try self.checkPointerTargetNonStack(entry.alloc_id);
            var target = entry.alloc_id;
            if (entry.alloc_id.domain() == .vm_alloc and entry.alloc_id != .null_ptr) {
                target = try self.promoteVmAllocRawToRodata(
                    entry.alloc_id.payloadIndex(),
                    visited_allocs,
                    in_progress_allocs,
                );
            }
            relocs.append(self.allocator, .{
                .byte_offset = entry.byte_offset,
                .target_alloc = target,
            }) catch return error.OutOfMemory;
        }
        const blob_id = self.rodata_pool.internBlob(canonical_bytes, relocs.items, align_log2) catch
            return error.OutOfMemory;
        _ = in_progress_allocs.remove(vm_idx);
        visited_allocs.put(self.allocator, vm_idx, blob_id) catch return error.OutOfMemory;
        return blob_id;
    }

    /// Converts a `VmEvalResult` into a `hir.ComptimeValue` (populating `out_store` for aggregates/variants).
    pub fn resultToComptimeValue(
        self: *MirVm,
        eval_res: VmEvalResult,
        out_store: ?*HirStore,
    ) VmEvalError!ComptimeValue {
        return self.slotToComptimeValue(eval_res.type_id, eval_res.repr, eval_res.slot, out_store);
    }

    /// Converts an evaluated `(raw_ty, repr, slot)` into a `hir.ComptimeValue` (`[CRITICAL-03]`, `[CRITICAL-04]`).
    pub fn slotToComptimeValue(
        self: *MirVm,
        raw_ty: TypeId,
        repr: VmValueRepr,
        slot: RegSlot,
        out_store: ?*HirStore,
    ) VmEvalError!ComptimeValue {
        try self.tickStepBudget();
        const ty = self.pool.unwrapUnderlyingType(raw_ty);
        if (ty == .unit_ty or ty == .never_ty) return .unit_val;
        if (ty == .bool_ty) return .{ .bool_val = (slot.scalar_u64 & 1) != 0 };
        if (ty == .char_ty) return .{ .char_val = @truncate(slot.scalar_u64) };
        if (ty == .f32_ty) return .{ .float_val = unpackF32Slot(slot) };
        if (ty == .f64_ty or ty == .untyped_float_ty) return .{ .float_val = canonicalizeF64(slot.scalar_f64) };

        if (resolveIntInfo(self.pool, ty, self.options.target_layout)) |info| {
            const bits = try self.readIntBitsFromSlot(slot, ty);
            if (info.is_signed) return .{ .int_val = signExtendToI128(bits, info.bits) };
            return .{ .int_val = @bitCast(bits) };
        }

        if (ty == .str_ty) {
            const bytes = try self.readStrSlotBytes(slot);
            defer self.allocator.free(bytes);
            const sym_id = self.interner.intern(bytes) catch return error.OutOfMemory;
            return .{ .str_val = sym_id };
        }

        const ty_node = self.pool.getNode(ty);
        if (ty_node.tag == .ref_ty or ty_node.tag == .raw_ptr_ty) {
            const pointee = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
            const p_node = self.pool.getNode(pointee);
            if (p_node.tag == .slice_ty and TypeId.fromInt(p_node.lhs) == .u8_ty) {
                const slice_slot = try self.loadTypedSlotFromMemory(slot.sym_ptr, pointee);
                const bytes = try self.readStrSlotBytes(slice_slot);
                defer self.allocator.free(bytes);
                const sym_id = self.interner.intern(bytes) catch return error.OutOfMemory;
                return .{ .bytes_val = sym_id };
            }
        }
        if (ty_node.tag == .slice_ty and TypeId.fromInt(ty_node.lhs) == .u8_ty) {
            const bytes = try self.readStrSlotBytes(slot);
            defer self.allocator.free(bytes);
            const sym_id = self.interner.intern(bytes) catch return error.OutOfMemory;
            return .{ .bytes_val = sym_id };
        }

        if (repr == .by_value_snapshot) {
            switch (ty_node.tag) {
                .optional_ty, .result_ty, .enum_ty => {
                    const sum_info = computeSumTypeTagAndPayloadLayout(
                        self.pool,
                        self.sym_table,
                        ty,
                        self.options.target_layout,
                    );
                    const tag_ord = try self.readSumDiscriminantAt(slot.sym_ptr, ty);
                    const pay_ty = self.pool.unwrapUnderlyingType(
                        resolveVariantPayloadType(self.pool, self.sym_table, ty, tag_ord),
                    );
                    var pay_const_idx: u32 = std.math.maxInt(u32);
                    if (pay_ty != .unit_ty and !pay_ty.isError()) {
                        if (out_store) |store_ptr| {
                            const pay_ptr = try self.advanceSymbolicPtr(slot.sym_ptr, sum_info.payload_offset);
                            const pay_slot = try self.loadTypedSlotFromMemory(pay_ptr, pay_ty);
                            const pay_repr = classifyValueRepr(
                                self.pool,
                                self.sym_table,
                                pay_ty,
                                self.options.target_layout,
                            );
                            const pay_cv = try self.slotToComptimeValue(pay_ty, pay_repr, pay_slot, store_ptr);
                            pay_const_idx = store_ptr.appendConst(pay_cv) catch return error.OutOfMemory;
                        }
                    }
                    return .{
                        .variant = .{
                            .type_id = raw_ty,
                            .tag_ordinal = tag_ord,
                            .payload_const_idx = pay_const_idx,
                        },
                    };
                },
                .tuple_ty, .struct_ty, .array_ty => {
                    const store_ptr = out_store orelse return .unit_val;
                    var elem_indices: std.ArrayListUnmanaged(u32) = .empty;
                    defer elem_indices.deinit(self.allocator);

                    if (ty_node.tag == .array_ty) {
                        const elem_ty = self.pool.unwrapUnderlyingType(TypeId.fromInt(ty_node.lhs));
                        const arr_len: u32 = ty_node.rhs & ~type_system.SYMBOLIC_ARRAY_LEN_FLAG;
                        const elem_lay = type_system.computeTypeLayoutWithPool(
                            self.pool,
                            self.sym_table,
                            elem_ty,
                            self.options.target_layout,
                        );
                        const elem_repr = classifyValueRepr(
                            self.pool,
                            self.sym_table,
                            elem_ty,
                            self.options.target_layout,
                        );
                        for (0..arr_len) |elem_i| {
                            const off = try self.mulOffsetChecked(elem_i, elem_lay.byte_size);
                            const elem_ptr = try self.advanceSymbolicPtr(slot.sym_ptr, off);
                            const elem_slot = try self.loadTypedSlotFromMemory(elem_ptr, elem_ty);
                            const elem_cv = try self.slotToComptimeValue(elem_ty, elem_repr, elem_slot, store_ptr);
                            const c_idx = store_ptr.appendConst(elem_cv) catch return error.OutOfMemory;
                            elem_indices.append(self.allocator, c_idx) catch return error.OutOfMemory;
                        }
                    } else {
                        const is_packed_agg = isPackedStructType(self.pool, self.sym_table, ty);
                        var ord: u32 = 0;
                        while (computeCompositeFieldOffsetAndType(
                            self.pool,
                            self.sym_table,
                            ty,
                            ord,
                            self.options.target_layout,
                        )) |f_info| : (ord += 1) {
                            const f_ptr = try self.advanceSymbolicPtr(slot.sym_ptr, f_info.byte_offset);
                            const f_slot = try self.loadTypedSlotFromMemoryAligned(f_ptr, f_info.field_ty, is_packed_agg);
                            const f_repr = classifyValueRepr(
                                self.pool,
                                self.sym_table,
                                f_info.field_ty,
                                self.options.target_layout,
                            );
                            const f_cv = try self.slotToComptimeValue(f_info.field_ty, f_repr, f_slot, store_ptr);
                            const c_idx = store_ptr.appendConst(f_cv) catch return error.OutOfMemory;
                            elem_indices.append(self.allocator, c_idx) catch return error.OutOfMemory;
                        }
                    }

                    const elem_start: u32 = @intCast(store_ptr.const_elements.items.len);
                    store_ptr.const_elements.appendSlice(
                        store_ptr.allocator,
                        elem_indices.items,
                    ) catch return error.OutOfMemory;
                    return .{
                        .aggregate = .{
                            .type_id = raw_ty,
                            .elem_start = elem_start,
                            .elem_len = @intCast(elem_indices.items.len),
                        },
                    };
                },
                else => {},
            }
        }
        return .unit_val;
    }
};

// ------------ HIR Comptime Evaluation Hook Adapter ------------

/// Converts an `AttrArgValue` into a `hir.ComptimeValue`.
fn convertAttrArgValue(arg_val: AttrArgValue, field_ty: TypeId) ComptimeValue {
    return switch (arg_val) {
        .bool_val => |flag| .{ .bool_val = flag },
        .char_val => |cp| .{ .char_val = cp },
        .int_val => |int_v| .{ .int_val = int_v },
        .float_val => |flt_v| .{ .float_val = flt_v },
        .str_val => |sym_id| .{ .str_val = sym_id },
        .enum_tag => |tag_ord| .{
            .variant = .{
                .type_id = field_ty,
                .tag_ordinal = tag_ord,
                .payload_const_idx = std.math.maxInt(u32),
            },
        },
        .none_opt => .{
            .variant = .{
                .type_id = field_ty,
                .tag_ordinal = 0,
                .payload_const_idx = std.math.maxInt(u32),
            },
        },
    };
}

/// Evaluates an arbitrary lowered `hir_id` subtree inside `source_store` using `MirVm` (`DR-05` §3).
///
/// Clones `source_store` into a scratch `HirStore`, wraps `hir_id` into a synthetic zero-argument
/// `HirFnMeta` (remapping any local bindings inside `hir_id` onto contiguous local slots), lowers
/// all functions in `source_store` + the wrapper via `mir.lowerHirFnToMir`, executes `MirVm`, and
/// copies any aggregate `const_pool` / `const_elements` entries into `out_const_store` when provided.
pub fn evalHirSubtreeWithMirVm(
    allocator: std.mem.Allocator,
    source_store: *const HirStore,
    hir_id: HirIndex,
    expected_ty: TypeId,
    interner: *StringInterner,
    pool: *InternPool,
    sym_table: *const SymbolTable,
    rodata_pool: *RodataPool,
    memo_cache: ?*PureCallMemoCache,
    diagnostic_sink: ?*DiagnosticSink,
    options: VmExecOptions,
    out_const_store: ?*HirStore,
) !?ComptimeValue {
    if (hir_id.isNone() or hir_id.asInt() >= source_store.nodes.len) return null;

    var temp_store = HirStore.init(allocator, source_store.file_id);
    temp_store.target_layout = options.target_layout;
    defer temp_store.deinit();

    // Copy nodes, origins, extra_data, patterns, match_arms, locals, functions, and const pools:
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

    const expr_node = temp_store.getNode(hir_id);
    const resolved_ret_ty = if (!expected_ty.isError()) expected_ty else expr_node.type_id;
    if (resolved_ret_ty.isError()) return null;

    // Synthesize `return_local_id` and remap any locals referenced inside `hir_id` into contiguous slots:
    const ret_local_id = try temp_store.appendLocal(.{
        .name = .empty,
        .type_id = resolved_ret_ty,
        .decl_span = Span.init(source_store.file_id, 0, 0),
        .mode = .let_mode,
        .is_mut = true,
        .is_temp = true,
    });

    var local_remap: std.AutoHashMapUnmanaged(u32, u32) = .empty;
    defer local_remap.deinit(allocator);
    var visited_nodes: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited_nodes.deinit(allocator);
    try remapSubtreeLocalsForWrapper(allocator, &temp_store, hir_id, &local_remap, &visited_nodes);

    const total_locals: u32 = @intCast(temp_store.locals.items.len - ret_local_id);
    const wrapper_fn_ty = try pool.internFn(.fn_ty, &.{}, &.{}, resolved_ret_ty, false);
    const wrapper_meta = HirFnMeta{
        .def_id = .NONE,
        .symbol_index = .none,
        .name = .empty,
        .fn_ty = wrapper_fn_ty,
        .ret_ty = resolved_ret_ty,
        .return_local_id = ret_local_id,
        .param_local_start = ret_local_id + 1,
        .param_len = 0,
        .total_local_len = total_locals,
        .body_hir = hir_id,
        .is_comptime = true,
    };

    var helper_bodies: std.ArrayListUnmanaged(MirBody) = .empty;
    defer {
        for (helper_bodies.items) |*hb| hb.deinit();
        helper_bodies.deinit(allocator);
    }

    for (source_store.functions.items) |fn_meta| {
        if (fn_meta.body_hir.isNone() or fn_meta.is_subscript) continue;
        var lowered_fn = mir.lowerHirFnToMir(
            allocator,
            &temp_store,
            fn_meta,
            pool,
            sym_table,
            interner,
            diagnostic_sink,
        ) catch return null;
        errdefer lowered_fn.deinit();
        try helper_bodies.append(allocator, lowered_fn);
    }

    var wrapper_body = mir.lowerHirFnToMir(
        allocator,
        &temp_store,
        wrapper_meta,
        pool,
        sym_table,
        interner,
        diagnostic_sink,
    ) catch return null;
    defer wrapper_body.deinit();

    var vm = try MirVm.init(
        allocator,
        interner,
        pool,
        sym_table,
        rodata_pool,
        memo_cache,
        diagnostic_sink,
        options,
    );
    defer vm.deinit();

    var helper_cursor: usize = 0;
    for (source_store.functions.items) |fn_meta| {
        if (fn_meta.body_hir.isNone() or fn_meta.is_subscript) continue;
        _ = try vm.registerBody(&helper_bodies.items[helper_cursor], fn_meta.symbol_index);
        helper_cursor += 1;
    }

    const eval_res = vm.evalBody(&wrapper_body, &.{}) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Cancelled => return error.Cancelled,
        error.EvaluationCycle => return error.EvaluationCycle,
        else => return null,
    };
    return vm.resultToComptimeValue(eval_res, out_const_store) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Cancelled => return error.Cancelled,
        error.EvaluationCycle => return error.EvaluationCycle,
        else => return null,
    };
}

/// Walks a cloned `HirStore` subtree and remaps local slots onto contiguous `[return_local_id + 1 ..]` slots.
fn remapSubtreeLocalsForWrapper(
    allocator: std.mem.Allocator,
    store: *HirStore,
    hir_id: HirIndex,
    remap: *std.AutoHashMapUnmanaged(u32, u32),
    visited: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    if (hir_id.isNone() or hir_id.asInt() >= store.nodes.len) return;
    if (visited.contains(hir_id.asInt())) return;
    try visited.put(allocator, hir_id.asInt(), {});

    var node = store.getNode(hir_id);
    switch (node.tag) {
        .hir_local_decl => {
            const mapped = try getOrCloneWrapperLocal(allocator, store, node.data.lhs, remap);
            node.data.lhs = mapped;
            store.nodes.set(hir_id.asInt(), node);
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.rhs), remap, visited);
        },
        .hir_var_ref => {
            const mapped = try getOrCloneWrapperLocal(allocator, store, node.data.lhs, remap);
            node.data.lhs = mapped;
            store.nodes.set(hir_id.asInt(), node);
        },
        .hir_block => {
            const stmts = try allocator.dupe(u32, store.getLenPrefixedExtra(node.data.lhs));
            defer allocator.free(stmts);
            for (stmts) |raw_stmt| {
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(raw_stmt), remap, visited);
            }
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.rhs), remap, visited);
        },
        .hir_binary_op => {
            if (node.data.lhs + 2 <= store.extra_data.items.len) {
                const left_id = store.extra_data.items[node.data.lhs];
                const right_id = store.extra_data.items[node.data.lhs + 1];
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(left_id), remap, visited);
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(right_id), remap, visited);
            }
        },
        .hir_unary_op, .hir_project_arg, .hir_defer => {
            if (node.tag == .hir_defer and (node.data.lhs >> 1) > 0) {
                const old_err = (node.data.lhs >> 1) - 1;
                const new_err = try getOrCloneWrapperLocal(allocator, store, old_err, remap);
                node.data.lhs = ((new_err + 1) << 1) | (node.data.lhs & 1);
                store.nodes.set(hir_id.asInt(), node);
            }
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.rhs), remap, visited);
        },
        .hir_field_proj, .hir_bitfield_read, .hir_cast, .hir_return, .hir_yield, .hir_loop, .hir_break => {
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.lhs), remap, visited);
        },
        .hir_index_proj, .hir_assign => {
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.lhs), remap, visited);
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.rhs), remap, visited);
        },
        .hir_soa_field_ptr, .hir_bitfield_rmw => {
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.lhs), remap, visited);
            if (node.data.rhs + 2 <= store.extra_data.items.len) {
                const sub_id = store.extra_data.items[node.data.rhs + 1];
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(sub_id), remap, visited);
            }
        },
        .hir_call, .hir_subscript_call => {
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.lhs), remap, visited);
            const args = try allocator.dupe(u32, store.getLenPrefixedExtra(node.data.rhs));
            defer allocator.free(args);
            for (args) |raw_arg| {
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(raw_arg), remap, visited);
            }
        },
        .hir_intrinsic_call, .hir_construct => {
            const kind_check = node.tag == .hir_construct and
                @as(u8, @truncate(node.data.lhs)) == @backingInt(hir.HirConstructKind.array_repeat);
            if (kind_check) {
                if (node.data.rhs + 2 <= store.extra_data.items.len) {
                    const elem_id = store.extra_data.items[node.data.rhs + 1];
                    try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(elem_id), remap, visited);
                }
            } else {
                const items = try allocator.dupe(u32, store.getLenPrefixedExtra(node.data.rhs));
                defer allocator.free(items);
                for (items) |raw_item| {
                    try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(raw_item), remap, visited);
                }
            }
        },
        .hir_if => {
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.lhs), remap, visited);
            if (node.data.rhs + 2 <= store.extra_data.items.len) {
                const then_id = store.extra_data.items[node.data.rhs];
                const else_id = store.extra_data.items[node.data.rhs + 1];
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(then_id), remap, visited);
                try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(else_id), remap, visited);
            }
        },
        .hir_match => {
            try remapSubtreeLocalsForWrapper(allocator, store, HirIndex.fromInt(node.data.lhs), remap, visited);
            if (node.data.rhs + 2 <= store.extra_data.items.len) {
                const arm_start = store.extra_data.items[node.data.rhs];
                const arm_len = store.extra_data.items[node.data.rhs + 1];
                for (0..arm_len) |arm_off| {
                    const arm = store.match_arms.items[arm_start + arm_off];
                    try remapPatternLocalsForWrapper(allocator, store, arm.pat_idx, remap);
                    try remapSubtreeLocalsForWrapper(allocator, store, arm.guard_hir, remap, visited);
                    try remapSubtreeLocalsForWrapper(allocator, store, arm.body_hir, remap, visited);
                }
            }
        },
        else => {},
    }
}

/// Remaps `.bind` pattern local slots inside `store.patterns[pat_idx]`.
fn remapPatternLocalsForWrapper(
    allocator: std.mem.Allocator,
    store: *HirStore,
    pat_idx: u32,
    remap: *std.AutoHashMapUnmanaged(u32, u32),
) !void {
    if (pat_idx >= store.patterns.items.len) return;
    var pat = store.patterns.items[pat_idx];
    switch (pat.kind) {
        .bind => |*bind_rec| {
            bind_rec.local_id = try getOrCloneWrapperLocal(allocator, store, bind_rec.local_id, remap);
            store.patterns.items[pat_idx] = pat;
        },
        .tuple => |tup| {
            const subs = try allocator.dupe(u32, store.extra_data.items[tup.sub_start .. tup.sub_start + tup.sub_len]);
            defer allocator.free(subs);
            for (subs) |sub_idx| try remapPatternLocalsForWrapper(allocator, store, sub_idx, remap);
        },
        .struct_pat => |sp| {
            const pairs = try allocator.dupe(
                u32,
                store.extra_data.items[sp.field_start .. sp.field_start + sp.field_len * 2],
            );
            defer allocator.free(pairs);
            var pair_i: usize = 0;
            while (pair_i + 1 < pairs.len) : (pair_i += 2) {
                try remapPatternLocalsForWrapper(allocator, store, pairs[pair_i + 1], remap);
            }
        },
        .variant => |vp| {
            const subs = try allocator.dupe(u32, store.extra_data.items[vp.sub_start .. vp.sub_start + vp.sub_len]);
            defer allocator.free(subs);
            for (subs) |sub_idx| try remapPatternLocalsForWrapper(allocator, store, sub_idx, remap);
        },
        .or_pat => |op| {
            try remapPatternLocalsForWrapper(allocator, store, op.lhs_pat, remap);
            try remapPatternLocalsForWrapper(allocator, store, op.rhs_pat, remap);
        },
        else => {},
    }
}

/// Clones `old_local_id` into a fresh slot at the end of `store.locals` on first encounter.
fn getOrCloneWrapperLocal(
    allocator: std.mem.Allocator,
    store: *HirStore,
    old_local_id: u32,
    remap: *std.AutoHashMapUnmanaged(u32, u32),
) !u32 {
    if (remap.get(old_local_id)) |existing| return existing;
    const orig_decl = if (old_local_id < store.locals.items.len)
        store.locals.items[old_local_id]
    else
        hir.HirLocalDecl{
            .type_id = .unit_ty,
            .decl_span = Span.init(store.file_id, 0, 0),
        };
    const new_id = try store.appendLocal(.{
        .name = orig_decl.name,
        .type_id = orig_decl.type_id,
        .decl_span = orig_decl.decl_span,
        .mode = .let_mode,
        .is_mut = orig_decl.is_mut,
        .is_param = false,
        .is_temp = orig_decl.is_temp,
        .is_comptime = orig_decl.is_comptime,
        .symbol_index = orig_decl.symbol_index,
    });
    try remap.put(allocator, old_local_id, new_id);
    return new_id;
}

/// Constructs a `hir.ComptimeEvalHook` bound to `compiler_db` (`CompilerDb` Phase 5 integration).
pub fn makeComptimeEvalHook(
    compiler_db: ?*query_db.CompilerDb,
    session_id: u32,
) ComptimeEvalHook {
    return .{
        .compiler_db = compiler_db,
        .session_id = session_id,
        .eval_hir_fn = hookEvalHirBridge,
        .eval_const_def_fn = hookEvalConstDefBridge,
    };
}

/// `ComptimeEvalHook.eval_hir_fn` callback forwarding Tier-2 `comptime` subtrees into `MirVm`.
fn hookEvalHirBridge(
    maybe_db: ?*query_db.CompilerDb,
    session_id: u32,
    store: *const HirStore,
    hir_id: HirIndex,
    expected_ty: TypeId,
    sink: ?*DiagnosticSink,
) anyerror!?ComptimeValue {
    _ = session_id;
    const db = maybe_db orelse return null;
    // Note: `store` is mutably owned by the active `HirLowerer` when `eval_hir_fn` fires (`hir.zig:4450`),
    // allowing aggregate constant elements to be interned into `const_pool` when needed:
    const mutable_store: *HirStore = @constCast(store);
    return db.evalHirExprInVm(mutable_store, hir_id, expected_ty, sink);
}

/// `ComptimeEvalHook.eval_const_def_fn` callback resolving cross-module `const` `DefId`s via `CompilerDb`.
fn hookEvalConstDefBridge(
    maybe_db: ?*query_db.CompilerDb,
    session_id: u32,
    def_id: DefId,
    expected_ty: TypeId,
    sink: ?*DiagnosticSink,
) anyerror!?ComptimeValue {
    _ = session_id;
    _ = expected_ty;
    const db = maybe_db orelse return null;
    return db.evalComptimeDefValue(def_id, sink);
}

// ---------------------------------------- MAIN -----------------------------------------

test "MirVm layout invariants and disjoint ComptimeAllocId domains" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(ComptimeAllocId));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(SymbolicPtr));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(RegSlot));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(ProvenanceEntry));

    const vm_id = ComptimeAllocId.fromVmIndex(42);
    const rodata_id = ComptimeAllocId.fromRodataIndex(42);
    const str_id = ComptimeAllocId.fromStringId(SymbolId.fromInt(42));
    const fn_id = ComptimeAllocId.fromFnIndex(42);

    try std.testing.expectEqual(AllocDomain.vm_alloc, vm_id.domain());
    try std.testing.expectEqual(AllocDomain.rodata_blob, rodata_id.domain());
    try std.testing.expectEqual(AllocDomain.string_lit, str_id.domain());
    try std.testing.expectEqual(AllocDomain.fn_or_none, fn_id.domain());

    try std.testing.expect(!vm_id.isNullOrNone());
    try std.testing.expect(ComptimeAllocId.null_ptr.isNullOrNone());
    try std.testing.expect(ComptimeAllocId.none.isNullOrNone());
    try std.testing.expect(fn_id.isFnAddr());
    try std.testing.expect(!ComptimeAllocId.none.isFnAddr());

    try std.testing.expectEqual(@as(u32, 42), vm_id.payloadIndex());
    try std.testing.expectEqual(@as(u32, 42), rodata_id.payloadIndex());
    try std.testing.expectEqual(@as(u32, 42), str_id.payloadIndex());
    try std.testing.expectEqual(@as(u32, 42), fn_id.payloadIndex());

    const quiet_f64 = canonicalizeF64(std.math.nan(f64));
    try std.testing.expectEqual(@as(u64, CANONICAL_F64_QNAN_BITS), @as(u64, @bitCast(quiet_f64)));
    const quiet_f32_slot = packF32Slot(std.math.nan(f32));
    try std.testing.expectEqual(@as(u64, CANONICAL_F32_QNAN_BITS), quiet_f32_slot.scalar_u64);
}

test "MirVm executes loops, inout/set mutation, >8B aggregates, memoization, and rodata promotion" {
    const allocator = std.testing.allocator;
    const source =
        \\pub struct Pair {
        \\    pub tag: u8,
        \\    pub total: i64,
        \\}
        \\
        \\pub fn bump(mut acc: inout i64, step: i64) {
        \\    acc = acc + step;
        \\}
        \\
        \\pub fn build_pair(limit: i64) -> Pair {
        \\    var sum: i64 = 0;
        \\    var idx: i64 = 1;
        \\    while idx <= limit {
        \\        bump(sum, idx);
        \\        idx = idx + 1;
        \\    }
        \\    return Pair { tag: 7, total: sum };
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(1),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var memo_cache = PureCallMemoCache.init(allocator);
    defer memo_cache.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        &memo_cache,
        &bundle.hir_bundle.diagnostics,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm.deinit();

    var build_pair_idx: ?usize = null;
    for (bundle.mir_bundle.bodies.items, 0..) |*body_ptr, idx| {
        _ = try vm.registerBody(body_ptr, .none);
        const fn_name = bundle.hir_bundle.interner.get(body_ptr.name);
        if (std.mem.eql(u8, fn_name, "build_pair")) build_pair_idx = idx;
    }
    const target_body = &bundle.mir_bundle.bodies.items[build_pair_idx.?];
    const limit_arg = [_]RegSlot{.{ .scalar_i64 = 10 }};

    const res_one = try vm.evalBody(target_body, &limit_arg);
    const res_two = try vm.evalBody(target_body, &limit_arg);
    try std.testing.expectEqual(@as(u64, 1), memo_cache.hit_count);

    // Promote both results to `.rodata`; native-reordered `Pair` places `total: i64` (`55`) at `0..8`,
    // `tag: u8` (`7`) at `8`, and deterministically zeroes trailing padding bytes `9..16`:
    const blob_one = try vm.promoteResultToRodata(res_one);
    const blob_two = try vm.promoteResultToRodata(res_two);
    try std.testing.expectEqual(blob_one.asInt(), blob_two.asInt());

    const blob = rodata_pool.getBlob(blob_one.payloadIndex()).?;
    try std.testing.expectEqual(@as(usize, 16), blob.bytes.len);
    try std.testing.expectEqual(@as(i64, 55), std.mem.readInt(i64, blob.bytes[0..8], .little));
    try std.testing.expectEqual(@as(u8, 7), blob.bytes[8]);
    for (blob.bytes[9..16]) |pad_byte| {
        try std.testing.expectEqual(@as(u8, 0), pad_byte);
    }
}

test "MirVm TargetLayout NATIVE_64 vs WASM32 usize width and provenance traps" {
    const allocator = std.testing.allocator;
    const source =
        \\pub fn max_plus_wrap() -> usize {
        \\    let base: usize = 4294967295;
        \\    return base +% 1;
        \\}
    ;

    var bundle_64 = try mir.lowerSourceToMir(allocator, FileId.fromInt(2), source, TargetLayout.NATIVE_64, .{});
    defer bundle_64.deinit();
    var bundle_32 = try mir.lowerSourceToMir(allocator, FileId.fromInt(3), source, TargetLayout.WASM32, .{});
    defer bundle_32.deinit();

    var rodata_64 = RodataPool.init(allocator);
    defer rodata_64.deinit();
    var vm_64 = try MirVm.init(
        allocator,
        &bundle_64.hir_bundle.interner,
        &bundle_64.hir_bundle.pool,
        &bundle_64.hir_bundle.sym_table,
        &rodata_64,
        null,
        &bundle_64.hir_bundle.diagnostics,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm_64.deinit();
    const res_64 = try vm_64.evalBody(&bundle_64.mir_bundle.bodies.items[0], &.{});
    try std.testing.expectEqual(@as(u64, 4294967296), res_64.slot.scalar_u64);

    var rodata_32 = RodataPool.init(allocator);
    defer rodata_32.deinit();
    var vm_32 = try MirVm.init(
        allocator,
        &bundle_32.hir_bundle.interner,
        &bundle_32.hir_bundle.pool,
        &bundle_32.hir_bundle.sym_table,
        &rodata_32,
        null,
        &bundle_32.hir_bundle.diagnostics,
        .{ .target_layout = TargetLayout.WASM32 },
    );
    defer vm_32.deinit();
    const res_32 = try vm_32.evalBody(&bundle_32.mir_bundle.bodies.items[0], &.{});
    try std.testing.expectEqual(@as(u64, 0), res_32.slot.scalar_u64);

    // Direct provenance & uninitialized memory checks on `vm_64`:
    const slot_alloc = try vm_64.allocMemory(16, 3, true, false, false, 0, Span.init(FileId.fromInt(2), 0, 0));
    const base_ptr = SymbolicPtr{ .alloc_id = slot_alloc, .byte_offset = 0 };
    var uninit_buf: [8]u8 = undefined;
    try std.testing.expectError(error.UninitializedRead, vm_64.readScalarBytes(base_ptr, 3, &uninit_buf));
    try std.testing.expectError(error.OutOfBounds, vm_64.readScalarBytes(
        .{ .alloc_id = slot_alloc, .byte_offset = 12 },
        0,
        &uninit_buf,
    ));

    // Write valid pointer at offset 0, then clobber byte 3 with scalar write (`E0503` provenance erased):
    const target_alloc = try vm_64.allocMemory(8, 3, true, false, true, 0, Span.init(FileId.fromInt(2), 0, 0));
    const target_ptr = SymbolicPtr{ .alloc_id = target_alloc, .byte_offset = 0 };
    try vm_64.writePointerAt(base_ptr, 3, target_ptr);
    try std.testing.expectError(error.ForbiddenOperation, vm_64.readScalarBytes(base_ptr, 3, &uninit_buf));
    try vm_64.writeScalarBytes(.{ .alloc_id = slot_alloc, .byte_offset = 3 }, 0, &.{0xAA});
    try std.testing.expectError(error.ForbiddenOperation, vm_64.readPointerAt(base_ptr, 3));
}

test "MirVm traps E0501 step budget with stack trace, E0502 overflow, E0507 div zero, E0510 assert, and reflection" {
    const allocator = std.testing.allocator;
    const trap_source =
        \\pub fn spin_inner(count: i64) -> i64 {
        \\    var cur: i64 = count;
        \\    while cur > 0 {
        \\        cur = cur + 1;
        \\    }
        \\    return cur;
        \\}
        \\
        \\pub fn spin_outer() -> i64 {
        \\    return spin_inner(1);
        \\}
        \\
        \\pub fn trigger_overflow(val: i64) -> i64 {
        \\    return val + 1;
        \\}
        \\
        \\pub fn trigger_div_zero(num: i64, den: i64) -> i64 {
        \\    return num / den;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(4),
        trap_source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();

    // [1] Step budget `E0501` with multi-frame `LabeledSpan` trace + `--comptime-limit` help:
    var sink_step = DiagnosticSink.init(allocator);
    defer sink_step.deinit();
    var vm_step = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink_step,
        .{ .step_budget = 64 },
    );
    defer vm_step.deinit();

    var outer_idx: usize = 0;
    var ovf_idx: usize = 0;
    var div_idx: usize = 0;
    for (bundle.mir_bundle.bodies.items, 0..) |*body_ptr, idx| {
        _ = try vm_step.registerBody(body_ptr, .none);
        const name = bundle.hir_bundle.interner.get(body_ptr.name);
        if (std.mem.eql(u8, name, "spin_outer")) outer_idx = idx;
        if (std.mem.eql(u8, name, "trigger_overflow")) ovf_idx = idx;
        if (std.mem.eql(u8, name, "trigger_div_zero")) div_idx = idx;
    }

    try std.testing.expectError(
        error.StepLimitExceeded,
        vm_step.evalBody(&bundle.mir_bundle.bodies.items[outer_idx], &.{}),
    );
    try std.testing.expect(sink_step.diagnostics.items.len >= 1);
    const step_diag = sink_step.diagnostics.items[0];
    try std.testing.expectEqual(DiagnosticCode.e0501_comptime_step_limit_exceeded, step_diag.code);
    try std.testing.expect(step_diag.notes.len >= 1);
    try std.testing.expect(step_diag.labels.len >= 2);

    // [2] Integer overflow `E0502` and division-by-zero `E0507`:
    var sink_arith = DiagnosticSink.init(allocator);
    defer sink_arith.deinit();
    var vm_arith = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink_arith,
        .{},
    );
    defer vm_arith.deinit();

    try std.testing.expectError(
        error.IntegerOverflow,
        vm_arith.evalBody(
            &bundle.mir_bundle.bodies.items[ovf_idx],
            &.{.{ .scalar_i64 = std.math.maxInt(i64) }},
        ),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0502_integer_constant_overflow,
        sink_arith.diagnostics.items[0].code,
    );

    try std.testing.expectError(
        error.ArithmeticTrap,
        vm_arith.evalBody(
            &bundle.mir_bundle.bodies.items[div_idx],
            &.{ .{ .scalar_i64 = 10 }, .{ .scalar_i64 = 0 } },
        ),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0507_comptime_arithmetic_trap,
        sink_arith.diagnostics.items[1].code,
    );

    // [3] `@embed_bytes` sandbox rejection (`..` and drive letters -> `E0503`) & VFS success, plus reflection:
    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(allocator);
    try vfs_map.put(allocator, "assets/magic.bin", "COREX");

    var vm_refl = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink_arith,
        .{ .virtual_files = &vfs_map },
    );
    defer vm_refl.deinit();

    try std.testing.expectError(
        error.ForbiddenOperation,
        vm_refl.evalEmbedBytesSlot("../secret.txt", .str_ty),
    );
    try std.testing.expectError(
        error.ForbiddenOperation,
        vm_refl.evalEmbedBytesSlot("C:\\Windows\\win.ini", .str_ty),
    );
    const embed_slot = try vm_refl.evalEmbedBytesSlot("assets/magic.bin", .str_ty);
    const embed_bytes = try vm_refl.readStrSlotBytes(embed_slot);
    defer allocator.free(embed_bytes);
    try std.testing.expectEqualStrings("COREX", embed_bytes);

    const size_cv = try vm_refl.evalReflectionIntrinsic(.size_of, &.{.i64_ty}, &.{}, &.{}, null);
    try std.testing.expectEqual(@as(i128, 8), size_cv.int_val);
    const name_cv = try vm_refl.evalReflectionIntrinsic(.type_name, &.{.i64_ty}, &.{}, &.{}, null);
    try std.testing.expectEqualStrings("i64", bundle.hir_bundle.interner.get(name_cv.str_val));
}

test "test_mir_vm_pure_call_memo_pointer_offset_rodata_fn_ptr_and_slot_recycling" {
    const allocator = std.testing.allocator;
    const source =
        \\pub fn read_elem(ptr: &i64) -> i64 {
        \\    return *ptr;
        \\}
        \\
        \\pub fn inc_one(val: i64) -> i64 {
        \\    return val + 1;
        \\}
        \\
        \\pub fn inc_ten(val: i64) -> i64 {
        \\    return val + 10;
        \\}
        \\
        \\pub fn apply_cb(cb: fn(i64) -> i64, val: i64) -> i64 {
        \\    return cb(val);
        \\}
        \\
        \\pub fn pure_double(val: i64) -> i64 {
        \\    return val * 2;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(20),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var memo_cache = PureCallMemoCache.init(allocator);
    defer memo_cache.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        &memo_cache,
        &bundle.hir_bundle.diagnostics,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm.deinit();

    var read_elem_body: ?*const MirBody = null;
    var apply_cb_body: ?*const MirBody = null;
    var pure_double_body: ?*const MirBody = null;
    var inc_one_fn: ComptimeAllocId = .none;
    var inc_ten_fn: ComptimeAllocId = .none;

    for (bundle.mir_bundle.bodies.items) |*body_ptr| {
        const fn_alloc = try vm.registerBody(body_ptr, .none);
        const fn_name = bundle.hir_bundle.interner.get(body_ptr.name);
        if (std.mem.eql(u8, fn_name, "read_elem")) {
            read_elem_body = body_ptr;
        } else if (std.mem.eql(u8, fn_name, "apply_cb")) {
            apply_cb_body = body_ptr;
        } else if (std.mem.eql(u8, fn_name, "pure_double")) {
            pure_double_body = body_ptr;
        } else if (std.mem.eql(u8, fn_name, "inc_one")) {
            inc_one_fn = fn_alloc;
        } else if (std.mem.eql(u8, fn_name, "inc_ten")) {
            inc_ten_fn = fn_alloc;
        }
    }

    // [CRITICAL-01]: Same `vm_alloc` at `byte_offset = 0` (`10`) vs `byte_offset = 8` (`20`) MUST NOT collide:
    const arr_alloc = try vm.allocMemory(16, 3, true, false, false, 0, Span.init(FileId.fromInt(20), 0, 0));
    var elem0_bytes: [8]u8 = undefined;
    var elem1_bytes: [8]u8 = undefined;
    std.mem.writeInt(i64, &elem0_bytes, 10, .little);
    std.mem.writeInt(i64, &elem1_bytes, 20, .little);
    try vm.writeScalarBytes(.{ .alloc_id = arr_alloc, .byte_offset = 0 }, 3, &elem0_bytes);
    try vm.writeScalarBytes(.{ .alloc_id = arr_alloc, .byte_offset = 8 }, 3, &elem1_bytes);

    const elem0_res = try vm.evalBody(
        read_elem_body.?,
        &.{.{ .sym_ptr = .{ .alloc_id = arr_alloc, .byte_offset = 0 } }},
    );
    const elem1_res = try vm.evalBody(
        read_elem_body.?,
        &.{.{ .sym_ptr = .{ .alloc_id = arr_alloc, .byte_offset = 8 } }},
    );
    try std.testing.expectEqual(@as(i64, 10), elem0_res.slot.scalar_i64);
    try std.testing.expectEqual(@as(i64, 20), elem1_res.slot.scalar_i64);

    // [CRITICAL-01]: Distinct `.rodata_blob` pointees (`111` vs `222`) MUST NOT collide in `PureCallMemoCache`:
    var rodata_a_bytes: [8]u8 = undefined;
    var rodata_b_bytes: [8]u8 = undefined;
    std.mem.writeInt(i64, &rodata_a_bytes, 111, .little);
    std.mem.writeInt(i64, &rodata_b_bytes, 222, .little);
    const rodata_a = try rodata_pool.internBlob(&rodata_a_bytes, &.{}, 3);
    const rodata_b = try rodata_pool.internBlob(&rodata_b_bytes, &.{}, 3);

    const ro_res_a = try vm.evalBody(
        read_elem_body.?,
        &.{.{ .sym_ptr = .{ .alloc_id = rodata_a, .byte_offset = 0 } }},
    );
    const ro_res_b = try vm.evalBody(
        read_elem_body.?,
        &.{.{ .sym_ptr = .{ .alloc_id = rodata_b, .byte_offset = 0 } }},
    );
    try std.testing.expectEqual(@as(i64, 111), ro_res_a.slot.scalar_i64);
    try std.testing.expectEqual(@as(i64, 222), ro_res_b.slot.scalar_i64);

    // [CRITICAL-01]: `.fn_or_none` function-pointer arguments disable `PureCallMemoCache` insertion:
    const inserts_before_fn_ptr = memo_cache.insert_count;
    const cb_res_one = try vm.evalBody(
        apply_cb_body.?,
        &.{ .{ .sym_ptr = .{ .alloc_id = inc_one_fn, .byte_offset = 0 } }, .{ .scalar_i64 = 5 } },
    );
    const cb_res_ten = try vm.evalBody(
        apply_cb_body.?,
        &.{ .{ .sym_ptr = .{ .alloc_id = inc_ten_fn, .byte_offset = 0 } }, .{ .scalar_i64 = 5 } },
    );
    try std.testing.expectEqual(@as(i64, 6), cb_res_one.slot.scalar_i64);
    try std.testing.expectEqual(@as(i64, 15), cb_res_ten.slot.scalar_i64);
    // `apply_cb` itself was NOT memoized (`inc_one` and `inc_ten` scalar subcalls were):
    try std.testing.expectEqual(inserts_before_fn_ptr + 2, memo_cache.insert_count);

    // [MAJOR-08]: Churning `5,000` distinct pure calls recycles `free_slots` so `entries.items.len <= MAX_MEMO_ENTRIES`:
    var call_idx: i64 = 0;
    while (call_idx < 5_000) : (call_idx += 1) {
        const dbl_res = try vm.evalBody(pure_double_body.?, &.{.{ .scalar_i64 = call_idx }});
        try std.testing.expectEqual(call_idx * 2, dbl_res.slot.scalar_i64);
    }
    try std.testing.expect(memo_cache.live_count <= MAX_MEMO_ENTRIES);
    try std.testing.expect(memo_cache.entries.items.len <= MAX_MEMO_ENTRIES);
}

test "test_mir_vm_embed_bytes_rejects_dot_windows_devices_and_prefix_escapes" {
    const allocator = std.testing.allocator;
    const forbidden_paths = [_][]const u8{
        "",
        ".",
        "./secret.bin",
        "assets/./secret.bin",
        "CON",
        "con.txt",
        "PRN",
        "aux.dat",
        "NUL",
        "com1.bin",
        "LPT9.rom",
        "assets/NUL.txt",
        "assets/com4.cfg",
    };
    for (forbidden_paths) |bad_path| {
        try std.testing.expect(!isValidSandboxedEmbedPath(bad_path));
    }
    try std.testing.expect(isValidSandboxedEmbedPath("assets/icon.png"));
    try std.testing.expect(isValidSandboxedEmbedPath("assets/console.bin"));

    // Sibling-prefix directory escape (`proj` vs `proj_evil`) MUST be rejected on component boundary:
    try std.testing.expect(!isCanonicalPathWithinRoot("/ws/proj", "/ws/proj"));
    try std.testing.expect(!isCanonicalPathWithinRoot("/ws/proj", "/ws/proj_evil/secret.bin"));
    try std.testing.expect(isCanonicalPathWithinRoot("/ws/proj", "/ws/proj/assets/data.bin"));

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();
    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var diag_sink = DiagnosticSink.init(allocator);
    defer diag_sink.deinit();

    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(allocator);
    try vfs_map.put(allocator, "CON", "FORBIDDEN");
    try vfs_map.put(allocator, ".", "FORBIDDEN");

    var vm = try MirVm.init(
        allocator,
        &interner,
        &pool,
        &sym_table,
        &rodata_pool,
        null,
        &diag_sink,
        .{ .virtual_files = &vfs_map },
    );
    defer vm.deinit();

    try std.testing.expectError(error.ForbiddenOperation, vm.evalEmbedBytesSlot("CON", .str_ty));
    try std.testing.expectError(error.ForbiddenOperation, vm.evalEmbedBytesSlot(".", .str_ty));
    try std.testing.expectEqual(
        DiagnosticCode.e0326_embed_path_escape,
        diag_sink.diagnostics.items[0].code,
    );
}

test "test_mir_vm_array_repeat_provenance_linear_time_and_step_budget_e0501" {
    const allocator = std.testing.allocator;
    const source =
        \\pub fn build_repeated_refs() -> i64 {
        \\    let target_val: i64 = 77;
        \\    let big_refs: [&i64; 50000] = [&target_val; 50000];
        \\    return *big_refs[49999];
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(21),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();

    // [CRITICAL-03]: Tight step budget (`500`) traps `[&target_val; 50000]` deterministically with `E0501`:
    var sink_limited = DiagnosticSink.init(allocator);
    defer sink_limited.deinit();
    var vm_limited = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink_limited,
        .{ .step_budget = 500 },
    );
    defer vm_limited.deinit();
    try std.testing.expectError(
        error.StepLimitExceeded,
        vm_limited.evalBody(&bundle.mir_bundle.bodies.items[0], &.{}),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0501_comptime_step_limit_exceeded,
        sink_limited.diagnostics.items[0].code,
    );

    // [CRITICAL-03]: Monotonic tail fast-path completes `50,000` pointer elements in $O(N)$ linear time:
    var vm_fast = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{ .step_budget = 250_000 },
    );
    defer vm_fast.deinit();
    const fast_res = try vm_fast.evalBody(&bundle.mir_bundle.bodies.items[0], &.{});
    try std.testing.expectEqual(@as(i64, 77), fast_res.slot.scalar_i64);
}

test "test_mir_vm_advance_symbolic_ptr_u32_overflow_loop_uaf_e0506_and_alias_implements" {
    const allocator = std.testing.allocator;
    const source =
        \\type CounterAlias = i32;
        \\
        \\pub fn loop_uaf() -> i64 {
        \\    var outer_val: i64 = 100;
        \\    var saved_ref: &i64 = &outer_val;
        \\    var iter: i64 = 0;
        \\    while iter < 2 {
        \\        let inner_val: i64 = 42;
        \\        if iter == 0 {
        \\            saved_ref = &inner_val;
        \\        } else {
        \\            return *saved_ref;
        \\        }
        \\        iter = iter + 1;
        \\    }
        \\    return *saved_ref;
        \\}
        \\
        \\pub fn check_alias_implements() -> bool {
        \\    return @implements[CounterAlias, Number]();
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(22),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var diag_sink = DiagnosticSink.init(allocator);
    defer diag_sink.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &diag_sink,
        .{},
    );
    defer vm.deinit();

    // [CRITICAL-04]: `advanceSymbolicPtr` traps with `E0504` on `u32` byte-offset overflow instead of wrapping:
    const dummy_alloc = try vm.allocMemory(32, 3, true, false, true, 0, Span.init(FileId.fromInt(22), 0, 0));
    try std.testing.expectError(
        error.OutOfBounds,
        vm.advanceSymbolicPtr(.{ .alloc_id = dummy_alloc, .byte_offset = 16 }, std.math.maxInt(u32)),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0504_comptime_out_of_bounds,
        diag_sink.diagnostics.items[0].code,
    );

    // [MAJOR-06]: Loop-scoped stack local invalidated on `ghost_storage_deinit` traps with `E0506` on next iteration:
    const uaf_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "loop_uaf").?;
    try std.testing.expectError(error.InvalidPointer, vm.evalBody(uaf_body, &.{}));
    try std.testing.expectEqual(
        DiagnosticCode.e0506_comptime_invalid_pointer,
        diag_sink.diagnostics.items[1].code,
    );

    // [MINOR-09]: `@implements[CounterAlias, Number]()` unwraps `type` alias and evaluates to `true`:
    const impl_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "check_alias_implements").?;
    const impl_res = try vm.evalBody(impl_body, &.{});
    try std.testing.expectEqual(@as(u64, 1), impl_res.slot.scalar_u64);
}

test "test_mir_vm_rodata_promotion_uninit_leaf_e0505_padding_subslice_and_cycle_e0503" {
    const allocator = std.testing.allocator;
    const source =
        \\@repr(C)
        \\pub struct PaddedPair {
        \\    pub flag: u8,
        \\    pub count: u64,
        \\}
        \\
        \\pub struct NativePaddedPair {
        \\    pub flag: u8,
        \\    pub count: u64,
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(23),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var padded_ty: TypeId = .err_ty;
    var native_padded_ty: TypeId = .err_ty;
    for (bundle.hir_bundle.sym_table.symbols.items) |sym_item| {
        if (sym_item.kind == .struct_sym and std.mem.eql(u8, sym_item.name_text, "PaddedPair")) {
            padded_ty = sym_item.type_id;
        } else if (sym_item.kind == .struct_sym and std.mem.eql(u8, sym_item.name_text, "NativePaddedPair")) {
            native_padded_ty = sym_item.type_id;
        }
    }
    try std.testing.expect(!padded_ty.isError());
    try std.testing.expect(!native_padded_ty.isError());

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var diag_sink = DiagnosticSink.init(allocator);
    defer diag_sink.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &diag_sink,
        .{},
    );
    defer vm.deinit();

    // [MAJOR-07] (a): Uninitialized non-padding leaf field (`count` at offset `8..16`) MUST trap with `E0505`:
    const partial_alloc = try vm.allocMemory(16, 3, true, false, false, 0, Span.init(FileId.fromInt(23), 0, 0));
    try vm.writeScalarBytes(.{ .alloc_id = partial_alloc, .byte_offset = 0 }, 0, &.{9});
    try std.testing.expectError(
        error.UninitializedRead,
        vm.promoteSnapshotToRodata(.{ .alloc_id = partial_alloc, .byte_offset = 0 }, padded_ty),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0505_comptime_uninitialized_read,
        diag_sink.diagnostics.items[0].code,
    );

    // [MAJOR-07] (b): Initialized leaf fields with uninitialized alignment padding (`1..8`) canonicalize padding to `0`:
    @memset(vm.allocations.items[partial_alloc.payloadIndex()].bytes[1..8], 0xAA);
    var count_bytes: [8]u8 = undefined;
    std.mem.writeInt(u64, &count_bytes, 99, .little);
    try vm.writeScalarBytes(.{ .alloc_id = partial_alloc, .byte_offset = 8 }, 3, &count_bytes);
    const promoted_pair = try vm.promoteSnapshotToRodata(.{ .alloc_id = partial_alloc, .byte_offset = 0 }, padded_ty);
    const pair_blob = rodata_pool.getBlob(promoted_pair.payloadIndex()).?;
    try std.testing.expectEqual(@as(u8, 9), pair_blob.bytes[0]);
    for (pair_blob.bytes[1..8]) |pad_byte| {
        try std.testing.expectEqual(@as(u8, 0), pad_byte);
    }
    try std.testing.expectEqual(@as(u64, 99), std.mem.readInt(u64, pair_blob.bytes[8..16], .little));

    // Companion native-reordered struct (`count: u64` at `0..8`, `flag: u8` at `8`, tail pad `9..16`):
    const nat_alloc = try vm.allocMemory(16, 3, true, false, false, 0, Span.init(FileId.fromInt(23), 0, 0));
    @memset(vm.allocations.items[nat_alloc.payloadIndex()].bytes[9..16], 0xCC);
    try vm.writeScalarBytes(.{ .alloc_id = nat_alloc, .byte_offset = 0 }, 3, &count_bytes);
    try vm.writeScalarBytes(.{ .alloc_id = nat_alloc, .byte_offset = 8 }, 0, &.{7});
    const promoted_nat = try vm.promoteSnapshotToRodata(.{ .alloc_id = nat_alloc, .byte_offset = 0 }, native_padded_ty);
    const nat_blob = rodata_pool.getBlob(promoted_nat.payloadIndex()).?;
    try std.testing.expectEqual(@as(u64, 99), std.mem.readInt(u64, nat_blob.bytes[0..8], .little));
    try std.testing.expectEqual(@as(u8, 7), nat_blob.bytes[8]);
    for (nat_blob.bytes[9..16]) |pad_byte| {
        try std.testing.expectEqual(@as(u8, 0), pad_byte);
    }

    // [MAJOR-07] (c): `.string_lit` sub-slice promotion (`byte_offset = 2`, `[u8; 3]`) copies exact sub-slice bytes:
    const lit_sym = try bundle.hir_bundle.interner.intern("xxABCzz");
    const arr_u8_3 = try bundle.hir_bundle.pool.internArray(.u8_ty, 3, false);
    const sub_blob_id = try vm.promoteSnapshotToRodata(
        .{ .alloc_id = ComptimeAllocId.fromStringId(lit_sym), .byte_offset = 2 },
        arr_u8_3,
    );
    try std.testing.expectEqualStrings("ABC", rodata_pool.getBlob(sub_blob_id.payloadIndex()).?.bytes);

    // [MAJOR-07] (d): Cyclic `vm_alloc` pointer provenance graph (`node_a <-> node_b`) traps cleanly with `E0503`:
    const ptr_u8_ty = try bundle.hir_bundle.pool.internRawPtr(.u8_ty, false);
    const node_a = try vm.allocMemory(8, 3, true, false, false, 0, Span.init(FileId.fromInt(23), 0, 0));
    const node_b = try vm.allocMemory(8, 3, true, false, false, 0, Span.init(FileId.fromInt(23), 0, 0));
    try vm.writePointerAt(.{ .alloc_id = node_a, .byte_offset = 0 }, 3, .{ .alloc_id = node_b, .byte_offset = 0 });
    try vm.writePointerAt(.{ .alloc_id = node_b, .byte_offset = 0 }, 3, .{ .alloc_id = node_a, .byte_offset = 0 });
    try std.testing.expectError(
        error.ForbiddenOperation,
        vm.promoteSnapshotToRodata(.{ .alloc_id = node_a, .byte_offset = 0 }, ptr_u8_ty),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0503_forbidden_comptime_operation,
        diag_sink.diagnostics.items[1].code,
    );
}

test "test_phase6_mir_vm_narrow_wire_zero_pad_drops_subscript_defer_and_e0326" {
    const allocator = std.testing.allocator;
    const source =
        \\@zero_pad
        \\@repr(C)
        \\pub struct WirePacket {
        \\    pub tag: u8,
        \\    pub payload: u32,
        \\}
        \\pub struct TrackedLeaf {
        \\    pub id: i64,
        \\}
        \\impl TrackedLeaf {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.id);
        \\    }
        \\}
        \\pub struct TrackedPair {
        \\    pub first: TrackedLeaf,
        \\    pub second: TrackedLeaf,
        \\}
        \\impl TrackedPair {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(900);
        \\    }
        \\}
        \\pub fn run_narrow(val: i32) -> u8 {
        \\    return val.narrow[u8]();
        \\}
        \\pub fn run_try_narrow(val: i32) -> i32 {
        \\    return match val.try_narrow[u8]() {
        \\        .Some(converted) => converted as i32,
        \\        .None => -1,
        \\    };
        \\}
        \\pub fn run_wire_roundtrip(tag_in: u8, pay_in: u32) -> u32 {
        \\    let pkt = WirePacket { tag: tag_in, payload: pay_in };
        \\    let raw_slice: &[u8] = pkt.as_bytes();
        \\    let pad_sum: u32 = (raw_slice[1] as u32) + (raw_slice[2] as u32) + (raw_slice[3] as u32);
        \\    let raw_u64: u64 = @bit_cast[u64](pkt);
        \\    let back_pkt: WirePacket = @bit_cast[WirePacket](raw_u64);
        \\    let parsed_opt: WirePacket? = @from_bytes[WirePacket](raw_slice);
        \\    let viewed_opt: (&WirePacket)? = @view_bytes[WirePacket](raw_slice);
        \\    let short_bytes: [u8; 3] = [1, 2, 3];
        \\    let short_slice: &[u8] = short_bytes.as_bytes();
        \\    let short_none: WirePacket? = @from_bytes[WirePacket](short_slice);
        \\    let short_penalty: u32 = match short_none {
        \\        .Some(_) => 9999,
        \\        .None => 0,
        \\    };
        \\    return short_penalty + match parsed_opt {
        \\        .Some(parsed) => match viewed_opt {
        \\            .Some(viewed) => pad_sum + (back_pkt.tag as u32) + parsed.payload + (viewed.tag as u32),
        \\            .None => 8888,
        \\        },
        \\        .None => 7777,
        \\    };
        \\}
        \\pub fn fallible_probe(should_fail: bool) -> Result[i32, i32] {
        \\    if should_fail { return .Err(77); }
        \\    return .Ok(5);
        \\}
        \\pub subscript logged_slot(mut arr: inout [i32; 2], mut log_acc: inout i32, idx: usize) -> i32 {
        \\    defer { log_acc = log_acc * 10 + 2; }
        \\    yield arr[idx];
        \\    log_acc = log_acc * 10 + 1;
        \\}
        \\pub fn test_subscript_defer_before_errdefer(mut out_obs: inout i32) -> Result[i32, i32] {
        \\    var arr: [i32; 2] = [10, 20];
        \\    var trace_acc: i32 = 0;
        \\    errdefer { out_obs = trace_acc; }
        \\    let elem_ref: &i32 = &logged_slot(arr, trace_acc, 0);
        \\    let probed: i32 = fallible_probe(true)?;
        \\    return .Ok(*elem_ref + probed);
        \\}
        \\pub fn check_subscript_error_order() -> i32 {
        \\    var observed_in_errdefer: i32 = -1;
        \\    let outcome: i32 = match test_subscript_defer_before_errdefer(observed_in_errdefer) {
        \\        .Ok(val) => val,
        \\        .Err(_) => 0,
        \\    };
        \\    return observed_in_errdefer + outcome;
        \\}
        \\pub fn make_tracked_pair() -> i64 {
        \\    var pair = TrackedPair {
        \\        first: TrackedLeaf { id: 10 },
        \\        second: TrackedLeaf { id: 20 },
        \\    };
        \\    let pair_ref: &TrackedPair = &pair;
        \\    return pair_ref.first.id + pair_ref.second.id;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(92),
        source,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Inject `drop_in_place(pair)` into `make_tracked_pair` to exercise reverse-order destructor execution:
    for (bundle.mir_bundle.bodies.items) |*body_mut| {
        if (!std.mem.eql(u8, bundle.hir_bundle.interner.get(body_mut.name), "make_tracked_pair")) continue;
        var pair_lid: ?mir.LocalId = null;
        for (body_mut.locals.items, 0..) |loc_item, loc_idx| {
            if (loc_idx == 0 or !loc_item.flags().is_address_taken) continue;
            const node = bundle.hir_bundle.pool.getNode(bundle.hir_bundle.pool.unwrapUnderlyingType(loc_item.type_id));
            if (node.tag == .struct_ty) {
                const sym = bundle.hir_bundle.sym_table.getSymbol(SymbolIndex.fromInt(node.rhs));
                if (std.mem.eql(u8, sym.name_text, "TrackedPair")) {
                    pair_lid = mir.LocalId.fromInt(@intCast(loc_idx));
                    break;
                }
            }
        }
        if (pair_lid) |lid| {
            const pair_ty = body_mut.locals.items[lid.asInt()].type_id;
            const pair_place = PlaceId.fromInt(@intCast(body_mut.places.items.len));
            try body_mut.places.append(allocator, .{ .base = lid.asInt(), .proj_start = 0, .proj_len = 0 });
            const drop_inst = try body_mut.appendInst(.{
                .op = .intrinsic_op,
                .flags = .{ .has_side_effects = true, .is_synthetic = true },
                .aux_u16 = @backingInt(MirIntrinsicKind.drop_in_place),
                .type_id = pair_ty,
                .operands = .{ .lhs = pair_place.asInt(), .rhs = mir.NONE_U32 },
            }, .none);
            const last_bb = &body_mut.blocks.items[0];
            var insert_pos: usize = last_bb.inst_start + last_bb.inst_len;
            for (last_bb.inst_start..last_bb.inst_start + last_bb.inst_len) |scan_pos| {
                const scan_inst = body_mut.getInst(body_mut.block_insts.items[scan_pos]);
                if (scan_inst.op == .ghost_storage_deinit and scan_inst.operands.lhs == lid.asInt()) {
                    insert_pos = scan_pos;
                    break;
                }
            }
            try body_mut.block_insts.insert(allocator, insert_pos, drop_inst);
            last_bb.inst_len += 1;
        }
    }

    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink,
        .{},
    );
    defer vm.deinit();
    for (bundle.mir_bundle.bodies.items) |*body_item| {
        _ = try vm.registerBody(body_item, body_item.symbol_index);
    }

    // [1] `.narrow` & `.try_narrow`:
    const narrow_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "run_narrow").?;
    const narrow_ok = try vm.evalBody(narrow_body, &[_]RegSlot{.{ .scalar_i64 = 200 }});
    try std.testing.expectEqual(@as(u64, 200), narrow_ok.slot.scalar_u64);
    try std.testing.expectError(
        error.IntegerOverflow,
        vm.evalBody(narrow_body, &[_]RegSlot{.{ .scalar_i64 = 300 }}),
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0502_integer_constant_overflow,
        sink.diagnostics.items[0].code,
    );

    const try_narrow_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "run_try_narrow").?;
    const try_some = try vm.evalBody(try_narrow_body, &[_]RegSlot{.{ .scalar_i64 = 42 }});
    try std.testing.expectEqual(@as(i64, 42), try_some.slot.scalar_i64);
    const try_none = try vm.evalBody(try_narrow_body, &[_]RegSlot{.{ .scalar_i64 = -5 }});
    try std.testing.expectEqual(@as(i64, -1), try_none.slot.scalar_i64);

    // [2] `@zero_pad` + `.as_bytes()` + `@bit_cast` + `@from_bytes` + `@view_bytes`:
    const wire_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "run_wire_roundtrip").?;
    const wire_res = try vm.evalBody(
        wire_body,
        &[_]RegSlot{ .{ .scalar_u64 = 7 }, .{ .scalar_u64 = 100 } },
    );
    try std.testing.expectEqual(@as(u64, 0 + 7 + 100 + 7), wire_res.slot.scalar_u64);

    // [3] `Fix-06B`: `subscript` post-yield + `defer` execute BEFORE caller `errdefer` on `?` early return (`1 -> 12`):
    const sub_err_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "check_subscript_error_order").?;
    const sub_err_res = try vm.evalBody(sub_err_body, &.{});
    try std.testing.expectEqual(@as(i64, 12), sub_err_res.slot.scalar_i64);

    // [4] `drop_in_place` + `@drop_trace` outer-then-reverse-field order (`900`, `20`, `10`):
    const drop_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "make_tracked_pair").?;
    _ = try vm.evalBody(drop_body, &.{});
    try std.testing.expectEqualSlices(i64, &[_]i64{ 900, 20, 10 }, vm.asDropTraceSlice());

    // [5] Virtual heap leak ledger & `E0506` double-free / UAF traps:
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());
    const heap_ptr = try vm.allocHeapMemory(16, 3, Span.init(FileId.fromInt(92), 0, 0));
    try std.testing.expectEqual(@as(u32, 1), vm.countUnfreedHeapAllocations());
    try vm.writeScalarBytes(heap_ptr, 0, &[_]u8{ 1, 2, 3, 4 });
    try vm.freeHeapMemory(heap_ptr);
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());
    try std.testing.expectError(error.InvalidPointer, vm.freeHeapMemory(heap_ptr));
    var uaf_buf: [4]u8 = undefined;
    try std.testing.expectError(error.InvalidPointer, vm.readScalarBytes(heap_ptr, 0, &uaf_buf));

    // [6] `Fix-17` Gate D: `@embed_bytes` path escape emits `E0326`:
    sink.diagnostics.clearRetainingCapacity();
    try std.testing.expectError(error.ForbiddenOperation, vm.evalEmbedBytesSlot("../escape.bin", .str_ty));
    try std.testing.expectEqual(
        DiagnosticCode.e0326_embed_path_escape,
        sink.diagnostics.items[0].code,
    );
}

//! Core Memory, Typed Handles, Bump Arena & String Interner Foundation
//!
//! Defines the foundational 32-bit index handles, `Span` and `PackedOperand` representations,
//! deterministic 64 KiB `BumpArena` slab allocator, and `Wyhash(0)` open-addressed `StringInterner`.
//!
//! All slabs are 16-byte aligned and deterministically zero-initialized on allocation and checkpoint
//! restoration to prevent uninitialized padding bytes from leaking into serialized compiler artifacts.

const std = @import("std");

// ---------------------------------------- TYPES ----------------------------------------

// -------------------- Typed Index Handles ---------------------

/// Canonical 32-bit handle identifying a source file registered in `VfsSourceMap`.
pub const FileId = enum(u32) {
    /// Sentinel value representing no source file.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `FileId`.
    pub inline fn fromInt(index: u32) FileId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: FileId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: FileId) bool {
        return self == .none;
    }
};

/// Canonical 32-bit handle for interned UTF-8 identifiers and string literals.
pub const StringId = enum(u32) {
    /// Reserved handle `0` always resolving to the empty string `""`.
    empty = 0,
    /// Sentinel value representing no interned string.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `StringId`.
    pub inline fn fromInt(index: u32) StringId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: StringId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: StringId) bool {
        return self == .none;
    }
};

/// Canonical alias for interned symbol identifiers (`StringId`).
pub const SymbolId = StringId;

/// Canonical 32-bit index into `TokenBuffer.tokens`.
pub const TokenIndex = enum(u32) {
    /// Sentinel value representing no lexical token.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `TokenIndex`.
    pub inline fn fromInt(index: u32) TokenIndex {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: TokenIndex) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: TokenIndex) bool {
        return self == .none;
    }
};

/// Canonical alias for lexical token handles (`TokenIndex`).
pub const TokenId = TokenIndex;

/// Canonical 32-bit index into `LosslessCstArena.nodes`.
pub const CstNodeIndex = enum(u32) {
    /// Sentinel value representing no CST node.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `CstNodeIndex`.
    pub inline fn fromInt(index: u32) CstNodeIndex {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: CstNodeIndex) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: CstNodeIndex) bool {
        return self == .none;
    }
};

/// Canonical alias for concrete syntax tree node handles (`CstNodeIndex`).
pub const CstNodeId = CstNodeIndex;

/// Canonical 32-bit index into `AstArena.nodes`.
pub const NodeIndex = enum(u32) {
    /// Reserved root node index (`0`) for translation units.
    root = 0,
    /// Sentinel value representing no AST node.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `NodeIndex`.
    pub inline fn fromInt(index: u32) NodeIndex {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: NodeIndex) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: NodeIndex) bool {
        return self == .none;
    }
};

/// Canonical alias for abstract syntax tree node handles (`NodeIndex`).
pub const AstNodeId = NodeIndex;

/// Canonical 32-bit index into `AstArena.extra_data`.
pub const ExtraIndex = enum(u32) {
    /// Sentinel value representing no extra payload offset.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into an `ExtraIndex`.
    pub inline fn fromInt(index: u32) ExtraIndex {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: ExtraIndex) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: ExtraIndex) bool {
        return self == .none;
    }
};

/// Canonical 32-bit index into the High-Level IR (`HirBody`) table.
pub const HirIndex = enum(u32) {
    /// Sentinel value representing no HIR instruction.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `HirIndex`.
    pub inline fn fromInt(index: u32) HirIndex {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: HirIndex) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: HirIndex) bool {
        return self == .none;
    }
};

/// Canonical alias for HIR node handles (`HirIndex`).
pub const HirId = HirIndex;

/// Canonical 32-bit handle for lexical and semantic scopes.
pub const ScopeId = enum(u32) {
    /// Reserved root module scope (`0`).
    root = 0,
    /// Sentinel value representing no scope.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `ScopeId`.
    pub inline fn fromInt(index: u32) ScopeId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: ScopeId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: ScopeId) bool {
        return self == .none;
    }
};

/// Canonical 32-bit handle for compile-time memory regions.
pub const RegionId = enum(u32) {
    /// Reserved global static memory region (`0`).
    static_region = 0,
    /// Sentinel value representing no region.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `RegionId`.
    pub inline fn fromInt(index: u32) RegionId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: RegionId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: RegionId) bool {
        return self == .none;
    }
};

/// Canonical 32-bit handle for emitted compiler diagnostics in `DiagnosticSink`.
pub const DiagId = enum(u32) {
    /// Sentinel value representing no diagnostic.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `DiagId`.
    pub inline fn fromInt(index: u32) DiagId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: DiagId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: DiagId) bool {
        return self == .none;
    }
};

/// Canonical 32-bit handle into the `InternPool` type store (`DR-01` §4.1).
pub const TypeId = enum(u32) {
    /// Built-in `unit` type (`0`).
    unit_ty = 0,
    /// Built-in bottom `never` type (`1`).
    never_ty = 1,
    /// Built-in boolean `bool` type (`2`).
    bool_ty = 2,
    /// Built-in Unicode scalar `char` type (`3`).
    char_ty = 3,
    /// Built-in UTF-8 string slice `str` type (`4`).
    str_ty = 4,
    /// Built-in 8-bit signed integer `i8` type (`5`).
    i8_ty = 5,
    /// Built-in 16-bit signed integer `i16` type (`6`).
    i16_ty = 6,
    /// Built-in 32-bit signed integer `i32` type (`7`).
    i32_ty = 7,
    /// Built-in 64-bit signed integer `i64` type (`8`).
    i64_ty = 8,
    /// Built-in 128-bit signed integer `i128` type (`9`).
    i128_ty = 9,
    /// Built-in pointer-sized signed integer `isize` type (`10`).
    isize_ty = 10,
    /// Built-in 8-bit unsigned integer `u8` type (`11`).
    u8_ty = 11,
    /// Built-in 16-bit unsigned integer `u16` type (`12`).
    u16_ty = 12,
    /// Built-in 32-bit unsigned integer `u32` type (`13`).
    u32_ty = 13,
    /// Built-in 64-bit unsigned integer `u64` type (`14`).
    u64_ty = 14,
    /// Built-in 128-bit unsigned integer `u128` type (`15`).
    u128_ty = 15,
    /// Built-in pointer-sized unsigned integer `usize` type (`16`).
    usize_ty = 16,
    /// Built-in 32-bit IEEE-754 floating-point `f32` type (`17`).
    f32_ty = 17,
    /// Built-in 64-bit IEEE-754 floating-point `f64` type (`18`).
    f64_ty = 18,
    /// Internal untyped integer literal inference sentinel (`19`).
    untyped_int_ty = 19,
    /// Internal untyped floating-point literal inference sentinel (`20`).
    untyped_float_ty = 20,
    /// Gradual error/hole recovery type sentinel (`21`).
    err_ty = 21,
    /// Constrained type group `Signed` (`32`).
    group_signed = 32,
    /// Constrained type group `Unsigned` (`33`).
    group_unsigned = 33,
    /// Constrained type group `Integer` (`34`).
    group_integer = 34,
    /// Constrained type group `Float` (`35`).
    group_float = 35,
    /// Constrained type group `Number` (`36`).
    group_number = 36,
    /// Constrained type group `Numeric` (`37`).
    group_numeric = 37,
    /// Constrained type group `Comparable` (`38`).
    group_comparable = 38,
    /// Constrained type group `Equatable` (`39`).
    group_equatable = 39,
    /// Constrained type group `Bytes` (`40`).
    group_bytes = 40,
    /// Constrained type group `Scalar` (`41`).
    group_scalar = 41,
    /// Constrained type group `Copy` (`42`).
    group_copy = 42,
    /// First dynamically interned user/composite type index (`64`).
    first_dynamic = 64,
    /// Sentinel value representing no type.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `TypeId`.
    pub inline fn fromInt(index: u32) TypeId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: TypeId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: TypeId) bool {
        return self == .none;
    }
};

/// Canonical 32-bit handle for MIR Control-Flow Graph (`CFG`) basic blocks.
pub const MirBlockId = enum(u32) {
    /// Function entry basic block (`0`).
    entry = 0,
    /// Sentinel value representing no basic block.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `MirBlockId`.
    pub inline fn fromInt(index: u32) MirBlockId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: MirBlockId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: MirBlockId) bool {
        return self == .none;
    }
};

/// Canonical 32-bit handle for MIR SSA values and local places.
pub const MirValueId = enum(u32) {
    /// Reserved return value slot (`0`).
    return_place = 0,
    /// Sentinel value representing no MIR value.
    none = std.math.maxInt(u32),
    _,

    /// Converts a raw 32-bit integer index into a `MirValueId`.
    pub inline fn fromInt(index: u32) MirValueId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 32-bit integer value of `self`.
    pub inline fn asInt(self: MirValueId) u32 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: MirValueId) bool {
        return self == .none;
    }
};

// ------------------ Source Spans & Locations ------------------

/// Bit-packed 32-bit AST/IR operand encoding a 2-bit tag and a 30-bit dense index.
pub const PackedOperand = packed struct(u32) {
    /// Discriminant tag specifying the target table of `payload`.
    pub const Tag = enum(u2) {
        /// Empty or unused operand slot.
        none = 0,
        /// Payload indexes `AstArena.nodes` (`NodeIndex`).
        node = 1,
        /// Payload indexes `TokenBuffer.tokens` (`TokenIndex`).
        token = 2,
        /// Payload indexes `AstArena.extra_data` (`ExtraIndex`).
        extra = 3,
    };

    /// Operand category discriminant.
    tag: Tag = .none,
    /// 30-bit unsigned index payload (`0 .. 1,073,741,823`).
    payload: u30 = 0,

    /// Canonical empty operand constant.
    pub const NONE: PackedOperand = .{ .tag = .none, .payload = 0 };

    /// Packs a valid `NodeIndex` into a `PackedOperand`.
    pub inline fn initNode(node_id: NodeIndex) PackedOperand {
        std.debug.assert(!node_id.isNone());
        return .{ .tag = .node, .payload = @intCast(node_id.asInt()) };
    }

    /// Packs a valid `TokenIndex` into a `PackedOperand`.
    pub inline fn initToken(token_id: TokenIndex) PackedOperand {
        std.debug.assert(!token_id.isNone());
        return .{ .tag = .token, .payload = @intCast(token_id.asInt()) };
    }

    /// Packs a valid `ExtraIndex` into a `PackedOperand`.
    pub inline fn initExtra(extra_id: ExtraIndex) PackedOperand {
        std.debug.assert(!extra_id.isNone());
        return .{ .tag = .extra, .payload = @intCast(extra_id.asInt()) };
    }

    /// Returns true if this operand slot is `.none`.
    pub inline fn isNone(self: PackedOperand) bool {
        return self.tag == .none;
    }
};

/// Compact 8-byte MIR program point for path-sensitive SAST dataflow lattices.
pub const MirLocation = extern struct {
    /// Enclosing basic block handle.
    block: MirBlockId,
    /// Zero-based instruction index inside `block`.
    instruction_index: u32,
};

/// Canonical 12-byte half-open byte range `[start_byte .. end_byte)` within `file_id`.
pub const Span = extern struct {
    /// Source file containing this byte range.
    file_id: FileId,
    /// Inclusive starting byte offset.
    start_byte: u32,
    /// Exclusive ending byte offset (`start_byte <= end_byte`).
    end_byte: u32,

    /// Zero-length sentinel span with `FileId.none`.
    pub const ZERO: Span = .{ .file_id = .none, .start_byte = 0, .end_byte = 0 };

    /// Constructs a validated `Span` for `file_id` covering `[start_byte .. end_byte)`.
    pub inline fn init(file_id: FileId, start_byte: u32, end_byte: u32) Span {
        std.debug.assert(start_byte <= end_byte);
        return .{
            .file_id = file_id,
            .start_byte = start_byte,
            .end_byte = end_byte,
        };
    }

    /// Returns the byte length of this span (`end_byte - start_byte`).
    pub inline fn countBytes(self: Span) u32 {
        return self.end_byte - self.start_byte;
    }

    /// Returns true if `byte_offset` falls within `[start_byte .. end_byte)`.
    pub inline fn hasByte(self: Span, byte_offset: u32) bool {
        return byte_offset >= self.start_byte and byte_offset < self.end_byte;
    }

    /// Computes the minimal bounding span covering both `first` and `second` in the same file.
    pub inline fn merge(first: Span, second: Span) Span {
        std.debug.assert(first.file_id == second.file_id);
        return .{
            .file_id = first.file_id,
            .start_byte = @min(first.start_byte, second.start_byte),
            .end_byte = @max(first.end_byte, second.end_byte),
        };
    }
};

// ------------------- Arena Slab Descriptors -------------------

/// Intrusive 32-byte header placed at the start of every 16-byte-aligned `BumpArena` slab.
pub const SlabHeader = extern struct {
    /// Previous slab in the doubly-linked arena slab list.
    prev: ?*SlabHeader,
    /// Next slab in the doubly-linked arena slab list.
    next: ?*SlabHeader,
    /// Total usable payload capacity in bytes (excluding `@sizeOf(SlabHeader)`).
    capacity: usize,
    /// Payload-relative byte offset currently bumped (`0 <= used <= capacity`).
    used: usize,
};

/// Saved `BumpArena` state enabling $O(1)$ scratch memory rewind and deterministic zeroing.
pub const Checkpoint = struct {
    /// Active slab at the moment the checkpoint was recorded.
    slab: ?*SlabHeader,
    /// Payload-relative byte offset (`slab.used`) at the moment of the checkpoint.
    used: usize,
    /// Cumulative payload bytes allocated across active slabs at checkpoint time.
    total_allocated: usize,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Default usable payload capacity per standard `BumpArena` slab (64 KiB).
pub const DEFAULT_SLAB_SIZE: usize = 64 * 1024;
/// Hard upper bound on total bytes allocated in a single `BumpArena` (512 MiB).
pub const MAX_ARENA_CAPACITY: usize = 512 * 1024 * 1024;
/// Base alignment enforced for all `BumpArena` slab allocations (16 bytes).
pub const SLAB_ALIGNMENT: std.mem.Alignment = .@"16";
/// Minimum power-of-two hash bucket count for `StringInterner` initialization.
const INITIAL_INTERNER_BUCKETS: usize = 64;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns the 16-byte-aligned payload base pointer immediately following `slab`.
inline fn slabPayload(slab: *SlabHeader) [*]u8 {
    return @as([*]u8, @ptrCast(slab)) + @sizeOf(SlabHeader);
}

/// Allocates a new 16-byte-aligned slab with `payload_capacity` usable bytes, zeroed in full.
fn allocateSlab(backing_allocator: std.mem.Allocator, payload_capacity: usize) !*SlabHeader {
    const raw_memory = try backing_allocator.alignedAlloc(
        u8,
        SLAB_ALIGNMENT,
        std.math.add(usize, @sizeOf(SlabHeader), payload_capacity) catch return error.OutOfMemory,
    );
    @memset(raw_memory, 0);

    const header_ptr: *SlabHeader = @ptrCast(raw_memory.ptr);
    header_ptr.* = .{
        .prev = null,
        .next = null,
        .capacity = payload_capacity,
        .used = 0,
    };
    return header_ptr;
}

/// Frees a single `slab` previously allocated by `allocateSlab`.
fn freeSlab(backing_allocator: std.mem.Allocator, slab: *SlabHeader) void {
    backing_allocator.free(@as([*]align(16) u8, @ptrCast(@alignCast(slab)))[0 .. @sizeOf(SlabHeader) + slab.capacity]);
}

/// `std.mem.Allocator` vtable callback routing allocations into `BumpArena.allocAligned`.
fn vtableAlloc(
    context_ptr: *anyopaque,
    byte_count: usize,
    alignment: std.mem.Alignment,
    return_address: usize,
) ?[*]u8 {
    _ = return_address;
    const alignment_bytes = alignment.toByteUnits();
    if (alignment_bytes > 16) return null;
    return (@as(*BumpArena, @ptrCast(@alignCast(context_ptr))).allocAligned(byte_count, alignment_bytes) catch return null).ptr;
}

/// Computes a deterministic 32-bit folded `Wyhash` digest with seed `0`.
inline fn hashStringBytes(text: []const u8) u32 {
    const hash64 = std.hash.Wyhash.hash(0, text);
    return @truncate(hash64 ^ (hash64 >> 32));
}

comptime {
    std.debug.assert(@sizeOf(FileId) == 4);
    std.debug.assert(@sizeOf(StringId) == 4);
    std.debug.assert(@sizeOf(TokenIndex) == 4);
    std.debug.assert(@sizeOf(CstNodeIndex) == 4);
    std.debug.assert(@sizeOf(NodeIndex) == 4);
    std.debug.assert(@sizeOf(ExtraIndex) == 4);
    std.debug.assert(@sizeOf(HirIndex) == 4);
    std.debug.assert(@sizeOf(ScopeId) == 4);
    std.debug.assert(@sizeOf(RegionId) == 4);
    std.debug.assert(@sizeOf(DiagId) == 4);
    std.debug.assert(@sizeOf(TypeId) == 4);
    std.debug.assert(@sizeOf(MirBlockId) == 4);
    std.debug.assert(@sizeOf(MirValueId) == 4);
    std.debug.assert(@sizeOf(PackedOperand) == 4);
    std.debug.assert(@sizeOf(MirLocation) == 8);
    std.debug.assert(@sizeOf(Span) == 12);
    std.debug.assert(@alignOf(Span) == 4);
    if (@sizeOf(usize) == 8) {
        std.debug.assert(@sizeOf(SlabHeader) == 32);
    }
    std.debug.assert(@sizeOf(SlabHeader) % 16 == 0);
}

// ------------------------------------- PUBLIC API --------------------------------------

// -------------------- Bump Arena Allocator --------------------

/// Deterministic 64 KiB slab bump allocator with $O(1)$ checkpoint/restore and zeroed memory.
pub const BumpArena = struct {
    /// Backing page/general allocator used to allocate 16-byte-aligned slabs.
    backing_allocator: std.mem.Allocator,
    /// Head of the doubly-linked slab chain.
    first_slab: ?*SlabHeader = null,
    /// Currently active slab receiving bump allocations.
    current_slab: ?*SlabHeader = null,
    /// Cumulative payload bytes allocated across active slabs (bounded by `MAX_ARENA_CAPACITY`).
    total_allocated: usize = 0,

    /// Initializes a lazy `BumpArena` performing zero heap allocations until first use.
    pub fn init(backing_allocator: std.mem.Allocator) BumpArena {
        return .{ .backing_allocator = backing_allocator };
    }

    /// Releases all slabs in the doubly-linked chain back to `backing_allocator`.
    pub fn deinit(self: *BumpArena) void {
        var slab_cursor = self.first_slab;
        while (slab_cursor) |slab| {
            const next_slab = slab.next;
            freeSlab(self.backing_allocator, slab);
            slab_cursor = next_slab;
        }
        self.* = undefined;
    }

    /// Captures an $O(1)$ checkpoint of the current arena bump position.
    pub inline fn checkpoint(self: *const BumpArena) Checkpoint {
        return .{
            .slab = self.current_slab,
            .used = if (self.current_slab) |slab| slab.used else 0,
            .total_allocated = self.total_allocated,
        };
    }

    /// Rewinds the arena to `saved_checkpoint`, zeroing reclaimed bytes and freeing oversized slabs.
    pub fn restore(self: *BumpArena, saved_checkpoint: Checkpoint) void {
        var slab_cursor: ?*SlabHeader = null;
        if (saved_checkpoint.slab) |target_slab| {
            std.debug.assert(saved_checkpoint.used <= target_slab.used);
            @memset(slabPayload(target_slab)[saved_checkpoint.used..target_slab.used], 0);
            target_slab.used = saved_checkpoint.used;
            slab_cursor = target_slab.next;
        } else {
            slab_cursor = self.first_slab;
        }

        while (slab_cursor) |slab| {
            const next_slab = slab.next;
            if (slab.capacity > DEFAULT_SLAB_SIZE) {
                // Unlink and free oversized slab so it never lingers or orphans subsequent slabs:
                if (slab.prev) |prev_slab| {
                    prev_slab.next = next_slab;
                } else {
                    self.first_slab = next_slab;
                }
                if (next_slab) |following_slab| {
                    following_slab.prev = slab.prev;
                }
                freeSlab(self.backing_allocator, slab);
            } else if (slab.used > 0) {
                @memset(slabPayload(slab)[0..slab.used], 0);
                slab.used = 0;
            }
            slab_cursor = next_slab;
        }

        self.current_slab = saved_checkpoint.slab;
        self.total_allocated = saved_checkpoint.total_allocated;
    }

    /// Rewinds the arena to the start of `first_slab`, retaining standard slabs for reuse.
    pub fn resetRetainingCapacity(self: *BumpArena) void {
        self.restore(.{
            .slab = null,
            .used = 0,
            .total_allocated = 0,
        });
        if (self.first_slab) |head_slab| {
            std.debug.assert(head_slab.used == 0);
            self.current_slab = head_slab;
        }
    }

    /// Allocates `byte_count` zero-initialized bytes aligned to `alignment_bytes` (`<= 16`).
    pub fn allocAligned(self: *BumpArena, byte_count: usize, alignment_bytes: usize) ![]u8 {
        std.debug.assert(std.math.isPowerOfTwo(alignment_bytes));
        std.debug.assert(alignment_bytes <= 16);

        if (byte_count == 0) {
            return @as([*]align(16) u8, @ptrFromInt(16))[0..0];
        }
        if (byte_count > MAX_ARENA_CAPACITY) return error.OutOfMemory;

        // [1] Fast path; bump pointer within `current_slab` if capacity permits:
        if (self.current_slab) |active_slab| {
            const aligned_offset = std.mem.alignForward(usize, active_slab.used, alignment_bytes);
            const new_used = std.math.add(usize, aligned_offset, byte_count) catch return error.OutOfMemory;
            if (new_used <= active_slab.capacity) {
                const new_total = std.math.add(usize, self.total_allocated, new_used - active_slab.used) catch return error.OutOfMemory;
                if (new_total > MAX_ARENA_CAPACITY) return error.OutOfMemory;

                const result_slice = slabPayload(active_slab)[aligned_offset..new_used];
                @memset(result_slice, 0);
                active_slab.used = new_used;
                self.total_allocated = new_total;
                return result_slice;
            }
        }

        // [2] Reuse cached standard slab if available and large enough for `byte_count`:
        const candidate_next: ?*SlabHeader = if (self.current_slab) |active_slab|
            active_slab.next
        else
            self.first_slab;

        if (candidate_next) |reusable_slab| {
            if (byte_count <= reusable_slab.capacity) {
                const new_total = std.math.add(usize, self.total_allocated, byte_count) catch return error.OutOfMemory;
                if (new_total > MAX_ARENA_CAPACITY) return error.OutOfMemory;

                std.debug.assert(reusable_slab.used == 0);
                const result_slice = slabPayload(reusable_slab)[0..byte_count];
                @memset(result_slice, 0);
                reusable_slab.used = byte_count;
                self.current_slab = reusable_slab;
                self.total_allocated = new_total;
                return result_slice;
            }
        }

        // [3] Slow path; allocate a new standard or oversized slab and splice into list:
        const new_total = std.math.add(usize, self.total_allocated, byte_count) catch return error.OutOfMemory;
        if (new_total > MAX_ARENA_CAPACITY) return error.OutOfMemory;

        const new_slab = try allocateSlab(self.backing_allocator, @max(byte_count, DEFAULT_SLAB_SIZE));

        if (self.current_slab) |active_slab| {
            new_slab.prev = active_slab;
            new_slab.next = active_slab.next;
            if (active_slab.next) |old_next| {
                old_next.prev = new_slab;
            }
            active_slab.next = new_slab;
        } else {
            new_slab.prev = null;
            new_slab.next = self.first_slab;
            if (self.first_slab) |old_first| {
                old_first.prev = new_slab;
            }
            self.first_slab = new_slab;
        }

        new_slab.used = byte_count;
        self.current_slab = new_slab;
        self.total_allocated = new_total;
        return slabPayload(new_slab)[0..byte_count];
    }

    /// Allocates a single zero-initialized instance of `T` inside the arena.
    pub fn create(self: *BumpArena, comptime T: type) !*T {
        return &(try self.allocSlice(T, 1))[0];
    }

    /// Allocates a slice of `n` zero-initialized elements of type `T`.
    pub fn allocSlice(self: *BumpArena, comptime T: type, n: usize) ![]T {
        if (n == 0) return &[_]T{};
        if (@sizeOf(T) == 0) {
            return @as([*]T, @ptrFromInt(std.mem.alignBackward(usize, std.math.maxInt(usize), @alignOf(T))))[0..n];
        }
        const raw_bytes = try self.allocAligned(
            std.math.mul(usize, @sizeOf(T), n) catch return error.OutOfMemory,
            @alignOf(T),
        );
        return @as([*]T, @ptrCast(@alignCast(raw_bytes.ptr)))[0..n];
    }

    /// Copies `source_slice` into newly allocated arena memory.
    pub fn dupe(self: *BumpArena, comptime T: type, source_slice: []const T) ![]T {
        const cloned_slice = try self.allocSlice(T, source_slice.len);
        @memcpy(cloned_slice, source_slice);
        return cloned_slice;
    }

    /// Copies `source_bytes` into newly allocated arena memory with a trailing NUL sentinel.
    pub fn dupeZ(self: *BumpArena, source_bytes: []const u8) ![:0]u8 {
        const raw_slice = try self.allocSlice(
            u8,
            std.math.add(usize, source_bytes.len, 1) catch return error.OutOfMemory,
        );
        @memcpy(raw_slice[0..source_bytes.len], source_bytes);
        raw_slice[source_bytes.len] = 0;
        return raw_slice[0..source_bytes.len :0];
    }

    /// Returns a standard `std.mem.Allocator` interface backed by this `BumpArena`.
    pub fn asAllocator(self: *BumpArena) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = vtableAlloc,
                .resize = std.mem.Allocator.noResize,
                .remap = std.mem.Allocator.noRemap,
                .free = std.mem.Allocator.noFree,
            },
        };
    }
};

// ---------------------- String Interner -----------------------

/// Deterministic `Wyhash(0)` open-addressed string interner with NUL-terminated arena storage.
pub const StringInterner = struct {
    /// Metadata entry describing a unique interned string in `string_arena`.
    pub const EntryMeta = extern struct {
        /// Pointer to NUL-terminated UTF-8 bytes inside `string_arena`.
        ptr: [*]const u8,
        /// Byte length of the string (excluding trailing NUL byte).
        len: u32,
        /// Folded 32-bit `Wyhash(0)` digest of the string bytes.
        hash: u32,
    };

    /// Backing allocator for `entries` and the open-addressed `buckets` table.
    backing_allocator: std.mem.Allocator,
    /// Arena storing contiguous NUL-terminated UTF-8 string payloads.
    string_arena: BumpArena,
    /// Dense metadata table indexed by `StringId.asInt()`.
    entries: std.ArrayList(EntryMeta) = .empty,
    /// Power-of-two open-addressing probe table (`StringId.none` marks empty slots).
    buckets: []StringId = &[_]StringId{},

    /// Initializes the `StringInterner` and pre-interns `""` at `StringId.empty` (`0`).
    pub fn init(backing_allocator: std.mem.Allocator) !StringInterner {
        var interner = StringInterner{
            .backing_allocator = backing_allocator,
            .string_arena = BumpArena.init(backing_allocator),
        };
        errdefer interner.deinit();

        interner.buckets = try backing_allocator.alloc(StringId, INITIAL_INTERNER_BUCKETS);
        @memset(interner.buckets, .none);

        const empty_hash = hashStringBytes("");
        try interner.entries.append(backing_allocator, .{
            .ptr = (try interner.string_arena.dupeZ("")).ptr,
            .len = 0,
            .hash = empty_hash,
        });
        interner.buckets[empty_hash & (INITIAL_INTERNER_BUCKETS - 1)] = .empty;
        return interner;
    }

    /// Releases all interned string slabs, metadata entries, and hash buckets.
    pub fn deinit(self: *StringInterner) void {
        self.entries.deinit(self.backing_allocator);
        if (self.buckets.len > 0) {
            self.backing_allocator.free(self.buckets);
        }
        self.string_arena.deinit();
        self.* = undefined;
    }

    /// Interns `text` and returns its canonical `StringId` in amortized $O(\text{len})$ time.
    pub fn intern(self: *StringInterner, text: []const u8) !StringId {
        if (text.len == 0) return .empty;
        if (text.len > std.math.maxInt(u32)) return error.OutOfMemory;

        // [1] Maintain <= 70% load factor using overflow-safe 64-bit arithmetic:
        if ((@as(u64, self.entries.items.len) + 1) * 10 >= @as(u64, self.buckets.len) * 7) {
            try self.growBuckets();
        }

        // [2] Probe open-addressing table for existing string:
        const text_hash = hashStringBytes(text);
        const bucket_mask: usize = self.buckets.len - 1;
        var slot_index: usize = @as(usize, text_hash) & bucket_mask;
        while (true) {
            const candidate_id = self.buckets[slot_index];
            if (candidate_id.isNone()) break;

            const candidate_meta = self.entries.items[candidate_id.asInt()];
            if (candidate_meta.hash == text_hash and candidate_meta.len == @as(u32, @intCast(text.len))) {
                if (std.mem.eql(u8, candidate_meta.ptr[0..candidate_meta.len], text)) {
                    return candidate_id;
                }
            }
            slot_index = (slot_index + 1) & bucket_mask;
        }

        // [3] Copy NUL-terminated bytes into `string_arena` and record new `StringId`:
        if (self.entries.items.len >= std.math.maxInt(u32)) return error.OutOfMemory;
        const new_id = StringId.fromInt(@intCast(self.entries.items.len));
        try self.entries.append(self.backing_allocator, .{
            .ptr = (try self.string_arena.dupeZ(text)).ptr,
            .len = @intCast(text.len),
            .hash = text_hash,
        });
        self.buckets[slot_index] = new_id;
        return new_id;
    }

    /// Performs a read-only probe for `text`, returning its `StringId` if already interned.
    pub fn lookup(self: *const StringInterner, text: []const u8) ?StringId {
        if (text.len == 0) return .empty;
        if (text.len > std.math.maxInt(u32) or self.buckets.len == 0) return null;

        const text_hash = hashStringBytes(text);
        const bucket_mask: usize = self.buckets.len - 1;
        var slot_index: usize = @as(usize, text_hash) & bucket_mask;
        while (true) {
            const candidate_id = self.buckets[slot_index];
            if (candidate_id.isNone()) return null;

            const candidate_meta = self.entries.items[candidate_id.asInt()];
            if (candidate_meta.hash == text_hash and candidate_meta.len == @as(u32, @intCast(text.len))) {
                if (std.mem.eql(u8, candidate_meta.ptr[0..candidate_meta.len], text)) {
                    return candidate_id;
                }
            }
            slot_index = (slot_index + 1) & bucket_mask;
        }
    }

    /// Resolves `string_id` to its NUL-terminated UTF-8 slice in $O(1)$ time.
    pub inline fn get(self: *const StringInterner, string_id: StringId) [:0]const u8 {
        std.debug.assert(!string_id.isNone());
        const entry_meta = self.entries.items[string_id.asInt()];
        return entry_meta.ptr[0..entry_meta.len :0];
    }

    /// Returns the total number of unique strings currently interned (including `""`).
    pub inline fn countStrings(self: *const StringInterner) usize {
        return self.entries.items.len;
    }

    /// Doubles the open-addressing bucket table capacity and re-inserts all existing entries.
    fn growBuckets(self: *StringInterner) !void {
        const new_capacity = std.math.mul(usize, self.buckets.len, 2) catch return error.OutOfMemory;
        std.debug.assert(std.math.isPowerOfTwo(new_capacity));

        const new_buckets = try self.backing_allocator.alloc(StringId, new_capacity);
        @memset(new_buckets, .none);

        const bucket_mask: usize = new_capacity - 1;
        for (self.entries.items, 0..) |entry_meta, entry_index| {
            var slot_index: usize = @as(usize, entry_meta.hash) & bucket_mask;
            while (!new_buckets[slot_index].isNone()) {
                slot_index = (slot_index + 1) & bucket_mask;
            }
            new_buckets[slot_index] = StringId.fromInt(@intCast(entry_index));
        }

        self.backing_allocator.free(self.buckets);
        self.buckets = new_buckets;
    }
};

/// Canonical alias for the Structure-of-Arrays `AstArena` (`DR-01` Section 4.1).
pub const AstStore = @import("syntax_arenas.zig").AstArena;

// ------------------------- Unit Tests -------------------------

test "test_mem_foundation_typed_handles_and_span_invariants" {
    const file_id = FileId.fromInt(7);
    try std.testing.expect(!file_id.isNone());
    try std.testing.expectEqual(@as(u32, 7), file_id.asInt());
    try std.testing.expect(FileId.none.isNone());

    const first_span = Span.init(file_id, 10, 25);
    try std.testing.expectEqual(@as(u32, 15), first_span.countBytes());
    try std.testing.expect(first_span.hasByte(10));
    try std.testing.expect(first_span.hasByte(24));
    try std.testing.expect(!first_span.hasByte(25));

    const merged_span = Span.merge(first_span, Span.init(file_id, 20, 42));
    try std.testing.expectEqual(@as(u32, 10), merged_span.start_byte);
    try std.testing.expectEqual(@as(u32, 42), merged_span.end_byte);

    const node_op = PackedOperand.initNode(NodeIndex.fromInt(123));
    try std.testing.expect(!node_op.isNone());
    try std.testing.expectEqual(PackedOperand.Tag.node, node_op.tag);
    try std.testing.expectEqual(@as(u30, 123), node_op.payload);
}

test "test_bump_arena_checkpoint_restore_and_oversized_splicing" {
    var arena = BumpArena.init(std.testing.allocator);
    defer arena.deinit();

    const first_slice = try arena.allocAligned(128, 16);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(first_slice.ptr) % 16);
    @memset(first_slice, 0xAA);

    const saved_cp = arena.checkpoint();
    const temp_slice = try arena.allocAligned(256, 8);
    @memset(temp_slice, 0xBB);

    // Allocate an oversized slab (> 64 KiB) after the checkpoint and verify it is freed on restore:
    try std.testing.expectEqual(
        DEFAULT_SLAB_SIZE + 4096,
        (try arena.allocAligned(DEFAULT_SLAB_SIZE + 4096, 16)).len,
    );

    arena.restore(saved_cp);
    const reused_slice = try arena.allocAligned(256, 8);
    try std.testing.expectEqual(temp_slice.ptr, reused_slice.ptr);
    for (reused_slice) |byte_val| {
        try std.testing.expectEqual(@as(u8, 0), byte_val);
    }
}

test "test_string_interner_deduplication_and_empty_sentinel" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try std.testing.expectEqual(StringId.empty, try interner.intern(""));
    try std.testing.expectEqualStrings("", interner.get(.empty));
    try std.testing.expectEqual(@as(u8, 0), interner.get(.empty)[0]);

    const first_id = try interner.intern("corex_identifier");
    try std.testing.expectEqual(first_id, try interner.intern("corex_identifier"));
    try std.testing.expect(first_id != try interner.intern("other_symbol"));
    try std.testing.expectEqual(first_id, interner.lookup("corex_identifier").?);
    try std.testing.expect(interner.lookup("missing_symbol") == null);
    try std.testing.expectEqualStrings("corex_identifier", interner.get(first_id));
}

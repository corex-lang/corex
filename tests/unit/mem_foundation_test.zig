//! Unit Tests for Memory Foundation (`tests/unit/mem_foundation_test.zig`)
//!
//! Verifies the binary layout and sentinel invariants of all 32-bit typed compiler handles, `Span`,
//! `PackedOperand`, `BumpArena` 64 KiB slab chaining and checkpoint/restore, and `StringInterner`.
//!
//! All tests run under `std.testing.allocator` to guarantee zero memory leaks across normal and error paths.

const std = @import("std");
const corex = @import("corex");

const mem = corex.mem_foundation;
const FileId = corex.FileId;
const StringId = corex.StringId;
const SymbolId = corex.SymbolId;
const TokenIndex = corex.TokenIndex;
const TokenId = corex.TokenId;
const CstNodeIndex = corex.CstNodeIndex;
const CstNodeId = corex.CstNodeId;
const NodeIndex = corex.NodeIndex;
const AstNodeId = corex.AstNodeId;
const ExtraIndex = corex.ExtraIndex;
const HirIndex = corex.HirIndex;
const HirId = corex.HirId;
const ScopeId = corex.ScopeId;
const RegionId = corex.RegionId;
const DiagId = corex.DiagId;
const TypeId = corex.TypeId;
const MirBlockId = corex.MirBlockId;
const MirValueId = corex.MirValueId;
const PackedOperand = corex.PackedOperand;
const MirLocation = corex.MirLocation;
const Span = corex.Span;
const BumpArena = corex.BumpArena;
const StringInterner = corex.StringInterner;

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------- Typed Handle & Span Tests ------------------

test "test_typed_handles_roundtrip_and_sentinel_invariants" {
    // [1] Verify 32-bit size and `.none` sentinel across all canonical index handles:
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(FileId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(StringId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TokenIndex));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(CstNodeIndex));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(NodeIndex));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(ExtraIndex));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(HirIndex));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(ScopeId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(RegionId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(DiagId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TypeId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(MirBlockId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(MirValueId));

    try std.testing.expect(FileId.none.isNone());
    try std.testing.expect(SymbolId.none.isNone());
    try std.testing.expect(TokenId.none.isNone());
    try std.testing.expect(CstNodeId.none.isNone());
    try std.testing.expect(AstNodeId.none.isNone());
    try std.testing.expect(ExtraIndex.none.isNone());
    try std.testing.expect(HirId.none.isNone());
    try std.testing.expect(ScopeId.none.isNone());
    try std.testing.expect(RegionId.none.isNone());
    try std.testing.expect(DiagId.none.isNone());
    try std.testing.expect(TypeId.none.isNone());
    try std.testing.expect(MirBlockId.none.isNone());
    try std.testing.expect(MirValueId.none.isNone());

    // [2] Verify reserved zero indices and pre-interned `TypeId` constants (`DR-01` §4.1):
    try std.testing.expectEqual(@as(u32, 0), StringId.empty.asInt());
    try std.testing.expectEqual(@as(u32, 0), NodeIndex.root.asInt());
    try std.testing.expectEqual(@as(u32, 0), ScopeId.root.asInt());
    try std.testing.expectEqual(@as(u32, 0), RegionId.static_region.asInt());
    try std.testing.expectEqual(@as(u32, 0), MirBlockId.entry.asInt());
    try std.testing.expectEqual(@as(u32, 0), MirValueId.return_place.asInt());
    try std.testing.expectEqual(@as(u32, 0), TypeId.unit_ty.asInt());
    try std.testing.expectEqual(@as(u32, 21), TypeId.err_ty.asInt());
    try std.testing.expectEqual(@as(u32, 32), TypeId.group_signed.asInt());
    try std.testing.expectEqual(@as(u32, 42), TypeId.group_copy.asInt());
    try std.testing.expectEqual(@as(u32, 64), TypeId.first_dynamic.asInt());

    // [3] Verify `fromInt` / `asInt` roundtrip for non-sentinel indices:
    try std.testing.expectEqual(@as(u32, 42), FileId.fromInt(42).asInt());
    try std.testing.expect(!FileId.fromInt(42).isNone());
    try std.testing.expectEqual(@as(u32, 99), HirIndex.fromInt(99).asInt());
    try std.testing.expectEqual(@as(u32, 77), DiagId.fromInt(77).asInt());
}

test "test_packed_operand_and_span_geometry" {
    try std.testing.expect(PackedOperand.NONE.isNone());

    const max_payload: u32 = (@as(u32, 1) << 30) - 1;
    const node_operand = PackedOperand.initNode(NodeIndex.fromInt(max_payload));
    const token_operand = PackedOperand.initToken(TokenIndex.fromInt(512));
    const extra_operand = PackedOperand.initExtra(ExtraIndex.fromInt(1024));

    try std.testing.expectEqual(PackedOperand.Tag.node, node_operand.tag);
    try std.testing.expectEqual(@as(u30, @intCast(max_payload)), node_operand.payload);
    try std.testing.expectEqual(PackedOperand.Tag.token, token_operand.tag);
    try std.testing.expectEqual(@as(u30, 512), token_operand.payload);
    try std.testing.expectEqual(PackedOperand.Tag.extra, extra_operand.tag);
    try std.testing.expectEqual(@as(u30, 1024), extra_operand.payload);

    try std.testing.expectEqual(@as(usize, 8), @sizeOf(MirLocation));
    try std.testing.expectEqual(@as(u32, 17), (MirLocation{ .block = .entry, .instruction_index = 17 }).instruction_index);

    try std.testing.expect(Span.ZERO.file_id.isNone());
    try std.testing.expectEqual(@as(u32, 0), Span.ZERO.countBytes());

    const file_id = FileId.fromInt(3);
    const left_span = Span.init(file_id, 100, 120);
    try std.testing.expectEqual(@as(u32, 20), left_span.countBytes());
    try std.testing.expect(!left_span.hasByte(99));
    try std.testing.expect(left_span.hasByte(100));
    try std.testing.expect(left_span.hasByte(119));
    try std.testing.expect(!left_span.hasByte(120));

    const merged_span = Span.merge(Span.init(file_id, 115, 160), left_span);
    try std.testing.expectEqual(file_id, merged_span.file_id);
    try std.testing.expectEqual(@as(u32, 100), merged_span.start_byte);
    try std.testing.expectEqual(@as(u32, 160), merged_span.end_byte);
}

// ---------------------- BumpArena Tests -----------------------

test "test_bump_arena_lazy_init_alignments_and_zero_fill" {
    var arena = BumpArena.init(std.testing.allocator);
    defer arena.deinit();

    // [1] Lazy initialization must not allocate any slab before first request:
    try std.testing.expect(arena.first_slab == null);
    try std.testing.expect(arena.current_slab == null);
    try std.testing.expectEqual(@as(usize, 0), arena.total_allocated);

    // [2] Zero-byte allocation and zero-sized type slices must not allocate a slab:
    try std.testing.expectEqual(@as(usize, 0), (try arena.allocAligned(0, 16)).len);
    try std.testing.expect(arena.first_slab == null);

    try std.testing.expectEqual(@as(usize, 8), (try arena.allocSlice(u0, 8)).len);
    try std.testing.expect(arena.first_slab == null);

    // [3] Verify 1, 2, 4, 8, and 16-byte alignments and deterministic zero-initialization:
    for (try arena.allocAligned(3, 1)) |byte_val| try std.testing.expectEqual(@as(u8, 0), byte_val);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr((try arena.allocAligned(5, 2)).ptr) % 2);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr((try arena.allocAligned(7, 4)).ptr) % 4);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr((try arena.allocAligned(9, 8)).ptr) % 8);
    const align_16 = try arena.allocAligned(32, 16);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(align_16.ptr) % 16);
    for (align_16) |byte_val| try std.testing.expectEqual(@as(u8, 0), byte_val);
}

test "test_bump_arena_multi_slab_checkpoint_restore_and_reset" {
    var arena = BumpArena.init(std.testing.allocator);
    defer arena.deinit();

    // [1] Allocate in first standard slab and record checkpoint:
    const base_slice = try arena.allocAligned(1024, 16);
    @memset(base_slice, 0x5A);
    const saved_cp = arena.checkpoint();

    // [2] Force allocation of a second standard slab, an oversized slab, and a third standard slab:
    const second_slab_slice = try arena.allocAligned(mem.DEFAULT_SLAB_SIZE - 128, 16);
    @memset(second_slab_slice, 0xA5);

    @memset(try arena.allocAligned(mem.DEFAULT_SLAB_SIZE * 2, 16), 0xFF);
    @memset(try arena.allocAligned(4096, 16), 0x33);

    // [3] Restore to `saved_cp`; oversized slab must be freed while standard slabs remain linked and zeroed:
    arena.restore(saved_cp);
    try std.testing.expectEqual(@as(usize, 1024), arena.total_allocated);
    for (base_slice) |byte_val| {
        try std.testing.expectEqual(@as(u8, 0x5A), byte_val);
    }

    // [4] Subsequent allocation must reuse cached standard slabs with zeroed memory:
    const reused_second = try arena.allocAligned(mem.DEFAULT_SLAB_SIZE - 128, 16);
    try std.testing.expectEqual(second_slab_slice.ptr, reused_second.ptr);
    for (reused_second) |byte_val| {
        try std.testing.expectEqual(@as(u8, 0), byte_val);
    }

    // [5] `resetRetainingCapacity` must rewind to `first_slab` with `used == 0`:
    arena.resetRetainingCapacity();
    try std.testing.expectEqual(@as(usize, 0), arena.total_allocated);
    try std.testing.expect(arena.first_slab != null);
    try std.testing.expectEqual(arena.first_slab, arena.current_slab);

    const from_head = try arena.allocAligned(1024, 16);
    try std.testing.expectEqual(base_slice.ptr, from_head.ptr);
    for (from_head) |byte_val| {
        try std.testing.expectEqual(@as(u8, 0), byte_val);
    }
}

test "test_bump_arena_helpers_and_capacity_limit" {
    var arena = BumpArena.init(std.testing.allocator);
    defer arena.deinit();

    try std.testing.expectEqual(@as(u32, 0), (try arena.create(Span)).start_byte);
    try std.testing.expectEqualSlices(u32, &[_]u32{ 10, 20, 30 }, try arena.dupe(u32, &[_]u32{ 10, 20, 30 }));

    const duped_z = try arena.dupeZ("corex");
    try std.testing.expectEqualStrings("corex", duped_z);
    try std.testing.expectEqual(@as(u8, 0), duped_z[duped_z.len]);

    // Verify `asAllocator()` compatibility with `std.ArrayList`:
    var list: std.ArrayList(u64) = .empty;
    try list.append(arena.asAllocator(), 0xCAFE_BABE);
    try std.testing.expectEqual(@as(u64, 0xCAFE_BABE), list.items[0]);

    // Verify hard `MAX_ARENA_CAPACITY` (`512 MiB`) guard:
    try std.testing.expectError(error.OutOfMemory, arena.allocAligned(mem.MAX_ARENA_CAPACITY + 1, 16));
}

// -------------------- StringInterner Tests --------------------

test "test_string_interner_wyhash_dedup_and_bucket_growth" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    // [1] Empty string must always resolve to `StringId.empty` (`0`):
    try std.testing.expectEqual(@as(usize, 1), interner.countStrings());
    try std.testing.expectEqual(StringId.empty, try interner.intern(""));
    try std.testing.expectEqual(StringId.empty, interner.lookup("").?);
    try std.testing.expectEqualStrings("", interner.get(.empty));
    try std.testing.expectEqual(@as(u8, 0), interner.get(.empty)[0]);

    // [2] Intern 300 distinct symbols to force multiple `growBuckets` rehashes:
    var expected_ids: [300]StringId = undefined;
    var name_buf: [32]u8 = undefined;
    var i: usize = 0;
    while (i < expected_ids.len) : (i += 1) {
        var name_writer = std.Io.Writer.fixed(&name_buf);
        try name_writer.print("symbol_ident_{d}", .{i});
        const symbol_text = name_writer.buffered();

        try std.testing.expect(interner.lookup(symbol_text) == null);
        expected_ids[i] = try interner.intern(symbol_text);
        try std.testing.expectEqual(expected_ids[i], try interner.intern(symbol_text));
        try std.testing.expectEqual(expected_ids[i], interner.lookup(symbol_text).?);
    }

    try std.testing.expectEqual(@as(usize, 301), interner.countStrings());

    // [3] Verify all 300 symbols remain intact and NUL-terminated after table growth:
    i = 0;
    while (i < expected_ids.len) : (i += 1) {
        var name_writer = std.Io.Writer.fixed(&name_buf);
        try name_writer.print("symbol_ident_{d}", .{i});
        const resolved_slice = interner.get(expected_ids[i]);
        try std.testing.expectEqualStrings(name_writer.buffered(), resolved_slice);
        try std.testing.expectEqual(@as(u8, 0), resolved_slice[resolved_slice.len]);
    }
}

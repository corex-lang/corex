//! Unit Tests for `codegen_dev_seam.zig` & `CompilerDb` `FieldHash64` (`tests/unit/codegen_dev_seam_test.zig`)
//!
//! Verifies the `DR-19` §1 and `DR-20` Seam `#3`–`#4` Phase-7 hot-reload & SIMD metadata seam:
//! - Hard `< 200` LOC budget guard on `stage0/src/codegen_dev_seam.zig`.
//! - Binary-exact record layouts (`CxDevSeamHeader` `64B`, `CxGotSlotMeta` `24B`,
//!   `CxTypeLayoutRecord` `32B`, `CxReloadControlBlock` `64B`, `FieldHash64` `8B`, `GotSlotId` `4B`).
//! - `.cx_dev_meta` round-trip serialization, validation, and tamper rejection.
//! - `computeNominalFieldHash64` semantic sensitivity (field renames/swaps vs identical physical
//!   `LayoutShapeKey`, plus cyclic pointer termination).
//! - `CompilerDb.setTargetLayout` invalidation when `cache_line_align_log2` or `simd_align_log2` changes.

const std = @import("std");
const corex = @import("corex");

const dev_seam = corex.codegen_dev_seam;
const FileId = corex.FileId;
const DefId = corex.DefId;
const TypeId = corex.TypeId;
const FieldHash64 = corex.FieldHash64;
const GotSlotId = corex.GotSlotId;
const CompilerDb = corex.CompilerDb;
const TargetSpec = corex.TargetSpec;

// -------------------------------------- INTERNALS --------------------------------------

/// Finds a named top-level symbol in `sym_table` and returns its resolved `TypeId`.
fn findSymbolTypeId(sym_table: *const corex.SymbolTable, target_name: []const u8) !TypeId {
    for (sym_table.symbols.items) |sym_rec| {
        if (std.mem.eql(u8, sym_rec.name_text, target_name) and !sym_rec.type_id.isError()) {
            return sym_rec.type_id;
        }
    }
    return error.TestSymbolNotFound;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_codegen_dev_seam_under_200_loc_budget_and_binary_record_roundtrip" {
    // [1] Enforce strict `< 200` line budget (`<= 199` lines) on `stage0/src/codegen_dev_seam.zig`:
    const seam_src = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "stage0/src/codegen_dev_seam.zig",
        std.testing.allocator,
        .limited(64 * 1024),
    );
    defer std.testing.allocator.free(seam_src);

    var line_count: usize = 0;
    var iter = std.mem.splitScalar(u8, seam_src, '\n');
    while (iter.next()) |_| {
        line_count += 1;
    }
    // Subtract trailing empty split after final newline if present:
    if (seam_src.len > 0 and seam_src[seam_src.len - 1] == '\n' and line_count > 0) {
        line_count -= 1;
    }
    try std.testing.expect(line_count < 200);

    // [2] Verify exact byte sizes of all `DR-19` §1.2 records and typed handles:
    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.CxDevSeamHeader));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.CxGotSlotMeta));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.CxTypeLayoutRecord));
    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.CxReloadControlBlock));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(FieldHash64));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(GotSlotId));

    const got_id = GotSlotId.fromInt(7);
    try std.testing.expect(!got_id.isNone());
    try std.testing.expect(GotSlotId.none.isNone());
    try std.testing.expectEqual(@as(u32, 7), got_id.asInt());

    // [3] Round-trip `.cx_dev_meta` binary serialization + negative tamper checks:
    const slots = [_]corex.CxGotSlotMeta{
        .{
            .def_id = DefId.init(FileId.fromInt(1), 0),
            .got_idx = 0,
            .abi_sig_hash64 = 0xCAFE_BABE_1234_5678,
            .slot_kind = .direct_fn,
        },
        .{
            .def_id = DefId.init(FileId.fromInt(1), 1),
            .got_idx = 1,
            .abi_sig_hash64 = 0xDEAD_BEEF_8765_4321,
            .slot_kind = .closure_invoke,
        },
    };
    const records = [_]corex.CxTypeLayoutRecord{
        .{
            .type_id = TypeId.fromInt(64),
            .byte_size = 16,
            .align_log2 = 3,
            .kind_flags = 1,
            .fields_len = 2,
            .fqn_hash32 = 0x1122_3344,
            .layout_shape_hash64 = 0xAAAA_BBBB_CCCC_DDDD,
            .field_hash64 = 0x9999_8888_7777_6666,
        },
    };
    const serialized = try dev_seam.serializeDevSeamMeta(
        std.testing.allocator,
        .{
            .arch_os_tag = TargetSpec.X86_64_LINUX.archOsTag(),
            .loop_contract_count = 3,
            .build_id_lo = 0x11,
            .build_id_hi = 0x22,
        },
        &slots,
        &records,
    );
    defer std.testing.allocator.free(serialized);
    try std.testing.expectEqual(@as(usize, 64 + 2 * 24 + 1 * 32), serialized.len);

    const decoded = try dev_seam.deserializeDevSeamMeta(serialized);
    try std.testing.expectEqual(@as(u32, 2), decoded.header.got_slot_count);
    try std.testing.expectEqual(@as(u32, 1), decoded.header.type_record_count);
    try std.testing.expectEqual(@as(u32, 3), decoded.header.loop_contract_count);
    try std.testing.expectEqual(@as(u64, 0xCAFE_BABE_1234_5678), decoded.got_slots[0].abi_sig_hash64);
    try std.testing.expectEqual(dev_seam.CxGotSlotMeta.SlotKind.closure_invoke, decoded.got_slots[1].slot_kind);
    try std.testing.expectEqual(@as(u64, 0x9999_8888_7777_6666), decoded.type_records[0].field_hash64);

    try std.testing.expectError(error.TruncatedHeader, dev_seam.deserializeDevSeamMeta(serialized[0..32]));
    try std.testing.expectError(error.PayloadSizeMismatch, dev_seam.deserializeDevSeamMeta(serialized[0 .. serialized.len - 4]));

    var bad_ver = try std.testing.allocator.dupe(u8, serialized);
    defer std.testing.allocator.free(bad_ver);
    bad_ver[8] = 99;
    try std.testing.expectError(error.UnsupportedVersion, dev_seam.deserializeDevSeamMeta(bad_ver));

    bad_ver[0] = 'Z';
    try std.testing.expectError(error.InvalidMagic, dev_seam.deserializeDevSeamMeta(bad_ver));
}

test "test_nominal_field_hash64_detects_semantic_swaps_and_terminates_on_cycles" {
    // [1] `Vec2 { x: f32, y: f32 }` vs `Vec2 { y: f32, x: f32 }`: identical `layout_shape_hash64`, distinct `field_hash64`!
    const src_v1 =
        \\pub struct Vec2 {
        \\    pub x: f32,
        \\    pub y: f32,
        \\}
        \\pub struct ListNode {
        \\    pub val: i32,
        \\    pub next: *ListNode,
        \\}
    ;
    const src_v2 =
        \\pub struct Vec2 {
        \\    pub y: f32,
        \\    pub x: f32,
        \\}
    ;

    var tc_v1 = try corex.typecheckSource(std.testing.allocator, FileId.fromInt(1), src_v1);
    defer tc_v1.deinit();
    try std.testing.expect(!tc_v1.diagnostics.hasErrors());

    var tc_v2 = try corex.typecheckSource(std.testing.allocator, FileId.fromInt(1), src_v2);
    defer tc_v2.deinit();
    try std.testing.expect(!tc_v2.diagnostics.hasErrors());

    const vec_ty_v1 = try findSymbolTypeId(&tc_v1.symbol_table, "Vec2");
    const node_ty_v1 = try findSymbolTypeId(&tc_v1.symbol_table, "ListNode");
    const vec_ty_v2 = try findSymbolTypeId(&tc_v2.symbol_table, "Vec2");

    const rec_v1 = corex.buildCxTypeLayoutRecord(
        &tc_v1.type_pool,
        &tc_v1.symbol_table,
        vec_ty_v1,
        corex.TargetLayout.NATIVE_64,
    );
    const rec_v2 = corex.buildCxTypeLayoutRecord(
        &tc_v2.type_pool,
        &tc_v2.symbol_table,
        vec_ty_v2,
        corex.TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(rec_v1.layout_shape_hash64, rec_v2.layout_shape_hash64);
    try std.testing.expect(rec_v1.field_hash64 != rec_v2.field_hash64);

    // Self-referential pointer cycle terminates cleanly and produces non-zero `FieldHash64`.
    const cycle_hash = corex.computeNominalFieldHash64(
        &tc_v1.type_pool,
        &tc_v1.symbol_table,
        node_ty_v1,
        corex.TargetLayout.NATIVE_64,
    );
    try std.testing.expect(!cycle_hash.isZero());

    // [2] `CompilerDb.setTargetLayout` invalidates `@align_of` on `cache_line_align_log2` change (`6 -> 7`).
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const file_id = FileId.fromInt(10);
    const cache_src =
        \\@cache_aligned
        \\pub struct HotSlot {
        \\    pub counter: u64,
        \\}
        \\pub const HOT_ALIGN: usize = @align_of[HotSlot]();
    ;
    _ = try db.setInput(file_id, cache_src, .low);
    const tree = try db.extractItemTree(file_id);
    const def_align = tree.entries[1].def_id;

    const eval_x64 = try db.evalComptimeDef(def_align);
    try std.testing.expect(!eval_x64.has_errors);
    try std.testing.expectEqual(@as(i128, 64), eval_x64.value.int_val);

    db.setTargetLayout(TargetSpec.AARCH64_MACOS.asTargetLayout());
    const eval_m1 = try db.evalComptimeDef(def_align);
    try std.testing.expect(!eval_m1.has_errors);
    try std.testing.expectEqual(@as(i128, 128), eval_m1.value.int_val);
}

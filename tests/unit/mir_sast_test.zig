//! Unit & Red-Team Regression Tests for Phase 6 `MIR` SAST Engine (`stage0/src/mir_sast.zig`)
//!
//! Covers all Phase 6 invariants (`PLAN.md` §2.6, `DR-06`, `DR-17`, `DR-20`):
//! - Binary layouts (`40B` `FnRegionSummary`, `34B` Early Cutoff digest, `DenseBitSet`, `Intv`,
//!   `PentagonSubRow`, `MovePathNode`, `WitnessCallEdge`), three-tier ownership (`Copy`,
//!   `AutoDrop`, `@linear`), trivial arena drop elision, `@secret`, `Context`, & `D-01` (`E0315`).
//! - Pass 1 & Pass 2 typestate (`E0301`–`E0305`, `E0313`, `W0308`, `E0328`), `> 64` simultaneous
//!   NLL loans (`[CRITICAL-08]`), `&mut`/`inout` temporary move-out (`[CRITICAL-07]`), conditional
//!   `set` `_drop_flag` (`[MAJOR-11]`), `MirVm` `@drop_trace` LIFO execution, & `comptime` drops
//!   (`[CRITICAL-04]`).
//! - Pass 3 `FnRegionSummary`, `E0306` escape (`[CRITICAL-05]`, `[CRITICAL-06]`), `@max_stack`
//!   (`E0316`, `[MINOR-18]`), contracts (`E0320`–`E0323`, `[CRITICAL-02]`, `[MAJOR-09]`,
//!   `[MAJOR-15]`), `Fix-17` Gates A–F (`E0324`–`E0327`, `W0330`, `[MINOR-19]`), `Fix-06B`
//!   vacated `subscript` (`W0329`, `[MAJOR-10]`), and `CompilerDb` Stage 9 SCCs (`[CRITICAL-03]`).
//! - Pass 4 sign-biased `Intv` (`NATIVE_64` & `WASM32`), Demand-Sliced Pentagon BCE (`E0307`,
//!   `W0314`, `Fix-06A`), `[CRITICAL-01]` mutable slice & zero-modulo guards, & `D-11` (`E0406`).

const std = @import("std");
const corex = @import("corex");

const mir = corex.mir;
const mir_sast = corex.mir_sast;
const symbol_resolver = corex.symbol_resolver;
const type_system = corex.type_system;

const BumpArena = corex.BumpArena;
const CapEnforcementScope = mir_sast.CapEnforcementScope;
const CompilerDb = corex.CompilerDb;
const ContextFieldKind = type_system.ContextFieldKind;
const ContextFieldLayout = type_system.ContextFieldLayout;
const DefId = corex.DefId;
const DenseBitSet = corex.DenseBitSet;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const EffectCapabilityMask = corex.EffectCapabilityMask;
const FileId = corex.FileId;
const FnContractScratchMask = corex.FnContractScratchMask;
const FnRegionSummary = corex.FnRegionSummary;
const GroupMatchResult = type_system.GroupMatchResult;
const Intv = corex.Intv;
const MirBody = corex.MirBody;
const MirIntrinsicKind = corex.MirIntrinsicKind;
const MirSastPipelineBundle = corex.MirSastPipelineBundle;
const MirVm = corex.MirVm;
const MovePathNode = corex.MovePathNode;
const OwnershipTier = corex.OwnershipTier;
const PackageCapPolicy = corex.PackageCapPolicy;
const PentagonSubRow = corex.PentagonSubRow;
const QueryKey = corex.QueryKey;
const RegSlot = corex.RegSlot;
const RodataPool = corex.RodataPool;
const SastConfig = corex.SastConfig;
const Span = corex.Span;
const SymbolIndex = corex.SymbolIndex;
const SymbolTable = corex.SymbolTable;
const TargetLayout = corex.TargetLayout;
const TypeFlags = type_system.TypeFlags;
const TypeId = corex.TypeId;
const WitnessCallEdge = corex.WitnessCallEdge;
const WitnessEdgeKind = corex.WitnessEdgeKind;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic matching `expected_code`.
fn hasDiagnosticCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Counts how many diagnostics in `sink` match `expected_code`.
fn countDiagnosticCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) usize {
    var match_count: usize = 0;
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) match_count += 1;
    }
    return match_count;
}

/// Lowers `source` through Phase 6 SAST on `NATIVE_64` and asserts zero errors were emitted.
fn verifyCleanSast(
    allocator: std.mem.Allocator,
    file_raw: u32,
    source: []const u8,
    config: SastConfig,
) !MirSastPipelineBundle {
    var bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(file_raw),
        source,
        TargetLayout.NATIVE_64,
        config,
    );
    errdefer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());
    return bundle;
}

/// Lowers `source` through Phase 6 SAST and asserts `expected_code` was emitted.
fn expectSastDiagnostic(
    allocator: std.mem.Allocator,
    file_raw: u32,
    source: []const u8,
    config: SastConfig,
    expected_code: DiagnosticCode,
) !void {
    var bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(file_raw),
        source,
        TargetLayout.NATIVE_64,
        config,
    );
    defer bundle.deinit();
    try std.testing.expect(hasDiagnosticCode(&bundle.diagnostics, expected_code));
}

/// Returns `true` if `body` contains an instruction with `.intrinsic_op` matching `target_kind`.
fn hasBodyIntrinsic(body: *const MirBody, target_kind: MirIntrinsicKind) bool {
    for (body.block_insts.items) |inst_val| {
        const inst = body.getInst(inst_val);
        if (inst.op == .intrinsic_op and @as(MirIntrinsicKind, @fromBackingInt(inst.aux_u16)) == target_kind) {
            return true;
        }
    }
    return false;
}

/// Resolves the `TypeId` of a named item in `sym_table` (`null` if absent).
fn findSymbolTypeByName(sym_table: *const SymbolTable, target_name: []const u8) ?TypeId {
    var sym_idx: u32 = 0;
    while (sym_idx < sym_table.symbols.items.len) : (sym_idx += 1) {
        const sym_rec = sym_table.getSymbol(SymbolIndex.fromInt(sym_idx)).*;
        if (std.mem.eql(u8, sym_rec.name_text, target_name) and !sym_rec.type_id.isError()) {
            return sym_rec.type_id;
        }
    }
    return null;
}

/// Resolves a `DefId` by item name from `CompilerDb.extractItemTree` entries.
fn findDefIdByName(entries: anytype, target_name: []const u8) ?DefId {
    for (entries) |entry| {
        if (std.mem.eql(u8, entry.name_text, target_name)) {
            return entry.def_id;
        }
    }
    return null;
}

/// Builds a CoreX source module with `70` simultaneous shared borrows to exercise `DenseBitSet.arena_words`.
fn buildOver64SimultaneousLoansSource(allocator: std.mem.Allocator, has_conflict: bool) ![]u8 {
    var src_buf: std.ArrayListUnmanaged(u8) = .empty;
    errdefer src_buf.deinit(allocator);
    var line_buf: [128]u8 = undefined;

    try src_buf.appendSlice(
        allocator,
        "pub fn borrow_cell(cell: &[i64; 1]) -> &[i64; 1] {\n" ++
            "    return cell;\n" ++
            "}\n" ++
            "pub fn mutate_cell(cell: &mut [i64; 1]) {\n" ++
            "    cell.*[0] = 777;\n" ++
            "}\n" ++
            "pub fn stress_seventy_loans() -> i64 {\n",
    );

    var idx: usize = 0;
    while (idx < 70) : (idx += 1) {
        try src_buf.appendSlice(
            allocator,
            try std.fmt.bufPrint(&line_buf, "    var cell_{d}: [i64; 1] = [{d}];\n", .{ idx, idx + 1 }),
        );
    }
    idx = 0;
    while (idx < 70) : (idx += 1) {
        try src_buf.appendSlice(
            allocator,
            try std.fmt.bufPrint(&line_buf, "    let view_{d} = borrow_cell(&cell_{d});\n", .{ idx, idx }),
        );
    }

    if (has_conflict) {
        try src_buf.appendSlice(allocator, "    mutate_cell(&mut cell_68);\n");
    }

    try src_buf.appendSlice(allocator, "    var total: i64 = 0;\n");
    idx = 0;
    while (idx < 70) : (idx += 1) {
        try src_buf.appendSlice(
            allocator,
            try std.fmt.bufPrint(&line_buf, "    total = total +% view_{d}[0];\n", .{idx}),
        );
    }

    if (!has_conflict) {
        try src_buf.appendSlice(
            allocator,
            "    mutate_cell(&mut cell_68);\n" ++
                "    total = total +% cell_68[0];\n",
        );
    }

    try src_buf.appendSlice(allocator, "    return total;\n}\n");
    return src_buf.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_phase6_binary_layouts_and_observable_summary_projection" {
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(FnRegionSummary));
    try std.testing.expectEqual(@as(usize, 34), FnRegionSummary.OBSERVABLE_SUMMARY_BYTES);
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(EffectCapabilityMask));
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(FnContractScratchMask));
    try std.testing.expectEqual(@as(usize, 12), @sizeOf(WitnessCallEdge));
    try std.testing.expectEqual(@as(usize, 20), @sizeOf(MovePathNode));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(Intv));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(PentagonSubRow));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(TypeFlags));

    var base_summary = FnRegionSummary{
        .ret_provenance_mask = 0x03,
        .param_flow_matrix = (@as(u64, 1) << 8),
        .global_escape_mask = 0x02,
        .consumed_param_mask = 0x04,
        .own_frame_bytes = 96,
        .max_subtree_bytes = 384,
        .inferred_effects_bits = EffectCapabilityMask.ALLOC_BIT,
        .direct_effects_bits = 0,
        .contracts_scratch_bits = 0x0015,
        .forwarded_cb_mask = 0x0002,
    };
    var edited_summary = base_summary;
    edited_summary.own_frame_bytes = 1024;
    edited_summary.direct_effects_bits = EffectCapabilityMask.ALLOC_BIT;

    var base_digest: [FnRegionSummary.OBSERVABLE_SUMMARY_BYTES]u8 = undefined;
    var edited_digest: [FnRegionSummary.OBSERVABLE_SUMMARY_BYTES]u8 = undefined;
    base_summary.writeObservableBytes(&base_digest);
    edited_summary.writeObservableBytes(&edited_digest);
    try std.testing.expectEqualSlices(u8, &base_digest, &edited_digest);

    edited_summary.max_subtree_bytes = 512;
    edited_summary.writeObservableBytes(&edited_digest);
    try std.testing.expect(!std.mem.eql(u8, &base_digest, &edited_digest));
}

test "test_phase6_dense_bitset_inline_and_arena_multiword_operations" {
    var bump_arena = BumpArena.init(std.testing.allocator);
    defer bump_arena.deinit();
    const arena_alloc = bump_arena.asAllocator();

    // [1] Inline (`<= 64` bits) set, unset, union, difference, intersection, and bit iterators:
    var inline_lhs = try DenseBitSet.initEmpty(arena_alloc, 64);
    var inline_rhs = try DenseBitSet.initEmpty(arena_alloc, 64);
    try std.testing.expect(inline_lhs == .inline_words);
    inline_lhs.set(0);
    inline_lhs.set(19);
    inline_lhs.set(63);
    inline_rhs.set(19);
    inline_rhs.set(42);

    try std.testing.expect(inline_lhs.intersects(inline_rhs));
    try std.testing.expectEqual(@as(?usize, 19), inline_lhs.firstIntersectionBit(inline_rhs));
    try std.testing.expectEqual(@as(?usize, 0), inline_lhs.nextSetBit(0));
    try std.testing.expectEqual(@as(?usize, 19), inline_lhs.nextSetBit(1));
    try std.testing.expectEqual(@as(?usize, 63), inline_lhs.nextSetBit(20));
    try std.testing.expectEqual(@as(?usize, null), inline_lhs.nextSetBit(64));

    const inline_merged = try inline_lhs.unionAlloc(inline_rhs, arena_alloc);
    try std.testing.expect(inline_merged.isSet(42));
    inline_lhs.differenceInPlace(inline_rhs);
    try std.testing.expect(!inline_lhs.isSet(19));
    try std.testing.expect(inline_lhs.isSet(63));

    // [2] Multi-word `BumpArena` (`160` bits -> 3 `u64` words) operations across word boundaries:
    var wide_lhs = try DenseBitSet.initEmpty(arena_alloc, 160);
    var wide_rhs = try DenseBitSet.initEmpty(arena_alloc, 160);
    try std.testing.expect(wide_lhs == .arena_words);
    wide_lhs.set(5);
    wide_lhs.set(64);
    wide_lhs.set(128);
    wide_lhs.set(159);
    wide_rhs.set(64);
    wide_rhs.set(140);
    wide_rhs.set(159);

    try std.testing.expect(wide_lhs.intersects(wide_rhs));
    try std.testing.expectEqual(@as(?usize, 64), wide_lhs.firstIntersectionBit(wide_rhs));
    wide_lhs.unset(64);
    try std.testing.expectEqual(@as(?usize, 159), wide_lhs.firstIntersectionBit(wide_rhs));

    var wide_union = try wide_lhs.unionAlloc(wide_rhs, arena_alloc);
    try std.testing.expect(wide_union == .arena_words);
    try std.testing.expect(wide_union.isSet(5));
    try std.testing.expect(wide_union.isSet(128));
    try std.testing.expect(wide_union.isSet(140));
    try std.testing.expectEqual(@as(?usize, 5), wide_union.nextSetBit(0));
    try std.testing.expectEqual(@as(?usize, 64), wide_union.nextSetBit(6));
    try std.testing.expectEqual(@as(?usize, 128), wide_union.nextSetBit(65));
    try std.testing.expectEqual(@as(?usize, 140), wide_union.nextSetBit(129));
    try std.testing.expectEqual(@as(?usize, 159), wide_union.nextSetBit(141));

    wide_union.differenceInPlace(wide_rhs);
    try std.testing.expect(!wide_union.isSet(140));
    try std.testing.expect(!wide_union.isSet(159));
    try std.testing.expect(wide_union.isSet(128));

    // Mixed inline-to-arena union preserves upper words cleanly:
    const mixed_union = try inline_rhs.unionAlloc(wide_rhs, arena_alloc);
    try std.testing.expect(mixed_union.isSet(42));
    try std.testing.expect(mixed_union.isSet(140));
}

test "test_phase6_ownership_tiers_trivial_arena_drop_secret_context_and_wire_e0315" {
    const allocator = std.testing.allocator;

    // [1] Three-tier ownership classification (`Copy`, `AutoDrop`, `@linear`) + `Context.trace_sink`:
    const tier_src =
        \\pub struct CopyPoint {
        \\    pub x: i64,
        \\    pub y: i64,
        \\}
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct CustomDropGuard {
        \\    pub tag: i64,
        \\}
        \\impl CustomDropGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub struct AutoDropWrap {
        \\    pub items: Vec[i64],
        \\}
        \\@linear
        \\pub struct DbLease {
        \\    pub slot: u32,
        \\}
        \\pub struct LinearWrap {
        \\    pub lease: DbLease,
        \\}
        \\pub struct BumpArena {
        \\    pub used: usize,
        \\}
        \\pub struct Context {}
        \\@zero_pad
        \\@repr(C)
        \\pub struct WireHeader {
        \\    pub kind: u8,
        \\    pub length: u32,
        \\}
        \\pub fn check_context_and_wire(ctx: &Context, hdr: &WireHeader, raw: &[u8]) -> usize {
        \\    let trace_ptr: (*mut u8)? = ctx.trace_sink;
        \\    let seed_val: u64 = ctx.rng_seed;
        \\    let encoded: &[u8] = hdr.as_bytes();
        \\    let decoded: WireHeader? = @from_bytes[WireHeader](raw);
        \\    let viewed: (&WireHeader)? = @view_bytes[WireHeader](encoded);
        \\    let _ = trace_ptr;
        \\    let _ = seed_val;
        \\    let _ = decoded;
        \\    let _ = viewed;
        \\    return encoded.len();
        \\}
    ;
    var ok_bundle = try verifyCleanSast(allocator, 101, tier_src, .{});
    defer ok_bundle.deinit();

    // Verify `Context.trace_sink` canonical seam layout:
    const trace_field = ContextFieldLayout.fromFieldName("trace_sink").?;
    try std.testing.expectEqual(ContextFieldKind.trace_sink, trace_field.kind);
    try std.testing.expectEqual(@as(u8, 3), trace_field.slot_ordinal);

    // Verify `Copy` scalars, slices, arrays, and plain structs:
    try std.testing.expectEqual(
        OwnershipTier.copy_tier,
        type_system.classifyOwnershipTier(&ok_bundle.pool, &ok_bundle.sym_table, .i64_ty),
    );
    try std.testing.expectEqual(
        OwnershipTier.copy_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            try ok_bundle.pool.internSlice(.u8_ty, false),
        ),
    );
    try std.testing.expectEqual(
        OwnershipTier.copy_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            try ok_bundle.pool.internArray(.i32_ty, 4, false),
        ),
    );
    try std.testing.expectEqual(
        OwnershipTier.copy_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            findSymbolTypeByName(&ok_bundle.sym_table, "CopyPoint").?,
        ),
    );

    // Verify `AutoDrop` heap containers, custom `drop` structs, and wrappers:
    try std.testing.expectEqual(
        OwnershipTier.auto_drop_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            findSymbolTypeByName(&ok_bundle.sym_table, "CustomDropGuard").?,
        ),
    );
    try std.testing.expectEqual(
        OwnershipTier.auto_drop_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            findSymbolTypeByName(&ok_bundle.sym_table, "AutoDropWrap").?,
        ),
    );

    // Verify `@linear` structs, `BumpArena`, wrappers, and `&mut T`:
    try std.testing.expectEqual(
        OwnershipTier.linear_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            findSymbolTypeByName(&ok_bundle.sym_table, "DbLease").?,
        ),
    );
    try std.testing.expectEqual(
        OwnershipTier.linear_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            findSymbolTypeByName(&ok_bundle.sym_table, "LinearWrap").?,
        ),
    );
    try std.testing.expectEqual(
        OwnershipTier.linear_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            findSymbolTypeByName(&ok_bundle.sym_table, "BumpArena").?,
        ),
    );
    try std.testing.expectEqual(
        OwnershipTier.linear_tier,
        type_system.classifyOwnershipTier(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            try ok_bundle.pool.internRef(.i64_ty, true),
        ),
    );

    // Verify `WireHeader` satisfies `IntoBytes` (`@repr(C) @zero_pad`):
    try std.testing.expectEqual(
        GroupMatchResult.matched_exact,
        type_system.checkGroupSatisfaction(
            &ok_bundle.pool,
            &ok_bundle.sym_table,
            TargetLayout.NATIVE_64,
            findSymbolTypeByName(&ok_bundle.sym_table, "WireHeader").?,
            .group_into_bytes,
        ),
    );

    // [2] Trivial lexical-region `AutoDrop` elision (`region_raw == 1`) vs custom `Drop` & heap `Vec` retention:
    const arena_drop_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct ArenaBuffer {
        \\    pub len: usize,
        \\}
        \\pub struct RegionNote {
        \\    pub code: i64,
        \\}
        \\impl RegionNote {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.code);
        \\    }
        \\}
        \\pub fn use_buf() -> usize {
        \\    let buf = ArenaBuffer { len: 16 };
        \\    return buf.len;
        \\}
        \\pub fn use_note() -> i64 {
        \\    let note = RegionNote { code: 7 };
        \\    return note.code;
        \\}
        \\pub fn use_vec() -> usize {
        \\    let items = Vec { len: 3 };
        \\    return items.len;
        \\}
    ;
    var raw_mir = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(102),
        arena_drop_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer raw_mir.deinit();
    try std.testing.expect(!raw_mir.hir_bundle.diagnostics.hasErrors());

    // Mark `ArenaBuffer` as an arena-backed `AutoDrop` handle (`has_drop = true`, no custom `fn drop`, no heap `Vec`):
    const buf_orig = raw_mir.mir_bundle.findBodyByName(&raw_mir.hir_bundle.interner, "use_buf").?;
    for (buf_orig.locals.items[1..]) |loc_decl| {
        if (!loc_decl.type_id.isError() and raw_mir.hir_bundle.pool.getNode(loc_decl.type_id).tag == .struct_ty) {
            var updated_flags = raw_mir.hir_bundle.pool.getFlags(loc_decl.type_id);
            updated_flags.is_copy = false;
            updated_flags.has_drop = true;
            raw_mir.hir_bundle.pool.nodes.items(.flags)[loc_decl.type_id.asInt()] = updated_flags;
        }
    }

    var stack_buf_body = try buf_orig.clone(allocator);
    defer stack_buf_body.deinit();
    var stack_buf_res = try corex.analyzeSingleMirBody(
        allocator,
        &stack_buf_body,
        &raw_mir.hir_bundle.pool,
        &raw_mir.hir_bundle.sym_table,
        &raw_mir.hir_bundle.interner,
        .{},
    );
    defer stack_buf_res.deinit();
    try std.testing.expectEqual(@as(u32, 1), stack_buf_res.emitted_drops);

    // Tagging `ArenaBuffer` with `region_raw = 1` (lexical arena) elides trivial non-heap `AutoDrop` to `0` drops:
    var region_buf_body = try buf_orig.clone(allocator);
    defer region_buf_body.deinit();
    for (region_buf_body.locals.items[1..]) |*loc_decl| {
        loc_decl.region_raw = 1;
    }
    var region_buf_res = try corex.analyzeSingleMirBody(
        allocator,
        &region_buf_body,
        &raw_mir.hir_bundle.pool,
        &raw_mir.hir_bundle.sym_table,
        &raw_mir.hir_bundle.interner,
        .{},
    );
    defer region_buf_res.deinit();
    try std.testing.expectEqual(@as(u32, 0), region_buf_res.emitted_drops);

    // Tagging `RegionNote` (explicit custom `fn drop` side effects) with `region_raw = 1` STILL emits `1` destructor:
    const note_orig = raw_mir.mir_bundle.findBodyByName(&raw_mir.hir_bundle.interner, "use_note").?;
    var region_note_body = try note_orig.clone(allocator);
    defer region_note_body.deinit();
    for (region_note_body.locals.items[1..]) |*loc_decl| {
        loc_decl.region_raw = 1;
    }
    var region_note_res = try corex.analyzeSingleMirBody(
        allocator,
        &region_note_body,
        &raw_mir.hir_bundle.pool,
        &raw_mir.hir_bundle.sym_table,
        &raw_mir.hir_bundle.interner,
        .{},
    );
    defer region_note_res.deinit();
    try std.testing.expectEqual(@as(u32, 1), region_note_res.emitted_drops);

    // Tagging `Vec` with `region_raw = 1` STILL emits a destructor because `Vec` owns heap memory:
    const vec_orig = raw_mir.mir_bundle.findBodyByName(&raw_mir.hir_bundle.interner, "use_vec").?;
    var region_vec_body = try vec_orig.clone(allocator);
    defer region_vec_body.deinit();
    for (region_vec_body.locals.items[1..]) |*loc_decl| {
        loc_decl.region_raw = 1;
    }
    var region_vec_res = try corex.analyzeSingleMirBody(
        allocator,
        &region_vec_body,
        &raw_mir.hir_bundle.pool,
        &raw_mir.hir_bundle.sym_table,
        &raw_mir.hir_bundle.interner,
        .{},
    );
    defer region_vec_res.deinit();
    try std.testing.expectEqual(@as(u32, 1), region_vec_res.emitted_drops);

    // [3] `D-01` Wire Contract Violations (`E0315`) on unzeroed padding, `bool`, pointer, and `@secret`:
    const wire_violations_src =
        \\@secret
        \\pub type MasterKey = distinct [u8; 16];
        \\pub struct SecretEnvelope {
        \\    pub key: MasterKey,
        \\}
        \\pub struct PaddedWire {
        \\    pub flag_byte: u8,
        \\    pub body_len: u32,
        \\}
        \\@repr(C)
        \\pub struct PtrWire {
        \\    pub ptr_field: &u8,
        \\}
        \\pub fn bad_wire_ops(
        \\    padded: &PaddedWire,
        \\    ptr_pkt: &PtrWire,
        \\    sec_env: &SecretEnvelope,
        \\    raw_bytes: &[u8],
        \\) -> usize {
        \\    let pad_bytes = padded.as_bytes();
        \\    let ptr_bytes = ptr_pkt.as_bytes();
        \\    let sec_bytes = sec_env.as_bytes();
        \\    let bad_bool: bool? = @from_bytes[bool](raw_bytes);
        \\    let _ = ptr_bytes;
        \\    let _ = sec_bytes;
        \\    let _ = bad_bool;
        \\    return pad_bytes.len();
        \\}
    ;
    var bad_wire_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(103),
        wire_violations_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bad_wire_bundle.deinit();
    try std.testing.expect(
        countDiagnosticCode(&bad_wire_bundle.diagnostics, .e0315_wire_layout_contract_violation) >= 4,
    );
    try std.testing.expect(
        bad_wire_bundle.pool.getFlags(
            findSymbolTypeByName(&bad_wire_bundle.sym_table, "SecretEnvelope").?,
        ).is_secret,
    );
}

test "test_phase6_typestate_uaf_e0301_partial_move_reinit_e0302_and_uninit_e0303" {
    const allocator = std.testing.allocator;

    // [1a] `E0301` use-after-free when reading/borrowing a buffer after `.free(&mut self)`:
    const uaf_method_src =
        \\pub struct RawBlock {
        \\    pub size: usize,
        \\}
        \\impl RawBlock {
        \\    pub fn free(&mut self) {
        \\        self.size = 0;
        \\    }
        \\}
        \\pub fn read_after_free() -> usize {
        \\    var blk = RawBlock { size: 64 };
        \\    blk.free();
        \\    return blk.size;
        \\}
    ;
    try expectSastDiagnostic(allocator, 201, uaf_method_src, .{}, .e0301_use_after_free);

    // [1b] `E0301` use-after-free dereferencing a dangling raw pointer after stack local scope ends:
    const uaf_dangling_ptr_src =
        \\pub fn deref_dangling_stack_ptr() -> i64 {
        \\    var raw_ptr: *i64 = 0 as *i64;
        \\    {
        \\        let inner_slot: i64 = 99;
        \\        raw_ptr = &raw inner_slot;
        \\    }
        \\    return unsafe { raw_ptr.* };
        \\}
    ;
    try expectSastDiagnostic(allocator, 202, uaf_dangling_ptr_src, .{}, .e0301_use_after_free);

    // [2a] `E0302` partial struct field move invalidates whole-parent read while sibling field stays valid:
    const sibling_ok_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct DualBuffers {
        \\    pub left: Vec[i64],
        \\    pub right: Vec[i64],
        \\}
        \\pub fn consume_vec(buf: own Vec[i64]) {}
        \\pub fn read_sibling_after_partial_move() -> usize {
        \\    var pair = DualBuffers {
        \\        left: Vec { len: 4 },
        \\        right: Vec { len: 9 },
        \\    };
        \\    consume_vec(own pair.left);
        \\    return pair.right.len;
        \\}
    ;
    var sibling_bundle = try verifyCleanSast(allocator, 203, sibling_ok_src, .{});
    defer sibling_bundle.deinit();

    const parent_after_partial_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct DualBuffers {
        \\    pub left: Vec[i64],
        \\    pub right: Vec[i64],
        \\}
        \\pub fn consume_vec(buf: own Vec[i64]) {}
        \\pub fn consume_dual(whole: own DualBuffers) {}
        \\pub fn bad_whole_use_after_field_move() {
        \\    var pair = DualBuffers {
        \\        left: Vec { len: 4 },
        \\        right: Vec { len: 9 },
        \\    };
        \\    consume_vec(own pair.left);
        \\    consume_dual(own pair);
        \\}
    ;
    try expectSastDiagnostic(allocator, 204, parent_after_partial_src, .{}, .e0302_use_after_move);

    // [2b] Dominating field re-initialization restores whole-struct validity (`0` errors):
    const reinit_restores_parent_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct DualBuffers {
        \\    pub left: Vec[i64],
        \\    pub right: Vec[i64],
        \\}
        \\pub fn consume_vec(buf: own Vec[i64]) {}
        \\pub fn consume_dual(whole: own DualBuffers) -> usize {
        \\    return whole.left.len + whole.right.len;
        \\}
        \\pub fn reinit_then_consume_whole() -> usize {
        \\    var pair = DualBuffers {
        \\        left: Vec { len: 4 },
        \\        right: Vec { len: 9 },
        \\    };
        \\    consume_vec(own pair.left);
        \\    pair.left = Vec { len: 12 };
        \\    return consume_dual(own pair);
        \\}
    ;
    var reinit_bundle = try verifyCleanSast(allocator, 205, reinit_restores_parent_src, .{});
    defer reinit_bundle.deinit();

    // [3] `E0303` uninitialized variable read & `&out` (`E0422`) normal return vs `Result.Err` exemption:
    const uninit_local_src =
        \\pub fn read_maybe_uninit(cond: bool) -> i64 {
        \\    var pending: i64;
        \\    if cond {
        \\        pending = 17;
        \\    }
        \\    return pending;
        \\}
    ;
    try expectSastDiagnostic(allocator, 206, uninit_local_src, .{}, .e0303_uninitialized_memory_read);

    const uninit_set_src =
        \\pub fn bad_set_out(out_val: &out i64, flag: bool) {
        \\    if flag {
        \\        out_val.* = 42;
        \\    }
        \\}
    ;
    try expectSastDiagnostic(allocator, 207, uninit_set_src, .{}, .e0422_out_param_contract_violation);

    const fallible_set_ok_src =
        \\pub fn init_set_or_err(out_val: &out i64, should_fail: bool) -> i64!i32 {
        \\    if should_fail {
        \\        return .Err(500);
        \\    }
        \\    out_val.* = 88;
        \\    return .Ok(1);
        \\}
    ;
    var set_ok_bundle = try verifyCleanSast(allocator, 208, fallible_set_ok_src, .{});
    defer set_ok_bundle.deinit();
}

test "test_phase6_linear_completeness_e0304_defer_errdefer_and_double_close_e0313" {
    const allocator = std.testing.allocator;

    // [1] Unconsumed `@linear` local & `?` error-path leak emit `E0304`:
    const linear_leak_src =
        \\@linear
        \\pub struct SocketLease {
        \\    pub port: u16,
        \\}
        \\pub fn may_fail(flag: bool) -> i32!i32 {
        \\    if flag { return .Err(1); }
        \\    return .Ok(0);
        \\}
        \\pub fn close_lease(lease: own SocketLease) {
        \\    let SocketLease { port: _ } = lease;
        \\}
        \\pub fn leak_on_try_unwind(flag: bool) -> i32!i32 {
        \\    let lease = SocketLease { port: 8080 };
        \\    let step = may_fail(flag)?;
        \\    close_lease(own lease);
        \\    return .Ok(step);
        \\}
    ;
    try expectSastDiagnostic(allocator, 210, linear_leak_src, .{}, .e0304_resource_or_memory_leak);

    // [2] Valid consumption via `defer` AND via `errdefer` + normal `own` (`0` errors):
    const linear_clean_src =
        \\@linear
        \\pub struct TxSession {
        \\    pub tx_id: i64,
        \\}
        \\pub fn step_op(should_err: bool) -> i64!i32 {
        \\    if should_err { return .Err(7); }
        \\    return .Ok(100);
        \\}
        \\pub fn commit_tx(session: own TxSession) {
        \\    let TxSession { tx_id: _ } = session;
        \\}
        \\pub fn rollback_tx(session: own TxSession) {
        \\    let TxSession { tx_id: _ } = session;
        \\}
        \\pub fn run_with_defer(flag: bool) -> i64 {
        \\    let session = TxSession { tx_id: 1 };
        \\    defer { commit_tx(own session); }
        \\    if flag { return 10; }
        \\    return 20;
        \\}
        \\pub fn run_with_errdefer(should_err: bool) -> i64!i32 {
        \\    let session = TxSession { tx_id: 2 };
        \\    errdefer { rollback_tx(own session); }
        \\    let val = step_op(should_err)?;
        \\    commit_tx(own session);
        \\    return .Ok(val);
        \\}
    ;
    var clean_linear_bundle = try verifyCleanSast(allocator, 211, linear_clean_src, .{});
    defer clean_linear_bundle.deinit();

    // [3] `E0313` duplicate `@linear` close and duplicate explicit `.free()` call:
    const double_close_src =
        \\@linear
        \\pub struct FileToken {
        \\    pub handle: i32,
        \\}
        \\pub struct PoolChunk {
        \\    pub bytes: usize,
        \\}
        \\impl PoolChunk {
        \\    pub fn free(&mut self) {
        \\        self.bytes = 0;
        \\    }
        \\}
        \\pub fn close_file(tok: own FileToken) {
        \\    let FileToken { handle: _ } = tok;
        \\}
        \\pub fn bad_double_cleanup() {
        \\    let tok = FileToken { handle: 4 };
        \\    close_file(own tok);
        \\    close_file(own tok);
        \\    var chunk = PoolChunk { bytes: 128 };
        \\    chunk.free();
        \\    chunk.free();
        \\}
    ;
    var dbl_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(212),
        double_close_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer dbl_bundle.deinit();
    try std.testing.expect(
        countDiagnosticCode(&dbl_bundle.diagnostics, .e0313_double_free_or_close) >= 2,
    );
}

test "test_phase6_nll_exclusivity_e0305_over_64_loans_mut_move_out_and_set_drop_flag" {
    const allocator = std.testing.allocator;

    // [1] NLL shortened sequential view borrow passes (`0` errors); interleaved use emits `E0305`:
    const nll_seq_src =
        \\pub fn head_slice(arr: &[i64]) -> &[i64] {
        \\    return arr;
        \\}
        \\pub fn write_head(arr: &mut [i64; 4]) {
        \\    arr.*[0] = 55;
        \\}
        \\pub fn ok_shortened_borrow() -> i64 {
        \\    var arr: [i64; 4] = [1, 2, 3, 4];
        \\    let view = head_slice(&arr);
        \\    let _ = view;
        \\    write_head(&mut arr);
        \\    return arr[0];
        \\}
    ;
    var seq_ok_bundle = try verifyCleanSast(allocator, 220, nll_seq_src, .{});
    defer seq_ok_bundle.deinit();

    const nll_conflict_src =
        \\pub fn head_slice(arr: &[i64]) -> &[i64] {
        \\    return arr;
        \\}
        \\pub fn write_head(arr: &mut [i64; 4]) {
        \\    arr.*[0] = 55;
        \\}
        \\pub fn bad_interleaved_borrow() -> usize {
        \\    var arr: [i64; 4] = [1, 2, 3, 4];
        \\    let view = head_slice(&arr);
        \\    write_head(&mut arr);
        \\    return view.len();
        \\}
    ;
    try expectSastDiagnostic(allocator, 221, nll_conflict_src, .{}, .e0305_exclusivity_violation);

    // [2] `[CRITICAL-08]` `> 64` (`70`) simultaneous tracked loans (`DenseBitSet.arena_words`):
    const seventy_conflict_src = try buildOver64SimultaneousLoansSource(allocator, true);
    defer allocator.free(seventy_conflict_src);
    try expectSastDiagnostic(allocator, 222, seventy_conflict_src, .{}, .e0305_exclusivity_violation);

    const seventy_clean_src = try buildOver64SimultaneousLoansSource(allocator, false);
    defer allocator.free(seventy_clean_src);
    var seventy_ok_bundle = try verifyCleanSast(allocator, 223, seventy_clean_src, .{});
    defer seventy_ok_bundle.deinit();

    // [3] `[CRITICAL-07]` `&mut Wrapper` temporary non-`Copy` field move-out:
    const mut_move_missing_reinit_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct Wrapper {
        \\    pub inner: Vec[i64],
        \\}
        \\pub fn take_vec(items: own Vec[i64]) {}
        \\pub fn bad_mut_ref_move_out(wrap_ref: &mut Wrapper) {
        \\    take_vec(own wrap_ref.inner);
        \\}
        \\pub fn bad_inout_read_before_reinit(wrap_io: &mut Wrapper) -> usize {
        \\    take_vec(own wrap_io.inner);
        \\    let bad_len = wrap_io.inner.len;
        \\    wrap_io.inner = Vec { len: 1 };
        \\    return bad_len;
        \\}
    ;
    var mut_bad_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(224),
        mut_move_missing_reinit_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer mut_bad_bundle.deinit();
    try std.testing.expect(
        hasDiagnosticCode(&mut_bad_bundle.diagnostics, .e0303_uninitialized_memory_read),
    );
    try std.testing.expect(
        hasDiagnosticCode(&mut_bad_bundle.diagnostics, .e0302_use_after_move),
    );

    const mut_move_reinit_ok_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct Wrapper {
        \\    pub inner: Vec[i64],
        \\}
        \\pub fn take_vec(items: own Vec[i64]) {}
        \\pub fn swap_mut_ref_field(wrap_ref: &mut Wrapper, cond: bool) {
        \\    take_vec(own wrap_ref.inner);
        \\    if cond {
        \\        wrap_ref.inner = Vec { len: 10 };
        \\    } else {
        \\        wrap_ref.inner = Vec { len: 20 };
        \\    }
        \\}
    ;
    var mut_ok_bundle = try verifyCleanSast(allocator, 225, mut_move_reinit_ok_src, .{});
    defer mut_ok_bundle.deinit();

    // [4] `[MAJOR-11]` Conditional `&out` parameter initialization updates `_drop_flag` cleanly in `MirVm`:
    const cond_set_drop_src =
        \\pub struct TrackedBox {
        \\    pub tag: i64,
        \\}
        \\impl TrackedBox {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub fn populate_box(out_box: &out TrackedBox, val: i64) {
        \\    out_box.* = TrackedBox { tag: val };
        \\}
        \\pub fn run_conditional_set(should_init: bool) -> i64 {
        \\    var slot: TrackedBox;
        \\    if should_init {
        \\        populate_box(&out slot, 707);
        \\    }
        \\    return 1;
        \\}
    ;
    var cond_set_bundle = try verifyCleanSast(allocator, 226, cond_set_drop_src, .{});
    defer cond_set_bundle.deinit();
    const cond_body = cond_set_bundle.mir_module.findBodyByName(
        &cond_set_bundle.interner,
        "run_conditional_set",
    ).?;
    try std.testing.expect(hasBodyIntrinsic(cond_body, .drop_if_live));

    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &cond_set_bundle.interner,
        &cond_set_bundle.pool,
        &cond_set_bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (cond_set_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    _ = try vm.evalBody(cond_body, &[_]RegSlot{.{ .scalar_u64 = 0 }});
    try std.testing.expectEqual(@as(usize, 0), vm.asDropTraceSlice().len);
    _ = try vm.evalBody(cond_body, &[_]RegSlot{.{ .scalar_u64 = 1 }});
    try std.testing.expectEqualSlices(i64, &[_]i64{707}, vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());
}

test "test_phase6_w0308_per_arena_tracking_and_d04_scratch_ping_pong_e0328" {
    const allocator = std.testing.allocator;

    // [1] `[MINOR-20]` Per-arena `LocalId` tracking for `W0308` across multiple distinct `BumpArena`s:
    const multi_arena_clean_src =
        \\pub struct BumpArena {
        \\    pub cursor: usize,
        \\}
        \\impl BumpArena {
        \\    pub fn alloc_bytes(&mut self, count: usize) -> usize {
        \\        self.cursor = self.cursor +% count;
        \\        return self.cursor;
        \\    }
        \\    pub fn reset(&mut self) {
        \\        self.cursor = 0;
        \\    }
        \\    pub fn deinit(own self) {
        \\        let BumpArena { cursor: _ } = self;
        \\    }
        \\}
        \\pub fn loop_arenas_clean(iters: usize) -> usize {
        \\    var primary_arena = BumpArena { cursor: 0 };
        \\    var secondary_arena = BumpArena { cursor: 0 };
        \\    var step: usize = 0;
        \\    var total: usize = 0;
        \\    while step < iters {
        \\        total = total +% primary_arena.alloc_bytes(32);
        \\        total = total +% secondary_arena.alloc_bytes(16);
        \\        primary_arena.reset();
        \\        secondary_arena.reset();
        \\        step = step +% 1;
        \\    }
        \\    primary_arena.deinit();
        \\    secondary_arena.deinit();
        \\    return total;
        \\}
    ;
    var clean_arena_bundle = try verifyCleanSast(allocator, 230, multi_arena_clean_src, .{});
    defer clean_arena_bundle.deinit();
    try std.testing.expectEqual(@as(usize, 0), clean_arena_bundle.diagnostics.diagnostics.items.len);

    // `active_arena` allocates + resets cleanly; `idle_arena` ONLY resets/deinits -> exactly 1 `W0308`:
    const multi_arena_warn_src =
        \\pub struct BumpArena {
        \\    pub cursor: usize,
        \\}
        \\impl BumpArena {
        \\    pub fn alloc_bytes(&mut self, count: usize) -> usize {
        \\        self.cursor = self.cursor +% count;
        \\        return self.cursor;
        \\    }
        \\    pub fn reset(&mut self) {
        \\        self.cursor = 0;
        \\    }
        \\    pub fn deinit(own self) {
        \\        let BumpArena { cursor: _ } = self;
        \\    }
        \\}
        \\pub fn loop_with_one_unused_arena(iters: usize) -> usize {
        \\    var active_arena = BumpArena { cursor: 0 };
        \\    var idle_arena = BumpArena { cursor: 0 };
        \\    var _intentionally_unused = BumpArena { cursor: 0 };
        \\    var step: usize = 0;
        \\    var acc: usize = 0;
        \\    while step < iters {
        \\        acc = acc +% active_arena.alloc_bytes(64);
        \\        active_arena.reset();
        \\        idle_arena.reset();
        \\        step = step +% 1;
        \\    }
        \\    _intentionally_unused.deinit();
        \\    idle_arena.deinit();
        \\    active_arena.deinit();
        \\    return acc;
        \\}
    ;
    var warn_arena_bundle = try verifyCleanSast(allocator, 231, multi_arena_warn_src, .{});
    defer warn_arena_bundle.deinit();
    try std.testing.expectEqual(
        @as(usize, 1),
        countDiagnosticCode(&warn_arena_bundle.diagnostics, .w0308_unused_region_allocation),
    );

    // [2] `D-04` `Context.scratch[0..2]` ping-pong: alternating `(0, 1)` passes; same-slot rewind emits `E0328`:
    const scratch_ping_pong_ok_src =
        \\pub struct ScratchArena {
        \\    pub backing: [u8; 8],
        \\}
        \\impl ScratchArena {
        \\    pub fn alloc_slice(&mut self) -> &[u8] {
        \\        return &self.backing;
        \\    }
        \\    pub fn reset(&mut self) {
        \\        self.backing[0] = 0;
        \\    }
        \\}
        \\pub struct Context {
        \\    pub allocator: usize,
        \\    pub scratch: [ScratchArena; 2],
        \\}
        \\pub fn helper_using_slot_one(ctx: &mut Context) -> usize {
        \\    ctx.scratch[1].reset();
        \\    let sub_slice = ctx.scratch[1].alloc_slice();
        \\    return sub_slice.len();
        \\}
        \\pub fn caller_ping_pong_ok(ctx: &mut Context) -> usize {
        \\    let live_zero = ctx.scratch[0].alloc_slice();
        \\    let sub_len = helper_using_slot_one(&mut ctx.*);
        \\    return live_zero.len() +% sub_len;
        \\}
    ;
    var scratch_ok_bundle = try verifyCleanSast(allocator, 232, scratch_ping_pong_ok_src, .{});
    defer scratch_ok_bundle.deinit();

    const scratch_conflict_src =
        \\pub struct ScratchArena {
        \\    pub backing: [u8; 8],
        \\}
        \\impl ScratchArena {
        \\    pub fn alloc_slice(&mut self) -> &[u8] {
        \\        return &self.backing;
        \\    }
        \\    pub fn reset(&mut self) {
        \\        self.backing[0] = 0;
        \\    }
        \\}
        \\pub struct Context {
        \\    pub allocator: usize,
        \\    pub scratch: [ScratchArena; 2],
        \\}
        \\pub fn helper_rewinding_slot_zero(ctx: &mut Context) {
        \\    ctx.scratch[0].reset();
        \\}
        \\pub fn caller_ping_pong_conflict(ctx: &mut Context) -> usize {
        \\    let live_zero = ctx.scratch[0].alloc_slice();
        \\    helper_rewinding_slot_zero(&mut ctx.*);
        \\    return live_zero.len();
        \\}
    ;
    try expectSastDiagnostic(
        allocator,
        233,
        scratch_conflict_src,
        .{},
        .e0328_scratch_arena_ping_pong_conflict,
    );
}

test "test_phase6_elaborate_drops_mir_vm_lifo_trace_and_comptime_drop_eval" {
    const allocator = std.testing.allocator;

    // [1] Branch-aware `ElaborateDrops` (`drop_in_place` + `drop_if_live`) verified in `MirVm` via `@drop_trace`:
    const drop_lifo_src =
        \\pub struct GuardItem {
        \\    pub id: i64,
        \\}
        \\impl GuardItem {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.id);
        \\    }
        \\}
        \\pub fn consume_early(item: own GuardItem) {
        \\    @drop_trace(1000 + item.id);
        \\}
        \\pub fn run_lifo_and_branch(take_middle: bool) -> i64 {
        \\    let first = GuardItem { id: 10 };
        \\    let middle = GuardItem { id: 20 };
        \\    let third = GuardItem { id: 30 };
        \\    if take_middle {
        \\        consume_early(own middle);
        \\    }
        \\    return first.id + third.id;
        \\}
    ;
    var drop_bundle = try verifyCleanSast(allocator, 240, drop_lifo_src, .{});
    defer drop_bundle.deinit();

    const run_body = drop_bundle.mir_module.findBodyByName(
        &drop_bundle.interner,
        "run_lifo_and_branch",
    ).?;
    try std.testing.expect(hasBodyIntrinsic(run_body, .drop_in_place));
    try std.testing.expect(hasBodyIntrinsic(run_body, .drop_if_live));

    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &drop_bundle.interner,
        &drop_bundle.pool,
        &drop_bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (drop_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    // `take_middle == false`: drops execute in exact reverse-LIFO declaration order `30, 20, 10`:
    const res_keep = try vm.evalBody(run_body, &[_]RegSlot{.{ .scalar_u64 = 0 }});
    try std.testing.expectEqual(@as(i64, 40), res_keep.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 30, 20, 10 }, vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());

    // `take_middle == true`: `middle` drops inside `consume_early` (`1020, 20`), then `30, 10` at scope exit:
    vm.drop_trace.clearRetainingCapacity();
    const res_move = try vm.evalBody(run_body, &[_]RegSlot{.{ .scalar_u64 = 1 }});
    try std.testing.expectEqual(@as(i64, 40), res_move.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 1020, 20, 30, 10 }, vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());

    // [2] `[CRITICAL-04]` `CompilerDb.evalComptimeDef` runs Stage 9 drop-elaborated `MIR`:
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    const ct_file = FileId.fromInt(241);
    const ct_drop_src =
        \\pub struct CtGuard {
        \\    pub code: i64,
        \\}
        \\impl CtGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.code);
        \\    }
        \\}
        \\pub fn take_ct_guard(item: own CtGuard) -> i64 {
        \\    return item.code;
        \\}
        \\pub fn compute_ct_value(cond: bool) -> i64 {
        \\    let guard = CtGuard { code: 55 };
        \\    if cond {
        \\        return take_ct_guard(own guard) + 5;
        \\    }
        \\    return 0;
        \\}
        \\pub const CT_RESULT: i64 = compute_ct_value(true);
    ;
    _ = try db.setInput(ct_file, ct_drop_src, .low);
    const ct_tree = try db.extractItemTree(ct_file);
    const ct_artifact = try db.evalComptimeDef(
        findDefIdByName(ct_tree.entries, "CT_RESULT").?,
    );
    try std.testing.expect(!ct_artifact.has_errors);
    try std.testing.expectEqual(@as(i128, 60), ct_artifact.value.int_val);
    try std.testing.expect(db.comptime_elab_mirs.count() >= 1);
}

test "test_phase6_region_escape_e0306_return_param_flow_wrapper_and_closures" {
    const allocator = std.testing.allocator;

    // [1] Stack & lexical `BumpArena` escape via `return` emits `E0306`:
    const ret_escape_src =
        \\pub fn escape_stack_slice() -> &[i64] {
        \\    let local_arr: [i64; 3] = [10, 20, 30];
        \\    return &local_arr;
        \\}
    ;
    try expectSastDiagnostic(allocator, 301, ret_escape_src, .{}, .e0306_region_escape_violation);

    // [2] `[CRITICAL-05]` `param_flow_matrix` exact `src_ord * 8 + dst_ord` bit direction (`bit 8`, NOT `1`):
    const param_flow_ok_src =
        \\pub fn assign_ref_slot(dst_slot: &mut &i64, src_ref: &i64) {
        \\    dst_slot.* = src_ref;
        \\}
        \\pub fn outer_into_inner_is_sound(seed: &i64) -> i64 {
        \\    let outer_val: i64 = 42;
        \\    let outer_ref: &i64 = &outer_val;
        \\    {
        \\        var inner_slot: &i64 = seed;
        \\        assign_ref_slot(&mut inner_slot, outer_ref);
        \\        return inner_slot.*;
        \\    }
        \\}
    ;
    var flow_ok_bundle = try verifyCleanSast(allocator, 302, param_flow_ok_src, .{});
    defer flow_ok_bundle.deinit();

    // Verify `assign_ref_slot` (`dst_ord = 0`, `src_ord = 1`) sets `1 << (1 * 8 + 0)` == `1 << 8`:
    const assign_body = flow_ok_bundle.mir_module.findBodyByName(
        &flow_ok_bundle.interner,
        "assign_ref_slot",
    ).?;
    var has_assign_summary = false;
    for (flow_ok_bundle.sast_result.summary_store.symbol_indices, 0..) |sym_idx, slot_i| {
        if (sym_idx == assign_body.symbol_index) {
            has_assign_summary = true;
            try std.testing.expectEqual(
                @as(u64, 1) << 8,
                flow_ok_bundle.sast_result.summary_store.summaries[slot_i].param_flow_matrix,
            );
        }
    }
    try std.testing.expect(has_assign_summary);

    const param_flow_escape_src =
        \\pub fn assign_ref_slot(dst_slot: &mut &i64, src_ref: &i64) {
        \\    dst_slot.* = src_ref;
        \\}
        \\pub fn inner_into_outer_escapes(seed: &i64) -> i64 {
        \\    var outer_slot: &i64 = seed;
        \\    {
        \\        let inner_val: i64 = 99;
        \\        assign_ref_slot(&mut outer_slot, &inner_val);
        \\    }
        \\    return outer_slot.*;
        \\}
    ;
    try expectSastDiagnostic(allocator, 303, param_flow_escape_src, .{}, .e0306_region_escape_violation);

    // [3] `[CRITICAL-06]` Nominal wrapper struct carrying borrowed view cannot escape stack frame:
    const wrapper_escape_src =
        \\pub struct PacketView {
        \\    pub bytes: &[u8],
        \\}
        \\pub fn make_dangling_view() -> PacketView {
        \\    let stack_buf: [u8; 4] = [1, 2, 3, 4];
        \\    return PacketView { bytes: &stack_buf };
        \\}
    ;
    try expectSastDiagnostic(allocator, 304, wrapper_escape_src, .{}, .e0306_region_escape_violation);

    // [4] `@local` non-escaping closure borrow passes (`0` errors) vs escaping closure (`E0306`):
    const local_closure_ok_src =
        \\pub fn eval_local_borrow_closure() -> i64 {
        \\    let base_num: i64 = 40;
        \\    let base_ref: &i64 = &base_num;
        \\    @local let add_to_base = || -> i64 { base_ref.* +% 2 };
        \\    return add_to_base();
        \\}
    ;
    var clos_ok_bundle = try verifyCleanSast(allocator, 305, local_closure_ok_src, .{});
    defer clos_ok_bundle.deinit();

    const escaping_closure_src =
        \\pub struct BumpArena {
        \\    pub buf: [u8; 8],
        \\}
        \\impl BumpArena {
        \\    pub fn view_bytes(&mut self) -> &[u8] {
        \\        return &self.buf;
        \\    }
        \\    pub fn deinit(own self) {
        \\        let BumpArena { buf: _ } = self;
        \\    }
        \\}
        \\pub fn escape_inner_region_via_closure(fallback: &[u8]) -> usize {
        \\    var outer_clos = || -> usize { fallback.len() };
        \\    {
        \\        var inner_arena = BumpArena { buf: [1, 2, 3, 4, 5, 6, 7, 8] };
        \\        let inner_view = inner_arena.view_bytes();
        \\        outer_clos = || -> usize { inner_view.len() };
        \\        inner_arena.deinit();
        \\    }
        \\    return outer_clos();
        \\}
    ;
    try expectSastDiagnostic(allocator, 306, escaping_closure_src, .{}, .e0306_region_escape_violation);
}

test "test_phase6_max_stack_e0316_malformed_attr_and_contracts_e0320_to_e0323" {
    const allocator = std.testing.allocator;

    // [1] `D-02` `@max_stack(N)`: bounded tree passes; tight budget & recursion emit `E0316`:
    const max_stack_ok_src =
        \\pub fn leaf_frame(val: i64) -> i64 {
        \\    let scratch_pad: [i64; 4] = [val, val, val, val];
        \\    return scratch_pad[0];
        \\}
        \\@max_stack(512)
        \\pub fn bounded_entry(val: i64) -> i64 {
        \\    return leaf_frame(val);
        \\}
    ;
    var stk_ok_bundle = try verifyCleanSast(allocator, 310, max_stack_ok_src, .{});
    defer stk_ok_bundle.deinit();

    const max_stack_exceed_src =
        \\pub fn heavy_leaf(val: i64) -> i64 {
        \\    let big_buf: [i64; 16] = [val; 16];
        \\    return big_buf[0];
        \\}
        \\@max_stack(16)
        \\pub fn tight_budget_caller(val: i64) -> i64 {
        \\    return heavy_leaf(val);
        \\}
        \\@max_stack(256)
        \\pub fn recursive_budget_caller(depth: i32) -> i32 {
        \\    if depth <= 0 { return 0; }
        \\    return recursive_budget_caller(depth -% 1);
        \\}
    ;
    var stk_bad_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(311),
        max_stack_exceed_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer stk_bad_bundle.deinit();
    try std.testing.expectEqual(
        @as(usize, 2),
        countDiagnosticCode(&stk_bad_bundle.diagnostics, .e0316_max_stack_budget_exceeded),
    );

    // `[MINOR-18]` Malformed `@max_stack(-8)` and `@max_stack()` emit `.e0406_range_refinement_violation`:
    const malformed_max_stack_src =
        \\@max_stack(-8)
        \\pub fn neg_budget() -> i32 { return 0; }
        \\@max_stack()
        \\pub fn empty_budget() -> i32 { return 0; }
    ;
    var malformed_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(312),
        malformed_max_stack_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer malformed_bundle.deinit();
    try std.testing.expectEqual(
        @as(usize, 2),
        countDiagnosticCode(&malformed_bundle.diagnostics, .e0406_range_refinement_violation),
    );

    // [2] Multi-hop `@no_alloc` (`E0320`), `@no_panic` (`E0321`), `@no_block` (`E0322`) + witness BFS:
    const multi_hop_contracts_src =
        \\extern "C" fn blocking_os_call() -> i32;
        \\pub struct Context {
        \\    pub allocator: usize,
        \\}
        \\pub fn leaf_alloc(ctx: &Context) -> usize {
        \\    return ctx.allocator;
        \\}
        \\pub fn mid_alloc(ctx: &Context) -> usize {
        \\    return leaf_alloc(ctx);
        \\}
        \\@no_alloc
        \\pub fn root_no_alloc(ctx: &Context) -> usize {
        \\    return mid_alloc(ctx);
        \\}
        \\pub fn leaf_panic(items: &[i64], idx: usize) -> i64 {
        \\    return items[idx];
        \\}
        \\pub fn mid_panic(items: &[i64], idx: usize) -> i64 {
        \\    return leaf_panic(items, idx);
        \\}
        \\@no_panic
        \\pub fn root_no_panic(items: &[i64], idx: usize) -> i64 {
        \\    return mid_panic(items, idx);
        \\}
        \\pub fn mid_block() -> i32 {
        \\    return unsafe { blocking_os_call() };
        \\}
        \\@no_block
        \\pub fn root_no_block() -> i32 {
        \\    return mid_block();
        \\}
    ;
    var hop_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(313),
        multi_hop_contracts_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer hop_bundle.deinit();
    try std.testing.expect(hasDiagnosticCode(&hop_bundle.diagnostics, .e0320_no_alloc_contract_violation));
    try std.testing.expect(hasDiagnosticCode(&hop_bundle.diagnostics, .e0321_no_panic_contract_violation));
    try std.testing.expect(hasDiagnosticCode(&hop_bundle.diagnostics, .e0322_no_block_contract_violation));

    // Reconstruct shortest 2-hop witness chain `root_no_alloc -> mid_alloc -> leaf_alloc`:
    const root_alloc_body = hop_bundle.mir_module.findBodyByName(
        &hop_bundle.interner,
        "root_no_alloc",
    ).?;
    var root_slot_opt: ?u32 = null;
    for (hop_bundle.sast_result.summary_store.symbol_indices, 0..) |sym_idx, slot_i| {
        if (sym_idx == root_alloc_body.symbol_index) root_slot_opt = @intCast(slot_i);
    }
    const witness_steps = try hop_bundle.sast_result.summary_store.reconstructShortestWitness(
        allocator,
        root_slot_opt.?,
        EffectCapabilityMask.ALLOC_BIT,
    );
    defer allocator.free(witness_steps);
    try std.testing.expectEqual(@as(usize, 2), witness_steps.len);
    try std.testing.expectEqual(WitnessEdgeKind.direct_call, witness_steps[0].edge.meta().edge_kind);

    // [3] `[MAJOR-09]` & `[CRITICAL-02]` Higher-order callback forwarding & mutable local `var` callable:
    const ho_pure_ok_src =
        \\pub fn apply_step(val: i32, cb: fn(i32) -> i32) -> i32 {
        \\    return cb(val);
        \\}
        \\@no_alloc
        \\pub fn pure_inc(val: i32) -> i32 {
        \\    return val +% 1;
        \\}
        \\@no_alloc
        \\pub fn caller_ho_pure(val: i32) -> i32 {
        \\    return apply_step(val, pure_inc);
        \\}
    ;
    var ho_ok_bundle = try verifyCleanSast(allocator, 314, ho_pure_ok_src, .{});
    defer ho_ok_bundle.deinit();

    const ho_impure_and_reassigned_src =
        \\pub struct Context {
        \\    pub allocator: usize,
        \\}
        \\pub fn apply_with_ctx(ctx: &Context, cb: fn(&Context) -> usize) -> usize {
        \\    return cb(ctx);
        \\}
        \\pub fn pure_cb(ctx: &Context) -> usize {
        \\    let _ = ctx;
        \\    return 0;
        \\}
        \\pub fn alloc_cb(ctx: &Context) -> usize {
        \\    return ctx.allocator;
        \\}
        \\@no_alloc
        \\pub fn bad_ho_forwarding(ctx: &Context) -> usize {
        \\    return apply_with_ctx(ctx, alloc_cb);
        \\}
        \\@no_alloc
        \\pub fn bad_reassigned_local_fn_ptr(ctx: &Context, flag: bool) -> usize {
        \\    var chosen_cb: fn(&Context) -> usize = pure_cb;
        \\    if flag {
        \\        chosen_cb = alloc_cb;
        \\    }
        \\    return chosen_cb(ctx);
        \\}
    ;
    var ho_bad_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(315),
        ho_impure_and_reassigned_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer ho_bad_bundle.deinit();
    try std.testing.expectEqual(
        @as(usize, 2),
        countDiagnosticCode(&ho_bad_bundle.diagnostics, .e0320_no_alloc_contract_violation),
    );

    // [4] `[MAJOR-15]` Trait `impl` effect escalation (`E0323`) vs same-named inherent method (`0` errors):
    const inherent_same_name_ok_src =
        \\pub trait StrictCodec {
        \\    @no_panic
        \\    fn decode_at(&self, data: &[i64], idx: usize) -> i64;
        \\}
        \\pub struct UnrelatedReader {}
        \\impl UnrelatedReader {
        \\    pub fn decode_at(&self, data: &[i64], idx: usize) -> i64 {
        \\        return data[idx];
        \\    }
        \\}
    ;
    var inherent_ok_bundle = try verifyCleanSast(allocator, 316, inherent_same_name_ok_src, .{});
    defer inherent_ok_bundle.deinit();

    const trait_impl_escalation_src =
        \\pub trait StrictCodec {
        \\    @no_panic
        \\    fn decode_at(&self, data: &[i64], idx: usize) -> i64;
        \\}
        \\pub struct EscalatingReader {}
        \\impl StrictCodec for EscalatingReader {
        \\    @no_panic
        \\    pub fn decode_at(&self, data: &[i64], idx: usize) -> i64 {
        \\        return data[idx];
        \\    }
        \\}
    ;
    try expectSastDiagnostic(
        allocator,
        317,
        trait_impl_escalation_src,
        .{},
        .e0323_trait_impl_effect_escalation,
    );
}

test "test_phase6_fix17_gates_a_to_f_sandbox_policies_and_fix06b_vacated_w0329" {
    const allocator = std.testing.allocator;

    // [1] `Fix-17` Gate B/C: `@link_section(".init_array")` & user `@std_cap_boundary` emit `E0327`:
    try std.testing.expect(symbol_resolver.isForbiddenExecutableSection(".init_array"));
    try std.testing.expect(symbol_resolver.isForbiddenExecutableSection(".CRT$XCU"));
    const bypass_attr_src =
        \\@link_section(".init_array")
        \\pub fn ctor_hook() {}
        \\@std_cap_boundary(emits: [fs])
        \\pub fn spoofed_boundary() {}
    ;
    var bypass_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(320),
        bypass_attr_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bypass_bundle.deinit();
    try std.testing.expect(
        countDiagnosticCode(&bypass_bundle.diagnostics, .e0327_forbidden_sandbox_bypass_attribute) >= 2,
    );

    // Inside `std` (`Durability.high`), `@std_cap_boundary(clears: [ffi_unsafe], emits: [fs])` firewalls FFI:
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    const std_file = FileId.fromInt(321);
    const std_firewall_src =
        \\extern "C" fn sys_open_raw() -> i32;
        \\@std_cap_boundary(clears: [ffi_unsafe], emits: [fs])
        \\pub fn std_fs_open() -> i32 {
        \\    return unsafe { sys_open_raw() };
        \\}
    ;
    _ = try db.setInput(std_file, std_firewall_src, .high);
    const std_tree = try db.extractItemTree(std_file);
    const std_open_def = findDefIdByName(std_tree.entries, "std_fs_open").?;
    try std.testing.expect((try db.verifySastMir(std_open_def)).is_verified_sound);
    const std_effects = (try db.getSastSummaryProj(std_open_def)).inferredEffects();
    try std.testing.expect(std_effects.fs);
    try std.testing.expect(!std_effects.ffi);
    try std.testing.expect(!std_effects.unsafe_op);

    // [2] `Fix-17` Gate D: `@embed_bytes` path traversal / Windows device rejection (`E0326`) vs VFS success:
    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(allocator);
    try vfs_map.put(allocator, "assets/banner.txt", "COREX");
    db.setEmbedSandbox(null, &vfs_map);

    const embed_file = FileId.fromInt(322);
    const embed_src =
        \\pub const OK_LEN: usize = @embed_bytes("assets/banner.txt").len();
        \\pub const ESCAPE_LEN: usize = @embed_bytes("../secret.key").len();
        \\pub const DEVICE_LEN: usize = @embed_bytes("CON.txt").len();
    ;
    _ = try db.setInput(embed_file, embed_src, .low);
    const embed_tree = try db.extractItemTree(embed_file);

    const ok_embed_art = try db.evalComptimeDef(findDefIdByName(embed_tree.entries, "OK_LEN").?);
    try std.testing.expect(!ok_embed_art.has_errors);
    try std.testing.expectEqual(@as(i128, 5), ok_embed_art.value.int_val);

    const esc_def = findDefIdByName(embed_tree.entries, "ESCAPE_LEN").?;
    const esc_art = try db.evalComptimeDef(esc_def);
    try std.testing.expect(esc_art.has_errors);
    try std.testing.expect(hasDiagnosticCode(db.getComptimeDiagnostics(esc_def).?, .e0326_embed_path_escape));

    const dev_def = findDefIdByName(embed_tree.entries, "DEVICE_LEN").?;
    const dev_art = try db.evalComptimeDef(dev_def);
    try std.testing.expect(dev_art.has_errors);
    try std.testing.expect(hasDiagnosticCode(db.getComptimeDiagnostics(dev_def).?, .e0326_embed_path_escape));

    // [3] `Fix-17` Gate E (`[MINOR-19]`): `PackageCapPolicy` `.surface` vs `.all` (`E0324`) & dead `ffi` (`W0330`):
    const pkg_scope_src =
        \\extern "C" fn raw_net_send() -> i32;
        \\pub fn pure_surface_api(val: i32) -> i32 {
        \\    return val +% 10;
        \\}
        \\@export
        \\fn internal_export_root() -> i32 {
        \\    return unsafe { raw_net_send() };
        \\}
        \\fn dead_ambient_helper() -> i32 {
        \\    return unsafe { raw_net_send() };
        \\}
    ;
    const surface_policy = PackageCapPolicy{
        .package_name = "scoped_dep",
        .allowed_caps = EffectCapabilityMask.EMPTY,
        .enforcement_scope = CapEnforcementScope.surface,
        .is_third_party_dependency = false,
        .policy_span = Span.init(FileId.fromInt(323), 0, 10),
    };
    var surface_bundle = try verifyCleanSast(
        allocator,
        323,
        pkg_scope_src,
        .{ .package_policy = surface_policy },
    );
    defer surface_bundle.deinit();

    var all_policy = surface_policy;
    all_policy.enforcement_scope = CapEnforcementScope.all;
    try expectSastDiagnostic(
        allocator,
        324,
        pkg_scope_src,
        .{ .package_policy = all_policy },
        .e0324_package_capability_violation,
    );

    const dead_only_dep_src =
        \\extern "C" fn hidden_c_hook() -> i32;
        \\pub fn safe_math(val: i32) -> i32 {
        \\    return val +% 2;
        \\}
        \\fn unreachable_c_wrapper() -> i32 {
        \\    return unsafe { hidden_c_hook() };
        \\}
    ;
    var dead_dep_bundle = try verifyCleanSast(
        allocator,
        325,
        dead_only_dep_src,
        .{
            .package_policy = .{
                .package_name = "third_party_math",
                .allowed_caps = EffectCapabilityMask.EMPTY,
                .enforcement_scope = CapEnforcementScope.all,
                .is_third_party_dependency = true,
                .policy_span = Span.init(FileId.fromInt(325), 0, 10),
            },
        },
    );
    defer dead_dep_bundle.deinit();
    try std.testing.expect(
        hasDiagnosticCode(&dead_dep_bundle.diagnostics, .w0330_ambient_dead_capability_in_dep),
    );

    // [4] `Fix-17` Gate F: Hermetic `comptime` capability violation (`E0325`):
    const bad_comptime_src =
        \\extern "C" fn host_entropy_u32() -> i32;
        \\pub fn entropy_bridge() -> i32 {
        \\    return unsafe { host_entropy_u32() };
        \\}
        \\pub const BAD_SEED: i32 = entropy_bridge();
    ;
    try expectSastDiagnostic(allocator, 326, bad_comptime_src, .{}, .e0325_comptime_sandbox_violation);

    // [5] `Fix-06B` (`[MAJOR-10]`): Multi-block `if`/`else` inside vacated non-`Copy` `inout` `subscript` window:
    const vacated_subscript_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct NonCopySlot {
        \\    pub buf: Vec[i64],
        \\}
        \\pub struct SlotPair {
        \\    pub items: [NonCopySlot; 2],
        \\}
        \\impl SlotPair {
        \\    pub subscript(idx: usize) -> NonCopySlot {
        \\        inout {
        \\            yield &mut self.items[idx];
        \\        }
        \\    }
        \\}
        \\pub fn write_through_vacated_branch(
        \\    use_branch_a: bool,
        \\    lookup_idx: usize,
        \\) -> usize {
        \\    var slots = SlotPair {
        \\        items: [
        \\            NonCopySlot { buf: Vec { len: 1 } },
        \\            NonCopySlot { buf: Vec { len: 2 } },
        \\        ],
        \\    };
        \\    let table: [usize; 2] = [10, 20];
        \\    slots[0] = if use_branch_a {
        \\        NonCopySlot { buf: Vec { len: table[lookup_idx] } }
        \\    } else {
        \\        NonCopySlot { buf: Vec { len: 99 } }
        \\    };
        \\    return slots.items[0].buf.len;
        \\}
    ;
    var vacated_bundle = try verifyCleanSast(allocator, 327, vacated_subscript_src, .{});
    defer vacated_bundle.deinit();
    try std.testing.expect(
        hasDiagnosticCode(&vacated_bundle.diagnostics, .w0329_vacated_projection_panic_abort),
    );

    const vacated_body = vacated_bundle.mir_module.findBodyByName(
        &vacated_bundle.interner,
        "write_through_vacated_branch",
    ).?;
    try std.testing.expect(hasBodyIntrinsic(vacated_body, .abort_vacated_panic));

    // Verify `MirVm` triggers immediate non-unwinding `error.AbortedVacatedPanic` on OOB inside vacated window:
    var vm_rodata = RodataPool.init(allocator);
    defer vm_rodata.deinit();
    var vm_sink = DiagnosticSink.init(allocator);
    defer vm_sink.deinit();
    var vm = try MirVm.init(
        allocator,
        &vacated_bundle.interner,
        &vacated_bundle.pool,
        &vacated_bundle.sym_table,
        &vm_rodata,
        null,
        &vm_sink,
        .{},
    );
    defer vm.deinit();
    for (vacated_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    const ok_eval = try vm.evalBody(
        vacated_body,
        &[_]RegSlot{ .{ .scalar_u64 = 1 }, .{ .scalar_u64 = 1 } },
    );
    try std.testing.expectEqual(@as(u64, 20), ok_eval.slot.scalar_u64);
    try std.testing.expect(!vm.has_aborted_vacated_panic);

    try std.testing.expectError(
        error.AbortedVacatedPanic,
        vm.evalBody(
            vacated_body,
            &[_]RegSlot{ .{ .scalar_u64 = 1 }, .{ .scalar_u64 = 5 } },
        ),
    );
    try std.testing.expect(vm.has_aborted_vacated_panic);

    // Under `@no_panic`, a panicking vacated `subscript` window is rejected with `E0321`:
    const vacated_no_panic_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct NonCopySlot {
        \\    pub buf: Vec[i64],
        \\}
        \\pub struct SlotPair {
        \\    pub items: [NonCopySlot; 2],
        \\}
        \\impl SlotPair {
        \\    pub subscript(idx: usize) -> NonCopySlot {
        \\        inout {
        \\            yield &mut self.items[idx];
        \\        }
        \\    }
        \\}
        \\@no_panic
        \\pub fn bad_no_panic_vacated(slots: &mut SlotPair, table: &[usize], idx: usize) {
        \\    if slots.items.len() > 0 {
        \\        slots.*[0] = NonCopySlot { buf: Vec { len: table[idx] } };
        \\    }
        \\}
    ;
    try expectSastDiagnostic(
        allocator,
        328,
        vacated_no_panic_src,
        .{},
        .e0321_no_panic_contract_violation,
    );
}

test "test_phase6_compiler_db_stage9_early_cutoff_and_mutual_recursion_sccs" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    // [1] 34-byte `getSastSummaryProj` Early Cutoff stability across private body edits:
    const cutoff_file = FileId.fromInt(340);
    const cutoff_v1 =
        \\pub fn helper_math(val: i64) -> i64 {
        \\    let doubled = val +% val;
        \\    return doubled;
        \\}
        \\@no_alloc
        \\@no_panic
        \\pub fn caller_entry(val: i64) -> i64 {
        \\    return helper_math(val);
        \\}
    ;
    const rev_one = try db.setInput(cutoff_file, cutoff_v1, .low);
    const tree_one = try db.extractItemTree(cutoff_file);
    const helper_def = findDefIdByName(tree_one.entries, "helper_math").?;
    const caller_def = findDefIdByName(tree_one.entries, "caller_entry").?;

    try std.testing.expect((try db.verifySastMir(caller_def)).is_verified_sound);

    const cutoff_v2 =
        \\pub fn helper_math(val: i64) -> i64 {
        \\    let doubled = (val *% 3) -% val;
        \\    return doubled;
        \\}
        \\@no_alloc
        \\@no_panic
        \\pub fn caller_entry(val: i64) -> i64 {
        \\    return helper_math(val);
        \\}
    ;
    const rev_two = try db.setInput(cutoff_file, cutoff_v2, .low);
    try std.testing.expect(rev_two.isAfter(rev_one));

    try std.testing.expect((try db.verifySastMir(caller_def)).is_verified_sound);
    const proj_memo = db.getMemoHeader(QueryKey.forSastSummaryProj(helper_def)).?;
    const caller_memo = db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, caller_def)).?;
    try std.testing.expectEqual(rev_one, proj_memo.changed_at);
    try std.testing.expectEqual(rev_one, caller_memo.changed_at);
    try std.testing.expectEqual(rev_two, caller_memo.verified_at);

    // Increasing `max_subtree_bytes` changes the 34-byte observable projection and invalidates `proj_memo`:
    const cutoff_v3 =
        \\pub fn helper_math(val: i64) -> i64 {
        \\    let local_pad: [i64; 8] = [val; 8];
        \\    return (local_pad[0] *% 3) -% 1;
        \\}
        \\@no_alloc
        \\@no_panic
        \\pub fn caller_entry(val: i64) -> i64 {
        \\    return helper_math(val);
        \\}
    ;
    const rev_three = try db.setInput(cutoff_file, cutoff_v3, .low);
    try std.testing.expect((try db.verifySastMir(caller_def)).is_verified_sound);
    const proj_memo_v3 = db.getMemoHeader(QueryKey.forSastSummaryProj(helper_def)).?;
    try std.testing.expectEqual(rev_three, proj_memo_v3.changed_at);

    // [2] `[CRITICAL-03]` Cross-`DefId` mutual recursion: pure `@no_alloc @no_panic` passes; `@max_stack` fails:
    const scc_ok_file = FileId.fromInt(341);
    const scc_pure_src =
        \\@no_alloc
        \\@no_panic
        \\pub fn ping_even(steps: u32) -> bool {
        \\    if steps == 0 { return true; }
        \\    return pong_odd(steps -% 1);
        \\}
        \\@no_alloc
        \\@no_panic
        \\pub fn pong_odd(steps: u32) -> bool {
        \\    if steps == 0 { return false; }
        \\    return ping_even(steps -% 1);
        \\}
    ;
    _ = try db.setInput(scc_ok_file, scc_pure_src, .low);
    const scc_ok_tree = try db.extractItemTree(scc_ok_file);
    const ping_def = findDefIdByName(scc_ok_tree.entries, "ping_even").?;
    const pong_def = findDefIdByName(scc_ok_tree.entries, "pong_odd").?;

    try std.testing.expect((try db.verifySastMir(ping_def)).is_verified_sound);
    try std.testing.expect((try db.verifySastMir(pong_def)).is_verified_sound);
    try std.testing.expectEqual(
        FnRegionSummary.STACK_UNBOUNDED,
        (try db.getSastSummaryProj(ping_def)).max_subtree_bytes,
    );

    const scc_stack_file = FileId.fromInt(342);
    const scc_stack_src =
        \\@max_stack(256)
        \\pub fn alpha_rec(steps: u32) -> u32 {
        \\    if steps == 0 { return 0; }
        \\    return beta_rec(steps -% 1);
        \\}
        \\pub fn beta_rec(steps: u32) -> u32 {
        \\    if steps == 0 { return 1; }
        \\    return alpha_rec(steps -% 1);
        \\}
    ;
    _ = try db.setInput(scc_stack_file, scc_stack_src, .low);
    const scc_stack_tree = try db.extractItemTree(scc_stack_file);
    const alpha_def = findDefIdByName(scc_stack_tree.entries, "alpha_rec").?;
    try std.testing.expect(!(try db.verifySastMir(alpha_def)).is_verified_sound);
    try std.testing.expect(
        hasDiagnosticCode(db.getSastDiagnostics(alpha_def).?, .e0316_max_stack_budget_exceeded),
    );
}

test "test_phase6_intv_lattice_pentagon_subrow_and_wasm32_usize_clamp" {
    const allocator = std.testing.allocator;

    // [1] `Intv` sign-biased monotonic encoding (`i64.min -> 0`, `-1 < 0`, `i64.max -> u64.max`) & lattice ops:
    try std.testing.expectEqual(@as(u64, 0), Intv.encodeSigned(std.math.minInt(i64)));
    try std.testing.expectEqual(std.math.maxInt(u64), Intv.encodeSigned(std.math.maxInt(i64)));
    try std.testing.expect(Intv.encodeSigned(-1) < Intv.encodeSigned(0));

    const signed_neg = Intv.initSigned(-50, -5);
    const signed_pos = Intv.initSigned(10, 80);
    const signed_overlap = Intv.initSigned(-10, 20);
    try std.testing.expect(Intv.initSigned(10, -1).isBottom());
    try std.testing.expect(Intv.BOTTOM.join(signed_neg).eql(signed_neg));
    try std.testing.expect(signed_neg.meet(signed_pos).isBottom());

    const met_iv = signed_neg.join(signed_pos).meet(signed_overlap);
    try std.testing.expectEqual(@as(i64, -10), Intv.decodeSigned(met_iv.lo_ord));
    try std.testing.expectEqual(@as(i64, 20), Intv.decodeSigned(met_iv.hi_ord));

    // [2] `PentagonSubRow` 256-bit strict upper-bound set across all four `u64` words:
    var row_lhs = PentagonSubRow{};
    var row_rhs = PentagonSubRow{};
    row_lhs.insert(3);
    row_lhs.insert(70);
    row_lhs.insert(250);
    row_rhs.insert(70);
    row_rhs.insert(199);

    const row_inter = row_lhs.intersectWith(row_rhs);
    try std.testing.expect(!row_inter.contains(3));
    try std.testing.expect(row_inter.contains(70));
    try std.testing.expect(!row_inter.contains(250));

    const row_union = row_lhs.unionWith(row_rhs);
    try std.testing.expect(row_union.contains(3));
    try std.testing.expect(row_union.contains(199));
    try std.testing.expect(row_union.contains(250));

    // [3] Checked `+`, wrapping `+%`, bitwise `&` BCE, & `WASM32` 32-bit `usize` clamp vs `NATIVE_64`:
    const mask_and_wasm_src =
        \\@no_panic
        \\pub fn masked_arith_and_wasm_usize(table: &[i64; 8], raw_idx: usize) -> u32 {
        \\    let checked_idx = (raw_idx & 3) + 2;
        \\    let wrapped_idx = (raw_idx & 3) +% 1;
        \\    let sum_pair = table[checked_idx] +% table[wrapped_idx];
        \\    let low_bits: usize = raw_idx & 255;
        \\    let narrowed: u32 = low_bits.narrow[u32]();
        \\    let _ = sum_pair;
        \\    return narrowed;
        \\}
    ;
    var wasm_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(401),
        mask_and_wasm_src,
        TargetLayout.WASM32,
        .{ .is_sast_strict = true },
    );
    defer wasm_bundle.deinit();
    try std.testing.expect(!wasm_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(usize, 0), wasm_bundle.diagnostics.diagnostics.items.len);
    try std.testing.expectEqual(@as(u32, 2), wasm_bundle.sast_result.eliminated_bounds_checks);
    try std.testing.expectEqual(@as(u32, 1), wasm_bundle.sast_result.eliminated_narrow_checks);

    // On `WASM32`, `usize` has 32-bit upper bound `[0, u32.max]`, so `raw_usize.narrow[u32]()` is statically proven!
    // On `NATIVE_64`, `usize` is 64-bit, so unmasked `raw_usize.narrow[u32]()` retains `narrow_check` (`E0321` in `@no_panic`):
    const usize_to_u32_src =
        \\@no_panic
        \\pub fn narrow_usize_to_u32(raw_usize: usize) -> u32 {
        \\    return raw_usize.narrow[u32]();
        \\}
    ;
    var wasm32_usize_ok = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(402),
        usize_to_u32_src,
        TargetLayout.WASM32,
        .{},
    );
    defer wasm32_usize_ok.deinit();
    try std.testing.expect(!wasm32_usize_ok.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(u32, 1), wasm32_usize_ok.sast_result.eliminated_narrow_checks);

    var native64_usize_fail = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(403),
        usize_to_u32_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer native64_usize_fail.deinit();
    try std.testing.expect(
        hasDiagnosticCode(&native64_usize_fail.diagnostics, .e0321_no_panic_contract_violation),
    );
}

test "test_phase6_pentagon_bce_for_range_rem_u_static_oob_e0307_and_strict_w0314" {
    const allocator = std.testing.allocator;

    // [1] Static out-of-bounds `E0307` on constant & interval-proven OOB index:
    const static_oob_src =
        \\pub fn bad_interval_oob(flag: bool) -> i64 {
        \\    let items: [i64; 4] = [10, 20, 30, 40];
        \\    let bad_idx: usize = if flag { 4 } else { 6 };
        \\    return items[bad_idx];
        \\}
    ;
    try expectSastDiagnostic(allocator, 410, static_oob_src, .{}, .e0307_static_buffer_overflow);

    // [2] Pentagon relational BCE (`if idx < slice.len()`, `for i in 0..slice.len()`, and `raw % slice.len()`):
    const pentagon_bce_src =
        \\@no_panic
        \\pub fn sum_verified_patterns(slice: &[i64], idx: usize, raw: usize) -> i64 {
        \\    var total: i64 = 0;
        \\    if idx < slice.len() {
        \\        total = total +% slice[idx];
        \\    }
        \\    for i in 0..slice.len() {
        \\        total = total +% slice[i];
        \\    }
        \\    if slice.len() > 0 {
        \\        total = total +% slice[raw % slice.len()];
        \\    }
        \\    return total;
        \\}
    ;
    var bce_bundle = try verifyCleanSast(
        allocator,
        411,
        pentagon_bce_src,
        .{ .is_sast_strict = true },
    );
    defer bce_bundle.deinit();
    try std.testing.expectEqual(@as(usize, 0), bce_bundle.diagnostics.diagnostics.items.len);
    try std.testing.expect(bce_bundle.sast_result.eliminated_bounds_checks >= 3);
    try std.testing.expect(bce_bundle.sast_result.peak_pentagon_bytes < 1_500_000);

    // [3] `--sast-strict` (`is_sast_strict = true`) emits `W0314` on unproven dynamic bounds access:
    const unproven_bounds_src =
        \\pub fn unchecked_dynamic_read(slice: &[i64], dyn_idx: usize) -> i64 {
        \\    return slice[dyn_idx];
        \\}
    ;
    var strict_bundle = try verifyCleanSast(
        allocator,
        412,
        unproven_bounds_src,
        .{ .is_sast_strict = true },
    );
    defer strict_bundle.deinit();
    try std.testing.expect(
        hasDiagnosticCode(&strict_bundle.diagnostics, .w0314_unproven_bounds_access),
    );
}

test "test_phase6_critical01_mutable_slice_reassignment_zero_mod_and_d11_narrow_e0406" {
    const allocator = std.testing.allocator;

    // [1] `[CRITICAL-01]` Reassigning mutable `var cur_slice` after `if idx < cur_slice.len()` MUST NOT elide BCE:
    const mut_slice_reassign_src =
        \\@no_panic
        \\pub fn bad_reassigned_slice_bce(long_s: &[i64], short_s: &[i64], idx: usize) -> i64 {
        \\    var cur_slice: &[i64] = long_s;
        \\    if idx < cur_slice.len() {
        \\        cur_slice = short_s;
        \\        return cur_slice[idx];
        \\    }
        \\    return 0;
        \\}
        \\pub fn warn_reassigned_slice_bce(long_s: &[i64], short_s: &[i64], idx: usize) -> i64 {
        \\    var cur_slice: &[i64] = long_s;
        \\    if idx < cur_slice.len() {
        \\        cur_slice = short_s;
        \\        return cur_slice[idx];
        \\    }
        \\    return 0;
        \\}
    ;
    var mut_slice_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(420),
        mut_slice_reassign_src,
        TargetLayout.NATIVE_64,
        .{ .is_sast_strict = true },
    );
    defer mut_slice_bundle.deinit();
    try std.testing.expectEqual(@as(u32, 0), mut_slice_bundle.sast_result.eliminated_bounds_checks);
    try std.testing.expect(
        hasDiagnosticCode(&mut_slice_bundle.diagnostics, .e0321_no_panic_contract_violation),
    );
    try std.testing.expect(
        hasDiagnosticCode(&mut_slice_bundle.diagnostics, .w0314_unproven_bounds_access),
    );

    // [2] `[CRITICAL-01]` `raw % divisor` when `0` is in `Intv(divisor)` MUST NOT elide panic/bounds checks:
    const unguarded_mod_src =
        \\@no_panic
        \\pub fn bad_zero_possible_modulo(slice: &[i64], raw: usize) -> i64 {
        \\    return slice[raw % slice.len()];
        \\}
    ;
    var zero_mod_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(421),
        unguarded_mod_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer zero_mod_bundle.deinit();
    try std.testing.expectEqual(@as(u32, 0), zero_mod_bundle.sast_result.eliminated_bounds_checks);
    try std.testing.expect(
        hasDiagnosticCode(&zero_mod_bundle.diagnostics, .e0321_no_panic_contract_violation),
    );

    // [3] `D-11` `.narrow[u8]()`: interval-proven narrowing elides `narrow_check`; static OOR emits `E0406`:
    const proven_narrow_src =
        \\@no_panic
        \\pub fn narrow_proven_byte(val: i32) -> u8 {
        \\    if val >= 0 and val <= 255 {
        \\        return val.narrow[u8]();
        \\    }
        \\    return 0;
        \\}
    ;
    var narrow_ok_bundle = try verifyCleanSast(allocator, 422, proven_narrow_src, .{});
    defer narrow_ok_bundle.deinit();
    try std.testing.expectEqual(@as(u32, 1), narrow_ok_bundle.sast_result.eliminated_narrow_checks);

    const static_bad_narrow_src =
        \\pub fn narrow_negative_to_u8() -> u8 {
        \\    let neg: i32 = -5;
        \\    return neg.narrow[u8]();
        \\}
        \\pub fn narrow_overflow_to_u8() -> u8 {
        \\    let big: i32 = 400;
        \\    return big.narrow[u8]();
        \\}
    ;
    var narrow_bad_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(423),
        static_bad_narrow_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer narrow_bad_bundle.deinit();
    try std.testing.expectEqual(
        @as(usize, 2),
        countDiagnosticCode(&narrow_bad_bundle.diagnostics, .e0406_range_refinement_violation),
    );
}

test "test_phase6_audit_regressions_overflow_params_drops_and_cross_file_caps" {
    const allocator = std.testing.allocator;

    // [1] Pass 4 `u64 * u64` overflow safety; checked `*` emits `E0321` without `i128` panic, `*%` passes:
    const checked_u64_mul_src =
        \\@no_panic
        \\pub fn checked_u64_mul(lhs: u64, rhs: u64) -> u64 {
        \\    return lhs * rhs;
        \\}
    ;
    try expectSastDiagnostic(
        allocator,
        430,
        checked_u64_mul_src,
        .{},
        .e0321_no_panic_contract_violation,
    );

    const wrapping_u64_mul_src =
        \\@no_panic
        \\pub fn wrapping_u64_mul(lhs: u64, rhs: u64) -> u64 {
        \\    return lhs *% rhs;
        \\}
    ;
    var wrap_mul_bundle = try verifyCleanSast(allocator, 431, wrapping_u64_mul_src, .{});
    defer wrap_mul_bundle.deinit();

    // [2] Pass 4 conditional formal-parameter overwrite & `&mut [T]` deref slice length soundness:
    const mut_param_overwrite_src =
        \\@no_panic
        \\pub fn bad_mut_param(var idx: usize, should_clobber: bool, arr: &[i64; 4]) -> i64 {
        \\    if idx < 2 {
        \\        if should_clobber {
        \\            idx = 9;
        \\        }
        \\        return arr[idx];
        \\    }
        \\    return 0;
        \\}
    ;
    var mut_param_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(432),
        mut_param_overwrite_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer mut_param_bundle.deinit();
    try std.testing.expectEqual(@as(u32, 0), mut_param_bundle.sast_result.eliminated_bounds_checks);
    try std.testing.expect(
        hasDiagnosticCode(&mut_param_bundle.diagnostics, .e0321_no_panic_contract_violation),
    );

    const mut_slice_deref_src =
        \\pub fn shrink_slice(slot: &mut &[i64], empty: &[i64]) {
        \\    slot.* = empty;
        \\}
        \\@no_panic
        \\pub fn bad_deref_slice_len(slot: &mut &[i64], empty: &[i64], idx: usize) -> i64 {
        \\    if idx < slot.*.len() {
        \\        shrink_slice(slot, empty);
        \\        return slot.*[idx];
        \\    }
        \\    return 0;
        \\}
    ;
    var mut_deref_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(433),
        mut_slice_deref_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer mut_deref_bundle.deinit();
    try std.testing.expectEqual(@as(u32, 0), mut_deref_bundle.sast_result.eliminated_bounds_checks);
    try std.testing.expect(
        hasDiagnosticCode(&mut_deref_bundle.diagnostics, .e0321_no_panic_contract_violation),
    );

    // [3] Pass 2 projected `own` partial move, conditional `.deinit()` `_drop_flag` clear, & composite `@linear`:
    const sink_partial_and_deinit_src =
        \\pub struct TrackedBuf {
        \\    pub id: i64,
        \\}
        \\impl TrackedBuf {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.id);
        \\    }
        \\    pub fn deinit(own self) {
        \\        @drop_trace(100 + self.id);
        \\        let TrackedBuf { id: _ } = self;
        \\    }
        \\}
        \\pub struct BufPair {
        \\    pub first: TrackedBuf,
        \\    pub second: TrackedBuf,
        \\}
        \\pub fn take_first_or_explicit_deinit(pair: own BufPair, is_explicit: bool) -> i64 {
        \\    var local_buf = TrackedBuf { id: 7 };
        \\    if is_explicit {
        \\        local_buf.deinit();
        \\    }
        \\    let moved_first = pair.first;
        \\    return moved_first.id;
        \\}
        \\pub fn entry_sink_partial(is_explicit: bool) -> i64 {
        \\    let pair = BufPair {
        \\        first: TrackedBuf { id: 1 },
        \\        second: TrackedBuf { id: 2 },
        \\    };
        \\    return take_first_or_explicit_deinit(own pair, is_explicit);
        \\}
    ;
    var sink_drop_bundle = try verifyCleanSast(allocator, 434, sink_partial_and_deinit_src, .{});
    defer sink_drop_bundle.deinit();

    const entry_body = sink_drop_bundle.mir_module.findBodyByName(
        &sink_drop_bundle.interner,
        "entry_sink_partial",
    ).?;
    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &sink_drop_bundle.interner,
        &sink_drop_bundle.pool,
        &sink_drop_bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (sink_drop_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    // `is_explicit == false`; `moved_first` (`1`), `local_buf` (`7`), and unmoved `pair.second` (`2`) each drop once:
    try std.testing.expectEqual(
        @as(i64, 1),
        (try vm.evalBody(entry_body, &[_]RegSlot{.{ .scalar_u64 = 0 }})).slot.scalar_i64,
    );
    try std.testing.expectEqual(@as(usize, 3), vm.asDropTraceSlice().len);

    // `is_explicit == true`; `local_buf.deinit()` clears `_drop_flag` so `local_buf` never double-drops:
    vm.drop_trace.clearRetainingCapacity();
    try std.testing.expectEqual(
        @as(i64, 1),
        (try vm.evalBody(entry_body, &[_]RegSlot{.{ .scalar_u64 = 1 }})).slot.scalar_i64,
    );
    var count_id_seven: usize = 0;
    var count_deinit_marker: usize = 0;
    for (vm.asDropTraceSlice()) |trace_id| {
        if (trace_id == 7) count_id_seven += 1;
        if (trace_id == 107) count_deinit_marker += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), count_deinit_marker);
    try std.testing.expect(count_id_seven <= 1);

    const composite_linear_src =
        \\@linear
        \\pub struct LinearLease {
        \\    pub handle: i32,
        \\}
        \\pub struct LeasePair {
        \\    pub left: LinearLease,
        \\    pub right: LinearLease,
        \\}
        \\pub fn release_lease(lease: own LinearLease) {
        \\    let LinearLease { handle: _ } = lease;
        \\}
        \\pub fn split_and_release_both(pair: own LeasePair) {
        \\    release_lease(own pair.left);
        \\    release_lease(own pair.right);
        \\}
    ;
    var comp_linear_bundle = try verifyCleanSast(allocator, 435, composite_linear_src, .{});
    defer comp_linear_bundle.deinit();

    // [4] `D-04` `Context.scratch[0]` slice passed directly into a callee that rewinds `scratch[0]` emits `E0328`:
    const scratch_arg_conflict_src =
        \\pub struct ScratchArena {
        \\    pub backing: [u8; 8],
        \\}
        \\impl ScratchArena {
        \\    pub fn alloc_slice(&mut self) -> &[u8] {
        \\        return &self.backing;
        \\    }
        \\    pub fn reset(&mut self) {
        \\        self.backing[0] = 0;
        \\    }
        \\}
        \\pub struct Context {
        \\    pub allocator: usize,
        \\    pub scratch: [ScratchArena; 2],
        \\}
        \\pub fn rewind_and_read(ctx: &mut Context, borrowed: &[u8]) -> usize {
        \\    ctx.scratch[0].reset();
        \\    return borrowed.len();
        \\}
        \\pub fn pass_scratch_into_rewinder(ctx: &mut Context) -> usize {
        \\    let scratch_view = ctx.scratch[0].alloc_slice();
        \\    return rewind_and_read(ctx, scratch_view);
        \\}
    ;
    try expectSastDiagnostic(
        allocator,
        436,
        scratch_arg_conflict_src,
        .{},
        .e0328_scratch_arena_ping_pong_conflict,
    );

    // [5] Cross-file `CompilerDb` `@std_cap_boundary` (`env` bit) & `--release` `optimizeMirModule` on SAST error:
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    const std_env_file = FileId.fromInt(437);
    const std_env_src =
        \\extern "C" fn host_getenv_raw() -> i32;
        \\@std_cap_boundary(clears: [ffi, unsafe_op], emits: [env])
        \\pub fn read_env_flag() -> i32 {
        \\    return unsafe { host_getenv_raw() };
        \\}
    ;
    _ = try db.setInput(std_env_file, std_env_src, .high);
    try db.symbol_table.named_module_scopes.put(
        allocator,
        (try db.interner.intern("std_env")).asInt(),
        (try db.resolveSignatures(std_env_file)).module_scope,
    );

    const app_file = FileId.fromInt(438);
    const app_src =
        \\use std_env.read_env_flag;
        \\pub fn app_probe_env() -> i32 {
        \\    return read_env_flag();
        \\}
    ;
    _ = try db.setInput(app_file, app_src, .low);
    const app_def = findDefIdByName((try db.extractItemTree(app_file)).entries, "app_probe_env").?;
    try std.testing.expect((try db.verifySastMir(app_def)).is_verified_sound);
    const app_effects = (try db.getSastSummaryProj(app_def)).inferredEffects();
    try std.testing.expect(app_effects.env);
    try std.testing.expect(!app_effects.ffi);
    try std.testing.expect(!app_effects.unsafe_op);
    _ = try db.optimizeMirModule(app_file, true);

    const invalid_sast_file = FileId.fromInt(439);
    const invalid_sast_src =
        \\pub fn uninit_in_release(cond: bool) -> i64 {
        \\    var slot: i64;
        \\    if cond {
        \\        slot = 10;
        \\    }
        \\    return slot;
        \\}
    ;
    _ = try db.setInput(invalid_sast_file, invalid_sast_src, .low);
    _ = try db.optimizeMirModule(invalid_sast_file, true);
    try std.testing.expect(
        hasDiagnosticCode(
            db.getOptimizedMirDiagnostics(invalid_sast_file, true).?,
            .e0303_uninitialized_memory_read,
        ),
    );
}

test "test_phase75_cond_scope_pre_else_drop_elaboration_and_linear_e0304_se01_se02" {
    const allocator = std.testing.allocator;

    // [1] `SE-01` & `SE-02` Two-checkpoint pre-`else` drop ordering (`B1` & `B2` drop BEFORE `else` runs!):
    const pre_else_drop_src =
        \\pub struct TraceGuard {
        \\    pub tag_id: i64,
        \\}
        \\impl TraceGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag_id);
        \\    }
        \\}
        \\pub fn make_guard(tag_id: i64) -> TraceGuard {
        \\    return TraceGuard { tag_id: tag_id };
        \\}
        \\pub fn maybe_guard(is_present: bool, tag_id: i64) -> TraceGuard? {
        \\    if is_present {
        \\        return .Some(TraceGuard { tag_id: tag_id });
        \\    }
        \\    return .None;
        \\}
        \\pub fn run_cond_drops(is_present: bool, is_passing_guard: bool) -> i64 {
        \\    if maybe_guard(is_present, 10) is .Some(bound_g) and
        \\        (extra_g := make_guard(20)).tag_id > (if is_passing_guard { 0 as i64 } else { 99 as i64 })
        \\    {
        \\        @drop_trace(100);
        \\        return bound_g.tag_id + extra_g.tag_id;
        \\    } else {
        \\        @drop_trace(900);
        \\        return -1;
        \\    }
        \\}
    ;
    var drop_bundle = try verifyCleanSast(allocator, 501, pre_else_drop_src, .{});
    defer drop_bundle.deinit();

    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &drop_bundle.interner,
        &drop_bundle.pool,
        &drop_bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (drop_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }
    const run_body = drop_bundle.mir_module.findBodyByName(&drop_bundle.interner, "run_cond_drops").?;

    // Checkpoint B2 false (`is_present = true`, `is_passing_guard = false`);
    // `extra_g` (`20`) and `bound_g` (`10`) drop in reverse-LIFO order before `else` emits `900`:
    const res_b2_miss = try vm.evalBody(
        run_body,
        &[_]RegSlot{ .{ .scalar_u64 = 1 }, .{ .scalar_u64 = 0 } },
    );
    try std.testing.expectEqual(@as(i64, -1), res_b2_miss.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 20, 10, 900 }, vm.asDropTraceSlice());

    // Checkpoint B1 false (`is_present = false`); `.None` drops no payload before `900`:
    vm.drop_trace.clearRetainingCapacity();
    const res_b1_miss = try vm.evalBody(
        run_body,
        &[_]RegSlot{ .{ .scalar_u64 = 0 }, .{ .scalar_u64 = 1 } },
    );
    try std.testing.expectEqual(@as(i64, -1), res_b1_miss.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{900}, vm.asDropTraceSlice());

    // True branch (`is_present = true`, `is_passing_guard = true`); `then` emits `100`, then `20, 10`:
    vm.drop_trace.clearRetainingCapacity();
    const res_hit = try vm.evalBody(
        run_body,
        &[_]RegSlot{ .{ .scalar_u64 = 1 }, .{ .scalar_u64 = 1 } },
    );
    try std.testing.expectEqual(@as(i64, 30), res_hit.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 100, 20, 10 }, vm.asDropTraceSlice());

    // [2] `SE-01` `@linear` binding inside `ConditionScope` consumed on `then` (B1 miss safe) passes `0` errors:
    const linear_ok_src =
        \\@linear
        \\pub struct LinearToken {
        \\    pub id_num: i64,
        \\}
        \\pub fn release_token(tok_in: own LinearToken) -> i64 {
        \\    let LinearToken { id_num } = tok_in;
        \\    return id_num;
        \\}
        \\pub fn maybe_token(is_ready: bool) -> LinearToken? {
        \\    if is_ready {
        \\        return .Some(LinearToken { id_num: 7 });
        \\    }
        \\    return .None;
        \\}
        \\pub fn consume_if_some(is_ready: bool) -> i64 {
        \\    if maybe_token(is_ready) is .Some(live_tok) {
        \\        return release_token(own live_tok);
        \\    }
        \\    return 0;
        \\}
    ;
    var linear_ok_bundle = try verifyCleanSast(allocator, 502, linear_ok_src, .{});
    defer linear_ok_bundle.deinit();

    // Unconsumed `@linear` binding when trailing guard fails at Checkpoint B2 emits `E0304`:
    const linear_leak_b2_src =
        \\@linear
        \\pub struct LinearToken {
        \\    pub id_num: i64,
        \\}
        \\pub fn release_token(tok_in: own LinearToken) -> i64 {
        \\    let LinearToken { id_num } = tok_in;
        \\    return id_num;
        \\}
        \\pub fn maybe_token(is_ready: bool) -> LinearToken? {
        \\    if is_ready {
        \\        return .Some(LinearToken { id_num: 7 });
        \\    }
        \\    return .None;
        \\}
        \\pub fn leak_on_guard_false(is_ready: bool, is_allowed: bool) -> i64 {
        \\    if maybe_token(is_ready) is .Some(live_tok) and is_allowed {
        \\        return release_token(own live_tok);
        \\    }
        \\    return 0;
        \\}
    ;
    try expectSastDiagnostic(allocator, 503, linear_leak_b2_src, .{}, .e0304_resource_or_memory_leak);
}

test "test_phase75_pentagon_dollar_bce_static_e0307_and_unreachable_e0321_se04_se05" {
    const allocator = std.testing.allocator;

    // [1] `SE-04` & `SE-05` Pentagon `$` backward-offset transfer rule proves `@no_panic` with zero `W0314`:
    const pentagon_dollar_ok_src =
        \\@no_panic
        \\pub fn sum_tail_and_trim(items: &[i64]) -> i64 {
        \\    if items.len() >= 3 {
        \\        let sub_mid: &[i64] = items[1..$ - 1];
        \\        let sub_incl: &[i64] = items[0..=1];
        \\        return items[$ - 1] +% items[$ - 2] +% (sub_mid.len() as i64) +% (sub_incl.len() as i64);
        \\    }
        \\    if 2 + 2 == 5 {
        \\        unreachable;
        \\    }
        \\    return 0;
        \\}
    ;
    var ok_bundle = try verifyCleanSast(allocator, 510, pentagon_dollar_ok_src, .{ .is_sast_strict = true });
    defer ok_bundle.deinit();
    try std.testing.expectEqual(@as(usize, 0), countDiagnosticCode(&ok_bundle.diagnostics, .w0314_unproven_bounds_access));

    // [2] Static `$` underflow (`arr[$ - 4]` on `[i64; 3]`) emits `E0307`:
    const dollar_underflow_src =
        \\pub fn static_dollar_underflow() -> i64 {
        \\    let fixed_arr: [i64; 3] = [10, 20, 30];
        \\    return fixed_arr[$ - 4];
        \\}
    ;
    try expectSastDiagnostic(allocator, 511, dollar_underflow_src, .{}, .e0307_static_buffer_overflow);

    // [3] Static `$` OOB (`arr[$ - 0]` == `arr[len]` on `[i64; 3]`) emits `E0307`:
    const dollar_oob_zero_src =
        \\pub fn static_dollar_zero_oob() -> i64 {
        \\    let fixed_arr: [i64; 3] = [10, 20, 30];
        \\    return fixed_arr[$ - 0];
        \\}
    ;
    try expectSastDiagnostic(allocator, 512, dollar_oob_zero_src, .{}, .e0307_static_buffer_overflow);

    // [4] `comptime` `MirVm` `$` underflow emits `E0307` (`e0307_static_buffer_overflow`):
    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    const ct_dollar_file = FileId.fromInt(513);
    const ct_dollar_src =
        \\pub fn read_from_end(back_off: usize) -> i64 {
        \\    let fixed_arr: [i64; 3] = [10, 20, 30];
        \\    return fixed_arr[$ - back_off];
        \\}
        \\pub const BAD_CT_DOLLAR: i64 = read_from_end(5);
    ;
    _ = try db.setInput(ct_dollar_file, ct_dollar_src, .low);
    const ct_tree = try db.extractItemTree(ct_dollar_file);
    const bad_dollar_def = findDefIdByName(ct_tree.entries, "BAD_CT_DOLLAR").?;
    const ct_art = try db.evalComptimeDef(bad_dollar_def);
    try std.testing.expect(ct_art.has_errors);
    try std.testing.expect(
        hasDiagnosticCode(
            db.getComptimeDiagnostics(bad_dollar_def).?,
            .e0307_static_buffer_overflow,
        ),
    );

    // [5] Reachable `unreachable` inside `@no_panic` emits `E0321`:
    const reachable_unreach_src =
        \\@no_panic
        \\pub fn bad_no_panic_unreach(is_flagged: bool) -> i32 {
        \\    if is_flagged {
        \\        return 1;
        \\    }
        \\    unreachable;
        \\}
    ;
    try expectSastDiagnostic(allocator, 514, reachable_unreach_src, .{}, .e0321_no_panic_contract_violation);
}

test "test_phase75_context_layout_80b_40b_and_with_allocator_escape_e0306_se08" {
    const allocator = std.testing.allocator;

    // [1] `SE-08` & `DR-08` Canonical 10-slot `Context` layout (`80B` on 64-bit, `40B` on `wasm32`, `0..9` ordinals):
    try std.testing.expectEqual(@as(u32, 80), ContextFieldLayout.BYTE_SIZE_64);
    try std.testing.expectEqual(@as(u32, 40), ContextFieldLayout.BYTE_SIZE_32);
    try std.testing.expectEqual(@as(usize, 10), ContextFieldLayout.CANONICAL_FIELDS.len);
    try std.testing.expectEqual(@as(u8, 0), ContextFieldLayout.fromFieldName("allocator").?.slot_ordinal);
    try std.testing.expectEqual(@as(u8, 2), ContextFieldLayout.fromFieldName("rng_seed").?.slot_ordinal);
    try std.testing.expectEqual(@as(u8, 4), ContextFieldLayout.fromFieldName("temp_allocator").?.slot_ordinal);
    try std.testing.expectEqual(@as(u8, 7), ContextFieldLayout.fromFieldName("cancel_token").?.slot_ordinal);
    try std.testing.expectEqual(@as(u8, 8), ContextFieldLayout.fromFieldName("reactor").?.slot_ordinal);
    try std.testing.expectEqual(@as(u8, 9), ContextFieldLayout.fromFieldName("reactor_ctx").?.slot_ordinal);

    // [2] Normal `context.allocator` allocation returned to caller passes (`0` errors),
    // and returning a `Copy` scalar computed inside `with context.allocator = …` passes (`0` errors):
    const ctx_alloc_ok_src =
        \\pub struct OwnedBuffer {
        \\    pub raw_handle: usize,
        \\    pub len: usize,
        \\}
        \\impl OwnedBuffer {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub fn alloc_buffer(size_n: usize) -> OwnedBuffer {
        \\    let active_alloc: Allocator = context.allocator;
        \\    return OwnedBuffer { raw_handle: active_alloc._handle, len: size_n };
        \\}
        \\pub fn caller_owned_ok() -> OwnedBuffer {
        \\    return alloc_buffer(16);
        \\}
        \\pub fn scoped_scalar_ok() -> usize {
        \\    let scratch_alloc = Allocator { _handle: 4096 };
        \\    return with context.allocator = scratch_alloc {
        \\        let temp_buf = alloc_buffer(32);
        \\        temp_buf.len
        \\    };
        \\}
    ;
    var ok_bundle = try verifyCleanSast(allocator, 520, ctx_alloc_ok_src, .{});
    defer ok_bundle.deinit();

    // [3] Escaping a heap carrier from `with context.allocator = …` via `return` emits `E0306`:
    const escape_return_src =
        \\pub struct OwnedBuffer {
        \\    pub raw_handle: usize,
        \\    pub len: usize,
        \\}
        \\impl OwnedBuffer {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub fn alloc_buffer(size_n: usize) -> OwnedBuffer {
        \\    let active_alloc: Allocator = context.allocator;
        \\    return OwnedBuffer { raw_handle: active_alloc._handle, len: size_n };
        \\}
        \\pub fn escape_via_return() -> OwnedBuffer {
        \\    let scratch_alloc = Allocator { _handle: 4096 };
        \\    with context.allocator = scratch_alloc {
        \\        return alloc_buffer(64);
        \\    }
        \\}
    ;
    try expectSastDiagnostic(allocator, 521, escape_return_src, .{}, .e0306_region_escape_violation);

    // [4] Escaping from `with context.temp_allocator = …` into an outer `var` local emits `E0306`:
    const escape_outer_var_src =
        \\pub struct OwnedBuffer {
        \\    pub raw_handle: usize,
        \\    pub len: usize,
        \\}
        \\impl OwnedBuffer {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub fn alloc_temp_buffer(size_n: usize) -> OwnedBuffer {
        \\    let active_temp: Allocator = context.temp_allocator;
        \\    return OwnedBuffer { raw_handle: active_temp._handle, len: size_n };
        \\}
        \\pub fn escape_via_outer_var() -> usize {
        \\    var outer_buf = alloc_temp_buffer(8);
        \\    let local_temp = Allocator { _handle: 8192 };
        \\    with context.temp_allocator = local_temp {
        \\        outer_buf = alloc_temp_buffer(16);
        \\    }
        \\    return outer_buf.len;
        \\}
    ;
    try expectSastDiagnostic(allocator, 522, escape_outer_var_src, .{}, .e0306_region_escape_violation);

    // [5] Growing/mutating an outer heap container via `inout` inside `with context.allocator = …` emits `E0306`:
    const escape_inout_grow_src =
        \\pub struct OwnedBuffer {
        \\    pub raw_handle: usize,
        \\    pub len: usize,
        \\}
        \\impl OwnedBuffer {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub fn alloc_buffer(size_n: usize) -> OwnedBuffer {
        \\    let active_alloc: Allocator = context.allocator;
        \\    return OwnedBuffer { raw_handle: active_alloc._handle, len: size_n };
        \\}
        \\pub fn grow_buffer(buf_ref: &mut OwnedBuffer, extra_n: usize) {
        \\    let active_alloc: Allocator = context.allocator;
        \\    buf_ref.raw_handle = active_alloc._handle;
        \\    buf_ref.len = buf_ref.len + extra_n;
        \\}
        \\pub fn escape_via_inout_mutation() -> usize {
        \\    var outer_buf = alloc_buffer(4);
        \\    let local_alloc = Allocator { _handle: 16384 };
        \\    with context.allocator = local_alloc {
        \\        grow_buffer(&mut outer_buf, 12);
        \\    }
        \\    return outer_buf.len;
        \\}
    ;
    try expectSastDiagnostic(allocator, 523, escape_inout_grow_src, .{}, .e0306_region_escape_violation);
}

test "test_regression_linear_complement_scalar_and_multi_autodrop_discharge" {
    const allocator = std.testing.allocator;

    // [1] `Outcome` with 1 uncovered `AutoDrop` variant (`Msg`) + 1 `Copy` scalar (`Code(usize)`);
    // taking `.Code(0xDEADBEEF)` must not downcast/drop `Msg`:
    const outcome_src =
        \\@linear
        \\pub struct LinearToken {
        \\    pub id_num: i64,
        \\}
        \\pub struct DropGuard {
        \\    pub tag: i64,
        \\}
        \\impl DropGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub enum Outcome {
        \\    Ok(LinearToken),
        \\    Msg(DropGuard),
        \\    Code(usize),
        \\}
        \\pub fn consume_token(tok_in: own LinearToken) -> i64 {
        \\    let LinearToken { id_num } = tok_in;
        \\    return id_num;
        \\}
        \\pub fn handle_outcome(mode: i64) -> i64 {
        \\    let out_val: Outcome = if mode == 0 {
        \\        .Ok(LinearToken { id_num: 10 })
        \\    } else if mode == 1 {
        \\        .Msg(DropGuard { tag: 77 })
        \\    } else {
        \\        .Code(0xDEADBEEF)
        \\    };
        \\    if out_val is .Ok(live_tok) {
        \\        return consume_token(own live_tok);
        \\    }
        \\    return 99;
        \\}
    ;

    var out_bundle = try verifyCleanSast(allocator, 530, outcome_src, .{});
    defer out_bundle.deinit();
    const out_body = out_bundle.mir_module.findBodyByName(&out_bundle.interner, "handle_outcome").?;

    var out_rodata = RodataPool.init(allocator);
    defer out_rodata.deinit();
    var out_vm = try MirVm.init(
        allocator,
        &out_bundle.interner,
        &out_bundle.pool,
        &out_bundle.sym_table,
        &out_rodata,
        null,
        null,
        .{},
    );
    defer out_vm.deinit();
    for (out_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try out_vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    // `.Code(0xDEADBEEF)` (`mode == 2`); zero bogus `DropGuard.drop` invocations:
    const code_res = try out_vm.evalBody(out_body, &[_]RegSlot{.{ .scalar_i64 = 2 }});
    try std.testing.expectEqual(@as(i64, 99), code_res.slot.scalar_i64);
    try std.testing.expectEqual(@as(usize, 0), out_vm.asDropTraceSlice().len);

    // `.Msg(DropGuard { tag: 77 })` (`mode == 1`); drops `77` cleanly:
    out_vm.drop_trace.clearRetainingCapacity();
    const msg_res = try out_vm.evalBody(out_body, &[_]RegSlot{.{ .scalar_i64 = 1 }});
    try std.testing.expectEqual(@as(i64, 99), msg_res.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{77}, out_vm.asDropTraceSlice());

    // [2] `OpenRes` with multiple uncovered `AutoDrop` variants (`IoErr`, `PathErr`, `PairErr`):
    const open_res_src =
        \\@linear
        \\pub struct LinearToken {
        \\    pub id_num: i64,
        \\}
        \\pub struct DropGuard {
        \\    pub tag: i64,
        \\}
        \\impl DropGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub enum OpenRes {
        \\    Ok(LinearToken),
        \\    IoErr(DropGuard),
        \\    PathErr(DropGuard),
        \\    PairErr(DropGuard, DropGuard),
        \\}
        \\pub fn consume_token(tok_in: own LinearToken) -> i64 {
        \\    let LinearToken { id_num } = tok_in;
        \\    return id_num;
        \\}
        \\pub fn handle_open(mode: i64) -> i64 {
        \\    let res_val: OpenRes = if mode == 0 {
        \\        .Ok(LinearToken { id_num: 5 })
        \\    } else if mode == 1 {
        \\        .IoErr(DropGuard { tag: 11 })
        \\    } else if mode == 2 {
        \\        .PathErr(DropGuard { tag: 22 })
        \\    } else {
        \\        .PairErr(DropGuard { tag: 31 }, DropGuard { tag: 32 })
        \\    };
        \\    if res_val is .Ok(live_tok) {
        \\        return consume_token(own live_tok);
        \\    }
        \\    return -1;
        \\}
    ;

    var open_bundle = try verifyCleanSast(allocator, 531, open_res_src, .{});
    defer open_bundle.deinit();
    const open_body = open_bundle.mir_module.findBodyByName(&open_bundle.interner, "handle_open").?;

    var open_rodata = RodataPool.init(allocator);
    defer open_rodata.deinit();
    var open_vm = try MirVm.init(
        allocator,
        &open_bundle.interner,
        &open_bundle.pool,
        &open_bundle.sym_table,
        &open_rodata,
        null,
        null,
        .{},
    );
    defer open_vm.deinit();
    for (open_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try open_vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    _ = try open_vm.evalBody(open_body, &[_]RegSlot{.{ .scalar_i64 = 1 }});
    try std.testing.expectEqualSlices(i64, &[_]i64{11}, open_vm.asDropTraceSlice());

    open_vm.drop_trace.clearRetainingCapacity();
    _ = try open_vm.evalBody(open_body, &[_]RegSlot{.{ .scalar_i64 = 2 }});
    try std.testing.expectEqualSlices(i64, &[_]i64{22}, open_vm.asDropTraceSlice());

    open_vm.drop_trace.clearRetainingCapacity();
    _ = try open_vm.evalBody(open_body, &[_]RegSlot{.{ .scalar_i64 = 3 }});
    try std.testing.expectEqualSlices(i64, &[_]i64{ 32, 31 }, open_vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), open_vm.countUnfreedHeapAllocations());
}

test "test_regression_partial_enum_variant_move_wildcard_autodrop" {
    const allocator = std.testing.allocator;

    const partial_variant_src =
        \\pub struct DropGuard {
        \\    pub tag: i64,
        \\}
        \\impl DropGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub enum GuardPair {
        \\    Both(DropGuard, DropGuard),
        \\    Empty,
        \\}
        \\pub fn run_partial_move_wildcard() -> i64 {
        \\    let pair_val: GuardPair = .Both(DropGuard { tag: 10 }, DropGuard { tag: 20 });
        \\    if pair_val is .Both(first_guard, _) {
        \\        @drop_trace(100);
        \\        return first_guard.tag;
        \\    }
        \\    return 0;
        \\}
        \\pub fn run_pure_ref_wildcard() -> i64 {
        \\    let pair_val: GuardPair = .Both(DropGuard { tag: 40 }, DropGuard { tag: 50 });
        \\    if pair_val is .Both(&first_ref, _) {
        \\        @drop_trace(200);
        \\        return first_ref.tag;
        \\    }
        \\    return 0;
        \\}
    ;

    var bundle = try verifyCleanSast(allocator, 532, partial_variant_src, .{});
    defer bundle.deinit();
    const move_body = bundle.mir_module.findBodyByName(&bundle.interner, "run_partial_move_wildcard").?;
    const ref_body = bundle.mir_module.findBodyByName(&bundle.interner, "run_pure_ref_wildcard").?;

    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &bundle.interner,
        &bundle.pool,
        &bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    // By-value `first_guard` + `_`; both `20` (`_`) and `10` (`first_guard`) drop in LIFO order with zero leaks:
    const move_res = try vm.evalBody(move_body, &.{});
    try std.testing.expectEqual(@as(i64, 10), move_res.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 100, 20, 10 }, vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());

    // Pure `ref` borrow `ref first_ref` + `_`; parent `pair_val` remains whole and drops `[50, 40]` once:
    vm.drop_trace.clearRetainingCapacity();
    const ref_res = try vm.evalBody(ref_body, &.{});
    try std.testing.expectEqual(@as(i64, 40), ref_res.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 200, 50, 40 }, vm.asDropTraceSlice());
    try std.testing.expectEqual(@as(u32, 0), vm.countUnfreedHeapAllocations());
}

test "test_regression_context_handle_escape_e0306_and_allocator_slot_isolation" {
    const allocator = std.testing.allocator;

    // [1] Escaping `context.logger` from `with context.logger = &local_log` emits `E0306`:
    const logger_escape_src =
        \\pub struct LocalLog {
        \\    pub level: u32,
        \\}
        \\impl LocalLog {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn escape_logger() -> Logger {
        \\    let local_log = LocalLog { level: 1 };
        \\    with context.logger = &local_log {
        \\        return context.logger;
        \\    }
        \\}
    ;
    try expectSastDiagnostic(allocator, 533, logger_escape_src, .{}, .e0306_region_escape_violation);

    // [2] Escaping `context.diagnostics` from `with context.diagnostics = &mut local_diag` emits `E0306`:
    const diag_escape_src =
        \\pub struct LocalDiag {
        \\    pub count: u32,
        \\}
        \\impl LocalDiag {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn escape_diagnostics() -> DiagSink {
        \\    var local_diag = LocalDiag { count: 0 };
        \\    with context.diagnostics = &mut local_diag {
        \\        return context.diagnostics;
        \\    }
        \\}
    ;
    try expectSastDiagnostic(allocator, 534, diag_escape_src, .{}, .e0306_region_escape_violation);

    // [3] Escaping `context.cancel_token` from `with context.cancel_token = &local_tok` emits `E0306`:
    const cancel_escape_src =
        \\pub struct LocalCancel {
        \\    pub is_cancelled: bool,
        \\}
        \\impl LocalCancel {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn escape_cancel_token() -> CancelToken {
        \\    let local_tok = LocalCancel { is_cancelled: false };
        \\    with context.cancel_token = &local_tok {
        \\        return context.cancel_token;
        \\    }
        \\}
    ;
    try expectSastDiagnostic(allocator, 535, cancel_escape_src, .{}, .e0306_region_escape_violation);

    // [4] Escaping a `.raw_ptr_ty` (`*mut u8`) carrier allocated inside `with context.allocator = …` emits `E0306`:
    const raw_ptr_escape_src =
        \\pub struct Arena {
        \\    pub cap: usize,
        \\}
        \\pub fn alloc_raw_bytes() -> *mut u8 {
        \\    let active_alloc = context.allocator;
        \\    return unsafe { active_alloc._handle as *mut u8 };
        \\}
        \\pub fn escape_raw_ptr() -> *mut u8 {
        \\    var local_arena = Arena { cap: 64 };
        \\    with context.allocator = &mut local_arena {
        \\        return alloc_raw_bytes();
        \\    }
        \\}
    ;
    try expectSastDiagnostic(allocator, 540, raw_ptr_escape_src, .{}, .e0306_region_escape_violation);

    // [5] Allocating from `context.allocator` (`slot 0`) inside `with context.temp_allocator = …` (`slot 4`)
    // does not conflate slot depths (`0` SAST errors):
    const non_conflated_src =
        \\pub struct OwnedBuffer {
        \\    pub raw_handle: usize,
        \\    pub len: usize,
        \\}
        \\impl OwnedBuffer {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub fn alloc_primary(size_n: usize) -> OwnedBuffer {
        \\    let primary_alloc: Allocator = context.allocator;
        \\    return OwnedBuffer { raw_handle: primary_alloc._handle, len: size_n };
        \\}
        \\pub fn alloc_temp(size_n: usize) -> OwnedBuffer {
        \\    let temp_alloc: Allocator = context.temp_allocator;
        \\    return OwnedBuffer { raw_handle: temp_alloc._handle, len: size_n };
        \\}
        \\pub fn outer_primary_inside_inner_temp_ok() -> OwnedBuffer {
        \\    let inner_temp = Allocator { _handle: 8192 };
        \\    with context.temp_allocator = inner_temp {
        \\        let scratch_only = alloc_temp(16);
        \\        let _ = scratch_only.len;
        \\        return alloc_primary(64);
        \\    }
        \\}
    ;
    var isolated_ok_bundle = try verifyCleanSast(allocator, 536, non_conflated_src, .{});
    defer isolated_ok_bundle.deinit();

    // [6] Escaping a generic `Holder[Logger]` carrier from `with context.logger = &local_log` emits `E0306`:
    const generic_holder_escape_src =
        \\pub struct Holder[T] {
        \\    pub inner: T,
        \\}
        \\pub struct LocalLog {
        \\    pub level: u32,
        \\}
        \\impl LocalLog {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn capture_logger_holder() -> Holder[Logger] {
        \\    return Holder { inner: context.logger };
        \\}
        \\pub fn escape_generic_logger_holder() -> Holder[Logger] {
        \\    let local_log = LocalLog { level: 1 };
        \\    with context.logger = &local_log {
        \\        return capture_logger_holder();
        \\    }
        \\}
    ;
    var gen_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(541),
        generic_holder_escape_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer gen_bundle.deinit();
    try std.testing.expectEqual(@as(usize, 1), gen_bundle.diagnostics.diagnostics.items.len);
    try std.testing.expect(hasDiagnosticCode(&gen_bundle.diagnostics, .e0306_region_escape_violation));

    // [7] Escaping an `enum` variant carrying `Logger` from `with context.logger = &local_log` emits `E0306`:
    const enum_carrier_escape_src =
        \\pub enum MaybeLogger {
        \\    Active(Logger),
        \\    Inactive,
        \\}
        \\pub struct LocalLog {
        \\    pub level: u32,
        \\}
        \\impl LocalLog {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn capture_enum_logger() -> MaybeLogger {
        \\    return .Active(context.logger);
        \\}
        \\pub fn escape_enum_logger() -> MaybeLogger {
        \\    let local_log = LocalLog { level: 2 };
        \\    with context.logger = &local_log {
        \\        return capture_enum_logger();
        \\    }
        \\}
    ;
    var enum_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(542),
        enum_carrier_escape_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer enum_bundle.deinit();
    try std.testing.expectEqual(@as(usize, 1), enum_bundle.diagnostics.diagnostics.items.len);
    try std.testing.expect(hasDiagnosticCode(&enum_bundle.diagnostics, .e0306_region_escape_violation));

    // [8] Escaping a pointer to `Logger` (`*Logger`) from `with context.logger = &local_log` emits `E0306`:
    const ptr_logger_escape_src =
        \\pub struct LocalLog {
        \\    pub level: u32,
        \\}
        \\impl LocalLog {
        \\    pub fn as_handle(&self) -> usize = 0;
        \\}
        \\pub fn capture_logger_ptr() -> *Logger {
        \\    let active_log = context.logger;
        \\    return unsafe { active_log._handle as *Logger };
        \\}
        \\pub fn escape_logger_ptr() -> *Logger {
        \\    let local_log = LocalLog { level: 3 };
        \\    with context.logger = &local_log {
        \\        return capture_logger_ptr();
        \\    }
        \\}
    ;
    var ptr_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(543),
        ptr_logger_escape_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer ptr_bundle.deinit();
    try std.testing.expectEqual(@as(usize, 1), ptr_bundle.diagnostics.diagnostics.items.len);
    try std.testing.expect(hasDiagnosticCode(&ptr_bundle.diagnostics, .e0306_region_escape_violation));
}

test "test_regression_dollar_shared_read_and_autoderef_mut_slice" {
    const allocator = std.testing.allocator;

    const dollar_borrow_src =
        \\pub struct ArrHolder {
        \\    pub arr: [i64; 4],
        \\}
        \\pub struct ViewMut {
        \\    pub buf: &mut [i32],
        \\}
        \\pub fn read_dollar_while_shared_borrowed() -> i64 {
        \\    var holder = ArrHolder { arr: [10, 20, 30, 40] };
        \\    let shared_ref = &holder;
        \\    let last_elem = holder.arr[$ - 1];
        \\    return shared_ref.arr[0] + last_elem;
        \\}
        \\pub fn write_dollar_through_view_mut() -> i64 {
        \\    var backing: [i32; 3] = [1, 2, 3];
        \\    let view = ViewMut { buf: &mut backing };
        \\    view.buf[$ - 1] = 9;
        \\    return backing[2] as i64;
        \\}
    ;

    var bundle = try verifyCleanSast(allocator, 537, dollar_borrow_src, .{});
    defer bundle.deinit();
    const read_body = bundle.mir_module.findBodyByName(&bundle.interner, "read_dollar_while_shared_borrowed").?;
    const write_body = bundle.mir_module.findBodyByName(&bundle.interner, "write_dollar_through_view_mut").?;

    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &bundle.interner,
        &bundle.pool,
        &bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    const read_res = try vm.evalBody(read_body, &.{});
    try std.testing.expectEqual(@as(i64, 50), read_res.slot.scalar_i64);
    const write_res = try vm.evalBody(write_body, &.{});
    try std.testing.expectEqual(@as(i64, 9), write_res.slot.scalar_i64);
}

test "test_regression_hir_if_condition_autodrop_scope_and_inclusive_slice_e0307" {
    const allocator = std.testing.allocator;

    // [1] `hir_if` (`is not` / boolean call) drops condition `AutoDrop` temporaries before `else`:
    const cond_temp_src =
        \\pub struct DropGuard {
        \\    pub tag: i64,
        \\}
        \\impl DropGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub fn make_opt_guard(is_some: bool, tag: i64) -> DropGuard? {
        \\    if is_some {
        \\        return .Some(DropGuard { tag: tag });
        \\    }
        \\    return .None;
        \\}
        \\pub fn run_if_cond_scope(is_inverted: bool) -> i64 {
        \\    if is_inverted {
        \\        if not (make_opt_guard(true, 5) is not .None) {
        \\            @drop_trace(10);
        \\            return 1;
        \\        } else {
        \\            @drop_trace(20);
        \\            return 2;
        \\        }
        \\    }
        \\    if make_opt_guard(true, 5) is not .None {
        \\        @drop_trace(10);
        \\        return 1;
        \\    } else {
        \\        @drop_trace(20);
        \\        return 2;
        \\    }
        \\}
    ;

    var cond_bundle = try verifyCleanSast(allocator, 538, cond_temp_src, .{});
    defer cond_bundle.deinit();
    const cond_body = cond_bundle.mir_module.findBodyByName(&cond_bundle.interner, "run_if_cond_scope").?;

    var rodata = RodataPool.init(allocator);
    defer rodata.deinit();
    var vm = try MirVm.init(
        allocator,
        &cond_bundle.interner,
        &cond_bundle.pool,
        &cond_bundle.sym_table,
        &rodata,
        null,
        null,
        .{},
    );
    defer vm.deinit();
    for (cond_bundle.mir_module.bodies.items) |*body_ptr| {
        _ = try vm.registerBody(body_ptr, body_ptr.symbol_index);
    }

    // `else` branch (`is_inverted = true`); live `.Some(DropGuard(5))` drops before `else` body emits `20`:
    const else_res = try vm.evalBody(cond_body, &[_]RegSlot{.{ .scalar_u64 = 1 }});
    try std.testing.expectEqual(@as(i64, 2), else_res.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 5, 20 }, vm.asDropTraceSlice());

    // `then` branch (`is_inverted = false`); `then` body emits `10`, then condition guard `5` drops at scope exit:
    vm.drop_trace.clearRetainingCapacity();
    const then_res = try vm.evalBody(cond_body, &[_]RegSlot{.{ .scalar_u64 = 0 }});
    try std.testing.expectEqual(@as(i64, 1), then_res.slot.scalar_i64);
    try std.testing.expectEqualSlices(i64, &[_]i64{ 10, 5 }, vm.asDropTraceSlice());

    // [2] `items[0..=usize.MAX]` (`18446744073709551615`) emits `E0307` directly (not `E0502`):
    const incl_max_src =
        \\pub fn bad_inclusive_usize_max(items: &[i32]) -> &[i32] {
        \\    return items[0..=18446744073709551615];
        \\}
    ;
    var incl_bundle = try corex.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(539),
        incl_max_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer incl_bundle.deinit();
    try std.testing.expect(hasDiagnosticCode(&incl_bundle.diagnostics, .e0307_static_buffer_overflow));
    try std.testing.expectEqual(
        @as(usize, 0),
        countDiagnosticCode(&incl_bundle.diagnostics, .e0502_integer_constant_overflow),
    );
}

test "test_regression_const_initializer_cond_if_is_match_sast_gate_f" {
    const allocator = std.testing.allocator;

    // [1] Top-level `const` initializers with `HirCondClauseKind.is_match` (`if … is …` & `while … is …`)
    // synchronize `extra_data` (`2` payload words) cleanly in Gate F SAST (`0` diagnostics):
    const clean_const_cond_src =
        \\pub const COND_IF_CONST: i64 = {
        \\    let maybe_seed: i64? = .Some(6);
        \\    let bonus_table: [i64; 3] = [10, 20, 30];
        \\    if maybe_seed is .Some(seed_val) and (doubled_val := seed_val * 2) > 8 {
        \\        doubled_val + bonus_table[1]
        \\    } else {
        \\        bonus_table[0]
        \\    }
        \\};
        \\
        \\pub const COND_WHILE_CONST: i64 = {
        \\    var step_opt: i64? = .Some(3);
        \\    var total_acc: i64 = 0;
        \\    while step_opt is .Some(cur_step) and cur_step > 0 {
        \\        total_acc = total_acc + cur_step;
        \\        step_opt = if cur_step > 1 { .Some(cur_step - 1) } else { .None };
        \\    }
        \\    total_acc
        \\};
        \\
        \\pub fn read_const_pair() -> i64 {
        \\    return COND_IF_CONST + COND_WHILE_CONST;
        \\}
    ;
    var clean_bundle = try verifyCleanSast(allocator, 544, clean_const_cond_src, .{});
    defer clean_bundle.deinit();

    // [2] Static OOB inside trailing clause or `else_tail` after `is_match` in a `const` initializer emits `E0307`:
    const bad_const_else_oob_src =
        \\pub const BAD_ELSE_CONST: i64 = {
        \\    let maybe_val: i64? = .None;
        \\    let fixed_arr: [i64; 3] = [10, 20, 30];
        \\    if maybe_val is .Some(hit_val) {
        \\        hit_val
        \\    } else {
        \\        fixed_arr[7]
        \\    }
        \\};
        \\pub fn use_bad_else() -> i64 {
        \\    return BAD_ELSE_CONST;
        \\}
    ;
    try expectSastDiagnostic(allocator, 545, bad_const_else_oob_src, .{}, .e0307_static_buffer_overflow);

    const bad_const_guard_oob_src =
        \\pub const BAD_GUARD_CONST: i64 = {
        \\    let maybe_val: i64? = .Some(4);
        \\    let fixed_arr: [i64; 2] = [10, 20];
        \\    if maybe_val is .Some(hit_val) and fixed_arr[5] > 0 {
        \\        hit_val
        \\    } else {
        \\        0
        \\    }
        \\};
        \\pub fn use_bad_guard() -> i64 {
        \\    return BAD_GUARD_CONST;
        \\}
    ;
    try expectSastDiagnostic(allocator, 546, bad_const_guard_oob_src, .{}, .e0307_static_buffer_overflow);
}

test "test_phase76_dr22_sast_raw_uninit_out_leak_e0422_struct_move_and_parallel_swap" {
    const allocator = std.testing.allocator;

    // [1] `&raw mut uninit_buf` is safe (`0` SAST errors) while `..own base` moves `AutoDrop` fields cleanly:
    const dr22_clean_src =
        \\pub struct Vec[T] {
        \\    pub len: usize,
        \\}
        \\pub struct PacketOwned {
        \\    pub tag: u32,
        \\    pub payload: Vec[u8],
        \\}
        \\pub fn raw_and_struct_move(left: &mut u32, right: &mut u32) -> u32 {
        \\    var uninit_buf: [u8; 8];
        \\    let raw_mut_ptr = &raw mut uninit_buf;
        \\    unsafe {
        \\        raw_mut_ptr.*[0] = 7;
        \\    }
        \\    (left.*, right.*) = (right.*, left.*);
        \\    let pkt_a = PacketOwned { tag: 1, payload: Vec { len: 4 } };
        \\    let pkt_b = PacketOwned { tag: 2, ..own pkt_a };
        \\    return pkt_b.tag + left.*;
        \\}
    ;
    var clean_bundle = try verifyCleanSast(allocator, 550, dr22_clean_src, .{});
    defer clean_bundle.deinit();

    // [2] Passing a live `AutoDrop` variable to `&out` emits `E0422`:
    const out_overwrite_src =
        \\pub struct OwnedBuf {
        \\    pub len: usize,
        \\}
        \\impl OwnedBuf {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub fn init_buf(dst: &out OwnedBuf) {
        \\    dst.* = OwnedBuf { len: 1 };
        \\}
        \\pub fn bad_live_out() {
        \\    var live_v = OwnedBuf { len: 5 };
        \\    init_buf(&out live_v);
        \\}
    ;
    try expectSastDiagnostic(allocator, 551, out_overwrite_src, .{}, .e0422_out_param_contract_violation);

    // [3] Overlapping LHS places in parallel destructuring assignment `(val, val) = (1, 2)` emit `E0305`:
    const overlap_swap_src =
        \\pub fn bad_overlap_assign() -> i64 {
        \\    var val: i64 = 0;
        \\    (val, val) = (1, 2);
        \\    return val;
        \\}
    ;
    try expectSastDiagnostic(allocator, 552, overlap_swap_src, .{}, .e0305_exclusivity_violation);

    // [4] `@no_alloc` formatted `@panic("…{x=}…")` + partial-move non-`own` `..base` spread pass SAST cleanly:
    const no_alloc_panic_and_partial_spread_src =
        \\pub struct DropHandle {
        \\    pub id: u32,
        \\}
        \\impl DropHandle {
        \\    pub fn drop(&mut self) {}
        \\}
        \\pub struct PacketMixed {
        \\    pub code: u32,
        \\    pub guard_keep: DropHandle,
        \\}
        \\@no_alloc
        \\pub fn check_code_no_alloc(code: u32, label: str) -> u32 {
        \\    if code == 0 {
        \\        @panic("invalid {code=:#06x} in {label}");
        \\    }
        \\    if code == 999 {
        \\        @panic(label);
        \\    }
        \\    return code;
        \\}
        \\pub fn move_field_with_copy_spread() -> u32 {
        \\    let pkt_1 = PacketMixed { code: 42, guard_keep: DropHandle { id: 9 } };
        \\    let pkt_2 = PacketMixed { guard_keep: own pkt_1.guard_keep, ..pkt_1 };
        \\    return pkt_2.code + pkt_2.guard_keep.id;
        \\}
    ;
    var spread_bundle = try verifyCleanSast(allocator, 553, no_alloc_panic_and_partial_spread_src, .{});
    defer spread_bundle.deinit();
}

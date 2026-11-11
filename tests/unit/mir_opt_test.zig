//! Unit Tests for Dual-Mode `MIR` Optimizer, Monomorphizer & `ICF` (`tests/unit/mir_opt_test.zig`)
//!
//! Exercises the Phase 5 `DR-13` Deliverables 5–6 dual-mode optimization pipeline (`stage0/src/mir_opt.zig`)
//! across `TargetLayout.NATIVE_64` and `TargetLayout.WASM32`:
//!
//! - Exact 16-byte `LayoutShapeKey` layout (`_pad: u32 = 0`), `AbiPassClass`, `NicheKind`, and `ptr_mask_64`.
//! - `--dev` 5-pass pipeline (`D1`–`D5`): `subscript` / `@inline(always)` splicing, `D2` reachable-only
//!   constant folding (`if false { 1 / 0 }` dead-branch trap safety vs reachable `E0502`/`E0507`), `D3`
//!   Ghost instruction stripping (`is_ghost_stripped == true`) plus `is_preserving_pre_strip_mir = true`
//!   snapshot retention for Phase 6 SAST, `D4` constant branch folding & unreachable block pruning, and
//!   `D5` FIFO generic + Constrained Type Group (`Number`, `any Signed`, `[T; N]`) monomorphization with
//!   Tarjan SCC `is_contextless` promotion.
//! - `LayoutShapeKey` pointer-shape deduplication (`D5`): positive `&u32` vs `&i32` pass-through merging
//!   (`dedup_merged_count > 0`) and negative soundness guards (`@type_name[T]()`, signed vs unsigned
//!   division/comparison `i32` vs `u32`, and distinct field-offset structs NEVER merging).
//! - `--release` 6-pass pipeline (`R1`–`R6`): `R1` bounded cost-model inliner + `W0501` warning on budget
//!   overflow/recursion, `R2` SROA composite promotion (including loop-carried struct accumulator `sum == 45`),
//!   `R3` dominator-scoped VRP redundant check folding + `u128` high-bit soundness, `R4` SCCP + `switch_int`
//!   fusion + commutative `GVN`, `R5` global `DCE` + jump-threading + block merging, and `R6` `Wyhash(0)`
//!   structural Identical Code Folding (`ICF`).
//! - `MirVerifier` (`V1`–`V6`) gate enforcement and differential `--dev` vs `--release` `MirVm` equivalence.

const std = @import("std");
const corex = @import("corex");

const mir = corex.mir;
const mir_vm = corex.mir_vm;
const mir_opt = corex.mir_opt;
const FileId = corex.FileId;
const TypeId = corex.TypeId;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const StringInterner = corex.StringInterner;
const SymbolTable = corex.SymbolTable;
const InternPool = corex.InternPool;
const TargetLayout = corex.TargetLayout;
const MirBody = mir.MirBody;
const MirSourceBundle = mir.MirSourceBundle;
const RegSlot = mir_vm.RegSlot;
const RodataPool = mir_vm.RodataPool;
const MirVm = mir_vm.MirVm;
const AbiPassClass = mir_opt.AbiPassClass;
const NicheKind = mir_opt.NicheKind;
const LayoutShapeKey = mir_opt.LayoutShapeKey;
const MirOptConfig = mir_opt.MirOptConfig;
const MirOptModuleResult = mir_opt.MirOptModuleResult;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic matching `expected_code`.
fn hasDiagnosticCode(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Counts total instructions matching `target_op` inside `body`.
fn countBodyOp(body: *const MirBody, target_op: mir.MirOp) usize {
    var match_count: usize = 0;
    for (body.blocks.items, 0..) |_, block_i| {
        const block_id = corex.MirBlockId.fromInt(@intCast(block_i));
        for (body.getBlockInsts(block_id)) |inst_val| {
            if (body.getInst(inst_val).op == target_op) {
                match_count += 1;
            }
        }
    }
    return match_count;
}

/// Counts total basic blocks in `body` whose terminator matches `target_kind`.
fn countBodyTerminator(body: *const MirBody, target_kind: mir.TerminatorKind) usize {
    var match_count: usize = 0;
    for (body.blocks.items) |basic_block| {
        if (basic_block.terminator.kind == target_kind) {
            match_count += 1;
        }
    }
    return match_count;
}

/// Runs `optimizeMirModule` on `bundle` with full `syntax_view` wired from `source`.
fn runOptimizeOnBundle(
    allocator: std.mem.Allocator,
    bundle: *MirSourceBundle,
    source: []const u8,
    is_release_mode: bool,
    is_preserving_pre_strip: bool,
    target_layout: TargetLayout,
    opt_sink: *DiagnosticSink,
) !MirOptModuleResult {
    const config = MirOptConfig{
        .is_release_mode = is_release_mode,
        .is_preserving_pre_strip_mir = is_preserving_pre_strip,
        .target_layout = target_layout,
        .syntax_view = .{
            .source = source,
            .tokens = &bundle.hir_bundle.tokens,
            .cst_arena = &bundle.hir_bundle.cst_arena,
        },
    };
    return mir_opt.optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        config,
        opt_sink,
    );
}

/// Evaluates `fn_name` inside `opt_res` using a fresh `MirVm` under `target_layout` and returns `RegSlot`.
fn evalOptimizedFnSlot(
    allocator: std.mem.Allocator,
    bundle: *MirSourceBundle,
    opt_res: *const MirOptModuleResult,
    fn_name: []const u8,
    args: []const RegSlot,
    target_layout: TargetLayout,
) !RegSlot {
    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{ .target_layout = target_layout },
    );
    defer vm.deinit();

    for (opt_res.bodies.items) |*body_item| {
        _ = try vm.registerBody(body_item, .none);
    }

    const entry_body = opt_res.findBodyByName(&bundle.hir_bundle.interner, fn_name) orelse
        return error.MissingEntryBody;
    const eval_res = try vm.evalBody(entry_body, args);
    return eval_res.slot;
}

/// Evaluates a `str`-returning function `fn_name` inside `opt_res` and returns its UTF-8 text.
fn evalOptimizedFnStr(
    allocator: std.mem.Allocator,
    bundle: *MirSourceBundle,
    opt_res: *const MirOptModuleResult,
    fn_name: []const u8,
    target_layout: TargetLayout,
) ![]const u8 {
    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{ .target_layout = target_layout },
    );
    defer vm.deinit();

    for (opt_res.bodies.items) |*body_item| {
        _ = try vm.registerBody(body_item, .none);
    }

    const entry_body = opt_res.findBodyByName(&bundle.hir_bundle.interner, fn_name) orelse
        return error.MissingEntryBody;
    const eval_res = try vm.evalBody(entry_body, &.{});
    const ct_val = try vm.resultToComptimeValue(eval_res, null);
    return bundle.hir_bundle.interner.get(ct_val.str_val);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_mir_opt_layout_shape_key_16_byte_invariant_and_target_layout_classification" {
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(AbiPassClass));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(NicheKind));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(LayoutShapeKey));
    try std.testing.expectEqual(@as(usize, 12), @offsetOf(LayoutShapeKey, "_pad"));

    const default_key = LayoutShapeKey{
        .size_bytes = 8,
        .align_log2 = 3,
        .abi_class = .integer_reg,
        .is_trivial_copy = 1,
        .niche_kind = .non_null_ptr,
        .ptr_mask_64 = 1,
    };
    try std.testing.expectEqual(@as(u32, 0), default_key._pad);

    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var sym_table = try SymbolTable.init(allocator, &interner);
    defer sym_table.deinit();
    var pool = try InternPool.init(allocator);
    defer pool.deinit();

    const ref_u32 = try pool.internRef(.u32_ty, false);
    const ref_i32 = try pool.internRef(.i32_ty, false);
    const slice_u8 = try pool.internSlice(.u8_ty, false);

    // `NATIVE_64`: `&u32` and `&i32` share identical 8-byte `non_null_ptr` shape (`ptr_mask_64 == 0x1`):
    const nat_ref_u32 = mir_opt.computeLayoutShapeKey(&pool, &sym_table, ref_u32, TargetLayout.NATIVE_64);
    const nat_ref_i32 = mir_opt.computeLayoutShapeKey(&pool, &sym_table, ref_i32, TargetLayout.NATIVE_64);
    try std.testing.expect(nat_ref_u32.isEqual(nat_ref_i32));
    try std.testing.expectEqual(@as(u32, 8), nat_ref_u32.size_bytes);
    try std.testing.expectEqual(@as(u8, 3), nat_ref_u32.align_log2);
    try std.testing.expectEqual(AbiPassClass.integer_reg, nat_ref_u32.abi_class);
    try std.testing.expectEqual(NicheKind.non_null_ptr, nat_ref_u32.niche_kind);
    try std.testing.expectEqual(@as(u32, 0x1), nat_ref_u32.ptr_mask_64);
    try std.testing.expectEqual(@as(u32, 0), nat_ref_u32._pad);

    // `WASM32`: `&u32` shrinks to 4 bytes (`align_log2 == 2`), and `[u8]` slice is 8-byte `pair_regs`:
    const wasm_ref_u32 = mir_opt.computeLayoutShapeKey(&pool, &sym_table, ref_u32, TargetLayout.WASM32);
    const wasm_slice = mir_opt.computeLayoutShapeKey(&pool, &sym_table, slice_u8, TargetLayout.WASM32);
    try std.testing.expectEqual(@as(u32, 4), wasm_ref_u32.size_bytes);
    try std.testing.expectEqual(@as(u8, 2), wasm_ref_u32.align_log2);
    try std.testing.expectEqual(@as(u32, 8), wasm_slice.size_bytes);
    try std.testing.expectEqual(AbiPassClass.pair_regs, wasm_slice.abi_class);
    try std.testing.expectEqual(@as(u32, 0x1), wasm_slice.ptr_mask_64);

    // Primitives (`()`, `bool`, `f64`, `u128`) map to distinct ABI classes and niche encodings:
    try std.testing.expectEqual(
        AbiPassClass.zst,
        mir_opt.computeLayoutShapeKey(&pool, &sym_table, .unit_ty, TargetLayout.NATIVE_64).abi_class,
    );
    try std.testing.expectEqual(
        NicheKind.bool_01,
        mir_opt.computeLayoutShapeKey(&pool, &sym_table, .bool_ty, TargetLayout.NATIVE_64).niche_kind,
    );
    try std.testing.expectEqual(
        AbiPassClass.float_reg,
        mir_opt.computeLayoutShapeKey(&pool, &sym_table, .f64_ty, TargetLayout.NATIVE_64).abi_class,
    );
    try std.testing.expectEqual(
        AbiPassClass.indirect_sret,
        mir_opt.computeLayoutShapeKey(&pool, &sym_table, .u128_ty, TargetLayout.WASM32).abi_class,
    );
}

test "test_mir_opt_dev_pipeline_d1_to_d4_subscript_dead_trap_ghost_strip_and_prune" {
    const allocator = std.testing.allocator;

    // [1] Positive `--dev` (`D1`–`D4`): `subscript`, `@inline(always)`, dead-branch `1 / 0` safety,
    // `D3` Ghost stripping (`is_preserving_pre_strip_mir = true`), and `D4` unreachable block pruning:
    const dev_src =
        \\pub struct GridRow {
        \\    pub cells: [i64; 4],
        \\}
        \\
        \\pub subscript grid_cell(mut row: inout GridRow, idx: usize) -> i64 {
        \\    yield row.cells[idx];
        \\}
        \\
        \\@inline(always)
        \\pub fn scale_up(val: i64) -> i64 {
        \\    return val * 3;
        \\}
        \\
        \\pub fn dev_compute(seed: i64) -> i64 {
        \\    if false {
        \\        return 1 / 0;
        \\    }
        \\    var row = GridRow { cells: [2, 4, 6, 8] };
        \\    grid_cell(row, 1) += seed;
        \\    let cell_ref: &i64 = &grid_cell(row, 1);
        \\    return scale_up(*cell_ref) + (5 * 4);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(400),
        dev_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var opt_sink = DiagnosticSink.init(allocator);
    defer opt_sink.deinit();

    var dev_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        dev_src,
        false,
        true,
        TargetLayout.NATIVE_64,
        &opt_sink,
    );
    defer dev_res.deinit();

    // Dead `if false { return 1 / 0; }` MUST NOT trigger `E0507`:
    try std.testing.expect(!opt_sink.hasErrors());

    // `D3`: `pre_strip_bodies` retain Ghost markers for Phase 6 SAST, while `bodies` are stripped:
    try std.testing.expectEqual(dev_res.bodies.items.len, dev_res.pre_strip_bodies.items.len);
    for (dev_res.pre_strip_bodies.items) |*pre_body| {
        try std.testing.expect(!pre_body.is_ghost_stripped);
    }
    for (dev_res.bodies.items) |*post_body| {
        try std.testing.expect(post_body.is_ghost_stripped);
        try std.testing.expect(!post_body.has_ghost_instructions);
        try mir.verifyMirBody(
            allocator,
            post_body,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            null,
        );
    }

    const compute_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "dev_compute").?;
    // `D1` spliced `@inline(always) scale_up` and `subscript` yielded zero `.call` terminators:
    try std.testing.expectEqual(@as(usize, 0), countBodyTerminator(compute_body, .call));
    // `D4` folded `if false` constant branch and pruned the dead division block:
    try std.testing.expectEqual(@as(usize, 0), countBodyTerminator(compute_body, .cond_br));
    try std.testing.expect(compute_body.is_contextless);

    // `(4 + 6) * 3 + 20 == 50`:
    const slot_out = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &dev_res,
        "dev_compute",
        &.{.{ .scalar_i64 = 6 }},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 50), slot_out.scalar_i64);

    // [2] Reachable constant `1 / 0` in `D2` MUST emit `E0507` without cascading extra traps:
    const trap_src =
        \\pub fn reachable_zero_div() -> i64 {
        \\    if true {
        \\        return 99 / (4 - 4);
        \\    }
        \\    return 0;
        \\}
    ;
    var trap_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(401),
        trap_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer trap_bundle.deinit();

    var trap_sink = DiagnosticSink.init(allocator);
    defer trap_sink.deinit();

    var trap_res = try runOptimizeOnBundle(
        allocator,
        &trap_bundle,
        trap_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &trap_sink,
    );
    defer trap_res.deinit();
    try std.testing.expectEqual(@as(usize, 1), trap_sink.diagnostics.items.len);
    try std.testing.expect(hasDiagnosticCode(&trap_sink, .e0507_comptime_arithmetic_trap));
}

test "test_mir_opt_d5_monomorphize_type_groups_and_tarjan_scc_contextless_promotion" {
    const allocator = std.testing.allocator;

    const mono_src =
        \\pub fn triple_num(val: Number) -> Number {
        \\    return val + val + val;
        \\}
        \\
        \\pub fn abs_diff_signed(lhs: any Signed, rhs: any Signed) -> i64 {
        \\    let left_i64 = lhs as i64;
        \\    let right_i64 = rhs as i64;
        \\    if left_i64 >= right_i64 {
        \\        return left_i64 - right_i64;
        \\    }
        \\    return right_i64 - left_i64;
        \\}
        \\
        \\pub fn head_plus_tail[T: Number, const LEN: usize](arr: [T; LEN]) -> T {
        \\    return arr[0] + arr[LEN - 1];
        \\}
        \\
        \\pub fn even_ping(count: i64) -> i64 {
        \\    if count <= 0 {
        \\        return 1;
        \\    }
        \\    return odd_pong(count - 1);
        \\}
        \\
        \\pub fn odd_pong(count: i64) -> i64 {
        \\    if count <= 0 {
        \\        return 2;
        \\    }
        \\    return even_ping(count - 1);
        \\}
        \\
        \\pub fn run_poly_suite() -> i64 {
        \\    let val_i64: i64 = 7;
        \\    let val_u32: u32 = 4;
        \\    let val_f64: f64 = 2.5;
        \\    let neg_ten: i8 = -10;
        \\    let pos_five: i64 = 5;
        \\    let i_sum = triple_num(val_i64);
        \\    let u_sum = triple_num(val_u32) as i64;
        \\    let f_sum = triple_num(val_f64) as i64;
        \\    let s_diff = abs_diff_signed(neg_ten, pos_five);
        \\    let fixed_arr: [i64; 4] = [10, 20, 30, 40];
        \\    let ends = head_plus_tail(fixed_arr);
        \\    return i_sum + u_sum + f_sum + s_diff + ends + even_ping(3);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(402),
        mono_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var opt_sink = DiagnosticSink.init(allocator);
    defer opt_sink.deinit();

    var dev_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        mono_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &opt_sink,
    );
    defer dev_res.deinit();
    try std.testing.expect(!opt_sink.hasErrors());

    // Tarjan SCC `contextless` promotion marks mutually recursive pure `even_ping`/`odd_pong` contextless:
    const ping_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "even_ping").?;
    const pong_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "odd_pong").?;
    const suite_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "run_poly_suite").?;
    try std.testing.expect(ping_body.is_contextless);
    try std.testing.expect(pong_body.is_contextless);
    try std.testing.expect(suite_body.is_contextless);

    // `21 + 12 + 7 + 15 + 50 + 2 == 107`:
    const out_slot = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &dev_res,
        "run_poly_suite",
        &.{},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 107), out_slot.scalar_i64);
}

test "test_mir_opt_d5_layout_shape_dedup_positive_and_negative_soundness_guards" {
    const allocator = std.testing.allocator;

    // [1] Positive `D5` deduplication: `select_ref[T]` instantiated with `&u32` and `&i32` shares
    // identical `LayoutShapeKey` + `OpSemanticsTag.pointer_or_ref` and merges (`dedup_merged_count >= 1`):
    const pos_src =
        \\pub fn select_ref[T](is_left: bool, left_ptr: T, right_ptr: T) -> T {
        \\    if is_left {
        \\        return left_ptr;
        \\    }
        \\    return right_ptr;
        \\}
        \\
        \\pub fn run_ptr_dedup() -> i64 {
        \\    let u_left: u32 = 11;
        \\    let u_right: u32 = 22;
        \\    let i_left: i32 = 33;
        \\    let i_right: i32 = 44;
        \\    let chosen_u = select_ref(true, &u_left, &u_right);
        \\    let chosen_i = select_ref(false, &i_left, &i_right);
        \\    return (*chosen_u as i64) + (*chosen_i as i64);
        \\}
    ;

    var pos_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(403),
        pos_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer pos_bundle.deinit();
    try std.testing.expect(!pos_bundle.hir_bundle.diagnostics.hasErrors());

    var pos_sink = DiagnosticSink.init(allocator);
    defer pos_sink.deinit();

    var pos_res = try runOptimizeOnBundle(
        allocator,
        &pos_bundle,
        pos_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &pos_sink,
    );
    defer pos_res.deinit();
    try std.testing.expect(!pos_sink.hasErrors());
    try std.testing.expect(pos_res.dedup_merged_count >= 1);

    const pos_val = try evalOptimizedFnSlot(
        allocator,
        &pos_bundle,
        &pos_res,
        "run_ptr_dedup",
        &.{},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 55), pos_val.scalar_i64);

    // [2] Negative soundness guards (`@type_name[T]()` on `&u32` vs `&i32`, signed vs unsigned
    // `i32` vs `u32` division/comparison, and distinct field-offset 8-byte tuples never merge):
    const neg_src =
        \\pub fn ptr_type_label[T](ptr_val: T) -> str {
        \\    let _ = ptr_val;
        \\    return @type_name[T]();
        \\}
        \\
        \\pub fn div_and_cmp[T: Integer](lhs: T, rhs: T) -> (T, bool) {
        \\    return (lhs / rhs, lhs < rhs);
        \\}
        \\
        \\pub fn extract_second[A, B](quad: (A, B)) -> B {
        \\    return quad.1;
        \\}
        \\
        \\pub fn label_ref_u32() -> str {
        \\    let sample: u32 = 1;
        \\    return ptr_type_label(&sample);
        \\}
        \\
        \\pub fn label_ref_i32() -> str {
        \\    let sample: i32 = 1;
        \\    return ptr_type_label(&sample);
        \\}
        \\
        \\pub fn verify_negative_dedup_guards() -> i64 {
        \\    let neg_eight: i32 = -8;
        \\    let pos_two_i: i32 = 2;
        \\    let big_u32: u32 = 4294967288;
        \\    let pos_two_u: u32 = 2;
        \\    let div_u32: u32 = 1073741822;
        \\    let signed_res = div_and_cmp(neg_eight, pos_two_i);
        \\    let unsigned_res = div_and_cmp(big_u32, pos_two_u);
        \\    let tup_narrow_first: (u16, u32) = (9, 700);
        \\    let tup_wide_first: (u32, u16) = (9, 300);
        \\    let sec_a = extract_second(tup_narrow_first) as i64;
        \\    let sec_b = extract_second(tup_wide_first) as i64;
        \\    var total: i64 = (signed_res.0 as i64) + ((unsigned_res.0 / div_u32) as i64);
        \\    if signed_res.1 and !unsigned_res.1 {
        \\        total += sec_a + sec_b;
        \\    }
        \\    return total;
        \\}
    ;

    var neg_bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(404),
        neg_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer neg_bundle.deinit();
    try std.testing.expect(!neg_bundle.hir_bundle.diagnostics.hasErrors());

    var neg_sink = DiagnosticSink.init(allocator);
    defer neg_sink.deinit();

    var neg_res = try runOptimizeOnBundle(
        allocator,
        &neg_bundle,
        neg_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &neg_sink,
    );
    defer neg_res.deinit();
    try std.testing.expect(!neg_sink.hasErrors());
    // ZERO unsound merges allowed across `@type_name`, signedness, or distinct field offsets:
    try std.testing.expectEqual(@as(u32, 0), neg_res.dedup_merged_count);

    try std.testing.expectEqualStrings(
        "&u32",
        try evalOptimizedFnStr(allocator, &neg_bundle, &neg_res, "label_ref_u32", TargetLayout.NATIVE_64),
    );
    try std.testing.expectEqualStrings(
        "&i32",
        try evalOptimizedFnStr(allocator, &neg_bundle, &neg_res, "label_ref_i32", TargetLayout.NATIVE_64),
    );

    // `-4 + (2147483644 / 1073741822 == 2) + 700 + 300 == 998`:
    const guard_slot = try evalOptimizedFnSlot(
        allocator,
        &neg_bundle,
        &neg_res,
        "verify_negative_dedup_guards",
        &.{},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 998), guard_slot.scalar_i64);
}

test "test_mir_opt_release_r1_inliner_and_w0501_on_recursion_and_budget_overflow" {
    const allocator = std.testing.allocator;

    const r1_src =
        \\@inline
        \\pub fn tiny_step(val: i64) -> i64 {
        \\    return val + 7;
        \\}
        \\
        \\@inline
        \\pub fn rec_countdown(num: i64) -> i64 {
        \\    if num <= 0 {
        \\        return 0;
        \\    }
        \\    return 1 + rec_countdown(num - 1);
        \\}
        \\
        \\@inline
        \\pub fn huge_over_budget(seed: i64) -> i64 {
        \\    var acc = seed;
        \\    acc = (acc + 1) * 2 - 1;
        \\    acc = (acc + 2) * 2 - 3;
        \\    acc = (acc + 3) * 2 - 5;
        \\    acc = (acc + 4) * 2 - 7;
        \\    acc = (acc + 5) * 2 - 9;
        \\    acc = (acc + 6) * 2 - 11;
        \\    acc = (acc + 7) * 2 - 13;
        \\    acc = (acc + 8) * 2 - 15;
        \\    acc = (acc + 9) * 2 - 17;
        \\    acc = (acc + 10) * 2 - 19;
        \\    acc = (acc + 11) * 2 - 21;
        \\    acc = (acc + 12) * 2 - 23;
        \\    acc = (acc + 13) * 2 - 25;
        \\    acc = (acc + 14) * 2 - 27;
        \\    acc = (acc + 15) * 2 - 29;
        \\    acc = (acc + 16) * 2 - 31;
        \\    acc = (acc + 17) * 2 - 33;
        \\    acc = (acc + 18) * 2 - 35;
        \\    acc = (acc + 19) * 2 - 37;
        \\    acc = (acc + 20) * 2 - 39;
        \\    acc = (acc + 21) * 2 - 41;
        \\    acc = (acc + 22) * 2 - 43;
        \\    return acc;
        \\}
        \\
        \\pub fn call_small_only(val: i64) -> i64 {
        \\    return tiny_step(val) + tiny_step(val + 1);
        \\}
        \\
        \\pub fn call_all_r1(val: i64) -> i64 {
        \\    return call_small_only(val) + rec_countdown(3) + huge_over_budget(1);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(405),
        r1_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();

    var rel_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        r1_src,
        true,
        false,
        TargetLayout.NATIVE_64,
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());

    // Both `rec_countdown` (recursive `@inline`) and `huge_over_budget` (`> INLINE_HINT_BUDGET`) emit `W0501`:
    var w0501_count: usize = 0;
    for (rel_sink.diagnostics.items) |diag_item| {
        if (diag_item.code == .w0501_inlining_budget_exceeded) {
            w0501_count += 1;
        }
    }
    try std.testing.expect(w0501_count >= 2);

    // `tiny_step` WAS inlined into `call_small_only` (zero `.call` terminators remain in `call_small_only`):
    try std.testing.expectEqual(
        @as(usize, 0),
        countBodyTerminator(rel_res.findBodyByName(&bundle.hir_bundle.interner, "call_small_only").?, .call),
    );

    // Verify `--dev` vs `--release` semantic equivalence on `call_all_r1`:
    var dev_sink = DiagnosticSink.init(allocator);
    defer dev_sink.deinit();
    var dev_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        r1_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &dev_sink,
    );
    defer dev_res.deinit();

    const dev_val = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &dev_res,
        "call_all_r1",
        &.{.{ .scalar_i64 = 4 }},
        TargetLayout.NATIVE_64,
    );
    const rel_val = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &rel_res,
        "call_all_r1",
        &.{.{ .scalar_i64 = 4 }},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(dev_val.scalar_i64, rel_val.scalar_i64);
}

test "test_mir_opt_release_r2_sroa_composite_promotion_and_loop_accumulator_45" {
    const allocator = std.testing.allocator;

    const sroa_src =
        \\pub struct Accumulator {
        \\    pub sum: i64,
        \\    pub steps: i64,
        \\}
        \\
        \\pub fn loop_sum_ten() -> i64 {
        \\    var acc = Accumulator { sum: 0, steps: 0 };
        \\    let start_i: i64 = 0;
        \\    let end_i: i64 = 10;
        \\    for idx in start_i..end_i {
        \\        acc.sum = acc.sum + idx;
        \\        acc.steps = acc.steps + 1;
        \\    }
        \\    return acc.sum;
        \\}
        \\
        \\pub fn tuple_pair_math(lhs: i64, rhs: i64) -> i64 {
        \\    var pair = (lhs + 3, rhs * 2);
        \\    pair.0 = pair.0 + 1;
        \\    return pair.0 + pair.1;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(406),
        sroa_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var dev_sink = DiagnosticSink.init(allocator);
    defer dev_sink.deinit();
    var dev_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        sroa_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &dev_sink,
    );
    defer dev_res.deinit();

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();

    var rel_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        sroa_src,
        true,
        false,
        TargetLayout.NATIVE_64,
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());

    // `R2` SROA promotes mutable non-address-taken `(i64, i64)` and `Accumulator` out of memory places:
    const dev_tup = dev_res.findBodyByName(&bundle.hir_bundle.interner, "tuple_pair_math").?;
    const rel_tup = rel_res.findBodyByName(&bundle.hir_bundle.interner, "tuple_pair_math").?;
    try std.testing.expect(countBodyOp(rel_tup, .place_load) < countBodyOp(dev_tup, .place_load));
    try std.testing.expect(countBodyOp(rel_tup, .place_store) < countBodyOp(dev_tup, .place_store));

    const dev_loop = dev_res.findBodyByName(&bundle.hir_bundle.interner, "loop_sum_ten").?;
    const rel_loop = rel_res.findBodyByName(&bundle.hir_bundle.interner, "loop_sum_ten").?;
    try std.testing.expect(countBodyOp(rel_loop, .place_load) < countBodyOp(dev_loop, .place_load));

    // Loop-carried struct accumulator `0..10` evaluates cleanly to `45`:
    const sum_slot = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &rel_res,
        "loop_sum_ten",
        &.{},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 45), sum_slot.scalar_i64);

    const tup_slot = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &rel_res,
        "tuple_pair_math",
        &.{ .{ .scalar_i64 = 7 }, .{ .scalar_i64 = 5 } },
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 21), tup_slot.scalar_i64);
}

test "test_mir_opt_release_r3_vrp_assert_folding_and_u128_high_bit_soundness" {
    const allocator = std.testing.allocator;

    const vrp_src =
        \\pub fn vrp_provable_bounds(raw_idx: usize) -> i64 {
        \\    let table: [i64; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
        \\    if raw_idx < 4 {
        \\        if raw_idx < 8 {
        \\            return table[raw_idx];
        \\        }
        \\        return -2;
        \\    }
        \\    return -1;
        \\}
        \\
        \\pub fn vrp_high_bit_u128(is_top_bit: bool) -> i64 {
        \\    var wide_num: u128 = 170141183460469231731687303715884105729;
        \\    if !is_top_bit {
        \\        wide_num = 25;
        \\    }
        \\    if wide_num < 10 {
        \\        return 999;
        \\    }
        \\    return 42;
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(407),
        vrp_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Inject a synthetic `MirIntrinsicKind.compile_assert` (`raw_idx < 8`) inside the `raw_idx < 4` block
    // so `R3` VRP folds BOTH the relational range check AND the `compile_assert` intrinsic (`DR-13` §6.2 `R3`):
    for (bundle.mir_bundle.bodies.items) |*raw_bounds_body| {
        if (raw_bounds_body.name == .empty or
            !std.mem.eql(u8, bundle.hir_bundle.interner.get(raw_bounds_body.name), "vrp_provable_bounds"))
        {
            continue;
        }
        for (raw_bounds_body.blocks.items, 0..) |bb_rec, bb_idx| {
            for (raw_bounds_body.getBlockInsts(mir.MirBlockId.fromInt(@intCast(bb_idx)))) |inst_id| {
                const inst = raw_bounds_body.getInst(inst_id);
                if (inst.op == .bin_op and inst.type_id == .bool_ty and bb_idx > 0 and !bb_rec.isCleanupPad()) {
                    const arg_off: u32 = @intCast(raw_bounds_body.extra_args.items.len);
                    try raw_bounds_body.extra_args.append(raw_bounds_body.allocator, inst_id.asInt());
                    const assert_val = try raw_bounds_body.appendInst(.{
                        .op = .intrinsic_op,
                        .flags = .{ .has_side_effects = true, .has_trap_risk = true },
                        .aux_u16 = @backingInt(mir.MirIntrinsicKind.compile_assert),
                        .type_id = .unit_ty,
                        .operands = .{ .lhs = arg_off, .rhs = 1 },
                    }, .none);
                    const insert_pos = raw_bounds_body.blocks.items[bb_idx].inst_start +
                        raw_bounds_body.blocks.items[bb_idx].inst_len;
                    try raw_bounds_body.block_insts.insert(raw_bounds_body.allocator, insert_pos, assert_val);
                    raw_bounds_body.blocks.items[bb_idx].inst_len += 1;
                    for ((bb_idx + 1)..raw_bounds_body.blocks.items.len) |later_bb| {
                        raw_bounds_body.blocks.items[later_bb].inst_start += 1;
                    }
                    break;
                }
            }
        }
    }

    var dev_sink = DiagnosticSink.init(allocator);
    defer dev_sink.deinit();
    var dev_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        vrp_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &dev_sink,
    );
    defer dev_res.deinit();

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();
    var rel_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        vrp_src,
        true,
        false,
        TargetLayout.NATIVE_64,
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());

    // `R3` VRP + `R5` DCE folds `compile_assert(raw_idx < 8)` (`.intrinsic_op`) AND eliminates inner `cond_br`:
    const rel_bounds = rel_res.findBodyByName(&bundle.hir_bundle.interner, "vrp_provable_bounds").?;
    const dev_bounds = dev_res.findBodyByName(&bundle.hir_bundle.interner, "vrp_provable_bounds").?;
    try std.testing.expect(countBodyOp(rel_bounds, .intrinsic_op) < countBodyOp(dev_bounds, .intrinsic_op));
    try std.testing.expectEqual(@as(usize, 1), countBodyTerminator(rel_bounds, .cond_br));

    const bounds_hit = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &rel_res,
        "vrp_provable_bounds",
        &.{.{ .scalar_u64 = 2 }},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 30), bounds_hit.scalar_i64);

    // `u128` value `2^127 + 1` MUST NOT wrap negative in VRP (`wide_num < 10` stays `false` -> `42`):
    const u128_top_out = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &rel_res,
        "vrp_high_bit_u128",
        &.{.{ .scalar_u64 = 1 }},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 42), u128_top_out.scalar_i64);
}

test "test_mir_opt_release_r4_sccp_switch_fusion_commutative_gvn_r5_dce_and_r6_icf" {
    const allocator = std.testing.allocator;

    const r4_r6_src =
        \\pub fn sccp_and_switch_fusion(tag_in: i64) -> i64 {
        \\    let fixed_mode: i64 = 2;
        \\    let mode_tag: i64 = if fixed_mode == 2 { 20 } else { 90 };
        \\    let dead_calc = (tag_in + 123) * 3;
        \\    let _ = dead_calc;
        \\    if mode_tag == 10 {
        \\        return tag_in + 1;
        \\    } else if mode_tag == 20 {
        \\        return tag_in + 100;
        \\    }
        \\    return tag_in + 999;
        \\}
        \\
        \\pub fn cascaded_switch_target(disc: i64) -> i64 {
        \\    return disc;
        \\}
        \\
        \\pub fn commutative_gvn_calc(lhs: i64, rhs: i64) -> i64 {
        \\    let sum_ab = lhs + rhs;
        \\    let sum_ba = rhs + lhs;
        \\    let prod_ab = lhs * rhs;
        \\    let prod_ba = rhs * lhs;
        \\    return (sum_ab - sum_ba) + (prod_ab - prod_ba) + sum_ab;
        \\}
        \\
        \\@inline(never)
        \\pub fn twin_hash_one(first: i64, second: i64) -> i64 {
        \\    let sum_part = first + second;
        \\    let mix_part = sum_part * 3;
        \\    return mix_part - first;
        \\}
        \\
        \\@inline(never)
        \\pub fn twin_hash_two(alpha: i64, beta: i64) -> i64 {
        \\    let total_part = alpha + beta;
        \\    let scaled_part = total_part * 3;
        \\    return scaled_part - alpha;
        \\}
        \\
        \\pub fn invoke_twins(seed: i64) -> i64 {
        \\    return sccp_and_switch_fusion(seed)
        \\        + commutative_gvn_calc(seed, 3)
        \\        + twin_hash_one(seed, 5)
        \\        + twin_hash_two(seed, 5);
        \\}
    ;

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(408),
        r4_r6_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Build a 2-stage cascaded `switch_int` inside `cascaded_switch_target` (`bb0 -> default bb1 -> switch_int`)
    // so `R4` `fuseAdjacentSwitchIntBlocks` fuses both `switch_int` terminators into 1 (`DR-13` §6.2 `R4`):
    for (bundle.mir_bundle.bodies.items) |*raw_body| {
        if (raw_body.name == .empty or
            !std.mem.eql(u8, bundle.hir_bundle.interner.get(raw_body.name), "cascaded_switch_target"))
        {
            continue;
        }
        var rebuilt = mir.MirBody.init(allocator, raw_body.file_id, raw_body.def_id);
        rebuilt.name = raw_body.name;
        rebuilt.ret_ty = .i64_ty;
        rebuilt.param_count = 1;
        rebuilt.is_contextless = true;
        rebuilt.has_ghost_instructions = true;
        try rebuilt.locals.append(
            allocator,
            mir.LocalDecl.init(.empty, .i64_ty, .none, 0, .let_mode, .{ .is_return_slot = true }),
        );
        try rebuilt.locals.append(
            allocator,
            mir.LocalDecl.init(.empty, .i64_ty, .none, 0, .let_mode, .{ .is_arg = true }),
        );
        const param_pl = mir.PlaceId.fromInt(0);
        try rebuilt.places.append(allocator, .{ .base = 1, .proj_start = 0, .proj_len = 0 });

        var ssa = mir.MirSsaBuilder.init(allocator, &rebuilt, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const bb1 = try ssa.createBlock(true, false);
        const bb_case0 = try ssa.createBlock(true, false);
        const bb_case1 = try ssa.createBlock(true, false);
        const bb_def = try ssa.createBlock(true, false);

        _ = try ssa.emitInst(
            bb0,
            .{ .op = .ghost_storage_init, .type_id = .unit_ty, .operands = .{ .lhs = 0, .rhs = 0 } },
            .none,
        );
        _ = try ssa.emitInst(
            bb0,
            .{ .op = .ghost_storage_init, .type_id = .unit_ty, .operands = .{ .lhs = 1, .rhs = 0 } },
            .none,
        );
        const disc_val = try ssa.emitInst(
            bb0,
            .{ .op = .place_load, .type_id = .i64_ty, .operands = .{ .lhs = param_pl.asInt(), .rhs = 0 } },
            .none,
        );
        const idx10 = try rebuilt.appendConst(.{ .int_val = 10 });
        const idx20 = try rebuilt.appendConst(.{ .int_val = 20 });
        const idx30 = try rebuilt.appendConst(.{ .int_val = 30 });
        const c10 = try ssa.emitInst(
            bb_case0,
            .{ .op = .const_scalar, .type_id = .i64_ty, .operands = .{ .lhs = idx10, .rhs = 0 } },
            .none,
        );
        const c20 = try ssa.emitInst(
            bb_case1,
            .{ .op = .const_scalar, .type_id = .i64_ty, .operands = .{ .lhs = idx20, .rhs = 0 } },
            .none,
        );
        const c30 = try ssa.emitInst(
            bb_def,
            .{ .op = .const_scalar, .type_id = .i64_ty, .operands = .{ .lhs = idx30, .rhs = 0 } },
            .none,
        );

        const sw_zero: u16 = @intCast(rebuilt.switch_values.items.len);
        try rebuilt.switch_values.append(allocator, 0);
        const sw_one: u16 = @intCast(rebuilt.switch_values.items.len);
        try rebuilt.switch_values.append(allocator, 1);

        const e0_case = try ssa.addOutgoingEdge(bb0, bb_case0, &.{}, sw_zero);
        _ = try ssa.addOutgoingEdge(bb0, bb1, &.{}, std.math.maxInt(u16));
        ssa.setTerminator(bb0, .{
            .kind = .switch_int,
            .cond_or_val = disc_val.asInt(),
            .edge_start = e0_case.asInt(),
            .edge_len = 2,
        });

        const e1_case = try ssa.addOutgoingEdge(bb1, bb_case1, &.{}, sw_one);
        _ = try ssa.addOutgoingEdge(bb1, bb_def, &.{}, std.math.maxInt(u16));
        ssa.setTerminator(bb1, .{
            .kind = .switch_int,
            .cond_or_val = disc_val.asInt(),
            .edge_start = e1_case.asInt(),
            .edge_len = 2,
        });

        ssa.setTerminator(bb_case0, .{ .kind = .ret, .cond_or_val = c10.asInt() });
        ssa.setTerminator(bb_case1, .{ .kind = .ret, .cond_or_val = c20.asInt() });
        ssa.setTerminator(bb_def, .{ .kind = .ret, .cond_or_val = c30.asInt() });
        try ssa.finish();

        raw_body.deinit();
        raw_body.* = rebuilt;
    }

    var dev_sink = DiagnosticSink.init(allocator);
    defer dev_sink.deinit();
    var dev_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        r4_r6_src,
        false,
        false,
        TargetLayout.NATIVE_64,
        &dev_sink,
    );
    defer dev_res.deinit();

    var rel_sink = DiagnosticSink.init(allocator);
    defer rel_sink.deinit();
    var rel_res = try runOptimizeOnBundle(
        allocator,
        &bundle,
        r4_r6_src,
        true,
        false,
        TargetLayout.NATIVE_64,
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());

    // [1] `R4` SCCP + `R5` DCE/jump-threading/block-merging collapses `sccp_and_switch_fusion` to 1 reachable
    // `.ret` block (`0` `.cond_br`, `0` `.br`), and `R4` fuses `cascaded_switch_target` into 1 `switch_int`:
    const sccp_body = rel_res.findBodyByName(&bundle.hir_bundle.interner, "sccp_and_switch_fusion").?;
    try std.testing.expectEqual(mir.TerminatorKind.ret, sccp_body.blocks.items[0].terminator.kind);
    try std.testing.expectEqual(@as(usize, 1), countBodyTerminator(sccp_body, .ret));
    try std.testing.expectEqual(@as(usize, 0), countBodyTerminator(sccp_body, .cond_br));
    try std.testing.expectEqual(@as(usize, 0), countBodyTerminator(sccp_body, .br));

    const dev_sw_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "cascaded_switch_target").?;
    const rel_sw_body = rel_res.findBodyByName(&bundle.hir_bundle.interner, "cascaded_switch_target").?;
    try std.testing.expectEqual(@as(usize, 2), countBodyTerminator(dev_sw_body, .switch_int));
    try std.testing.expectEqual(@as(usize, 1), countBodyTerminator(rel_sw_body, .switch_int));

    // [2] `R4` commutative GVN deduplicates `lhs + rhs` / `rhs + lhs` and `lhs * rhs` / `rhs * lhs`:
    const dev_gvn_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "commutative_gvn_calc").?;
    const rel_gvn_body = rel_res.findBodyByName(&bundle.hir_bundle.interner, "commutative_gvn_calc").?;
    try std.testing.expect(countBodyOp(rel_gvn_body, .bin_op) < countBodyOp(dev_gvn_body, .bin_op));

    // [3] `R6` `Wyhash(0)` + full structural equality ICF folds `twin_hash_one` and `twin_hash_two`,
    // redirecting both call sites inside `invoke_twins` to the same canonical `DefId`:
    try std.testing.expect(rel_res.icf_folded_count >= 1);
    const twins_caller = rel_res.findBodyByName(&bundle.hir_bundle.interner, "invoke_twins").?;
    var twin_call_defs: [2]corex.DefId = .{ .NONE, .NONE };
    var seen_twin_calls: usize = 0;
    const twin_one_def = rel_res.findBodyByName(&bundle.hir_bundle.interner, "twin_hash_one").?.def_id;
    const twin_two_def = rel_res.findBodyByName(&bundle.hir_bundle.interner, "twin_hash_two").?.def_id;
    for (twins_caller.calls.items) |call_site| {
        if (call_site.direct_def_id == twin_one_def or call_site.direct_def_id == twin_two_def) {
            if (seen_twin_calls < 2) {
                twin_call_defs[seen_twin_calls] = call_site.direct_def_id;
            }
            seen_twin_calls += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 2), seen_twin_calls);
    try std.testing.expectEqual(twin_call_defs[0], twin_call_defs[1]);

    // [4] Differential `--dev` vs `--release` execution parity (`(7 + 100) + 10 + 29 + 29 == 175`):
    const dev_out = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &dev_res,
        "invoke_twins",
        &.{.{ .scalar_i64 = 7 }},
        TargetLayout.NATIVE_64,
    );
    const rel_out = try evalOptimizedFnSlot(
        allocator,
        &bundle,
        &rel_res,
        "invoke_twins",
        &.{.{ .scalar_i64 = 7 }},
        TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(i64, 175), dev_out.scalar_i64);
    try std.testing.expectEqual(dev_out.scalar_i64, rel_out.scalar_i64);
}

test "test_mir_opt_differential_dev_vs_release_across_native64_and_wasm32_targets" {
    const allocator = std.testing.allocator;

    const workload_src =
        \\pub enum OpCmd {
        \\    Add(i64),
        \\    Scale(i64),
        \\    Reset,
        \\}
        \\
        \\pub struct MachineState {
        \\    pub value: i64,
        \\    pub edits: i64,
        \\}
        \\
        \\pub fn apply_cmd(state: MachineState, cmd: OpCmd) -> MachineState {
        \\    return match cmd {
        \\        .Add(delta) => MachineState { value: state.value + delta, edits: state.edits + 1 },
        \\        .Scale(factor) => MachineState { value: state.value * factor, edits: state.edits + 1 },
        \\        .Reset => MachineState { value: 0, edits: state.edits + 1 },
        \\    };
        \\}
        \\
        \\pub fn run_workload(seed: i64) -> i64 {
        \\    var st = MachineState { value: seed, edits: 0 };
        \\    let cmd_add: OpCmd = .Add(5);
        \\    let cmd_scale: OpCmd = .Scale(3);
        \\    let cmd_reset: OpCmd = .Reset;
        \\    st = apply_cmd(st, cmd_add);
        \\    st = apply_cmd(st, cmd_scale);
        \\    if seed < 0 {
        \\        st = apply_cmd(st, cmd_reset);
        \\    }
        \\    let ptr_bytes = @size_of[usize]() as i64;
        \\    return st.value + st.edits + ptr_bytes;
        \\}
    ;

    const layouts = [_]TargetLayout{ TargetLayout.NATIVE_64, TargetLayout.WASM32 };
    const expected_for_six = [_]i64{
        // `((6 + 5) * 3) + 2 + 8 == 43` on `NATIVE_64`:
        43,
        // `((6 + 5) * 3) + 2 + 4 == 39` on `WASM32`:
        39,
    };

    for (layouts, 0..) |target_layout, layout_i| {
        var bundle = try mir.lowerSourceToMir(
            allocator,
            FileId.fromInt(@intCast(410 + layout_i)),
            workload_src,
            target_layout,
            .{},
        );
        defer bundle.deinit();
        try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

        var dev_sink = DiagnosticSink.init(allocator);
        defer dev_sink.deinit();
        var dev_res = try runOptimizeOnBundle(
            allocator,
            &bundle,
            workload_src,
            false,
            false,
            target_layout,
            &dev_sink,
        );
        defer dev_res.deinit();
        try std.testing.expect(!dev_sink.hasErrors());

        var rel_sink = DiagnosticSink.init(allocator);
        defer rel_sink.deinit();
        var rel_res = try runOptimizeOnBundle(
            allocator,
            &bundle,
            workload_src,
            true,
            false,
            target_layout,
            &rel_sink,
        );
        defer rel_res.deinit();
        try std.testing.expect(!rel_sink.hasErrors());

        // Every concrete `--dev` and `--release` output body MUST pass `MirVerifier` (`V1`–`V6`):
        for (dev_res.bodies.items) |*dev_body| {
            try mir.verifyMirBody(
                allocator,
                dev_body,
                &bundle.hir_bundle.pool,
                &bundle.hir_bundle.sym_table,
                null,
            );
        }
        for (rel_res.bodies.items) |*rel_body| {
            try mir.verifyMirBody(
                allocator,
                rel_body,
                &bundle.hir_bundle.pool,
                &bundle.hir_bundle.sym_table,
                null,
            );
        }

        const dev_pos = try evalOptimizedFnSlot(
            allocator,
            &bundle,
            &dev_res,
            "run_workload",
            &.{.{ .scalar_i64 = 6 }},
            target_layout,
        );
        const rel_pos = try evalOptimizedFnSlot(
            allocator,
            &bundle,
            &rel_res,
            "run_workload",
            &.{.{ .scalar_i64 = 6 }},
            target_layout,
        );
        try std.testing.expectEqual(expected_for_six[layout_i], dev_pos.scalar_i64);
        try std.testing.expectEqual(dev_pos.scalar_i64, rel_pos.scalar_i64);

        const dev_neg = try evalOptimizedFnSlot(
            allocator,
            &bundle,
            &dev_res,
            "run_workload",
            &.{.{ .scalar_i64 = -4 }},
            target_layout,
        );
        const rel_neg = try evalOptimizedFnSlot(
            allocator,
            &bundle,
            &rel_res,
            "run_workload",
            &.{.{ .scalar_i64 = -4 }},
            target_layout,
        );
        try std.testing.expectEqual(dev_neg.scalar_i64, rel_neg.scalar_i64);
    }
}

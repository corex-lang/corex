//! Unit Tests for Typed High-Level IR (`hir.zig`)
//!
//! Covers 18-byte SoA `HirNode` column layout and `BitSpec` packing, all 12 canonical
//! `AST -> HIR` desugarings (`DR-13` §2.2 & `DR-02` §2.2), deterministic `renderHir`
//! formatting, and per-`DefId` `lowerDefToHir` parity across 64-bit and `wasm32` layouts.

const std = @import("std");
const corex = @import("corex");

const hir = corex.hir;
const mir = corex.mir;
const mir_opt = corex.mir_opt;
const mir_vm = corex.mir_vm;
const parser = corex.parser;
const type_system = corex.type_system;
const symbol_resolver = corex.symbol_resolver;
const diagnostic = corex.diagnostic;

const HirTag = hir.HirTag;
const HirFlags = hir.HirFlags;
const HirNode = hir.HirNode;
const HirIndex = hir.HirIndex;
const HirStore = hir.HirStore;
const HirFnMeta = hir.HirFnMeta;
const BitSpec = hir.BitSpec;
const ReturnErrorKind = hir.ReturnErrorKind;
const HirUnaryOp = hir.HirUnaryOp;
const TargetLayout = type_system.TargetLayout;
const TypeId = corex.TypeId;
const TokenIndex = corex.TokenIndex;
const DefId = corex.DefId;
const FileId = corex.FileId;
const StringInterner = corex.StringInterner;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;

// -------------------------------------- INTERNALS --------------------------------------

/// Checks whether `sink` recorded at least one diagnostic with `expected_code`.
fn hasDiag(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Finds a lowered `HirFnMeta` inside `store` by matching its unqualified function `fn_name`.
fn findFnMetaByName(
    store: *const HirStore,
    interner: *const StringInterner,
    fn_name: []const u8,
) ?HirFnMeta {
    for (store.functions.items) |fn_meta| {
        if (fn_meta.name != .empty) {
            if (std.mem.eql(u8, interner.get(fn_meta.name), fn_name)) return fn_meta;
        }
    }
    return null;
}

/// Counts how many `HirNode`s inside `store` match `wanted_tag` within `[start_idx, end_idx)`.
fn countTagInRange(
    store: *const HirStore,
    start_idx: usize,
    end_idx: usize,
    wanted_tag: HirTag,
) usize {
    const tags = store.nodes.items(.tag);
    const clamped_end = @min(end_idx, tags.len);
    var total_matches: usize = 0;
    var idx: usize = start_idx;
    while (idx < clamped_end) : (idx += 1) {
        if (tags[idx] == wanted_tag) {
            total_matches += 1;
        }
    }
    return total_matches;
}

/// Computes `[start_idx, end_idx)` of `HirNode`s emitted for `fn_pos` inside `store.functions`.
fn fnNodeSpan(store: *const HirStore, fn_pos: usize) struct { start: usize, end: usize } {
    const start_idx: usize = if (fn_pos > 0 and !store.functions.items[fn_pos - 1].body_hir.isNone())
        store.functions.items[fn_pos - 1].body_hir.asInt() + 1
    else
        0;
    const end_idx: usize = if (!store.functions.items[fn_pos].body_hir.isNone())
        store.functions.items[fn_pos].body_hir.asInt() + 1
    else
        store.countNodes();
    return .{ .start = start_idx, .end = end_idx };
}

/// Parses, resolves signatures, and lowers `source` via `hir.lowerFileToHir` for virtual syntax desugaring tests.
fn lowerResolvedAstToHir(
    allocator: std.mem.Allocator,
    source: []const u8,
) !hir.HirSourceBundle {
    const file_id = FileId.fromInt(0);
    var interner = try StringInterner.init(allocator);
    errdefer interner.deinit();
    var diagnostics = DiagnosticSink.init(allocator);
    errdefer diagnostics.deinit();
    var tokens = corex.TokenBuffer.init(allocator);
    errdefer tokens.deinit();
    var cst_arena = corex.LosslessCstArena.init(allocator);
    errdefer cst_arena.deinit();
    var ast_arena = corex.AstArena.init(allocator);
    errdefer ast_arena.deinit();

    _ = try parser.parseSource(
        source,
        file_id,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
        &interner,
    );

    var sym_table = try symbol_resolver.SymbolTable.init(allocator, &interner);
    errdefer sym_table.deinit();
    _ = try symbol_resolver.collectFileModuleItems(
        &sym_table,
        &interner,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        &diagnostics,
    );
    try symbol_resolver.resolveFileUseImports(
        &sym_table,
        &interner,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &diagnostics,
    );

    var pool = try type_system.InternPool.init(allocator);
    errdefer pool.deinit();
    var checker = try type_system.TypeChecker.init(
        allocator,
        &interner,
        &pool,
        &sym_table,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        null,
    );
    defer checker.deinit();
    try checker.resolveModuleSignatures();

    const hir_store = try hir.lowerFileToHir(
        allocator,
        file_id,
        source,
        &tokens,
        &cst_arena,
        &ast_arena,
        &interner,
        &pool,
        &sym_table,
        null,
        &diagnostics,
        TargetLayout.NATIVE_64,
        .{},
    );

    return .{
        .allocator = allocator,
        .interner = interner,
        .tokens = tokens,
        .cst_arena = cst_arena,
        .ast_arena = ast_arena,
        .sym_table = sym_table,
        .pool = pool,
        .side_tables = .{
            .allocator = allocator,
            .def_id = .NONE,
            .ast_start = 0,
            .ast_end = 0,
            .node_types = &.{},
            .node_symbols = &.{},
        },
        .hir_store = hir_store,
        .diagnostics = diagnostics,
    };
}

/// Compiles `source` through `HIR -> MIR` and evaluates `entry_name(args)` in `MirVm` as `i64`.
fn evalSourceFnI64(
    allocator: std.mem.Allocator,
    source: []const u8,
    target_layout: TargetLayout,
    entry_name: []const u8,
    arg_slots: []const mir_vm.RegSlot,
    step_budget: u64,
) !i64 {
    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(0),
        source,
        target_layout,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var opt_sink = DiagnosticSink.init(allocator);
    defer opt_sink.deinit();
    var opt_res = try mir_opt.optimizeMirModule(
        allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{
            .is_release_mode = false,
            .target_layout = target_layout,
            .syntax_view = .{
                .source = source,
                .tokens = &bundle.hir_bundle.tokens,
                .cst_arena = &bundle.hir_bundle.cst_arena,
            },
        },
        &opt_sink,
    );
    defer opt_res.deinit();
    try std.testing.expect(!opt_sink.hasErrors());

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();
    var memo_cache = mir_vm.PureCallMemoCache.init(allocator);
    defer memo_cache.deinit();

    var vm_engine = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        &memo_cache,
        &bundle.hir_bundle.diagnostics,
        .{ .target_layout = target_layout, .step_budget = step_budget },
    );
    defer vm_engine.deinit();

    for (opt_res.bodies.items) |*body_item| {
        var sym_idx = bundle.hir_bundle.sym_table.def_to_symbol.get(
            body_item.def_id.asInt(),
        ) orelse symbol_resolver.SymbolIndex.none;
        if (sym_idx.isNone()) {
            for (bundle.hir_bundle.hir_store.functions.items) |fn_meta| {
                if (fn_meta.name == body_item.name and !fn_meta.symbol_index.isNone()) {
                    sym_idx = fn_meta.symbol_index;
                    break;
                }
            }
        }
        _ = try vm_engine.registerBody(body_item, sym_idx);
    }

    const entry_body = opt_res.findBodyByName(
        &bundle.hir_bundle.interner,
        entry_name,
    ) orelse return error.MissingEntryBody;
    const eval_res = try vm_engine.evalBody(entry_body, arg_slots);
    try std.testing.expectEqual(mir_vm.VmValueRepr.inline_scalar, eval_res.repr);
    return eval_res.slot.scalar_i64;
}

// ------------------------------------- PUBLIC API --------------------------------------

// Byte-layout and BitSpec packing invariants:

test "test_hir_soa_column_byte_layout_and_bitspec_packing" {
    // [1] Exact 18-byte SoA column sum (`DR-13` §2.1) and 20-byte AoS `HirNode`:
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(HirTag));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(HirFlags));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TypeId));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TokenIndex));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(HirNode.Data));
    const soa_column_bytes = @sizeOf(HirTag) +
        @sizeOf(HirFlags) +
        @sizeOf(TypeId) +
        @sizeOf(TokenIndex) +
        @sizeOf(HirNode.Data);
    try std.testing.expectEqual(@as(usize, 18), soa_column_bytes);
    try std.testing.expectEqual(@as(usize, 20), @sizeOf(HirNode));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(BitSpec));

    // [2] Exhaustive `BitSpec` round-trip across signed/unsigned widths (`u8`, `u16`, `u32`, `u64`):
    const sample_specs = [_]BitSpec{
        .{ .bit_offset = 0, .bit_width = 1, .backing_bits = 8, .is_signed = false },
        .{ .bit_offset = 1, .bit_width = 4, .backing_bits = 16, .is_signed = true },
        .{ .bit_offset = 5, .bit_width = 11, .backing_bits = 16, .is_signed = false },
        .{ .bit_offset = 19, .bit_width = 13, .backing_bits = 32, .is_signed = true },
        .{ .bit_offset = 32, .bit_width = 32, .backing_bits = 64, .is_signed = false },
    };
    for (sample_specs) |expected_spec| {
        const unpacked = BitSpec.fromU32(expected_spec.asU32());
        try std.testing.expectEqual(expected_spec.bit_offset, unpacked.bit_offset);
        try std.testing.expectEqual(expected_spec.bit_width, unpacked.bit_width);
        try std.testing.expectEqual(expected_spec.backing_bits, unpacked.backing_bits);
        try std.testing.expectEqual(expected_spec.is_signed, unpacked.is_signed);
    }
}

// Rule 1: Pipeline `|>` desugaring (bare, call, and method prepend):

test "test_hir_desugar_pipeline_bare_call_and_method_prepend" {
    const pipe_src =
        "pub struct Scaler {\n" ++
        "    pub factor: i32,\n" ++
        "}\n" ++
        "impl Scaler {\n" ++
        "    pub fn apply(&self, input: i32, bias: i32) -> i32 {\n" ++
        "        return input * self.factor + bias;\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn double_val(num: i32) -> i32 {\n" ++
        "    return num * 2;\n" ++
        "}\n" ++
        "pub fn affine_step(num: i32, mul: i32, addend: i32) -> i32 {\n" ++
        "    return num * mul + addend;\n" ++
        "}\n" ++
        "pub fn run_pipes(seed: i32) -> i32 {\n" ++
        "    let scaler = Scaler { factor: 4 };\n" ++
        "    let first = seed |> double_val |> affine_step(3, 7);\n" ++
        "    return first |> scaler.apply(5);\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        pipe_src,
        TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());

    // Verify `run_pipes` contains 3 lowered `hir_call` nodes (`double_val`, `affine_step`, `apply`):
    const store = &bundle.hir_store;
    var found_calls: usize = 0;
    for (store.functions.items, 0..) |fn_meta, fn_pos| {
        if (fn_meta.name != .empty and
            std.mem.eql(u8, bundle.interner.get(fn_meta.name), "run_pipes"))
        {
            const span_range = fnNodeSpan(store, fn_pos);
            found_calls = countTagInRange(store, span_range.start, span_range.end, .hir_call);
        }
    }
    try std.testing.expect(found_calls >= 3);

    // `seed = 10`: `double_val(10) = 20`, `affine_step(20, 3, 7) = 67`, `scaler.apply(67, 5) = 273`:
    const actual_val = try evalSourceFnI64(
        std.testing.allocator,
        pipe_src,
        TargetLayout.NATIVE_64,
        "run_pipes",
        &[_]mir_vm.RegSlot{.{ .scalar_i64 = 10 }},
        10_000,
    );
    try std.testing.expectEqual(@as(i64, 273), actual_val);
}

// Rule 2 & Rule 3: Postfix `?` (`@from` upcast + `explicit_err`) and `catch`:

test "test_hir_desugar_try_operator_from_upcast_and_catch_expressions" {
    const err_src =
        "pub struct IoError {\n" ++
        "    pub code: i32,\n" ++
        "}\n" ++
        "pub enum AppError {\n" ++
        "    @from Io(IoError),\n" ++
        "    Invalid,\n" ++
        "}\n" ++
        "pub fn read_port(is_ok: bool) -> Result[i32, IoError] {\n" ++
        "    if is_ok {\n" ++
        "        return .Ok(25);\n" ++
        "    }\n" ++
        "    return .Err(IoError { code: 404 });\n" ++
        "}\n" ++
        "pub fn lift_port(is_ok: bool) -> Result[i32, AppError] {\n" ++
        "    let port_val = read_port(is_ok)?;\n" ++
        "    return .Ok(port_val + 5);\n" ++
        "}\n" ++
        "pub fn propagate_opt(opt_in: i32?) -> i32? {\n" ++
        "    let inner = opt_in?;\n" ++
        "    return .Some(inner * 2);\n" ++
        "}\n" ++
        "pub fn eval_try_and_catch(mode: i32) -> i32 {\n" ++
        "    if mode == 0 {\n" ++
        "        return lift_port(true) catch 900;\n" ++
        "    } else if mode == 1 {\n" ++
        "        return lift_port(false) catch |app_err| match app_err {\n" ++
        "            .Io(io_err) => io_err.code,\n" ++
        "            .Invalid => -1,\n" ++
        "        };\n" ++
        "    } else if mode == 2 {\n" ++
        "        let some_in: i32? = .Some(12);\n" ++
        "        return propagate_opt(some_in) catch 77;\n" ++
        "    }\n" ++
        "    let none_in: i32? = .None;\n" ++
        "    return propagate_opt(none_in) catch 77;\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        err_src,
        TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());

    // Verify synthetic `hir_return` inside `?` carries `ReturnErrorKind.explicit_err`:
    var has_explicit_err_return = false;
    var has_normal_return = false;
    const node_tags = bundle.hir_store.nodes.items(.tag);
    const node_data = bundle.hir_store.nodes.items(.data);
    for (node_tags, node_data) |node_tag, data_pair| {
        if (node_tag == .hir_return) {
            if (data_pair.rhs == @backingInt(ReturnErrorKind.explicit_err)) {
                has_explicit_err_return = true;
            } else if (data_pair.rhs == @backingInt(ReturnErrorKind.normal)) {
                has_normal_return = true;
            }
        }
    }
    try std.testing.expect(has_explicit_err_return);
    try std.testing.expect(has_normal_return);

    // Execute all 4 paths (`Ok`, `@from` upcast `Err -> Io(404)`, `Some`, `None`):
    try std.testing.expectEqual(
        @as(i64, 30),
        try evalSourceFnI64(
            std.testing.allocator,
            err_src,
            TargetLayout.NATIVE_64,
            "eval_try_and_catch",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 0 }},
            10_000,
        ),
    );
    try std.testing.expectEqual(
        @as(i64, 404),
        try evalSourceFnI64(
            std.testing.allocator,
            err_src,
            TargetLayout.NATIVE_64,
            "eval_try_and_catch",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 1 }},
            10_000,
        ),
    );
    try std.testing.expectEqual(
        @as(i64, 24),
        try evalSourceFnI64(
            std.testing.allocator,
            err_src,
            TargetLayout.NATIVE_64,
            "eval_try_and_catch",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 2 }},
            10_000,
        ),
    );
    try std.testing.expectEqual(
        @as(i64, 77),
        try evalSourceFnI64(
            std.testing.allocator,
            err_src,
            TargetLayout.NATIVE_64,
            "eval_try_and_catch",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 3 }},
            10_000,
        ),
    );
}

// Rule 4: `let … else`, `if let`, conjunctive `if expr is Pat and guard`, and `while is`:

test "test_hir_desugar_let_else_if_let_conjunctive_is_and_while_is" {
    const cond_src =
        "pub fn eval_patterns(seed: i32) -> i32 {\n" ++
        "    let opt_seed: i32? = if seed >= 0 { .Some(seed) } else { .None };\n" ++
        "    let .Some(base) = opt_seed else {\n" ++
        "        return -99;\n" ++
        "    };\n" ++
        "    var total: i32 = 0;\n" ++
        "    if let .Some(bonus) = opt_seed {\n" ++
        "        total += bonus;\n" ++
        "    }\n" ++
        "    if opt_seed is .Some(checked) and checked > 10 {\n" ++
        "        total += checked * 10;\n" ++
        "    }\n" ++
        "    var countdown: i32? = .Some(base);\n" ++
        "    while countdown is .Some(rem) and rem > 0 {\n" ++
        "        total += 1;\n" ++
        "        countdown = if rem > 1 { .Some(rem - 1) } else { .None };\n" ++
        "    }\n" ++
        "    return total;\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        cond_src,
        TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());
    try std.testing.expect(
        countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_match) >= 4,
    );
    try std.testing.expect(
        countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_loop) >= 1,
    );

    // Negative `seed = -1` diverges via `let … else` (`-99`):
    try std.testing.expectEqual(
        @as(i64, -99),
        try evalSourceFnI64(
            std.testing.allocator,
            cond_src,
            TargetLayout.NATIVE_64,
            "eval_patterns",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = -1 }},
            10_000,
        ),
    );
    // `seed = 4`: `bonus = 4`, `checked > 10` is false, `while` runs 4 times -> `8`:
    try std.testing.expectEqual(
        @as(i64, 8),
        try evalSourceFnI64(
            std.testing.allocator,
            cond_src,
            TargetLayout.NATIVE_64,
            "eval_patterns",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 4 }},
            10_000,
        ),
    );
    // `seed = 12`: `bonus = 12`, `checked * 10 = 120`, `while` runs 12 times -> `144`:
    try std.testing.expectEqual(
        @as(i64, 144),
        try evalSourceFnI64(
            std.testing.allocator,
            cond_src,
            TargetLayout.NATIVE_64,
            "eval_patterns",
            &[_]mir_vm.RegSlot{.{ .scalar_i64 = 12 }},
            10_000,
        ),
    );
}

// Rule 5: `while` & `for` (`0..n`, `0u8..=255u8` overflow-free, `continue` step, `soa_zip`):

test "test_hir_desugar_while_for_inclusive_u8_continue_and_soa_zip" {
    const loop_src =
        "pub fn sum_inclusive_u8_and_continue() -> i32 {\n" ++
        "    var u8_sum: i32 = 0;\n" ++
        "    let low_byte: u8 = 0;\n" ++
        "    let high_byte: u8 = 255;\n" ++
        "    for byte_val in low_byte..=high_byte {\n" ++
        "        u8_sum += byte_val as i32;\n" ++
        "    }\n" ++
        "    var odd_sum: i32 = 0;\n" ++
        "    let start_i: i32 = 0;\n" ++
        "    let end_i: i32 = 6;\n" ++
        "    for idx in start_i..end_i {\n" ++
        "        if idx % 2 == 0 {\n" ++
        "            continue;\n" ++
        "        }\n" ++
        "        odd_sum += idx;\n" ++
        "    }\n" ++
        "    var countdown: i32 = 3;\n" ++
        "    while countdown > 0 {\n" ++
        "        odd_sum += countdown;\n" ++
        "        countdown -= 1;\n" ++
        "    }\n" ++
        "    return u8_sum + odd_sum;\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        loop_src,
        TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());
    try std.testing.expect(
        countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_continue) >= 1,
    );

    // Inclusive `0u8..=255u8` synthesizes a `bool` `_is_done` temp local (`DR-13` §2.2 Rule 5):
    var has_done_bool_temp = false;
    for (bundle.hir_store.locals.items) |loc_meta| {
        if (loc_meta.is_temp and loc_meta.type_id == .bool_ty) {
            has_done_bool_temp = true;
            break;
        }
    }
    try std.testing.expect(has_done_bool_temp);

    // `0..=255` sums to `32640` (terminates cleanly!), `odd_sum = 1+3+5 = 9`, `while = 3+2+1 = 6` -> `32655`:
    const actual_sum = try evalSourceFnI64(
        std.testing.allocator,
        loop_src,
        TargetLayout.NATIVE_64,
        "sum_inclusive_u8_and_continue",
        &.{},
        50_000,
    );
    try std.testing.expectEqual(@as(i64, 32655), actual_sum);

    // Verify `zip_soa_columns` emits zero AoS `hir_construct` temporaries (`DR-13` §2.2 Rule 5):
    const zip_src =
        "pub fn zip_soa_columns(left: [i32], right: [i32]) -> i32 {\n" ++
        "    var dot_acc: i32 = 0;\n" ++
        "    for pair in soa_zip(px: left, py: right) {\n" ++
        "        dot_acc += pair.px + pair.1;\n" ++
        "    }\n" ++
        "    return dot_acc;\n" ++
        "}\n";
    var zip_bundle = try lowerResolvedAstToHir(std.testing.allocator, zip_src);
    defer zip_bundle.deinit();
    try std.testing.expect(!zip_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(
        @as(usize, 0),
        countTagInRange(&zip_bundle.hir_store, 0, zip_bundle.hir_store.countNodes(), .hir_construct),
    );
    try std.testing.expect(
        countTagInRange(
            &zip_bundle.hir_store,
            0,
            zip_bundle.hir_store.countNodes(),
            .hir_index_proj,
        ) >= 2,
    );
}

// Rule 6 & Rule 7: `#soa` field projection inversion and LSB-first `bit_field` RMW:

test "test_hir_desugar_soa_projection_inversion_and_lsb_bitfield_rmw" {
    const soa_bf_src =
        "pub struct Particle {\n" ++
        "    pub vx: i32,\n" ++
        "    pub vy: i32,\n" ++
        "}\n" ++
        "pub bit_field PacketCtrl : u16 {\n" ++
        "    pub is_valid: bool | 1,\n" ++
        "    pub delta: i8 | 4,\n" ++
        "    pub seq: u16 | 11,\n" ++
        "}\n" ++
        "pub fn read_elem_style(items: #soa [Particle; 4], idx: usize) -> i32 {\n" ++
        "    return items[idx].vy;\n" ++
        "}\n" ++
        "pub fn read_col_style(items: #soa [Particle; 4], idx: usize) -> i32 {\n" ++
        "    return items.vy[idx];\n" ++
        "}\n" ++
        "pub fn bump_trace(log: &mut i32, digit: i32, ret_idx: usize) -> usize {\n" ++
        "    *log = *log * 10 + digit;\n" ++
        "    return ret_idx;\n" ++
        "}\n" ++
        "pub fn eval_bitfield_order_and_sign() -> i32 {\n" ++
        "    var slots: [PacketCtrl; 2] = [\n" ++
        "        PacketCtrl { is_valid: true, delta: -3, seq: 10 },\n" ++
        "        PacketCtrl { is_valid: false, delta: 2, seq: 5 },\n" ++
        "    ];\n" ++
        "    slots[0].is_valid = true;\n" ++
        "    slots[0].delta = -3;\n" ++
        "    slots[0].seq = 10;\n" ++
        "    var order_log: i32 = 0;\n" ++
        "    slots[bump_trace(&mut order_log, 2, 0)].seq +=\n" ++
        "        bump_trace(&mut order_log, 1, 7) as u16;\n" ++
        "    let signed_delta = slots[0].delta as i32;\n" ++
        "    let updated_seq = slots[0].seq as i32;\n" ++
        "    return order_log * 1000 + updated_seq * 10 + (signed_delta + 10);\n" ++
        "}\n";

    // Check both `NATIVE_64` and `WASM32` layouts for identical `hir_soa_field_ptr` inversion:
    const layouts = [_]TargetLayout{ TargetLayout.NATIVE_64, TargetLayout.WASM32 };
    for (layouts) |layout| {
        var bundle = try hir.lowerSourceToHir(std.testing.allocator, soa_bf_src, layout);
        defer bundle.deinit();
        try std.testing.expect(!bundle.diagnostics.hasErrors());

        var soa_ordinals: [2]u32 = .{ 999, 888 };
        var found_soa_ptrs: usize = 0;
        const tags = bundle.hir_store.nodes.items(.tag);
        const data_items = bundle.hir_store.nodes.items(.data);
        for (tags, data_items) |tag, data_pair| {
            if (tag == .hir_soa_field_ptr and found_soa_ptrs < 2) {
                soa_ordinals[found_soa_ptrs] = bundle.hir_store.extra_data.items[data_pair.rhs];
                found_soa_ptrs += 1;
            }
        }
        try std.testing.expectEqual(@as(usize, 2), found_soa_ptrs);
        try std.testing.expectEqual(@as(u32, 1), soa_ordinals[0]);
        try std.testing.expectEqual(soa_ordinals[0], soa_ordinals[1]);

        try std.testing.expect(
            countTagInRange(
                &bundle.hir_store,
                0,
                bundle.hir_store.countNodes(),
                .hir_bitfield_read,
            ) >= 2,
        );
        try std.testing.expect(
            countTagInRange(
                &bundle.hir_store,
                0,
                bundle.hir_store.countNodes(),
                .hir_bitfield_rmw,
            ) >= 1,
        );
    }

    // RHS (`1`) runs BEFORE LHS (`2`) -> `order_log = 12`, `seq = 17`, `signed_delta = -3` -> `12177`:
    const actual_bf = try evalSourceFnI64(
        std.testing.allocator,
        soa_bf_src,
        TargetLayout.NATIVE_64,
        "eval_bitfield_order_and_sign",
        &.{},
        10_000,
    );
    try std.testing.expectEqual(@as(i64, 12177), actual_bf);
}

test "test_hir_bit_field_literal_initialization_without_error_hole" {
    const bf_lit_src =
        "pub bit_field HeaderFlags : u16 {\n" ++
        "    pub is_live: bool | 1,\n" ++
        "    pub delta: i8 | 4,\n" ++
        "    pub seq: u16 | 11,\n" ++
        "}\n" ++
        "pub fn eval_bf_lit() -> i32 {\n" ++
        "    let flags = HeaderFlags { seq: 14, delta: -5, is_live: true };\n" ++
        "    let live_bit: i32 = if flags.is_live { 1 } else { 0 };\n" ++
        "    return live_bit * 1000 + (flags.seq as i32) * 10 + ((flags.delta as i32) + 10);\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(std.testing.allocator, bf_lit_src, TargetLayout.NATIVE_64);
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(
        @as(usize, 0),
        countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_error_hole),
    );

    const actual_val = try evalSourceFnI64(
        std.testing.allocator,
        bf_lit_src,
        TargetLayout.NATIVE_64,
        "eval_bf_lit",
        &.{},
        10_000,
    );
    try std.testing.expectEqual(@as(i64, 1145), actual_val);
}

// Rule 8 & Rule 9: `@overload` specificity, operator trait `&self` auto-ref, `@derive`, `@attribute_schema`:

test "test_hir_desugar_overload_operator_autoref_two_phase_derive_and_attr_schema" {
    const trait_src =
        "@attribute_schema(targets = [.StructField])\n" ++
        "pub struct WireTag {\n" ++
        "    pub tag_num: i32 = 0,\n" ++
        "}\n" ++
        "@derive(Eq, Hash, Debug, Clone)\n" ++
        "pub struct Point2D {\n" ++
        "    @WireTag(tag_num = 9)\n" ++
        "    pub px: i32,\n" ++
        "    pub py: i32,\n" ++
        "}\n" ++
        "@overload\n" ++
        "pub fn rank_number(val: Float) -> i32 {\n" ++
        "    let _keep = val;\n" ++
        "    return 30;\n" ++
        "}\n" ++
        "@overload\n" ++
        "pub fn rank_number(val: Signed) -> i32 {\n" ++
        "    let _keep = val;\n" ++
        "    return 20;\n" ++
        "}\n" ++
        "@overload\n" ++
        "pub fn rank_number(val: i32) -> i32 {\n" ++
        "    return val + 1;\n" ++
        "}\n" ++
        "pub fn exercise_overload_derive_and_schema() -> i32 {\n" ++
        "    let v_i32: i32 = 9;\n" ++
        "    let v_i64: i64 = 9;\n" ++
        "    let v_f64: f64 = 1.5;\n" ++
        "    let exact_i32 = rank_number(v_i32);\n" ++
        "    let signed_i64 = rank_number(v_i64);\n" ++
        "    let float_num = rank_number(v_f64);\n" ++
        "    let p_one = Point2D { px: 4, py: 8 };\n" ++
        "    let p_two = p_one.clone();\n" ++
        "    let p_diff = Point2D { px: 4, py: 9 };\n" ++
        "    let eq_score: i32 = if p_one == p_two and p_one != p_diff { 100 } else { 0 };\n" ++
        "    let hash_ok: i32 = if p_one.hash() == p_two.hash() { 5 } else { 0 };\n" ++
        "    let meta_opt: WireTag? = comptime @field_attr_lookup[WireTag](\n" ++
        "        @type_info[Point2D]().id,\n" ++
        "        0,\n" ++
        "    );\n" ++
        "    let meta_val: i32 = match meta_opt {\n" ++
        "        .Some(tag_meta) => tag_meta.tag_num,\n" ++
        "        .None => 0,\n" ++
        "    };\n" ++
        "    return exact_i32 + signed_i64 + float_num + eq_score + hash_ok + meta_val;\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        trait_src,
        TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());

    // Verify synthesized `@derive` bodies (`eq`, `hash`, `debug`, `clone`) were lowered:
    try std.testing.expect(findFnMetaByName(&bundle.hir_store, &bundle.interner, "eq") != null);
    try std.testing.expect(findFnMetaByName(&bundle.hir_store, &bundle.interner, "hash") != null);
    try std.testing.expect(findFnMetaByName(&bundle.hir_store, &bundle.interner, "clone") != null);
    try std.testing.expect(
        findFnMetaByName(&bundle.hir_store, &bundle.interner, "debug") != null or
            findFnMetaByName(&bundle.hir_store, &bundle.interner, "debug_fmt") != null,
    );

    // Verify `p_one == p_two` and `p_one != p_diff` emitted synthetic `&self` `addr_of` nodes:
    var addr_of_count: usize = 0;
    const tags = bundle.hir_store.nodes.items(.tag);
    const data_items = bundle.hir_store.nodes.items(.data);
    for (tags, data_items) |tag, data_pair| {
        if (tag == .hir_unary_op and data_pair.lhs == @backingInt(HirUnaryOp.addr_of)) {
            addr_of_count += 1;
        }
    }
    try std.testing.expect(addr_of_count >= 4);

    // `10 + 20 + 30 + 100 + 5 + 9 = 174`:
    const actual_total = try evalSourceFnI64(
        std.testing.allocator,
        trait_src,
        TargetLayout.NATIVE_64,
        "exercise_overload_derive_and_schema",
        &.{},
        20_000,
    );
    try std.testing.expectEqual(@as(i64, 174), actual_total);
}

// Rule 10: `comptime if`, `comptime match`, `comptime for` unrolling, `E0503`, and `MAX_UNROLL` `E0501`:

test "test_hir_desugar_comptime_if_match_for_unroll_and_limit_diagnostics" {
    // [1] Positive static unrolling (`comptime if`, `comptime match`, `comptime for` + `continue`/`break`):
    {
        const unroll_src =
            "pub const MODE_TAG: i32 = 2;\n" ++
            "pub fn unrolled_kernel() -> i32 {\n" ++
            "    let branch_base: i32 = comptime if MODE_TAG == 2 { 100 } else { 0 };\n" ++
            "    let match_bonus: i32 = comptime match MODE_TAG {\n" ++
            "        1 => 10,\n" ++
            "        2 => 20,\n" ++
            "        _ => 30,\n" ++
            "    };\n" ++
            "    var loop_acc: i32 = 0;\n" ++
            "    comptime for step in 0..8 {\n" ++
            "        comptime if step == 1 {\n" ++
            "            continue;\n" ++
            "        }\n" ++
            "        comptime if step == 5 {\n" ++
            "            break;\n" ++
            "        }\n" ++
            "        loop_acc += step;\n" ++
            "    }\n" ++
            "    return branch_base + match_bonus + loop_acc;\n" ++
            "}\n";

        var bundle = try hir.lowerSourceToHir(
            std.testing.allocator,
            unroll_src,
            TargetLayout.NATIVE_64,
        );
        defer bundle.deinit();
        try std.testing.expect(!bundle.diagnostics.hasErrors());
        // Zero runtime `hir_loop` or `hir_match` nodes remain after static unrolling:
        try std.testing.expectEqual(
            @as(usize, 0),
            countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_loop),
        );
        try std.testing.expectEqual(
            @as(usize, 0),
            countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_match),
        );

        // `100 + 20 + (0 + 2 + 3 + 4) = 129`:
        const actual = try evalSourceFnI64(
            std.testing.allocator,
            unroll_src,
            TargetLayout.NATIVE_64,
            "unrolled_kernel",
            &.{},
            5_000,
        );
        try std.testing.expectEqual(@as(i64, 129), actual);
    }

    // [2] Negative: exceeding `MAX_UNROLL` (`4096`) emits `E0501`:
    {
        const over_unroll_src =
            "pub fn too_many_unrolls() -> i32 {\n" ++
            "    var acc: i32 = 0;\n" ++
            "    comptime for idx in 0..4100 {\n" ++
            "        acc += idx;\n" ++
            "    }\n" ++
            "    return acc;\n" ++
            "}\n";

        var bundle = try hir.lowerSourceToHir(
            std.testing.allocator,
            over_unroll_src,
            TargetLayout.NATIVE_64,
        );
        defer bundle.deinit();
        try std.testing.expect(
            hasDiag(&bundle.diagnostics, .e0501_comptime_step_limit_exceeded),
        );
    }

    // [3] Negative: runtime-conditioned `break` inside `comptime for` emits `E0503`:
    {
        const runtime_break_src =
            "pub fn bad_comptime_break(flag: bool) -> i32 {\n" ++
            "    var acc: i32 = 0;\n" ++
            "    comptime for idx in 0..4 {\n" ++
            "        if flag {\n" ++
            "            break;\n" ++
            "        }\n" ++
            "        acc += idx;\n" ++
            "    }\n" ++
            "    return acc;\n" ++
            "}\n";

        var bundle = try hir.lowerSourceToHir(
            std.testing.allocator,
            runtime_break_src,
            TargetLayout.NATIVE_64,
        );
        defer bundle.deinit();
        try std.testing.expect(
            hasDiag(&bundle.diagnostics, .e0503_forbidden_comptime_operation),
        );
    }
}

// Rule 11 & Rule 12: String interpolation & Hylo post-argument callee sequencing (`DR-02` §2.2):

test "test_hir_desugar_string_interpolation_and_hylo_post_arg_sequencing" {
    const interp_seq_src =
        "pub struct IntBuf {\n" ++
        "    pub len_count: i32,\n" ++
        "    pub last_added: i32,\n" ++
        "}\n" ++
        "impl IntBuf {\n" ++
        "    pub fn cur_len(&self) -> i32 {\n" ++
        "        return self.len_count;\n" ++
        "    }\n" ++
        "    pub fn push_elem(&mut self, item: i32) -> () {\n" ++
        "        self.len_count += 1;\n" ++
        "        self.last_added = item;\n" ++
        "    }\n" ++
        "}\n" ++
        "pub struct AdderBox {\n" ++
        "    pub bias: i32,\n" ++
        "}\n" ++
        "impl AdderBox {\n" ++
        "    pub fn sum_with(&self, lhs: i32, rhs: i32) -> i32 {\n" ++
        "        return self.bias + lhs + rhs;\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn log_arg(trace: &mut i32, digit: i32, out_val: i32) -> i32 {\n" ++
        "    *trace = *trace * 10 + digit;\n" ++
        "    return out_val;\n" ++
        "}\n" ++
        "pub fn make_adder(trace: &mut i32, digit: i32) -> AdderBox {\n" ++
        "    *trace = *trace * 10 + digit;\n" ++
        "    return AdderBox { bias: 0 };\n" ++
        "}\n" ++
        "pub fn format_banner(label: str) -> str {\n" ++
        "    return \"hdr={label}:ok\";\n" ++
        "}\n" ++
        "pub fn run_hylo_order() -> i32 {\n" ++
        "    var trace: i32 = 0;\n" ++
        "    let sum = make_adder(&mut trace, 3).sum_with(\n" ++
        "        log_arg(&mut trace, 1, 10),\n" ++
        "        log_arg(&mut trace, 2, 20),\n" ++
        "    );\n" ++
        "    var buf = IntBuf { len_count: 7, last_added: 0 };\n" ++
        "    buf.push_elem(buf.cur_len());\n" ++
        "    let banner_len = format_banner(\"v5\").len() as i32;\n" ++
        "    return trace * 100 + sum + buf.last_added + banner_len;\n" ++
        "}\n";

    var bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        interp_seq_src,
        TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.diagnostics.hasErrors());

    // String interpolation lowers into `hir_construct` / `hir_intrinsic_call` without errors:
    try std.testing.expect(
        countTagInRange(&bundle.hir_store, 0, bundle.hir_store.countNodes(), .hir_construct) +
            countTagInRange(
                &bundle.hir_store,
                0,
                bundle.hir_store.countNodes(),
                .hir_intrinsic_call,
            ) >= 1,
    );

    // Args (`1`, `2`) run BEFORE receiver (`3`) -> `trace = 123`, `sum = 30`, `last = 7`, `len = 9`:
    const actual_order = try evalSourceFnI64(
        std.testing.allocator,
        interp_seq_src,
        TargetLayout.NATIVE_64,
        "run_hylo_order",
        &.{},
        15_000,
    );
    try std.testing.expectEqual(@as(i64, 12346), actual_order);
}

// Deterministic `renderHir` & isolated per-`DefId` `lowerDefToHir`:

test "test_hir_deterministic_render_and_isolated_lower_def_to_hir" {
    const sample_src =
        "pub fn helper_one(val: usize) -> usize {\n" ++
        "    return val + @size_of[usize]();\n" ++
        "}\n" ++
        "pub fn helper_two(val: usize) -> usize {\n" ++
        "    return helper_one(val) * 2;\n" ++
        "}\n";

    // [1] `NATIVE_64` vs `WASM32` `@size_of[usize]()` target layout sensitivity + deterministic render:
    var native_b1 = try hir.lowerSourceToHir(
        std.testing.allocator,
        sample_src,
        TargetLayout.NATIVE_64,
    );
    defer native_b1.deinit();
    var native_b2 = try hir.lowerSourceToHir(
        std.testing.allocator,
        sample_src,
        TargetLayout.NATIVE_64,
    );
    defer native_b2.deinit();
    var wasm_bundle = try hir.lowerSourceToHir(
        std.testing.allocator,
        sample_src,
        TargetLayout.WASM32,
    );
    defer wasm_bundle.deinit();

    const dump_one = try hir.renderHir(
        std.testing.allocator,
        &native_b1.hir_store,
        &native_b1.pool,
        &native_b1.sym_table,
        &native_b1.interner,
    );
    defer std.testing.allocator.free(dump_one);

    const dump_two = try hir.renderHir(
        std.testing.allocator,
        &native_b2.hir_store,
        &native_b2.pool,
        &native_b2.sym_table,
        &native_b2.interner,
    );
    defer std.testing.allocator.free(dump_two);

    const wasm_dump = try hir.renderHir(
        std.testing.allocator,
        &wasm_bundle.hir_store,
        &wasm_bundle.pool,
        &wasm_bundle.sym_table,
        &wasm_bundle.interner,
    );
    defer std.testing.allocator.free(wasm_dump);

    try std.testing.expectEqualStrings(dump_one, dump_two);
    try std.testing.expect(!std.mem.eql(u8, dump_one, wasm_dump));

    // [2] Isolated per-`DefId` `lowerDefToHir` produces only the requested `DefId` cleanly:
    const target_def = native_b1.hir_store.functions.items[1].def_id;
    var single_diag = DiagnosticSink.init(std.testing.allocator);
    defer single_diag.deinit();
    var single_store = try hir.lowerDefToHir(
        std.testing.allocator,
        target_def,
        sample_src,
        &native_b1.tokens,
        &native_b1.cst_arena,
        &native_b1.ast_arena,
        &native_b1.interner,
        &native_b1.pool,
        &native_b1.sym_table,
        &native_b1.side_tables,
        &single_diag,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer single_store.deinit();

    try std.testing.expect(!single_diag.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), single_store.functions.items.len);
    try std.testing.expectEqual(target_def, single_store.functions.items[0].def_id);
}

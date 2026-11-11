//! Unit Tests for Sandboxed Compile-Time `MIR` Virtual Machine (`mir_vm.zig`)
//!
//! Covers 4B/8B handle and register slot layouts, disjoint 2-bit `ComptimeAllocId` domains,
//! 3-way `VmValueRepr` execution (`inline_scalar`, `inline_ptr`, `by_value_snapshot`), all
//! `comptime` diagnostics (`E0501`–`E0510`) with multi-frame `LabeledSpan` stack traces,
//! all 9 `DR-05` reflection intrinsics across `NATIVE_64` and `WASM32` layouts, and bounded
//! `PureCallMemoCache` + `RodataPool` deduplication.

const std = @import("std");
const corex = @import("corex");

const hir = corex.hir;
const mir = corex.mir;
const mir_vm = corex.mir_vm;
const query_db = corex.query_db;
const type_system = corex.type_system;
const symbol_resolver = corex.symbol_resolver;
const diagnostic = corex.diagnostic;

const AllocDomain = mir_vm.AllocDomain;
const ComptimeAllocId = mir_vm.ComptimeAllocId;
const SymbolicPtr = mir_vm.SymbolicPtr;
const RegSlot = mir_vm.RegSlot;
const ProvenanceEntry = mir_vm.ProvenanceEntry;
const VmValueRepr = mir_vm.VmValueRepr;
const RodataPool = mir_vm.RodataPool;
const PureCallMemoCache = mir_vm.PureCallMemoCache;
const MirVm = mir_vm.MirVm;
const VmExecOptions = mir_vm.VmExecOptions;
const MirBody = mir.MirBody;
const MirSsaBuilder = mir.MirSsaBuilder;
const LocalDecl = mir.LocalDecl;
const LocalId = mir.LocalId;
const PlaceId = mir.PlaceId;
const TargetLayout = type_system.TargetLayout;
const TypeId = corex.TypeId;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const FileId = corex.FileId;
const DefId = corex.DefId;
const TokenIndex = corex.TokenIndex;
const Span = corex.Span;
const SymbolId = corex.SymbolId;

// -------------------------------------- INTERNALS --------------------------------------

/// Checks whether `sink` contains at least one diagnostic matching `expected_code`.
fn hasDiag(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Checks whether `sink` recorded `expected_code` with a secondary `"called at `comptime` from"` frame label.
fn hasDiagWithStackTrace(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code != expected_code) continue;
        for (diag_item.labels) |lbl| {
            if (lbl.style == .secondary and
                std.mem.indexOf(u8, lbl.label, "called at `comptime` from") != null)
            {
                return true;
            }
        }
    }
    return false;
}

/// Registers every lowered `MirBody` inside `bundle` on `vm_engine`.
fn registerAllBodies(vm_engine: *MirVm, bundle: *mir.MirSourceBundle) !void {
    for (bundle.mir_bundle.bodies.items) |*body_ptr| {
        var sym_idx = bundle.hir_bundle.sym_table.def_to_symbol.get(
            body_ptr.def_id.asInt(),
        ) orelse symbol_resolver.SymbolIndex.none;
        if (sym_idx.isNone()) {
            for (bundle.hir_bundle.hir_store.functions.items) |fn_meta| {
                if (fn_meta.name == body_ptr.name and !fn_meta.symbol_index.isNone()) {
                    sym_idx = fn_meta.symbol_index;
                    break;
                }
            }
        }
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
    }
}

/// Appends a `LocalDecl` to `body` and returns its `LocalId`.
fn addTestLocal(body: *MirBody, decl: LocalDecl) !LocalId {
    const idx: u32 = @intCast(body.locals.items.len);
    try body.locals.append(body.allocator, decl);
    return LocalId.fromInt(idx);
}

/// Appends a `MirPlace` to `body` and returns its `PlaceId`.
fn addTestPlace(
    body: *MirBody,
    base_loc: LocalId,
    projs: []const mir.MirProjection,
) !PlaceId {
    const start_off: u24 = @intCast(body.projections.items.len);
    if (projs.len > 0) {
        try body.projections.appendSlice(body.allocator, projs);
    }
    const idx: u32 = @intCast(body.places.items.len);
    try body.places.append(body.allocator, .{
        .base = base_loc.asInt(),
        .proj_start = start_off,
        .proj_len = @intCast(projs.len),
    });
    return PlaceId.fromInt(idx);
}

// ------------------------------------- PUBLIC API --------------------------------------

// Exact handle/slot byte layouts and disjoint 2-bit `ComptimeAllocId` domains:

test "test_mir_vm_handle_and_slot_byte_layouts_and_disjoint_alloc_domains" {
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(ComptimeAllocId));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(SymbolicPtr));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(RegSlot));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(ProvenanceEntry));

    // Disjoint 2-bit MSB domains (`0b00` vm_alloc, `0b01` rodata_blob, `0b10` string_lit, `0b11` fn_or_none):
    const vm_id = ComptimeAllocId.fromVmIndex(7);
    const rodata_id = ComptimeAllocId.fromRodataIndex(7);
    const str_id = ComptimeAllocId.fromStringId(SymbolId.fromInt(7));
    const fn_id = ComptimeAllocId.fromFnIndex(7);

    try std.testing.expectEqual(AllocDomain.vm_alloc, vm_id.domain());
    try std.testing.expectEqual(AllocDomain.rodata_blob, rodata_id.domain());
    try std.testing.expectEqual(AllocDomain.string_lit, str_id.domain());
    try std.testing.expectEqual(AllocDomain.fn_or_none, fn_id.domain());

    try std.testing.expectEqual(@as(u32, 7), vm_id.payloadIndex());
    try std.testing.expectEqual(@as(u32, 7), rodata_id.payloadIndex());
    try std.testing.expectEqual(@as(u32, 7), str_id.payloadIndex());
    try std.testing.expectEqual(@as(u32, 7), fn_id.payloadIndex());

    try std.testing.expect(vm_id != rodata_id and rodata_id != str_id and str_id != fn_id);
    try std.testing.expect(ComptimeAllocId.null_ptr.isNullOrNone());
    try std.testing.expect(ComptimeAllocId.none.isNullOrNone());
    try std.testing.expect(fn_id.isFnAddr());
    try std.testing.expect(!ComptimeAllocId.none.isFnAddr());
}

// 3-way `VmValueRepr` classification & execution (`inline_scalar`, `inline_ptr`, `by_value_snapshot`):

test "test_mir_vm_three_way_value_repr_execution_across_all_types" {
    const repr_src =
        "pub struct SampleNode {\n" ++
        "    pub weight: i64,\n" ++
        "    pub tag: u32,\n" ++
        "}\n" ++
        "pub enum SampleOpt {\n" ++
        "    Empty,\n" ++
        "    Wide(u128),\n" ++
        "}\n" ++
        "pub bit_field CompactFlags : u16 {\n" ++
        "    pub is_live: bool | 1,\n" ++
        "    pub code: u16 | 15,\n" ++
        "}\n" ++
        "pub bit_field WideFlags : u128 {\n" ++
        "    pub low_half: u64 | 64,\n" ++
        "    pub high_half: u64 | 64,\n" ++
        "}\n" ++
        "pub fn make_wide_u128(seed: u128) -> u128 {\n" ++
        "    let shift_bits: u128 = 64;\n" ++
        "    let low_tag: u128 = 99;\n" ++
        "    return (seed << shift_bits) | low_tag;\n" ++
        "}\n" ++
        "pub fn read_ptr_val(ptr_in: &i64) -> i64 {\n" ++
        "    return *ptr_in;\n" ++
        "}\n" ++
        "pub fn read_slice_head(items: [i64]) -> i64 {\n" ++
        "    return items[0];\n" ++
        "}\n" ++
        "pub fn run_all_reprs() -> i64 {\n" ++
        "    let seed_wide: u128 = 3;\n" ++
        "    let shift_bits: u128 = 64;\n" ++
        "    let low_mask: u128 = 255;\n" ++
        "    let big_val = make_wide_u128(seed_wide);\n" ++
        "    let wrapped: SampleOpt = .Wide(big_val);\n" ++
        "    let high_part: i64 = match wrapped {\n" ++
        "        .Empty => 0,\n" ++
        "        .Wide(payload) => ((payload >> shift_bits) as i64) + ((payload & low_mask) as i64),\n" ++
        "    };\n" ++
        "    let tup: (i64, str) = (11, \"corex\");\n" ++
        "    var soa_arr: #soa [SampleNode; 2] = @default_init[#soa [SampleNode; 2]]();\n" ++
        "    soa_arr[0].weight = 20;\n" ++
        "    soa_arr[0].tag = 1;\n" ++
        "    soa_arr[1].weight = 30;\n" ++
        "    soa_arr[1].tag = 2;\n" ++
        "    soa_arr.weight[1] += 5;\n" ++
        "    var compact = CompactFlags { is_live: true, code: 12 };\n" ++
        "    compact.is_live = true;\n" ++
        "    compact.code = 12;\n" ++
        "    var wide_bf = WideFlags { low_half: 4, high_half: 8 };\n" ++
        "    wide_bf.low_half = 4;\n" ++
        "    wide_bf.high_half = 8;\n" ++
        "    let local_num: i64 = 7;\n" ++
        "    let via_ref = read_ptr_val(&local_num);\n" ++
        "    let fixed_i64: [i64; 2] = [6, 9];\n" ++
        "    let slice_first = read_slice_head(&fixed_i64);\n" ++
        "    return high_part + tup.0 + soa_arr[1].weight + (compact.code as i64) +\n" ++
        "        (wide_bf.high_half as i64) + via_ref + slice_first + (tup.1.len as i64);\n" ++
        "}\n";

    const layouts = [_]TargetLayout{ TargetLayout.NATIVE_64, TargetLayout.WASM32 };
    for (layouts) |layout| {
        var bundle = try mir.lowerSourceToMir(
            std.testing.allocator,
            FileId.fromInt(1),
            repr_src,
            layout,
            .{},
        );
        defer bundle.deinit();
        try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

        const pool = &bundle.hir_bundle.pool;
        const sym_table = &bundle.hir_bundle.sym_table;
        const ref_i64 = try pool.internRef(.i64_ty, false);
        const slice_u8 = try pool.internSlice(.u8_ty, false);

        try std.testing.expectEqual(
            VmValueRepr.inline_scalar,
            mir_vm.classifyValueRepr(pool, sym_table, .i64_ty, layout),
        );
        try std.testing.expectEqual(
            VmValueRepr.inline_scalar,
            mir_vm.classifyValueRepr(pool, sym_table, .usize_ty, layout),
        );
        try std.testing.expectEqual(
            VmValueRepr.inline_ptr,
            mir_vm.classifyValueRepr(pool, sym_table, ref_i64, layout),
        );
        try std.testing.expectEqual(
            VmValueRepr.by_value_snapshot,
            mir_vm.classifyValueRepr(pool, sym_table, .u128_ty, layout),
        );
        try std.testing.expectEqual(
            VmValueRepr.by_value_snapshot,
            mir_vm.classifyValueRepr(pool, sym_table, .i128_ty, layout),
        );
        try std.testing.expectEqual(
            VmValueRepr.by_value_snapshot,
            mir_vm.classifyValueRepr(pool, sym_table, .str_ty, layout),
        );
        try std.testing.expectEqual(
            VmValueRepr.by_value_snapshot,
            mir_vm.classifyValueRepr(pool, sym_table, slice_u8, layout),
        );

        var rodata_pool = RodataPool.init(std.testing.allocator);
        defer rodata_pool.deinit();
        var vm_engine = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            pool,
            sym_table,
            &rodata_pool,
            null,
            &bundle.hir_bundle.diagnostics,
            .{ .target_layout = layout },
        );
        defer vm_engine.deinit();
        try registerAllBodies(&vm_engine, &bundle);

        const wide_body = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "make_wide_u128",
        ).?;
        try std.testing.expectEqual(
            VmValueRepr.by_value_snapshot,
            mir_vm.classifyValueRepr(pool, sym_table, wide_body.ret_ty, layout),
        );

        const entry_body = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "run_all_reprs",
        ).?;
        const eval_res = try vm_engine.evalBody(entry_body, &.{});
        // `(3 + 99) + 11 + 35 + 12 + 8 + 7 + 6 + 5 = 186`:
        try std.testing.expectEqual(@as(i64, 186), eval_res.slot.scalar_i64);
    }
}

// `E0501` (loop + repeat array), `E0502` (overflow/shift/neg), `E0507` (div/rem 0), `E0510` (`@compile_assert`/`@compile_error`):

test "test_mir_vm_comptime_diagnostics_e0501_e0502_e0507_and_e0510_with_stack_traces" {
    const trap_src =
        "pub fn spin_callee(seed: i64) -> i64 {\n" ++
        "    var cur: i64 = seed;\n" ++
        "    while cur > 0 {\n" ++
        "        cur += 1;\n" ++
        "    }\n" ++
        "    return cur;\n" ++
        "}\n" ++
        "pub fn spin_caller() -> i64 {\n" ++
        "    return spin_callee(1);\n" ++
        "}\n" ++
        "pub fn repeat_callee() -> u8 {\n" ++
        "    let big_arr: [u8; 4096] = [7u8; 4096];\n" ++
        "    return big_arr[0];\n" ++
        "}\n" ++
        "pub fn repeat_caller() -> u8 {\n" ++
        "    return repeat_callee();\n" ++
        "}\n" ++
        "pub fn overflow_callee(mode: i32, byte_in: i8, shift_amt: u32) -> i32 {\n" ++
        "    if mode == 0 {\n" ++
        "        return (byte_in + 1i8) as i32;\n" ++
        "    } else if mode == 1 {\n" ++
        "        return (1u32 << shift_amt) as i32;\n" ++
        "    }\n" ++
        "    return (-byte_in) as i32;\n" ++
        "}\n" ++
        "pub fn overflow_caller(mode: i32, byte_in: i8, shift_amt: u32) -> i32 {\n" ++
        "    return overflow_callee(mode, byte_in, shift_amt);\n" ++
        "}\n" ++
        "pub fn div_rem_callee(is_rem: bool, num: i64, den: i64) -> i64 {\n" ++
        "    if is_rem {\n" ++
        "        return num % den;\n" ++
        "    }\n" ++
        "    return num / den;\n" ++
        "}\n" ++
        "pub fn div_rem_caller(is_rem: bool, num: i64, den: i64) -> i64 {\n" ++
        "    return div_rem_callee(is_rem, num, den);\n" ++
        "}\n" ++
        "pub fn assert_callee(is_err_intr: bool, flag: bool) -> i32 {\n" ++
        "    if is_err_intr {\n" ++
        "        if !flag {\n" ++
        "            @compile_error(\"explicit user error\");\n" ++
        "        }\n" ++
        "        return 1;\n" ++
        "    }\n" ++
        "    @compile_assert(flag, \"invariant violated\");\n" ++
        "    return 2;\n" ++
        "}\n" ++
        "pub fn assert_caller(is_err_intr: bool, flag: bool) -> i32 {\n" ++
        "    return assert_callee(is_err_intr, flag);\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        trap_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();

    // [1] `E0501` on unbounded loop AND large `[7u8; 4096]` repeat initialization (with stack trace!):
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        var vm_loop = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &sink,
            .{ .step_budget = 80 },
        );
        defer vm_loop.deinit();
        try registerAllBodies(&vm_loop, &bundle);

        const spin_caller = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "spin_caller",
        ).?;
        try std.testing.expectError(error.StepLimitExceeded, vm_loop.evalBody(spin_caller, &.{}));
        try std.testing.expect(hasDiagWithStackTrace(&sink, .e0501_comptime_step_limit_exceeded));

        var sink_rep = DiagnosticSink.init(std.testing.allocator);
        defer sink_rep.deinit();
        var vm_rep = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &sink_rep,
            .{ .step_budget = 100 },
        );
        defer vm_rep.deinit();
        try registerAllBodies(&vm_rep, &bundle);

        const rep_caller = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "repeat_caller",
        ).?;
        try std.testing.expectError(error.StepLimitExceeded, vm_rep.evalBody(rep_caller, &.{}));
        try std.testing.expect(
            hasDiagWithStackTrace(&sink_rep, .e0501_comptime_step_limit_exceeded),
        );
    }

    // [2] `E0502` on checked add (`127i8 + 1`), shift (`1u32 << 32`), and negation (`-(-128i8)`):
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        var vm_ovf = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &sink,
            .{},
        );
        defer vm_ovf.deinit();
        try registerAllBodies(&vm_ovf, &bundle);

        const ovf_caller = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "overflow_caller",
        ).?;
        try std.testing.expectError(
            error.IntegerOverflow,
            vm_ovf.evalBody(
                ovf_caller,
                &[_]RegSlot{ .{ .scalar_i64 = 0 }, .{ .scalar_i64 = 127 }, .{ .scalar_u64 = 1 } },
            ),
        );
        try std.testing.expectError(
            error.IntegerOverflow,
            vm_ovf.evalBody(
                ovf_caller,
                &[_]RegSlot{ .{ .scalar_i64 = 1 }, .{ .scalar_i64 = 0 }, .{ .scalar_u64 = 32 } },
            ),
        );
        try std.testing.expectError(
            error.IntegerOverflow,
            vm_ovf.evalBody(
                ovf_caller,
                &[_]RegSlot{ .{ .scalar_i64 = 2 }, .{ .scalar_i64 = -128 }, .{ .scalar_u64 = 1 } },
            ),
        );
        try std.testing.expect(hasDiagWithStackTrace(&sink, .e0502_integer_constant_overflow));
    }

    // [3] `E0507` on division/remainder by zero & `E0510` on `@compile_assert` / `@compile_error`:
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        var vm_trap = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &sink,
            .{},
        );
        defer vm_trap.deinit();
        try registerAllBodies(&vm_trap, &bundle);

        const div_caller = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "div_rem_caller",
        ).?;
        try std.testing.expectError(
            error.ArithmeticTrap,
            vm_trap.evalBody(
                div_caller,
                &[_]RegSlot{ .{ .scalar_u64 = 0 }, .{ .scalar_i64 = 9 }, .{ .scalar_i64 = 0 } },
            ),
        );
        try std.testing.expectError(
            error.ArithmeticTrap,
            vm_trap.evalBody(
                div_caller,
                &[_]RegSlot{ .{ .scalar_u64 = 1 }, .{ .scalar_i64 = 9 }, .{ .scalar_i64 = 0 } },
            ),
        );
        try std.testing.expect(hasDiagWithStackTrace(&sink, .e0507_comptime_arithmetic_trap));

        const assert_caller = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "assert_caller",
        ).?;
        try std.testing.expectError(
            error.CompileAssertionFailed,
            vm_trap.evalBody(
                assert_caller,
                &[_]RegSlot{ .{ .scalar_u64 = 0 }, .{ .scalar_u64 = 0 } },
            ),
        );
        try std.testing.expect(hasDiagWithStackTrace(&sink, .e0510_compile_assertion_failed));
    }
}

// `E0503` forbidden operations (`extern` FFI call, `ptr as usize` exposure, `@embed_bytes` path escapes):

test "test_mir_vm_comptime_diagnostics_e0503_ffi_ptr_cast_and_embed_escapes" {
    // [1] Path-traversal & Windows device-name sandbox predicate checks (`CON`, `NUL`, `../`, `C:\`):
    try std.testing.expect(mir_vm.isValidSandboxedEmbedPath("assets/shader.spv"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("../secret.key"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("/etc/passwd"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("C:\\Windows\\win.ini"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("CON"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("NUL"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("con.txt"));
    try std.testing.expect(!mir_vm.isValidSandboxedEmbedPath("sub/lpt1.log"));

    // [2] `extern` FFI call, `ptr as usize` cast, and escaping `@embed_bytes` inside `MirVm`:
    const ffi_src =
        "extern \"C\" {\n" ++
        "    pub fn host_random() -> i32;\n" ++
        "}\n" ++
        "pub fn call_ffi_inner() -> i32 {\n" ++
        "    return unsafe { host_random() };\n" ++
        "}\n" ++
        "pub fn call_ffi_outer() -> i32 {\n" ++
        "    return call_ffi_inner();\n" ++
        "}\n" ++
        "pub fn expose_ptr_inner(val_ref: &i32) -> usize {\n" ++
        "    return unsafe { (val_ref as *const i32) as usize };\n" ++
        "}\n" ++
        "pub fn expose_ptr_outer() -> usize {\n" ++
        "    let local_num: i32 = 5;\n" ++
        "    return expose_ptr_inner(&local_num);\n" ++
        "}\n" ++
        "pub fn bad_embed_escape(which_mode: i32) -> usize {\n" ++
        "    if which_mode == 0 {\n" ++
        "        return @embed_bytes(\"../escape.bin\").len;\n" ++
        "    }\n" ++
        "    return @embed_bytes(\"CON\").len;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        ffi_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(std.testing.allocator);

    var vm_engine = try MirVm.init(
        std.testing.allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink,
        .{ .virtual_files = &vfs_map },
    );
    defer vm_engine.deinit();
    try registerAllBodies(&vm_engine, &bundle);

    // Register `host_random` as an `extern` FFI symbol so calling it traps `E0503` with stack trace:
    for (bundle.hir_bundle.sym_table.symbols.items, 0..) |sym, raw_i| {
        if (std.mem.eql(u8, sym.name_text, "host_random")) {
            _ = try vm_engine.registerExternFn(
                sym.def_id,
                symbol_resolver.SymbolIndex.fromInt(@intCast(raw_i)),
            );
        }
    }

    const ffi_outer = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "call_ffi_outer",
    ).?;
    try std.testing.expectError(error.ForbiddenOperation, vm_engine.evalBody(ffi_outer, &.{}));
    try std.testing.expect(hasDiagWithStackTrace(&sink, .e0503_forbidden_comptime_operation));

    const ptr_outer = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "expose_ptr_outer",
    ).?;
    try std.testing.expectError(error.ForbiddenOperation, vm_engine.evalBody(ptr_outer, &.{}));

    const embed_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "bad_embed_escape",
    ).?;
    try std.testing.expectError(
        error.ForbiddenOperation,
        vm_engine.evalBody(embed_body, &[_]RegSlot{.{ .scalar_i64 = 0 }}),
    );
    try std.testing.expectError(
        error.ForbiddenOperation,
        vm_engine.evalBody(embed_body, &[_]RegSlot{.{ .scalar_i64 = 1 }}),
    );
}

// `E0504` spatial out-of-bounds indexing (array, slice, `#soa`, negative signed index):

test "test_mir_vm_comptime_diagnostics_e0504_spatial_oob_and_negative_index" {
    const oob_src =
        "pub struct Cell {\n" ++
        "    pub val: i32,\n" ++
        "}\n" ++
        "pub fn slice_read_oob(items: [i32], idx: usize) -> i32 {\n" ++
        "    return items[idx];\n" ++
        "}\n" ++
        "pub fn trigger_oob_inner(kind: i32, raw_idx: i32) -> i32 {\n" ++
        "    let fixed_arr: [i32; 3] = [10, 20, 30];\n" ++
        "    if kind == 0 {\n" ++
        "        return fixed_arr[raw_idx as usize];\n" ++
        "    } else if kind == 1 {\n" ++
        "        return slice_read_oob(&fixed_arr, raw_idx as usize);\n" ++
        "    }\n" ++
        "    var soa_cells: #soa [Cell; 2] = @default_init[#soa [Cell; 2]]();\n" ++
        "    soa_cells[0].val = 1;\n" ++
        "    soa_cells[1].val = 2;\n" ++
        "    return soa_cells[raw_idx as usize].val;\n" ++
        "}\n" ++
        "pub fn trigger_oob_outer(kind: i32, raw_idx: i32) -> i32 {\n" ++
        "    return trigger_oob_inner(kind, raw_idx);\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        oob_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    var vm_engine = try MirVm.init(
        std.testing.allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink,
        .{},
    );
    defer vm_engine.deinit();
    try registerAllBodies(&vm_engine, &bundle);

    const outer_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "trigger_oob_outer",
    ).?;

    // Array OOB (`idx = 3`), negative index cast (`idx = -1`), slice OOB (`idx = 2`), `#soa` OOB (`idx = 2`):
    try std.testing.expectError(
        error.OutOfBounds,
        vm_engine.evalBody(outer_body, &[_]RegSlot{ .{ .scalar_i64 = 0 }, .{ .scalar_i64 = 3 } }),
    );
    try std.testing.expectError(
        error.OutOfBounds,
        vm_engine.evalBody(outer_body, &[_]RegSlot{ .{ .scalar_i64 = 0 }, .{ .scalar_i64 = -1 } }),
    );
    try std.testing.expectError(
        error.OutOfBounds,
        vm_engine.evalBody(outer_body, &[_]RegSlot{ .{ .scalar_i64 = 1 }, .{ .scalar_i64 = 3 } }),
    );
    try std.testing.expectError(
        error.OutOfBounds,
        vm_engine.evalBody(outer_body, &[_]RegSlot{ .{ .scalar_i64 = 2 }, .{ .scalar_i64 = 2 } }),
    );
    try std.testing.expect(hasDiagWithStackTrace(&sink, .e0504_comptime_out_of_bounds));
}

// `E0505` uninitialized read via `init_mask` + `.rodata` leaf check vs zeroed alignment padding:

test "test_mir_vm_comptime_diagnostics_e0505_init_mask_and_rodata_padding" {
    var interner = try corex.StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var pool = try type_system.InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var sym_table = try symbol_resolver.SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();
    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    var vm_engine = try MirVm.init(
        std.testing.allocator,
        &interner,
        &pool,
        &sym_table,
        &rodata_pool,
        null,
        &sink,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm_engine.deinit();

    // [1] Synthetic `MirBody` loading an uninitialized `i32` local slot traps `E0505`:
    {
        var uninit_body = MirBody.init(
            std.testing.allocator,
            FileId.fromInt(1),
            DefId.init(FileId.fromInt(1), 0),
        );
        defer uninit_body.deinit();
        uninit_body.ret_ty = .i32_ty;
        const ret_loc = try addTestLocal(
            &uninit_body,
            LocalDecl.init(
                .empty,
                .i32_ty,
                TokenIndex.fromInt(0),
                0,
                .let_mode,
                .{ .is_return_slot = true },
            ),
        );
        const uninit_loc = try addTestLocal(
            &uninit_body,
            LocalDecl.init(.empty, .i32_ty, TokenIndex.fromInt(0), 0, .let_mode, .{}),
        );
        _ = try addTestPlace(&uninit_body, ret_loc, &.{});
        const uninit_pl = try addTestPlace(&uninit_body, uninit_loc, &.{});

        var ssa = MirSsaBuilder.init(std.testing.allocator, &uninit_body, &.{}, null);
        defer ssa.deinit();
        const bb0 = try ssa.createBlock(true, false);
        const bad_val = try ssa.emitInst(bb0, .{
            .op = .place_load,
            .type_id = .i32_ty,
            .operands = .{ .lhs = uninit_pl.asInt(), .rhs = 0 },
        }, TokenIndex.fromInt(0));
        ssa.setTerminator(bb0, .{ .kind = .ret, .cond_or_val = bad_val.asInt() });
        try ssa.finish();

        try std.testing.expectError(
            error.UninitializedRead,
            vm_engine.evalBody(&uninit_body, &.{}),
        );
        try std.testing.expect(hasDiag(&sink, .e0505_comptime_uninitialized_read));
    }

    // [2] `(u8, i64)` (`16B`, bytes `1..8` alignment padding):
    // Promoting with `i64` leaf uninitialized traps `E0505`; initializing `i64` succeeds and zeros `1..8`:
    const padded_tup_ty = try pool.internTuple(&[_]TypeId{ .u8_ty, .i64_ty });
    const alloc_id = try vm_engine.allocMemory(
        16,
        3,
        true,
        false,
        false,
        0,
        Span.init(FileId.fromInt(1), 0, 0),
    );
    const base_ptr = SymbolicPtr{ .alloc_id = alloc_id, .byte_offset = 0 };

    // Dirty raw bytes `1..8` without setting `init_mask` so padding canonicalization is proven:
    @memset(vm_engine.allocations.items[alloc_id.payloadIndex()].bytes[1..8], 0xCC);
    try vm_engine.writeScalarBytes(base_ptr, 0, &[_]u8{0x2A});

    // Leaf `.1` (`i64` at `8..16`) is still uninitialized -> `promoteSnapshotToRodata` traps `E0505`:
    try std.testing.expectError(
        error.UninitializedRead,
        vm_engine.promoteSnapshotToRodata(base_ptr, padded_tup_ty),
    );

    // Initialize `.1` (`8..16`), leaving padding `1..8` uninitialized -> `.rodata` promotion zeros `1..8`:
    var i64_bytes: [8]u8 = undefined;
    std.mem.writeInt(i64, &i64_bytes, 9001, .little);
    try vm_engine.writeScalarBytes(
        .{ .alloc_id = alloc_id, .byte_offset = 8 },
        3,
        &i64_bytes,
    );

    const promoted_id = try vm_engine.promoteSnapshotToRodata(base_ptr, padded_tup_ty);
    try std.testing.expectEqual(AllocDomain.rodata_blob, promoted_id.domain());
    const blob = rodata_pool.getBlob(promoted_id.payloadIndex()).?;
    try std.testing.expectEqual(@as(u8, 0x2A), blob.bytes[0]);
    for (blob.bytes[1..8]) |pad_byte| {
        try std.testing.expectEqual(@as(u8, 0), pad_byte);
    }
    try std.testing.expectEqual(@as(i64, 9001), std.mem.readInt(i64, blob.bytes[8..16], .little));
}

// `E0506` temporal UAF (dangling return + loop-local `ghost_storage_deinit`), null deref, `.rodata` write:

test "test_mir_vm_comptime_diagnostics_e0506_temporal_uaf_null_and_rodata_write" {
    const ptr_src =
        "pub fn leak_stack_ptr() -> *i32 {\n" ++
        "    var local_slot: i32 = 77;\n" ++
        "    return unsafe { &local_slot as *i32 };\n" ++
        "}\n" ++
        "pub fn loop_uaf_deref() -> i64 {\n" ++
        "    var keeper: i64 = 100;\n" ++
        "    var saved_ref: &i64 = &keeper;\n" ++
        "    var step: i64 = 0;\n" ++
        "    while step < 2 {\n" ++
        "        let iter_local: i64 = 42;\n" ++
        "        if step == 0 {\n" ++
        "            saved_ref = &iter_local;\n" ++
        "        } else {\n" ++
        "            return *saved_ref;\n" ++
        "        }\n" ++
        "        step = step + 1;\n" ++
        "    }\n" ++
        "    return *saved_ref;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        ptr_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    var vm_engine = try MirVm.init(
        std.testing.allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &sink,
        .{},
    );
    defer vm_engine.deinit();
    try registerAllBodies(&vm_engine, &bundle);

    // [1] Returning a dangling stack pointer traps `E0506`:
    const leak_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "leak_stack_ptr",
    ).?;
    try std.testing.expectError(error.InvalidPointer, vm_engine.evalBody(leak_body, &.{}));

    // [2] Dereferencing a loop-iteration local after `ghost_storage_deinit` traps `E0506`:
    const loop_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "loop_uaf_deref",
    ).?;
    try std.testing.expectError(error.InvalidPointer, vm_engine.evalBody(loop_body, &.{}));

    // [3] Null pointer dereference, immutable `.rodata_blob` write, and `.string_lit` write trap `E0506`:
    var dummy_byte: [1]u8 = .{0};
    try std.testing.expectError(
        error.InvalidPointer,
        vm_engine.readScalarBytes(SymbolicPtr.NULL, 0, &dummy_byte),
    );

    const ro_blob_id = try rodata_pool.internBlob("IMMUT", &.{}, 0);
    try std.testing.expectError(
        error.InvalidPointer,
        vm_engine.writeScalarBytes(.{ .alloc_id = ro_blob_id, .byte_offset = 0 }, 0, "X"),
    );

    const str_sym = try bundle.hir_bundle.interner.intern("hello");
    const str_alloc_id = ComptimeAllocId.fromStringId(str_sym);
    try std.testing.expectError(
        error.InvalidPointer,
        vm_engine.writeScalarBytes(.{ .alloc_id = str_alloc_id, .byte_offset = 0 }, 0, "Y"),
    );
    try std.testing.expect(hasDiag(&sink, .e0506_comptime_invalid_pointer));
}

// `E0508` recursion depth & memory cap enforcement + `E0509` cyclic `const` dependency detection:

test "test_mir_vm_comptime_diagnostics_e0508_recursion_memory_caps_and_e0509_cycles" {
    const rec_src =
        "pub fn recurse_deep(depth: i64) -> i64 {\n" ++
        "    if depth <= 0 {\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "    return 1 + recurse_deep(depth - 1);\n" ++
        "}\n" ++
        "pub fn blow_memory() -> u8 {\n" ++
        "    let huge: [u8; 2048] = [1u8; 2048];\n" ++
        "    return huge[0];\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        rec_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    // [1] Call-stack recursion cap (`max_call_depth = 10`) -> `E0508` with stack-trace labels:
    {
        var vm_rec = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &sink,
            .{ .max_call_depth = 10 },
        );
        defer vm_rec.deinit();
        try registerAllBodies(&vm_rec, &bundle);

        const rec_body = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "recurse_deep",
        ).?;
        try std.testing.expectError(
            error.ResourceLimitExceeded,
            vm_rec.evalBody(rec_body, &[_]RegSlot{.{ .scalar_i64 = 25 }}),
        );
        try std.testing.expect(
            hasDiagWithStackTrace(&sink, .e0508_comptime_resource_limit_exceeded),
        );
    }

    // [2] Memory byte cap (`mem_limit = 512`) -> `E0508`:
    {
        var sink_mem = DiagnosticSink.init(std.testing.allocator);
        defer sink_mem.deinit();
        var vm_mem = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &sink_mem,
            .{ .mem_limit = 512 },
        );
        defer vm_mem.deinit();
        try registerAllBodies(&vm_mem, &bundle);

        const mem_body = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "blow_memory",
        ).?;
        try std.testing.expectError(error.ResourceLimitExceeded, vm_mem.evalBody(mem_body, &.{}));
        try std.testing.expect(hasDiag(&sink_mem, .e0508_comptime_resource_limit_exceeded));
    }

    // [3] Mutual `const` evaluation cycle (`CYCLE_A <-> CYCLE_B`) -> `E0509` via `CompilerDb`:
    {
        var db = try query_db.CompilerDb.init(std.testing.allocator);
        defer db.deinit();

        const cycle_file = FileId.fromInt(7);
        const cycle_src =
            "pub const CYCLE_A: i32 = CYCLE_B + 1;\n" ++
            "pub const CYCLE_B: i32 = CYCLE_A + 1;\n";

        _ = try db.setInput(cycle_file, cycle_src, .low);
        const item_tree = try db.extractItemTree(cycle_file);
        const def_a = item_tree.findByName("CYCLE_A").?.def_id;
        if (db.evalComptimeDef(def_a)) |eval_art| {
            try std.testing.expect(eval_art.has_errors);
        } else |err| {
            try std.testing.expectEqual(error.DependencyCycle, err);
        }

        try std.testing.expect(hasDiag(db.getComptimeDiagnostics(def_a).?, .e0509_comptime_evaluation_cycle));
    }
}

// All 9 `DR-05` reflection intrinsics across both `TargetLayout.NATIVE_64` and `TargetLayout.WASM32`:

test "test_mir_vm_all_nine_reflection_intrinsics_native64_vs_wasm32" {
    const refl_src =
        "@attribute_schema(targets = [.StructField])\n" ++
        "pub struct FieldMeta {\n" ++
        "    pub slot_id: i32 = 0,\n" ++
        "}\n" ++
        "pub trait Identifiable {\n" ++
        "    fn id_code(&self) -> usize;\n" ++
        "}\n" ++
        "pub struct PtrRecord {\n" ++
        "    pub ptr_ref: &i32,\n" ++
        "    @FieldMeta(slot_id = 42)\n" ++
        "    pub tag_word: usize,\n" ++
        "}\n" ++
        "impl Identifiable for PtrRecord {\n" ++
        "    fn id_code(&self) -> usize {\n" ++
        "        return self.tag_word;\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn eval_surface_reflection() -> usize {\n" ++
        "    let anchor: i32 = 9;\n" ++
        "    let rec = PtrRecord { ptr_ref: &anchor, tag_word: 100 };\n" ++
        "    let sz = @size_of[PtrRecord]();\n" ++
        "    let al = @align_of[PtrRecord]();\n" ++
        "    let tname = @type_name[PtrRecord]();\n" ++
        "    let fld = @field(rec, \"tag_word\");\n" ++
        "    let has_yes: usize = if @has_field[PtrRecord](\"ptr_ref\") { 1 } else { 0 };\n" ++
        "    let has_no: usize = if @has_field[PtrRecord](\"absent\") { 10 } else { 0 };\n" ++
        "    let impl_yes: usize = if @implements[PtrRecord, Identifiable]() { 2 } else { 0 };\n" ++
        "    let impl_no: usize = if @implements[i32, Identifiable]() { 20 } else { 0 };\n" ++
        "    let meta_opt: FieldMeta? = comptime @field_attr_lookup[FieldMeta](\n" ++
        "        @type_info[PtrRecord]().id,\n" ++
        "        1,\n" ++
        "    );\n" ++
        "    let attr_val: usize = match meta_opt {\n" ++
        "        .Some(meta) => meta.slot_id as usize,\n" ++
        "        .None => 0,\n" ++
        "    };\n" ++
        "    let blob = @embed_bytes(\"assets/header.bin\");\n" ++
        "    return sz * 1000 + al * 100 + fld + tname.len + has_yes + has_no +\n" ++
        "        impl_yes + impl_no + attr_val + blob.len;\n" ++
        "}\n";

    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(std.testing.allocator);
    try vfs_map.put(std.testing.allocator, "assets/header.bin", "CX05!");

    const Case = struct {
        layout: TargetLayout,
        expected_size: u64,
        expected_align: u64,
        expected_score: u64,
    };
    // Score = `sz*1000 + al*100 + 159`: `NATIVE_64` (`16, 8`) -> `16959`; `WASM32` (`8, 4`) -> `8559`:
    const cases = [_]Case{
        .{
            .layout = TargetLayout.NATIVE_64,
            .expected_size = 16,
            .expected_align = 8,
            .expected_score = 16_959,
        },
        .{
            .layout = TargetLayout.WASM32,
            .expected_size = 8,
            .expected_align = 4,
            .expected_score = 8_559,
        },
    };

    for (cases) |case_cfg| {
        var bundle = try mir.lowerSourceToMir(
            std.testing.allocator,
            FileId.fromInt(1),
            refl_src,
            case_cfg.layout,
            .{},
        );
        defer bundle.deinit();
        try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

        var rodata_pool = RodataPool.init(std.testing.allocator);
        defer rodata_pool.deinit();
        var vm_engine = try MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &bundle.hir_bundle.diagnostics,
            .{ .target_layout = case_cfg.layout, .virtual_files = &vfs_map },
        );
        defer vm_engine.deinit();
        try registerAllBodies(&vm_engine, &bundle);

        const refl_body = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "eval_surface_reflection",
        ).?;
        const eval_res = try vm_engine.evalBody(refl_body, &.{});
        try std.testing.expectEqual(case_cfg.expected_score, eval_res.slot.scalar_u64);

        // Also verify `@type_info[PtrRecord]()` mirror layout metadata directly on `vm_engine`:
        var ptr_rec_ty: TypeId = .err_ty;
        for (bundle.hir_bundle.sym_table.symbols.items) |sym| {
            if (std.mem.eql(u8, sym.name_text, "PtrRecord")) {
                ptr_rec_ty = sym.type_id;
                break;
            }
        }
        try std.testing.expect(!ptr_rec_ty.isError());
        const ti_cv = try vm_engine.evalReflectionIntrinsic(
            .type_info,
            &[_]TypeId{ptr_rec_ty},
            &.{},
            &.{},
            &bundle.hir_bundle.hir_store,
        );
        try std.testing.expectEqual(case_cfg.expected_size, ti_cv.type_info_mirror.size_bytes);
        try std.testing.expectEqual(case_cfg.expected_align, ti_cv.type_info_mirror.align_bytes);
        try std.testing.expectEqualStrings(
            "PtrRecord",
            bundle.hir_bundle.interner.get(ti_cv.type_info_mirror.type_name_id),
        );
    }
}

// `PureCallMemoCache` (`Wyhash(0)` hits, `.rodata` content hashing, bounded FIFO eviction) & `RodataPool`:

test "test_mir_vm_pure_call_memo_cache_eviction_and_rodata_deduplication" {
    const memo_src =
        "pub fn pure_checksum(slice_in: [u8], bias: i64) -> i64 {\n" ++
        "    var acc: i64 = bias;\n" ++
        "    for idx in 0..slice_in.len {\n" ++
        "        acc = acc * 31 + (slice_in[idx] as i64);\n" ++
        "    }\n" ++
        "    return acc;\n" ++
        "}\n" ++
        "pub fn pure_square(num: i64) -> i64 {\n" ++
        "    return num * num + 3;\n" ++
        "}\n" ++
        "pub fn run_memo_pair(seed: i64) -> i64 {\n" ++
        "    let bytes: [u8; 3] = [1, 2, 3];\n" ++
        "    let first = pure_checksum(&bytes, seed);\n" ++
        "    let second = pure_checksum(&bytes, seed);\n" ++
        "    return first + second;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        memo_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Mark pure callees `is_contextless = true` (mirroring `D5` Tarjan purity inference):
    for (bundle.mir_bundle.bodies.items) |*body_ptr| {
        body_ptr.is_contextless = true;
    }

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var memo_cache = PureCallMemoCache.init(std.testing.allocator);
    defer memo_cache.deinit();

    var vm_engine = try MirVm.init(
        std.testing.allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        &memo_cache,
        &bundle.hir_bundle.diagnostics,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm_engine.deinit();
    try registerAllBodies(&vm_engine, &bundle);

    // [1] `.rodata_blob` slice content + scalar `seed` hits `PureCallMemoCache` on second call, while
    // stack `.vm_alloc` slice in `run_memo_pair` executes without unsound cross-frame pointer caching:
    const pair_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "run_memo_pair",
    ).?;
    const pair_res = try vm_engine.evalBody(pair_body, &[_]RegSlot{.{ .scalar_i64 = 5 }});
    try std.testing.expectEqual(@as(i64, 299962), pair_res.slot.scalar_i64);
    try std.testing.expectEqual(@as(u64, 0), memo_cache.hit_count);

    const checksum_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "pure_checksum",
    ).?;
    const slice_u8_ty = try bundle.hir_bundle.pool.internSlice(.u8_ty, false);
    const ro_bytes_id = try rodata_pool.internBlob(&[_]u8{ 1, 2, 3 }, &.{}, 0);
    const ro_slice_a = try vm_engine.makeFatSliceSlot(
        slice_u8_ty,
        .{ .alloc_id = ro_bytes_id, .byte_offset = 0 },
        3,
    );
    const ro_slice_b = try vm_engine.makeFatSliceSlot(
        slice_u8_ty,
        .{ .alloc_id = ro_bytes_id, .byte_offset = 0 },
        3,
    );
    const ro_first = try vm_engine.evalBody(
        checksum_body,
        &[_]RegSlot{ ro_slice_a, .{ .scalar_i64 = 5 } },
    );
    const ro_second = try vm_engine.evalBody(
        checksum_body,
        &[_]RegSlot{ ro_slice_b, .{ .scalar_i64 = 5 } },
    );
    try std.testing.expectEqual(@as(i64, 149981), ro_first.slot.scalar_i64);
    try std.testing.expectEqual(@as(i64, 149981), ro_second.slot.scalar_i64);
    try std.testing.expectEqual(@as(u64, 1), memo_cache.hit_count);

    // [2] Drive `> MAX_MEMO_ENTRIES` (`4,096`) distinct pure calls to verify bounded eviction & slot reuse:
    const sq_body = bundle.mir_bundle.findBodyByName(
        &bundle.hir_bundle.interner,
        "pure_square",
    ).?;
    var call_i: i64 = 0;
    while (call_i < @as(i64, @intCast(mir_vm.MAX_MEMO_ENTRIES + 64))) : (call_i += 1) {
        const sq_res = try vm_engine.evalBody(sq_body, &[_]RegSlot{.{ .scalar_i64 = call_i }});
        try std.testing.expectEqual(call_i * call_i + 3, sq_res.slot.scalar_i64);
    }
    try std.testing.expectEqual(mir_vm.MAX_MEMO_ENTRIES, memo_cache.live_count);
    try std.testing.expect(memo_cache.entries.items.len <= mir_vm.MAX_MEMO_ENTRIES);
    try std.testing.expect(memo_cache.live_bytes <= mir_vm.MAX_MEMO_BYTES);

    // [3] `RodataPool` structural deduplication across bytes, relocations, and alignments:
    const reloc_target = ComptimeAllocId.fromRodataIndex(0);
    const b_one = try rodata_pool.internBlob("ABCD", &.{}, 2);
    const b_two = try rodata_pool.internBlob("ABCD", &.{}, 2);
    const b_diff_align = try rodata_pool.internBlob("ABCD", &.{}, 3);
    const b_with_reloc = try rodata_pool.internBlob(
        "ABCD1234",
        &[_]mir_vm.RodataReloc{.{ .byte_offset = 0, .target_alloc = reloc_target }},
        3,
    );
    const b_same_reloc = try rodata_pool.internBlob(
        "ABCD1234",
        &[_]mir_vm.RodataReloc{.{ .byte_offset = 0, .target_alloc = reloc_target }},
        3,
    );
    try std.testing.expectEqual(b_one, b_two);
    try std.testing.expect(b_one != b_diff_align);
    try std.testing.expectEqual(b_with_reloc, b_same_reloc);
    try std.testing.expect(b_diff_align != b_with_reloc);
}

test "test_mir_vm_standalone_pure_memo_structural_body_identity_without_db" {
    const standalone_src =
        "pub fn standalone_add(val: i64) -> i64 {\n" ++
        "    return val + 10;\n" ++
        "}\n" ++
        "pub fn standalone_mul(val: i64) -> i64 {\n" ++
        "    return val * 10;\n" ++
        "}\n";

    var bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(1),
        standalone_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    // Clear `def_id` and `symbol_index` on both pure bodies to verify deterministic structural hashing
    // without `@intFromPtr` when `compiler_db == null`:
    for (bundle.mir_bundle.bodies.items) |*body_ptr| {
        body_ptr.is_contextless = true;
        body_ptr.def_id = corex.DefId.NONE;
        body_ptr.symbol_index = .none;
    }

    var rodata_pool = RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var memo_cache = PureCallMemoCache.init(std.testing.allocator);
    defer memo_cache.deinit();

    var vm_engine = try MirVm.init(
        std.testing.allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        &memo_cache,
        &bundle.hir_bundle.diagnostics,
        .{ .target_layout = TargetLayout.NATIVE_64 },
    );
    defer vm_engine.deinit();

    const add_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "standalone_add").?;
    const mul_body = bundle.mir_bundle.findBodyByName(&bundle.hir_bundle.interner, "standalone_mul").?;

    const add_first = try vm_engine.evalBody(add_body, &[_]RegSlot{.{ .scalar_i64 = 3 }});
    const mul_first = try vm_engine.evalBody(mul_body, &[_]RegSlot{.{ .scalar_i64 = 3 }});
    try std.testing.expectEqual(@as(i64, 13), add_first.slot.scalar_i64);
    try std.testing.expectEqual(@as(i64, 30), mul_first.slot.scalar_i64);
    try std.testing.expectEqual(@as(u64, 0), memo_cache.hit_count);

    const add_second = try vm_engine.evalBody(add_body, &[_]RegSlot{.{ .scalar_i64 = 3 }});
    const mul_second = try vm_engine.evalBody(mul_body, &[_]RegSlot{.{ .scalar_i64 = 3 }});
    try std.testing.expectEqual(@as(i64, 13), add_second.slot.scalar_i64);
    try std.testing.expectEqual(@as(i64, 30), mul_second.slot.scalar_i64);
    try std.testing.expectEqual(@as(u64, 2), memo_cache.hit_count);
}

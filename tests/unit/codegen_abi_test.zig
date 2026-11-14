//! Unit Tests for `codegen_abi.zig` & Phase 7 Frontend/IR Extensions (`tests/unit/codegen_abi_test.zig`)
//!
//! Verifies all Wave 3A Phase 7 invariants across `diagnostic.zig`, `symbol_resolver.zig`,
//! `type_system.zig`, `hir.zig`, `mir.zig`, `mir_sast.zig`, `mir_opt.zig`, `mir_vm.zig`, and
//! `codegen_abi.zig`:
//! - Binary-exact struct sizes (`DeclContractFlags` `2B`, `MirBasicBlock` `32B`, `RawBlobConst` `16B`,
//!   `LoopContractMeta` `8B`, `MirLoopContractEntry` `16B`, `TargetSpec` `4B`, `NicheSpec` `24B`,
//!   `ResolvedTypeLayout` `32B`, `AbiParamRecipe` `16B`, `ProvenValueRange` `24B`).
//! - Phase 7 CLI/driver diagnostics (`E0006`, `E0007`, `E0008`), all 7 canonical target triples,
//!   `TypeLayoutResolver` native vs `@repr(C)`/`@packed`/`@cache_aligned`/`#soa`/niche parity,
//!   `AbiClassifier` (`cx_native`, `cx_result_cc` `[CRITICAL-06]`, `SysV`, `Win64`, `AAPCS64`, `wasm32`),
//!   `@must_vectorize`/`@vectorize_width`, `MirConst.raw_blob`, `computeBodyProvenRanges`, all 17
//!   Phase 7 intrinsics in `MirVm` oracle mode, and `Prune-02` `atomicWriteOutputFile`.

const std = @import("std");
const corex = @import("corex");

const codegen_abi = corex.codegen_abi;
const mir = corex.mir;
const mir_vm = corex.mir_vm;
const mir_opt = corex.mir_opt;
const mir_sast = corex.mir_sast;
const type_system = corex.type_system;
const FileId = corex.FileId;
const Span = corex.Span;
const TypeId = corex.TypeId;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const TypeLayoutResolver = corex.TypeLayoutResolver;
const AbiClassifier = corex.AbiClassifier;
const CallingConvKind = corex.CallingConvKind;
const AbiPassMode = corex.AbiPassMode;
const RegBank = codegen_abi.RegBank;
const SwifterrorKind = codegen_abi.SwifterrorKind;
const FnParamSpec = codegen_abi.FnParamSpec;
const FnSignatureView = codegen_abi.FnSignatureView;

// -------------------------------------- INTERNALS --------------------------------------

/// Finds a named top-level symbol in `sym_table` and returns its resolved `TypeId`.
fn lookupNamedTypeId(sym_table: *const corex.SymbolTable, target_name: []const u8) !TypeId {
    for (sym_table.symbols.items) |sym_rec| {
        if (std.mem.eql(u8, sym_rec.name_text, target_name) and !sym_rec.type_id.isError()) {
            return sym_rec.type_id;
        }
    }
    return error.TestSymbolNotFound;
}

/// Evaluates zero-arg function `entry_name` from `source_text` in `MirVm` and returns its scalar `RegSlot`.
fn evalFunctionInOracleVm(
    allocator: std.mem.Allocator,
    source_text: []const u8,
    entry_name: []const u8,
    target_spec: TargetSpec,
    stdout_buf: ?*std.ArrayListUnmanaged(u8),
    stderr_buf: ?*std.ArrayListUnmanaged(u8),
) !struct { slot: mir_vm.RegSlot, exit_code: ?i32 } {
    var diag_sink = DiagnosticSink.init(allocator);
    defer diag_sink.deinit();

    var bundle = try mir.lowerSourceToMir(
        allocator,
        FileId.fromInt(1),
        source_text,
        target_spec.asTargetLayout(),
        .{},
    );
    defer bundle.deinit();
    try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

    var rodata_pool = mir_vm.RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm_engine = try mir_vm.MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        &diag_sink,
        .{
            .target_layout = target_spec.asTargetLayout(),
            .stdout_capture = stdout_buf,
            .stderr_capture = stderr_buf,
            .is_oracle_runtime_mode = true,
        },
    );
    defer vm_engine.deinit();

    var entry_body_ptr: ?*const mir.MirBody = null;
    for (bundle.mir_bundle.bodies.items) |*body_ptr| {
        const sym_idx = bundle.hir_bundle.sym_table.def_to_symbol.get(body_ptr.def_id.asInt()) orelse .none;
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
        const fn_name = bundle.hir_bundle.interner.get(body_ptr.name);
        if (std.mem.eql(u8, fn_name, entry_name)) {
            entry_body_ptr = body_ptr;
        }
    }
    const target_body = entry_body_ptr orelse return error.EntryFunctionNotFound;
    const eval_res = vm_engine.evalBody(target_body, &.{}) catch |vm_err| {
        if (vm_err == error.ProcessExited) {
            return .{ .slot = .{ .scalar_u64 = 0 }, .exit_code = vm_engine.exited_with_code };
        }
        return vm_err;
    };
    return .{ .slot = eval_res.slot, .exit_code = vm_engine.exited_with_code };
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_phase7_binary_sizes_target_triples_and_e0006_e0007_e0008_diagnostics" {
    // [1] Verify exact binary record sizes across Phase 7 Wave 3A:
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(corex.DeclContractFlags));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.MirBasicBlock));
    try std.testing.expectEqual(
        @sizeOf(union(enum) { unit_val, int_val: i128 }),
        @sizeOf(corex.MirConst),
    );
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.RawBlobConst));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.LoopContractMask));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.LoopContractMeta));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.MirLoopContractEntry));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(TargetSpec));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.NicheSpec));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.ResolvedTypeLayout));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.AbiParamRecipe));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.ProvenValueRange));

    // [2] Verify all 7 canonical targets, vendor aliases, and `D-10A` cache-line / SIMD layout rules.
    for (codegen_abi.ALL_CANONICAL_TARGETS) |spec| {
        const parsed = TargetSpec.parseTargetTriple(spec.canonicalName()).?;
        try std.testing.expectEqual(spec.arch, parsed.arch);
        try std.testing.expectEqual(spec.os, parsed.os);
        try std.testing.expect(spec.asZigTargetTriple().len > 0);
        try std.testing.expect(spec.asLlvmTargetTriple().len > 0);
        try std.testing.expect(spec.asLlvmDataLayout().len > 0);
    }
    try std.testing.expectEqual(@as(u8, 7), TargetSpec.AARCH64_MACOS.asTargetLayout().cache_line_align_log2);
    try std.testing.expectEqual(@as(u8, 6), TargetSpec.X86_64_LINUX.asTargetLayout().cache_line_align_log2);
    try std.testing.expectEqual(@as(u8, 4), TargetSpec.WASM32_WASI.asTargetLayout().ptr_byte_size);

    const avx2_spec = TargetSpec.parseTargetTriple("x86_64-linux-gnu+avx2").?;
    try std.testing.expectEqual(corex.SimdLevel.avx2, avx2_spec.simd_level);
    try std.testing.expectEqual(@as(u8, 5), avx2_spec.asTargetLayout().simd_align_log2);
    try std.testing.expect(TargetSpec.parseTargetTriple("wasm32-wasi+avx512") == null);

    // [3] Exercise `E0006`, `E0007`, and `E0008` in `DiagnosticSink`:
    try std.testing.expectEqualStrings("E0006", DiagnosticCode.e0006_invalid_target_triple.asCodeStr());
    try std.testing.expectEqualStrings("E0007", DiagnosticCode.e0007_codegen_backend_failure.asCodeStr());
    try std.testing.expectEqualStrings("E0008", DiagnosticCode.e0008_linker_invocation_failed.asCodeStr());

    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    const invalid_target = try TargetSpec.parseOrEmitInvalidTarget("mips64-unknown-freebsd", Span.ZERO, &sink);
    try std.testing.expect(invalid_target == null);
    try codegen_abi.emitBackendFailureDiagnostic(&sink, Span.ZERO, "tier_a_c99", "synthetic test failure");
    try codegen_abi.emitLinkerFailureDiagnostic(&sink, Span.ZERO, 1, "undefined symbol: missing_fn");

    try std.testing.expectEqual(@as(usize, 3), sink.diagnostics.items.len);
    try std.testing.expectEqual(DiagnosticCode.e0006_invalid_target_triple, sink.diagnostics.items[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0007_codegen_backend_failure, sink.diagnostics.items[1].code);
    try std.testing.expectEqual(DiagnosticCode.e0008_linker_invocation_failed, sink.diagnostics.items[2].code);
}

test "test_type_layout_resolver_struct_reordering_repr_c_packed_cache_aligned_soa_and_niches" {
    const src =
        \\pub struct NativeStruct {
        \\    pub flag: bool,
        \\    pub count: u64,
        \\    pub tag_b: u8,
        \\}
        \\@repr(C)
        \\pub struct ReprCStruct {
        \\    pub flag: bool,
        \\    pub count: u64,
        \\    pub tag_b: u8,
        \\}
        \\@packed
        \\pub struct PackedStruct {
        \\    pub flag: bool,
        \\    pub count: u64,
        \\    pub tag_b: u8,
        \\}
        \\@cache_aligned
        \\pub struct CacheLineCounter {
        \\    pub val: u64,
        \\}
        \\@align(32)
        \\@link_name("cx_aligned_block")
        \\pub struct ExplicitAligned {
        \\    pub byte_val: u8,
        \\}
        \\pub struct Particle {
        \\    pub pos_x: f32,
        \\    pub flags: u8,
        \\}
        \\@extern("C")
        \\@link_name("puts")
        \\pub fn c_puts(msg: *u8) -> i32;
    ;

    var tc_res = try corex.typecheckSource(std.testing.allocator, FileId.fromInt(1), src);
    defer tc_res.deinit();
    try std.testing.expect(!tc_res.diagnostics.hasErrors());

    // Verify `@link_name` extracted on `c_puts`.
    var has_link_name = false;
    for (tc_res.symbol_table.symbols.items) |sym_rec| {
        if (std.mem.eql(u8, sym_rec.name_text, "c_puts")) {
            try std.testing.expectEqualStrings("puts", sym_rec.link_name_text);
            has_link_name = true;
        }
    }
    try std.testing.expect(has_link_name);

    const native_ty = try lookupNamedTypeId(&tc_res.symbol_table, "NativeStruct");
    const repr_c_ty = try lookupNamedTypeId(&tc_res.symbol_table, "ReprCStruct");
    const packed_ty = try lookupNamedTypeId(&tc_res.symbol_table, "PackedStruct");
    const cache_ty = try lookupNamedTypeId(&tc_res.symbol_table, "CacheLineCounter");
    const explicit_ty = try lookupNamedTypeId(&tc_res.symbol_table, "ExplicitAligned");
    const particle_ty = try lookupNamedTypeId(&tc_res.symbol_table, "Particle");

    // [1] Resolve on `x86_64-linux`:
    var resolver_x64 = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.X86_64_LINUX,
    );
    defer resolver_x64.deinit();

    const native_layout = try resolver_x64.resolveType(native_ty);
    try std.testing.expectEqual(@as(u64, 16), native_layout.size_bytes);
    const native_fields = resolver_x64.getFieldsByDecl(native_layout);
    // `count: u64` (decl 1) -> offset `0`; `flag: bool` (decl 0, has_niche) -> offset `8`; `tag_b: u8` (decl 2) -> offset `9`:
    try std.testing.expectEqual(@as(u64, 8), native_fields[0].byte_offset);
    try std.testing.expectEqual(@as(u64, 0), native_fields[1].byte_offset);
    try std.testing.expectEqual(@as(u64, 9), native_fields[2].byte_offset);
    const phys_order = resolver_x64.getPhysicalFieldOrder(native_layout);
    try std.testing.expectEqualSlices(u32, &.{ 1, 0, 2 }, phys_order);

    const repr_c_layout = try resolver_x64.resolveType(repr_c_ty);
    try std.testing.expectEqual(@as(u64, 24), repr_c_layout.size_bytes);
    const repr_c_fields = resolver_x64.getFieldsByDecl(repr_c_layout);
    try std.testing.expectEqual(@as(u64, 0), repr_c_fields[0].byte_offset);
    try std.testing.expectEqual(@as(u64, 8), repr_c_fields[1].byte_offset);
    try std.testing.expectEqual(@as(u64, 16), repr_c_fields[2].byte_offset);
    const repr_c_pads = try resolver_x64.getPaddingSpans(repr_c_ty);
    try std.testing.expectEqual(@as(usize, 2), repr_c_pads.len);
    try std.testing.expectEqual(@as(u64, 1), repr_c_pads[0].byte_offset);
    try std.testing.expectEqual(@as(u64, 7), repr_c_pads[0].byte_len);

    const packed_layout = try resolver_x64.resolveType(packed_ty);
    try std.testing.expectEqual(@as(u64, 10), packed_layout.size_bytes);
    try std.testing.expectEqual(@as(u8, 0), packed_layout.align_log2);

    const cache_x64 = try resolver_x64.resolveType(cache_ty);
    try std.testing.expectEqual(@as(u64, 64), cache_x64.size_bytes);
    try std.testing.expectEqual(@as(u8, 6), cache_x64.align_log2);

    const explicit_layout = try resolver_x64.resolveType(explicit_ty);
    try std.testing.expectEqual(@as(u64, 32), explicit_layout.size_bytes);
    try std.testing.expectEqual(@as(u8, 5), explicit_layout.align_log2);

    // [2] `@cache_aligned` on `aarch64-macos` (`D-10A`) aligns to `128B` (`align_log2 == 7`):
    var resolver_mac = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.AARCH64_MACOS,
    );
    defer resolver_mac.deinit();
    const cache_mac = try resolver_mac.resolveType(cache_ty);
    try std.testing.expectEqual(@as(u64, 128), cache_mac.size_bytes);
    try std.testing.expectEqual(@as(u8, 7), cache_mac.align_log2);

    // [3] `#soa [Particle; 5]` aligns column 1 (`flags: u8`) to `16B` (`SSE2`) vs `32B` (`AVX2`):
    const col1_sse = resolver_x64.getSoaColumnOffset(particle_ty, 1, 5).?;
    // `pos_x` = `5 * 4 = 20` bytes -> aligned up to `16B` = `32`:
    try std.testing.expectEqual(@as(u64, 32), col1_sse.byte_offset);

    var resolver_avx2 = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.parseTargetTriple("x86_64-linux+avx2").?,
    );
    defer resolver_avx2.deinit();
    const col1_avx2 = resolver_avx2.getSoaColumnOffset(particle_ty, 1, 5).?;
    try std.testing.expectEqual(@as(u64, 32), col1_avx2.byte_offset);
    try std.testing.expectEqual(@as(u8, 5), col1_avx2.col_align_log2);

    // [4] Multi-tier niches (`[CRITICAL-04]`):
    const ref_i32 = try tc_res.type_pool.internRef(.i32_ty, false);
    const opt_ref = try tc_res.type_pool.internOptional(ref_i32);
    const opt_str = try tc_res.type_pool.internOptional(.str_ty);
    const opt_bool = try tc_res.type_pool.internOptional(.bool_ty);
    const res_never = try tc_res.type_pool.internResult(.i64_ty, .never_ty);

    try std.testing.expectEqual(@as(u64, 8), (try resolver_x64.resolveType(opt_ref)).size_bytes);
    try std.testing.expectEqual(@as(u64, 16), (try resolver_x64.resolveType(opt_str)).size_bytes);
    try std.testing.expectEqual(@as(u64, 1), (try resolver_x64.resolveType(opt_bool)).size_bytes);
    const res_never_layout = try resolver_x64.resolveType(res_never);
    try std.testing.expectEqual(@as(u64, 8), res_never_layout.size_bytes);
    try std.testing.expectEqual(codegen_abi.SumReprKind.transparent_ok, res_never_layout.sum_repr);
}

test "test_abi_classifier_cx_native_cx_result_cc_swifterror_and_7_target_c_abis" {
    const src =
        \\@repr(C)
        \\pub struct MixedSysV {
        \\    pub id: i64,
        \\    pub ratio: f64,
        \\}
        \\@repr(C)
        \\pub struct OddThreeBytes {
        \\    pub a: u8,
        \\    pub b: u8,
        \\    pub c: u8,
        \\}
        \\@repr(C)
        \\pub struct Vec4f {
        \\    pub x: f32,
        \\    pub y: f32,
        \\    pub z: f32,
        \\    pub w: f32,
        \\}
        \\@repr(C)
        \\pub struct Big40 {
        \\    pub words: [u64; 5],
        \\}
    ;

    var tc_res = try corex.typecheckSource(std.testing.allocator, FileId.fromInt(2), src);
    defer tc_res.deinit();
    try std.testing.expect(!tc_res.diagnostics.hasErrors());

    const mixed_ty = try lookupNamedTypeId(&tc_res.symbol_table, "MixedSysV");
    const odd3_ty = try lookupNamedTypeId(&tc_res.symbol_table, "OddThreeBytes");
    const vec4f_ty = try lookupNamedTypeId(&tc_res.symbol_table, "Vec4f");
    const big40_ty = try lookupNamedTypeId(&tc_res.symbol_table, "Big40");
    const ref_u8 = try tc_res.type_pool.internRef(.u8_ty, false);

    // [1] `cx_result_cc` `[CRITICAL-06]` eligibility matrix on `x86_64-linux`:
    var res_linux = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.X86_64_LINUX,
    );
    defer res_linux.deinit();

    const res_zst_err = try tc_res.type_pool.internResult(.i64_ty, .unit_ty);
    var fn_zst = try AbiClassifier.classifyFn(std.testing.allocator, &res_linux, .{
        .params = &.{.{ .type_id = big40_ty, .mode = .let_mode }},
        .ret_ty = res_zst_err,
        .is_contextless = false,
    });
    defer fn_zst.deinit(std.testing.allocator);
    try std.testing.expectEqual(CallingConvKind.cx_result_cc, fn_zst.calling_conv);
    try std.testing.expectEqual(SwifterrorKind.zst_err, fn_zst.swifterror_kind);
    try std.testing.expectEqual(@as(u8, 0), fn_zst.swifterror_recipe.attr_bits);
    try std.testing.expect(fn_zst.has_implicit_context);
    try std.testing.expectEqual(AbiPassMode.indirect_by_ref, fn_zst.param_recipes[0].pass_mode);
    try std.testing.expect(fn_zst.param_recipes[0].attrs().is_readonly);

    const res_int56 = try tc_res.type_pool.internResult(mixed_ty, .u32_ty);
    var fn_int56 = try AbiClassifier.classifyFn(std.testing.allocator, &res_linux, .{
        .params = &.{},
        .ret_ty = res_int56,
    });
    defer fn_int56.deinit(std.testing.allocator);
    try std.testing.expectEqual(CallingConvKind.cx_result_cc, fn_int56.calling_conv);
    try std.testing.expectEqual(SwifterrorKind.tagged_int56, fn_int56.swifterror_kind);
    try std.testing.expectEqual(AbiPassMode.direct_pair, fn_int56.ret_recipe.pass_mode);

    const res_ptr_err = try tc_res.type_pool.internResult(.i64_ty, ref_u8);
    var fn_ptr_err = try AbiClassifier.classifyFn(std.testing.allocator, &res_linux, .{
        .params = &.{},
        .ret_ty = res_ptr_err,
    });
    defer fn_ptr_err.deinit(std.testing.allocator);
    try std.testing.expectEqual(CallingConvKind.cx_result_cc, fn_ptr_err.calling_conv);
    try std.testing.expectEqual(SwifterrorKind.nonnull_ptr, fn_ptr_err.swifterror_kind);

    // Un-niched 8B `i64` error and `16B` `str` error MUST fall back to `cx_native`:
    const res_i64_err = try tc_res.type_pool.internResult(.i64_ty, .i64_ty);
    var fn_fallback = try AbiClassifier.classifyFn(std.testing.allocator, &res_linux, .{
        .params = &.{},
        .ret_ty = res_i64_err,
    });
    defer fn_fallback.deinit(std.testing.allocator);
    try std.testing.expectEqual(CallingConvKind.cx_native, fn_fallback.calling_conv);
    try std.testing.expectEqual(SwifterrorKind.none, fn_fallback.swifterror_kind);

    // [2] `SysV AMD64` (`x86_64-linux` `extern "C"`): `MixedSysV` -> `(gpr, xmm_vec)`, `Big40` -> `indirect_byval` + `sret`:
    var fn_sysv = try AbiClassifier.classifyFn(std.testing.allocator, &res_linux, .{
        .params = &.{ .{ .type_id = mixed_ty }, .{ .type_id = big40_ty } },
        .ret_ty = big40_ty,
        .is_extern_c = true,
    });
    defer fn_sysv.deinit(std.testing.allocator);
    try std.testing.expectEqual(CallingConvKind.c_system, fn_sysv.calling_conv);
    try std.testing.expect(fn_sysv.has_sret);
    try std.testing.expectEqual(AbiPassMode.direct_pair, fn_sysv.param_recipes[0].pass_mode);
    try std.testing.expectEqual(RegBank.gpr, fn_sysv.param_recipes[0].bank_0);
    try std.testing.expectEqual(RegBank.xmm_vec, fn_sysv.param_recipes[0].bank_1);
    try std.testing.expectEqual(AbiPassMode.indirect_byval, fn_sysv.param_recipes[1].pass_mode);

    // [3] `Win64` (`x86_64-windows` `extern "C"`): odd `3B` struct and `i128` MUST pass by ref and return via `sret`:
    var res_win = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.X86_64_WINDOWS,
    );
    defer res_win.deinit();
    var fn_win = try AbiClassifier.classifyFn(std.testing.allocator, &res_win, .{
        .params = &.{ .{ .type_id = odd3_ty }, .{ .type_id = .i128_ty }, .{ .type_id = .u64_ty } },
        .ret_ty = odd3_ty,
        .is_extern_c = true,
    });
    defer fn_win.deinit(std.testing.allocator);
    try std.testing.expect(fn_win.has_sret);
    try std.testing.expectEqual(AbiPassMode.indirect_by_ref, fn_win.param_recipes[0].pass_mode);
    try std.testing.expectEqual(AbiPassMode.indirect_by_ref, fn_win.param_recipes[1].pass_mode);
    try std.testing.expectEqual(AbiPassMode.direct_scalar, fn_win.param_recipes[2].pass_mode);

    // [4] `Apple ARM64` (`aarch64-macos` `extern "C"`): `Vec4f` -> `direct_hfa` (`4` lanes), `i8` -> `sext`, `u16` -> `zext`:
    var res_arm_mac = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.AARCH64_MACOS,
    );
    defer res_arm_mac.deinit();
    var fn_arm = try AbiClassifier.classifyFn(std.testing.allocator, &res_arm_mac, .{
        .params = &.{ .{ .type_id = vec4f_ty }, .{ .type_id = .i8_ty }, .{ .type_id = .u16_ty } },
        .ret_ty = vec4f_ty,
        .is_extern_c = true,
    });
    defer fn_arm.deinit(std.testing.allocator);
    try std.testing.expectEqual(AbiPassMode.direct_hfa, fn_arm.ret_recipe.pass_mode);
    try std.testing.expectEqual(@as(u8, 4), fn_arm.ret_recipe.piece_count);
    try std.testing.expect(fn_arm.param_recipes[1].attrs().is_sext);
    try std.testing.expect(fn_arm.param_recipes[2].attrs().is_zext);

    // [5] `wasm32-wasi`: `swifterror` disabled (`wasm_mvp`):
    var res_wasm = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.WASM32_WASI,
    );
    defer res_wasm.deinit();
    var fn_wasm = try AbiClassifier.classifyFn(std.testing.allocator, &res_wasm, .{
        .params = &.{},
        .ret_ty = res_zst_err,
    });
    defer fn_wasm.deinit(std.testing.allocator);
    try std.testing.expectEqual(CallingConvKind.wasm_mvp, fn_wasm.calling_conv);
    try std.testing.expectEqual(SwifterrorKind.none, fn_wasm.swifterror_kind);
    try std.testing.expect(fn_wasm.abiSigHash64() != 0);
}

test "test_phase7_loop_contracts_raw_blob_proven_ranges_and_17_intrinsics_in_vm" {
    // [1] `@must_vectorize` + `@vectorize_width(8)` lower to `MirBody.loop_contracts` and survive `--release` opt:
    const loop_src =
        \\pub fn sum_lanes(arr: [i32; 8]) -> i32 {
        \\    var acc: i32 = 0;
        \\    var idx: usize = 0;
        \\    @must_vectorize
        \\    @vectorize_width(8)
        \\    while idx < 8 {
        \\        acc = acc + arr[idx];
        \\        idx = idx + 1;
        \\    }
        \\    return acc;
        \\}
    ;
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var mir_bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(3),
        loop_src,
        type_system.TargetLayout.NATIVE_64,
        .{},
    );
    defer mir_bundle.deinit();
    try std.testing.expect(!mir_bundle.hir_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), mir_bundle.mir_bundle.bodies.items[0].loop_contracts.items.len);
    const lc = mir_bundle.mir_bundle.bodies.items[0].loop_contracts.items[0];
    try std.testing.expect(lc.meta.contract_flags.is_must_vectorize);
    try std.testing.expectEqual(@as(u16, 8), lc.meta.min_lanes);

    var opt_res = try mir_opt.optimizeMirModule(
        std.testing.allocator,
        mir_bundle.mir_bundle.bodies.items,
        &mir_bundle.hir_bundle.pool,
        &mir_bundle.hir_bundle.sym_table,
        &mir_bundle.hir_bundle.interner,
        .{ .is_release_mode = true },
        &sink,
    );
    defer opt_res.deinit();
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), opt_res.bodies.items[0].loop_contracts.items.len);

    // [2] `computeBodyProvenRanges` decodes `SIGN_BIAS_U64` on signed values (`[MAJOR-08]`):
    const range_src =
        \\pub fn clamp_signed(val: i32) -> i32 {
        \\    if val >= -5 && val <= 12 {
        \\        return val + 1;
        \\    }
        \\    return 0;
        \\}
    ;
    var sast_bundle = try mir_sast.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(4),
        range_src,
        type_system.TargetLayout.NATIVE_64,
        .{ .diagnostic_sink = &sink },
    );
    defer sast_bundle.deinit();
    try std.testing.expect(!sink.hasErrors());
    const proven = try corex.computeBodyProvenRanges(
        std.testing.allocator,
        &sast_bundle.mir_module.bodies.items[0],
        &sast_bundle.pool,
        &sast_bundle.sym_table,
    );
    defer std.testing.allocator.free(proven);
    try std.testing.expect(proven.len > 0);
    for (proven) |fact| {
        if (fact.flags().is_signed) {
            try std.testing.expect(fact.signedMin() <= fact.signedMax());
        }
    }

    // [3] `materializeModuleEmbedBytes` rewrites `@embed_bytes` into `MirConst.raw_blob` (`[CRITICAL-07]`):
    const embed_src =
        \\pub fn blob_sum() -> u8 {
        \\    let bytes = @embed_bytes("assets/magic.bin");
        \\    return bytes[0] + bytes[3];
        \\}
    ;
    var vfs_map: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer vfs_map.deinit(std.testing.allocator);
    try vfs_map.put(std.testing.allocator, "assets/magic.bin", &[_]u8{ 10, 20, 30, 32 });

    var embed_bundle = try mir.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(5),
        embed_src,
        type_system.TargetLayout.NATIVE_64,
        .{},
    );
    defer embed_bundle.deinit();
    try std.testing.expect(!embed_bundle.hir_bundle.diagnostics.hasErrors());

    var blob_store = corex.MirBlobStore.init(std.testing.allocator);
    defer blob_store.deinit();
    const is_materialized = try corex.materializeModuleEmbedBytes(
        embed_bundle.mir_bundle.bodies.items,
        &embed_bundle.hir_bundle.interner,
        &embed_bundle.hir_bundle.tokens,
        &blob_store,
        .{ .virtual_files = &vfs_map },
        &sink,
    );
    try std.testing.expect(is_materialized);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), blob_store.blobs.items.len);

    // [4] Empty-slice non-null niche (`Option[str]::Some("") != Option[str]::None`) + atomics + SIMD + I/O in `MirVm`:
    const vm_showcase_src =
        \\pub fn run_phase7_intrinsics() -> i32 {
        \\    let some_empty: str? = .Some("");
        \\    let none_str: str? = .None;
        \\    if some_empty == none_str {
        \\        @panic("empty str collided with None");
        \\    }
        \\    var cell: i32 = 10;
        \\    @atomic_store(&mut cell, 25);
        \\    let prev_add = @atomic_rmw_add(&mut cell, 5);
        \\    let prev_sub = @atomic_rmw_sub(&mut cell, 3);
        \\    let prev_xchg = @atomic_rmw_xchg(&mut cell, 40);
        \\    let cx_pair = @atomic_cmpxchg(&mut cell, 40, 50);
        \\    @atomic_fence();
        \\    let cur_atomic = @atomic_load(&cell);
        \\    let vec_a = @simd_splat[[i32; 4]](3);
        \\    let vec_b: [i32; 4] = [1, 2, 3, 4];
        \\    let vec_sum = @simd_add(vec_a, vec_b);
        \\    let vec_diff = @simd_sub(vec_sum, [1, 1, 1, 1]);
        \\    let vec_prod = @simd_mul(vec_diff, [2, 2, 2, 2]);
        \\    let lane_total = @simd_reduce_add(vec_prod);
        \\    let has_reloaded = @poll_reload(&mut cell);
        \\    let wrote = @sys_write(1, "ok!");
        \\    if has_reloaded || !cx_pair.1 || prev_add != 25 || prev_sub != 30 || prev_xchg != 27 {
        \\        @trap();
        \\    }
        \\    return cur_atomic + lane_total + (wrote as i32);
        \\}
    ;
    var stdout_cap: std.ArrayListUnmanaged(u8) = .empty;
    defer stdout_cap.deinit(std.testing.allocator);
    var stderr_cap: std.ArrayListUnmanaged(u8) = .empty;
    defer stderr_cap.deinit(std.testing.allocator);

    const exec_out = try evalFunctionInOracleVm(
        std.testing.allocator,
        vm_showcase_src,
        "run_phase7_intrinsics",
        TargetSpec.X86_64_LINUX,
        &stdout_cap,
        &stderr_cap,
    );
    try std.testing.expect(exec_out.exit_code == null);
    // `cur_atomic = 50`; `vec_prod = [(4-1)*2, (5-1)*2, (6-1)*2, (7-1)*2] = [6,8,10,12]` -> `36`; `wrote = 3` -> `89`:
    try std.testing.expectEqual(@as(i64, 89), exec_out.slot.scalar_i64);
    try std.testing.expectEqualStrings("ok!", stdout_cap.items);

    // Verify `@sys_exit(7)` halts cleanly with `exited_with_code == 7`:
    const exit_src =
        \\pub fn do_exit() -> i32 {
        \\    @sys_exit(7);
        \\}
    ;
    const exit_res = try evalFunctionInOracleVm(
        std.testing.allocator,
        exit_src,
        "do_exit",
        TargetSpec.X86_64_LINUX,
        null,
        null,
    );
    try std.testing.expectEqual(@as(?i32, 7), exit_res.exit_code);

    // [5] Verify `Prune-02` `atomicWriteOutputFile` & lazy `ZigDriverLocator`:
    const out_path = ".zig-cache/test_phase7_atomic_write.bin";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, out_path) catch {};

    try corex.atomicWriteOutputFile(std.testing.io, std.testing.allocator, out_path, "first_payload");
    try corex.atomicWriteOutputFile(std.testing.io, std.testing.allocator, out_path, "replaced_payload_v2");
    const read_back = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        out_path,
        std.testing.allocator,
        .limited(1024),
    );
    defer std.testing.allocator.free(read_back);
    try std.testing.expectEqualStrings("replaced_payload_v2", read_back);

    var locator: codegen_abi.ZigDriverLocator = .{};
    defer locator.deinit(std.testing.allocator);
    const zig_exe = try locator.resolve(std.testing.io, std.testing.allocator, null);
    try std.testing.expect(zig_exe.len >= 3);
}

test "test_regression_sysv_eightbyte_span_c_union_abi_and_refined_niche_layout" {
    const src =
        \\pub type Pos1To10 = u32 is 1..=10;
        \\pub type Pos5To10 = u32 is 5..=10;
        \\@repr(C)
        \\pub struct FloatAndOptU32 {
        \\    pub head_f64: f64,
        \\    pub maybe_id: u32?,
        \\}
        \\@repr(C)
        \\pub union FloatIntUnion {
        \\    pub as_f32: f32,
        \\    pub as_u32: u32,
        \\}
    ;

    var tc_res = try corex.typecheckSource(std.testing.allocator, FileId.fromInt(9), src);
    defer tc_res.deinit();
    try std.testing.expect(!tc_res.diagnostics.hasErrors());

    const pos_1_10_ty = try lookupNamedTypeId(&tc_res.symbol_table, "Pos1To10");
    const pos_5_10_ty = try lookupNamedTypeId(&tc_res.symbol_table, "Pos5To10");
    const float_opt_ty = try lookupNamedTypeId(&tc_res.symbol_table, "FloatAndOptU32");
    const union_ty = try lookupNamedTypeId(&tc_res.symbol_table, "FloatIntUnion");

    var res_linux = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.X86_64_LINUX,
    );
    defer res_linux.deinit();

    // [1] Refined scalar niches (`u32 is 1..=10` and `u32 is 5..=10`) pack `Option` in `4B` at `invalid_first == 0`.
    const opt_1_10 = try tc_res.type_pool.internOptional(pos_1_10_ty);
    const opt_5_10 = try tc_res.type_pool.internOptional(pos_5_10_ty);
    const lay_1_10 = try res_linux.resolveType(opt_1_10);
    const lay_5_10 = try res_linux.resolveType(opt_5_10);
    try std.testing.expectEqual(@as(u64, 4), lay_1_10.size_bytes);
    try std.testing.expectEqual(codegen_abi.SumReprKind.niche_single, lay_1_10.sum_repr);
    try std.testing.expectEqual(@as(u64, 0), res_linux.sum_details.get(opt_1_10.toU32()).?.niche.invalid_first);
    try std.testing.expectEqual(@as(u64, 4), lay_5_10.size_bytes);
    try std.testing.expectEqual(codegen_abi.SumReprKind.niche_single, lay_5_10.sum_repr);
    try std.testing.expectEqual(@as(u64, 0), res_linux.sum_details.get(opt_5_10.toU32()).?.niche.invalid_first);

    // [2] `SysV AMD64` (`x86_64-linux` `extern "C"`): `{ f64, u32? }` (`16B`) classifies as `(xmm_vec, gpr)`.
    var fn_sysv_span = try AbiClassifier.classifyFn(std.testing.allocator, &res_linux, .{
        .params = &.{ .{ .type_id = float_opt_ty }, .{ .type_id = union_ty } },
        .ret_ty = float_opt_ty,
        .is_extern_c = true,
    });
    defer fn_sysv_span.deinit(std.testing.allocator);
    try std.testing.expectEqual(AbiPassMode.direct_pair, fn_sysv_span.param_recipes[0].pass_mode);
    try std.testing.expectEqual(RegBank.xmm_vec, fn_sysv_span.param_recipes[0].bank_0);
    try std.testing.expectEqual(RegBank.gpr, fn_sysv_span.param_recipes[0].bank_1);
    try std.testing.expectEqual(AbiPassMode.direct_pair, fn_sysv_span.ret_recipe.pass_mode);
    try std.testing.expectEqual(RegBank.xmm_vec, fn_sysv_span.ret_recipe.bank_0);
    try std.testing.expectEqual(RegBank.gpr, fn_sysv_span.ret_recipe.bank_1);

    // [3] C `union { f32, u32 }` merges eightbyte classes (`INTEGER` wins over `SSE`) and is NOT an `AAPCS64` HFA.
    try std.testing.expectEqual(AbiPassMode.direct_scalar, fn_sysv_span.param_recipes[1].pass_mode);
    try std.testing.expectEqual(RegBank.gpr, fn_sysv_span.param_recipes[1].bank_0);

    var res_arm_mac = TypeLayoutResolver.init(
        std.testing.allocator,
        &tc_res.type_pool,
        &tc_res.symbol_table,
        TargetSpec.AARCH64_MACOS,
    );
    defer res_arm_mac.deinit();
    var fn_arm_union = try AbiClassifier.classifyFn(std.testing.allocator, &res_arm_mac, .{
        .params = &.{.{ .type_id = union_ty }},
        .ret_ty = union_ty,
        .is_extern_c = true,
    });
    defer fn_arm_union.deinit(std.testing.allocator);
    try std.testing.expectEqual(AbiPassMode.direct_scalar, fn_arm_union.param_recipes[0].pass_mode);
    try std.testing.expectEqual(RegBank.gpr, fn_arm_union.param_recipes[0].bank_0);
    try std.testing.expectEqual(AbiPassMode.direct_scalar, fn_arm_union.ret_recipe.pass_mode);
    try std.testing.expectEqual(RegBank.gpr, fn_arm_union.ret_recipe.bank_0);
}

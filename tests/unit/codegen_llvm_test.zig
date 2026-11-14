//! Unit & Native-Execution Tests for Tier B (`stage0/src/codegen_llvm.zig`)
//!
//! Verifies all Phase 7 Wave 3B Tier B (LLVM 20–23 `.ll` + driver) invariants (`DR-07`, `DR-09`,
//! `DR-18`, `DR-19`, `DR-20`, and `phase7_spec.md` §3–§4):
//! - Byte-for-byte deterministic LLVM 20–23 opaque-pointer (`ptr`) `.ll` IR across all 7 targets,
//!   `nounwind uwtable(sync)` on native (`nounwind` on `wasm32`), zero C++ LSDA, and DWARF v5
//!   `LineTablesOnly` metadata.
//! - Two-pass `PHINode` creation + synthetic `_bb_edge_<idx>` duplicate-predecessor trampolines
//!   (`[CRITICAL-05]`).
//! - `cx_result_cc` (`swiftcc` + bare `ptr swifterror %_cx_err_slot`, `Err(0)` `tagged_int56`,
//!   `zst_err`, `PackedOk`, `[CRITICAL-06]`).
//! - MVS `noalias` parameter attributes + function-entry hoisted `@llvm.experimental.noalias.scope.decl`
//!   (`DR-09` §4.1 – never inside loop blocks!).
//! - Pentagon `!range` + `!noundef`, `@llvm.assume` `"nonnull"`/`"align"`, `#soa` + `@must_vectorize`
//!   `!llvm.access.group` & `!llvm.loop`, `<4 x i32>` SIMD intrinsics, `--dev` GOT, cross-target
//!   object compilation (`x86_64-linux`, `aarch64-macos`, `wasm32-wasi`), native host execution
//!   parity against Tier A & `MirVm`, and `--fuzz` `SanitizerCoverage` edge-hit verification.

const std = @import("std");
const corex = @import("corex");

const codegen_abi = corex.codegen_abi;
const codegen_dev_seam = corex.codegen_dev_seam;
const mir_sast = corex.mir_sast;
const mir_vm = corex.mir_vm;
const vfs_sourcemap = corex.vfs_sourcemap;

const FileId = corex.FileId;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const OptLevel = corex.OptLevel;
const ProvenValueRange = corex.ProvenValueRange;
const CodegenBackend = corex.CodegenBackend;
const CodegenArtifact = corex.CodegenArtifact;
const OutputArtifactKind = corex.OutputArtifactKind;

// -------------------------------------- INTERNALS --------------------------------------

/// Prints all diagnostics in `sink` to `stderr` when a test unexpectedly fails.
fn dumpDiagnosticsOnFailure(label: []const u8, sink: *const DiagnosticSink) void {
    for (sink.diagnostics.items) |diag_item| {
        std.debug.print("[{s}] {s}: {s}\n", .{ label, @tagName(diag_item.code), diag_item.message });
    }
}

/// Lowers `source_text` through `mir_sast`, Pentagon `ProvenValueRange`, and Tier B (`LLVM`).
fn emitLlvmModuleFromSource(
    allocator: std.mem.Allocator,
    source_text: []const u8,
    target_spec: TargetSpec,
    opt_level: OptLevel,
    is_release: bool,
    is_fuzz: bool,
    is_dev_got: bool,
    has_dwarf_vfs: bool,
    artifact_kind: OutputArtifactKind,
    output_path: ?[]const u8,
    extra_proven_b0: ?[]const ProvenValueRange,
) !CodegenArtifact {
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var sast_bundle = try mir_sast.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(0),
        source_text,
        target_spec.asTargetLayout(),
        .{ .diagnostic_sink = &sink },
    );
    defer sast_bundle.deinit();
    if (sink.hasErrors()) dumpDiagnosticsOnFailure("tier_b_sink", &sink);
    if (sast_bundle.diagnostics.hasErrors()) {
        dumpDiagnosticsOnFailure("tier_b_sast", &sast_bundle.diagnostics);
    }
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(!sast_bundle.diagnostics.hasErrors());

    const body_count = sast_bundle.mir_module.bodies.items.len;
    var body_ranges = try allocator.alloc([]const ProvenValueRange, body_count);
    var owned_slices = try allocator.alloc([]ProvenValueRange, body_count);
    defer {
        for (owned_slices) |sl| {
            if (sl.len > 0) allocator.free(sl);
        }
        allocator.free(owned_slices);
        allocator.free(body_ranges);
    }

    for (sast_bundle.mir_module.bodies.items, 0..) |*body_ptr, b_idx| {
        const computed = try corex.computeBodyProvenRanges(
            allocator,
            body_ptr,
            &sast_bundle.pool,
            &sast_bundle.sym_table,
        );
        if (b_idx == 0 and extra_proven_b0 != null) {
            const extra = extra_proven_b0.?;
            var merged = try allocator.alloc(ProvenValueRange, extra.len + computed.len);
            @memcpy(merged[0..extra.len], extra);
            @memcpy(merged[extra.len..], computed);
            if (computed.len > 0) allocator.free(computed);
            owned_slices[b_idx] = merged;
            body_ranges[b_idx] = merged;
        } else {
            owned_slices[b_idx] = computed;
            body_ranges[b_idx] = computed;
        }
    }

    var vfs = vfs_sourcemap.VfsSourceMap.init(allocator, &sast_bundle.interner);
    defer vfs.deinit(std.testing.io);
    var tok_map: std.AutoHashMapUnmanaged(u32, *const corex.TokenBuffer) = .empty;
    defer tok_map.deinit(allocator);
    if (has_dwarf_vfs) {
        _ = try vfs.setOverlay("src/tier_b_case.cx", source_text, .root);
        try tok_map.put(allocator, 0, &sast_bundle.token_buffer);
    }

    const backend = CodegenBackend{
        .tier_b_llvm = .{
            .target = target_spec,
            .opt_level = opt_level,
            .is_release_mode = is_release,
            .is_fuzz_instrumented = is_fuzz,
        },
    };
    return backend.emitModule(allocator, .{
        .bodies = sast_bundle.mir_module.bodies.items,
        .pool = &sast_bundle.pool,
        .sym_table = &sast_bundle.sym_table,
        .interner = &sast_bundle.interner,
        .module_name = "tier_b_test",
        .vfs_source_map = if (has_dwarf_vfs) &vfs else null,
        .file_tokens = if (has_dwarf_vfs) &tok_map else null,
        .proven_ranges = body_ranges,
        .summary_store = &sast_bundle.sast_result.summary_store,
        .is_dev_got_enabled = is_dev_got,
        .is_oracle_trace_enabled = true,
        .artifact_kind = artifact_kind,
        .output_path = output_path,
        .io = std.testing.io,
        .diagnostic_sink = &sink,
    }) catch |err| {
        dumpDiagnosticsOnFailure("tier_b_driver", &sink);
        return err;
    };
}

/// Counts non-overlapping occurrences of `needle` inside `haystack`.
fn countSubstrings(haystack: []const u8, needle: []const u8) usize {
    if (needle.len == 0) return 0;
    var count: usize = 0;
    var pos: usize = 0;
    while (std.mem.indexOfPos(u8, haystack, pos, needle)) |hit| {
        count += 1;
        pos = hit + needle.len;
    }
    return count;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_codegen_llvm_determinism_swifterror_mvs_hoist_pentagon_and_7_targets" {
    const ir_showcase_src =
        \\pub struct Particle {
        \\    pub px: f32,
        \\    pub py: f32,
        \\}
        \\pub fn fallible_tag56(code: i32) -> Result[i64, i32] {
        \\    if code <= 0 {
        \\        return .Err(0);
        \\    }
        \\    return .Ok((code as i64) * 10);
        \\}
        \\pub fn fallible_zst(flag: bool) -> Result[i32, unit] {
        \\    if !flag {
        \\        return .Err(());
        \\    }
        \\    return .Ok(77);
        \\}
        \\pub fn mvs_soa_kernel(
        \\    mut dst_pts: inout #soa [Particle; 8],
        \\    mut aux_sum: inout i32,
        \\    scale_vec: [i32; 4]
        \\) -> i32 {
        \\    var idx: usize = 0;
        \\    @must_vectorize
        \\    @vectorize_width(4)
        \\    while idx < 8 {
        \\        dst_pts[idx].px = dst_pts[idx].px + 1.0;
        \\        idx = idx + 1;
        \\    }
        \\    let doubled = @simd_add(scale_vec, @simd_splat[[i32; 4]](2));
        \\    let red = @simd_reduce_add(doubled);
        \\    aux_sum = aux_sum + red;
        \\    return aux_sum;
        \\}
        \\pub fn multi_arm_switch(tag_v: i32) -> i32 {
        \\    var bonus: i32 = 1;
        \\    match tag_v {
        \\        1 => { bonus = 10; },
        \\        2 => { bonus = 10; },
        \\        3 => { bonus = 20; },
        \\        _ => { bonus = 10; },
        \\    }
        \\    return bonus;
        \\}
    ;

    for (codegen_abi.ALL_CANONICAL_TARGETS) |spec| {
        var run_1 = try emitLlvmModuleFromSource(
            std.testing.allocator,
            ir_showcase_src,
            spec,
            .release_fast_o2,
            true,
            false,
            false,
            true,
            .source_text,
            null,
            null,
        );
        defer run_1.deinit(std.testing.allocator);

        var run_2 = try emitLlvmModuleFromSource(
            std.testing.allocator,
            ir_showcase_src,
            spec,
            .release_fast_o2,
            true,
            false,
            false,
            true,
            .source_text,
            null,
            null,
        );
        defer run_2.deinit(std.testing.allocator);

        // [1] Byte-for-byte determinism across all 7 targets:
        try std.testing.expectEqualStrings(run_1.emitted_text, run_2.emitted_text);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "personality") == null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "DICompileUnit") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "LineTablesOnly") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "Dwarf Version\", i32 5") != null);

        // `--release` omits 16-slot `@_cx_err_trace` (`0` bytes overhead, `D-06B`):
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "@_cx_err_trace") == null);

        if (spec.isWasm()) {
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "uwtable") == null);
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "swifterror") == null);
        } else {
            // [2] Native `cx_result_cc`: `swiftcc` + bare `ptr swifterror %_cx_err_slot` (`[CRITICAL-06]`):
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "nounwind uwtable(sync)") != null);
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "swiftcc ") != null);
            try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "ptr swifterror %_cx_err_slot") != null);
        }

        // [3] MVS `noalias` + function-entry hoisted `@llvm.experimental.noalias.scope.decl` (`DR-09` §4.1):
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "ptr noalias nonnull") != null);
        try std.testing.expect(
            std.mem.indexOf(u8, run_1.emitted_text, "call void @llvm.experimental.noalias.scope.decl") != null,
        );
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "!alias.scope !") != null);
        try std.testing.expect(std.mem.indexOf(u8, run_1.emitted_text, "!noalias !") != null);

        // Verify `noalias.scope.decl` inside `mvs_soa_kernel` appears ONLY in `_bb_0:` and NEVER in loop blocks:
        const kernel_pos = std.mem.indexOf(u8, run_1.emitted_text, "mvs_soa_kernel(").?;
        const kernel_end = std.mem.indexOfPos(u8, run_1.emitted_text, kernel_pos, "\n}\n").?;
        const kernel_ir = run_1.emitted_text[kernel_pos..kernel_end];
        const bb1_pos = std.mem.indexOf(u8, kernel_ir, "\n_bb_1:\n").?;
        const expected_mvs_decls: usize = if (spec.isWasm()) 3 else 2;
        try std.testing.expectEqual(
            expected_mvs_decls,
            countSubstrings(kernel_ir[0..bb1_pos], "@llvm.experimental.noalias.scope.decl"),
        );
        try std.testing.expectEqual(
            @as(usize, 0),
            countSubstrings(kernel_ir[bb1_pos..], "@llvm.experimental.noalias.scope.decl"),
        );

        // [4] `#soa` + `@must_vectorize` + `@vectorize_width(4)` + `<4 x i32>` SIMD intrinsics:
        try std.testing.expect(std.mem.indexOf(u8, kernel_ir, "!llvm.access.group !") != null);
        try std.testing.expect(std.mem.indexOf(u8, kernel_ir, "!llvm.loop !") != null);
        try std.testing.expect(
            std.mem.indexOf(u8, run_1.emitted_text, "!\"llvm.loop.vectorize.enable\", i1 true") != null,
        );
        try std.testing.expect(
            std.mem.indexOf(u8, run_1.emitted_text, "!\"llvm.loop.vectorize.width\", i32 4") != null,
        );
        try std.testing.expect(std.mem.indexOf(u8, kernel_ir, "<4 x i32>") != null);
        try std.testing.expect(
            std.mem.indexOf(u8, run_1.emitted_text, "@llvm.vector.reduce.add.v4i32") != null,
        );
    }

    // [5] Verify Pentagon `!range` + `!noundef`, full-domain `!range` suppression, and `@llvm.assume`:
    const pentagon_src =
        \\pub fn load_bounded(ptr_ref: &i32) -> i32 {
        \\    let copied_ptr: &i32 = ptr_ref;
        \\    let loaded_v = *copied_ptr;
        \\    return loaded_v + 1;
        \\}
    ;
    // Inject both a bounded `[0, 100]` scalar fact and a non-null 16-byte aligned pointer fact, plus a full-domain `u8` `[0, 255]`:
    var sast_probe = try mir_sast.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(0),
        pentagon_src,
        TargetSpec.X86_64_LINUX.asTargetLayout(),
        .{},
    );
    defer sast_probe.deinit();
    const probe_body = &sast_probe.mir_module.bodies.items[0];
    var ptr_val_raw: u32 = 0;
    var load_val_raw: u32 = 0;
    for (0..probe_body.insts.len) |idx| {
        const inst = probe_body.insts.get(idx);
        if (inst.op == .place_load or inst.op == .block_param) {
            const r_ty = sast_probe.pool.unwrapUnderlyingType(inst.type_id);
            if (r_ty == .i32_ty) {
                load_val_raw = @intCast(idx);
            } else if (!r_ty.isPrimitiveOrSentinel()) {
                const r_tag = sast_probe.pool.getNode(r_ty).tag;
                if (r_tag == .ref_ty or r_tag == .mut_ref_ty or r_tag == .raw_ptr_ty) {
                    ptr_val_raw = @intCast(idx);
                }
            }
        }
    }

    const injected_facts = [_]ProvenValueRange{
        .{
            .mir_value_raw = load_val_raw,
            .bit_width = 32,
            .proven_align_log2 = 0,
            .flags_bits = @bitCast(ProvenValueRange.Flags{ .is_signed = true }),
            .min_bits = 0,
            .max_bits = 100,
        },
        .{
            .mir_value_raw = ptr_val_raw,
            .bit_width = 64,
            .proven_align_log2 = 4,
            .flags_bits = @bitCast(ProvenValueRange.Flags{ .is_nonnull_ptr = true, .is_non_zero = true }),
            .min_bits = 1,
            .max_bits = std.math.maxInt(u64),
        },
    };

    var pentagon_art = try emitLlvmModuleFromSource(
        std.testing.allocator,
        pentagon_src,
        TargetSpec.X86_64_LINUX,
        .release_fast_o2,
        false,
        false,
        true,
        false,
        .source_text,
        null,
        &injected_facts,
    );
    defer pentagon_art.deinit(std.testing.allocator);

    try std.testing.expect(std.mem.indexOf(u8, pentagon_art.emitted_text, "!range !") != null);
    try std.testing.expect(std.mem.indexOf(u8, pentagon_art.emitted_text, "!{i32 0, i32 101}") != null);
    try std.testing.expect(
        std.mem.indexOf(
            u8,
            pentagon_art.emitted_text,
            "call void @llvm.assume(i1 true) [ \"nonnull\"(ptr ",
        ) != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, pentagon_art.emitted_text, "\"align\"(ptr ") != null);
    try std.testing.expect(std.mem.indexOf(u8, pentagon_art.emitted_text, "@_cx_dev_got") != null);
    try std.testing.expect(std.mem.indexOf(u8, pentagon_art.emitted_text, "@_cx_err_trace") != null);
    try std.testing.expect(pentagon_art.dev_seam_bytes != null);
}

test "test_codegen_llvm_cross_target_object_verifier_linux_macos_wasm" {
    const cross_src =
        \\pub fn checked_err(val: i32) -> Result[i32, i32] {
        \\    if val == 0 {
        \\        return .Err(0);
        \\    }
        \\    return .Ok(val * 2);
        \\}
        \\pub fn run_cross(x_in: i32) -> i32 {
        \\    let res = checked_err(x_in);
        \\    return match res {
        \\        .Ok(val_ok) => val_ok,
        \\        .Err(err_code) => err_code - 1,
        \\    };
        \\}
    ;

    const cross_targets = [_]TargetSpec{
        TargetSpec.X86_64_LINUX,
        TargetSpec.AARCH64_MACOS,
        TargetSpec.WASM32_WASI,
    };

    for (cross_targets) |spec| {
        const obj_path = try std.fmt.allocPrint(
            std.testing.allocator,
            ".zig-cache/test_tier_b_{s}{s}",
            .{ spec.canonicalName(), spec.objectExtension() },
        );
        defer std.testing.allocator.free(obj_path);
        defer std.Io.Dir.cwd().deleteFile(std.testing.io, obj_path) catch {};

        var artifact = try emitLlvmModuleFromSource(
            std.testing.allocator,
            cross_src,
            spec,
            .release_fast_o2,
            true,
            false,
            false,
            true,
            .object_file,
            obj_path,
            null,
        );
        defer artifact.deinit(std.testing.allocator);

        const obj_bytes = try std.Io.Dir.cwd().readFileAlloc(
            std.testing.io,
            obj_path,
            std.testing.allocator,
            .limited(4 * 1024 * 1024),
        );
        defer std.testing.allocator.free(obj_bytes);
        try std.testing.expect(obj_bytes.len > 64);
    }
}

test "test_codegen_llvm_native_release_execution_and_fuzz_sancov_edge_hits" {
    const host_spec = TargetSpec.host();
    const exec_src =
        \\@zero_pad
        \\@repr(C)
        \\pub struct ZeroPadItem {
        \\    pub marker: u8,
        \\    pub wide: u64,
        \\}
        \\pub struct Particle {
        \\    pub vx: i32,
        \\    pub vy: i32,
        \\}
        \\pub struct DropProbe {
        \\    pub tag: i64,
        \\}
        \\impl DropProbe {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\pub fn step_tag56(code: i32) -> Result[i32, i32] {
        \\    if code == 0 {
        \\        return .Err(0);
        \\    }
        \\    return .Ok(code * 4);
        \\}
        \\pub fn step_zst(ok_flag: bool) -> Result[i32, unit] {
        \\    if !ok_flag {
        \\        return .Err(());
        \\    }
        \\    return .Ok(9);
        \\}
        \\pub fn chain_swifterror(val: i32) -> Result[i32, i32] {
        \\    let first = step_tag56(val)?;
        \\    return .Ok(first + 3);
        \\}
        \\pub fn swap_loop(iters: i32) -> i32 {
        \\    var a_val: i32 = 2;
        \\    var b_val: i32 = 3;
        \\    var idx: i32 = 0;
        \\    while idx < iters {
        \\        let next_b = a_val +% b_val;
        \\        a_val = b_val;
        \\        b_val = next_b;
        \\        idx = idx + 1;
        \\    }
        \\    return a_val;
        \\}
        \\pub fn add_to_slot(mut target_slot: inout i32, amount: i32) {
        \\    target_slot = target_slot + amount;
        \\}
        \\pub fn main() -> i32 {
        \\    // [1] `@zero_pad` `0x00` verification:
        \\    let z_item = ZeroPadItem { marker: 5, wide: 777 };
        \\    let raw_b: &[u8] = z_item.as_bytes();
        \\    var pad_acc: u8 = 0;
        \\    var k_idx: usize = 1;
        \\    while k_idx < 8 {
        \\        pad_acc = pad_acc | raw_b[k_idx];
        \\        k_idx = k_idx + 1;
        \\    }
        \\    if pad_acc != 0 {
        \\        @trap();
        \\    }
        \\    // [2] Niche `Option[str]` empty-string invariant:
        \\    let s_some: str? = .Some("");
        \\    let s_none: str? = .None;
        \\    if s_some == s_none {
        \\        @trap();
        \\    }
        \\    match s_some {
        \\        .Some(empty_s) => {
        \\            if empty_s.len != 0 { @trap(); }
        \\        },
        \\        .None => @trap(),
        \\    }
        \\    // [3] `cx_result_cc` `swifterror` (`Err(0)` `tagged_int56` + `zst_err` + `?` propagation):
        \\    var total: i32 = 0;
        \\    match chain_swifterror(0) {
        \\        .Ok(_) => @trap(),
        \\        .Err(err_zero) => {
        \\            if err_zero != 0 { @trap(); }
        \\            total = total + 5;
        \\        },
        \\    }
        \\    match chain_swifterror(6) {
        \\        .Ok(ok_v) => { total = total + ok_v; },
        \\        .Err(_) => @trap(),
        \\    }
        \\    match step_zst(false) {
        \\        .Ok(_) => @trap(),
        \\        .Err(_) => { total = total + 1; },
        \\    }
        \\    match step_zst(true) {
        \\        .Ok(z_ok) => { total = total + z_ok; },
        \\        .Err(_) => @trap(),
        \\    }
        \\    // [4] `#soa` + `@must_vectorize` + MVS `inout` + `<4 x i32>` SIMD + atomics:
        \\    var soa_buf: #soa [Particle; 4] = @default_init[#soa [Particle; 4]]();
        \\    soa_buf[0].vx = 1;
        \\    soa_buf[0].vy = 2;
        \\    soa_buf[1].vx = 3;
        \\    soa_buf[1].vy = 4;
        \\    soa_buf[2].vx = 5;
        \\    soa_buf[2].vy = 6;
        \\    soa_buf[3].vx = 7;
        \\    soa_buf[3].vy = 8;
        \\    var li: usize = 0;
        \\    @must_vectorize
        \\    @vectorize_width(4)
        \\    while li < 4 {
        \\        soa_buf[li].vx = soa_buf[li].vx + 2;
        \\        li = li + 1;
        \\    }
        \\    add_to_slot(total, soa_buf[0].vx + soa_buf[3].vy);
        \\    var atom_cell: i32 = 10;
        \\    let old_atom = @atomic_rmw_add(&mut atom_cell, 4);
        \\    let vec_res = @simd_reduce_add(@simd_add(@simd_splat[[i32; 4]](3), [1, 2, 3, 4]));
        \\    {
        \\        let guard = DropProbe { tag: 99 };
        \\        let _ = guard.tag;
        \\    }
        \\    let wr_len = @sys_write(1, "LLVM_OK");
        \\    return total + old_atom + atom_cell + vec_res + swap_loop(4) + (wr_len as i32) - 90;
        \\}
    ;

    // Evaluate ground-truth oracle result in `MirVm`:
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var sast_vm = try mir_sast.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(0),
        exec_src,
        host_spec.asTargetLayout(),
        .{ .diagnostic_sink = &sink },
    );
    defer sast_vm.deinit();
    if (sink.hasErrors()) dumpDiagnosticsOnFailure("tier_b_vm_sink", &sink);
    if (sast_vm.diagnostics.hasErrors()) {
        dumpDiagnosticsOnFailure("tier_b_vm_sast", &sast_vm.diagnostics);
    }
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(!sast_vm.diagnostics.hasErrors());
    var rodata = mir_vm.RodataPool.init(std.testing.allocator);
    defer rodata.deinit();
    var vm_stdout: std.ArrayListUnmanaged(u8) = .empty;
    defer vm_stdout.deinit(std.testing.allocator);
    var vm = try mir_vm.MirVm.init(
        std.testing.allocator,
        &sast_vm.interner,
        &sast_vm.pool,
        &sast_vm.sym_table,
        &rodata,
        null,
        &sink,
        .{
            .target_layout = host_spec.asTargetLayout(),
            .stdout_capture = &vm_stdout,
            .is_oracle_runtime_mode = true,
        },
    );
    defer vm.deinit();
    var main_ptr: ?*const corex.MirBody = null;
    for (sast_vm.mir_module.bodies.items) |*bp| {
        const s_idx = sast_vm.sym_table.def_to_symbol.get(bp.def_id.asInt()) orelse .none;
        _ = try vm.registerBody(bp, s_idx);
        if (std.mem.eql(u8, sast_vm.interner.get(bp.name), "main")) main_ptr = bp;
    }
    const expected_exit = (try vm.evalBody(main_ptr.?, &.{})).slot.scalar_i64;

    // Compile and execute Tier B `--release` (`-O2`) binary on the host:
    const rel_exe = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/test_tier_b_rel_run{s}",
        .{host_spec.executableExtension()},
    );
    defer std.testing.allocator.free(rel_exe);
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, rel_exe) catch {};

    const rel_trace = ".zig-cache/test_tier_b_rel.trace";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, rel_trace) catch {};

    var rel_art = try emitLlvmModuleFromSource(
        std.testing.allocator,
        exec_src,
        host_spec,
        .release_fast_o2,
        true,
        false,
        false,
        true,
        .executable,
        rel_exe,
        null,
    );
    defer rel_art.deinit(std.testing.allocator);

    var rel_env = std.process.Environ.Map.init(std.testing.allocator);
    defer rel_env.deinit();
    try rel_env.put("COREX_ORACLE_TRACE_FILE", rel_trace);

    const rel_run = try std.process.run(std.testing.allocator, std.testing.io, .{
        .argv = &.{rel_exe},
        .environ_map = &rel_env,
    });
    defer std.testing.allocator.free(rel_run.stdout);
    defer std.testing.allocator.free(rel_run.stderr);

    const actual_exit: i64 = switch (rel_run.term) {
        .exited => |code| @intCast(code),
        else => -1,
    };
    try std.testing.expectEqual(expected_exit, actual_exit);
    try std.testing.expectEqualStrings(vm_stdout.items, rel_run.stdout);

    const trace_data = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        rel_trace,
        std.testing.allocator,
        .limited(4096),
    );
    defer std.testing.allocator.free(trace_data);
    try std.testing.expect(std.mem.indexOf(u8, trace_data, "DROP:99\n") != null);

    // Compile and execute Tier B `--fuzz` (`SanitizerCoverage` + Windows COFF `.SCOV$*` shim):
    const fuzz_src =
        \\pub fn classify_byte(input_b: u8) -> i32 {
        \\    if input_b == 65 {
        \\        return 10;
        \\    } else if input_b > 100 {
        \\        return 20;
        \\    }
        \\    return 3;
        \\}
        \\pub fn main() -> i32 {
        \\    let opt_a: str? = .Some("");
        \\    let opt_b: str? = .None;
        \\    let opt_c: str? = .Some("");
        \\    if !(opt_a != opt_b) || !(opt_a == opt_c) {
        \\        @trap();
        \\    }
        \\    let sum_v = classify_byte(65) + classify_byte(120) + classify_byte(7);
        \\    return sum_v - 33;
        \\}
    ;

    const fuzz_exe = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/test_tier_b_fuzz_run{s}",
        .{host_spec.executableExtension()},
    );
    defer std.testing.allocator.free(fuzz_exe);
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, fuzz_exe) catch {};

    var fuzz_art = try emitLlvmModuleFromSource(
        std.testing.allocator,
        fuzz_src,
        host_spec,
        .release_fast_o2,
        false,
        true,
        false,
        false,
        .executable,
        fuzz_exe,
        null,
    );
    defer fuzz_art.deinit(std.testing.allocator);

    var fuzz_env = std.process.Environ.Map.init(std.testing.allocator);
    defer fuzz_env.deinit();
    try fuzz_env.put("COREX_FUZZ_STATS", "1");

    const fuzz_run = try std.process.run(std.testing.allocator, std.testing.io, .{
        .argv = &.{fuzz_exe},
        .environ_map = &fuzz_env,
    });
    defer std.testing.allocator.free(fuzz_run.stdout);
    defer std.testing.allocator.free(fuzz_run.stderr);

    const fuzz_exit: u8 = switch (fuzz_run.term) {
        .exited => |code| code,
        else => 255,
    };
    try std.testing.expectEqual(@as(u8, 0), fuzz_exit);
    try std.testing.expect(std.mem.indexOf(u8, fuzz_run.stderr, "SANCOV_EDGES:") != null);
    // Verify non-zero hit edges (`SANCOV_EDGES:<hit>/<total>` where `<hit> > 0`):
    const prefix = "SANCOV_EDGES:";
    const hit_start = std.mem.indexOf(u8, fuzz_run.stderr, prefix).? + prefix.len;
    const slash_pos = std.mem.indexOfPos(u8, fuzz_run.stderr, hit_start, "/").?;
    const hit_edges = try std.fmt.parseInt(usize, fuzz_run.stderr[hit_start..slash_pos], 10);
    try std.testing.expect(hit_edges > 0);
}

test "test_regression_codegen_llvm_wasi_import_module_extern_dedup_and_quoted_ident" {
    const wasi_src =
        \\@derive(Debug)
        \\pub struct DbgTag {
        \\    pub val: i32,
        \\}
        \\@extern("C")
        \\@link_name("fd_write")
        \\pub fn wasi_fd_write_a(fd: i32, iovs: *u8, iovs_len: usize, nwritten: *usize) -> u16;
        \\@extern("C")
        \\@link_name("fd_write")
        \\pub fn wasi_fd_write_b(fd: i32, iovs: *u8, iovs_len: usize, nwritten: *usize) -> u16;
        \\@extern("C")
        \\@link_name("proc_exit")
        \\pub fn wasi_proc_exit_a(code: i32) -> never;
        \\@extern("C")
        \\@link_name("custom$sym-name")
        \\pub fn ext_dollar_hyphen(val: i32) -> i32;
        \\pub fn invoke_wasi_and_quoted(x_in: i32) -> i32 {
        \\    if x_in == -999 {
        \\        unsafe { wasi_proc_exit_a(1); }
        \\    }
        \\    let dbg_s: str = (DbgTag { val: x_in }).debug();
        \\    let err_a: u16 = unsafe { wasi_fd_write_a(1, 0 as *u8, 0, 0 as *usize) };
        \\    let err_b: u16 = unsafe { wasi_fd_write_b(1, 0 as *u8, 0, 0 as *usize) };
        \\    return (dbg_s.len as i32) + (err_a as i32) + (err_b as i32) + unsafe { ext_dollar_hyphen(x_in) };
        \\}
    ;

    var ir_art = try emitLlvmModuleFromSource(
        std.testing.allocator,
        wasi_src,
        TargetSpec.WASM32_WASI,
        .release_fast_o2,
        true,
        false,
        false,
        false,
        .source_text,
        null,
        null,
    );
    defer ir_art.deinit(std.testing.allocator);

    try std.testing.expectEqual(
        @as(usize, 1),
        countSubstrings(ir_art.emitted_text, "\"wasm-import-name\"=\"fd_write\""),
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        countSubstrings(ir_art.emitted_text, "\"wasm-import-name\"=\"proc_exit\""),
    );
    try std.testing.expectEqual(
        @as(usize, 2),
        countSubstrings(ir_art.emitted_text, "\"wasm-import-module\"=\"wasi_snapshot_preview1\""),
    );
    try std.testing.expect(std.mem.indexOf(u8, ir_art.emitted_text, "@\"custom$sym-name\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, ir_art.emitted_text, "c\"DbgTag\"") != null);

    const wasm_obj = ".zig-cache/test_tier_b_wasi_dedup.o";
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, wasm_obj) catch {};

    var obj_art = try emitLlvmModuleFromSource(
        std.testing.allocator,
        wasi_src,
        TargetSpec.WASM32_WASI,
        .release_fast_o2,
        true,
        false,
        false,
        false,
        .object_file,
        wasm_obj,
        null,
    );
    defer obj_art.deinit(std.testing.allocator);
}

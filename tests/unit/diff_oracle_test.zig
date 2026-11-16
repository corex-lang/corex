//! Unit & End-to-End Tests for `diff_oracle.zig` and Phase 7 CLI (`tests/unit/diff_oracle_test.zig`)
//!
//! Verifies 4-tier differential parity (`MirVm --dev`, `MirVm --release`, Tier A `-ofmt=c`, and
//! Tier B `LLVM -O2` per `DR-20` `D-07A`) across native/C structs, `@zero_pad`, `bit_field`, niche
//! `Option`/`Result` (`str?` `.Some("")` vs `.None`, `cx_result_cc` `?` + `Err(0)`), `defer` /
//! `errdefer` / `AutoDrop` `@drop_trace`, `#soa` + `@must_vectorize`, `@local` closures, atomics,
//! SIMD (`[i32; 4]` & `[f32; 4]` in-order horizontal reduction), `@sys_write`, `@sys_exit`, and
//! deliberate runtime traps (`@panic`, checked integer overflow).
//!
//! Also exercises end-to-end CLI workflows via `router.runCli`: `corex build`, `corex build
//! -ofmt=c --emit-c`, `corex build --emit-llvm`, `corex build --fuzz` (`COREX_FUZZ_STATS=1`),
//! `corex run -- <args…>`, `corex test --diff-backends`, and `E0006` invalid `--target`.

const std = @import("std");
const corex = @import("corex");

const router = corex.router;
const diff_oracle = corex.diff_oracle;
const DiagnosticCode = corex.DiagnosticCode;
const TargetSpec = corex.TargetSpec;
const OracleTierOutcome = corex.OracleTierOutcome;

// --------------------------------------- CONSTS ----------------------------------------

/// Showcase `.cx` source exercising structs, `@repr(C)`, `@zero_pad`, `bit_field`, niche `Option`, and `Result`.
const LAYOUT_NICHE_RESULT_SRC =
    "//! 4-Tier Struct Layout, Bitfield, Niche Option, and Result `?` Oracle Case\n" ++
    "pub struct ReorderedNative {\n" ++
    "    pub tag_byte: u8,\n" ++
    "    pub wide_val: i64,\n" ++
    "    pub mid_val: i32,\n" ++
    "}\n" ++
    "\n" ++
    "@repr(C)\n" ++
    "@zero_pad\n" ++
    "pub struct WireHeader {\n" ++
    "    pub opcode: u8,\n" ++
    "    pub length: u32,\n" ++
    "}\n" ++
    "\n" ++
    "pub bit_field PacketFlags: u16 {\n" ++
    "    pub version: u8 | 4,\n" ++
    "    pub is_urgent: bool | 1,\n" ++
    "    pub channel: u8 | 5,\n" ++
    "    pub reserved_bits: u8 | 6,\n" ++
    "}\n" ++
    "\n" ++
    "pub fn classify_text_opt(maybe_label: str?) -> i32 {\n" ++
    "    return match maybe_label {\n" ++
    "        .Some(label_str) => (label_str.len() as i32) + 10,\n" ++
    "        .None => -1,\n" ++
    "    };\n" ++
    "}\n" ++
    "\n" ++
    "pub fn fallible_step(input_code: i32) -> i32!i32 {\n" ++
    "    if input_code == 0 {\n" ++
    "        return .Err(0);\n" ++
    "    }\n" ++
    "    if input_code < 0 {\n" ++
    "        return .Err(-7);\n" ++
    "    }\n" ++
    "    return .Ok(input_code * 3);\n" ++
    "}\n" ++
    "\n" ++
    "pub fn propagate_chain(seed_code: i32) -> i32!i32 {\n" ++
    "    let first_ok: i32 = fallible_step(seed_code)?;\n" ++
    "    let second_ok: i32 = fallible_step(first_ok - 3)?;\n" ++
    "    return .Ok(first_ok + second_ok);\n" ++
    "}\n" ++
    "\n" ++
    "pub fn main() -> i32 {\n" ++
    "    let nat = ReorderedNative { tag_byte: 5, wide_val: 100, mid_val: 20 };\n" ++
    "    let wire = WireHeader { opcode: 3, length: 12 };\n" ++
    "    var flags = PacketFlags { version: 6, is_urgent: true, channel: 9, reserved_bits: 0 };\n" ++
    "    flags.channel = 11;\n" ++
    "    let flag_score: i32 = (flags.version as i32) + (flags.channel as i32) +\n" ++
    "        (if flags.is_urgent { 4 } else { 0 });\n" ++
    "\n" ++
    "    let empty_some_score: i32 = classify_text_opt(.Some(\"\"));\n" ++
    "    let non_empty_score: i32 = classify_text_opt(.Some(\"cx\"));\n" ++
    "    let none_score: i32 = classify_text_opt(.None);\n" ++
    "\n" ++
    "    let ok_res: i32 = match propagate_chain(2) {\n" ++
    "        .Ok(total_v) => total_v,\n" ++
    "        .Err(err_v) => err_v,\n" ++
    "    };\n" ++
    "    let zero_err_res: i32 = match propagate_chain(1) {\n" ++
    "        .Ok(_) => 999,\n" ++
    "        .Err(err_zero) => err_zero + 8,\n" ++
    "    };\n" ++
    "\n" ++
    "    return (nat.tag_byte as i32) + (nat.wide_val as i32) + nat.mid_val +\n" ++
    "        (wire.opcode as i32) + (wire.length as i32) + flag_score +\n" ++
    "        empty_some_score + non_empty_score + none_score + ok_res + zero_err_res;\n" ++
    "}\n";

/// Showcase `.cx` source exercising `Drop`, conditional moves, `defer`, and `errdefer` LIFO `@drop_trace`.
const DROP_DEFER_ERRDEFER_SRC =
    "//! 4-Tier AutoDrop, Conditional Move, `defer`, and `errdefer` LIFO Oracle Case\n" ++
    "pub trait Drop {\n" ++
    "    fn drop(&mut self);\n" ++
    "}\n" ++
    "\n" ++
    "pub struct ScopeToken {\n" ++
    "    pub id: i64,\n" ++
    "}\n" ++
    "\n" ++
    "impl Drop for ScopeToken {\n" ++
    "    pub fn drop(&mut self) {\n" ++
    "        @drop_trace(self.id);\n" ++
    "    }\n" ++
    "}\n" ++
    "\n" ++
    "pub fn consume_token(token_val: own ScopeToken) -> i64 {\n" ++
    "    @drop_trace(token_val.id + 1000);\n" ++
    "    return token_val.id;\n" ++
    "}\n" ++
    "\n" ++
    "pub fn run_transaction(should_fail: bool, should_move: bool) -> i32!i32 {\n" ++
    "    let first_tok = ScopeToken { id: 10 };\n" ++
    "    defer { @drop_trace(90); }\n" ++
    "    errdefer { @drop_trace(77); }\n" ++
    "    let second_tok = ScopeToken { id: 20 };\n" ++
    "    var acc: i32 = first_tok.id as i32;\n" ++
    "    if should_move {\n" ++
    "        acc = acc + (consume_token(own second_tok) as i32);\n" ++
    "    }\n" ++
    "    if should_fail {\n" ++
    "        return .Err(5);\n" ++
    "    }\n" ++
    "    return .Ok(acc + 3);\n" ++
    "}\n" ++
    "\n" ++
    "pub fn main() -> i32 {\n" ++
    "    let ok_score: i32 = match run_transaction(false, true) {\n" ++
    "        .Ok(val) => val,\n" ++
    "        .Err(err_code) => err_code,\n" ++
    "    };\n" ++
    "    let err_score: i32 = match run_transaction(true, false) {\n" ++
    "        .Ok(val) => val,\n" ++
    "        .Err(err_code) => err_code,\n" ++
    "    };\n" ++
    "    return ok_score + err_score;\n" ++
    "}\n";

/// Showcase `.cx` source exercising `#soa`, `@must_vectorize`, `inout` MVS, and `@local` closures.
const SOA_VECTORIZE_CLOSURE_SRC =
    "//! 4-Tier `#soa` Column Array, `@must_vectorize`, `inout` MVS, and Closure Oracle Case\n" ++
    "pub struct Particle {\n" ++
    "    pub pos_x: i32,\n" ++
    "    pub vel_x: i32,\n" ++
    "    pub mass: i32,\n" ++
    "}\n" ++
    "\n" ++
    "pub fn step_value(current: &mut i32, delta: i32) {\n" ++
    "    current.* = current.* + delta;\n" ++
    "}\n" ++
    "\n" ++
    "pub fn scale_lane(val: i32) -> i32 {\n" ++
    "    return val * 2;\n" ++
    "}\n" ++
    "\n" ++
    "pub fn apply_fn_ptr(seed: i32, mapper: fn(i32) -> i32) -> i32 {\n" ++
    "    return mapper(seed);\n" ++
    "}\n" ++
    "\n" ++
    "pub fn main() -> i32 {\n" ++
    "    var swarm: #soa [Particle; 4] = @default_init[#soa [Particle; 4]]();\n" ++
    "    swarm[0].pos_x = 1;\n" ++
    "    swarm[1].vel_x = 5;\n" ++
    "    swarm[2].mass = 9;\n" ++
    "    swarm[3].pos_x = 10;\n" ++
    "    var lanes_a: [i32; 4] = [3, 6, 9, 12];\n" ++
    "    let lanes_b: [i32; 4] = [1, 2, 3, 4];\n" ++
    "    var idx: usize = 0;\n" ++
    "    @must_vectorize\n" ++
    "    while idx < 4 {\n" ++
    "        lanes_a[idx] = lanes_a[idx] + lanes_b[idx];\n" ++
    "        idx += 1;\n" ++
    "    }\n" ++
    "\n" ++
    "    var total_pos: i32 = swarm[0].pos_x + swarm[1].vel_x + swarm[2].mass + swarm[3].pos_x;\n" ++
    "    step_value(&mut total_pos, lanes_a[0] + lanes_a[3]);\n" ++
    "    let bias: i32 = 5;\n" ++
    "    let bias_ref: &i32 = &bias;\n" ++
    "    @local let read_biased = || -> i32 { bias_ref.* + 8 };\n" ++
    "    let closure_sum: i32 = read_biased() + apply_fn_ptr(6, scale_lane) + bias_ref.*;\n" ++
    "    return total_pos + closure_sum;\n" ++
    "}\n";

/// Showcase `.cx` source exercising `@atomic_*`, `@simd_*` (`i32` & `f32`), and `@sys_write`.
const ATOMICS_SIMD_STREAMS_SRC =
    "//! 4-Tier Atomics, Integer/Float SIMD, and `@sys_write` Streams Oracle Case\n" ++
    "pub fn main() -> i32 {\n" ++
    "    var cell: u32 = 12;\n" ++
    "    @atomic_store(&mut cell, 20, 5);\n" ++
    "    let prev_add: u32 = @atomic_rmw_add(&mut cell, 7, 5);\n" ++
    "    let prev_sub: u32 = @atomic_rmw_sub(&mut cell, 2, 5);\n" ++
    "    let prev_xchg: u32 = @atomic_rmw_xchg(&mut cell, 30, 5);\n" ++
    "    let (observed_u32, did_swap) = @atomic_cmpxchg(&mut cell, 30, 44, 5, 5);\n" ++
    "    @atomic_fence(5);\n" ++
    "    let loaded_u32: u32 = @atomic_load(&cell, 5);\n" ++
    "\n" ++
    "    let iv_a: [i32; 4] = @simd_splat[[i32; 4]](4);\n" ++
    "    let iv_b: [i32; 4] = [1, 2, 3, 4];\n" ++
    "    let iv_prod: [i32; 4] = @simd_mul(@simd_add(iv_a, iv_b), @simd_sub(iv_a, [1, 1, 1, 1]));\n" ++
    "    let iv_sum: i32 = @simd_reduce_add(iv_prod);\n" ++
    "\n" ++
    "    let fv_a: [f32; 4] = @simd_splat[[f32; 4]](1.5);\n" ++
    "    let fv_b: [f32; 4] = [0.5, 1.5, 2.5, 3.5];\n" ++
    "    let fv_sum: f32 = @simd_reduce_add(@simd_add(fv_a, fv_b));\n" ++
    "\n" ++
    "    let written_out: isize = @sys_write(1, \"alpha-out\\n\");\n" ++
    "    let written_err: isize = @sys_write(2, \"beta-err\\n\");\n" ++
    "    let swap_bonus: i32 = if did_swap { 3 } else { 0 };\n" ++
    "\n" ++
    "    return (prev_add as i32) + (prev_sub as i32) + (prev_xchg as i32) +\n" ++
    "        (observed_u32 as i32) + (loaded_u32 as i32) + iv_sum +\n" ++
    "        (fv_sum as i32) + (written_out as i32) + (written_err as i32) + swap_bonus;\n" ++
    "}\n";

// -------------------------------------- INTERNALS --------------------------------------

/// Runs `runFourTierDiffOracle` on `source_text` and prints the diff table on unexpected failure.
fn expectFourTierParity(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_text: []const u8,
) !diff_oracle.DiffOracleReport {
    var report = try corex.runFourTierDiffOracle(allocator, source_text, .{ .io = io });
    errdefer report.deinit(allocator);
    if (!report.is_all_matching) {
        std.debug.print("\n{s}\n", .{report.rendered_diff_table});
    }
    try std.testing.expect(report.is_all_matching);
    return report;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_diff_oracle_four_tier_layouts_niche_sum_types_bitfields_and_result_cc" {
    var report = try expectFourTierParity(
        std.testing.allocator,
        std.testing.io,
        LAYOUT_NICHE_RESULT_SRC,
    );
    defer report.deinit(std.testing.allocator);

    try std.testing.expect(!report.outcomes[0].has_trapped);
    // (5 + 100 + 20) + (3 + 12) + (6 + 11 + 4) + 10 + 12 + (-1) + 15 + 8 = 205
    try std.testing.expectEqual(@as(i64, 205), report.outcomes[0].return_scalar_i64);
}

test "test_diff_oracle_four_tier_defer_errdefer_and_autodrop_lifo_trace" {
    var report = try expectFourTierParity(
        std.testing.allocator,
        std.testing.io,
        DROP_DEFER_ERRDEFER_SRC,
    );
    defer report.deinit(std.testing.allocator);

    try std.testing.expect(!report.outcomes[0].has_trapped);
    // ok_score = (10 + 20) + 3 = 33; err_score = 5 -> 38
    try std.testing.expectEqual(@as(i64, 38), report.outcomes[0].return_scalar_i64);
    // Call 1 (ok, moved second_tok): consume(1020, drop 20), defer(90), drop first_tok(10)
    // Call 2 (err, kept second_tok): drop second_tok(20), errdefer(77), defer(90), drop first_tok(10)
    try std.testing.expectEqualSlices(
        i64,
        &[_]i64{ 1020, 20, 90, 10, 20, 77, 90, 10 },
        report.outcomes[0].drop_trace,
    );
}

test "test_diff_oracle_four_tier_soa_must_vectorize_and_local_closures" {
    var report = try expectFourTierParity(
        std.testing.allocator,
        std.testing.io,
        SOA_VECTORIZE_CLOSURE_SRC,
    );
    defer report.deinit(std.testing.allocator);

    try std.testing.expect(!report.outcomes[0].has_trapped);
    // total_pos = (1 + 5 + 9 + 10) + (4 + 16) = 45; closure_sum = (13 + 12 + 5) = 30 -> 75
    try std.testing.expectEqual(@as(i64, 75), report.outcomes[0].return_scalar_i64);
}

test "test_diff_oracle_four_tier_atomics_simd_and_sys_write_streams" {
    var report = try expectFourTierParity(
        std.testing.allocator,
        std.testing.io,
        ATOMICS_SIMD_STREAMS_SRC,
    );
    defer report.deinit(std.testing.allocator);

    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqualStrings("alpha-out\n", report.outcomes[0].stdout_bytes);
    try std.testing.expectEqualStrings("beta-err\n", report.outcomes[0].stderr_bytes);
    // 20 + 27 + 25 + 30 + 44 + ((5+6+7+8)*3 = 78) + 14 + 10 + 9 + 3 = 260
    try std.testing.expectEqual(@as(i64, 260), report.outcomes[0].return_scalar_i64);
}

test "test_diff_oracle_four_tier_sys_exit_and_deliberate_runtime_trap_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `@sys_exit(37)` exit-code + pre-exit stream/drop-trace parity:
    const sys_exit_src =
        "//! `@sys_exit` 4-Tier Parity\n" ++
        "pub fn main() -> i32 {\n" ++
        "    @drop_trace(55);\n" ++
        "    let _ = @sys_write(1, \"bye-37\\n\");\n" ++
        "    @sys_exit(37);\n" ++
        "}\n";
    var exit_report = try expectFourTierParity(allocator, io, sys_exit_src);
    defer exit_report.deinit(allocator);
    try std.testing.expect(!exit_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i32, 37), exit_report.outcomes[0].exit_code);
    try std.testing.expectEqualStrings("bye-37\n", exit_report.outcomes[0].stdout_bytes);
    try std.testing.expectEqualSlices(i64, &[_]i64{55}, exit_report.outcomes[0].drop_trace);

    // [2] Deliberate `@panic("oracle_boom")` trap parity:
    const panic_src =
        "//! `@panic` 4-Tier Trap Parity\n" ++
        "pub fn main() -> i32 {\n" ++
        "    @drop_trace(404);\n" ++
        "    @panic(\"oracle_boom\");\n" ++
        "}\n";
    var panic_report = try expectFourTierParity(allocator, io, panic_src);
    defer panic_report.deinit(allocator);
    try std.testing.expect(panic_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i32, 101), panic_report.outcomes[0].exit_code);
    try std.testing.expectEqualStrings("panic: oracle_boom\n", panic_report.outcomes[0].stderr_bytes);
    try std.testing.expectEqualSlices(i64, &[_]i64{404}, panic_report.outcomes[0].drop_trace);

    // [3] Deliberate checked signed integer overflow trap parity:
    const overflow_src =
        "//! Checked Overflow 4-Tier Trap Parity\n" ++
        "@noinline\n" ++
        "pub fn hidden_delta() -> i32 {\n" ++
        "    return 1;\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let max_val: i32 = 2_147_483_647;\n" ++
        "    return max_val + hidden_delta();\n" ++
        "}\n";
    var ovf_report = try expectFourTierParity(allocator, io, overflow_src);
    defer ovf_report.deinit(allocator);
    try std.testing.expect(ovf_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i32, 101), ovf_report.outcomes[0].exit_code);

    // [4] Monochrome box-drawing diff renderer verification on synthetic mismatch:
    const synthetic_tiers = [4]OracleTierOutcome{
        .{ .return_scalar_i64 = 10, .exit_code = 10 },
        .{ .return_scalar_i64 = 10, .exit_code = 10 },
        .{ .return_scalar_i64 = 99, .exit_code = 99 },
        .{ .return_scalar_i64 = 10, .exit_code = 10 },
    };
    const diff_res = try diff_oracle.compareOutcomesAndRenderTable(allocator, &synthetic_tiers);
    defer if (diff_res.rendered_table.len > 0) allocator.free(diff_res.rendered_table);
    try std.testing.expect(!diff_res.is_all_matching);
    try std.testing.expect(std.mem.indexOf(u8, diff_res.rendered_table, "╭") != null);
    try std.testing.expect(std.mem.indexOf(u8, diff_res.rendered_table, "✗") != null);
}

test "test_cli_end_to_end_build_emit_c_emit_llvm_fuzz_run_test_diff_backends_and_e0006" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const cli_src_path = ".zig-cache/phase7_cli_e2e_app.cx";
    const cli_exe_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/phase7_cli_e2e_app{s}",
        .{TargetSpec.host().executableExtension()},
    );
    defer allocator.free(cli_exe_path);
    const cli_c_path = ".zig-cache/phase7_cli_e2e_app.c";
    const cli_ll_path = ".zig-cache/phase7_cli_e2e_app.ll";
    const cli_fuzz_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/phase7_cli_e2e_fuzz{s}",
        .{TargetSpec.host().executableExtension()},
    );
    defer allocator.free(cli_fuzz_path);

    const cli_app_source =
        "//! Phase 7 CLI End-to-End Integration Program\n" ++
        "pub fn compute_tag(step: i32) -> i32 {\n" ++
        "    if step > 2 {\n" ++
        "        return step * 4;\n" ++
        "    }\n" ++
        "    return step + 1;\n" ++
        "}\n" ++
        "\n" ++
        "pub fn main() -> i32 {\n" ++
        "    let _ = @sys_write(1, \"cli-run-ok\\n\");\n" ++
        "    return compute_tag(5) - 20;\n" ++
        "}\n";

    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = cli_src_path, .data = cli_app_source });
    defer std.Io.Dir.cwd().deleteFile(io, cli_src_path) catch {};
    defer std.Io.Dir.cwd().deleteFile(io, cli_exe_path) catch {};
    defer std.Io.Dir.cwd().deleteFile(io, cli_c_path) catch {};
    defer std.Io.Dir.cwd().deleteFile(io, cli_ll_path) catch {};
    defer std.Io.Dir.cwd().deleteFile(io, cli_fuzz_path) catch {};

    var stdout_buf: [8192]u8 = undefined;
    var stderr_buf: [8192]u8 = undefined;

    // [1] `corex build <src> -o <exe>`:
    {
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "build", cli_src_path, "-o", cli_exe_path },
            &out_w,
            &err_w,
        );
        try std.testing.expectEqual(@as(u8, 0), code);
        try std.testing.expect(std.mem.indexOf(u8, out_w.buffered(), "✓ build") != null);
    }

    // [2] `corex build -ofmt=c --emit-c <src> -o <c_file>`:
    {
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "build", "-ofmt=c", "--emit-c", cli_src_path, "-o", cli_c_path },
            &out_w,
            &err_w,
        );
        try std.testing.expectEqual(@as(u8, 0), code);
        const emitted_c = try std.Io.Dir.cwd().readFileAlloc(
            io,
            cli_c_path,
            allocator,
            .limited(2 * 1024 * 1024),
        );
        defer allocator.free(emitted_c);
        try std.testing.expect(std.mem.indexOf(u8, emitted_c, "int main(void)") != null);
    }

    // [3] `corex build --emit-llvm <src> -o <ll_file>`:
    {
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "build", "--emit-llvm", cli_src_path, "-o", cli_ll_path },
            &out_w,
            &err_w,
        );
        try std.testing.expectEqual(@as(u8, 0), code);
        const emitted_ll = try std.Io.Dir.cwd().readFileAlloc(
            io,
            cli_ll_path,
            allocator,
            .limited(2 * 1024 * 1024),
        );
        defer allocator.free(emitted_ll);
        try std.testing.expect(std.mem.indexOf(u8, emitted_ll, "define i32 @main(") != null);
    }

    // [4] `corex build --fuzz <src> -o <fuzz_exe>` + `COREX_FUZZ_STATS=1`:
    {
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "build", "--fuzz", cli_src_path, "-o", cli_fuzz_path },
            &out_w,
            &err_w,
        );
        try std.testing.expectEqual(@as(u8, 0), code);

        var env_map = std.process.Environ.Map.init(allocator);
        defer env_map.deinit();
        try env_map.put("COREX_FUZZ_STATS", "1");

        const fuzz_run = try std.process.run(allocator, io, .{
            .argv = &.{cli_fuzz_path},
            .environ_map = &env_map,
        });
        defer allocator.free(fuzz_run.stdout);
        defer allocator.free(fuzz_run.stderr);
        try std.testing.expect(std.mem.indexOf(u8, fuzz_run.stderr, "SANCOV_EDGES:") != null);
    }

    // [5] `corex run <src> -- arg_alpha arg_beta`:
    {
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "run", cli_src_path, "--", "arg_alpha", "arg_beta" },
            &out_w,
            &err_w,
        );
        try std.testing.expectEqual(@as(u8, 0), code);
        try std.testing.expectEqualStrings("cli-run-ok\n", out_w.buffered());
    }

    // [6] `corex test --diff-backends <src>`:
    {
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "test", "--diff-backends", cli_src_path },
            &out_w,
            &err_w,
        );
        if (code != 0) {
            std.debug.print("test --diff-backends stderr:\n{s}\n", .{err_w.buffered()});
        }
        try std.testing.expectEqual(@as(u8, 0), code);
        try std.testing.expect(std.mem.indexOf(u8, out_w.buffered(), "✓ test") != null);
    }

    // [7] Invalid `--target=sparc64-solaris` emits `E0006` + catalog parity on `E0007`/`E0008`:
    {
        try std.testing.expectEqualStrings(
            "E0006",
            DiagnosticCode.e0006_invalid_target_triple.asCodeStr(),
        );
        try std.testing.expectEqualStrings(
            "E0007",
            DiagnosticCode.e0007_codegen_backend_failure.asCodeStr(),
        );
        try std.testing.expectEqualStrings(
            "E0008",
            DiagnosticCode.e0008_linker_invocation_failed.asCodeStr(),
        );
        var out_w = std.Io.Writer.fixed(&stdout_buf);
        var err_w = std.Io.Writer.fixed(&stderr_buf);
        const code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "build", "--target=sparc64-solaris", cli_src_path },
            &out_w,
            &err_w,
        );
        try std.testing.expectEqual(@as(u8, 1), code);
        try std.testing.expect(std.mem.indexOf(u8, err_w.buffered(), "E0006") != null);
    }
}

test "test_regression_refined_niche_option_packed_align_and_aggregate_insert" {
    const src =
        \\pub type SmallPos = u32 is 1..=10;
        \\pub type MidPos = u32 is 5..=10;
        \\
        \\@packed
        \\pub struct UnalignedFrame {
        \\    pub prefix: u8,
        \\    pub payload: u64,
        \\    pub tail: u32,
        \\}
        \\
        \\pub fn classify_small_opt(maybe_small: SmallPos?) -> i32 {
        \\    return match maybe_small {
        \\        .Some(val_s) => {
        \\            let widened: u32 = val_s;
        \\            widened as i32
        \\        },
        \\        .None => -3,
        \\    };
        \\}
        \\
        \\pub fn classify_mid_opt(maybe_mid: MidPos?) -> i32 {
        \\    return match maybe_mid {
        \\        .Some(val_m) => {
        \\            let widened: u32 = val_m;
        \\            widened as i32
        \\        },
        \\        .None => -7,
        \\    };
        \\}
        \\
        \\pub fn replace_packed_payload(base_frame: UnalignedFrame, next_payload: u64) -> UnalignedFrame {
        \\    var updated: UnalignedFrame = base_frame;
        \\    updated.payload = next_payload;
        \\    return updated;
        \\}
        \\
        \\pub fn bump_packed_slot(frame_ref: &mut UnalignedFrame, delta: u64) {
        \\    frame_ref.*.payload = frame_ref.*.payload + delta;
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let s_one: SmallPos = 1;
        \\    let s_ten: SmallPos = 10;
        \\    let m_five: MidPos = 5;
        \\    let m_ten: MidPos = 10;
        \\    let opt_s1: SmallPos? = .Some(s_one);
        \\    let opt_s10: SmallPos? = .Some(s_ten);
        \\    let opt_snone: SmallPos? = .None;
        \\    let opt_m5: MidPos? = .Some(m_five);
        \\    let opt_mnone: MidPos? = .None;
        \\    let eq_bonus: i32 = if opt_s1 != opt_snone and opt_m5 != opt_mnone { 4 } else { 0 };
        \\
        \\    var frame = UnalignedFrame { prefix: 3, payload: 100, tail: 9 };
        \\    frame = replace_packed_payload(frame, 200);
        \\    bump_packed_slot(&mut frame, 15);
        \\
        \\    let niche_sum: i32 = classify_small_opt(opt_s1) + classify_small_opt(opt_s10) +
        \\        classify_small_opt(opt_snone) + classify_mid_opt(opt_m5) +
        \\        classify_mid_opt(.Some(m_ten)) + classify_mid_opt(opt_mnone);
        \\    return niche_sum + eq_bonus + (frame.prefix as i32) + (frame.payload as i32) + (frame.tail as i32);
        \\}
    ;

    var report = try expectFourTierParity(std.testing.allocator, std.testing.io, src);
    defer report.deinit(std.testing.allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // niche_sum = 1 + 10 - 3 + 5 + 10 - 7 = 16; eq_bonus = 4; frame = 3 + 215 + 9 = 227 -> 247.
    try std.testing.expectEqual(@as(i64, 247), report.outcomes[0].return_scalar_i64);
}

test "test_regression_must_vectorize_scalar_reduction_and_shared_mvs_aliasing" {
    const src =
        \\pub fn sum_slice_vectorized(lanes: &[i32]) -> i32 {
        \\    var acc: i32 = 0;
        \\    var idx: usize = 0;
        \\    @must_vectorize
        \\    while idx < lanes.len() {
        \\        acc = acc + lanes[idx];
        \\        idx += 1;
        \\    }
        \\    return acc;
        \\}
        \\
        \\pub fn add_aliased_shared_refs(lhs_ref: &i32, rhs_ref: &i32, dst_acc: &mut i32) {
        \\    dst_acc.* = dst_acc.* + lhs_ref.* + rhs_ref.*;
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let data_arr: [i32; 8] = [2, 4, 6, 8, 1, 3, 5, 7];
        \\    var total: i32 = sum_slice_vectorized(&data_arr);
        \\    let shared_cell: i32 = 11;
        \\    add_aliased_shared_refs(&shared_cell, &shared_cell, &mut total);
        \\    return total;
        \\}
    ;

    var report = try expectFourTierParity(std.testing.allocator, std.testing.io, src);
    defer report.deinit(std.testing.allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // sum = 36; + 11 + 11 = 58.
    try std.testing.expectEqual(@as(i64, 58), report.outcomes[0].return_scalar_i64);
}

test "test_regression_slice_array_coercion_const_str_ref_derive_debug_and_composite_eq" {
    const src =
        \\@derive(Debug)
        \\pub struct StatusBadge {
        \\    pub code: i32,
        \\}
        \\
        \\pub const BANNER_TEXT: str = "corex-rodata";
        \\
        \\pub fn read_borrowed_slice(bytes_ref: &[u8]) -> i32 {
        \\    return (bytes_ref.len() as i32) + (bytes_ref[0] as i32) + (bytes_ref[3] as i32);
        \\}
        \\
        \\pub fn read_borrowed_str(text_ref: &str) -> i32 {
        \\    return text_ref.*.len() as i32;
        \\}
        \\
        \\pub fn inspect_badge_debug_len(val: i32) -> i32 {
        \\    let badge = StatusBadge { code: val };
        \\    let dbg_str: str = badge.debug();
        \\    return if dbg_str.len() > 0 { 5 } else { 0 };
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let raw_quad: [u8; 4] = [10, 20, 30, 40];
        \\    let coerced_score: i32 = read_borrowed_slice(&raw_quad);
        \\    let banner_len: i32 = read_borrowed_str(&BANNER_TEXT) + read_borrowed_str(&"ok");
        \\    let dbg_ok: i32 = inspect_badge_debug_len(7);
        \\    let opt_pair_a: [i32; 2]? = .Some([1, 2]);
        \\    let opt_pair_b: [i32; 2]? = .Some([1, 2]);
        \\    let opt_pair_c: [i32; 2]? = .Some([1, 3]);
        \\    let eq_score: i32 = if opt_pair_a == opt_pair_b and opt_pair_a != opt_pair_c { 17 } else { 0 };
        \\    return coerced_score + banner_len + dbg_ok + eq_score;
        \\}
    ;

    var report = try expectFourTierParity(std.testing.allocator, std.testing.io, src);
    defer report.deinit(std.testing.allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // coerced_score = 4 + 10 + 40 = 54; banner_len = 12 + 2 = 14; dbg_ok = 5; eq_score = 17 -> 90.
    try std.testing.expectEqual(@as(i64, 90), report.outcomes[0].return_scalar_i64);
}

test "test_regression_128bit_float_casts_bitfields_c_union_and_closure_pass_modes" {
    const src =
        \\pub bit_field WideBits: u128 {
        \\    pub lo_word: u64 | 64,
        \\    pub hi_tag: u32 | 32,
        \\    pub top_rest: u32 | 32,
        \\}
        \\
        \\@repr(C)
        \\pub union WordBytes {
        \\    pub as_f32: f32,
        \\    pub as_u32: u32,
        \\}
        \\
        \\pub struct BigTriple {
        \\    pub first: i64,
        \\    pub second: i64,
        \\    pub third: i64,
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let wide_neg: i128 = -8_000_000_000;
        \\    let as_f64: f64 = wide_neg as f64;
        \\    let back_i128: i128 = as_f64 as i128;
        \\    let interp_s: str = "v={wide_neg}";
        \\    let cast_ok: i32 = if back_i128 == wide_neg and interp_s == "v=-8000000000" { 13 } else { 0 };
        \\
        \\    var wbf = WideBits { lo_word: 9, hi_tag: 42, top_rest: 3 };
        \\    wbf.hi_tag = 55;
        \\    let bf_score: i32 = (wbf.lo_word as i32) + (wbf.hi_tag as i32) + (wbf.top_rest as i32);
        \\
        \\    let u_one = WordBytes { as_f32: 1.0 };
        \\    let raw_ieee: u32 = unsafe { u_one.as_u32 };
        \\    let union_ok: i32 = if raw_ieee == 0x3F80_0000 { 19 } else { 0 };
        \\
        \\    let scale_bias: i64 = 4;
        \\    let bias_ref: &i64 = &scale_bias;
        \\    @local let sum_big = |triple_in: BigTriple| -> i64 {
        \\        triple_in.first + triple_in.second + triple_in.third + bias_ref.*
        \\    };
        \\    let closure_val: i32 = sum_big(BigTriple { first: 5, second: 6, third: 7 }) as i32;
        \\    return cast_ok + bf_score + union_ok + closure_val;
        \\}
    ;

    var report = try expectFourTierParity(std.testing.allocator, std.testing.io, src);
    defer report.deinit(std.testing.allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // `cast_ok = 13`; `bf_score = 9 + 55 + 3 = 67`; `union_ok = 19`; `closure_val = 22` -> `121`:
    try std.testing.expectEqual(@as(i64, 121), report.outcomes[0].return_scalar_i64);
}

test "test_phase75_four_tier_parity_se01_to_se08_and_unreachable_dollar_traps" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Full 4-tier parity across `SE-01`–`SE-08` (`ConditionScope` pre-`else` `@drop_trace`, `orelse`,
    // `$` indexing/slicing, nested `$` scopes, `at_pat` + `slice_pat`, named args + `|>`, `with context`):
    const phase75_showcase_src =
        \\pub struct DropItem {
        \\    pub marker: i64,
        \\}
        \\impl DropItem {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.marker);
        \\    }
        \\}
        \\
        \\pub fn maybe_drop_item(is_some: bool, marker: i64) -> DropItem? {
        \\    if is_some {
        \\        return .Some(DropItem { marker: marker });
        \\    }
        \\    return .None;
        \\}
        \\
        \\pub fn scale_and_offset(val_in: i32, factor: i32 = 2, delta: i32 = 3) -> i32 {
        \\    return val_in * factor + delta;
        \\}
        \\
        \\pub fn read_cancel_bonus() -> i32 {
        \\    return context.cancel_token._handle as i32;
        \\}
        \\
        \\pub fn match_slice_and_at(items: &[i32], opt_num: i32?) -> i32 {
        \\    let slice_part: i32 = match items {
        \\        [] => 0,
        \\        [single_v] => single_v,
        \\        [first_v, ..mid_sub, last_v] => first_v + (mid_sub.len() as i32) * 10 + last_v,
        \\    };
        \\    let at_part: i32 = match opt_num {
        \\        whole_opt @ .Some(inner_v) => if whole_opt is .Some(dup_v) { inner_v + dup_v } else { 0 },
        \\        .None => 0,
        \\    };
        \\    return slice_part + at_part;
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let cond_score: i32 = if maybe_drop_item(true, 11) is .Some(item_a) and
        \\        (item_b := DropItem { marker: 22 }).marker > 50
        \\    {
        \\        (item_a.marker as i32) + (item_b.marker as i32)
        \\    } else if (fallback_n := 6) > 4 {
        \\        @drop_trace(99);
        \\        fallback_n
        \\    } else {
        \\        0
        \\    };
        \\
        \\    var loop_sum: i32 = 0;
        \\    var step_opt: i32? = .Some(3);
        \\    while step_opt is .Some(cur_step) and (next_step := cur_step - 1) >= 0 {
        \\        loop_sum = loop_sum + cur_step;
        \\        step_opt = if next_step > 0 { .Some(next_step) } else { .None };
        \\    }
        \\
        \\    let none_opt: i32? = .None;
        \\    let some_opt: i32? = .Some(5);
        \\    let orelse_score: i32 = (none_opt orelse 7) + (some_opt orelse 99);
        \\
        \\    let outer_nums: [i32; 6] = [2, 4, 6, 8, 10, 12];
        \\    let inner_idx: [usize; 3] = [5, 3, 1];
        \\    let nested_view: &[i32] = outer_nums[inner_idx[$ - 1]..$ - 1];
        \\    let incl_view: &[i32] = outer_nums[0..=2];
        \\    let mid_str: str = "corex"[1..$ - 1];
        \\    let slice_score: i32 = nested_view[$ - 1] + incl_view[$ - 1] + (mid_str.len() as i32);
        \\
        \\    let pat_score: i32 = match_slice_and_at(nested_view, .Some(4));
        \\    let pipe_score: i32 = 5 |> scale_and_offset(delta: 4, factor: 3);
        \\
        \\    let outer_tok = CancelToken { _handle: 15 };
        \\    let inner_tok = CancelToken { _handle: 20 };
        \\    let outer_ctx: i32 = with context.cancel_token = outer_tok {
        \\        let inner_ctx: i32 = with context.cancel_token = inner_tok {
        \\            read_cancel_bonus()
        \\        };
        \\        inner_ctx + read_cancel_bonus()
        \\    };
        \\    let ctx_score: i32 = outer_ctx + read_cancel_bonus();
        \\
        \\    return cond_score + loop_sum + orelse_score + slice_score + pat_score + pipe_score + ctx_score;
        \\}
    ;

    var ok_report = try expectFourTierParity(allocator, io, phase75_showcase_src);
    defer ok_report.deinit(allocator);
    try std.testing.expect(!ok_report.outcomes[0].has_trapped);
    // Pre-`else` drop trace; `item_b` (`22`), `item_a` (`11`), then `else if` `@drop_trace(99)`:
    try std.testing.expectEqualSlices(i64, &[_]i64{ 22, 11, 99 }, ok_report.outcomes[0].drop_trace);
    // `cond_score = 6`, `loop_sum = 6`, `orelse_score = 12`, `slice_score = 19`, `pat_score = 42`,
    // `pipe_score = 19`, and `ctx_score = 35`, yielding `6 + 6 + 12 + 19 + 42 + 19 + 35 = 139`:
    try std.testing.expectEqual(@as(i64, 139), ok_report.outcomes[0].return_scalar_i64);

    // [2] Deliberate runtime `unreachable` (`MirTrapReason.unreachable_reached`) traps uniformly (`exit 101`):
    const unreach_trap_src =
        \\pub fn pick_branch(code: i32) -> i32 {
        \\    if code == 0 {
        \\        return 10;
        \\    }
        \\    unreachable;
        \\}
        \\pub fn main() -> i32 {
        \\    return pick_branch(1);
        \\}
    ;
    var unreach_report = try expectFourTierParity(allocator, io, unreach_trap_src);
    defer unreach_report.deinit(allocator);
    try std.testing.expect(unreach_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i32, 101), unreach_report.outcomes[0].exit_code);

    // [3] Runtime `$ - back_step` underflow traps even in `--release` across all 4 tiers (`SE-04`, `exit 101`):
    const dollar_trap_src =
        \\pub fn pick_from_end(items: &[i32], back_step: usize) -> i32 {
        \\    return items[$ - back_step];
        \\}
        \\pub fn main() -> i32 {
        \\    let nums: [i32; 3] = [10, 20, 30];
        \\    return pick_from_end(&nums, 5);
        \\}
    ;
    var dollar_report = try expectFourTierParity(allocator, io, dollar_trap_src);
    defer dollar_report.deinit(allocator);
    try std.testing.expect(dollar_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(i32, 101), dollar_report.outcomes[0].exit_code);
}

test "test_regression_four_tier_linear_complement_partial_variant_and_cond_drops" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const complement_drops_src =
        \\@linear
        \\pub struct LinearToken {
        \\    pub id: i32,
        \\}
        \\
        \\pub fn consume_linear(tok: own LinearToken) -> i32 {
        \\    let LinearToken { id } = tok;
        \\    return id;
        \\}
        \\
        \\pub struct DropGuard {
        \\    pub tag: i64,
        \\}
        \\
        \\impl DropGuard {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.tag);
        \\    }
        \\}
        \\
        \\pub enum Outcome {
        \\    Ok(LinearToken),
        \\    Msg(DropGuard),
        \\    Code(usize),
        \\}
        \\
        \\pub enum OpenRes {
        \\    Ok(LinearToken),
        \\    IoErr(DropGuard),
        \\    PathErr(DropGuard),
        \\}
        \\
        \\pub enum GuardPair {
        \\    Both(DropGuard, DropGuard),
        \\    Empty,
        \\}
        \\
        \\pub fn handle_outcome_code() -> i32 {
        \\    let out_val: Outcome = .Code(3735928559);
        \\    if out_val is .Ok(lin_tok) {
        \\        return consume_linear(own lin_tok);
        \\    }
        \\    return 10;
        \\}
        \\
        \\pub fn handle_outcome_msg() -> i32 {
        \\    let out_val: Outcome = .Msg(DropGuard { tag: 77 });
        \\    if out_val is .Ok(lin_tok) {
        \\        return consume_linear(own lin_tok);
        \\    }
        \\    return 20;
        \\}
        \\
        \\pub fn handle_open_path_err() -> i32 {
        \\    let open_val: OpenRes = .PathErr(DropGuard { tag: 88 });
        \\    if open_val is .Ok(lin_tok) {
        \\        return consume_linear(own lin_tok);
        \\    }
        \\    return 30;
        \\}
        \\
        \\pub fn handle_partial_pair() -> i32 {
        \\    let pair_val: GuardPair = .Both(DropGuard { tag: 11 }, DropGuard { tag: 22 });
        \\    if pair_val is .Both(first_guard, _) {
        \\        @drop_trace(100);
        \\        return first_guard.tag as i32;
        \\    }
        \\    return 0;
        \\}
        \\
        \\pub fn make_opt_guard(is_some: bool, tag: i64) -> DropGuard? {
        \\    if is_some {
        \\        return .Some(DropGuard { tag: tag });
        \\    }
        \\    return .None;
        \\}
        \\
        \\pub fn handle_cond_else_drop() -> i32 {
        \\    if not (make_opt_guard(true, 5) is not .None) {
        \\        @drop_trace(300);
        \\        return 1;
        \\    } else {
        \\        @drop_trace(400);
        \\        return 40;
        \\    }
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let code_part: i32 = handle_outcome_code();
        \\    let msg_part: i32 = handle_outcome_msg();
        \\    let open_part: i32 = handle_open_path_err();
        \\    let pair_part: i32 = handle_partial_pair();
        \\    let cond_part: i32 = handle_cond_else_drop();
        \\    return code_part + msg_part + open_part + pair_part + cond_part;
        \\}
    ;

    var report = try expectFourTierParity(allocator, io, complement_drops_src);
    defer report.deinit(allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // `.Code(0xDEADBEEF)` emits zero drop trace; `.Msg(77)` -> `77`; `.PathErr(88)` -> `88`;
    // `.Both(11, 22)` partial move -> `100, 22, 11`; `hir_if` condition scope -> `5` before `400`:
    try std.testing.expectEqualSlices(
        i64,
        &[_]i64{ 77, 88, 100, 22, 11, 5, 400 },
        report.outcomes[0].drop_trace,
    );
    try std.testing.expectEqual(@as(i64, 111), report.outcomes[0].return_scalar_i64);
}

test "test_regression_four_tier_context_arena_closure_drop_and_dependent_defaults" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const ctx_defaults_src =
        \\pub struct Arena {
        \\    pub bump_tag: usize,
        \\}
        \\
        \\impl Arena {
        \\    pub fn release(&mut self) {}
        \\}
        \\
        \\pub struct CtxDropProbe {
        \\    pub marker: i64,
        \\}
        \\
        \\impl CtxDropProbe {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.marker + (context.cancel_token._handle as i64));
        \\    }
        \\}
        \\
        \\pub const MAX_RETRIES: i32 = 4;
        \\
        \\pub fn make_window(lo: i32, mid: i32 = lo + 5, hi: i32 = mid * 2) -> i32 {
        \\    return hi - lo;
        \\}
        \\
        \\pub fn match_const_pat(retries: i32) -> i32 {
        \\    if retries is MAX_RETRIES {
        \\        return 7;
        \\    }
        \\    return 0;
        \\}
        \\
        \\pub fn run_arena_context() -> i32 {
        \\    let initial_alloc = context.allocator;
        \\    let _ = initial_alloc._handle;
        \\    var local_arena = Arena { bump_tag: 99 };
        \\    defer local_arena.release();
        \\    with context.allocator = &mut local_arena {
        \\        let active_alloc = context.allocator;
        \\        return if active_alloc._handle != 0 { 9 } else { 0 };
        \\    }
        \\}
        \\
        \\pub fn run_closure_and_drop_in_with() -> i32 {
        \\    let read_cancel = @local |bonus: i32| -> i32 {
        \\        return (context.cancel_token._handle as i32) + bonus;
        \\    };
        \\    let active_tok = CancelToken { _handle: 33 };
        \\    let inner_res: i32 = with context.cancel_token = active_tok {
        \\        let inner_probe = CtxDropProbe { marker: 100 };
        \\        let _ = inner_probe.marker;
        \\        read_cancel(7)
        \\    };
        \\    let outer_probe = CtxDropProbe { marker: 200 };
        \\    let _ = outer_probe.marker;
        \\    let snap_ctx = context;
        \\    return inner_res + read_cancel(0) + (snap_ctx.rng_seed as i32);
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let win_pos: i32 = make_window(3);
        \\    let win_named: i32 = make_window(mid: 10, lo: 4);
        \\    let pat_part: i32 = match_const_pat(4);
        \\    let arena_part: i32 = run_arena_context();
        \\    let ctx_part: i32 = run_closure_and_drop_in_with();
        \\    return win_pos + win_named + pat_part + arena_part + ctx_part;
        \\}
    ;

    var report = try expectFourTierParity(allocator, io, ctx_defaults_src);
    defer report.deinit(allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // `inner_probe` drops inside `with context.cancel_token = 33` (`133`); `outer_probe` drops after restore (`200`):
    try std.testing.expectEqualSlices(i64, &[_]i64{ 133, 200 }, report.outcomes[0].drop_trace);
    // `win_pos = 13`; `win_named = 16`; `pat_part = 7`; `arena_part = 9`; `ctx_part = 40` -> `85`:
    try std.testing.expectEqual(@as(i64, 85), report.outcomes[0].return_scalar_i64);
}

test "test_regression_four_tier_primitive_float_ne_and_alias_endian_helpers" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const endian_src =
        \\pub type Word = u32;
        \\pub type NetPort = distinct u16;
        \\
        \\pub fn main() -> i32 {
        \\    let ne_word: u32 = 0x1234_5678;
        \\    let ne_round: u32 = u32.from_ne_bytes(ne_word.to_ne_bytes());
        \\    let ne_ok: i32 = if ne_round == ne_word { 11 } else { 0 };
        \\
        \\    let f32_five: f32 = f32.from_le_bytes([0x00, 0x00, 0xA0, 0x40]);
        \\    let f32_three: f32 = f32.from_be_bytes([0x40, 0x40, 0x00, 0x00]);
        \\    let f32_ne: f32 = f32.from_ne_bytes(f32_five.to_ne_bytes());
        \\    let f32_be_hi: u8 = f32_three.to_be_bytes()[0];
        \\    let f32_le_hi: u8 = f32_five.to_le_bytes()[3];
        \\    let f32_score: i32 = (f32_ne as i32) + (f32_three as i32) +
        \\        (if f32_be_hi == 0x40 and f32_le_hi == 0x40 { 7 } else { 0 });
        \\
        \\    let f64_nine: f64 = f64.from_le_bytes([0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x22, 0x40]);
        \\    let f64_seven: f64 = f64.from_be_bytes([0x40, 0x1C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
        \\    let f64_ne: f64 = f64.from_ne_bytes(f64_nine.to_ne_bytes());
        \\    let f64_be_sec: u8 = f64_seven.to_be_bytes()[1];
        \\    let f64_score: i32 = (f64_ne as i32) + (f64_seven as i32) +
        \\        (if f64_be_sec == 0x1C { 13 } else { 0 });
        \\
        \\    let alias_max_ok: i32 = if Word.MAX == 0xFFFF_FFFF { 5 } else { 0 };
        \\    let alias_word: Word = Word.from_le_bytes([19, 0, 0, 0]);
        \\    let http_port: NetPort = NetPort.from_be_bytes([0x00, 0x50]);
        \\    let port_lo: i32 = http_port.to_be_bytes()[1] as i32;
        \\    let lit_bytes_ok: i32 = if (258).to_le_bytes()[1] == 1 and (2.0).to_be_bytes()[0] == 0x40 { 3 } else { 0 };
        \\
        \\    return ne_ok + f32_score + f64_score + alias_max_ok + (alias_word as i32) + port_lo + lit_bytes_ok;
        \\}
    ;

    var report = try expectFourTierParity(allocator, io, endian_src);
    defer report.deinit(allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    // `ne_ok = 11`; `f32_score = 5 + 3 + 7 = 15`; `f64_score = 9 + 7 + 13 = 29`;
    // `alias_max_ok = 5`; `alias_word = 19`; `port_lo = 80`; `lit_bytes_ok = 3` -> `162`:
    try std.testing.expectEqual(@as(i64, 162), report.outcomes[0].return_scalar_i64);
}

test "test_phase76_four_tier_parity_dr22_strings_fmt_update_swap_subscript_loc_builder_and_fsm" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    const dr22_showcase_src =
        \\pub struct DropBox {
        \\    pub id: i64,
        \\}
        \\impl DropBox {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.id);
        \\    }
        \\}
        \\
        \\pub struct ConfigCopy {
        \\    pub width: i32,
        \\    pub height: i32,
        \\    pub scale: i32,
        \\}
        \\
        \\pub struct PacketOwned {
        \\    pub code: i32,
        \\    pub guard_keep: DropBox,
        \\    pub guard_replace: DropBox,
        \\}
        \\
        \\pub struct Ring4 {
        \\    pub slots: [i32; 4],
        \\}
        \\impl Ring4 {
        \\    pub subscript(idx: usize) -> i32 {
        \\        let {
        \\            yield self.slots[idx % 4];
        \\        }
        \\        inout {
        \\            yield &mut self.slots[idx % 4];
        \\        }
        \\    }
        \\}
        \\
        \\pub struct RowBuilder {
        \\    pub total: i32,
        \\    pub count: i32,
        \\}
        \\@builder_item
        \\pub fn item(bld: &mut RowBuilder, weight: i32) {
        \\    bld.total = bld.total + weight;
        \\    bld.count = bld.count + 1;
        \\}
        \\
        \\pub fn build_rows(seed: i32, body: @builder |&mut RowBuilder|) -> i32 {
        \\    var bld = RowBuilder { total: seed, count: 0 };
        \\    body(&mut bld);
        \\    return bld.total + bld.count * 10;
        \\}
        \\
        \\pub fn swap_pair(left: &mut i32, right: &mut i32) {
        \\    (left.*, right.*) = (right.*, left.*);
        \\}
        \\
        \\pub fn caller_probe(loc: SourceLoc = @caller_location()) -> i32 {
        \\    return (if loc.line > 50 { 9 } else { 0 }) + (loc.fn_name.len() as i32);
        \\}
        \\
        \\pub enum LexState {
        \\    Start,
        \\    Scan(i32),
        \\    Emit(i32),
        \\}
        \\
        \\pub fn run_fsm(steps: i32) -> i32 {
        \\    var acc: i32 = 0;
        \\    return fsm: match LexState.Start {
        \\        .Start => {
        \\            continue :fsm LexState.Scan(steps);
        \\        },
        \\        .Scan(rem) => {
        \\            if rem > 0 {
        \\                acc = acc + rem;
        \\                continue :fsm LexState.Scan(rem - 1);
        \\            }
        \\            continue :fsm LexState.Emit(acc);
        \\        },
        \\        .Emit(final_sum) => final_sum + 3,
        \\    };
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    let tag_num: i32 = 7;
        \\    let banner: str = """
        \\        hdr={tag_num}
        \\        ok
        \\        """;
        \\    let _ = @sys_write(1, banner);
        \\
        \\    let magic_bytes: &[u8; 4] = b"CX\x2a!";
        \\    let byte_nl: u8 = b'\n';
        \\    let bytes_score: i32 = (magic_bytes.*[2] as i32) + (byte_nl as i32);
        \\
        \\    let hex_val: u32 = 0x2a_u32;
        \\    let fmt_line: str = "\n{{{hex_val:08x}|{hex_val=}}}\n";
        \\    let _ = @sys_write(1, fmt_line);
        \\    let fmt_score: i32 = fmt_line.len() as i32;
        \\
        \\    let base_cfg = ConfigCopy { width: 10, height: 20, scale: 3 };
        \\    let next_cfg = ConfigCopy { width: 15, ..base_cfg };
        \\    let cfg_score: i32 = next_cfg.width + next_cfg.height + next_cfg.scale + base_cfg.width;
        \\
        \\    var pkt_score: i32 = 0;
        \\    {
        \\        let pkt_1 = PacketOwned {
        \\            code: 1,
        \\            guard_keep: DropBox { id: 101 },
        \\            guard_replace: DropBox { id: 202 },
        \\        };
        \\        let pkt_2 = PacketOwned {
        \\            code: 6,
        \\            guard_replace: DropBox { id: 303 },
        \\            ..own pkt_1
        \\        };
        \\        pkt_score = pkt_2.code + (pkt_2.guard_keep.id as i32) - 100;
        \\    }
        \\
        \\    var first_v: i32 = 12;
        \\    var second_v: i32 = 35;
        \\    swap_pair(&mut first_v, &mut second_v);
        \\    let swap_score: i32 = first_v - second_v;
        \\
        \\    var ring = Ring4 { slots: [2, 4, 6, 8] };
        \\    let prev_ring_slot: i32 = ring[1];
        \\    ring[5] = prev_ring_slot + 10;
        \\    let sub_score: i32 = ring[1] + ring[3];
        \\
        \\    let loc_score: i32 = caller_probe();
        \\    let builder_score: i32 = build_rows(5) {
        \\        item(7);
        \\        item(8);
        \\    };
        \\    let fsm_score: i32 = run_fsm(4);
        \\
        \\    return (banner.len() as i32) + bytes_score + fmt_score + cfg_score + pkt_score +
        \\        swap_score + sub_score + loc_score + builder_score + fsm_score - 200;
        \\}
    ;

    var report = try expectFourTierParity(allocator, io, dr22_showcase_src);
    defer report.deinit(allocator);
    try std.testing.expect(!report.outcomes[0].has_trapped);
    try std.testing.expectEqualStrings(
        "hdr=7\nok\n{0000002a|hex_val=42}\n",
        report.outcomes[0].stdout_bytes,
    );
    try std.testing.expectEqual(@as(usize, 3), report.outcomes[0].drop_trace.len);
    // `8 + 52 + 23 + 48 + 7 + 23 + 22 + 13 + 40 + 13 - 200 = 49`:
    try std.testing.expectEqual(@as(i64, 49), report.outcomes[0].return_scalar_i64);

    // Verify 4-tier parity for `[u8; 6]`-backed `bit_field`, `[i32; 3]` `~x`, single-eval rvalue `..make_cfg()`,
    // partial-move + `..base` spread, generic `type` alias defaults, and `/` vs. `*` `@overload` zones:
    const byte_bf_and_spread_src =
        \\pub bit_field MacAddr: [u8; 6] {
        \\    pub oui: u32 | 24,
        \\    pub nibble: u8 | 4,
        \\    pub nic: u32 | 20,
        \\}
        \\
        \\pub struct CopyTriple {
        \\    pub width: i32,
        \\    pub height: i32,
        \\    pub scale: i32,
        \\}
        \\
        \\pub struct GuardId {
        \\    pub id: i32,
        \\}
        \\
        \\impl GuardId {
        \\    pub fn drop(&mut self) {
        \\        @drop_trace(self.id as i64);
        \\    }
        \\}
        \\
        \\pub struct MixedPkt {
        \\    pub code: i32,
        \\    pub guard: GuardId,
        \\}
        \\
        \\pub type Pair[A, B = A] = (A, B);
        \\
        \\@overload
        \\pub fn zone_pick(val: i32, /) -> i32 {
        \\    return val + 2;
        \\}
        \\
        \\@overload
        \\pub fn zone_pick(*, val: i32) -> i32 {
        \\    return val + 10;
        \\}
        \\
        \\pub fn make_triple(calls: &mut i32) -> CopyTriple {
        \\    calls.* += 1;
        \\    return CopyTriple { width: 1, height: 7, scale: 3 };
        \\}
        \\
        \\pub fn main() -> i32 {
        \\    var mac = MacAddr { oui: 0x010203_u32, nibble: 0x0a_u8, nic: 0xbcdef_u32 };
        \\    mac.nibble = 0x05_u8;
        \\    let inv_mac = ~mac;
        \\    let raw_inv: [u8; 6] = inv_mac as [u8; 6];
        \\    let bf_score: i32 = (mac.oui == 0x010203_u32) as i32 +
        \\        (mac.nibble as i32) +
        \\        ((mac.nic & 0x0f_u32) as i32) +
        \\        ((raw_inv[0] == 0xfc_u8) as i32);
        \\
        \\    let arr3: [i32; 3] = [1, -2, 3];
        \\    let inv_arr3 = ~arr3;
        \\    let arr_score: i32 = inv_arr3[0] + inv_arr3[1] + inv_arr3[2];
        \\
        \\    var eval_calls: i32 = 0;
        \\    let rval_spread = CopyTriple { width: 9, ..make_triple(&mut eval_calls) };
        \\    let spread_score: i32 = rval_spread.width + rval_spread.height + rval_spread.scale + (eval_calls * 10);
        \\
        \\    var pkt_score: i32 = 0;
        \\    {
        \\        let p1 = MixedPkt { code: 11, guard: GuardId { id: 77 } };
        \\        let p2 = MixedPkt { guard: own p1.guard, ..p1 };
        \\        pkt_score = p2.code + p2.guard.id - 70;
        \\    }
        \\
        \\    let dup_pair: Pair[i32] = (4, 6);
        \\    let zone_score: i32 = dup_pair.0 + dup_pair.1 + zone_pick(3) + zone_pick(val: 4);
        \\    return bf_score + arr_score + spread_score + pkt_score + zone_score;
        \\}
    ;
    var bf_report = try expectFourTierParity(allocator, io, byte_bf_and_spread_src);
    defer bf_report.deinit(allocator);
    try std.testing.expect(!bf_report.outcomes[0].has_trapped);
    try std.testing.expectEqual(@as(usize, 1), bf_report.outcomes[0].drop_trace.len);
    // `bf_score = 1 + 5 + 15 + 1 = 22`; `arr_score = -2 + 1 + -4 = -5`; `spread_score = 9 + 7 + 3 + 10 = 29`;
    // `pkt_score = 11 + 77 - 70 = 18`; `zone_score = 4 + 6 + 5 + 14 = 29` -> `22 - 5 + 29 + 18 + 29 = 93`:
    try std.testing.expectEqual(@as(i64, 93), bf_report.outcomes[0].return_scalar_i64);
}

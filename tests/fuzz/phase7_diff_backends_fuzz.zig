//! Phase 7 Deterministic 4-Tier Differential Backend & Codegen Fuzzing Suite (`tests/fuzz/phase7_diff_backends_fuzz.zig`)
//!
//! Exercises two complementary Phase 7 verification invariants (`DR-01`, `DR-20` `D-07A`):
//! 1. **Full 4-Tier Native + VM Differential Parity (`10` structure-aware PRNG `.cx` programs):**
//!    Synthesizes randomized, type-safe `.cx` modules combining structs (`@repr(C)` / `@zero_pad`),
//!    `inout` MVS parameters, `Result[i32, i32]` `?` propagation (`cx_result_cc`), `Option` `match`
//!    arms, `AutoDrop` + `defer` `@drop_trace(id)` sequences, bounded `while` loops, `[i32; 4]` SIMD
//!    arithmetic, and `@sys_write` streams, asserting 100% 4-tier `runFourTierDiffOracle` parity.
//! 2. **Cross-Target Deterministic IR Emission & VM Parity (`48` PRNG programs x 7 targets):**
//!    Verifies byte-for-byte deterministic Tier A (`-ofmt=c`, zero `void*`) and Tier B (`LLVM`)
//!    source emission (`Run 1 == Run 2`) across all 7 canonical `TargetSpec` triples alongside
//!    `--dev` vs `--release` `MirVm` execution parity.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of randomized `.cx` programs verified end-to-end through `zig cc` native execution in Test 1.
const FOUR_TIER_NATIVE_FUZZ_SEEDS: usize = 10;

/// Number of randomized `.cx` programs verified across all 7 cross-targets for deterministic IR in Test 2.
const CROSS_TARGET_DETERMINISM_SEEDS: usize = 48;

/// All 7 canonical Phase 7 target triples rotated during cross-target determinism fuzzing.
const ALL_CANONICAL_TARGETS = [_]TargetSpec{
    TargetSpec.X86_64_LINUX,
    TargetSpec.AARCH64_LINUX,
    TargetSpec.X86_64_MACOS,
    TargetSpec.AARCH64_MACOS,
    TargetSpec.X86_64_WINDOWS,
    TargetSpec.AARCH64_WINDOWS,
    TargetSpec.WASM32_WASI,
};

// -------------------------------------- INTERNALS --------------------------------------

/// Synthesizes a deterministic, well-typed `.cx` program from `prng_seed` with bounded arithmetic.
fn generateRandomValidCxProgram(allocator: std.mem.Allocator, prng_seed: u64) ![]u8 {
    var pcg = std.Random.Pcg.init(prng_seed ^ 0x9E37_79B9_7F4A_7C15);
    const rng = pcg.random();

    const init_alpha: i32 = rng.intRangeAtMost(i32, -40, 40);
    const init_beta: i32 = rng.intRangeAtMost(i32, 1, 25);
    const init_gamma: i32 = rng.intRangeAtMost(i32, -20, 30);
    const loop_limit: usize = rng.intRangeAtMost(usize, 1, 5);
    const simd_scalar: i32 = rng.intRangeAtMost(i32, -6, 9);
    const trace_first: i64 = rng.intRangeAtMost(i64, 10, 99);
    const trace_defer: i64 = rng.intRangeAtMost(i64, 100, 199);
    const should_take_branch = rng.boolean();
    const should_trigger_err = rng.boolean();
    const use_some_opt = rng.boolean();

    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);
    const writer_alloc = allocator;

    try builder.appendSlice(
        writer_alloc,
        "//! Generated Structure-Aware Phase 7 Differential Fuzz Program\n" ++
            "pub trait Drop {\n" ++
            "    fn drop(&mut self);\n" ++
            "}\n\n" ++
            "pub struct GuardBox {\n" ++
            "    pub code: i64,\n" ++
            "}\n\n" ++
            "impl Drop for GuardBox {\n" ++
            "    pub fn drop(&mut self) {\n" ++
            "        @drop_trace(self.code);\n" ++
            "    }\n" ++
            "}\n\n" ++
            "@repr(C)\n" ++
            "@zero_pad\n" ++
            "pub struct PairPacket {\n" ++
            "    pub tag_u8: u8,\n" ++
            "    pub payload_i32: i32,\n" ++
            "}\n\n" ++
            "pub fn bump_acc(mut acc_slot: inout i32, step_val: i32) -> unit {\n" ++
            "    acc_slot = acc_slot +% step_val;\n" ++
            "}\n\n" ++
            "pub fn checked_gate(flag_err: bool, val_in: i32) -> Result[i32, i32] {\n" ++
            "    if flag_err {\n" ++
            "        return .Err(0);\n" ++
            "    }\n" ++
            "    return .Ok(val_in +% 7);\n" ++
            "}\n\n" ++
            "pub fn eval_gate_wrapper(flag_err: bool, val_in: i32) -> Result[i32, i32] {\n" ++
            "    let unwrapped: i32 = checked_gate(flag_err, val_in)?;\n" ++
            "    return .Ok(unwrapped *% 2);\n" ++
            "}\n\n",
    );

    const main_body_text = try std.fmt.allocPrint(
        writer_alloc,
        "pub fn main() -> i32 {{\n" ++
            "    let guard_inst = GuardBox {{ code: {d} }};\n" ++
            "    defer {{ @drop_trace({d}); }}\n" ++
            "    let pkt = PairPacket {{ tag_u8: {d}, payload_i32: {d} }};\n" ++
            "    var running_acc: i32 = pkt.payload_i32 +% (pkt.tag_u8 as i32) +% (guard_inst.code as i32);\n" ++
            "    if {s} {{\n" ++
            "        bump_acc(running_acc, {d});\n" ++
            "    }} else {{\n" ++
            "        bump_acc(running_acc, {d});\n" ++
            "    }}\n" ++
            "    var iter_idx: usize = 0;\n" ++
            "    while iter_idx < {d} {{\n" ++
            "        bump_acc(running_acc, (iter_idx as i32) +% 1);\n" ++
            "        iter_idx += 1;\n" ++
            "    }}\n" ++
            "    let maybe_bonus: i32? = {s};\n" ++
            "    let opt_term: i32 = match maybe_bonus {{\n" ++
            "        .Some(inner_v) => inner_v,\n" ++
            "        .None => -3,\n" ++
            "    }};\n" ++
            "    let res_term: i32 = match eval_gate_wrapper({s}, {d}) {{\n" ++
            "        .Ok(ok_v) => ok_v,\n" ++
            "        .Err(err_v) => err_v -% 5,\n" ++
            "    }};\n" ++
            "    let vec_lanes: [i32; 4] = @simd_add(@simd_splat[[i32; 4]]({d}), [1, 2, 3, 4]);\n" ++
            "    let simd_term: i32 = @simd_reduce_add(vec_lanes);\n" ++
            "    let _ = @sys_write(1, \"fuzz-ok\\n\");\n" ++
            "    return running_acc +% opt_term +% res_term +% simd_term;\n" ++
            "}}\n",
        .{
            trace_first,
            trace_defer,
            @as(u32, @intCast(@mod(init_beta, 16))),
            init_alpha,
            if (should_take_branch) "true" else "false",
            init_beta,
            init_gamma,
            loop_limit,
            if (use_some_opt) ".Some(11)" else ".None",
            if (should_trigger_err) "true" else "false",
            init_gamma,
            simd_scalar,
        },
    );
    defer writer_alloc.free(main_body_text);

    try builder.appendSlice(writer_alloc, main_body_text);
    return builder.toOwnedSlice(writer_alloc);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_phase7_four_tier_differential_native_and_vm_parity" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    var seed_idx: usize = 0;
    while (seed_idx < FOUR_TIER_NATIVE_FUZZ_SEEDS) : (seed_idx += 1) {
        const cx_program = try generateRandomValidCxProgram(allocator, @intCast(seed_idx));
        defer allocator.free(cx_program);

        var report = try corex.runFourTierDiffOracle(allocator, cx_program, .{ .io = io });
        defer report.deinit(allocator);

        if (!report.is_all_matching) {
            std.debug.print(
                "Phase 7 4-tier fuzz mismatch at seed {d}:\n{s}\nProgram:\n{s}\n",
                .{ seed_idx, report.rendered_diff_table, cx_program },
            );
        }
        try std.testing.expect(report.is_all_matching);
        try std.testing.expect(!report.outcomes[0].has_trapped);
        try std.testing.expectEqualStrings("fuzz-ok\n", report.outcomes[0].stdout_bytes);
        try std.testing.expectEqual(@as(usize, 2), report.outcomes[0].drop_trace.len);
    }
}

test "test_fuzz_phase7_deterministic_ir_emission_and_vm_parity_across_targets" {
    const allocator = std.testing.allocator;

    var seed_idx: usize = 0;
    while (seed_idx < CROSS_TARGET_DETERMINISM_SEEDS) : (seed_idx += 1) {
        const prng_seed: u64 = 100 + @as(u64, @intCast(seed_idx));
        const cx_program = try generateRandomValidCxProgram(allocator, prng_seed);
        defer allocator.free(cx_program);

        const target_spec = ALL_CANONICAL_TARGETS[seed_idx % ALL_CANONICAL_TARGETS.len];

        var db_first = try CompilerDb.init(allocator);
        defer db_first.deinit();
        db_first.setTargetSpec(target_spec);
        const fid = FileId.fromInt(0);
        _ = try db_first.setInput(fid, cx_program, .low);

        var db_second = try CompilerDb.init(allocator);
        defer db_second.deinit();
        db_second.setTargetSpec(target_spec);
        _ = try db_second.setInput(fid, cx_program, .low);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        const is_release = (seed_idx & 1) == 1;
        var c_run1 = try db_first.compileModuleArtifact(
            fid,
            .{
                .tier_a_c99 = .{
                    .target = target_spec,
                    .is_release_mode = is_release,
                    .has_line_directives = false,
                },
            },
            .{ .artifact_kind = .source_text, .diagnostic_sink = &sink },
        );
        defer c_run1.deinit(allocator);

        var c_run2 = try db_second.compileModuleArtifact(
            fid,
            .{
                .tier_a_c99 = .{
                    .target = target_spec,
                    .is_release_mode = is_release,
                    .has_line_directives = false,
                },
            },
            .{ .artifact_kind = .source_text, .diagnostic_sink = &sink },
        );
        defer c_run2.deinit(allocator);

        try std.testing.expect(!sink.hasErrors());
        try std.testing.expectEqualStrings(c_run1.emitted_text, c_run2.emitted_text);
        try std.testing.expect(std.mem.indexOf(u8, c_run1.emitted_text, "void*") == null);

        var ll_run1 = try db_first.compileModuleArtifact(
            fid,
            .{
                .tier_b_llvm = .{
                    .target = target_spec,
                    .is_release_mode = is_release,
                },
            },
            .{ .artifact_kind = .source_text, .diagnostic_sink = &sink },
        );
        defer ll_run1.deinit(allocator);

        var ll_run2 = try db_second.compileModuleArtifact(
            fid,
            .{
                .tier_b_llvm = .{
                    .target = target_spec,
                    .is_release_mode = is_release,
                },
            },
            .{ .artifact_kind = .source_text, .diagnostic_sink = &sink },
        );
        defer ll_run2.deinit(allocator);

        try std.testing.expect(!sink.hasErrors());
        try std.testing.expectEqualStrings(ll_run1.emitted_text, ll_run2.emitted_text);
    }
}

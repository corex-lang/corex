//! CoreX Stage 0 Build Graph (`build.zig`)
//!
//! Configures the Stage 0 Zig bootstrap compiler (`corex`), installing the unified binary into both
//! `build/stage0/` and the standard `zig-out/bin/` prefix per `.agents/skills/build/SKILL.md`.
//!
//! Provides `zig build`, `zig build run`, `zig build test` (executing both internal module tests and
//! `tests/test_runner.zig`), and `zig build bench` (executing `phase0_bench`, `phase1_bench`, and `phase2_bench`).

const std = @import("std");

// ------------------------------------- PUBLIC API --------------------------------------

/// Configures the CoreX Stage 0 build graph, artifacts, verification suites, and benchmark steps.
pub fn build(builder: *std.Build) void {
    const target = builder.standardTargetOptions(.{});
    const optimize = builder.standardOptimizeOption(.{});

    // [1] Define the canonical `corex` Stage 0 library module rooted at `stage0/src/root.zig`:
    const corex_mod = builder.addModule("corex", .{
        .root_source_file = builder.path("stage0/src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    // [2] Build the `corex` CLI executable and install into `build/stage0/` and `zig-out/bin/`:
    const exe_mod = builder.createModule(.{
        .root_source_file = builder.path("stage0/src/main.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "corex", .module = corex_mod },
        },
    });
    const corex_exe = builder.addExecutable(.{
        .name = "corex",
        .root_module = exe_mod,
    });
    builder.installArtifact(corex_exe);

    const install_stage0 = builder.addInstallArtifact(corex_exe, .{
        .dest_dir = .{ .override = .{ .custom = "../build/stage0" } },
    });
    builder.getInstallStep().dependOn(&install_stage0.step);

    // [3] Configure `zig build run -- <args>`:
    const run_cmd = builder.addRunArtifact(corex_exe);
    run_cmd.step.dependOn(builder.getInstallStep());
    run_cmd.addPassthruArgs();
    builder.step("run", "Run the CoreX Stage 0 compiler CLI").dependOn(&run_cmd.step);

    // [4] Configure `zig build test` (running `stage0/src/root.zig` and `tests/test_runner.zig`):
    const test_step = builder.step("test", "Run all CoreX Stage 0 unit, snapshot, fuzz, and drift tests");
    const root_unit_tests = builder.addTest(.{
        .name = "corex-stage0-unit",
        .root_module = corex_mod,
    });
    test_step.dependOn(&builder.addRunArtifact(root_unit_tests).step);

    const external_test_mod = builder.createModule(.{
        .root_source_file = builder.path("tests/test_runner.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "corex", .module = corex_mod },
        },
    });
    const external_tests = builder.addTest(.{
        .name = "corex-test-runner",
        .root_module = external_test_mod,
    });
    test_step.dependOn(&builder.addRunArtifact(external_tests).step);

    // [5] Configure `zig build bench` (executing `phase0_bench`, `phase1_bench`, and `phase2_bench` in `.fast`):
    const bench_optimize: std.builtin.Optimize = if (optimize == .debug) .fast else optimize;
    const bench_corex_mod = builder.createModule(.{
        .root_source_file = builder.path("stage0/src/root.zig"),
        .target = target,
        .optimize = bench_optimize,
    });
    const bench0_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase0_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench0_exe = builder.addExecutable(.{
        .name = "phase0_bench",
        .root_module = bench0_exe_mod,
    });
    const run_bench0 = builder.addRunArtifact(bench0_exe);

    const bench1_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase1_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench1_exe = builder.addExecutable(.{
        .name = "phase1_bench",
        .root_module = bench1_exe_mod,
    });
    const run_bench1 = builder.addRunArtifact(bench1_exe);
    run_bench1.step.dependOn(&run_bench0.step);

    const bench2_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase2_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench2_exe = builder.addExecutable(.{
        .name = "phase2_bench",
        .root_module = bench2_exe_mod,
    });
    const run_bench2 = builder.addRunArtifact(bench2_exe);
    run_bench2.step.dependOn(&run_bench1.step);

    const bench_step = builder.step("bench", "Run Phase 0, Phase 1, and Phase 2 statistical performance benchmarks");
    bench_step.dependOn(&run_bench0.step);
    bench_step.dependOn(&run_bench1.step);
    bench_step.dependOn(&run_bench2.step);

    builder.step("bench-phase1", "Run Phase 1 lexer performance benchmarks").dependOn(
        &builder.addRunArtifact(bench1_exe).step,
    );
    builder.step("bench-phase2", "Run Phase 2 parser performance benchmarks").dependOn(
        &builder.addRunArtifact(bench2_exe).step,
    );
}

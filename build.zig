//! CoreX Stage 0 Build Graph (`build.zig`)
//!
//! Configures the Stage 0 Zig bootstrap compiler (`corex`), installing the unified binary into both
//! `build/stage0/` and the standard `zig-out/bin/` prefix per `.agents/skills/build/SKILL.md`.
//!
//! Provides `zig build`, `zig build run`, `zig build test` (executing both internal module tests and
//! `tests/test_runner.zig`), and `zig build bench` (executing `phase0_bench` through `phase7_bench`).

const std = @import("std");

// -------------------------------------- INTERNALS --------------------------------------

/// Wires the optional `-Dllvm-prefix=<path>` C++20 `corex_llvm` static bridge into `mod`.
fn configureLlvmBridgeForModule(
    builder: *std.Build,
    mod: *std.Build.Module,
    llvm_prefix_opt: ?[]const u8,
) void {
    mod.addIncludePath(builder.path("stage0/src"));
    if (llvm_prefix_opt) |llvm_prefix| {
        const inc_dir = std.fmt.allocPrint(builder.allocator, "{s}/include", .{llvm_prefix}) catch @panic("OOM");
        const lib_dir = std.fmt.allocPrint(builder.allocator, "{s}/lib", .{llvm_prefix}) catch @panic("OOM");
        mod.addSystemIncludePath(.{ .cwd_relative = inc_dir });
        mod.addLibraryPath(.{ .cwd_relative = lib_dir });
        mod.link_libcpp = true;
        mod.addCSourceFile(.{
            .file = builder.path("stage0/src/corex_llvm.cpp"),
            .flags = &.{
                "-std=c++20",
                "-fno-exceptions",
                "-fno-rtti",
                "-D__STDC_CONSTANT_MACROS",
                "-D__STDC_FORMAT_MACROS",
                "-D__STDC_LIMIT_MACROS",
            },
        });
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Configures the CoreX Stage 0 build graph, artifacts, verification suites, and benchmark steps.
pub fn build(builder: *std.Build) void {
    const target = builder.standardTargetOptions(.{});
    const optimize = builder.standardOptimizeOption(.{});
    const llvm_prefix_opt = builder.option(
        []const u8,
        "llvm-prefix",
        "Optional LLVM 20–23 installation prefix enabling the static C++20 corex_llvm bridge",
    );

    const build_options = builder.addOptions();
    build_options.addOption(bool, "has_llvm_cpp_bridge", llvm_prefix_opt != null);

    // [1] Define the canonical `corex` Stage 0 library module rooted at `stage0/src/root.zig`:
    const corex_mod = builder.addModule("corex", .{
        .root_source_file = builder.path("stage0/src/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    corex_mod.addOptions("build_options", build_options);
    configureLlvmBridgeForModule(builder, corex_mod, llvm_prefix_opt);

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

    // [5] Configure `zig build bench` (executing all phase benchmark suites in `.fast`):
    const bench_optimize: std.builtin.Optimize = if (optimize == .debug) .fast else optimize;
    const bench_corex_mod = builder.createModule(.{
        .root_source_file = builder.path("stage0/src/root.zig"),
        .target = target,
        .optimize = bench_optimize,
    });
    bench_corex_mod.addOptions("build_options", build_options);
    configureLlvmBridgeForModule(builder, bench_corex_mod, llvm_prefix_opt);
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

    const bench3_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase3_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench3_exe = builder.addExecutable(.{
        .name = "phase3_bench",
        .root_module = bench3_exe_mod,
    });
    const run_bench3 = builder.addRunArtifact(bench3_exe);
    run_bench3.step.dependOn(&run_bench2.step);

    const bench4_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase4_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench4_exe = builder.addExecutable(.{
        .name = "phase4_bench",
        .root_module = bench4_exe_mod,
    });
    const run_bench4 = builder.addRunArtifact(bench4_exe);
    run_bench4.step.dependOn(&run_bench3.step);

    const bench5_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase5_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench5_exe = builder.addExecutable(.{
        .name = "phase5_bench",
        .root_module = bench5_exe_mod,
    });
    const run_bench5 = builder.addRunArtifact(bench5_exe);
    run_bench5.step.dependOn(&run_bench4.step);

    const bench6_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase6_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench6_exe = builder.addExecutable(.{
        .name = "phase6_bench",
        .root_module = bench6_exe_mod,
    });
    const run_bench6 = builder.addRunArtifact(bench6_exe);
    run_bench6.step.dependOn(&run_bench5.step);

    const bench7_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase7_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench7_exe = builder.addExecutable(.{
        .name = "phase7_bench",
        .root_module = bench7_exe_mod,
    });
    const run_bench7 = builder.addRunArtifact(bench7_exe);
    run_bench7.step.dependOn(&run_bench6.step);

    const bench_step = builder.step(
        "bench",
        "Run Phase 0 through Phase 7 statistical performance benchmarks",
    );
    bench_step.dependOn(&run_bench0.step);
    bench_step.dependOn(&run_bench1.step);
    bench_step.dependOn(&run_bench2.step);
    bench_step.dependOn(&run_bench3.step);
    bench_step.dependOn(&run_bench4.step);
    bench_step.dependOn(&run_bench5.step);
    bench_step.dependOn(&run_bench6.step);
    bench_step.dependOn(&run_bench7.step);

    builder.step("bench-phase1", "Run Phase 1 lexer performance benchmarks").dependOn(
        &builder.addRunArtifact(bench1_exe).step,
    );
    builder.step("bench-phase2", "Run Phase 2 parser performance benchmarks").dependOn(
        &builder.addRunArtifact(bench2_exe).step,
    );
    builder.step("bench-phase3", "Run Phase 3 query engine & formatter performance benchmarks").dependOn(
        &builder.addRunArtifact(bench3_exe).step,
    );
    builder.step("bench-phase4", "Run Phase 4 name resolution & type checker performance benchmarks").dependOn(
        &builder.addRunArtifact(bench4_exe).step,
    );
    builder.step("bench-phase5", "Run Phase 5 HIR, MIR, optimizer & MirVm performance benchmarks").dependOn(
        &builder.addRunArtifact(bench5_exe).step,
    );
    builder.step("bench-phase6", "Run Phase 6 MIR SAST, drop elaboration & Pentagon BCE benchmarks").dependOn(
        &builder.addRunArtifact(bench6_exe).step,
    );
    builder.step("bench-phase7", "Run Phase 7 ABI, Tier A C99, Tier B LLVM & C-baseline benchmarks").dependOn(
        &builder.addRunArtifact(bench7_exe).step,
    );
}

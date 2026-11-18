//! CoreX Stage 0 Build Graph (`build.zig`)
//!
//! Configures the Stage 0 Zig bootstrap compiler (`corex`), installing the unified binary into both
//! `build/stage0/` and the standard `zig-out/bin/` prefix per `.agents/skills/build/SKILL.md`.
//!
//! Provides `zig build`, `zig build run`, `zig build test` (executing both internal module tests and
//! `tests/test_runner.zig`), and `zig build bench` (executing `phase0_bench` through `phase7_bench`).

const std = @import("std");

// ---------------------------------------- TYPES ----------------------------------------

/// Candidate library filename in `<llvm-prefix>/lib` paired with its canonical `-l<name>` stem.
const LibCandidate = struct {
    /// Exact filename probed inside `<llvm-prefix>/lib`.
    file_name: []const u8,
    /// Linker stem passed to `Module.linkSystemLibrary`.
    link_name: []const u8,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Candidate filenames for `lldCommon` probed inside `<llvm-prefix>/lib`.
const LLD_COMMON_CANDIDATES = [_][]const u8{
    "liblldCommon.a",
    "lldCommon.lib",
    "liblldCommon.so",
    "liblldCommon.dylib",
};

/// Embedded `lld` driver libraries linked when `lldCommon` is present in `<llvm-prefix>/lib`.
const LLD_DRIVER_LIBS = [_][]const u8{
    "lldCommon",
    "lldELF",
    "lldMachO",
    "lldCOFF",
    "lldMinGW",
    "lldWasm",
};

/// Monolithic shared/import `LLVM` library candidates exporting full `llvm::*` C++ symbols.
const LLVM_DYLIB_CANDIDATES = [_]LibCandidate{
    .{ .file_name = "libLLVM.so", .link_name = "LLVM" },
    .{ .file_name = "libLLVM.dylib", .link_name = "LLVM" },
    .{ .file_name = "libLLVM-23.so", .link_name = "LLVM-23" },
    .{ .file_name = "libLLVM-22.so", .link_name = "LLVM-22" },
    .{ .file_name = "libLLVM-21.so", .link_name = "LLVM-21" },
    .{ .file_name = "libLLVM-20.so", .link_name = "LLVM-20" },
    .{ .file_name = "libLLVM.dll.a", .link_name = "LLVM" },
    .{ .file_name = "LLVM.lib", .link_name = "LLVM" },
};

/// Fallback `LLVM-C` shared/import library candidates when neither monolithic `LLVM` nor static `LLVM*` archives exist.
const LLVM_C_FALLBACK_CANDIDATES = [_]LibCandidate{
    .{ .file_name = "LLVM-C.lib", .link_name = "LLVM-C" },
    .{ .file_name = "libLLVM-C.so", .link_name = "LLVM-C" },
    .{ .file_name = "libLLVM-C.dylib", .link_name = "LLVM-C" },
    .{ .file_name = "libLLVM-C.dll.a", .link_name = "LLVM-C" },
};

/// Optional `zlib` compression library candidates probed in `<llvm-prefix>/lib`.
const ZLIB_CANDIDATES = [_]LibCandidate{
    .{ .file_name = "libz.a", .link_name = "z" },
    .{ .file_name = "libz.so", .link_name = "z" },
    .{ .file_name = "libz.dylib", .link_name = "z" },
    .{ .file_name = "zlibstatic.lib", .link_name = "zlibstatic" },
    .{ .file_name = "zlib.lib", .link_name = "zlib" },
    .{ .file_name = "z.lib", .link_name = "z" },
};

/// Optional `zstd` compression library candidates probed in `<llvm-prefix>/lib`.
const ZSTD_CANDIDATES = [_]LibCandidate{
    .{ .file_name = "libzstd.a", .link_name = "zstd" },
    .{ .file_name = "libzstd.so", .link_name = "zstd" },
    .{ .file_name = "libzstd.dylib", .link_name = "zstd" },
    .{ .file_name = "zstd_static.lib", .link_name = "zstd_static" },
    .{ .file_name = "zstd.lib", .link_name = "zstd" },
};

/// Windows Win32 import libraries required by static `LLVMSupport` / `lld`.
const WINDOWS_LLVM_SYSTEM_LIBS = [_][]const u8{
    "advapi32",
    "ntdll",
    "ole32",
    "psapi",
    "shell32",
    "uuid",
    "version",
    "ws2_32",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` when `<lib_dir>/<file_name>` exists and can be opened for reading.
fn hasFileInDir(builder: *std.Build, lib_dir: []const u8, file_name: []const u8) bool {
    const candidate_path = std.fs.path.join(builder.allocator, &.{ lib_dir, file_name }) catch return false;
    if (std.Io.Dir.cwd().openFile(builder.graph.io, candidate_path, .{ .mode = .read_only })) |opened| {
        opened.close(builder.graph.io);
        return true;
    } else |_| {
        return false;
    }
}

/// Returns `true` when `<lib_dir>` contains `liblldCommon.a`, `lldCommon.lib`, or an equivalent `lldCommon` binary.
fn hasLldCommonInDir(builder: *std.Build, lib_dir: []const u8) bool {
    for (LLD_COMMON_CANDIDATES) |file_name| {
        if (hasFileInDir(builder, lib_dir, file_name)) return true;
    }
    return false;
}

/// Returns the first matching `LibCandidate.link_name` present in `lib_dir`, or `null`.
fn findFirstLibCandidate(builder: *std.Build, lib_dir: []const u8, candidates: []const LibCandidate) ?[]const u8 {
    for (candidates) |cand| {
        if (hasFileInDir(builder, lib_dir, cand.file_name)) return cand.link_name;
    }
    return null;
}

/// Extracts the `-l<stem>` name for a static `libLLVM*.a` or `LLVM*.lib` component archive (`null` if non-component).
fn extractLlvmStaticArchiveStem(file_name: []const u8) ?[]const u8 {
    if (std.mem.startsWith(u8, file_name, "libLLVM") and std.mem.endsWith(u8, file_name, ".a")) {
        const stem = file_name["lib".len .. file_name.len - ".a".len];
        if (std.mem.eql(u8, stem, "LLVM-C") or
            std.mem.startsWith(u8, stem, "LLVMTesting") or
            std.mem.startsWith(u8, stem, "LLVMExegesis"))
        {
            return null;
        }
        return stem;
    }
    if (std.mem.startsWith(u8, file_name, "LLVM") and std.mem.endsWith(u8, file_name, ".lib")) {
        const stem = file_name[0 .. file_name.len - ".lib".len];
        if (std.mem.eql(u8, stem, "LLVM") or
            std.mem.eql(u8, stem, "LLVM-C") or
            std.mem.startsWith(u8, stem, "LLVMTesting") or
            std.mem.startsWith(u8, stem, "LLVMExegesis"))
        {
            return null;
        }
        return stem;
    }
    return null;
}

/// Discovers and links monolithic shared `LLVM` or all static `LLVM*` archives in `lib_dir` plus host system libraries.
fn linkLlvmAndSystemLibraries(builder: *std.Build, mod: *std.Build.Module, lib_dir: []const u8) void {
    if (findFirstLibCandidate(builder, lib_dir, &LLVM_DYLIB_CANDIDATES)) |shared_llvm| {
        mod.linkSystemLibrary(shared_llvm, .{ .use_pkg_config = .no });
        return;
    }

    var static_stems: std.ArrayListUnmanaged([]const u8) = .empty;
    if (std.Io.Dir.cwd().openDir(builder.graph.io, lib_dir, .{ .iterate = true })) |opened_dir_val| {
        var opened_dir = opened_dir_val;
        defer opened_dir.close(builder.graph.io);
        if (opened_dir.walk(builder.allocator)) |walker_val| {
            var walker = walker_val;
            defer walker.deinit();
            while (walker.next(builder.graph.io) catch null) |entry| {
                if (entry.kind != .file or std.mem.indexOfAny(u8, entry.path, "/\\") != null) continue;
                if (extractLlvmStaticArchiveStem(entry.path)) |raw_stem| {
                    const owned_stem = builder.allocator.dupe(u8, raw_stem) catch @panic("OOM");
                    static_stems.append(builder.allocator, owned_stem) catch @panic("OOM");
                }
            }
        } else |_| {}
    } else |_| {}

    if (static_stems.items.len > 0) {
        std.mem.sort([]const u8, static_stems.items, {}, struct {
            /// Orders discovered `LLVM*` library stems lexicographically for deterministic link lines.
            fn lessThan(_: void, lhs: []const u8, rhs: []const u8) bool {
                return std.mem.order(u8, lhs, rhs) == .lt;
            }
        }.lessThan);
        for (static_stems.items) |llvm_stem| {
            mod.linkSystemLibrary(llvm_stem, .{ .use_pkg_config = .no });
        }
        if (findFirstLibCandidate(builder, lib_dir, &ZLIB_CANDIDATES)) |zlib_name| {
            mod.linkSystemLibrary(zlib_name, .{ .use_pkg_config = .no });
        }
        if (findFirstLibCandidate(builder, lib_dir, &ZSTD_CANDIDATES)) |zstd_name| {
            mod.linkSystemLibrary(zstd_name, .{ .use_pkg_config = .no });
        }
        const os_tag = if (mod.resolved_target) |rt| rt.result.os.tag else @import("builtin").os.tag;
        if (os_tag == .windows) {
            for (WINDOWS_LLVM_SYSTEM_LIBS) |win_lib| {
                mod.linkSystemLibrary(win_lib, .{ .use_pkg_config = .no });
            }
        } else {
            mod.linkSystemLibrary("pthread", .{ .use_pkg_config = .no });
            mod.linkSystemLibrary("m", .{ .use_pkg_config = .no });
            if (os_tag != .macos) {
                mod.linkSystemLibrary("dl", .{ .use_pkg_config = .no });
            }
        }
    } else if (findFirstLibCandidate(builder, lib_dir, &LLVM_C_FALLBACK_CANDIDATES)) |llvm_c_name| {
        mod.linkSystemLibrary(llvm_c_name, .{ .use_pkg_config = .no });
    }
}

/// Wires the optional `-Dllvm-prefix=<path>` C++20 `corex_llvm` static bridge (and `lld` if installed) into `mod`.
fn configureLlvmBridgeForModule(
    builder: *std.Build,
    mod: *std.Build.Module,
    llvm_prefix_opt: ?[]const u8,
) void {
    mod.addIncludePath(builder.path("stage0/src"));
    if (llvm_prefix_opt) |llvm_prefix| {
        const inc_dir = std.fmt.allocPrint(builder.allocator, "{s}/include", .{llvm_prefix}) catch @panic("OOM");
        const lib_dir = std.fmt.allocPrint(builder.allocator, "{s}/lib", .{llvm_prefix}) catch @panic("OOM");
        const has_lld = hasLldCommonInDir(builder, lib_dir);
        mod.addSystemIncludePath(.{ .cwd_relative = inc_dir });
        mod.addLibraryPath(.{ .cwd_relative = lib_dir });
        mod.link_libcpp = true;
        const base_flags: []const []const u8 = if (has_lld)
            &.{
                "-std=c++20",
                "-fno-exceptions",
                "-fno-rtti",
                "-D__STDC_CONSTANT_MACROS",
                "-D__STDC_FORMAT_MACROS",
                "-D__STDC_LIMIT_MACROS",
                "-DCOREX_HAS_LLD=1",
            }
        else
            &.{
                "-std=c++20",
                "-fno-exceptions",
                "-fno-rtti",
                "-D__STDC_CONSTANT_MACROS",
                "-D__STDC_FORMAT_MACROS",
                "-D__STDC_LIMIT_MACROS",
            };
        mod.addCSourceFile(.{
            .file = builder.path("stage0/src/corex_llvm.cpp"),
            .flags = base_flags,
        });
        if (has_lld) {
            for (LLD_DRIVER_LIBS) |lld_lib| {
                mod.linkSystemLibrary(lld_lib, .{ .use_pkg_config = .no });
            }
        }
        linkLlvmAndSystemLibraries(builder, mod, lib_dir);
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

    const bench8_exe_mod = builder.createModule(.{
        .root_source_file = builder.path("bench/suites/phase8_bench.zig"),
        .target = target,
        .optimize = bench_optimize,
        .imports = &.{
            .{ .name = "corex", .module = bench_corex_mod },
        },
    });
    const bench8_exe = builder.addExecutable(.{
        .name = "phase8_bench",
        .root_module = bench8_exe_mod,
    });
    const run_bench8 = builder.addRunArtifact(bench8_exe);
    run_bench8.step.dependOn(&run_bench7.step);

    const bench_step = builder.step(
        "bench",
        "Run Phase 0 through Phase 8 statistical performance benchmarks",
    );
    bench_step.dependOn(&run_bench0.step);
    bench_step.dependOn(&run_bench1.step);
    bench_step.dependOn(&run_bench2.step);
    bench_step.dependOn(&run_bench3.step);
    bench_step.dependOn(&run_bench4.step);
    bench_step.dependOn(&run_bench5.step);
    bench_step.dependOn(&run_bench6.step);
    bench_step.dependOn(&run_bench7.step);
    bench_step.dependOn(&run_bench8.step);

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
    builder.step("bench-phase8", "Run Phase 8 translate-c, mir_async & C FFI baseline benchmarks").dependOn(
        &builder.addRunArtifact(bench8_exe).step,
    );
}

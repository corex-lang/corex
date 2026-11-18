//! Phase 8 `translate-c`, Coroutine Frame Coloring & C FFI Baseline Benchmark Suite
//!
//! Measures zero-`libclang` C11/C23 header translation throughput, `mir_async` liveness-colored
//! coroutine frame sizing, and native Tier B `--release` `extern "C"` call overhead against `zig cc -O2`.
//!
//! Compiles the shared C99 callee as a separate translation unit so cross-ABI calls are never inlined
//! away, and verifies identical exit-code checksums between CoreX and C99 before timed runs.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const TargetLayout = corex.TargetLayout;
const CompilerDb = corex.CompilerDb;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;
const BenchConfig = corex.bench_harness.BenchConfig;
const BenchResult = corex.bench_harness.BenchResult;
const c_translate = corex.c_translate;
const mir_async = corex.mir_async;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-built ~360-line C11/C23 header buffer for Case 1 (`translate-c` throughput).
const PreparedCHeaderCorpus = struct {
    /// Owned UTF-8 C11/C23 header source bytes (`>= 320` lines).
    owned_c_header: []u8,

    /// Releases `owned_c_header`.
    fn deinit(self: *PreparedCHeaderCorpus, allocator: std.mem.Allocator) void {
        allocator.free(self.owned_c_header);
    }
};

/// Pre-lowered `64`-coroutine post-demotion `MIR` bundle for Case 2 (`mir_async` coloring).
const PreparedAsyncMirState = struct {
    /// Owned `.cx` source buffer containing `64` multi-suspend `async fn` items.
    owned_cx_source: []u8,
    /// Lowered `Source -> HIR -> MIR` bundle with cross-suspend SSA values demoted.
    lowered_bundle: corex.mir.MirSourceBundle,

    /// Releases `lowered_bundle` and `owned_cx_source`.
    fn deinit(self: *PreparedAsyncMirState, allocator: std.mem.Allocator) void {
        self.lowered_bundle.deinit();
        allocator.free(self.owned_cx_source);
    }
};

/// Pre-compiled native FFI benchmark binaries and shared C `.o` helper for Cases 3–4.
const PreparedFfiBinaries = struct {
    /// Process `Io` handle borrowed from `main`.
    io: std.Io,
    /// Scratch directory containing compiled benchmark artifacts.
    scratch_dir: []u8,
    /// Native CoreX Tier B (`--release -O2`) FFI caller binary path.
    corex_ffi_exe: []u8,
    /// Native `zig cc -O2` pure C99 FFI caller baseline binary path.
    c_baseline_exe: []u8,

    /// Deletes `scratch_dir` and frees owned path slices.
    fn deinit(self: *PreparedFfiBinaries, allocator: std.mem.Allocator) void {
        std.Io.Dir.cwd().deleteTree(self.io, self.scratch_dir) catch {};
        allocator.free(self.scratch_dir);
        allocator.free(self.corex_ffi_exe);
        allocator.free(self.c_baseline_exe);
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical benchmark warmup count (`5` untimed iterations).
const BENCH_WARMUP_COUNT: u32 = 5;
/// Canonical benchmark timed count (`30` measured iterations).
const BENCH_MEASURED_COUNT: u32 = 30;
/// Number of generated declaration groups in the multi-hundred-line C11/C23 benchmark header.
const SYNTHETIC_C_GROUP_COUNT: usize = 24;
/// Number of generated multi-suspend `async fn` coroutines in Case 2.
const SYNTHETIC_ASYNC_CORO_COUNT: usize = 64;
/// Shared C99 FFI callee compiled separately (`-c -O2`) so cross-TU ABI calls are never inlined away.
const FFI_CALLEE_C_SOURCE =
    "#include <stdint.h>\n" ++
    "uint64_t cx_bench_c_mix_step(uint64_t state_val, uint64_t round_idx) {\n" ++
    "    uint64_t mixed = (state_val ^ (round_idx + 0x9E3779B97F4A7C15ULL)) * 0xBF58476D1CE4E5B9ULL;\n" ++
    "    return mixed ^ (mixed >> 29);\n" ++
    "}\n";
/// CoreX `extern "C"` FFI caller executing `2,000,000` cross-ABI calls in Case 3.
const FFI_CALLER_CX_SOURCE =
    "//! Phase 8 Zero-Overhead `extern \"C\"` FFI Call Loop Benchmark\n" ++
    "extern \"C\" fn cx_bench_c_mix_step(state_val: u64, round_idx: u64) -> u64;\n\n" ++
    "pub fn run_ffi_loop(total_rounds: u64, init_seed: u64) -> u64 {\n" ++
    "    var state_acc: u64 = init_seed;\n" ++
    "    var iter_i: u64 = 0;\n" ++
    "    while iter_i < total_rounds {\n" ++
    "        state_acc = unsafe { cx_bench_c_mix_step(state_acc, iter_i) };\n" ++
    "        iter_i += 1;\n" ++
    "    }\n" ++
    "    return state_acc;\n" ++
    "}\n\n" ++
    "pub fn main() -> i32 {\n" ++
    "    let final_digest: u64 = run_ffi_loop(2_000_000, 0xCAFE_BABE_1234_5678);\n" ++
    "    return ((final_digest ^ (final_digest >> 32)) & 127) as i32;\n" ++
    "}\n";
/// Equivalent ISO C99 `extern` caller compiled with `zig cc -O2` in Case 4.
const FFI_CALLER_C_SOURCE =
    "#include <stdint.h>\n" ++
    "extern uint64_t cx_bench_c_mix_step(uint64_t state_val, uint64_t round_idx);\n" ++
    "static uint64_t run_ffi_loop(uint64_t total_rounds, uint64_t init_seed) {\n" ++
    "    uint64_t state_acc = init_seed;\n" ++
    "    for (uint64_t iter_i = 0; iter_i < total_rounds; iter_i += 1) {\n" ++
    "        state_acc = cx_bench_c_mix_step(state_acc, iter_i);\n" ++
    "    }\n" ++
    "    return state_acc;\n" ++
    "}\n" ++
    "int main(void) {\n" ++
    "    volatile uint64_t seed = 0xCAFEBABE12345678ULL;\n" ++
    "    uint64_t final_digest = run_ffi_loop(2000000ULL, seed);\n" ++
    "    return (int)((final_digest ^ (final_digest >> 32)) & 127ULL);\n" ++
    "}\n";

// -------------------------------------- INTERNALS --------------------------------------

/// Lazily initialized ~360-line C11/C23 header buffer for Case 1.
var shared_c_header_corpus: ?PreparedCHeaderCorpus = null;

/// Lazily initialized `64`-coroutine `MIR` bundle for Case 2.
var shared_async_mir_state: ?PreparedAsyncMirState = null;

/// Pre-compiled native FFI benchmark binaries for Cases 3–4.
var shared_ffi_binaries: ?PreparedFfiBinaries = null;

/// Synthesizes a realistic ~360-line C11/C23 systems header (`SYNTHETIC_C_GROUP_COUNT` groups).
fn buildSyntheticCHeaderCorpus(allocator: std.mem.Allocator) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    try builder.appendSlice(
        allocator,
        "#pragma once\n#include <stdint.h>\n#include <stddef.h>\n#include <stdbool.h>\n\n",
    );

    var group_buf: [1024]u8 = undefined;
    var grp_i: usize = 0;
    while (grp_i < SYNTHETIC_C_GROUP_COUNT) : (grp_i += 1) {
        const group_text = try std.fmt.bufPrint(
            &group_buf,
            "#define CX_SYS_PORT_{d:0>2} {d}\n" ++
                "#define CX_SYS_MASK_{d:0>2} 0x{X:0>4}U\n" ++
                "enum CxRingMode_{d:0>2} {{\n" ++
                "    CX_RING_IDLE_{d:0>2} = 0,\n" ++
                "    CX_RING_ARMED_{d:0>2} = {d},\n" ++
                "    CX_RING_DRAIN_{d:0>2} = {d}\n" ++
                "}};\n" ++
                "typedef struct CxPacketHdr_{d:0>2} {{\n" ++
                "    uint32_t stream_id;\n" ++
                "    unsigned int opcode_bits : 6;\n" ++
                "    unsigned int priority_bits : 5;\n" ++
                "    int signed_delta : 13;\n" ++
                "    uint64_t timestamp_ns;\n" ++
                "}} CxPacketHdr_{d:0>2};\n" ++
                "int32_t cx_sys_submit_{d:0>2}(const CxPacketHdr_{d:0>2} *hdr, size_t count);\n" ++
                "int32_t cx_sys_trace_{d:0>2}(const char *tag_str, ...);\n\n",
            .{
                grp_i,
                1024 + grp_i * 4,
                grp_i,
                0x100 + grp_i,
                grp_i,
                grp_i,
                grp_i,
                grp_i + 1,
                grp_i,
                grp_i + 10,
                grp_i,
                grp_i,
                grp_i,
                grp_i,
                grp_i,
            },
        );
        try builder.appendSlice(allocator, group_text);
    }
    return builder.toOwnedSlice(allocator);
}

/// Lazily initializes `shared_c_header_corpus`.
fn getOrInitCHeaderCorpus(allocator: std.mem.Allocator) !*PreparedCHeaderCorpus {
    if (shared_c_header_corpus) |*existing| return existing;
    shared_c_header_corpus = .{
        .owned_c_header = try buildSyntheticCHeaderCorpus(allocator),
    };
    return &shared_c_header_corpus.?;
}

/// Synthesizes a `64`-coroutine `.cx` module exercising sequential `.await` buffer reuse & `FramePinned`.
fn buildSyntheticAsyncModuleSource(allocator: std.mem.Allocator) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    try builder.appendSlice(
        allocator,
        "//! Synthetic 64-Coroutine Phase 8 Frame Coloring Benchmark Module\n" ++
            "pub async fn touch_pinned(slot_ref: &mut u64, step_v: u64) {\n" ++
            "    slot_ref.* = slot_ref.* +% step_v;\n" ++
            "    cx.async.yield_now().await;\n" ++
            "}\n\n",
    );

    var coro_buf: [768]u8 = undefined;
    var fn_idx: usize = 0;
    while (fn_idx < SYNTHETIC_ASYNC_CORO_COUNT) : (fn_idx += 1) {
        const coro_text = try std.fmt.bufPrint(
            &coro_buf,
            "pub async fn coro_worker_{d:0>3}(seed_byte: u8) -> u64 {{\n" ++
                "    var pinned_acc: u64 = {d}_u64;\n" ++
                "    let phase_one_buf: [u8; 256] = [seed_byte; 256];\n" ++
                "    touch_pinned(&mut pinned_acc, 3_u64).await;\n" ++
                "    let mid_byte: u8 = phase_one_buf[127] +% 1_u8;\n" ++
                "    let phase_two_buf: [u8; 256] = [mid_byte; 256];\n" ++
                "    cx.async.yield_now().await;\n" ++
                "    return pinned_acc +% (phase_two_buf[63] as u64);\n" ++
                "}}\n\n",
            .{ fn_idx, fn_idx + 1 },
        );
        try builder.appendSlice(allocator, coro_text);
    }
    return builder.toOwnedSlice(allocator);
}

/// Lazily initializes `shared_async_mir_state`.
fn getOrInitAsyncMirState(allocator: std.mem.Allocator) !*PreparedAsyncMirState {
    if (shared_async_mir_state) |*existing| return existing;

    const owned_src = try buildSyntheticAsyncModuleSource(allocator);
    errdefer allocator.free(owned_src);

    var lowered = try corex.lowerSourceToMir(
        allocator,
        FileId.fromInt(1),
        owned_src,
        TargetLayout.NATIVE_64,
        .{},
    );
    errdefer lowered.deinit();

    for (lowered.mir_bundle.bodies.items) |*body_ptr| {
        if (body_ptr.is_async) {
            try mir_async.demoteCrossSuspendSsaValues(
                allocator,
                body_ptr,
                &lowered.hir_bundle.pool,
                &lowered.hir_bundle.sym_table,
            );
        }
    }

    shared_async_mir_state = .{
        .owned_cx_source = owned_src,
        .lowered_bundle = lowered,
    };
    return &shared_async_mir_state.?;
}

/// Compiles the shared C99 callee `.o`, CoreX `--release` FFI caller, and `zig cc -O2` baseline caller.
fn preparePhase8NativeBinaries(allocator: std.mem.Allocator, io: std.Io) !PreparedFfiBinaries {
    const host_spec = TargetSpec.host();
    const exe_ext = host_spec.executableExtension();
    const obj_ext = host_spec.defaultObjExtension();

    const scratch_dir = try allocator.dupe(u8, ".zig-cache/phase8_bench_ffi");
    errdefer allocator.free(scratch_dir);
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    const corex_exe = try std.fmt.allocPrint(allocator, "{s}/cx_ffi_caller{s}", .{ scratch_dir, exe_ext });
    errdefer allocator.free(corex_exe);
    const c_base_exe = try std.fmt.allocPrint(allocator, "{s}/c_ffi_caller{s}", .{ scratch_dir, exe_ext });
    errdefer allocator.free(c_base_exe);

    const c_callee_src = try std.fmt.allocPrint(allocator, "{s}/c_callee.c", .{scratch_dir});
    defer allocator.free(c_callee_src);
    const c_callee_obj = try std.fmt.allocPrint(allocator, "{s}/c_callee{s}", .{ scratch_dir, obj_ext });
    defer allocator.free(c_callee_obj);
    const c_caller_src = try std.fmt.allocPrint(allocator, "{s}/c_caller.c", .{scratch_dir});
    defer allocator.free(c_caller_src);

    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = c_callee_src, .data = FFI_CALLEE_C_SOURCE });
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = c_caller_src, .data = FFI_CALLER_C_SOURCE });

    const zig_exe = try corex.codegen_abi.resolveZigExecutable(io, allocator, null);
    defer allocator.free(zig_exe);

    // [1] Compile shared C99 callee object (`zig cc -c -O2`):
    const cc_obj = try std.process.run(allocator, io, .{
        .argv = &.{
            zig_exe,
            "cc",
            "-c",
            "-std=c99",
            "-O2",
            "-target",
            host_spec.asZigTargetTriple(),
            c_callee_src,
            "-o",
            c_callee_obj,
        },
    });
    defer allocator.free(cc_obj.stdout);
    defer allocator.free(cc_obj.stderr);
    if (!cc_obj.term.success()) return error.CCalleeCompileFailed;

    // [2] Compile CoreX Tier B (`--release -O2`) FFI caller linked against `c_callee_obj`:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        db.setTargetSpec(host_spec);
        const fid = FileId.fromInt(0);
        _ = try db.setInput(fid, FFI_CALLER_CX_SOURCE, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var art = try db.compileModuleArtifact(
            fid,
            .{
                .tier_b_llvm = .{
                    .target = host_spec,
                    .is_release_mode = true,
                    .opt_level = .release_fast_o2,
                },
            },
            .{
                .artifact_kind = .executable,
                .extra_libs = &.{c_callee_obj},
                .output_path = corex_exe,
                .io = io,
                .diagnostic_sink = &sink,
            },
        );
        defer art.deinit(allocator);
        if (sink.hasErrors()) return error.CorexFfiCallerCompileFailed;
    }

    // [3] Compile `zig cc -O2` pure C99 baseline caller linked against the exact same `c_callee_obj`:
    const cc_exe = try std.process.run(allocator, io, .{
        .argv = &.{
            zig_exe,
            "cc",
            "-std=c99",
            "-O2",
            "-target",
            host_spec.asZigTargetTriple(),
            c_caller_src,
            c_callee_obj,
            "-o",
            c_base_exe,
        },
    });
    defer allocator.free(cc_exe.stdout);
    defer allocator.free(cc_exe.stderr);
    if (!cc_exe.term.success()) return error.CBaselineCompileFailed;

    // [4] Verify identical exit-code checksum between CoreX `--release` and `zig cc -O2`:
    const cx_run = try std.process.run(allocator, io, .{ .argv = &.{corex_exe} });
    defer allocator.free(cx_run.stdout);
    defer allocator.free(cx_run.stderr);
    const c_run = try std.process.run(allocator, io, .{ .argv = &.{c_base_exe} });
    defer allocator.free(c_run.stdout);
    defer allocator.free(c_run.stderr);

    const cx_status: u8 = switch (cx_run.term) {
        .exited => |code| code,
        else => return error.CorexFfiBinaryCrashed,
    };
    const c_status: u8 = switch (c_run.term) {
        .exited => |code| code,
        else => return error.CBaselineBinaryCrashed,
    };
    if (cx_status != c_status) return error.FfiChecksumMismatch;

    return .{
        .io = io,
        .scratch_dir = scratch_dir,
        .corex_ffi_exe = corex_exe,
        .c_baseline_exe = c_base_exe,
    };
}

/// Case 1 (`translate_c_header_360loc`): Zero-`libclang` C11/C23 preprocess + AST + `.cx` emission.
fn benchTranslateCHeader360Loc(allocator: std.mem.Allocator) !usize {
    const corpus = try getOrInitCHeaderCorpus(allocator);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    const emitted_cx = try c_translate.translateHeaderSource(
        allocator,
        corpus.owned_c_header,
        "sys_ring_bench.h",
        .none,
        .{ .target = TargetSpec.X86_64_LINUX_GNU },
        .{ .is_formatted = true },
        &sink,
    );
    defer allocator.free(emitted_cx);
    if (sink.hasErrors()) return error.TranslateCBenchmarkFailed;

    std.mem.doNotOptimizeAway(emitted_cx.len);
    return corpus.owned_c_header.len;
}

/// Case 2 (`mir_async_color_64_coros`): Liveness-colored coroutine frame layout & `<= 16 KiB` verification.
fn benchMirAsyncFrameColor64Coros(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitAsyncMirState(allocator);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var plan = try mir_async.analyzeAsyncModule(
        allocator,
        state.lowered_bundle.mir_bundle.bodies.items,
        &state.lowered_bundle.hir_bundle.pool,
        &state.lowered_bundle.hir_bundle.sym_table,
        TargetLayout.NATIVE_64,
        &sink,
    );
    defer plan.deinit();
    if (sink.hasErrors()) return error.MirAsyncBenchmarkFailed;

    var total_reused_slots: u32 = 0;
    for (plan.body_plans) |body_plan| {
        if (!body_plan.is_async) continue;
        if (body_plan.has_exceeded_inline_cap or
            body_plan.frame_layout.total_frame_bytes > corex.ASYNC_INLINE_FRAME_CAP_BYTES)
        {
            return error.AsyncInlineCapExceeded;
        }
        total_reused_slots += body_plan.reused_slot_count;
    }
    if (total_reused_slots < SYNTHETIC_ASYNC_CORO_COUNT) return error.ExpectedSlotReuse;
    std.mem.doNotOptimizeAway(total_reused_slots);
    return state.owned_cx_source.len;
}

/// Case 3 (`ffi_extern_c_corex_release`): Executes `2M` `extern "C"` calls in native CoreX `--release`.
fn benchFfiExternCCorexRelease(allocator: std.mem.Allocator) !usize {
    const bins = shared_ffi_binaries orelse return error.MissingNativeFfiBinaries;
    const run_res = try std.process.run(allocator, bins.io, .{ .argv = &.{bins.corex_ffi_exe} });
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);
    return FFI_CALLER_CX_SOURCE.len;
}

/// Case 4 (`ffi_extern_c_zig_cc_o2_base`): Executes `2M` `extern` calls in `zig cc -O2` pure C99 baseline.
fn benchFfiExternCCBaseline(allocator: std.mem.Allocator) !usize {
    const bins = shared_ffi_binaries orelse return error.MissingNativeFfiBinaries;
    const run_res = try std.process.run(allocator, bins.io, .{ .argv = &.{bins.c_baseline_exe} });
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);
    return FFI_CALLER_C_SOURCE.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 8 `translate-c`, `mir_async`, and C FFI benchmark suite and renders the monochrome table.
pub fn main(init: std.process.Init) !void {
    shared_ffi_binaries = try preparePhase8NativeBinaries(init.gpa, init.io);
    defer {
        if (shared_ffi_binaries) |*bins_ref| {
            bins_ref.deinit(init.gpa);
            shared_ffi_binaries = null;
        }
        if (shared_async_mir_state) |*async_ref| {
            async_ref.deinit(init.gpa);
            shared_async_mir_state = null;
        }
        if (shared_c_header_corpus) |*c_ref| {
            c_ref.deinit(init.gpa);
            shared_c_header_corpus = null;
        }
    }

    const cases = [_]BenchCase{
        .{
            .name = "translate_c_header_360loc (C11/C23 -> .cx)",
            .run_fn = benchTranslateCHeader360Loc,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "mir_async_color_64_coros (64 coros <= 16 KiB)",
            .run_fn = benchMirAsyncFrameColor64Coros,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "ffi_extern_c_corex_release (2M C ABI calls)",
            .run_fn = benchFfiExternCCorexRelease,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "ffi_extern_c_zig_cc_o2_base (2M C ABI calls)",
            .run_fn = benchFfiExternCCBaseline,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
    };

    var results: [cases.len]BenchResult = undefined;
    for (cases, 0..) |bench_case, i| {
        results[i] = try corex.bench_harness.runCase(init.gpa, init.io, bench_case);
    }

    var stdout_buf: [8192]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    const style_config: StyleConfig = .{
        .is_color_enabled = corex.style.isColorEnabled(.auto, init.io, std.Io.File.stdout(), init.environ_map),
    };

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 8 translate-c, mir_async Frame Coloring & C FFI Baseline Suite (5 warmup, 30 measured)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, &results);
    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.SUCCESS,
        "parity",
        "CoreX extern \"C\" (--release -O2) vs zig cc -O2 C99 FFI baseline checksum verified identical",
    );
    try stdout_writer.interface.writeByte('\n');
    try stdout_writer.interface.flush();
}

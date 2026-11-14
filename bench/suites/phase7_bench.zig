//! Phase 7 ABI Layout, Tier A (`-ofmt=c`), Tier B (`LLVM`), Cold-Start & C-Baseline Benchmark Suite (`bench/suites/phase7_bench.zig`)
//!
//! Benchmarks six core Phase 7 codegen and native runtime execution workloads (`DR-01`, `DR-09`):
//! 1. `abi_layout_classify_64kib`: `TypeLayoutResolver` + `AbiClassifier` throughput across a
//!    `128`-function (~64 KiB) `.cx` module on `x86_64-linux` and `aarch64-macos`.
//! 2. `codegen_tier_a_c99_emit_64kib`: Tier A (`-ofmt=c`) deterministic C99 source emission on the
//!    `128`-function (~64 KiB) post-SAST `MIR` module.
//! 3. `codegen_tier_b_llvm_emit_64kib`: Tier B (`LLVM 20–23`) `.ll` IR source emission (`swifterror`,
//!    `!range`, `!llvm.loop`, SIMD) on the `128`-function (~64 KiB) post-SAST `MIR` module.
//! 4. `compiled_binary_cold_start`: Cold-start process startup + exit latency of a native CoreX binary.
//! 5. `runtime_compute_corex_release`: Native CoreX Tier B (`--release`) compute kernel execution.
//! 6. `runtime_compute_zig_cc_o3_base`: Equivalent `zig cc -O3` C99 baseline kernel execution with
//!    verified bit-identical checksum output.

const std = @import("std");
const corex = @import("corex");

const FileId = corex.FileId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetSpec = corex.TargetSpec;
const CodegenBackend = corex.CodegenBackend;
const TypeLayoutResolver = corex.TypeLayoutResolver;
const AbiClassifier = corex.AbiClassifier;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;
const BenchConfig = corex.bench_harness.BenchConfig;
const BenchResult = corex.bench_harness.BenchResult;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-lowered ~64 KiB (`128`-function) post-SAST `CompilerDb` state for Cases 1–3.
const PreparedCodegen64kState = struct {
    /// Owned ~64 KiB `.cx` source buffer (`128` functions + structs + `Result`/`Option` + SIMD).
    owned_source: []u8,
    /// Persistent `CompilerDb` holding the optimized `MIR` module for `FileId(0)`.
    db: CompilerDb,
    /// Cached slice of optimized `MirBody` items inside `db`.
    opt_bodies: []const corex.MirBody,

    /// Releases `db` and `owned_source`.
    fn deinit(self: *PreparedCodegen64kState, allocator: std.mem.Allocator) void {
        self.db.deinit();
        allocator.free(self.owned_source);
    }
};

/// Pre-compiled native binary paths and runtime `Io` handle for Cases 4–6.
const PreparedNativeBinaries = struct {
    /// Process `Io` context borrowed from `main`.
    io: std.Io,
    /// Path to minimal native CoreX cold-start binary.
    cold_start_exe: []u8,
    /// Path to native CoreX Tier B `--release` compute kernel binary.
    corex_compute_exe: []u8,
    /// Path to temporary C baseline `.c` source file.
    c_baseline_src: []u8,
    /// Path to `zig cc -O3` C baseline compute kernel binary.
    c_baseline_exe: []u8,

    /// Deletes temporary binaries on disk and frees owned path strings.
    fn deinit(self: *PreparedNativeBinaries, allocator: std.mem.Allocator) void {
        std.Io.Dir.cwd().deleteFile(self.io, self.cold_start_exe) catch {};
        std.Io.Dir.cwd().deleteFile(self.io, self.corex_compute_exe) catch {};
        std.Io.Dir.cwd().deleteFile(self.io, self.c_baseline_src) catch {};
        std.Io.Dir.cwd().deleteFile(self.io, self.c_baseline_exe) catch {};
        allocator.free(self.cold_start_exe);
        allocator.free(self.corex_compute_exe);
        allocator.free(self.c_baseline_src);
        allocator.free(self.c_baseline_exe);
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical benchmark warmup count (`5` untimed iterations).
const BENCH_WARMUP_COUNT: u32 = 5;

/// Canonical benchmark timed count (`30` measured iterations).
const BENCH_MEASURED_COUNT: u32 = 30;

/// Number of generated worker functions in the ~64 KiB codegen workload (`4` preamble + `124` = `128`).
const SYNTHETIC_WORKER_COUNT: usize = 124;

/// Shared preamble (`4` functions + `@repr(C)` `@zero_pad` struct + `CachePadded` struct) for Cases 1–3.
const SYNTHETIC_PHASE7_PREAMBLE =
    "//! Synthetic ~64 KiB Phase 7 Codegen & ABI Benchmark Module\n" ++
    "@repr(C)\n" ++
    "@zero_pad\n" ++
    "pub struct BenchFrame {\n" ++
    "    pub opcode: u8,\n" ++
    "    pub payload: i32,\n" ++
    "    pub seq_id: u64,\n" ++
    "}\n\n" ++
    "@cache_aligned\n" ++
    "pub struct AlignedCounter {\n" ++
    "    pub ticks: u64,\n" ++
    "}\n\n" ++
    "pub fn mix_scalar(lhs_v: i64, rhs_v: i64) -> i64 {\n" ++
    "    return (lhs_v ^ (rhs_v << 3)) +% 17;\n" ++
    "}\n\n" ++
    "pub fn validate_frame(frame_in: BenchFrame) -> Result[i64, i32] {\n" ++
    "    if frame_in.opcode == 0 {\n" ++
    "        return .Err(0);\n" ++
    "    }\n" ++
    "    return .Ok((frame_in.payload as i64) +% (frame_in.seq_id as i64));\n" ++
    "}\n\n" ++
    "pub fn unwrap_opt_delta(maybe_delta: i32?) -> i32 {\n" ++
    "    return match maybe_delta {\n" ++
    "        .Some(delta_v) => delta_v,\n" ++
    "        .None => 5,\n" ++
    "    };\n" ++
    "}\n\n" ++
    "pub fn bump_counter(mut slot_ref: inout AlignedCounter, step: u64) -> u64 {\n" ++
    "    slot_ref.ticks = slot_ref.ticks +% step;\n" ++
    "    return slot_ref.ticks;\n" ++
    "}\n\n";

/// Minimal CoreX cold-start program for Case 4.
const COLD_START_CX_SOURCE =
    "//! Minimal Cold-Start Benchmark Program\n" ++
    "pub fn main() -> i32 {\n" ++
    "    return 0;\n" ++
    "}\n";

/// Compute-intensive numeric mixing loop (`4,000,000` rounds) in CoreX for Case 5.
const COMPUTE_KERNEL_CX_SOURCE =
    "//! Phase 7 Runtime Compute Kernel (CoreX vs C `-O3` Parity)\n" ++
    "pub fn run_mix_rounds(round_count: u64, init_seed: u64) -> u64 {\n" ++
    "    var state_a: u64 = init_seed;\n" ++
    "    var state_b: u64 = 0x9E37_79B9_7F4A_7C15;\n" ++
    "    var iter_i: u64 = 0;\n" ++
    "    while iter_i < round_count {\n" ++
    "        state_a = (state_a ^ (state_b >> 13)) *% 0xBF58_476D_1CE4_E5B9;\n" ++
    "        state_b = (state_b +% state_a +% iter_i) ^ (state_a >> 29);\n" ++
    "        iter_i += 1;\n" ++
    "    }\n" ++
    "    return state_a ^ state_b;\n" ++
    "}\n\n" ++
    "pub fn main() -> i32 {\n" ++
    "    let digest: u64 = run_mix_rounds(4_000_000, 0x1234_5678_9ABC_DEF0);\n" ++
    "    return ((digest ^ (digest >> 32)) & 127) as i32;\n" ++
    "}\n";

/// Equivalent ISO C99 baseline kernel compiled with `zig cc -O3` for Case 6.
const COMPUTE_KERNEL_C_SOURCE =
    "#include <stdint.h>\n" ++
    "static uint64_t run_mix_rounds(uint64_t round_count, uint64_t init_seed) {\n" ++
    "    uint64_t state_a = init_seed;\n" ++
    "    uint64_t state_b = 0x9E3779B97F4A7C15ULL;\n" ++
    "    for (uint64_t iter_i = 0; iter_i < round_count; iter_i += 1) {\n" ++
    "        state_a = (state_a ^ (state_b >> 13)) * 0xBF58476D1CE4E5B9ULL;\n" ++
    "        state_b = (state_b + state_a + iter_i) ^ (state_a >> 29);\n" ++
    "    }\n" ++
    "    return state_a ^ state_b;\n" ++
    "}\n" ++
    "int main(void) {\n" ++
    "    volatile uint64_t seed = 0x123456789ABCDEF0ULL;\n" ++
    "    uint64_t digest = run_mix_rounds(4000000ULL, seed);\n" ++
    "    return (int)((digest ^ (digest >> 32)) & 127ULL);\n" ++
    "}\n";

// -------------------------------------- INTERNALS --------------------------------------

/// Cached ~64 KiB post-SAST `MIR` module state lazily initialized on first Case 1–3 invocation.
var shared_codegen_64k_state: ?PreparedCodegen64kState = null;

/// Pre-compiled native binary bundle initialized in `main` before Cases 4–6 run.
var shared_native_binaries: ?PreparedNativeBinaries = null;

/// Builds the ~64 KiB (`128`-function) synthetic `.cx` module text.
fn buildSyntheticPhase7Source(allocator: std.mem.Allocator) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    try builder.appendSlice(allocator, SYNTHETIC_PHASE7_PREAMBLE);
    var worker_buf: [1024]u8 = undefined;
    var fn_idx: usize = 0;
    while (fn_idx < SYNTHETIC_WORKER_COUNT) : (fn_idx += 1) {
        const worker_text = try std.fmt.bufPrint(
            &worker_buf,
            "pub fn codegen_worker_{d:0>3}(seed_val: i32, seq_in: u64) -> Result[i64, i32] {{\n" ++
                "    let frame_item = BenchFrame {{ opcode: 1, payload: seed_val +% {d}, seq_id: seq_in }};\n" ++
                "    let checked_sum: i64 = validate_frame(frame_item)?;\n" ++
                "    var local_cnt = AlignedCounter {{ ticks: seq_in }};\n" ++
                "    let bumped_u64: u64 = bump_counter(local_cnt, {d});\n" ++
                "    let simd_vec: [i32; 4] = @simd_add(@simd_splat[[i32; 4]](seed_val), [1, 2, 3, 4]);\n" ++
                "    let simd_sum: i32 = @simd_reduce_add(simd_vec) +% unwrap_opt_delta(.Some({d}));\n" ++
                "    return .Ok(mix_scalar(checked_sum, (bumped_u64 as i64) +% (simd_sum as i64)));\n" ++
                "}}\n\n",
            .{ fn_idx, @as(i32, @intCast(fn_idx & 31)), @as(u64, fn_idx + 1), @as(i32, @intCast(fn_idx & 15)) },
        );
        try builder.appendSlice(allocator, worker_text);
    }
    return builder.toOwnedSlice(allocator);
}

/// Lazily initializes `shared_codegen_64k_state`.
fn getOrInitCodegen64kState(allocator: std.mem.Allocator) !*PreparedCodegen64kState {
    if (shared_codegen_64k_state) |*existing| return existing;

    const owned_source = try buildSyntheticPhase7Source(allocator);
    errdefer allocator.free(owned_source);

    var db = try CompilerDb.init(allocator);
    errdefer db.deinit();
    db.setTargetSpec(TargetSpec.X86_64_LINUX);
    const fid = FileId.fromInt(0);
    _ = try db.setInput(fid, owned_source, .low);

    const opt_mod = try db.optimizeMirModule(fid, true);
    shared_codegen_64k_state = .{
        .owned_source = owned_source,
        .db = db,
        .opt_bodies = opt_mod.bodies.items,
    };
    return &shared_codegen_64k_state.?;
}

/// Compiles native CoreX & `zig cc -O3` binaries in `.zig-cache/` and verifies checksum parity.
fn prepareNativeBenchmarkBinaries(allocator: std.mem.Allocator, io: std.Io) !PreparedNativeBinaries {
    const host_spec = TargetSpec.host();
    const exe_ext = host_spec.executableExtension();

    const cold_exe = try std.fmt.allocPrint(allocator, ".zig-cache/phase7_bench_cold{s}", .{exe_ext});
    errdefer allocator.free(cold_exe);
    const cx_comp_exe = try std.fmt.allocPrint(allocator, ".zig-cache/phase7_bench_cx_comp{s}", .{exe_ext});
    errdefer allocator.free(cx_comp_exe);
    const c_base_src = try allocator.dupe(u8, ".zig-cache/phase7_bench_c_base.c");
    errdefer allocator.free(c_base_src);
    const c_base_exe = try std.fmt.allocPrint(allocator, ".zig-cache/phase7_bench_c_base{s}", .{exe_ext});
    errdefer allocator.free(c_base_exe);

    // [1] Compile Cold-Start CoreX executable:
    {
        var cold_db = try CompilerDb.init(allocator);
        defer cold_db.deinit();
        cold_db.setTargetSpec(host_spec);
        const fid = FileId.fromInt(0);
        _ = try cold_db.setInput(fid, COLD_START_CX_SOURCE, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var art = try cold_db.compileModuleArtifact(
            fid,
            .{ .tier_b_llvm = .{ .target = host_spec, .is_release_mode = true } },
            .{ .artifact_kind = .executable, .output_path = cold_exe, .io = io, .diagnostic_sink = &sink },
        );
        defer art.deinit(allocator);
    }

    // [2] Compile CoreX `--release` compute kernel executable:
    {
        var comp_db = try CompilerDb.init(allocator);
        defer comp_db.deinit();
        comp_db.setTargetSpec(host_spec);
        const fid = FileId.fromInt(0);
        _ = try comp_db.setInput(fid, COMPUTE_KERNEL_CX_SOURCE, .low);
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        var art = try comp_db.compileModuleArtifact(
            fid,
            .{
                .tier_b_llvm = .{
                    .target = host_spec,
                    .is_release_mode = true,
                    .opt_level = .release_aggressive_o3,
                },
            },
            .{ .artifact_kind = .executable, .output_path = cx_comp_exe, .io = io, .diagnostic_sink = &sink },
        );
        defer art.deinit(allocator);
    }

    // [3] Compile `zig cc -O3` C99 baseline executable:
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = c_base_src, .data = COMPUTE_KERNEL_C_SOURCE });
    const cc_run = try std.process.run(allocator, io, .{
        .argv = &.{ "zig", "cc", "-std=c99", "-O3", c_base_src, "-o", c_base_exe },
    });
    defer allocator.free(cc_run.stdout);
    defer allocator.free(cc_run.stderr);
    switch (cc_run.term) {
        .exited => |code| if (code != 0) return error.CBaselineCompileFailed,
        else => return error.CBaselineCompileFailed,
    }

    // [4] Verify identical exit-code checksum between CoreX `--release` and `zig cc -O3`:
    const cx_check = try std.process.run(allocator, io, .{ .argv = &.{cx_comp_exe} });
    defer allocator.free(cx_check.stdout);
    defer allocator.free(cx_check.stderr);
    const c_check = try std.process.run(allocator, io, .{ .argv = &.{c_base_exe} });
    defer allocator.free(c_check.stdout);
    defer allocator.free(c_check.stderr);

    const cx_exit: u8 = switch (cx_check.term) {
        .exited => |code| code,
        else => return error.CorexComputeCrashed,
    };
    const c_exit: u8 = switch (c_check.term) {
        .exited => |code| code,
        else => return error.CBaselineCrashed,
    };
    if (cx_exit != c_exit) return error.ComputeChecksumMismatch;

    return .{
        .io = io,
        .cold_start_exe = cold_exe,
        .corex_compute_exe = cx_comp_exe,
        .c_baseline_src = c_base_src,
        .c_baseline_exe = c_base_exe,
    };
}

/// Case 1 (`abi_layout_classify_64kib`): `TypeLayoutResolver` + `AbiClassifier` across `128` functions.
fn benchAbiLayoutClassify64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitCodegen64kState(allocator);
    var total_recipes: usize = 0;

    for ([_]TargetSpec{ TargetSpec.X86_64_LINUX, TargetSpec.AARCH64_MACOS }) |spec| {
        var resolver = TypeLayoutResolver.init(
            allocator,
            &state.db.type_pool,
            &state.db.symbol_table,
            spec,
        );
        defer resolver.deinit();

        for (state.opt_bodies) |*body_item| {
            const param_count: usize = body_item.param_count;
            var param_specs_buf: [16]corex.codegen_abi.FnParamSpec = undefined;
            const capped_params = @min(param_count, 16);
            var idx: usize = 0;
            while (idx < capped_params) : (idx += 1) {
                const local_decl = body_item.locals.items[1 + idx];
                param_specs_buf[idx] = .{
                    .type_id = local_decl.type_id,
                    .mode = local_decl.mode(),
                    .is_non_escaping = true,
                };
            }
            var recipe = try AbiClassifier.classifyFn(allocator, &resolver, .{
                .params = param_specs_buf[0..capped_params],
                .ret_ty = body_item.ret_ty,
                .is_extern_c = false,
                .is_contextless = body_item.is_contextless,
            });
            total_recipes += recipe.param_recipes.len + 1;
            recipe.deinit(allocator);
        }
    }
    std.mem.doNotOptimizeAway(total_recipes);
    return state.owned_source.len;
}

/// Case 2 (`codegen_tier_a_c99_emit_64kib`): Tier A (`-ofmt=c`) ISO C99 emission on `128` functions.
fn benchTierAC99Emit64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitCodegen64kState(allocator);
    const backend = CodegenBackend{
        .tier_a_c99 = .{
            .target = TargetSpec.X86_64_LINUX,
            .is_release_mode = true,
            .has_line_directives = false,
        },
    };
    var art = try backend.emitModule(allocator, .{
        .bodies = state.opt_bodies,
        .pool = &state.db.type_pool,
        .sym_table = &state.db.symbol_table,
        .interner = &state.db.interner,
        .module_name = "bench_tier_a",
        .artifact_kind = .source_text,
    });
    defer art.deinit(allocator);

    const emitted_len = art.emitted_text.len;
    std.mem.doNotOptimizeAway(emitted_len);
    return state.owned_source.len;
}

/// Case 3 (`codegen_tier_b_llvm_emit_64kib`): Tier B (`LLVM`) `.ll` IR emission on `128` functions.
fn benchTierBLlvmEmit64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitCodegen64kState(allocator);
    const backend = CodegenBackend{
        .tier_b_llvm = .{
            .target = TargetSpec.X86_64_LINUX,
            .is_release_mode = true,
        },
    };
    var art = try backend.emitModule(allocator, .{
        .bodies = state.opt_bodies,
        .pool = &state.db.type_pool,
        .sym_table = &state.db.symbol_table,
        .interner = &state.db.interner,
        .module_name = "bench_tier_b",
        .artifact_kind = .source_text,
    });
    defer art.deinit(allocator);

    const emitted_len = art.emitted_text.len;
    std.mem.doNotOptimizeAway(emitted_len);
    return state.owned_source.len;
}

/// Case 4 (`compiled_binary_cold_start`): Spawns and awaits the minimal native CoreX executable.
fn benchCompiledBinaryColdStart(allocator: std.mem.Allocator) !usize {
    const bins = shared_native_binaries orelse return error.MissingNativeBinaries;
    const run_res = try std.process.run(allocator, bins.io, .{ .argv = &.{bins.cold_start_exe} });
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);
    return COLD_START_CX_SOURCE.len;
}

/// Case 5 (`runtime_compute_corex_release`): Executes the CoreX Tier B (`-O3`) compute kernel.
fn benchRuntimeComputeCorexRelease(allocator: std.mem.Allocator) !usize {
    const bins = shared_native_binaries orelse return error.MissingNativeBinaries;
    const run_res = try std.process.run(allocator, bins.io, .{ .argv = &.{bins.corex_compute_exe} });
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);
    return COMPUTE_KERNEL_CX_SOURCE.len;
}

/// Case 6 (`runtime_compute_zig_cc_o3_base`): Executes the `zig cc -O3` C99 baseline compute kernel.
fn benchRuntimeComputeCBaseline(allocator: std.mem.Allocator) !usize {
    const bins = shared_native_binaries orelse return error.MissingNativeBinaries;
    const run_res = try std.process.run(allocator, bins.io, .{ .argv = &.{bins.c_baseline_exe} });
    defer allocator.free(run_res.stdout);
    defer allocator.free(run_res.stderr);
    return COMPUTE_KERNEL_C_SOURCE.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 7 codegen, cold-start, and C-baseline benchmark suite and renders the monochrome table.
pub fn main(init: std.process.Init) !void {
    shared_native_binaries = try prepareNativeBenchmarkBinaries(init.gpa, init.io);
    defer {
        if (shared_native_binaries) |*bins_ref| {
            bins_ref.deinit(init.gpa);
            shared_native_binaries = null;
        }
        if (shared_codegen_64k_state) |*cg_ref| {
            cg_ref.deinit(init.gpa);
            shared_codegen_64k_state = null;
        }
    }

    const cases = [_]BenchCase{
        .{
            .name = "abi_layout_classify_64kib (128-fn x 2 targets)",
            .run_fn = benchAbiLayoutClassify64k,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "codegen_tier_a_c99_emit_64kib (64 KiB -> C99)",
            .run_fn = benchTierAC99Emit64k,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "codegen_tier_b_llvm_emit_64kib (64 KiB -> .ll)",
            .run_fn = benchTierBLlvmEmit64k,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "compiled_binary_cold_start (native CoreX exe)",
            .run_fn = benchCompiledBinaryColdStart,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "runtime_compute_corex_release (4M mix rounds)",
            .run_fn = benchRuntimeComputeCorexRelease,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "runtime_compute_zig_cc_o3_base (4M mix rounds)",
            .run_fn = benchRuntimeComputeCBaseline,
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
        "Phase 7 ABI Layout, Tier A (-ofmt=c), Tier B (LLVM), Cold-Start & C-Baseline Suite (5 warmup, 30 measured)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, &results);
    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.SUCCESS,
        "parity",
        "CoreX Tier B (--release -O3) vs zig cc -O3 C99 baseline checksum verified identical",
    );
    try stdout_writer.interface.writeByte('\n');
    try stdout_writer.interface.flush();
}

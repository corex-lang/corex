//! Phase 5 `HIR`, Block-Argument SSA `MIR`, Optimizer & `MirVm` Benchmark Suite (`bench/suites/phase5_bench.zig`)
//!
//! Benchmarks isolated `AST -> HIR` lowering (`lowerFileToHir`), `HIR -> MIR` Braun SSA + Maranget
//! decision-tree construction + `V1`–`V6` formal verification (`lowerHirToMir`), `--dev` (`D1`–`D5`)
//! and `--release` (`D1`–`D5` + `R1`–`R6`) `MIR` optimization pipelines across a 64 KiB (`2,048` LOC,
//! `128`-function) `.cx` module, and `MirVm.evalBody` register execution + `Wyhash(0)` pure-call
//! memoization (`4,096` calls).
//!
//! Executed via `zig build bench` or `zig build bench-phase5`, enforcing 5 warmup iterations and
//! 30 timed iterations per workload and rendering the canonical monochrome Unicode report table.

const std = @import("std");
const corex = @import("corex");

const symbol_resolver = corex.symbol_resolver;
const type_system = corex.type_system;
const FileId = corex.FileId;
const StringInterner = corex.StringInterner;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const SymbolTable = corex.SymbolTable;
const InternPool = corex.InternPool;
const BodySemanticSideTables = corex.BodySemanticSideTables;
const HirStore = corex.HirStore;
const MirModuleBundle = corex.MirModuleBundle;
const MirBody = corex.MirBody;
const MirSourceBundle = corex.mir.MirSourceBundle;
const RodataPool = corex.RodataPool;
const PureCallMemoCache = corex.PureCallMemoCache;
const MirVm = corex.MirVm;
const RegSlot = corex.RegSlot;
const DiagnosticSink = corex.DiagnosticSink;
const TargetLayout = corex.TargetLayout;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-parsed, pre-typechecked, and pre-lowered 64 KiB `.cx` state for isolated Phase 5 benchmarks.
const PrePreparedPhase5State = struct {
    /// Shared string interner.
    interner: StringInterner,
    /// Shared type intern pool.
    pool: InternPool,
    /// Shared symbol table and scope arena.
    sym_table: SymbolTable,
    /// Pre-populated token and trivia buffer.
    token_buf: TokenBuffer,
    /// Pre-populated lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Pre-populated AST arena.
    ast_arena: AstArena,
    /// Extracted file-level semantic side tables from `TypeChecker`.
    side_tables: BodySemanticSideTables,
    /// Pre-lowered `HirStore` for isolated `lowerHirToMir` benchmarking.
    hir_store: HirStore,
    /// Pre-lowered `MirModuleBundle` for isolated `optimizeMirModule` benchmarking.
    mir_bundle: MirModuleBundle,

    /// Releases all arenas and buffers owned by `self`.
    fn deinit(self: *PrePreparedPhase5State) void {
        self.mir_bundle.deinit();
        self.hir_store.deinit();
        self.side_tables.deinit();
        self.ast_arena.deinit();
        self.cst_arena.deinit();
        self.token_buf.deinit();
        self.sym_table.deinit();
        self.pool.deinit();
        self.interner.deinit();
    }
};

/// Persistent `MirVm` + `PureCallMemoCache` state for benchmarking `4,096` `evalBody` calls.
const PreparedVmMemoState = struct {
    /// Lowered source + MIR bundle owning the pure kernel body.
    bundle: MirSourceBundle,
    /// Optimized `--release` module owning the contextless `MirBody` target.
    opt_res: corex.MirOptModuleResult,
    /// Arena-backed `.rodata` pool shared across VM calls.
    rodata_pool: RodataPool,
    /// Bounded `Wyhash(0)` pure-call memoization cache.
    memo_cache: PureCallMemoCache,
    /// Reusable sandboxed 64-bit register `MirVm`.
    vm_engine: MirVm,
    /// Resolved pointer to `eval_memo_kernel` inside `opt_res.bodies`.
    kernel_body: *const MirBody,

    /// Releases all VM, cache, optimizer, and bundle allocations owned by `self`.
    fn deinit(self: *PreparedVmMemoState) void {
        self.vm_engine.deinit();
        self.memo_cache.deinit();
        self.rodata_pool.deinit();
        self.opt_res.deinit();
        self.bundle.deinit();
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Shared 32-line preamble defining `FramePair` and 2 helpers (`pipe_boost`, `lift_seed`).
const SYNTHETIC_PREAMBLE_32_LOC =
    "/// Aggregate accumulator candidate for SROA scalar promotion.\n" ++
    "pub struct FramePair {\n" ++
    "    pub sum: i32,\n" ++
    "    pub count: i32,\n" ++
    "}\n" ++
    "\n" ++
    "/// Generic `Number` pipeline helper exercising `D5` monomorphization and `R1` inlining.\n" ++
    "@inline\n" ++
    "pub fn pipe_boost(val: Number, factor: Number) -> Number {\n" ++
    "    return val * factor + val;\n" ++
    "}\n" ++
    "\n" ++
    "/// Fallible helper exercising `Result` `?` propagation and `catch` fallback.\n" ++
    "pub fn lift_seed(val: i32) -> Result[i32, u32] {\n" ++
    "    if val < 0 {\n" ++
    "        return .Err(1);\n" ++
    "    }\n" ++
    "    return .Ok(val + 3);\n" ++
    "}\n" ++
    "\n" ++
    "// Padding lines to keep total module line count at an exact 2,048 LOC (32 + 126 * 16):\n" ++
    "// [line 22]\n" ++
    "// [line 23]\n" ++
    "// [line 24]\n" ++
    "// [line 25]\n" ++
    "// [line 26]\n" ++
    "// [line 27]\n" ++
    "// [line 28]\n" ++
    "// [line 29]\n" ++
    "// [line 30]\n" ++
    "// [line 31]\n" ++
    "// [line 32]\n";

/// Representative 16-line `.cx` worker function repeated 126 times (`2 + 126 = 128` functions, `2,048` LOC).
const SYNTHETIC_WORKER_16_LOC =
    "/// Evaluates pipelines, `?`/`catch`, `match`, `for` loops, structs, and `defer`.\n" ++
    "pub fn eval_phase5_work000(seed_val: i32, flag_byte: u8) -> Result[i32, u32] {\n" ++
    "    var cleanup_acc: i32 = 0;\n" ++
    "    defer { cleanup_acc += 1; }\n" ++
    "    let checked: i32 = lift_seed(seed_val |> pipe_boost(2))? + (lift_seed(seed_val) catch 5);\n" ++
    "    var pair = FramePair { sum: checked, count: 0 };\n" ++
    "    for step_idx in 0..4 {\n" ++
    "        pair.sum = pair.sum + step_idx;\n" ++
    "        pair.count = pair.count + 1;\n" ++
    "    }\n" ++
    "    let bonus: i32 = match flag_byte {\n" ++
    "        0..=127 => 10,\n" ++
    "        128..=255 => 20,\n" ++
    "    };\n" ++
    "    return .Ok(pair.sum + pair.count + bonus + cleanup_acc);\n" ++
    "}\n";

/// Total byte size of the 64 KiB (`2,048` LOC, `128`-function) synthetic Phase 5 `.cx` module.
const SYNTHETIC_MODULE_LEN: usize = SYNTHETIC_PREAMBLE_32_LOC.len + SYNTHETIC_WORKER_16_LOC.len * 126;

/// Complete ~64 KiB (`2,048` LOC, `128` functions) synthetic `.cx` module with unique worker names.
const SYNTHETIC_PHASE5_MODULE_64K: [SYNTHETIC_MODULE_LEN]u8 = blk: {
    @setEvalBranchQuota(600_000);
    var buf: [SYNTHETIC_MODULE_LEN]u8 = undefined;
    @memcpy(buf[0..SYNTHETIC_PREAMBLE_32_LOC.len], SYNTHETIC_PREAMBLE_32_LOC);

    const worker_prefix_len = ("/// Evaluates pipelines, `?`/`catch`, `match`, `for` loops, structs, and `defer`.\n" ++
        "pub fn eval_phase5_work").len;

    var i: usize = 0;
    while (i < 126) : (i += 1) {
        const start = SYNTHETIC_PREAMBLE_32_LOC.len + i * SYNTHETIC_WORKER_16_LOC.len;
        @memcpy(buf[start .. start + SYNTHETIC_WORKER_16_LOC.len], SYNTHETIC_WORKER_16_LOC);
        const digits_off = start + worker_prefix_len;
        buf[digits_off + 0] = '0' + @as(u8, @intCast((i / 100) % 10));
        buf[digits_off + 1] = '0' + @as(u8, @intCast((i / 10) % 10));
        buf[digits_off + 2] = '0' + @as(u8, @intCast(i % 10));
    }
    break :blk buf;
};

/// Pure contextless `.cx` kernel used for `MirVm.evalBody` + `Wyhash(0)` memoization benchmarking.
const VM_MEMO_KERNEL_SRC =
    "pub fn pure_inner_mix(val: i64, round_idx: i64) -> i64 {\n" ++
    "    return (val * 13 + round_idx * 7) ^ (val >> 1);\n" ++
    "}\n" ++
    "pub fn eval_memo_kernel(seed_val: i64) -> i64 {\n" ++
    "    var acc: i64 = seed_val + 1;\n" ++
    "    var step: i64 = 0;\n" ++
    "    while step < 8 {\n" ++
    "        acc = pure_inner_mix(acc, step);\n" ++
    "        step += 1;\n" ++
    "    }\n" ++
    "    return acc;\n" ++
    "}\n";

/// Number of `MirVm.evalBody` invocations executed per measured iteration in Benchmark 5.
const VM_BENCH_CALL_COUNT: usize = 4_096;

// -------------------------------------- INTERNALS --------------------------------------

/// Lazily initialized 64 KiB pre-parsed, pre-typechecked, and pre-lowered Phase 5 state.
var shared_phase5_state: ?PrePreparedPhase5State = null;
/// Lazily initialized `MirVm` + `PureCallMemoCache` benchmark state.
var shared_vm_memo_state: ?PreparedVmMemoState = null;

/// Returns the pre-prepared 64 KiB Phase 5 benchmark state, initializing once on first use.
fn getOrInitPhase5State(allocator: std.mem.Allocator) !*PrePreparedPhase5State {
    if (shared_phase5_state == null) {
        const file_id = FileId.fromInt(0);
        var interner = try StringInterner.init(allocator);
        errdefer interner.deinit();
        var pool = try InternPool.init(allocator);
        errdefer pool.deinit();
        var sym_table = try SymbolTable.init(allocator, &interner);
        errdefer sym_table.deinit();
        var token_buf = TokenBuffer.init(allocator);
        errdefer token_buf.deinit();
        var cst_arena = LosslessCstArena.init(allocator);
        errdefer cst_arena.deinit();
        var ast_arena = AstArena.init(allocator);
        errdefer ast_arena.deinit();

        _ = try corex.parseSource(
            &SYNTHETIC_PHASE5_MODULE_64K,
            file_id,
            &token_buf,
            &cst_arena,
            &ast_arena,
            null,
            &interner,
        );
        _ = try symbol_resolver.collectFileModuleItems(
            &sym_table,
            &interner,
            file_id,
            &SYNTHETIC_PHASE5_MODULE_64K,
            &token_buf,
            &cst_arena,
            &ast_arena,
            null,
        );
        try symbol_resolver.resolveFileUseImports(
            &sym_table,
            &interner,
            file_id,
            &SYNTHETIC_PHASE5_MODULE_64K,
            &token_buf,
            &cst_arena,
            null,
        );

        var checker = try type_system.TypeChecker.init(
            allocator,
            &interner,
            &pool,
            &sym_table,
            file_id,
            &SYNTHETIC_PHASE5_MODULE_64K,
            &token_buf,
            &cst_arena,
            &ast_arena,
            null,
        );
        defer checker.deinit();
        checker.target_layout = TargetLayout.NATIVE_64;
        try checker.resolveModuleSignatures();
        try checker.checkFileBodies();

        var side_tables = try checker.extractFileSemanticSideTables(allocator);
        errdefer side_tables.deinit();

        var hir_store = try corex.lowerFileToHir(
            allocator,
            file_id,
            &SYNTHETIC_PHASE5_MODULE_64K,
            &token_buf,
            &cst_arena,
            &ast_arena,
            &interner,
            &pool,
            &sym_table,
            &side_tables,
            null,
            TargetLayout.NATIVE_64,
            .{},
        );
        errdefer hir_store.deinit();

        var mir_bundle = try corex.lowerHirToMir(
            allocator,
            &hir_store,
            &pool,
            &sym_table,
            &interner,
            null,
        );
        errdefer mir_bundle.deinit();

        shared_phase5_state = .{
            .interner = interner,
            .pool = pool,
            .sym_table = sym_table,
            .token_buf = token_buf,
            .cst_arena = cst_arena,
            .ast_arena = ast_arena,
            .side_tables = side_tables,
            .hir_store = hir_store,
            .mir_bundle = mir_bundle,
        };
    }
    return &shared_phase5_state.?;
}

/// Returns the pre-prepared `MirVm` + `PureCallMemoCache` state, initializing once on first use.
fn getOrInitVmMemoState(allocator: std.mem.Allocator) !*PreparedVmMemoState {
    if (shared_vm_memo_state == null) {
        var bundle = try corex.lowerSourceToMir(
            allocator,
            FileId.fromInt(1),
            VM_MEMO_KERNEL_SRC,
            TargetLayout.NATIVE_64,
            .{},
        );
        errdefer bundle.deinit();

        var opt_sink = DiagnosticSink.init(allocator);
        defer opt_sink.deinit();
        var opt_res = try corex.optimizeMirModule(
            allocator,
            bundle.mir_bundle.bodies.items,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &bundle.hir_bundle.interner,
            .{
                .is_release_mode = false,
                .is_preserving_pre_strip_mir = false,
                .target_layout = TargetLayout.NATIVE_64,
                .syntax_view = .{
                    .source = VM_MEMO_KERNEL_SRC,
                    .tokens = &bundle.hir_bundle.tokens,
                    .cst_arena = &bundle.hir_bundle.cst_arena,
                },
            },
            &opt_sink,
        );
        errdefer opt_res.deinit();

        var rodata_pool = RodataPool.init(allocator);
        errdefer rodata_pool.deinit();
        var memo_cache = PureCallMemoCache.init(allocator);
        errdefer memo_cache.deinit();

        shared_vm_memo_state = .{
            .bundle = bundle,
            .opt_res = opt_res,
            .rodata_pool = rodata_pool,
            .memo_cache = memo_cache,
            .vm_engine = undefined,
            .kernel_body = undefined,
        };
        const state_ptr = &shared_vm_memo_state.?;
        state_ptr.vm_engine = try MirVm.init(
            allocator,
            &state_ptr.bundle.hir_bundle.interner,
            &state_ptr.bundle.hir_bundle.pool,
            &state_ptr.bundle.hir_bundle.sym_table,
            &state_ptr.rodata_pool,
            &state_ptr.memo_cache,
            null,
            .{ .target_layout = TargetLayout.NATIVE_64 },
        );
        for (state_ptr.opt_res.bodies.items) |*body_item| {
            const sym_idx = state_ptr.bundle.hir_bundle.sym_table.def_to_symbol.get(
                body_item.def_id.asInt(),
            ) orelse .none;
            _ = try state_ptr.vm_engine.registerBody(body_item, sym_idx);
        }
        state_ptr.kernel_body = state_ptr.opt_res.findBodyByName(
            &state_ptr.bundle.hir_bundle.interner,
            "eval_memo_kernel",
        ).?;
    }
    return &shared_vm_memo_state.?;
}

/// Benchmarks isolated `AST -> HIR` lowering on a pre-parsed & pre-typechecked 64 KiB (`2,048` LOC) `.cx` module.
fn benchLowerFileToHir64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPhase5State(allocator);
    var hir_store = try corex.lowerFileToHir(
        allocator,
        FileId.fromInt(0),
        &SYNTHETIC_PHASE5_MODULE_64K,
        &state.token_buf,
        &state.cst_arena,
        &state.ast_arena,
        &state.interner,
        &state.pool,
        &state.sym_table,
        &state.side_tables,
        null,
        TargetLayout.NATIVE_64,
        .{},
    );
    defer hir_store.deinit();
    std.mem.doNotOptimizeAway(hir_store.countNodes());
    return SYNTHETIC_PHASE5_MODULE_64K.len;
}

/// Benchmarks isolated `HIR -> MIR` Braun SSA + Maranget + `V1`–`V6` verification on a 64 KiB `.cx` module.
fn benchLowerHirToMirAndVerify64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPhase5State(allocator);
    var mir_bundle = try corex.lowerHirToMir(
        allocator,
        &state.hir_store,
        &state.pool,
        &state.sym_table,
        &state.interner,
        null,
    );
    defer mir_bundle.deinit();
    std.mem.doNotOptimizeAway(mir_bundle.bodies.items.len);
    return SYNTHETIC_PHASE5_MODULE_64K.len;
}

/// Benchmarks `--dev` (`D1`–`D5`) `MIR` optimization and monomorphization on a 64 KiB `.cx` module.
fn benchOptimizeMirDev64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPhase5State(allocator);
    var opt_res = try corex.optimizeMirModule(
        allocator,
        state.mir_bundle.bodies.items,
        &state.pool,
        &state.sym_table,
        &state.interner,
        .{
            .is_release_mode = false,
            .is_preserving_pre_strip_mir = false,
            .target_layout = TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = &SYNTHETIC_PHASE5_MODULE_64K,
                .tokens = &state.token_buf,
                .cst_arena = &state.cst_arena,
            },
        },
        null,
    );
    defer opt_res.deinit();
    std.mem.doNotOptimizeAway(opt_res.bodies.items.len);
    return SYNTHETIC_PHASE5_MODULE_64K.len;
}

/// Benchmarks `--release` (`D1`–`D5` + `R1`–`R6`) `MIR` optimization (inline, SROA, VRP, SCCP/GVN, DCE, ICF) on 64 KiB.
fn benchOptimizeMirRelease64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPhase5State(allocator);
    var opt_res = try corex.optimizeMirModule(
        allocator,
        state.mir_bundle.bodies.items,
        &state.pool,
        &state.sym_table,
        &state.interner,
        .{
            .is_release_mode = true,
            .is_preserving_pre_strip_mir = false,
            .target_layout = TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = &SYNTHETIC_PHASE5_MODULE_64K,
                .tokens = &state.token_buf,
                .cst_arena = &state.cst_arena,
            },
        },
        null,
    );
    defer opt_res.deinit();
    std.mem.doNotOptimizeAway(opt_res.icf_folded_count + opt_res.bodies.items.len);
    return SYNTHETIC_PHASE5_MODULE_64K.len;
}

/// Benchmarks `MirVm.evalBody` register execution + `Wyhash(0)` pure-call memoization across `4,096` calls.
fn benchMirVmEvalBodyAndMemo4096(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitVmMemoState(allocator);
    state.memo_cache.clear();

    var checksum: i64 = 0;
    var i: usize = 0;
    while (i < VM_BENCH_CALL_COUNT) : (i += 1) {
        const arg_slot = [1]RegSlot{.{ .scalar_i64 = @intCast(i & 63) }};
        const eval_res = try state.vm_engine.evalBody(state.kernel_body, &arg_slot);
        checksum +%= eval_res.slot.scalar_i64;
    }
    std.mem.doNotOptimizeAway(checksum);
    return VM_BENCH_CALL_COUNT * @sizeOf(RegSlot) + state.memo_cache.live_bytes;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 5 `HIR`, `MIR`, optimizer & `MirVm` benchmark suite and prints the monochrome Unicode table.
pub fn main(init: std.process.Init) !void {
    defer {
        if (shared_vm_memo_state) |*vm_ref| {
            vm_ref.deinit();
            shared_vm_memo_state = null;
        }
        if (shared_phase5_state) |*p5_ref| {
            p5_ref.deinit();
            shared_phase5_state = null;
        }
    }

    const results = try corex.bench_harness.runSuite(
        init.gpa,
        init.io,
        &[_]BenchCase{
            .{
                .name = "lowerFileToHir (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchLowerFileToHir64k,
            },
            .{
                .name = "lowerHirToMir + MirVerifier (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchLowerHirToMirAndVerify64k,
            },
            .{
                .name = "optimizeMirModule --dev D1..D5 (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchOptimizeMirDev64k,
            },
            .{
                .name = "optimizeMirModule --release R1..R6 (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchOptimizeMirRelease64k,
            },
            .{
                .name = "MirVm evalBody + Wyhash memo (4,096 calls)",
                .run_fn = benchMirVmEvalBodyAndMemo4096,
            },
        },
    );
    defer init.gpa.free(results);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    const style_config: StyleConfig = .{
        .is_color_enabled = corex.style.isColorEnabled(.auto, init.io, std.Io.File.stdout(), init.environ_map),
    };

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 5 HIR, Block-Argument SSA MIR, Optimizer & MirVm Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, results);
    try stdout_writer.interface.flush();
}

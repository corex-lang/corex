//! Phase 6 `MIR` SAST, Demand-Sliced Pentagon BCE & 34B Early Cutoff Benchmark Suite (`bench/suites/phase6_bench.zig`)
//!
//! Benchmarks three core Phase 6 compiler static-verification workloads (`DR-06`, `DR-17`, `DR-20`):
//! 1. `sast_4pass_module_64kib`: Full 4-pass `analyzeAndElaborateMirModule` throughput (`Pass 1`
//!    `MovePath` trie + `Pass 2` Typestate/NLL/`ElaborateDrops` + `Pass 4` `Intv`/Pentagon BCE +
//!    `Pass 3` Tarjan SCC 40-byte summaries & capability contracts) on a ~64 KiB (`128`-function)
//!    synthetic `.cx` module with borrows, custom `Drop` glue, contracts, and slice loops.
//! 2. `sast_pentagon_4k_ssa_bce`: `Pass 4` `Intv` + Demand-Sliced Sparse ABCD Pentagon solver on a
//!    single heavy function (`>= 4,000` SSA instructions) with guarded array/slice accesses and
//!    modular indexing (`raw % slice.len`), enforcing `peak_pentagon_bytes < 2 MiB` (`Fix-06A`).
//! 3. `sast_early_cutoff_db_128fn`: Incremental `CompilerDb` re-verification across a `128`-function
//!    call chain when the leaf function's private implementation mutates without changing its
//!    34-byte caller-observable `SAST_SUMMARY_PROJ_FLAG` summary.

const std = @import("std");
const corex = @import("corex");

const symbol_resolver = corex.symbol_resolver;
const type_system = corex.type_system;
const FileId = corex.FileId;
const DefId = corex.DefId;
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
const CompilerDb = corex.CompilerDb;
const TargetLayout = corex.TargetLayout;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;
const BenchConfig = corex.bench_harness.BenchConfig;
const BenchResult = corex.bench_harness.BenchResult;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-lowered ~64 KiB (`128`-function) pre-SAST `MIR` module state for Case 1 (`sast_4pass_module_64kib`).
const PreparedModule64kState = struct {
    /// Shared string interner.
    interner: StringInterner,
    /// Shared type intern pool.
    pool: InternPool,
    /// Shared symbol table.
    sym_table: SymbolTable,
    /// Pre-populated token and trivia buffer.
    token_buf: TokenBuffer,
    /// Pre-populated lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Pre-populated AST arena.
    ast_arena: AstArena,
    /// File-level semantic side tables extracted from `TypeChecker`.
    side_tables: BodySemanticSideTables,
    /// Lowered `HirStore`.
    hir_store: HirStore,
    /// Pristine pre-SAST `MirModuleBundle` (`128` bodies cloned per iteration for in-place SAST elaboration).
    mir_bundle: MirModuleBundle,

    /// Releases all arenas and tables owned by `self`.
    fn deinit(self: *PreparedModule64kState) void {
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

/// Pre-lowered single-function (`>= 4,000` SSA instructions) state for Case 2 (`sast_pentagon_4k_ssa_bce`).
const PreparedPentagon4kState = struct {
    /// Heap-allocated `.cx` source buffer for `heavy_pentagon_kernel`.
    owned_source: []u8,
    /// Shared string interner.
    interner: StringInterner,
    /// Shared type intern pool.
    pool: InternPool,
    /// Shared symbol table.
    sym_table: SymbolTable,
    /// Pre-populated token buffer.
    token_buf: TokenBuffer,
    /// Pre-populated lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Pre-populated AST arena.
    ast_arena: AstArena,
    /// File-level semantic side tables.
    side_tables: BodySemanticSideTables,
    /// Lowered `HirStore`.
    hir_store: HirStore,
    /// Pristine pre-SAST `MirModuleBundle` containing `heavy_pentagon_kernel` (`>= 4,000` SSA insts).
    mir_bundle: MirModuleBundle,

    /// Releases all buffers and arenas owned by `self`.
    fn deinit(self: *PreparedPentagon4kState, allocator: std.mem.Allocator) void {
        self.mir_bundle.deinit();
        self.hir_store.deinit();
        self.side_tables.deinit();
        self.ast_arena.deinit();
        self.cst_arena.deinit();
        self.token_buf.deinit();
        self.sym_table.deinit();
        self.pool.deinit();
        self.interner.deinit();
        allocator.free(self.owned_source);
    }
};

/// Persistent `CompilerDb` state with a `128`-function call chain for Case 3 (`sast_early_cutoff_db_128fn`).
const PreparedEarlyCutoffDbState = struct {
    /// Revision A `.cx` module text (`chain_fn_000`..`chain_fn_127`).
    source_rev_a: []u8,
    /// Revision B `.cx` module text mutating only `chain_fn_000`'s private body (`34B` summary unchanged).
    source_rev_b: []u8,
    /// Persistent incremental `CompilerDb`.
    db: CompilerDb,
    /// Top-of-chain `DefId` (`chain_fn_127`) transitively depending on `chain_fn_000`..`chain_fn_126`.
    root_def_id: DefId,
    /// Tracks which revision text is currently installed in `db`.
    is_using_rev_a: bool,

    /// Releases `db` and both owned revision buffers.
    fn deinit(self: *PreparedEarlyCutoffDbState, allocator: std.mem.Allocator) void {
        self.db.deinit();
        allocator.free(self.source_rev_b);
        allocator.free(self.source_rev_a);
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical benchmark warmup count (`5` untimed iterations).
const BENCH_WARMUP_COUNT: u32 = 5;

/// Canonical benchmark timed count (`30` measured iterations).
const BENCH_MEASURED_COUNT: u32 = 30;

/// Hard upper bound (`2 MiB`) asserted on `peak_pentagon_bytes` (`DR-20` `Fix-06A` `< 1.5 MB` budget).
const PENTAGON_PEAK_ASSERT_CAP_BYTES: usize = 2 * 1024 * 1024;

/// Number of functions in the incremental Early Cutoff call chain (`Case 3`).
const EARLY_CUTOFF_CHAIN_FN_COUNT: usize = 128;

/// Number of unrolled guarded/modular blocks inside `heavy_pentagon_kernel` (`>= 4,000` SSA instructions).
const PENTAGON_KERNEL_BLOCK_COUNT: usize = 96;

/// Shared preamble defining `Drop`, `TrackedGuard` (`1` method), and `3` helpers (`4` bodies total).
const SYNTHETIC_PHASE6_PREAMBLE =
    "pub trait Drop {\n" ++
    "    fn drop(&mut self);\n" ++
    "}\n" ++
    "\n" ++
    "pub struct TrackedGuard {\n" ++
    "    pub id: i64,\n" ++
    "}\n" ++
    "\n" ++
    "impl Drop for TrackedGuard {\n" ++
    "    pub fn drop(&mut self) {\n" ++
    "        @drop_trace(self.id);\n" ++
    "    }\n" ++
    "}\n" ++
    "\n" ++
    "pub fn consume_guard(own guard: sink TrackedGuard) -> i64 {\n" ++
    "    return guard.id;\n" ++
    "}\n" ++
    "\n" ++
    "pub fn borrow_slice_view(items: &[i64]) -> &[i64] {\n" ++
    "    return items;\n" ++
    "}\n" ++
    "\n" ++
    "@no_alloc\n" ++
    "@no_block\n" ++
    "pub fn mask_lane(val: i64, mask_seed: i64) -> i64 {\n" ++
    "    return (val ^ mask_seed) & 1023;\n" ++
    "}\n\n";

/// Representative Phase 6 worker repeated `124` times (`4 + 124 = 128` functions, ~64 KiB total).
const SYNTHETIC_PHASE6_WORKER =
    "/// Exercises NLL borrows, `drop_in_place` + `drop_if_live`, contracts, and Pentagon slice BCE.\n" ++
    "@no_alloc\n" ++
    "@no_block\n" ++
    "@max_stack(2048)\n" ++
    "pub fn eval_phase6_work000(seed_val: i64, probe_idx: usize, take_move: bool) -> i64 {\n" ++
    "    let outer_guard = TrackedGuard { id: 100 };\n" ++
    "    let branch_guard = TrackedGuard { id: 200 };\n" ++
    "    let local_lanes: [i64; 4] = [seed_val & 63, 11, 23, 37];\n" ++
    "    let slice_view: &[i64] = borrow_slice_view(&local_lanes);\n" ++
    "    var acc: i64 = outer_guard.id;\n" ++
    "    if take_move {\n" ++
    "        acc = mask_lane(acc, consume_guard(branch_guard));\n" ++
    "    }\n" ++
    "    if slice_view.len > 0 {\n" ++
    "        acc = mask_lane(acc, slice_view[probe_idx % slice_view.len]);\n" ++
    "    }\n" ++
    "    var step_idx: usize = 0;\n" ++
    "    while step_idx < 4 {\n" ++
    "        if step_idx < slice_view.len {\n" ++
    "            acc = mask_lane(acc, slice_view[step_idx]);\n" ++
    "        }\n" ++
    "        step_idx += 1;\n" ++
    "    }\n" ++
    "    return acc;\n" ++
    "}\n";

/// Total byte length of the ~64 KiB (`128`-function) synthetic Phase 6 `.cx` module.
const SYNTHETIC_PHASE6_MODULE_LEN: usize =
    SYNTHETIC_PHASE6_PREAMBLE.len + SYNTHETIC_PHASE6_WORKER.len * 124;

/// Complete ~64 KiB (`128`-function) synthetic `.cx` module with unique `eval_phase6_work000..123` names.
const SYNTHETIC_PHASE6_MODULE_64K: [SYNTHETIC_PHASE6_MODULE_LEN]u8 = blk: {
    @setEvalBranchQuota(800_000);
    var buf: [SYNTHETIC_PHASE6_MODULE_LEN]u8 = undefined;
    @memcpy(buf[0..SYNTHETIC_PHASE6_PREAMBLE.len], SYNTHETIC_PHASE6_PREAMBLE);

    const digits_prefix_len = ("/// Exercises NLL borrows, `drop_in_place` + `drop_if_live`, contracts, and Pentagon slice BCE.\n" ++
        "@no_alloc\n" ++
        "@no_block\n" ++
        "@max_stack(2048)\n" ++
        "pub fn eval_phase6_work").len;

    var i: usize = 0;
    while (i < 124) : (i += 1) {
        const start = SYNTHETIC_PHASE6_PREAMBLE.len + i * SYNTHETIC_PHASE6_WORKER.len;
        @memcpy(buf[start .. start + SYNTHETIC_PHASE6_WORKER.len], SYNTHETIC_PHASE6_WORKER);
        const digits_off = start + digits_prefix_len;
        buf[digits_off + 0] = '0' + @as(u8, @intCast((i / 100) % 10));
        buf[digits_off + 1] = '0' + @as(u8, @intCast((i / 10) % 10));
        buf[digits_off + 2] = '0' + @as(u8, @intCast(i % 10));
    }
    break :blk buf;
};

// -------------------------------------- INTERNALS --------------------------------------

/// Lazily initialized ~64 KiB (`128`-function) pre-SAST `MIR` module state (`Case 1`).
var shared_module_64k_state: ?PreparedModule64kState = null;
/// Lazily initialized `>= 4,000`-SSA Pentagon kernel state (`Case 2`).
var shared_pentagon_4k_state: ?PreparedPentagon4kState = null;
/// Lazily initialized `128`-function `CompilerDb` Early Cutoff state (`Case 3`).
var shared_early_cutoff_db_state: ?PreparedEarlyCutoffDbState = null;

/// Builds the `.cx` source for `heavy_pentagon_kernel` (`>= 4,000` SSA instructions).
fn buildPentagon4kKernelSource(allocator: std.mem.Allocator) ![]u8 {
    var src_buf: std.ArrayList(u8) = .empty;
    errdefer src_buf.deinit(allocator);

    try src_buf.appendSlice(
        allocator,
        "@no_alloc\n@no_block\n" ++
            "pub fn heavy_pentagon_kernel(data: &[i64], raw_idx: usize) -> i64 {\n" ++
            "    let fixed_lut: [i64; 8] = [3, 5, 7, 11, 13, 17, 19, 23];\n" ++
            "    var acc: i64 = fixed_lut[raw_idx & 7];\n" ++
            "    if data.len > 0 {\n",
    );

    var i: usize = 0;
    while (i < PENTAGON_KERNEL_BLOCK_COUNT) : (i += 1) {
        var block_buf: [512]u8 = undefined;
        const block_text = try std.fmt.bufPrint(
            &block_buf,
            "        let idx_{d}: usize = (raw_idx & 255) + {d};\n" ++
                "        if idx_{d} < data.len {{\n" ++
                "            let direct_v_{d} = data[idx_{d}];\n" ++
                "            let mod_a_{d} = data[(idx_{d} + 1) % data.len];\n" ++
                "            let mod_b_{d} = data[(idx_{d} + 3) % data.len];\n" ++
                "            let lut_v_{d} = fixed_lut[idx_{d} & 7];\n" ++
                "            acc = ((acc ^ direct_v_{d}) | (mod_a_{d} & 1023)) ^ (mod_b_{d} & lut_v_{d});\n" ++
                "        }}\n",
            .{ i, i, i, i, i, i, i, i, i, i, i, i, i, i, i },
        );
        try src_buf.appendSlice(allocator, block_text);
    }

    try src_buf.appendSlice(
        allocator,
        "    }\n    return acc;\n}\n",
    );
    return src_buf.toOwnedSlice(allocator);
}

/// Builds a `128`-function call chain (`chain_fn_000`..`chain_fn_127`) with `leaf_body` in `chain_fn_000`.
fn buildCallChain128Source(allocator: std.mem.Allocator, leaf_body: []const u8) ![]u8 {
    var src_buf: std.ArrayList(u8) = .empty;
    errdefer src_buf.deinit(allocator);

    try src_buf.appendSlice(allocator, "pub fn chain_fn_000(val: i64) -> i64 {\n");
    try src_buf.appendSlice(allocator, leaf_body);
    try src_buf.appendSlice(allocator, "}\n\n");

    var i: usize = 1;
    while (i < EARLY_CUTOFF_CHAIN_FN_COUNT) : (i += 1) {
        var fn_buf: [192]u8 = undefined;
        const fn_text = try std.fmt.bufPrint(
            &fn_buf,
            "pub fn chain_fn_{d:0>3}(val: i64) -> i64 {{\n" ++
                "    return chain_fn_{d:0>3}(val ^ {d});\n" ++
                "}}\n\n",
            .{ i, i - 1, i },
        );
        try src_buf.appendSlice(allocator, fn_text);
    }

    return src_buf.toOwnedSlice(allocator);
}

/// Returns the pre-prepared ~64 KiB (`128`-function) state for `Case 1`, initializing lazily on first use.
fn getOrInitModule64kState(allocator: std.mem.Allocator) !*PreparedModule64kState {
    if (shared_module_64k_state == null) {
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
            &SYNTHETIC_PHASE6_MODULE_64K,
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
            &SYNTHETIC_PHASE6_MODULE_64K,
            &token_buf,
            &cst_arena,
            &ast_arena,
            null,
        );
        try symbol_resolver.resolveFileUseImports(
            &sym_table,
            &interner,
            file_id,
            &SYNTHETIC_PHASE6_MODULE_64K,
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
            &SYNTHETIC_PHASE6_MODULE_64K,
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
            &SYNTHETIC_PHASE6_MODULE_64K,
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

        var mir_bundle = try corex.lowerHirToMirForSast(
            allocator,
            &hir_store,
            &pool,
            &sym_table,
            &interner,
            null,
        );
        errdefer mir_bundle.deinit();

        if (mir_bundle.bodies.items.len != 128) {
            return error.UnexpectedSyntheticFunctionCount;
        }

        shared_module_64k_state = .{
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
    return &shared_module_64k_state.?;
}

/// Returns the pre-prepared `>= 4,000`-SSA Pentagon state for `Case 2`, initializing lazily on first use.
fn getOrInitPentagon4kState(allocator: std.mem.Allocator) !*PreparedPentagon4kState {
    if (shared_pentagon_4k_state == null) {
        const owned_source = try buildPentagon4kKernelSource(allocator);
        errdefer allocator.free(owned_source);

        const file_id = FileId.fromInt(1);
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
            owned_source,
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
            owned_source,
            &token_buf,
            &cst_arena,
            &ast_arena,
            null,
        );
        try symbol_resolver.resolveFileUseImports(
            &sym_table,
            &interner,
            file_id,
            owned_source,
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
            owned_source,
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
            owned_source,
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

        var mir_bundle = try corex.lowerHirToMirForSast(
            allocator,
            &hir_store,
            &pool,
            &sym_table,
            &interner,
            null,
        );
        errdefer mir_bundle.deinit();

        if (mir_bundle.bodies.items.len != 1 or mir_bundle.bodies.items[0].insts.len < 4_000) {
            return error.InsufficientPentagonSsaInstructions;
        }

        shared_pentagon_4k_state = .{
            .owned_source = owned_source,
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
    return &shared_pentagon_4k_state.?;
}

/// Returns the persistent `128`-function `CompilerDb` state for `Case 3`, initializing lazily on first use.
fn getOrInitEarlyCutoffDbState(allocator: std.mem.Allocator) !*PreparedEarlyCutoffDbState {
    if (shared_early_cutoff_db_state == null) {
        const source_rev_a = try buildCallChain128Source(
            allocator,
            "    let masked_a: i64 = (val & 255) ^ 3;\n    return masked_a | 1;\n",
        );
        errdefer allocator.free(source_rev_a);

        const source_rev_b = try buildCallChain128Source(
            allocator,
            "    let shifted_b: i64 = ((val & 127) << 1) ^ 9;\n    return shifted_b | 5;\n",
        );
        errdefer allocator.free(source_rev_b);

        var db = try CompilerDb.init(allocator);
        errdefer db.deinit();

        const file_id = FileId.fromInt(0);
        _ = try db.setInput(file_id, source_rev_a, .low);
        const item_tree = try db.extractItemTree(file_id);
        if (item_tree.entries.len != EARLY_CUTOFF_CHAIN_FN_COUNT) {
            return error.UnexpectedCallChainLength;
        }

        for (item_tree.entries) |entry| {
            const sast_art = try db.verifySastMir(entry.def_id);
            if (!sast_art.is_verified_sound) return error.UnexpectedUnsoundCallChain;
        }

        shared_early_cutoff_db_state = .{
            .source_rev_a = source_rev_a,
            .source_rev_b = source_rev_b,
            .db = db,
            .root_def_id = item_tree.entries[EARLY_CUTOFF_CHAIN_FN_COUNT - 1].def_id,
            .is_using_rev_a = true,
        };
    }
    return &shared_early_cutoff_db_state.?;
}

/// Case 1 (`sast_4pass_module_64kib`): Full 4-pass `analyzeAndElaborateMirModule` on ~64 KiB (`128` functions).
fn benchSast4PassModule64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitModule64kState(allocator);
    const cloned_bodies = try allocator.alloc(MirBody, state.mir_bundle.bodies.items.len);
    var cloned_init_count: usize = 0;
    defer {
        for (cloned_bodies[0..cloned_init_count]) |*cloned_item| {
            cloned_item.deinit();
        }
        allocator.free(cloned_bodies);
    }

    for (state.mir_bundle.bodies.items, 0..) |*pristine_body, i| {
        cloned_bodies[i] = try pristine_body.clone(allocator);
        cloned_init_count += 1;
    }

    var sast_res = try corex.analyzeAndElaborateMirModule(
        allocator,
        cloned_bodies,
        &state.pool,
        &state.sym_table,
        &state.interner,
        .{
            .is_sast_strict = true,
            .source_text = &SYNTHETIC_PHASE6_MODULE_64K,
            .token_buffer = &state.token_buf,
            .cst_arena = &state.cst_arena,
        },
    );
    defer sast_res.deinit();

    if (sast_res.peak_pentagon_bytes >= PENTAGON_PEAK_ASSERT_CAP_BYTES) {
        return error.PentagonScratchBudgetExceeded;
    }
    if (sast_res.emitted_drops == 0 or sast_res.eliminated_bounds_checks == 0) {
        return error.ExpectedDropsAndBoundsCheckEliminations;
    }
    std.mem.doNotOptimizeAway(sast_res.emitted_drops + sast_res.eliminated_bounds_checks);
    return SYNTHETIC_PHASE6_MODULE_64K.len;
}

/// Case 2 (`sast_pentagon_4k_ssa_bce`): Demand-Sliced Sparse ABCD Pentagon on `>= 4,000` SSA instructions.
fn benchPentagon4kSsaBce(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitPentagon4kState(allocator);
    var working_body = try state.mir_bundle.bodies.items[0].clone(allocator);
    defer working_body.deinit();

    var sast_res = try corex.analyzeSingleMirBody(
        allocator,
        &working_body,
        &state.pool,
        &state.sym_table,
        &state.interner,
        .{
            .is_sast_strict = true,
            .source_text = state.owned_source,
            .token_buffer = &state.token_buf,
            .cst_arena = &state.cst_arena,
        },
    );
    defer sast_res.deinit();

    // Explicitly assert `res.peak_pentagon_bytes < 2 * 1024 * 1024` (`DR-20` `Fix-06A` `< 1.5 MB` budget):
    if (sast_res.peak_pentagon_bytes == 0 or sast_res.peak_pentagon_bytes >= PENTAGON_PEAK_ASSERT_CAP_BYTES) {
        return error.PentagonScratchBudgetExceeded;
    }
    std.debug.assert(sast_res.peak_pentagon_bytes < 2 * 1024 * 1024);
    if (sast_res.eliminated_bounds_checks == 0) {
        return error.ExpectedPentagonBceEliminations;
    }

    std.mem.doNotOptimizeAway(sast_res.eliminated_bounds_checks);
    return sast_res.peak_pentagon_bytes;
}

/// Case 3 (`sast_early_cutoff_db_128fn`): Incremental `CompilerDb` 34B `SAST_SUMMARY_PROJ_FLAG` Early Cutoff.
fn benchSastEarlyCutoffDb128Fn(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitEarlyCutoffDbState(allocator);
    const prev_cutoff_hits = state.db.telemetry.early_cutoff_hits;
    _ = try state.db.setInput(
        FileId.fromInt(0),
        if (state.is_using_rev_a) state.source_rev_b else state.source_rev_a,
        .low,
    );
    state.is_using_rev_a = !state.is_using_rev_a;

    const root_sast = try state.db.verifySastMir(state.root_def_id);
    if (!root_sast.is_verified_sound) {
        return error.UnexpectedUnsoundCallChain;
    }
    if (state.db.telemetry.early_cutoff_hits <= prev_cutoff_hits) {
        return error.ExpectedSastSummaryEarlyCutoff;
    }

    std.mem.doNotOptimizeAway(root_sast.sast_fingerprint.low);
    return EARLY_CUTOFF_CHAIN_FN_COUNT * @sizeOf(corex.FnRegionSummary);
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 6 `MIR` SAST, Pentagon BCE & Early Cutoff benchmark suite and renders the monochrome table.
pub fn main(init: std.process.Init) !void {
    defer {
        if (shared_early_cutoff_db_state) |*db_ref| {
            db_ref.deinit(init.gpa);
            shared_early_cutoff_db_state = null;
        }
        if (shared_pentagon_4k_state) |*pent_ref| {
            pent_ref.deinit(init.gpa);
            shared_pentagon_4k_state = null;
        }
        if (shared_module_64k_state) |*mod_ref| {
            mod_ref.deinit();
            shared_module_64k_state = null;
        }
    }

    const cases = [_]BenchCase{
        .{
            .name = "sast_4pass_module_64kib (64 KiB / 128-fn .cx)",
            .run_fn = benchSast4PassModule64k,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "sast_pentagon_4k_ssa_bce (>= 4,000 SSA insts)",
            .run_fn = benchPentagon4kSsaBce,
            .config = BenchConfig{
                .warmup_iterations = BENCH_WARMUP_COUNT,
                .measured_iterations = BENCH_MEASURED_COUNT,
            },
        },
        .{
            .name = "sast_early_cutoff_db_128fn (34B summary cutoff)",
            .run_fn = benchSastEarlyCutoffDb128Fn,
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
        "Phase 6 MIR SAST, Pentagon BCE & 34B Early Cutoff Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, &results);
    try stdout_writer.interface.flush();
}

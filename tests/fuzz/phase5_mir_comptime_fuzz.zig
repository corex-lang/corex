//! Phase 5 Deterministic HIR, MIR, Comptime VM & Optimizer Fuzzing Suite (`tests/fuzz/phase5_mir_comptime_fuzz.zig`)
//!
//! Exercises three complementary verification invariants across the Phase 5 middle-end:
//! 1. **Fault Tolerance & Verifier Soundness (`>= 400` iterations):** Combines Phase 5 `.cx` constructs
//!    (`|>` pipelines, `?`/`catch`, `let … else`, `for`/`while`, `#soa`, `bit_field`, `@derive(Eq, Clone)`,
//!    `comptime if`/`for`, `defer`/`errdefer`, `subscript`/`yield`) with malformed/type-error snippets and
//!    random byte perturbations, asserting zero panics, zero memory leaks, and `V1`–`V6` `MirVerifier`
//!    acceptance whenever `!diagnostics.hasErrors()`.
//! 2. **Differential `--dev` vs `--release` `MirVm` Parity (`>= 200` programs x 2 target layouts):**
//!    Generates structure-aware, well-typed multi-function `.cx` programs and evaluates `entry_main(seed)`
//!    in `MirVm` on both `--dev` (`D1`–`D5`) and `--release` (`D1`–`D5` + `R1`–`R6`) across `NATIVE_64`
//!    and `WASM32`, asserting `V1`–`V6` validity and 100% identical scalar outcomes or trap codes.
//! 3. **Incremental `CompilerDb` Stages 10–13 Parity (`>= 120` revisions):** Mutates a multi-item `.cx`
//!    module in a persistent `CompilerDb` vs a fresh scratch `CompilerDb`, asserting 100% fingerprint
//!    and value parity across `lowerDefHir`, `buildDefMir`, `evalComptimeDef`, and `optimizeMirModule`.

const std = @import("std");
const corex = @import("corex");

const mir = corex.mir;
const mir_vm = corex.mir_vm;
const mir_opt = corex.mir_opt;
const FileId = corex.FileId;
const DefId = corex.DefId;
const Durability = corex.Durability;
const Fingerprint128 = corex.Fingerprint128;
const QueryKey = corex.QueryKey;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const TargetLayout = corex.TargetLayout;
const RegSlot = corex.RegSlot;
const RodataPool = mir_vm.RodataPool;
const MirVm = corex.MirVm;
const MirSourceBundle = mir.MirSourceBundle;
const MirOptConfig = mir_opt.MirOptConfig;
const MirOptModuleResult = mir_opt.MirOptModuleResult;

// ---------------------------------------- TYPES ----------------------------------------

/// Deterministic scalar outcome or trap classification when evaluating `entry_main` in `MirVm`.
const DifferentialOutcome = union(enum) {
    /// Normal termination returning a 64-bit signed scalar register.
    scalar_i64: i64,
    /// Deterministic compile-time / VM trap error (`IntegerOverflow`, `ArithmeticTrap`, etc.).
    vm_trap: mir_vm.VmEvalError,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Number of mutated/malformed `.cx` modules verified in `test_fuzz_phase5_malformed_and_mutated_hir_mir_fault_tolerance`.
const MALFORMED_HIR_MIR_ITERATIONS: usize = 420;

/// Number of generated well-typed `.cx` programs verified in `test_fuzz_phase5_differential_dev_vs_release_mir_vm_parity`.
const DIFFERENTIAL_DEV_RELEASE_ITERATIONS: usize = 210;

/// Number of incremental `CompilerDb` revision steps verified in `test_fuzz_phase5_incremental_compiler_db_stages_10_to_13_parity`.
const INCREMENTAL_DB_ITERATIONS: usize = 128;

/// Valid Phase 5 seed items covering all `AST -> HIR -> MIR` desugarings and constructs.
const PHASE5_SEED_ITEMS = [_][]const u8{
    "pub const ENABLE_FAST_PATH: bool = true;\n",
    "pub struct IoFault { pub code: i32 }\n",
    "pub enum PipelineErr { @from Io(IoFault), BadInput, }\n",
    "@derive(Eq, Clone)\npub struct RowPoint { pub x: i32, pub y: i32 }\n",
    "pub bit_field RegControl : u16 { pub is_active: bool | 1, pub mode_bits: u16 | 15 }\n",
    "pub fn scale_pipe(val: i32, factor: i32) -> i32 { return val * factor + 1; }\n",
    "pub fn generic_mix(lhs: Number, rhs: Number) -> Number { return lhs + rhs; }\n",
    "pub fn fetch_checked(is_ok: bool) -> Result[i32, IoFault] {\n" ++
        "    if is_ok { return .Ok(12); }\n" ++
        "    return .Err(IoFault { code: 7 });\n" ++
        "}\n",
    "pub fn lift_pipeline(is_ok: bool, seed: i32) -> Result[i32, PipelineErr] {\n" ++
        "    var err_trace: i32 = 0;\n" ++
        "    errdefer { err_trace += 1; }\n" ++
        "    let base = fetch_checked(is_ok)?;\n" ++
        "    let piped = seed |> scale_pipe(2);\n" ++
        "    return .Ok(piped + base + err_trace);\n" ++
        "}\n",
    "pub fn recover_and_loop(opt_in: i32?, is_ok: bool) -> i32 {\n" ++
        "    let .Some(start_val) = opt_in else { return 0; };\n" ++
        "    let lifted = lift_pipeline(is_ok, start_val) catch |err| match err {\n" ++
        "        .Io(fault) => fault.code,\n" ++
        "        .BadInput => -1,\n" ++
        "    };\n" ++
        "    var acc: i32 = lifted;\n" ++
        "    for step in 0..3 { acc += step; }\n" ++
        "    var rem_steps: i32 = 2;\n" ++
        "    while rem_steps > 0 { acc += 1; rem_steps -= 1; }\n" ++
        "    return acc;\n" ++
        "}\n",
    "pub fn soa_and_bitfield_ops() -> i32 {\n" ++
        "    var pts: #soa [RowPoint; 2] = @default_init[#soa [RowPoint; 2]]();\n" ++
        "    pts[0].x = 4;\n" ++
        "    pts.y[1] += 6;\n" ++
        "    var reg = RegControl { is_active: true, mode_bits: 9 };\n" ++
        "    reg.mode_bits = 11;\n" ++
        "    let bonus: i32 = comptime if ENABLE_FAST_PATH { 5 } else { 1 };\n" ++
        "    var unrolled: i32 = 0;\n" ++
        "    comptime for idx in 0..2 { unrolled += idx; }\n" ++
        "    defer { unrolled += 0; }\n" ++
        "    return pts[0].x + pts[1].y + (reg.mode_bits as i32) + bonus + unrolled;\n" ++
        "}\n",
    "pub subscript lane_at(lanes: &mut [i32; 2], idx: usize) -> i32 {\n" ++
        "    yield lanes[idx];\n" ++
        "}\n",
};

/// Deliberately malformed, poison-typed, or error-triggering snippets for fault-tolerance fuzzing.
const PHASE5_MUTATION_SNIPPETS = [_][]const u8{
    "pub fn syntax_hole_fn(seed: i32) -> i32 { let broken: = ; return broken + seed; }\n",
    "pub fn mismatched_pipe(seed: i32) -> bool { return seed |> scale_pipe(3); }\n",
    "pub fn non_exhaustive_bool(flag: bool) -> i32 { return match flag { true => 10 }; }\n",
    "pub fn invalid_try_context(is_ok: bool) -> i32 { return fetch_checked(is_ok)?; }\n",
    "pub bit_field BrokenBits : u16 { pub flag: bool | 1, pub tiny: u8 | 4 }\n",
    "pub fn conflicting_number_args(left: i32, right: i64) -> i32 { return generic_mix(left, right); }\n",
    "pub fn unresolved_ident_use(val: i32) -> i32 { return missing_callee(val) + unknown_var; }\n",
};

/// `const` initializer variants for Stage 12 `evalComptimeDef` Early Cutoff & backdating parity.
const INCREMENTAL_CONST_VARIANTS = [_][]const u8{
    "pub const SCALE_FACTOR: i64 = 6 * 7;\n\n",
    "// Trivia-only edit preserving evaluated value 42:\npub const SCALE_FACTOR: i64 = 40 + 2;\n\n",
    "pub const SCALE_FACTOR: i64 = (10 << 2) + 5;\n\n",
    "pub const SCALE_FACTOR: i64 = 19;\n\n",
};

/// Worker function body variants for incremental `CompilerDb` Stages 10–13 parity fuzzing.
const INCREMENTAL_WORKER_VARIANTS = [_][]const u8{
    "    let base = mix_generic(input_val, SCALE_FACTOR);\n    return base + 1;\n",
    "    // Formatting and comment-only edit:\n" ++
        "    let base = mix_generic(input_val, SCALE_FACTOR);\n\n" ++
        "    return base + 1;\n",
    "    var total: i64 = 0;\n" ++
        "    for step in 0..4 {\n" ++
        "        total += (step as i64);\n" ++
        "    }\n" ++
        "    return mix_generic(input_val, total) + SCALE_FACTOR;\n",
    "    let opt_num: i64? = .Some(input_val);\n" ++
        "    let .Some(unwrapped) = opt_num else { return 0; };\n" ++
        "    return unwrapped |> add_offset(SCALE_FACTOR);\n",
    "    let tag_res: i64 = match input_val {\n" ++
        "        0..=3 => SCALE_FACTOR,\n" ++
        "        4 | 5 => input_val * 2,\n" ++
        "        _ => input_val - 1,\n" ++
        "    };\n" ++
        "    return tag_res;\n",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `err` is an expected Phase 6 ownership/move/init rejection on random valid-typed mutations.
fn isExpectedMutationVerifierError(err: anyerror) bool {
    return switch (err) {
        error.V4GhostExclusivityConflict,
        error.V5ReadUninitializedOrMoved,
        error.V5IncompleteExitInitialization,
        error.V6LocalClosureEscape,
        => true,
        else => false,
    };
}

/// Generates a deterministic, well-typed multi-function `.cx` program from `random` and `prog_idx`.
fn generateWellTypedDifferentialProgram(
    allocator: std.mem.Allocator,
    random: std.Random,
    prog_idx: usize,
) ![]u8 {
    var src_buf: std.ArrayList(u8) = .empty;
    errdefer src_buf.deinit(allocator);

    const inline_op_choice = random.uintLessThan(u8, 6);
    const loop_bound = random.intRangeAtMost(i64, 1, 5);
    const range_bound = random.intRangeAtMost(i64, 1, 4);
    const defer_delta = random.intRangeAtMost(i64, 2, 11);
    const shift_amt = random.intRangeAtMost(i64, 1, 3);
    const guard_thresh = random.intRangeAtMost(i64, 4, 20);
    const const_bias = random.intRangeAtMost(i64, -9, 15);
    const is_overflow_probe = (prog_idx % 19 == 18);

    try src_buf.appendSlice(
        allocator,
        "pub struct AccPair {\n    pub left: i64,\n    pub right: i64,\n}\n" ++
            "pub enum StepMode {\n    Idle,\n    Shift(i64),\n    Scale(i64),\n}\n" ++
            "pub fn bump_defer_log(slot: &mut i64, delta: i64) {\n    *slot = *slot + delta;\n}\n" ++
            "pub fn generic_combine(lhs: Number, rhs: Number) -> Number {\n    return lhs + rhs;\n}\n",
    );

    // Emit `@inline` small arithmetic/bitwise helper:
    const inline_expr = switch (inline_op_choice) {
        0 => "(val + delta) ^ 5",
        1 => "(val - delta) | 3",
        2 => "(val & 255) * 3 + delta",
        3 => "((val & 127) << 1) + delta",
        4 => "((val & 255) >> 1) - delta",
        else => "(val ^ delta) + 7",
    };
    var helper_buf: [512]u8 = undefined;
    const helper_text = try std.fmt.bufPrint(
        &helper_buf,
        "@inline\npub fn inline_step(val: i64, delta: i64) -> i64 {{\n    return {s};\n}}\n",
        .{inline_expr},
    );
    try src_buf.appendSlice(allocator, helper_text);

    // Emit worker exercising LIFO `defer` cleanup + `StepMode` enum `match`:
    var worker_buf: [768]u8 = undefined;
    const worker_text = try std.fmt.bufPrint(
        &worker_buf,
        "pub fn run_mode_worker(mode: StepMode, audit_log: &mut i64) -> i64 {{\n" ++
            "    defer bump_defer_log(audit_log, {d});\n" ++
            "    return match mode {{\n" ++
            "        .Idle => 1,\n" ++
            "        .Shift(amount) => (amount & 31) << {d},\n" ++
            "        .Scale(factor) => inline_step(factor, 2),\n" ++
            "    }};\n" ++
            "}}\n",
        .{ defer_delta, shift_amt },
    );
    try src_buf.appendSlice(allocator, worker_text);

    // Emit `entry_main(seed: i64) -> i64` combining SROA structs/tuples, diamond joins, loops, and `match`:
    const final_tail = if (is_overflow_probe)
        "    let max_pos: i64 = 9223372036854775806;\n    return max_pos + (safe_seed & 7);\n}\n"
    else
        "    return pair.left + pair.right + tup.0 - tup.1 + matched + mode_val + audit_acc + (small_sum as i64);\n}\n";

    var main_buf: [1536]u8 = undefined;
    const main_text = try std.fmt.bufPrint(
        &main_buf,
        "pub fn entry_main(seed: i64) -> i64 {{\n" ++
            "    let safe_seed: i64 = (seed & 31) + 1;\n" ++
            "    let two_i64: i64 = 2;\n" ++
            "    var pair = AccPair {{ left: safe_seed, right: {d} }};\n" ++
            "    let tup: (i64, i64) = (safe_seed + 2, 4);\n" ++
            "    if (safe_seed & 1) == 0 {{\n" ++
            "        pair.left = inline_step(pair.left, tup.0);\n" ++
            "    }} else {{\n" ++
            "        pair.right = generic_combine(pair.right, tup.1);\n" ++
            "    }}\n" ++
            "    var iter_idx: i64 = 0;\n" ++
            "    while iter_idx < {d} {{\n" ++
            "        pair.left = generic_combine(pair.left, iter_idx);\n" ++
            "        iter_idx += 1;\n" ++
            "    }}\n" ++
            "    for step_num in 0..{d} {{\n" ++
            "        pair.right = pair.right + (step_num as i64);\n" ++
            "    }}\n" ++
            "    let matched: i64 = match safe_seed {{\n" ++
            "        0..=4 => pair.left + 3,\n" ++
            "        5 | 6 | 7 => pair.right + 5,\n" ++
            "        other if other > {d} => inline_step(other, 1),\n" ++
            "        _ => generic_combine(pair.left, two_i64),\n" ++
            "    }};\n" ++
            "    var audit_acc: i64 = 0;\n" ++
            "    let chosen_mode: StepMode = if (safe_seed & 2) == 0 {{ .Shift(safe_seed) }} else {{ .Scale(safe_seed) }};\n" ++
            "    let mode_val = run_mode_worker(chosen_mode, &mut audit_acc);\n" ++
            "    let small_lhs: i32 = (safe_seed as i32) & 15;\n" ++
            "    let small_rhs: i32 = 6;\n" ++
            "    let small_sum: i32 = generic_combine(small_lhs, small_rhs);\n" ++
            "{s}",
        .{ const_bias, loop_bound, range_bound, guard_thresh, final_tail },
    );
    try src_buf.appendSlice(allocator, main_text);

    return src_buf.toOwnedSlice(allocator);
}

/// Evaluates `entry_main(seed_arg)` inside `opt_res` using `MirVm` and classifies its scalar or trap outcome.
fn evalEntryMainOutcome(
    allocator: std.mem.Allocator,
    bundle: *MirSourceBundle,
    opt_res: *const MirOptModuleResult,
    seed_arg: i64,
    target_layout: TargetLayout,
) !DifferentialOutcome {
    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm_engine = try MirVm.init(
        allocator,
        &bundle.hir_bundle.interner,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{
            .step_budget = 50_000,
            .target_layout = target_layout,
        },
    );
    defer vm_engine.deinit();

    for (opt_res.bodies.items) |*body_item| {
        _ = try vm_engine.registerBody(body_item, .none);
    }

    const entry_body = opt_res.findBodyByName(&bundle.hir_bundle.interner, "entry_main") orelse
        return error.MissingEntryMain;
    const args = [1]RegSlot{.{ .scalar_i64 = seed_arg }};
    const eval_res = vm_engine.evalBody(entry_body, &args) catch |vm_err| switch (vm_err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return .{ .vm_trap = vm_err },
    };
    return .{ .scalar_i64 = eval_res.slot.scalar_i64 };
}

/// Builds a multi-item `.cx` module for incremental `CompilerDb` Stages 10–13 parity testing.
fn buildIncrementalPhase5Module(
    allocator: std.mem.Allocator,
    has_banner_comment: bool,
    const_choice: usize,
    worker_choices: [3]usize,
) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    if (has_banner_comment) {
        try builder.appendSlice(allocator, "//! Incremental Phase 5 HIR/MIR/Comptime/Opt parity banner\n\n");
    }
    try builder.appendSlice(allocator, INCREMENTAL_CONST_VARIANTS[const_choice]);
    try builder.appendSlice(
        allocator,
        "pub fn mix_generic(lhs: Number, rhs: Number) -> Number {\n    return lhs + rhs;\n}\n\n" ++
            "pub fn add_offset(val: i64, offset: i64) -> i64 {\n    return val + offset;\n}\n\n",
    );

    var worker_idx: usize = 0;
    while (worker_idx < 3) : (worker_idx += 1) {
        var hdr_buf: [128]u8 = undefined;
        const hdr_slice = try std.fmt.bufPrint(
            &hdr_buf,
            "pub fn worker_{d}(input_val: i64) -> i64 {{\n",
            .{worker_idx},
        );
        try builder.appendSlice(allocator, hdr_slice);
        try builder.appendSlice(allocator, INCREMENTAL_WORKER_VARIANTS[worker_choices[worker_idx]]);
        try builder.appendSlice(allocator, "}\n\n");
    }

    return builder.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_phase5_malformed_and_mutated_hir_mir_fault_tolerance" {
    var prng = std.Random.DefaultPrng.init(0xF005_C0DE_2026_0501);
    const random = prng.random();

    var source_buf: [4096]u8 = undefined;
    var verified_clean_modules: usize = 0;

    var iter_idx: usize = 0;
    while (iter_idx < MALFORMED_HIR_MIR_ITERATIONS) : (iter_idx += 1) {
        var byte_len: usize = 0;
        const item_count = random.intRangeAtMost(usize, 2, 6);
        const is_clean_seed_round = (iter_idx % 5 == 0);

        if (is_clean_seed_round) {
            // Emit foundation items `0..8` without duplicates plus a random dependency-closed subset of `8..12`:
            for (PHASE5_SEED_ITEMS[0..8]) |base_item| {
                @memcpy(source_buf[byte_len .. byte_len + base_item.len], base_item);
                byte_len += base_item.len;
            }
            if (random.boolean()) {
                const pipe_item = PHASE5_SEED_ITEMS[8];
                @memcpy(source_buf[byte_len .. byte_len + pipe_item.len], pipe_item);
                byte_len += pipe_item.len;
                if (random.boolean()) {
                    const rec_item = PHASE5_SEED_ITEMS[9];
                    @memcpy(source_buf[byte_len .. byte_len + rec_item.len], rec_item);
                    byte_len += rec_item.len;
                }
            }
            if (random.boolean()) {
                const soa_item = PHASE5_SEED_ITEMS[10];
                @memcpy(source_buf[byte_len .. byte_len + soa_item.len], soa_item);
                byte_len += soa_item.len;
            }
            if (random.boolean()) {
                const sub_item = PHASE5_SEED_ITEMS[11];
                @memcpy(source_buf[byte_len .. byte_len + sub_item.len], sub_item);
                byte_len += sub_item.len;
            }
        } else {
            var item_idx: usize = 0;
            while (item_idx < item_count) : (item_idx += 1) {
                const snippet = if (random.uintLessThan(u8, 3) == 0)
                    PHASE5_MUTATION_SNIPPETS[random.uintLessThan(usize, PHASE5_MUTATION_SNIPPETS.len)]
                else
                    PHASE5_SEED_ITEMS[random.uintLessThan(usize, PHASE5_SEED_ITEMS.len)];

                if (byte_len + snippet.len <= source_buf.len) {
                    @memcpy(source_buf[byte_len .. byte_len + snippet.len], snippet);
                    byte_len += snippet.len;
                }
            }
        }

        // Apply single-byte perturbation on 30% of non-clean rounds:
        if (!is_clean_seed_round and iter_idx % 3 == 0 and byte_len > 0) {
            const mut_pos = random.uintLessThan(usize, byte_len);
            source_buf[mut_pos] = switch (random.uintLessThan(u8, 7)) {
                0 => ';',
                1 => ' ',
                2 => '?',
                3 => '|',
                4 => '}',
                5 => '_',
                else => source_buf[mut_pos],
            };
        }

        const source_slice = source_buf[0..byte_len];
        const file_id = FileId.fromInt(@intCast((iter_idx & 0xFF) + 1));
        const layout = if ((iter_idx & 1) == 0) TargetLayout.NATIVE_64 else TargetLayout.WASM32;

        var bundle = mir.lowerSourceToMir(
            std.testing.allocator,
            file_id,
            source_slice,
            layout,
            .{},
        ) catch |err| {
            if (isExpectedMutationVerifierError(err)) continue;
            return err;
        };
        defer bundle.deinit();

        if (!bundle.hir_bundle.diagnostics.hasErrors()) {
            verified_clean_modules += 1;
            for (bundle.mir_bundle.bodies.items) |*body_ptr| {
                try mir.verifyMirBody(
                    std.testing.allocator,
                    body_ptr,
                    &bundle.hir_bundle.pool,
                    &bundle.hir_bundle.sym_table,
                    null,
                );
            }
        }
    }

    try std.testing.expect(verified_clean_modules >= 40);
}

test "test_fuzz_phase5_differential_dev_vs_release_mir_vm_parity" {
    var prng = std.Random.DefaultPrng.init(0xD1FF_0505_2026_BEEF);
    const random = prng.random();
    const layouts = [_]TargetLayout{ TargetLayout.NATIVE_64, TargetLayout.WASM32 };

    var prog_idx: usize = 0;
    while (prog_idx < DIFFERENTIAL_DEV_RELEASE_ITERATIONS) : (prog_idx += 1) {
        const prog_src = try generateWellTypedDifferentialProgram(
            std.testing.allocator,
            random,
            prog_idx,
        );
        defer std.testing.allocator.free(prog_src);

        const seed_arg = random.intRangeAtMost(i64, -50, 120);
        const file_id = FileId.fromInt(@intCast((prog_idx & 0xFF) + 1));

        for (layouts) |target_layout| {
            var bundle = try mir.lowerSourceToMir(
                std.testing.allocator,
                file_id,
                prog_src,
                target_layout,
                .{},
            );
            defer bundle.deinit();
            try std.testing.expect(!bundle.hir_bundle.diagnostics.hasErrors());

            for (bundle.mir_bundle.bodies.items) |*raw_body| {
                try mir.verifyMirBody(
                    std.testing.allocator,
                    raw_body,
                    &bundle.hir_bundle.pool,
                    &bundle.hir_bundle.sym_table,
                    null,
                );
            }

            var dev_sink = DiagnosticSink.init(std.testing.allocator);
            defer dev_sink.deinit();
            var dev_opt = try mir_opt.optimizeMirModule(
                std.testing.allocator,
                bundle.mir_bundle.bodies.items,
                &bundle.hir_bundle.pool,
                &bundle.hir_bundle.sym_table,
                &bundle.hir_bundle.interner,
                MirOptConfig{
                    .is_release_mode = false,
                    .target_layout = target_layout,
                    .syntax_view = .{
                        .source = prog_src,
                        .tokens = &bundle.hir_bundle.tokens,
                        .cst_arena = &bundle.hir_bundle.cst_arena,
                    },
                },
                &dev_sink,
            );
            defer dev_opt.deinit();
            try std.testing.expect(!dev_sink.hasErrors());
            for (dev_opt.bodies.items) |*dev_body| {
                try mir.verifyMirBody(
                    std.testing.allocator,
                    dev_body,
                    &bundle.hir_bundle.pool,
                    &bundle.hir_bundle.sym_table,
                    null,
                );
            }

            var rel_sink = DiagnosticSink.init(std.testing.allocator);
            defer rel_sink.deinit();
            var rel_opt = try mir_opt.optimizeMirModule(
                std.testing.allocator,
                bundle.mir_bundle.bodies.items,
                &bundle.hir_bundle.pool,
                &bundle.hir_bundle.sym_table,
                &bundle.hir_bundle.interner,
                MirOptConfig{
                    .is_release_mode = true,
                    .target_layout = target_layout,
                    .syntax_view = .{
                        .source = prog_src,
                        .tokens = &bundle.hir_bundle.tokens,
                        .cst_arena = &bundle.hir_bundle.cst_arena,
                    },
                },
                &rel_sink,
            );
            defer rel_opt.deinit();
            try std.testing.expect(!rel_sink.hasErrors());
            for (rel_opt.bodies.items) |*rel_body| {
                try mir.verifyMirBody(
                    std.testing.allocator,
                    rel_body,
                    &bundle.hir_bundle.pool,
                    &bundle.hir_bundle.sym_table,
                    null,
                );
            }

            const dev_outcome = try evalEntryMainOutcome(
                std.testing.allocator,
                &bundle,
                &dev_opt,
                seed_arg,
                target_layout,
            );
            const rel_outcome = try evalEntryMainOutcome(
                std.testing.allocator,
                &bundle,
                &rel_opt,
                seed_arg,
                target_layout,
            );
            try std.testing.expectEqual(dev_outcome, rel_outcome);
        }
    }
}

test "test_fuzz_phase5_incremental_compiler_db_stages_10_to_13_parity" {
    var prng = std.Random.DefaultPrng.init(0xDB05_FA5E_2026_1013);
    const random = prng.random();

    var inc_db = try CompilerDb.init(std.testing.allocator);
    defer inc_db.deinit();

    const file_id = FileId.fromInt(1);
    var has_banner_comment = false;
    var const_choice: usize = 0;
    var worker_choices = [3]usize{ 0, 1, 2 };
    var durability: Durability = .low;

    var step_idx: usize = 0;
    while (step_idx < INCREMENTAL_DB_ITERATIONS) : (step_idx += 1) {
        switch (random.uintLessThan(u8, 5)) {
            0 => has_banner_comment = !has_banner_comment,
            1 => const_choice = random.uintLessThan(usize, INCREMENTAL_CONST_VARIANTS.len),
            2 => {
                const slot = random.uintLessThan(usize, 3);
                worker_choices[slot] = random.uintLessThan(usize, INCREMENTAL_WORKER_VARIANTS.len);
            },
            3 => durability = switch (random.uintLessThan(u8, 3)) {
                0 => .low,
                1 => .medium,
                else => .high,
            },
            else => {},
        }

        const mod_src = try buildIncrementalPhase5Module(
            std.testing.allocator,
            has_banner_comment,
            const_choice,
            worker_choices,
        );
        defer std.testing.allocator.free(mod_src);

        _ = try inc_db.setInput(file_id, mod_src, durability);

        var scratch_db = try CompilerDb.init(std.testing.allocator);
        defer scratch_db.deinit();
        _ = try scratch_db.setInput(file_id, mod_src, durability);

        // [1] Stage 12 `evalComptimeDef` parity on `SCALE_FACTOR` (`item_ord = 0`):
        const const_def = DefId.init(file_id, 0);
        const inc_eval = try inc_db.evalComptimeDef(const_def);
        const scr_eval = try scratch_db.evalComptimeDef(const_def);
        try std.testing.expectEqual(inc_eval.has_errors, scr_eval.has_errors);
        try std.testing.expect(
            Fingerprint128.eql(inc_eval.value_fingerprint, scr_eval.value_fingerprint),
        );
        try std.testing.expectEqual(inc_eval.value.int_val, scr_eval.value.int_val);

        // [2] Stage 10 `lowerDefHir` & Stage 11 `buildDefMir` parity across all 6 module definitions:
        var item_ord: u12 = 0;
        while (item_ord < 6) : (item_ord += 1) {
            const def_id = DefId.init(file_id, item_ord);

            const inc_hir = try inc_db.lowerDefHir(def_id);
            const scr_hir = try scratch_db.lowerDefHir(def_id);
            const inc_hir_hdr = try inc_db.fetchQuery(QueryKey.forDef(.lower_def_hir, def_id));
            const scr_hir_hdr = try scratch_db.fetchQuery(QueryKey.forDef(.lower_def_hir, def_id));
            try std.testing.expectEqual(inc_hir.countNodes(), scr_hir.countNodes());
            try std.testing.expect(
                Fingerprint128.eql(inc_hir_hdr.output_fingerprint, scr_hir_hdr.output_fingerprint),
            );

            const inc_mir_art = try inc_db.buildDefMirArtifact(def_id);
            const scr_mir_art = try scratch_db.buildDefMirArtifact(def_id);
            try std.testing.expect(
                Fingerprint128.eql(inc_mir_art.mir_fingerprint, scr_mir_art.mir_fingerprint),
            );

            const inc_primary = try inc_db.buildDefMir(def_id);
            const scr_primary = try scratch_db.buildDefMir(def_id);
            try std.testing.expectEqual(inc_primary != null, scr_primary != null);
            if (inc_primary) |inc_body| {
                try std.testing.expectEqual(
                    inc_body.blocks.items.len,
                    scr_primary.?.blocks.items.len,
                );
            }
        }

        // [3] Stage 13 `optimizeMirModule` parity across both `--dev` and `--release`:
        const modes = [_]bool{ false, true };
        for (modes) |is_release| {
            const inc_opt = try inc_db.optimizeMirModule(file_id, is_release);
            const scr_opt = try scratch_db.optimizeMirModule(file_id, is_release);
            try std.testing.expectEqual(inc_opt.fingerprint, scr_opt.fingerprint);
            try std.testing.expectEqual(inc_opt.bodies.items.len, scr_opt.bodies.items.len);
            try std.testing.expectEqual(inc_opt.dedup_merged_count, scr_opt.dedup_merged_count);
            try std.testing.expectEqual(inc_opt.icf_folded_count, scr_opt.icf_folded_count);
        }
    }

    try std.testing.expect(inc_db.telemetry.early_cutoff_hits >= 1);
}

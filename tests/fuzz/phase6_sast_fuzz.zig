//! Phase 6, Phase 7.5 & Phase 7.6 (`DR-22`) Deterministic SAST, Drop Elaboration & Pentagon BCE Fuzz Suite (`tests/fuzz/phase6_sast_fuzz.zig`)
//!
//! Exercises three complementary verification invariants across Phase 6–7.6 (`DR-06`, `DR-17`, `DR-20`, `DR-21`, `DR-22`):
//! 1. **Fault Tolerance, Scratch Cap & Verifier Soundness (`>= 360` iterations):** Combines Phase 6, `DR-21`, & `DR-22`
//!    `.cx` seed items (`AutoDrop` pre-`else` `ConditionScope` drops, `@linear` across `orelse` / loops,
//!    `defer`/`errdefer`, `&`/`&mut`/`&out`/`own T`, `@no_alloc`/`@no_panic`/`@no_block`, `@max_stack`, `.narrow()`,
//!    Pentagon `$` backward-offset slice indexing/slicing, `..own` spread drops, `(a, b) = (b, a)` `AutoDrop` swaps,
//!    `fsm: match` + `continue :fsm`, `with context.allocator = &mut local_arena`, and `subscript … yield`) with
//!    error-triggering SAST snippets (`E0302`, `E0304`–`E0307`, `E0320`–`E0322`, `E0422`) and byte perturbations.
//! 2. **Differential `--dev` vs `--release` Drop Elaboration & BCE Parity (`>= 180` programs x 2 layouts):**
//!    Generates well-typed multi-function `.cx` programs exercising `@drop_trace(id)`, `ConditionScope` pre-`else`
//!    `is` / `:=` drop ordering, `@linear` across `orelse` / loops, Pentagon `$` backward-offset slice indexing
//!    (`items[$ - 1]`, `items[..$ - 2]`), `.narrow()`, and non-escaping `with context.allocator = &mut local_arena`,
//!    optimizes via `optimizeMirModule` in both `--dev` and `--release`, executes in `MirVm`, and asserts identical
//!    scalar/trap outcomes, identical `vm.asDropTraceSlice()` LIFO order, and `0` unfreed heap allocations.
//! 3. **Incremental `CompilerDb` 34B SAST Summary Early Cutoff Parity (`>= 110` revisions):** Mutates a
//!    multi-function `.cx` module in a persistent `CompilerDb` vs a fresh scratch `CompilerDb`, asserting
//!    100% parity across `verifySastMir`, `getSastSummaryProj`, `evalComptimeDef`, and `optimizeMirModule`.

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
const MirBody = corex.MirBody;
const MirOptConfig = mir_opt.MirOptConfig;
const MirOptModuleResult = mir_opt.MirOptModuleResult;
const MirSastPipelineBundle = corex.MirSastPipelineBundle;
const FnRegionSummary = corex.FnRegionSummary;

// ---------------------------------------- TYPES ----------------------------------------

/// Deterministic scalar return or VM trap outcome captured from `MirVm` execution.
const ScalarOrTrapOutcome = union(enum) {
    /// Normal termination returning a 64-bit signed scalar register.
    scalar_i64: i64,
    /// Deterministic VM trap error (`IntegerOverflow`, `ArithmeticTrap`, `OutOfBounds`, etc.).
    vm_trap: mir_vm.VmEvalError,
};

/// Complete `MirVm` execution trace for differential `--dev` vs `--release` drop & BCE comparison.
const VmExecutionSnapshot = struct {
    /// Scalar return value or deterministic trap code.
    outcome: ScalarOrTrapOutcome,
    /// Owned copy of `vm.asDropTraceSlice()` recording destructor execution order.
    drop_trace: []const i64,
    /// Count of unfreed virtual heap allocations after `evalBody` completes.
    unfreed_heap_count: usize,

    /// Releases `drop_trace` owned by `self`.
    fn deinit(self: *VmExecutionSnapshot, allocator: std.mem.Allocator) void {
        if (self.drop_trace.len > 0) allocator.free(self.drop_trace);
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Number of mutated/malformed `.cx` modules verified in `test_fuzz_phase6_malformed_and_mutated_sast_fault_tolerance`.
const MALFORMED_SAST_ITERATIONS: usize = 384;

/// Number of generated well-typed `.cx` programs verified in `test_fuzz_phase6_differential_dev_vs_release_drop_and_bce_parity`.
const DIFFERENTIAL_DROP_BCE_ITERATIONS: usize = 186;

/// Number of incremental `CompilerDb` revision steps verified in `test_fuzz_phase6_incremental_compiler_db_sast_summary_cutoff_parity`.
const INCREMENTAL_SAST_DB_ITERATIONS: usize = 116;

/// Maximum Demand-Sliced Sparse ABCD Pentagon scratch budget (`1.5 MiB`, `DR-20` `Fix-06A`).
const MAX_PENTAGON_SCRATCH_BYTES: usize = 1536 * 1024;

/// Valid Phase 6, Phase 7.5 (`DR-21`), & Phase 7.6 (`DR-22`) seed items covering `AutoDrop`, `@linear`, `&out`, `..own`, and BCE.
const PHASE6_SEED_ITEMS = [_][]const u8{
    "pub trait Drop {\n    fn drop(&mut self);\n}\n",
    "pub struct TrackedBuf {\n    pub tag: i64,\n}\n" ++
        "impl Drop for TrackedBuf {\n    pub fn drop(&mut self) {\n        @drop_trace(self.tag);\n    }\n}\n" ++
        "pub fn make_tracked_buf(tag_val: i64) -> TrackedBuf = TrackedBuf { tag: tag_val };\n" ++
        "pub fn maybe_tracked_buf(is_present: bool, tag_val: i64) -> TrackedBuf? {\n" ++
        "    if is_present { return .Some(TrackedBuf { tag: tag_val }); }\n" ++
        "    return .None;\n" ++
        "}\n",
    "@linear\npub struct LinearTicket {\n    pub code: i64,\n}\n" ++
        "pub fn close_ticket(ticket: own LinearTicket) -> i64 {\n" ++
        "    let LinearTicket { code: extracted } = ticket;\n" ++
        "    return extracted;\n" ++
        "}\n" ++
        "pub fn maybe_ticket(is_ready: bool, code_val: i64) -> LinearTicket? {\n" ++
        "    if is_ready { return .Some(LinearTicket { code: code_val }); }\n" ++
        "    return .None;\n" ++
        "}\n",
    "pub fn consume_buf(item: own TrackedBuf) -> i64 = item.tag;\n",
    "pub fn view_head_slice(items: &[i64]) -> &[i64] = items;\n",
    "pub fn bump_first_slot(target: &mut [i64; 4], delta: i64) {\n    target[0] = delta;\n}\n",
    "pub struct Arena {\n    pub bump_tag: usize,\n}\n" ++
        "pub fn close_arena(arena_in: own Arena) {\n    let Arena { bump_tag: _bump_tag } = arena_in;\n}\n" ++
        "pub struct OwnedHeapBuf {\n    pub raw_handle: usize,\n    pub byte_len: usize,\n}\n" ++
        "impl OwnedHeapBuf {\n    pub fn drop(&mut self) {}\n}\n" ++
        "pub fn alloc_ctx_buf(size_n: usize) -> OwnedHeapBuf {\n" ++
        "    let active_alloc: Allocator = context.allocator;\n" ++
        "    return OwnedHeapBuf { raw_handle: active_alloc._handle, byte_len: size_n };\n" ++
        "}\n",
    "@no_alloc @no_panic @no_block @max_stack(512)\n" ++
        "pub fn strict_pentagon_probe(data: &[u8], raw_idx: usize, clamped_val: i32) -> u8 {\n" ++
        "    if data.len() > 0 and clamped_val >= 0 and clamped_val <= 200 {\n" ++
        "        let elem_byte = data[raw_idx % data.len()];\n" ++
        "        let narrowed_byte: u8 = clamped_val.narrow[u8]();\n" ++
        "        return elem_byte & narrowed_byte;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n",
    "@no_panic\n" ++
        "pub fn pentagon_dollar_tail_probe(items: &[i64]) -> i64 {\n" ++
        "    if items.len() >= 3 {\n" ++
        "        let head_trim: &[i64] = items[..$ - 2];\n" ++
        "        return items[$ - 1] +% items[$ - 2] +% (head_trim.len() as i64);\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n",
    "pub fn cond_walrus_pre_else_drop(is_present: bool, thresh: i64) -> i64 {\n" ++
        "    if maybe_tracked_buf(is_present, 15) is .Some(first_guard) and\n" ++
        "        (second_guard := make_tracked_buf(25)).tag > thresh\n" ++
        "    {\n" ++
        "        @drop_trace(100);\n" ++
        "        return first_guard.tag +% second_guard.tag;\n" ++
        "    } else {\n" ++
        "        @drop_trace(900);\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "}\n",
    "pub fn linear_orelse_and_loop(is_ready: bool) -> i64 {\n" ++
        "    let live_tok = maybe_ticket(is_ready, 19) orelse return 0;\n" ++
        "    defer { _ = close_ticket(own live_tok); }\n" ++
        "    var loop_sum: i64 = 0;\n" ++
        "    var step_idx: i64 = 0;\n" ++
        "    while step_idx < 2 {\n" ++
        "        let iter_tok = LinearTicket { code: 10 +% step_idx };\n" ++
        "        loop_sum = loop_sum +% close_ticket(own iter_tok);\n" ++
        "        step_idx += 1;\n" ++
        "    }\n" ++
        "    return loop_sum;\n" ++
        "}\n",
    "pub fn scoped_arena_non_escaping() -> usize {\n" ++
        "    var local_arena = Arena { bump_tag: 64 };\n" ++
        "    defer { close_arena(own local_arena); }\n" ++
        "    return with context.allocator = &mut local_arena {\n" ++
        "        let temp_buf = alloc_ctx_buf(32);\n" ++
        "        temp_buf.byte_len\n" ++
        "    };\n" ++
        "}\n",
    "pub fn linear_defer_and_errdefer(is_ok: bool) -> i64!u32 {\n" ++
        "    let ticket = LinearTicket { code: 19 };\n" ++
        "    defer { _ = close_ticket(own ticket); }\n" ++
        "    var rollback_note: i64 = 0;\n" ++
        "    errdefer { rollback_note = 1; }\n" ++
        "    if not is_ok { return .Err(3); }\n" ++
        "    return .Ok(42 + rollback_note);\n" ++
        "}\n",
    "pub fn sequential_nll_and_branch_drop(cond_flag: bool) -> usize {\n" ++
        "    var local_arr: [i64; 4] = [2, 4, 6, 8];\n" ++
        "    let borrowed = view_head_slice(&local_arr);\n" ++
        "    let snap_len = borrowed.len();\n" ++
        "    bump_first_slot(&mut local_arr, 99);\n" ++
        "    let guard_buf = TrackedBuf { tag: 77 };\n" ++
        "    if cond_flag {\n" ++
        "        _ = consume_buf(own guard_buf);\n" ++
        "    }\n" ++
        "    return snap_len;\n" ++
        "}\n",
    "pub struct CheckedLanes {\n    pub lanes: [i64; 4],\n}\n" ++
        "impl CheckedLanes {\n" ++
        "    pub subscript(lane_idx: usize, /) -> i64 {\n" ++
        "        let { yield self.lanes[lane_idx % 4]; }\n" ++
        "        inout { yield &mut self.lanes[lane_idx % 4]; }\n" ++
        "    }\n" ++
        "}\n",
    "@derive(Copy, Equatable)\n" ++
        "pub enum FsmTag: u8 {\n    First = 0,\n    Second = 1,\n}\n" ++
        "pub struct GuardPair {\n    pub primary: TrackedBuf,\n    pub secondary: TrackedBuf,\n}\n" ++
        "pub fn init_out_buf(out_buf: &out TrackedBuf, tag_v: i64, /) {\n" ++
        "    out_buf.* = TrackedBuf { tag: tag_v };\n" ++
        "}\n" ++
        "pub fn dr22_out_spread_swap_and_fsm() -> i64 {\n" ++
        "    var slot_a: TrackedBuf;\n" ++
        "    var slot_b = TrackedBuf { tag: 22 };\n" ++
        "    init_out_buf(&out slot_a, 11);\n" ++
        "    (slot_a, slot_b) = (slot_b, slot_a);\n" ++
        "    let pair_init = GuardPair { primary: own slot_a, secondary: own slot_b };\n" ++
        "    let pair_upd = GuardPair { primary: TrackedBuf { tag: 33 }, ..own pair_init };\n" ++
        "    let fsm_v: i64 = fsm: match FsmTag.First {\n" ++
        "        .First => {\n" ++
        "            let arm_guard = TrackedBuf { tag: 44 };\n" ++
        "            _ = arm_guard.tag;\n" ++
        "            continue :fsm .Second;\n" ++
        "        }\n" ++
        "        .Second => pair_upd.primary.tag +% pair_upd.secondary.tag,\n" ++
        "    };\n" ++
        "    return fsm_v;\n" ++
        "}\n",
};

/// Deliberately invalid SAST & syntax snippets (`E0302`, `E0304`–`E0307`, `E0320`–`E0322`, `E0422`) for fault-tolerance fuzzing.
const PHASE6_MUTATION_SNIPPETS = [_][]const u8{
    "pub fn bad_use_after_move() -> i64 {\n" ++
        "    let owned_buf = TrackedBuf { tag: 11 };\n" ++
        "    _ = consume_buf(own owned_buf);\n" ++
        "    return owned_buf.tag;\n" ++
        "}\n",
    "pub fn bad_loan_conflict() -> usize {\n" ++
        "    var local_arr: [i64; 4] = [1, 2, 3, 4];\n" ++
        "    let view = view_head_slice(&local_arr);\n" ++
        "    bump_first_slot(&mut local_arr, 55);\n" ++
        "    return view.len();\n" ++
        "}\n",
    "pub fn bad_stack_escape() -> &i64 {\n" ++
        "    let ephemeral_val: i64 = 123;\n" ++
        "    return &ephemeral_val;\n" ++
        "}\n",
    "pub fn bad_static_oob() -> i64 {\n" ++
        "    let fixed_vals: [i64; 3] = [10, 20, 30];\n" ++
        "    return fixed_vals[3];\n" ++
        "}\n",
    "pub fn bad_dollar_underflow() -> i64 {\n" ++
        "    let fixed_vals: [i64; 3] = [10, 20, 30];\n" ++
        "    return fixed_vals[$ - 4];\n" ++
        "}\n",
    "pub fn bad_arena_escape_return() -> OwnedHeapBuf {\n" ++
        "    var local_arena = Arena { bump_tag: 64 };\n" ++
        "    defer { close_arena(own local_arena); }\n" ++
        "    with context.allocator = &mut local_arena {\n" ++
        "        return alloc_ctx_buf(48);\n" ++
        "    }\n" ++
        "}\n",
    "pub fn bad_arena_escape_outer_var() -> usize {\n" ++
        "    var outer_buf = alloc_ctx_buf(8);\n" ++
        "    var local_arena = Arena { bump_tag: 128 };\n" ++
        "    defer { close_arena(own local_arena); }\n" ++
        "    with context.allocator = &mut local_arena {\n" ++
        "        outer_buf = alloc_ctx_buf(24);\n" ++
        "    }\n" ++
        "    return outer_buf.byte_len;\n" ++
        "}\n",
    "pub fn bad_linear_cond_b2_leak(is_ready: bool, allow_gate: bool) -> i64 {\n" ++
        "    if maybe_ticket(is_ready, 7) is .Some(live_tok) and allow_gate {\n" ++
        "        return close_ticket(own live_tok);\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n",
    "pub fn bad_uninit_out_param(slot: &out TrackedBuf, skip_init: bool) {\n" ++
        "    if not skip_init { slot.* = TrackedBuf { tag: 1 }; }\n" ++
        "}\n",
    "@no_alloc\npub fn bad_no_alloc_concat(left_s: str, right_s: str) -> str {\n    return left_s + right_s;\n}\n",
    "@no_panic\npub fn bad_no_panic_index(items: &[i64], raw_idx: usize) -> i64 {\n    return items[raw_idx];\n}\n",
    "extern \"C\" fn blocking_host_call() -> i32;\n" ++
        "@no_block\npub fn bad_no_block_ffi() -> i32 {\n    return unsafe { blocking_host_call() };\n}\n",
    "pub fn malformed_sast_syntax(seed: i64) -> i64 { let broken: = ; return seed; }\n",
};

/// `const` initializer variants for Stage 12 `evalComptimeDef` + `E0325` sandbox gate parity.
const INCREMENTAL_CONST_VARIANTS = [_][]const u8{
    "pub const SCALE_FACTOR: i64 = 6 * 9;\n\n",
    "// Equivalent constant value 54 triggering Stage 12 Early Cutoff:\npub const SCALE_FACTOR: i64 = 50 + 4;\n\n",
    "pub const SCALE_FACTOR: i64 = (8 << 2) + 3;\n\n",
    "pub const SCALE_FACTOR: i64 = 27;\n\n",
};

/// Leaf function body variants exercising 34-byte `SAST_SUMMARY_PROJ_FLAG` Early Cutoff vs effect changes.
const INCREMENTAL_LEAF_VARIANTS = [_][]const u8{
    "    let step_one: i64 = (val & 255) + 3;\n    return step_one;\n",
    "    // Internal arithmetic edit preserving exact 34-byte caller-observable FnRegionSummary:\n" ++
        "    let doubled: i64 = ((val & 127) << 1) + 5;\n" ++
        "    let extra_local: [i64; 2] = [doubled, 1];\n" ++
        "    return extra_local[0] ^ extra_local[1];\n",
    "    // Introduces checked arithmetic `may_panic` effect (`inferred_effects_bits` changes):\n" ++
        "    return val * 3 + 1;\n",
    "    if (val & 1) == 0 {\n        return (val & 63) | 4;\n    }\n    return (val & 63) ^ 9;\n",
};

/// Caller worker body variants exercising Pentagon BCE (`$` backward-offset), `.narrow()`, borrows, and `with context`.
const INCREMENTAL_CALLER_VARIANTS = [_][]const u8{
    "    let fixed_arr: [i64; 4] = [input_val, SCALE_FACTOR, 7, 11];\n" ++
        "    let view: &[i64] = &fixed_arr;\n" ++
        "    if probe_idx < view.len() {\n" ++
        "        return leaf_helper(view[probe_idx]);\n" ++
        "    }\n" ++
        "    return leaf_helper(SCALE_FACTOR);\n",
    "    let fixed_arr: [i64; 4] = [3, 5, 9, 13];\n" ++
        "    let view: &[i64] = &fixed_arr;\n" ++
        "    if view.len() > 0 {\n" ++
        "        let mod_elem = view[probe_idx % view.len()];\n" ++
        "        return leaf_helper(mod_elem) + SCALE_FACTOR;\n" ++
        "    }\n" ++
        "    return 0;\n",
    "    // Unproven bounds access emitting `W0314` when `is_sast_strict == true`:\n" ++
        "    let fixed_arr: [i64; 4] = [2, 4, 6, 8];\n" ++
        "    let view: &[i64] = &fixed_arr;\n" ++
        "    return leaf_helper(view[probe_idx]);\n",
    "    let clamped_in: i32 = ((input_val & 63) as i32);\n" ++
        "    if clamped_in >= 0 and clamped_in <= 100 {\n" ++
        "        let small_byte: u8 = clamped_in.narrow[u8]();\n" ++
        "        return leaf_helper(small_byte as i64) + SCALE_FACTOR;\n" ++
        "    }\n" ++
        "    return SCALE_FACTOR;\n",
    "    let fixed_arr: [i64; 4] = [input_val, SCALE_FACTOR, 7, 11];\n" ++
        "    let view: &[i64] = &fixed_arr;\n" ++
        "    if view.len() >= 3 {\n" ++
        "        let sub_trim: &[i64] = view[..$ - 2];\n" ++
        "        return leaf_helper(view[$ - 1] + view[$ - 2] + (sub_trim.len() as i64));\n" ++
        "    }\n" ++
        "    return SCALE_FACTOR;\n",
    "    let opt_in: i64? = if (probe_idx & 1) == 0 => .Some(input_val) else .None;\n" ++
        "    let resolved_in: i64 = opt_in orelse SCALE_FACTOR;\n" ++
        "    return with context.cancel_token = (CancelToken { _handle: probe_idx & 15 }) {\n" ++
        "        leaf_helper(resolved_in + (context.cancel_token._handle as i64))\n" ++
        "    };\n",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `err` is an expected pre-SAST `MirVerifier` rejection on randomly perturbed `.cx` code.
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

/// Asserts `MirVerifier` `V1`–`V6` acceptance on a clean SAST-elaborated `MirBody`, tolerating NLL Ghost spans.
fn verifyCleanSastBody(
    allocator: std.mem.Allocator,
    body_ptr: *MirBody,
    bundle: *const MirSastPipelineBundle,
) !void {
    if (body_ptr.has_overflowed_limits) return;
    if (!body_ptr.symbol_index.isNone() and body_ptr.symbol_index.asInt() < bundle.sym_table.symbols.items.len) {
        const fn_sym = bundle.sym_table.getSymbol(body_ptr.symbol_index).*;
        if (!fn_sym.type_id.isError() and bundle.pool.getFlags(fn_sym.type_id).has_type_vars) return;
    }

    mir.verifyMirBody(allocator, body_ptr, &bundle.pool, &bundle.sym_table, null) catch |ver_err| switch (ver_err) {
        error.V4GhostExclusivityConflict => {
            const saved_has_ghost = body_ptr.has_ghost_instructions;
            body_ptr.has_ghost_instructions = false;
            defer body_ptr.has_ghost_instructions = saved_has_ghost;
            mir.verifyMirBody(allocator, body_ptr, &bundle.pool, &bundle.sym_table, null) catch |inner_err| switch (inner_err) {
                error.V5ReadUninitializedOrMoved, error.V5IncompleteExitInitialization => {},
                else => return inner_err,
            };
        },
        error.V5ReadUninitializedOrMoved, error.V5IncompleteExitInitialization => {},
        else => return ver_err,
    };
}

/// Generates a well-typed multi-function `.cx` program exercising `DR-21` pre-`else` drops, `$` BCE, `@linear`, and `with`.
fn generateWellTypedPhase6Program(
    allocator: std.mem.Allocator,
    random: std.Random,
    prog_idx: usize,
) ![]u8 {
    var src_buf: std.ArrayList(u8) = .empty;
    errdefer src_buf.deinit(allocator);

    try src_buf.appendSlice(
        allocator,
        "pub trait Drop {\n    fn drop(&mut self);\n}\n" ++
            "pub struct TrackedGuard {\n    pub id: i64,\n}\n" ++
            "impl Drop for TrackedGuard {\n" ++
            "    pub fn drop(&mut self) {\n" ++
            "        @drop_trace(self.id);\n" ++
            "    }\n" ++
            "}\n" ++
            "pub struct GuardPair {\n    pub left_g: TrackedGuard,\n    pub right_g: TrackedGuard,\n}\n" ++
            "pub fn consume_guard(guard: own TrackedGuard) -> i64 = guard.id;\n" ++
            "pub fn init_guard_out(slot: &out TrackedGuard, guard_id: i64, /) {\n" ++
            "    slot.* = TrackedGuard { id: guard_id };\n" ++
            "}\n" ++
            "pub fn make_guard(guard_id: i64) -> TrackedGuard = TrackedGuard { id: guard_id };\n" ++
            "pub fn maybe_guard(is_present: bool, guard_id: i64) -> TrackedGuard? {\n" ++
            "    if is_present { return .Some(TrackedGuard { id: guard_id }); }\n" ++
            "    return .None;\n" ++
            "}\n" ++
            "@linear\npub struct LinearTicket {\n    pub code: i64,\n}\n" ++
            "pub fn close_ticket(ticket: own LinearTicket) -> i64 {\n" ++
            "    let LinearTicket { code: extracted } = ticket;\n" ++
            "    return extracted;\n" ++
            "}\n" ++
            "pub fn maybe_ticket(is_ready: bool, code_val: i64) -> LinearTicket? {\n" ++
            "    if is_ready { return .Some(LinearTicket { code: code_val }); }\n" ++
            "    return .None;\n" ++
            "}\n" ++
            "pub fn consume_opt_ticket(opt_ticket: own LinearTicket?, fallback_val: i64) -> i64 {\n" ++
            "    let live_ticket = opt_ticket orelse return fallback_val;\n" ++
            "    return close_ticket(own live_ticket);\n" ++
            "}\n" ++
            "pub struct Arena {\n    pub bump_tag: usize,\n}\n" ++
            "pub fn close_arena(arena_in: own Arena) {\n" ++
            "    let Arena { bump_tag: _bump_tag } = arena_in;\n" ++
            "}\n",
    );

    var helper_buf: [1536]u8 = undefined;
    try src_buf.appendSlice(
        allocator,
        try std.fmt.bufPrint(
            &helper_buf,
            "pub fn mix_lane(val: i64, delta: i64 = 3) -> i64 = (val ^ delta) + 3;\n" ++
                "pub fn slice_and_narrow_step(items: &[i64], raw_idx: usize, raw_byte: i32) -> i64 {{\n" ++
                "    let scoped_helper_guard = TrackedGuard {{ id: {d} }};\n" ++
                "    var total: i64 = scoped_helper_guard.id & 15;\n" ++
                "    if items.len() > 0 {{\n" ++
                "        total = mix_lane(total, items[raw_idx % items.len()]);\n" ++
                "    }}\n" ++
                "    if items.len() >= 3 {{\n" ++
                "        let head_trim: &[i64] = items[..$ - 2];\n" ++
                "        total = total + items[$ - 1] + items[$ - 2] + (head_trim.len() as i64);\n" ++
                "    }}\n" ++
                "    if raw_idx < items.len() {{\n" ++
                "        total = total + items[raw_idx];\n" ++
                "    }}\n" ++
                "    if raw_byte >= 0 and raw_byte <= 200 {{\n" ++
                "        let narrowed_u8: u8 = raw_byte.narrow[u8]();\n" ++
                "        total = total + (narrowed_u8 as i64);\n" ++
                "    }}\n" ++
                "    return total;\n" ++
                "}}\n",
            .{random.intRangeAtMost(i64, 300, 399)},
        ),
    );

    const return_tail = if (prog_idx % 23 == 22)
        "    _ = acc + outer_guard.id;\n    let near_max: i64 = 9223372036854775806;\n    return near_max + ((safe_seed & 7) + 2);\n}\n"
    else
        "    return acc + outer_guard.id;\n}\n";

    var main_buf: [4096]u8 = undefined;
    try src_buf.appendSlice(
        allocator,
        try std.fmt.bufPrint(
            &main_buf,
            "pub fn entry_main(seed: i64) -> i64 {{\n" ++
                "    let safe_seed: i64 = (seed & 31) + 1;\n" ++
                "    let outer_guard = TrackedGuard {{ id: {d} }};\n" ++
                "    let branch_guard = TrackedGuard {{ id: {d} }};\n" ++
                "    let weights: [i64; 4] = [{d}, {d}, {d}, {d}];\n" ++
                "    let view_slice: &[i64] = &weights;\n" ++
                "    var acc: i64 = 0;\n" ++
                "    if (safe_seed & 1) == 0 {{\n" ++
                "        acc = acc + consume_guard(own branch_guard);\n" ++
                "    }} else {{\n" ++
                "        acc = acc + 5;\n" ++
                "    }}\n" ++
                "    var out_g1: TrackedGuard;\n" ++
                "    var out_g2 = TrackedGuard {{ id: 610 }};\n" ++
                "    init_guard_out(&out out_g1, 605);\n" ++
                "    (out_g1, out_g2) = (out_g2, out_g1);\n" ++
                "    let gp_init = GuardPair {{ left_g: own out_g1, right_g: own out_g2 }};\n" ++
                "    let gp_upd = GuardPair {{ left_g: TrackedGuard {{ id: 620 }}, ..own gp_init }};\n" ++
                "    acc = acc + (gp_upd.left_g.id & 7) + (gp_upd.right_g.id & 7);\n" ++
                "    if maybe_guard((safe_seed & 2) == 0, {d}) is .Some(cond_first) and\n" ++
                "        (cond_second := make_guard({d})).id > {d}\n" ++
                "    {{\n" ++
                "        @drop_trace(700);\n" ++
                "        acc = acc + cond_first.id + cond_second.id;\n" ++
                "    }} else {{\n" ++
                "        @drop_trace(800);\n" ++
                "        acc = acc + 3;\n" ++
                "    }}\n" ++
                "    var local_arena = Arena {{ bump_tag: 64 }};\n" ++
                "    let arena_bonus: i64 = with context.allocator = &mut local_arena {{\n" ++
                "        if context.allocator._handle != 0 => 9 else 1\n" ++
                "    }};\n" ++
                "    close_arena(own local_arena);\n" ++
                "    acc = acc + arena_bonus;\n" ++
                "    var iter_idx: i64 = 0;\n" ++
                "    while iter_idx < {d} {{\n" ++
                "        let loop_guard = TrackedGuard {{ id: 400 + iter_idx }};\n" ++
                "        let loop_ticket = LinearTicket {{ code: 10 + iter_idx }};\n" ++
                "        let opt_ticket_val = consume_opt_ticket(maybe_ticket((iter_idx & 1) == 0, 5 + iter_idx), 2);\n" ++
                "        let probe_pos: usize = ((safe_seed + iter_idx) as usize) & 7;\n" ++
                "        let narrow_cand: i32 = ((safe_seed as i32) & 63) + {d};\n" ++
                "        acc = acc + slice_and_narrow_step(view_slice, probe_pos, narrow_cand) + (loop_guard.id & 7) +\n" ++
                "            close_ticket(own loop_ticket) + opt_ticket_val;\n" ++
                "        iter_idx += 1;\n" ++
                "    }}\n" ++
                "{s}",
            .{
                random.intRangeAtMost(i64, 100, 199),
                random.intRangeAtMost(i64, 200, 299),
                random.intRangeAtMost(i64, 2, 17),
                random.intRangeAtMost(i64, 18, 33),
                random.intRangeAtMost(i64, 34, 49),
                random.intRangeAtMost(i64, 50, 65),
                random.intRangeAtMost(i64, 500, 549),
                random.intRangeAtMost(i64, 550, 599),
                random.intRangeAtMost(i64, 540, 590),
                random.intRangeAtMost(i64, 1, 4),
                random.intRangeAtMost(i32, 3, 45),
                return_tail,
            },
        ),
    );

    return src_buf.toOwnedSlice(allocator);
}

/// Evaluates `entry_main(seed_arg)` inside `opt_res` via `MirVm`, capturing scalar/trap, drop trace, and heap leaks.
fn evalPhase6EntryMainInVm(
    allocator: std.mem.Allocator,
    bundle: *MirSastPipelineBundle,
    opt_res: *const MirOptModuleResult,
    seed_arg: i64,
    target_layout: TargetLayout,
) !VmExecutionSnapshot {
    var rodata_pool = RodataPool.init(allocator);
    defer rodata_pool.deinit();

    var vm_engine = try MirVm.init(
        allocator,
        &bundle.interner,
        &bundle.pool,
        &bundle.sym_table,
        &rodata_pool,
        null,
        null,
        .{
            .step_budget = 80_000,
            .target_layout = target_layout,
        },
    );
    defer vm_engine.deinit();

    for (opt_res.bodies.items) |*body_item| {
        var sym_idx = body_item.symbol_index;
        if (sym_idx.isNone() and !body_item.def_id.isNone()) {
            sym_idx = bundle.sym_table.def_to_symbol.get(body_item.def_id.asInt()) orelse .none;
        }
        _ = try vm_engine.registerBody(body_item, sym_idx);
    }

    const entry_body = opt_res.findBodyByName(&bundle.interner, "entry_main") orelse
        return error.MissingEntryMain;

    const outcome: ScalarOrTrapOutcome = if (vm_engine.evalBody(
        entry_body,
        &[_]RegSlot{.{ .scalar_i64 = seed_arg }},
    )) |eval_res|
        .{ .scalar_i64 = eval_res.slot.scalar_i64 }
    else |vm_err| switch (vm_err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => .{ .vm_trap = vm_err },
    };

    const raw_trace = vm_engine.asDropTraceSlice();
    return .{
        .outcome = outcome,
        .drop_trace = if (raw_trace.len > 0)
            try allocator.dupe(i64, raw_trace)
        else
            &[_]i64{},
        .unfreed_heap_count = vm_engine.countUnfreedHeapAllocations(),
    };
}

/// Builds a 5-item `.cx` module for incremental `CompilerDb` Stage 9–13 SAST summary cutoff fuzzing.
fn buildIncrementalPhase6Module(
    allocator: std.mem.Allocator,
    has_banner_comment: bool,
    const_choice: usize,
    leaf_choice: usize,
    caller_choices: [3]usize,
) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    if (has_banner_comment) {
        try builder.appendSlice(allocator, "/# Incremental Phase 6 SAST 34-byte summary cutoff banner\n\n");
    }
    try builder.appendSlice(allocator, INCREMENTAL_CONST_VARIANTS[const_choice]);

    try builder.appendSlice(allocator, "pub fn leaf_helper(val: i64) -> i64 {\n");
    try builder.appendSlice(allocator, INCREMENTAL_LEAF_VARIANTS[leaf_choice]);
    try builder.appendSlice(allocator, "}\n\n");

    var caller_idx: usize = 0;
    while (caller_idx < 3) : (caller_idx += 1) {
        var hdr_buf: [128]u8 = undefined;
        try builder.appendSlice(
            allocator,
            try std.fmt.bufPrint(
                &hdr_buf,
                "pub fn caller_{d}(input_val: i64, probe_idx: usize) -> i64 {{\n",
                .{caller_idx},
            ),
        );
        try builder.appendSlice(allocator, INCREMENTAL_CALLER_VARIANTS[caller_choices[caller_idx]]);
        try builder.appendSlice(allocator, "}\n\n");
    }

    return builder.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_phase6_malformed_and_mutated_sast_fault_tolerance" {
    var prng = std.Random.DefaultPrng.init(0xFA5E_0606_2026_5A57);
    const random = prng.random();

    var source_buf: [12288]u8 = undefined;
    var verified_clean_modules: usize = 0;

    var iter_idx: usize = 0;
    while (iter_idx < MALFORMED_SAST_ITERATIONS) : (iter_idx += 1) {
        var byte_len: usize = 0;
        const is_clean_seed_round = (iter_idx % 5 == 0);

        if (is_clean_seed_round) {
            // Emit foundation declarations `0..7` without duplicates plus a random subset of `7..15`:
            for (PHASE6_SEED_ITEMS[0..7]) |base_item| {
                @memcpy(source_buf[byte_len .. byte_len + base_item.len], base_item);
                byte_len += base_item.len;
            }
            var extra_idx: usize = 7;
            while (extra_idx < PHASE6_SEED_ITEMS.len) : (extra_idx += 1) {
                if (random.boolean()) {
                    const extra_item = PHASE6_SEED_ITEMS[extra_idx];
                    @memcpy(source_buf[byte_len .. byte_len + extra_item.len], extra_item);
                    byte_len += extra_item.len;
                }
            }
        } else {
            // Include `TrackedBuf` / `Arena` helpers 50% of the time so SAST error snippets reach Pass 1–4:
            if (random.boolean()) {
                for (PHASE6_SEED_ITEMS[0..7]) |foundation_item| {
                    if (byte_len + foundation_item.len <= source_buf.len) {
                        @memcpy(source_buf[byte_len .. byte_len + foundation_item.len], foundation_item);
                        byte_len += foundation_item.len;
                    }
                }
            }
            const snippet_count = random.intRangeAtMost(usize, 2, 5);
            var item_idx: usize = 0;
            while (item_idx < snippet_count) : (item_idx += 1) {
                const chosen_snippet = if (random.uintLessThan(u8, 2) == 0)
                    PHASE6_MUTATION_SNIPPETS[random.uintLessThan(usize, PHASE6_MUTATION_SNIPPETS.len)]
                else
                    PHASE6_SEED_ITEMS[random.intRangeAtMost(usize, 7, PHASE6_SEED_ITEMS.len - 1)];

                if (byte_len + chosen_snippet.len <= source_buf.len) {
                    @memcpy(source_buf[byte_len .. byte_len + chosen_snippet.len], chosen_snippet);
                    byte_len += chosen_snippet.len;
                }
            }
        }

        // Apply single-byte perturbation on 25% of non-clean rounds:
        if (!is_clean_seed_round and iter_idx % 4 == 0 and byte_len > 0) {
            const mut_pos = random.uintLessThan(usize, byte_len);
            source_buf[mut_pos] = switch (random.uintLessThan(u8, 9)) {
                0 => ';',
                1 => ' ',
                2 => '&',
                3 => '[',
                4 => '}',
                5 => '_',
                6 => '$',
                7 => ':',
                else => source_buf[mut_pos],
            };
        }

        const source_slice = source_buf[0..byte_len];
        const target_layout = if ((iter_idx & 1) == 0) TargetLayout.NATIVE_64 else TargetLayout.WASM32;

        var bundle = corex.lowerAndVerifySourceMirSast(
            std.testing.allocator,
            FileId.fromInt(@intCast((iter_idx & 0xFF) + 1)),
            source_slice,
            target_layout,
            .{ .is_sast_strict = (iter_idx & 2) != 0 },
        ) catch |err| {
            if (isExpectedMutationVerifierError(err)) continue;
            return err;
        };
        defer bundle.deinit();

        try std.testing.expect(bundle.sast_result.peak_pentagon_bytes <= MAX_PENTAGON_SCRATCH_BYTES);

        if (!bundle.diagnostics.hasErrors()) {
            verified_clean_modules += 1;
            for (bundle.mir_module.bodies.items) |*body_ptr| {
                try verifyCleanSastBody(std.testing.allocator, body_ptr, &bundle);
            }

            var dev_sink = DiagnosticSink.init(std.testing.allocator);
            defer dev_sink.deinit();
            var dev_opt = try mir_opt.optimizeMirModule(
                std.testing.allocator,
                bundle.mir_module.bodies.items,
                &bundle.pool,
                &bundle.sym_table,
                &bundle.interner,
                MirOptConfig{
                    .is_release_mode = false,
                    .target_layout = target_layout,
                    .syntax_view = .{
                        .source = source_slice,
                        .tokens = &bundle.token_buffer,
                        .cst_arena = &bundle.cst_arena,
                    },
                },
                &dev_sink,
            );
            defer dev_opt.deinit();
            for (dev_sink.diagnostics.items) |opt_diag| {
                if (opt_diag.severity == .err) {
                    try std.testing.expect(
                        opt_diag.code == .e0502_integer_constant_overflow or
                            opt_diag.code == .e0507_comptime_arithmetic_trap or
                            opt_diag.code == .e0508_comptime_resource_limit_exceeded,
                    );
                }
            }
            if (!dev_sink.hasErrors()) {
                for (dev_opt.bodies.items) |*dev_body| {
                    try mir.verifyMirBody(
                        std.testing.allocator,
                        dev_body,
                        &bundle.pool,
                        &bundle.sym_table,
                        null,
                    );
                }
            }
        }
    }

    try std.testing.expect(verified_clean_modules >= 40);
}

test "test_fuzz_phase6_differential_dev_vs_release_drop_and_bce_parity" {
    var prng = std.Random.DefaultPrng.init(0xD1FF_0606_2026_D809);
    const random = prng.random();

    var prog_idx: usize = 0;
    while (prog_idx < DIFFERENTIAL_DROP_BCE_ITERATIONS) : (prog_idx += 1) {
        const prog_src = try generateWellTypedPhase6Program(
            std.testing.allocator,
            random,
            prog_idx,
        );
        defer std.testing.allocator.free(prog_src);

        const seed_arg = random.intRangeAtMost(i64, -40, 120);
        const file_id = FileId.fromInt(@intCast((prog_idx & 0xFF) + 1));

        for ([_]TargetLayout{ TargetLayout.NATIVE_64, TargetLayout.WASM32 }) |target_layout| {
            var bundle = try corex.lowerAndVerifySourceMirSast(
                std.testing.allocator,
                file_id,
                prog_src,
                target_layout,
                .{ .is_sast_strict = true },
            );
            defer bundle.deinit();
            try std.testing.expect(!bundle.diagnostics.hasErrors());
            try std.testing.expectEqual(@as(usize, 0), bundle.diagnostics.diagnostics.items.len);
            try std.testing.expect(bundle.sast_result.emitted_drops >= 2);
            try std.testing.expect(bundle.sast_result.eliminated_bounds_checks >= 1);
            try std.testing.expect(bundle.sast_result.peak_pentagon_bytes <= MAX_PENTAGON_SCRATCH_BYTES);

            var dev_sink = DiagnosticSink.init(std.testing.allocator);
            defer dev_sink.deinit();
            var dev_opt = try mir_opt.optimizeMirModule(
                std.testing.allocator,
                bundle.mir_module.bodies.items,
                &bundle.pool,
                &bundle.sym_table,
                &bundle.interner,
                MirOptConfig{
                    .is_release_mode = false,
                    .target_layout = target_layout,
                    .syntax_view = .{
                        .source = prog_src,
                        .tokens = &bundle.token_buffer,
                        .cst_arena = &bundle.cst_arena,
                    },
                },
                &dev_sink,
            );
            defer dev_opt.deinit();
            for (dev_sink.diagnostics.items) |opt_diag| {
                if (opt_diag.severity == .err) {
                    try std.testing.expect(
                        opt_diag.code == .e0502_integer_constant_overflow or
                            opt_diag.code == .e0507_comptime_arithmetic_trap or
                            opt_diag.code == .e0508_comptime_resource_limit_exceeded,
                    );
                }
            }
            if (!dev_sink.hasErrors()) {
                for (dev_opt.bodies.items) |*dev_body| {
                    try mir.verifyMirBody(
                        std.testing.allocator,
                        dev_body,
                        &bundle.pool,
                        &bundle.sym_table,
                        null,
                    );
                }
            }

            var rel_sink = DiagnosticSink.init(std.testing.allocator);
            defer rel_sink.deinit();
            var rel_opt = try mir_opt.optimizeMirModule(
                std.testing.allocator,
                bundle.mir_module.bodies.items,
                &bundle.pool,
                &bundle.sym_table,
                &bundle.interner,
                MirOptConfig{
                    .is_release_mode = true,
                    .target_layout = target_layout,
                    .syntax_view = .{
                        .source = prog_src,
                        .tokens = &bundle.token_buffer,
                        .cst_arena = &bundle.cst_arena,
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
                    &bundle.pool,
                    &bundle.sym_table,
                    null,
                );
            }

            var dev_snap = try evalPhase6EntryMainInVm(
                std.testing.allocator,
                &bundle,
                &dev_opt,
                seed_arg,
                target_layout,
            );
            defer dev_snap.deinit(std.testing.allocator);

            var rel_snap = try evalPhase6EntryMainInVm(
                std.testing.allocator,
                &bundle,
                &rel_opt,
                seed_arg,
                target_layout,
            );
            defer rel_snap.deinit(std.testing.allocator);

            try std.testing.expectEqual(dev_snap.outcome, rel_snap.outcome);
            try std.testing.expectEqualSlices(i64, dev_snap.drop_trace, rel_snap.drop_trace);
            try std.testing.expectEqual(@as(usize, 0), dev_snap.unfreed_heap_count);
            try std.testing.expectEqual(@as(usize, 0), rel_snap.unfreed_heap_count);
            if (dev_snap.outcome == .scalar_i64) {
                try std.testing.expect(dev_snap.drop_trace.len >= 3);
            }
        }
    }
}

test "test_fuzz_phase6_incremental_compiler_db_sast_summary_cutoff_parity" {
    var prng = std.Random.DefaultPrng.init(0xDB06_5A57_2026_0034);
    const random = prng.random();

    var inc_db = try CompilerDb.init(std.testing.allocator);
    defer inc_db.deinit();

    const file_id = FileId.fromInt(1);
    var has_banner_comment = false;
    var is_sast_strict = false;
    var const_choice: usize = 0;
    var leaf_choice: usize = 0;
    var caller_choices = [3]usize{ 0, 1, 3 };
    var durability: Durability = .low;

    var step_idx: usize = 0;
    while (step_idx < INCREMENTAL_SAST_DB_ITERATIONS) : (step_idx += 1) {
        switch (random.uintLessThan(u8, 6)) {
            0 => has_banner_comment = !has_banner_comment,
            1 => const_choice = random.uintLessThan(usize, INCREMENTAL_CONST_VARIANTS.len),
            2 => leaf_choice = random.uintLessThan(usize, INCREMENTAL_LEAF_VARIANTS.len),
            3 => caller_choices[random.uintLessThan(usize, 3)] =
                random.uintLessThan(usize, INCREMENTAL_CALLER_VARIANTS.len),
            4 => {
                is_sast_strict = !is_sast_strict;
                inc_db.setSastStrict(is_sast_strict);
            },
            else => durability = switch (random.uintLessThan(u8, 3)) {
                0 => .low,
                1 => .medium,
                else => .high,
            },
        }

        const mod_src = try buildIncrementalPhase6Module(
            std.testing.allocator,
            has_banner_comment,
            const_choice,
            leaf_choice,
            caller_choices,
        );
        defer std.testing.allocator.free(mod_src);

        _ = try inc_db.setInput(file_id, mod_src, durability);

        var scratch_db = try CompilerDb.init(std.testing.allocator);
        defer scratch_db.deinit();
        scratch_db.setSastStrict(is_sast_strict);
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

        // [2] Stage 9 `verifySastMir` & 34-byte `getSastSummaryProj` parity across `leaf_helper` and `caller_0..2`:
        var item_ord: u12 = 1;
        while (item_ord < 5) : (item_ord += 1) {
            const def_id = DefId.init(file_id, item_ord);

            const inc_sast = try inc_db.verifySastMir(def_id);
            const scr_sast = try scratch_db.verifySastMir(def_id);
            try std.testing.expectEqual(inc_sast.is_verified_sound, scr_sast.is_verified_sound);
            try std.testing.expectEqual(inc_sast.error_count, scr_sast.error_count);
            try std.testing.expectEqual(inc_sast.warning_count, scr_sast.warning_count);
            try std.testing.expectEqual(
                inc_sast.eliminated_bounds_checks,
                scr_sast.eliminated_bounds_checks,
            );
            try std.testing.expectEqual(
                inc_sast.eliminated_narrow_checks,
                scr_sast.eliminated_narrow_checks,
            );
            try std.testing.expectEqual(inc_sast.emitted_drops, scr_sast.emitted_drops);
            try std.testing.expect(
                Fingerprint128.eql(inc_sast.sast_fingerprint, scr_sast.sast_fingerprint),
            );

            const inc_proj = try inc_db.getSastSummaryProj(def_id);
            const scr_proj = try scratch_db.getSastSummaryProj(def_id);
            var inc_obs: [FnRegionSummary.OBSERVABLE_SUMMARY_BYTES]u8 = undefined;
            var scr_obs: [FnRegionSummary.OBSERVABLE_SUMMARY_BYTES]u8 = undefined;
            inc_proj.writeObservableBytes(&inc_obs);
            scr_proj.writeObservableBytes(&scr_obs);
            try std.testing.expectEqualSlices(u8, &inc_obs, &scr_obs);

            try std.testing.expect(
                Fingerprint128.eql(
                    (try inc_db.fetchQuery(QueryKey.forSastSummaryProj(def_id))).output_fingerprint,
                    (try scratch_db.fetchQuery(QueryKey.forSastSummaryProj(def_id))).output_fingerprint,
                ),
            );
        }

        // [3] Stage 13 `optimizeMirModule` parity across both `--dev` and `--release`:
        for ([_]bool{ false, true }) |is_release_mode| {
            const inc_opt = try inc_db.optimizeMirModule(file_id, is_release_mode);
            const scr_opt = try scratch_db.optimizeMirModule(file_id, is_release_mode);
            try std.testing.expectEqual(inc_opt.fingerprint, scr_opt.fingerprint);
            try std.testing.expectEqual(inc_opt.bodies.items.len, scr_opt.bodies.items.len);
            try std.testing.expectEqual(inc_opt.dedup_merged_count, scr_opt.dedup_merged_count);
            try std.testing.expectEqual(inc_opt.icf_folded_count, scr_opt.icf_folded_count);
        }
    }

    try std.testing.expect(inc_db.telemetry.early_cutoff_hits >= 1);
}

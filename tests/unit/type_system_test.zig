//! Unit Tests for Canonical `InternPool`, Constrained Type Groups & Bidirectional Type Checker (`tests/unit/type_system_test.zig`)
//!
//! Exercises the 14-byte SoA `TypeNode`, `InternPool` (`TypeArena`) static slots `0..63`, $O(1)$
//! `TypeGroupMask` algebra, Bind-Once (`E0404`) vs. Bind-Many (`any Group`) generics, `distinct`
//! newtype isolation (`E0405`), `~T` underlying-type approximation (`E0402`), `is` range refinements
//! (`E0406`), `bit_field` width verification, `#soa` column slice projection, contextual `.Variant`
//! inference (`E0407`), `@overload` disambiguation (`E0400`), `Result[T, E]` / `T?` postfix `?`
//! (`E0410`) with `@from` upcasting (`E0411`), `catch |err|`, `let … else` divergence (`E0412`),
//! `@must_use` / `Result` discard checks (`E0413` / `E0414`), Maranget exhaustiveness (`E0415` /
//! `W0401`), integer literal overflow (`E0502`), and `CompilerDb` incremental body type-checking.

const std = @import("std");
const corex = @import("corex");

const type_system = corex.type_system;
const FileId = corex.FileId;
const DefId = corex.DefId;
const TypeId = corex.TypeId;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const DiagnosticCode = corex.DiagnosticCode;
const TypeTag = type_system.TypeTag;
const TypeFlags = type_system.TypeFlags;
const ParamMode = type_system.ParamMode;
const TypeGroupMask = type_system.TypeGroupMask;
const InternPool = type_system.InternPool;

// -------------------------------------- INTERNALS --------------------------------------

/// Runs `typecheckSource` on `source` and returns its `TypecheckResult`.
fn runFullTypecheck(
    allocator: std.mem.Allocator,
    source: []const u8,
) !type_system.TypecheckResult {
    return type_system.typecheckSource(allocator, FileId.fromInt(1), source);
}

/// Returns `true` if `sink` contains at least one diagnostic with `expected_code`.
fn hasDiag(sink: *const DiagnosticSink, expected_code: DiagnosticCode) bool {
    for (sink.diagnostics.items) |diag| {
        if (diag.code == expected_code) return true;
    }
    return false;
}

// ------------------------------------- PUBLIC API --------------------------------------

// -------- 14-Byte TypeNode, InternPool & TypeGroupMask --------

test "test_type_system_14_byte_soa_node_intern_pool_and_type_group_masks" {
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(TypeTag));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(TypeFlags));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(ParamMode));
    try std.testing.expectEqual(
        @as(usize, 14),
        @sizeOf(TypeTag) + @sizeOf(TypeFlags) + 3 * @sizeOf(u32),
    );

    var pool = try InternPool.init(std.testing.allocator);
    defer pool.deinit();

    // [1] Static slots `0..63` pre-allocated:
    try std.testing.expectEqual(@as(usize, 64), pool.countTypes());
    try std.testing.expect(pool.getFlags(.err_ty).has_error);
    try std.testing.expect(pool.getFlags(.i32_ty).is_copy);
    try std.testing.expect(pool.getFlags(.u128_ty).is_copy);
    try std.testing.expect(pool.getFlags(.str_ty).is_copy);

    // [2] O(1) `TypeGroupMask` membership and subset algebra (`DR-04` Section 1.2):
    try std.testing.expect(TypeGroupMask.containsPrimitive(TypeGroupMask.SIGNED, .i32_ty));
    try std.testing.expect(!TypeGroupMask.containsPrimitive(TypeGroupMask.SIGNED, .u32_ty));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.SIGNED, TypeGroupMask.INTEGER));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.INTEGER, TypeGroupMask.NUMBER));
    try std.testing.expect(!TypeGroupMask.isSubsetOf(TypeGroupMask.SIGNED, TypeGroupMask.UNSIGNED));

    try std.testing.expect(TypeGroupMask.containsPrimitive(TypeGroupMask.UNSIGNED, .u64_ty));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.UNSIGNED, TypeGroupMask.INTEGER));

    try std.testing.expect(TypeGroupMask.containsPrimitive(TypeGroupMask.FLOAT, .f64_ty));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.FLOAT, TypeGroupMask.NUMBER));

    try std.testing.expect(TypeGroupMask.containsPrimitive(TypeGroupMask.COMPARABLE, .str_ty));
    try std.testing.expect(TypeGroupMask.isSubsetOf(TypeGroupMask.COMPARABLE, TypeGroupMask.EQUATABLE));

    // [3] Structural deduplication across composite types:
    const ref_a = try pool.internRef(.i32_ty, false);
    const ref_b = try pool.internRef(.i32_ty, false);
    const mut_ref = try pool.internRef(.i32_ty, true);
    try std.testing.expectEqual(ref_a, ref_b);
    try std.testing.expect(ref_a != mut_ref);

    const res_a = try pool.internResult(.u64_ty, .str_ty);
    const res_b = try pool.internResult(.u64_ty, .str_ty);
    try std.testing.expectEqual(res_a, res_b);
    try std.testing.expect(pool.getFlags(res_a).is_must_use);

    const ref_range_a = try pool.internRefined(.u16_ty, .none, 1, 1024);
    const ref_range_b = try pool.internRefined(.u16_ty, .none, 1, 1024);
    try std.testing.expectEqual(ref_range_a, ref_range_b);
    try std.testing.expectEqual(TypeId.u16_ty, pool.unwrapRefinementBase(ref_range_a));
}

// ---------- Bind-Once (E0404) vs. Bind-Many Generics ----------

test "test_type_system_bind_once_e0404_vs_bind_many_and_composite_unification" {
    // [1] Valid Bind-Once, Bind-Many, and composite slice `[Number]` calls:
    {
        const valid_src =
            "pub fn add_same(lhs: Number, rhs: Number) -> Number {\n" ++
            "    return lhs + rhs;\n" ++
            "}\n" ++
            "pub fn compare_any(lhs: any Number, rhs: any Number) -> bool {\n" ++
            "    let _keep_lhs = lhs;\n" ++
            "    let _keep_rhs = rhs;\n" ++
            "    return true;\n" ++
            "}\n" ++
            "pub fn first_same(xs: &[Number], ys: &[Number]) -> Number {\n" ++
            "    let _keep_ys = ys;\n" ++
            "    return xs[0];\n" ++
            "}\n" ++
            "pub fn caller(a32: i32, b32: i32, c8: i8, d64: i64, s1: &[i32], s2: &[i32]) -> i32 {\n" ++
            "    let sum = add_same(a32, b32);\n" ++
            "    let _ok = compare_any(c8, d64);\n" ++
            "    let elem = first_same(s1, s2);\n" ++
            "    return sum + elem;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, valid_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    // [2] Passing mismatched types (`i32` and `i64`) to Bind-Once `Number` emits `E0404`:
    {
        const conflict_src =
            "pub fn add_same(lhs: Number, rhs: Number) -> Number {\n" ++
            "    return lhs + rhs;\n" ++
            "}\n" ++
            "pub fn bad_caller(lhs: i32, rhs: i64) -> i32 {\n" ++
            "    return add_same(lhs, rhs);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, conflict_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0404_bind_once_group_conflict));
    }

    // [3] Passing mismatched slices (`&[i32]` and `&[i64]`) to composite `&[Number]` emits `E0404`:
    {
        const slice_conflict_src =
            "pub fn pair_slices(xs: &[Number], ys: &[Number]) -> Number {\n" ++
            "    let _keep = ys;\n" ++
            "    return xs[0];\n" ++
            "}\n" ++
            "pub fn bad_slice_caller(xs: &[i32], ys: &[i64]) -> i32 {\n" ++
            "    return pair_slices(xs, ys);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, slice_conflict_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0404_bind_once_group_conflict));
    }

    // [4] `-> any Group` in return position is rejected with `E0402`:
    {
        const bad_ret_src =
            "pub fn invalid_return(val: i32) -> any Number {\n" ++
            "    return val;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, bad_ret_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0402_unsatisfied_trait_bound));
    }
}

// -------- Distinct Newtypes (E0405), ~T & Type Groups ---------

test "test_type_system_distinct_newtypes_e0405_tilde_approximation_and_user_groups" {
    // [1] Mixing `distinct` newtype with base type or sibling `distinct` type emits `E0405`:
    {
        const distinct_err_src =
            "pub type UserId = distinct u64;\n" ++
            "pub type OrderId = distinct u64;\n" ++
            "pub fn mix_ids(user_id: UserId, order_id: OrderId, raw_val: u64) -> UserId {\n" ++
            "    let _bad_cmp = user_id == order_id;\n" ++
            "    return user_id + raw_val;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, distinct_err_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0405_distinct_type_mixing));
    }

    // [2] Passing `distinct` type to bare `Unsigned` fails (`E0402`), but `~u64`, `~Unsigned`, and `type G = ~u64` succeed:
    {
        const tilde_ok_src =
            "pub type UserId = distinct u64;\n" ++
            "pub type AnyU64Id = u32 | ~u64;\n" ++
            "pub fn accept_tilde_prim(val: ~u64) -> ~u64 {\n" ++
            "    return val;\n" ++
            "}\n" ++
            "pub fn accept_tilde_group(val: ~Unsigned) -> ~Unsigned {\n" ++
            "    return val;\n" ++
            "}\n" ++
            "pub fn accept_user_group(val: AnyU64Id) -> AnyU64Id {\n" ++
            "    return val;\n" ++
            "}\n" ++
            "pub fn test_caller(uid: UserId) -> UserId {\n" ++
            "    let step1: UserId = accept_tilde_prim(uid);\n" ++
            "    let step2: UserId = accept_tilde_group(step1);\n" ++
            "    return accept_user_group(step2);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, tilde_ok_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    {
        const bare_group_reject_src =
            "pub type UserId = distinct u64;\n" ++
            "pub fn require_bare_unsigned(val: Unsigned) -> Unsigned {\n" ++
            "    return val;\n" ++
            "}\n" ++
            "pub fn bad_caller(uid: UserId) -> UserId {\n" ++
            "    return require_bare_unsigned(uid);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, bare_group_reject_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0402_unsatisfied_trait_bound));
    }
}

// -------- Range Refinements (E0406), bit_field & #soa ---------

test "test_type_system_range_refinements_e0406_bit_field_soa_and_overflow_e0502" {
    // [1] `is` range refinements: in-range literal & subrange widening succeed; out-of-range emits `E0406`:
    {
        const refine_ok_src =
            "pub type WellKnownPort = u16 is 1..=1024;\n" ++
            "pub type NonZeroPort = u16 is 1..=65535;\n" ++
            "pub fn widen_port(port: WellKnownPort) -> NonZeroPort {\n" ++
            "    let _raw_u16: u16 = port;\n" ++
            "    return port;\n" ++
            "}\n" ++
            "pub fn make_http_port() -> WellKnownPort {\n" ++
            "    return 80;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, refine_ok_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    {
        const refine_err_src =
            "pub type WellKnownPort = u16 is 1..=1024;\n" ++
            "pub fn bad_port() -> WellKnownPort {\n" ++
            "    return 8080;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, refine_err_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0406_range_refinement_violation));
    }

    // [2] `bit_field(u8)` exact 8-bit sum passes; mismatched 7-bit sum emits `E0406`:
    {
        const bf_ok_src =
            "pub bit_field Flags8(u8) {\n" ++
            "    pub mode: u8 | 3,\n" ++
            "    pub status: u8 | 4,\n" ++
            "    pub active: bool | 1,\n" ++
            "}\n" ++
            "pub fn read_mode(flags: Flags8) -> u8 {\n" ++
            "    return flags.mode;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, bf_ok_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    {
        const bf_bad_src =
            "pub bit_field BadFlags(u8) {\n" ++
            "    pub mode: u8 | 3,\n" ++
            "    pub status: u8 | 4,\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, bf_bad_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0406_range_refinement_violation));
    }

    // [3] `#soa [Particle]` column slice projection (`particles.vx` has type `[f32]`):
    {
        const soa_src =
            "pub struct Particle {\n" ++
            "    pub vx: f32,\n" ++
            "    pub vy: f32,\n" ++
            "}\n" ++
            "pub fn first_velocity_x(particles: #soa [Particle]) -> f32 {\n" ++
            "    let vx_col: [f32] = particles.vx;\n" ++
            "    return vx_col[0];\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, soa_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    // [4] Integer literal bounds (`u128::MAX` and `i128::MIN` succeed; `256` into `u8` emits `E0502`):
    {
        const bounds_ok_src =
            "pub const MAX_U128: u128 = 340282366920938463463374607431768211455;\n" ++
            "pub const MIN_I128: i128 = -170141183460469231731687303715884105728;\n";

        var res = try runFullTypecheck(std.testing.allocator, bounds_ok_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    {
        const overflow_src =
            "pub fn bad_byte() -> u8 {\n" ++
            "    return 256;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, overflow_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0502_integer_constant_overflow));
    }
}

// ---------- Contextual .Variant, @overload & Error ? ----------

test "test_type_system_contextual_variants_overload_try_from_error_and_must_use" {
    // [1] Contextual `.Variant` in `let`, `return`, binary `==`, and invalid `.Unknown` (`E0407`):
    {
        const ctx_ok_src =
            "pub enum State { Idle, Running(u32) }\n" ++
            "pub fn check_state(cur: State) -> u32? {\n" ++
            "    if cur == .Idle {\n" ++
            "        return .None;\n" ++
            "    }\n" ++
            "    return .Some(42);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, ctx_ok_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    {
        const ctx_bad_src =
            "pub enum State { Idle, Running }\n" ++
            "pub fn invalid_state() -> State {\n" ++
            "    return .NonExistent;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, ctx_bad_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0407_invalid_contextual_variant));
    }

    // [2] `@overload` ambiguity emits `E0400`:
    {
        const ambig_src =
            "@overload\n" ++
            "pub fn process_num(val: Integer) -> i32 {\n" ++
            "    let _keep = val;\n" ++
            "    return 1;\n" ++
            "}\n" ++
            "@overload\n" ++
            "pub fn process_num(val: Signed) -> i32 {\n" ++
            "    let _keep = val;\n" ++
            "    return 2;\n" ++
            "}\n" ++
            "pub fn call_ambig(arg: i32) -> i32 {\n" ++
            "    return process_num(arg);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, ambig_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0400_ambiguous_overload));
    }

    // [3] `?` propagation with `@from` enum variant upcasting (`DR-07`) vs missing `@from` (`E0411`) & non-fallible (`E0410`):
    {
        const from_ok_src =
            "pub struct IoError { pub code: i32 }\n" ++
            "pub enum AppError {\n" ++
            "    @from Io(IoError),\n" ++
            "    Other,\n" ++
            "}\n" ++
            "pub fn read_low(flag: bool) -> Result[i32, IoError] {\n" ++
            "    if flag { return .Ok(10); }\n" ++
            "    return .Err(IoError { code: 1 });\n" ++
            "}\n" ++
            "pub fn run_app(flag: bool) -> Result[i32, AppError] {\n" ++
            "    let val = read_low(flag)?;\n" ++
            "    return .Ok(val + 1);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, from_ok_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
    }

    {
        const missing_from_src =
            "pub struct IoError { pub code: i32 }\n" ++
            "pub struct DbError { pub code: i32 }\n" ++
            "pub fn query_db() -> Result[i32, DbError] {\n" ++
            "    return .Ok(1);\n" ++
            "}\n" ++
            "pub fn handler() -> Result[i32, IoError] {\n" ++
            "    let val = query_db()?;\n" ++
            "    return .Ok(val);\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, missing_from_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0411_missing_from_error_conversion));
    }

    {
        const try_in_infallible_src =
            "pub fn fallible() -> Result[i32, i32] {\n" ++
            "    return .Ok(1);\n" ++
            "}\n" ++
            "pub fn infallible() -> i32 {\n" ++
            "    return fallible()?;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, try_in_infallible_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0410_try_outside_fallible_fn));
    }

    // [4] `let … else` non-diverging `else` block (`E0412`), unused `Result` (`E0413`), and wildcard `let _ = fallible()` (`E0414`):
    {
        const err_sem_src =
            "pub fn compute_res(val: i32) -> Result[i32, i32] {\n" ++
            "    return .Ok(val);\n" ++
            "}\n" ++
            "pub fn bad_semantics(opt_val: i32?) -> i32 {\n" ++
            "    compute_res(1);\n" ++
            "    let _ = compute_res(2);\n" ++
            "    let .Some(unwrapped) = opt_val else {\n" ++
            "        let _non_diverging: i32 = 0;\n" ++
            "    };\n" ++
            "    return unwrapped;\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, err_sem_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0412_let_else_not_diverging));
        try std.testing.expect(hasDiag(&res.diagnostics, .e0413_unhandled_must_use_or_result));
        try std.testing.expect(hasDiag(&res.diagnostics, .e0414_bare_wildcard_result_discard));
    }
}

// -------- Maranget Exhaustiveness (E0415) & CompilerDb --------

test "test_type_system_maranget_exhaustiveness_e0415_w0401_and_incremental_query_db" {
    // [1] Non-exhaustive `match` on integer range (`E0415`) and unreachable duplicate arm (`W0401`):
    {
        const match_src =
            "pub fn classify_byte(val: u8) -> i32 {\n" ++
            "    return match val {\n" ++
            "        0..=100 => 1,\n" ++
            "        50..=80 => 2,\n" ++
            "        101..=200 => 3,\n" ++
            "    };\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, match_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0415_non_exhaustive_match));
        try std.testing.expect(hasDiag(&res.diagnostics, .w0401_unreachable_pattern_arm));
    }

    // [2] Refutable nested pattern `.Some(1)` followed by `.Some(_)` and `.None` is exhaustive without false `W0401`:
    {
        const nested_match_src =
            "pub fn inspect_opt(opt: u8?) -> i32 {\n" ++
            "    return match opt {\n" ++
            "        .Some(1) => 10,\n" ++
            "        .Some(_) => 20,\n" ++
            "        .None => 0,\n" ++
            "    };\n" ++
            "}\n";

        var res = try runFullTypecheck(std.testing.allocator, nested_match_src);
        defer res.deinit();
        try std.testing.expect(!res.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(u32, 0), res.diagnostics.warning_count);
    }

    // [3] `CompilerDb` incremental body expansion preserving `@from` pairs (`CRIT-03`) and shifted AST nodes (`CRIT-05`):
    {
        var db = try CompilerDb.init(std.testing.allocator);
        defer db.deinit();

        const file_id = FileId.fromInt(1);
        const rev1_src =
            "pub struct LowErr { pub code: i32 }\n" ++
            "pub enum TopErr { @from Wrap(LowErr), Other }\n" ++
            "pub fn first_fn(val: i32) -> Result[i32, LowErr] {\n" ++
            "    return .Ok(val + 1);\n" ++
            "}\n" ++
            "pub fn second_fn(val: i32) -> Result[i32, TopErr] {\n" ++
            "    let step = first_fn(val)?;\n" ++
            "    return .Ok(step * 2);\n" ++
            "}\n";

        _ = try db.setInput(file_id, rev1_src, .low);
        const def_first = DefId.init(file_id, 2);
        const def_second = DefId.init(file_id, 3);

        const body1_r1 = try db.typecheckBody(def_first);
        const body2_r1 = try db.typecheckBody(def_second);
        try std.testing.expectEqual(@as(u32, 0), body1_r1.error_count);
        try std.testing.expectEqual(@as(u32, 0), body2_r1.error_count);

        // Expand `first_fn`'s body with extra local statements (shifting `second_fn`'s AST node indices while
        // `ItemTree` signature firewall keeps `resolve_signatures` backdated):
        const rev2_src =
            "pub struct LowErr { pub code: i32 }\n" ++
            "pub enum TopErr { @from Wrap(LowErr), Other }\n" ++
            "pub fn first_fn(val: i32) -> Result[i32, LowErr] {\n" ++
            "    let s1 = val + 1;\n" ++
            "    let s2 = s1 + 2;\n" ++
            "    let s3 = s2 + 3;\n" ++
            "    let s4 = s3 + 4;\n" ++
            "    return .Ok(s4);\n" ++
            "}\n" ++
            "pub fn second_fn(val: i32) -> Result[i32, TopErr] {\n" ++
            "    let step = first_fn(val)?;\n" ++
            "    return .Ok(step * 2);\n" ++
            "}\n";

        _ = try db.setInput(file_id, rev2_src, .low);
        const body1_r2 = try db.typecheckBody(def_first);
        const body2_r2 = try db.typecheckBody(def_second);
        try std.testing.expectEqual(@as(u32, 0), body1_r2.error_count);
        try std.testing.expectEqual(@as(u32, 0), body2_r2.error_count);
    }

    // [4] Nominal `enum` exhaustiveness ignores implicit `Self` and `impl` methods in `target_scope`:
    {
        const exhaustive_enum_src =
            "pub enum Mode { Alpha, Beta(i32) }\n" ++
            "impl Mode {\n" ++
            "    pub fn weight(&self) -> i32 { return 1; }\n" ++
            "}\n" ++
            "pub fn eval_mode(mode: Mode) -> i32 {\n" ++
            "    return match mode {\n" ++
            "        .Alpha => 0,\n" ++
            "        .Beta(val) => val,\n" ++
            "    };\n" ++
            "}\n";

        var ok_res = try runFullTypecheck(std.testing.allocator, exhaustive_enum_src);
        defer ok_res.deinit();
        try std.testing.expect(!ok_res.diagnostics.hasErrors());
        try std.testing.expectEqual(@as(u32, 0), ok_res.diagnostics.warning_count);

        const missing_alpha_src =
            "pub enum Mode { Alpha, Beta(i32) }\n" ++
            "pub fn eval_missing(mode: Mode) -> i32 {\n" ++
            "    return match mode {\n" ++
            "        .Beta(val) => val,\n" ++
            "    };\n" ++
            "}\n";

        var err_res = try runFullTypecheck(std.testing.allocator, missing_alpha_src);
        defer err_res.deinit();
        try std.testing.expect(hasDiag(&err_res.diagnostics, .e0415_non_exhaustive_match));
        try std.testing.expect(std.mem.indexOf(u8, err_res.diagnostics.diagnostics.items[0].message, ".Alpha") != null);
        try std.testing.expect(std.mem.indexOf(u8, err_res.diagnostics.diagnostics.items[0].message, ".Self") == null);
    }
}

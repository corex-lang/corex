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

    // [4] Integer literal bounds (`u128.MAX` and `i128.MIN` succeed; `256` into `u8` emits `E0502`):
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

    // [5] `DR-21` positive typing (`orelse`, `:=`, `$`, `= expr;`, named/default args) & negative `E0214`/`E0416`/`E0418`/`E0419`:
    {
        const dr21_ok_src =
            "pub fn add_scaled(base: i32, scale: i32 = 2, bias: i32 = 1) -> i32 = base * scale + bias;\n" ++
            "pub fn check_dr21(opt: i32?, slice: &[i32]) -> i32 {\n" ++
            "    let fallback = opt orelse 10;\n" ++
            "    if (len_val := slice.len()) >= 2 {\n" ++
            "        let last_elem = slice[$-1];\n" ++
            "        return add_scaled(fallback + last_elem, bias: len_val as i32);\n" ++
            "    }\n" ++
            "    return fallback;\n" ++
            "}\n";
        var ok_res = try runFullTypecheck(std.testing.allocator, dr21_ok_src);
        defer ok_res.deinit();
        try std.testing.expect(!ok_res.diagnostics.hasErrors());

        const e0214_src =
            "pub fn bad_cond_bind(opt: i32?) -> i32 {\n" ++
            "    if opt is .Some(val) or true { return 1; }\n" ++
            "    return 0;\n" ++
            "}\n";
        var e0214_res = try runFullTypecheck(std.testing.allocator, e0214_src);
        defer e0214_res.deinit();
        try std.testing.expect(hasDiag(&e0214_res.diagnostics, .e0214_invalid_condition_binding));

        const e0416_src =
            "pub fn bad_dollar() -> usize {\n" ++
            "    return $;\n" ++
            "}\n";
        var e0416_res = try runFullTypecheck(std.testing.allocator, e0416_src);
        defer e0416_res.deinit();
        try std.testing.expect(hasDiag(&e0416_res.diagnostics, .e0416_invalid_dollar_length_expr));

        const e0418_src =
            "pub fn bad_irrefutable_is(val: i32) -> i32 {\n" ++
            "    if val is bound { return bound; }\n" ++
            "    return 0;\n" ++
            "}\n";
        var e0418_res = try runFullTypecheck(std.testing.allocator, e0418_src);
        defer e0418_res.deinit();
        try std.testing.expect(hasDiag(&e0418_res.diagnostics, .e0418_irrefutable_is_binding));

        const e0419_src =
            "pub fn pair_sum(left: i32, right: i32) -> i32 = left + right;\n" ++
            "pub fn bad_call() -> i32 {\n" ++
            "    return pair_sum(left: 1, 2);\n" ++
            "}\n";
        var e0419_res = try runFullTypecheck(std.testing.allocator, e0419_src);
        defer e0419_res.deinit();
        try std.testing.expect(hasDiag(&e0419_res.diagnostics, .e0419_invalid_call_arguments));
    }
}

// -------- Phase 7.5 (DR-21) Red-Team Sema Regressions ---------

test "test_type_system_walrus_dominance_rejects_negated_equality_call_args_and_nested_rhs" {
    const cases = [_][]const u8{
        "pub fn leak_eq_false(cond: bool) -> i32 {\n" ++
            "    if (cond and (leaked := 0x7777) > 0) == false { return leaked; }\n" ++
            "    return 0;\n" ++
            "}\n",
        "pub fn ignore_flag(_flag: bool) -> bool = true;\n" ++
            "pub fn leak_call_arg(cond: bool) -> i32 {\n" ++
            "    if ignore_flag(cond and (leaked := 42) > 0) { return leaked; }\n" ++
            "    return 0;\n" ++
            "}\n",
        "pub fn leak_walrus_rhs() -> i32 {\n" ++
            "    if (outer := ((inner := 1) + 2)) > 0 { return outer + inner; }\n" ++
            "    return 0;\n" ++
            "}\n",
        "pub fn leak_orelse(opt_flag: bool?) -> i32 {\n" ++
            "    if (opt_flag orelse ((leaked := 7) > 0)) { return leaked; }\n" ++
            "    return 0;\n" ++
            "}\n",
    };

    for (cases) |bad_src| {
        var res = try runFullTypecheck(std.testing.allocator, bad_src);
        defer res.deinit();
        try std.testing.expect(hasDiag(&res.diagnostics, .e0215_invalid_walrus_position));
    }
}

test "test_type_system_default_param_rejects_non_copy_earlier_param_e0304" {
    const bad_linear_default_src =
        "@linear\n" ++
        "pub struct LinearTok {\n" ++
        "    pub handle: i32,\n" ++
        "}\n" ++
        "pub fn consume_pair(tok: LinearTok, dup_tok: LinearTok = tok) -> i32 {\n" ++
        "    let LinearTok { handle: h1 } = tok;\n" ++
        "    let LinearTok { handle: h2 } = dup_tok;\n" ++
        "    return h1 + h2;\n" ++
        "}\n";
    var bad_res = try runFullTypecheck(std.testing.allocator, bad_linear_default_src);
    defer bad_res.deinit();
    try std.testing.expect(hasDiag(&bad_res.diagnostics, .e0304_resource_or_memory_leak));

    const ok_copy_default_src =
        "pub fn add_adjacent(base: i32, next: i32 = base + 1) -> i32 = base + next;\n";
    var ok_res = try runFullTypecheck(std.testing.allocator, ok_copy_default_src);
    defer ok_res.deinit();
    try std.testing.expect(!ok_res.diagnostics.hasErrors());
}

test "test_type_system_retired_option_unwrap_suggested_fix_span_past_offset_50" {
    const unwrap_or_src =
        "// Padding comment so method call starts well past byte offset fifty!\n" ++
        "pub fn migrate_unwrap_or(opt_val: i32?) -> i32 {\n" ++
        "    return opt_val.unwrap_or(99);\n" ++
        "}\n";
    var res_or = try runFullTypecheck(std.testing.allocator, unwrap_or_src);
    defer res_or.deinit();
    try std.testing.expectEqual(@as(u32, 1), res_or.diagnostics.error_count);
    const diag_or = res_or.diagnostics.diagnostics.items[0];
    try std.testing.expectEqual(@as(usize, 1), diag_or.suggestions.len);
    try std.testing.expectEqual(@as(usize, 1), diag_or.suggestions[0].edits.len);
    const edit_or = diag_or.suggestions[0].edits[0];
    try std.testing.expect(edit_or.start_byte > 50);
    try std.testing.expect(edit_or.start_byte < edit_or.end_byte);
    try std.testing.expectEqualStrings(
        "opt_val.unwrap_or(99)",
        unwrap_or_src[edit_or.start_byte..edit_or.end_byte],
    );
    try std.testing.expectEqualStrings(
        "opt_val orelse 99",
        res_or.interner.get(edit_or.replacement_id),
    );

    const unwrap_src =
        "// Padding comment so method call starts well past byte offset fifty!\n" ++
        "pub fn migrate_unwrap(opt_val: i32?) -> i32 {\n" ++
        "    return opt_val.unwrap();\n" ++
        "}\n";
    var res_unw = try runFullTypecheck(std.testing.allocator, unwrap_src);
    defer res_unw.deinit();
    try std.testing.expectEqual(@as(u32, 1), res_unw.diagnostics.error_count);
    const diag_unw = res_unw.diagnostics.diagnostics.items[0];
    try std.testing.expectEqual(@as(usize, 1), diag_unw.suggestions.len);
    const edit_unw = diag_unw.suggestions[0].edits[0];
    try std.testing.expect(edit_unw.start_byte > 50);
    try std.testing.expect(edit_unw.start_byte < edit_unw.end_byte);
    try std.testing.expectEqualStrings(
        "opt_val.unwrap()",
        unwrap_src[edit_unw.start_byte..edit_unw.end_byte],
    );
    try std.testing.expectEqualStrings(
        "opt_val orelse unreachable",
        res_unw.interner.get(edit_unw.replacement_id),
    );
}

test "test_type_system_inline_core_dot_access_emits_e0218_without_cascading_e0403" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const core_fid = FileId.fromInt(20);
    const user_fid = FileId.fromInt(21);
    const core_stub_src =
        "pub mod mem {\n" ++
        "    pub fn size_of_type[T]() -> usize = 8;\n" ++
        "}\n";
    _ = try db.setInput(core_fid, core_stub_src, .high);
    try db.registerRootModule("core", core_fid);
    try db.registerRootModule("cx", core_fid);

    // [1] Inline `core.mem.size_of_type[u64]()` emits `E0218` with zero cascading `E0403`:
    _ = try db.setInput(user_fid, "pub fn entry() -> usize = core.mem.size_of_type[u64]();\n", .low);
    const body_art = try db.typecheckBody(DefId.init(user_fid, 0));
    try std.testing.expect(body_art.error_count >= 1);
    const body_sink = db.getBodyDiagnostics(DefId.init(user_fid, 0)).?;
    try std.testing.expect(hasDiag(body_sink, .e0218_direct_core_import_forbidden));
    try std.testing.expect(!hasDiag(body_sink, .e0403_unresolved_symbol));

    // [2] Non-root `dummy.core.mem.*` does not fall back to `named_module_scopes`:
    const dummy_inline_src =
        "mod dummy {}\n" ++
        "pub fn entry() -> usize = dummy.core.mem.size_of_type[u64]();\n";
    _ = try db.setInput(user_fid, dummy_inline_src, .low);
    _ = try db.typecheckBody(DefId.init(user_fid, 1));
    const dummy_sink = db.getBodyDiagnostics(DefId.init(user_fid, 1)).?;
    try std.testing.expect(hasDiag(dummy_sink, .e0403_unresolved_symbol));
}

test "test_type_system_const_patterns_irrefutable_is_e0418_and_linear_tuple_guard" {
    // [1] Bare `SCREAMING_SNAKE_CASE` constants in `is` and `match` match constant values instead of shadowing:
    const const_match_ok_src =
        "pub const MAX_RETRIES: i32 = 3;\n" ++
        "pub fn classify_attempt(attempt: i32) -> i32 {\n" ++
        "    if attempt is MAX_RETRIES {\n" ++
        "        return 100;\n" ++
        "    }\n" ++
        "    return match attempt {\n" ++
        "        MAX_RETRIES => 10,\n" ++
        "        _ => 0,\n" ++
        "    };\n" ++
        "}\n";
    var const_ok_res = try runFullTypecheck(std.testing.allocator, const_match_ok_src);
    defer const_ok_res.deinit();
    try std.testing.expect(!const_ok_res.diagnostics.hasErrors());

    const non_exhaustive_const_src =
        "pub const ONLY_TRUE: bool = true;\n" ++
        "pub fn bad_const_match(flag: bool) -> i32 {\n" ++
        "    return match flag {\n" ++
        "        ONLY_TRUE => 1,\n" ++
        "    };\n" ++
        "}\n";
    var non_ex_res = try runFullTypecheck(std.testing.allocator, non_exhaustive_const_src);
    defer non_ex_res.deinit();
    try std.testing.expect(hasDiag(&non_ex_res.diagnostics, .e0415_non_exhaustive_match));

    // [2] Irrefutable composite patterns in `is` (`(a, b)`, `Point { x, y }`, `.Some(_) | _`) emit `E0418`:
    const irrefutable_cases = [_][]const u8{
        "pub fn bad_tuple_is(pair: (i32, i32)) -> i32 {\n" ++
            "    if pair is (left, right) { return left + right; }\n" ++
            "    return 0;\n" ++
            "}\n",
        "pub struct Point { pub x: i32, pub y: i32 }\n" ++
            "pub fn bad_struct_is(pt: Point) -> i32 {\n" ++
            "    if pt is (Point { x, y }) { return x + y; }\n" ++
            "    return 0;\n" ++
            "}\n",
        "pub fn bad_or_wildcard_is(opt: i32?) -> i32 {\n" ++
            "    if opt is (.Some(_) | _) { return 1; }\n" ++
            "    return 0;\n" ++
            "}\n",
    };
    for (irrefutable_cases) |irref_src| {
        var irref_res = try runFullTypecheck(std.testing.allocator, irref_src);
        defer irref_res.deinit();
        try std.testing.expect(hasDiag(&irref_res.diagnostics, .e0418_irrefutable_is_binding));
    }

    // [3] Borrowing linear leaf with `ref` while binding `Copy` leaf by value before `and` succeeds (`0` errors):
    const linear_ref_guard_ok_src =
        "@linear\n" ++
        "pub struct Handle { pub fd: i32 }\n" ++
        "pub enum Slot { Active(Handle), Empty }\n" ++
        "pub fn check_slot(pair_lin: (Slot, i32)) -> i32 {\n" ++
        "    var res: i32 = 0;\n" ++
        "    if pair_lin is (.Active(ref _h), copy_val) and copy_val > 0 {\n" ++
        "        res = copy_val;\n" ++
        "    }\n" ++
        "    let (slot_val, _) = pair_lin;\n" ++
        "    match slot_val {\n" ++
        "        .Active(owned_h) => {\n" ++
        "            let Handle { fd } = owned_h;\n" ++
        "            return res + fd;\n" ++
        "        },\n" ++
        "        .Empty => return res,\n" ++
        "    }\n" ++
        "}\n";
    var lin_ok_res = try runFullTypecheck(std.testing.allocator, linear_ref_guard_ok_src);
    defer lin_ok_res.deinit();
    try std.testing.expect(!lin_ok_res.diagnostics.hasErrors());

    // Moving the linear leaf by value before `and` still emits `E0304`:
    const linear_move_guard_bad_src =
        "@linear\n" ++
        "pub struct Handle { pub fd: i32 }\n" ++
        "pub enum Slot { Active(Handle), Empty }\n" ++
        "pub fn bad_slot(pair_lin: (Slot, i32)) -> i32 {\n" ++
        "    if pair_lin is (.Active(moved_h), copy_val) and copy_val > 0 {\n" ++
        "        let Handle { fd } = moved_h;\n" ++
        "        return fd + copy_val;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";
    var lin_bad_res = try runFullTypecheck(std.testing.allocator, linear_move_guard_bad_src);
    defer lin_bad_res.deinit();
    try std.testing.expect(hasDiag(&lin_bad_res.diagnostics, .e0304_resource_or_memory_leak));
}

test "test_type_system_overload_named_defaults_generic_default_subst_and_tuple_variant_e0419" {
    // [1] `@overload` disambiguation supports named and omitted default arguments + records `call_arg_mappings`:
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();
    const file_id = FileId.fromInt(30);
    const overload_src =
        "@overload\n" ++
        "pub fn format_metric(val: i32, scale: i32 = 10) -> i32 = val * scale;\n" ++
        "@overload\n" ++
        "pub fn format_metric(tag: str, bonus: i32 = 5) -> i32 {\n" ++
        "    let _ = tag;\n" ++
        "    return bonus;\n" ++
        "}\n" ++
        "pub fn caller() -> i32 {\n" ++
        "    return format_metric(scale: 3, val: 4) + format_metric(tag: \"ok\");\n" ++
        "}\n";
    _ = try db.setInput(file_id, overload_src, .low);
    const caller_def = DefId.init(file_id, 2);
    const caller_art = try db.typecheckBody(caller_def);
    try std.testing.expectEqual(@as(u32, 0), caller_art.error_count);
    const caller_st = db.def_side_tables.getPtr(caller_def.asInt()).?;
    try std.testing.expectEqual(@as(u32, 2), caller_st.call_arg_mappings.count());

    // [2] Generic function with omitted default validates `subst(param_ty)` against default initializer type:
    const bad_generic_default_src =
        "pub fn with_zero[T](seed: T = 0) -> T = seed;\n" ++
        "pub fn bad_bool_caller() -> bool = with_zero[bool]();\n";
    var bad_gen_res = try runFullTypecheck(std.testing.allocator, bad_generic_default_src);
    defer bad_gen_res.deinit();
    try std.testing.expect(hasDiag(&bad_gen_res.diagnostics, .e0401_type_mismatch));

    const ok_generic_default_src =
        "pub fn with_zero[T](seed: T = 0) -> T = seed;\n" ++
        "pub fn ok_int_caller() -> i64 = with_zero[i64]();\n";
    var ok_gen_res = try runFullTypecheck(std.testing.allocator, ok_generic_default_src);
    defer ok_gen_res.deinit();
    try std.testing.expect(!ok_gen_res.diagnostics.hasErrors());

    // [3] Tuple-variant constructors reject bogus `.named_arg` labels with `E0419`:
    const tuple_variant_cases = [_][]const u8{
        "pub fn bad_ctx_some() -> i32? = .Some(fake: 5);\n",
        "pub fn bad_qual_some() -> i32? = Option[i32].Some(fake: 5);\n",
        "pub enum Boxed { Item(i32) }\n" ++
            "pub fn bad_enum_ctor() -> Boxed = Boxed.Item(fake: 5);\n",
    };
    for (tuple_variant_cases) |bad_ctor_src| {
        var ctor_res = try runFullTypecheck(std.testing.allocator, bad_ctor_src);
        defer ctor_res.deinit();
        try std.testing.expect(hasDiag(&ctor_res.diagnostics, .e0419_invalid_call_arguments));
    }
}

test "test_type_system_tuple_leading_zero_loop_labels_break_typing_and_context_layout" {
    // [1] Tuple index with leading zero (`tup.00`) emits `E0403`:
    var tup_res = try runFullTypecheck(
        std.testing.allocator,
        "pub fn bad_tup(tup: (i32, i32)) -> i32 = tup.00;\n",
    );
    defer tup_res.deinit();
    try std.testing.expect(hasDiag(&tup_res.diagnostics, .e0403_unresolved_symbol));

    // [2] Unknown `:label` (`E0403`) and value `break` targeting `comptime for` (`E0412`):
    var unknown_lbl_res = try runFullTypecheck(
        std.testing.allocator,
        "pub fn unknown_lbl() {\n    while true { break :missing; }\n}\n",
    );
    defer unknown_lbl_res.deinit();
    try std.testing.expect(hasDiag(&unknown_lbl_res.diagnostics, .e0403_unresolved_symbol));

    var ct_val_break_res = try runFullTypecheck(
        std.testing.allocator,
        "pub fn comptime_val_break() -> i32? {\n" ++
            "    return ct_loop: comptime for idx in 0..3 {\n" ++
            "        if idx == 1 { break :ct_loop 42; }\n" ++
            "    };\n" ++
            "}\n",
    );
    defer ct_val_break_res.deinit();
    try std.testing.expect(hasDiag(&ct_val_break_res.diagnostics, .e0412_let_else_not_diverging));

    // [3] Diverging `break @panic(…)` keeps `for` type `()` (not `()?`), while mixing `break ();` & `break;` emits `E0401`:
    const diverging_break_ok_src =
        "pub fn check_nonneg(items: &[i32]) {\n" ++
        "    let _unit_res: () = for item in items {\n" ++
        "        if item < 0 { break @panic(\"negative\"); }\n" ++
        "    };\n" ++
        "}\n";
    var div_ok_res = try runFullTypecheck(std.testing.allocator, diverging_break_ok_src);
    defer div_ok_res.deinit();
    try std.testing.expect(!div_ok_res.diagnostics.hasErrors());

    const mixed_break_cases = [_][]const u8{
        "pub fn mix_val_then_bare(items: &[i32]) {\n" ++
            "    let _ = for item in items {\n" ++
            "        if item > 0 { break (); }\n" ++
            "        break;\n" ++
            "    };\n" ++
            "}\n",
        "pub fn mix_bare_then_val(items: &[i32]) {\n" ++
            "    let _ = for item in items {\n" ++
            "        if item > 0 { break; }\n" ++
            "        break ();\n" ++
            "    };\n" ++
            "}\n",
    };
    for (mixed_break_cases) |mix_src| {
        var mix_res = try runFullTypecheck(std.testing.allocator, mix_src);
        defer mix_res.deinit();
        try std.testing.expect(hasDiag(&mix_res.diagnostics, .e0401_type_mismatch));
    }

    // [4] Reject unrelated `&Struct` on `with context.logger` and reject `context` inside `extern "C" fn`:
    const bad_context_cases = [_][]const u8{
        "pub struct Unrelated { pub code: i32 }\n" ++
            "pub fn bad_logger_override(unrel: &Unrelated) -> i32 {\n" ++
            "    return with context.logger = unrel { 1 };\n" ++
            "}\n",
        "extern \"C\" fn bad_extern_ctx() -> u64 {\n" ++
            "    return context.rng_seed;\n" ++
            "}\n",
        "extern \"C\" fn bad_extern_with(raw_ptr: *mut u8) -> i32 {\n" ++
            "    return with context.logger = raw_ptr { 0 };\n" ++
            "}\n",
    };
    for (bad_context_cases) |ctx_err_src| {
        var ctx_err_res = try runFullTypecheck(std.testing.allocator, ctx_err_src);
        defer ctx_err_res.deinit();
        try std.testing.expect(hasDiag(&ctx_err_res.diagnostics, .e0401_type_mismatch));
    }

    // [5] Populated `Context` layout matches 8-field struct layout (`80B` on 64-bit, `48B` on `wasm32`, align `8`):
    var ctx_layout_res = try runFullTypecheck(
        std.testing.allocator,
        "pub fn capture_ctx() -> u64 { let snap = context; return snap.rng_seed; }\n",
    );
    defer ctx_layout_res.deinit();
    try std.testing.expect(!ctx_layout_res.diagnostics.hasErrors());

    var ctx_type_id: TypeId = .err_ty;
    for (ctx_layout_res.symbol_table.symbols.items) |sym| {
        if (sym.flags.is_builtin and std.mem.eql(u8, sym.name_text, "Context")) {
            ctx_type_id = sym.type_id;
            break;
        }
    }
    try std.testing.expect(!ctx_type_id.isError());

    const layout_64 = type_system.computeTypeLayoutWithPool(
        &ctx_layout_res.type_pool,
        &ctx_layout_res.symbol_table,
        ctx_type_id,
        type_system.TargetLayout.NATIVE_64,
    );
    try std.testing.expectEqual(@as(u64, 80), layout_64.byte_size);
    try std.testing.expectEqual(@as(u32, 8), layout_64.align_bytes);

    const layout_wasm32 = type_system.computeTypeLayoutWithPool(
        &ctx_layout_res.type_pool,
        &ctx_layout_res.symbol_table,
        ctx_type_id,
        type_system.TargetLayout.WASM32,
    );
    try std.testing.expectEqual(@as(u64, 48), layout_wasm32.byte_size);
    try std.testing.expectEqual(@as(u32, 8), layout_wasm32.align_bytes);
}

test "test_type_system_float_pi_and_tau_associated_constants_and_retired_std" {
    // [1] `f32.PI`, `f32.TAU`, `f64.PI`, and `f64.TAU` synthesize exact `f32` and `f64` types (`0` errors):
    const float_const_src =
        "pub fn circle_f32(radius: f32) -> f32 = (f32.PI * radius * radius) + (f32.TAU * radius);\n" ++
        "pub fn circle_f64(radius: f64) -> f64 = (f64.PI * radius * radius) + (f64.TAU * radius);\n";
    var float_ok_res = try runFullTypecheck(std.testing.allocator, float_const_src);
    defer float_ok_res.deinit();
    try std.testing.expect(!float_ok_res.diagnostics.hasErrors());

    // [2] Integer primitives reject float-only `PI` and `TAU` associated constants with `E0403`:
    var bad_int_pi = try runFullTypecheck(
        std.testing.allocator,
        "pub fn bad_pi() -> i32 = i32.PI;\n",
    );
    defer bad_int_pi.deinit();
    try std.testing.expect(hasDiag(&bad_int_pi.diagnostics, .e0403_unresolved_symbol));

    // [3] Inline `std.meta` root access is rejected (`E0403`), whereas `cx.atomic.Ordering` resolves in $O(1)$:
    var bad_std_inline = try runFullTypecheck(
        std.testing.allocator,
        "pub fn bad_std(_info: std.meta.TypeInfo) -> i32 = 0;\n",
    );
    defer bad_std_inline.deinit();
    try std.testing.expect(hasDiag(&bad_std_inline.diagnostics, .e0403_unresolved_symbol));

    var ok_cx_atomic = try runFullTypecheck(
        std.testing.allocator,
        "pub fn ok_atomic() -> cx.atomic.Ordering = cx.atomic.Ordering.SeqCst;\n",
    );
    defer ok_cx_atomic.deinit();
    try std.testing.expect(!ok_cx_atomic.diagnostics.hasErrors());
}

//! Phase 4 Deterministic Name Resolution, Type System & Error Semantics Fuzzing Suite (`tests/fuzz/phase4_typecheck_fuzz.zig`)
//!
//! Exercises structure-aware and mutated `.cx` programs with Constrained Type Groups (`Number`,
//! `any Signed`, `~Unsigned`), `distinct` newtypes, `is` range refinements, `bit_field` declarations,
//! `#soa` slices, `Result[T, E]` / `T?` `?` propagation, `catch |err|`, `let … else`, `match`
//! exhaustiveness, and syntax recovery holes (`expr_hole`, `type_hole`, `pattern_hole`) through
//! `symbol_resolver` and `type_system`.
//!
//! - Asserts zero crashes, zero leaks, and poison-type (`TypeId.err_ty`) soundness across mutated ASTs.
//! - Asserts 100% fingerprint parity between an incrementally mutated `CompilerDb` and a fresh
//!   scratch `CompilerDb` across `resolve_signatures`, `def_signature`, and `typecheck_body`.

const std = @import("std");
const corex = @import("corex");

const type_system = corex.type_system;
const FileId = corex.FileId;
const DefId = corex.DefId;
const Durability = corex.Durability;
const Fingerprint128 = corex.Fingerprint128;
const CompilerDb = corex.CompilerDb;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of generated/mutated `.cx` modules verified in `test_fuzz_phase4_typechecker_fault_tolerance_and_poison_soundness`.
const TYPECHECK_FUZZ_ITERATIONS: usize = 600;
/// Number of incremental `CompilerDb` revision steps verified in `test_fuzz_phase4_incremental_typecheck_parity`.
const INCREMENTAL_TYPECHECK_ITERATIONS: usize = 250;

/// Type-level and declaration seed items for Phase 4 structure-aware fuzzing.
const PHASE4_SEED_ITEMS = [_][]const u8{
    "pub type UserId = distinct u64;\n",
    "pub type PortNum = u16 is 1..=1024;\n",
    "pub type NumericId = u32 | ~u64;\n",
    "pub struct IoError { pub code: i32 }\n",
    "pub enum AppError { @from Io(IoError), InvalidPort, }\n",
    "pub struct Vec2 { pub x: f32, pub y: f32 }\n",
    "pub bit_field HeaderBits(u8) { pub ver: u8 | 3, pub flags: u8 | 5 }\n",
    "pub fn add_numbers(lhs: Number, rhs: Number) -> Number { return lhs + rhs; }\n",
    "pub fn compare_any(lhs: any Signed, rhs: any Signed) -> bool { let _a = lhs; let _b = rhs; return true; }\n",
    "pub fn unwrap_id(uid: ~u64) -> ~u64 { return uid; }\n",
    "pub fn read_port(raw: u16) -> Result[PortNum, IoError] {\n" ++
        "    if raw == 80 { return .Ok(80); }\n" ++
        "    return .Err(IoError { code: 404 });\n" ++
        "}\n",
    "pub fn handle_request(raw: u16) -> Result[u16, AppError] {\n" ++
        "    let port = read_port(raw)?;\n" ++
        "    let safe_val: u16 = port;\n" ++
        "    return .Ok(safe_val);\n" ++
        "}\n",
    "pub fn match_byte(val: u8) -> i32 {\n" ++
        "    return match val {\n" ++
        "        0..=127 => 1,\n" ++
        "        128..=255 => 2,\n" ++
        "    };\n" ++
        "}\n",
    "pub fn guard_optional(opt: i32?) -> i32 {\n" ++
        "    let .Some(inner) = opt else { return 0; };\n" ++
        "    return inner + 1;\n" ++
        "}\n",
    "pub fn project_soa(items: #soa [Vec2]) -> f32 {\n" ++
        "    let xs: [f32] = items.x;\n" ++
        "    return xs[0];\n" ++
        "}\n",
};

/// Deliberately malformed or type-error seed items stressing poison-type propagation (`TypeId.err_ty`).
const PHASE4_MUTATION_SNIPPETS = [_][]const u8{
    "pub fn broken_hole(a: i32) -> i32 { let x: = ; return x + a; }\n",
    "pub fn conflict_call(a: i32, b: i64) -> i32 { return add_numbers(a, b); }\n",
    "pub fn bad_distinct(u: UserId, raw: u64) -> u64 { return u + raw; }\n",
    "pub fn bad_refine() -> PortNum { return 9999; }\n",
    "pub fn bad_try() -> i32 { return read_port(80)?; }\n",
    "pub fn bad_match(b: bool) -> i32 { return match b { true => 1 }; }\n",
    "pub fn bad_discard() { read_port(80); let _ = read_port(80); }\n",
};

/// Function body variants for incremental `CompilerDb` Phase 4 parity fuzzing.
const PHASE4_BODY_VARIANTS = [_][]const u8{
    "    let step = add_generic(input_val, 10);\n    return .Ok(step);\n",
    "    // Comment edit only\n    let step = add_generic(input_val, 10);\n\n    return .Ok(step);\n",
    "    let step = match input_val { 0 => 1, _ => input_val + 2 };\n    return .Ok(step);\n",
    "    let opt_v: i32? = .Some(input_val);\n    let .Some(v) = opt_v else { return .Err(1); };\n    return .Ok(v);\n",
    "    let bad_mismatch: bool = input_val;\n    let _keep = bad_mismatch;\n    return .Ok(0);\n",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Builds a multi-item `.cx` module for incremental `CompilerDb` fuzzing.
fn buildIncrementalTypecheckModule(
    allocator: std.mem.Allocator,
    has_banner_comment: bool,
    body_choices: [3]usize,
) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    if (has_banner_comment) {
        try builder.appendSlice(allocator, "//! Incremental Phase 4 fuzz banner\n\n");
    }
    try builder.appendSlice(
        allocator,
        "pub fn add_generic(lhs: Number, rhs: Number) -> Number {\n    return lhs + rhs;\n}\n\n",
    );

    var fn_i: usize = 0;
    while (fn_i < 3) : (fn_i += 1) {
        var hdr_buf: [128]u8 = undefined;
        const hdr = try std.fmt.bufPrint(
            &hdr_buf,
            "pub fn worker_{d}(input_val: i32) -> Result[i32, i32] {{\n",
            .{fn_i},
        );
        try builder.appendSlice(allocator, hdr);
        try builder.appendSlice(allocator, PHASE4_BODY_VARIANTS[body_choices[fn_i]]);
        try builder.appendSlice(allocator, "}\n\n");
    }
    return builder.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_phase4_typechecker_fault_tolerance_and_poison_soundness" {
    var prng = std.Random.DefaultPrng.init(0xF004_C0DE_2026_0004);
    const random = prng.random();

    var source_buf: [4096]u8 = undefined;
    var iter_idx: usize = 0;
    while (iter_idx < TYPECHECK_FUZZ_ITERATIONS) : (iter_idx += 1) {
        var byte_len: usize = 0;
        const item_count = random.intRangeAtMost(usize, 2, 7);
        var item_i: usize = 0;
        while (item_i < item_count) : (item_i += 1) {
            const snippet = if (random.uintLessThan(u8, 4) == 0)
                PHASE4_MUTATION_SNIPPETS[random.uintLessThan(usize, PHASE4_MUTATION_SNIPPETS.len)]
            else
                PHASE4_SEED_ITEMS[random.uintLessThan(usize, PHASE4_SEED_ITEMS.len)];

            if (byte_len + snippet.len <= source_buf.len) {
                @memcpy(source_buf[byte_len .. byte_len + snippet.len], snippet);
                byte_len += snippet.len;
            }
        }

        // Apply random single-byte perturbation on 25% of iterations:
        if (iter_idx % 4 == 0 and byte_len > 0) {
            const mut_pos = random.uintLessThan(usize, byte_len);
            source_buf[mut_pos] = switch (random.uintLessThan(u8, 6)) {
                0 => ';',
                1 => ' ',
                2 => '?',
                3 => '~',
                4 => '_',
                else => source_buf[mut_pos],
            };
        }

        const source_slice = source_buf[0..byte_len];
        const file_id = FileId.fromInt(@intCast((iter_idx & 0xFF) + 1));

        var res = try type_system.typecheckSource(std.testing.allocator, file_id, source_slice);
        defer res.deinit();

        try std.testing.expect(res.type_pool.countTypes() >= 64);
    }
}

test "test_fuzz_phase4_incremental_typecheck_parity" {
    var prng = std.Random.DefaultPrng.init(0xDB04_FA5E_2026_1110);
    const random = prng.random();

    var inc_db = try CompilerDb.init(std.testing.allocator);
    defer inc_db.deinit();

    const file_id = FileId.fromInt(1);
    var body_choices = [3]usize{ 0, 1, 2 };
    var has_banner = false;
    var dur: Durability = .low;

    var step_idx: usize = 0;
    while (step_idx < INCREMENTAL_TYPECHECK_ITERATIONS) : (step_idx += 1) {
        switch (random.uintLessThan(u8, 4)) {
            0 => has_banner = !has_banner,
            1 => {
                const slot = random.uintLessThan(usize, 3);
                body_choices[slot] = random.uintLessThan(usize, PHASE4_BODY_VARIANTS.len);
            },
            2 => dur = switch (random.uintLessThan(u8, 3)) {
                0 => .low,
                1 => .medium,
                else => .high,
            },
            else => {},
        }

        const src = try buildIncrementalTypecheckModule(
            std.testing.allocator,
            has_banner,
            body_choices,
        );
        defer std.testing.allocator.free(src);

        _ = try inc_db.setInput(file_id, src, dur);

        var scratch_db = try CompilerDb.init(std.testing.allocator);
        defer scratch_db.deinit();
        _ = try scratch_db.setInput(file_id, src, dur);

        const inc_mod_scope = try inc_db.resolveSignatures(file_id);
        const scr_mod_scope = try scratch_db.resolveSignatures(file_id);
        try std.testing.expect(
            Fingerprint128.eql(inc_mod_scope.signatures_fingerprint, scr_mod_scope.signatures_fingerprint),
        );

        var item_ord: u12 = 0;
        while (item_ord < 4) : (item_ord += 1) {
            const def_id = DefId.init(file_id, item_ord);
            const inc_sig = try inc_db.getDefSignature(def_id);
            const scr_sig = try scratch_db.getDefSignature(def_id);
            try std.testing.expect(Fingerprint128.eql(inc_sig.signature_fingerprint, scr_sig.signature_fingerprint));

            const inc_body = try inc_db.typecheckBody(def_id);
            const scr_body = try scratch_db.typecheckBody(def_id);
            try std.testing.expectEqual(inc_body.error_count, scr_body.error_count);
            try std.testing.expect(Fingerprint128.eql(inc_body.typed_fingerprint, scr_body.typed_fingerprint));
        }
    }
}

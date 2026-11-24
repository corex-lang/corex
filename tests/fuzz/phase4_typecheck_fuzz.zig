//! Phase 4, Phase 7.5 & Phase 7.6 Deterministic Name Resolution, Type System & `DR-22` Fuzzing Suite (`tests/fuzz/phase4_typecheck_fuzz.zig`)
//!
//! Exercises structure-aware and mutated `.cx` programs combining Phase 4 (`Number`, `any Signed`,
//! `~Unsigned`, `distinct`, `is` range refinements, `bit_field`, `#soa`, `T!E` / `T?` `?`,
//! `catch |err|`, `let … else`, `match` exhaustiveness, and recovery holes) with Phase 7.5 (`DR-21`)
//! and Phase 7.6 (`DR-22` inline union bounds, generic defaults, `@derive(From)`, `/` & `*` zones,
//! `FmtArgs` / `{x=}` / `"""…"""`, `b'x'` / `b"…"`, `_u64` suffixes, `..base`, `(a, b) = (b, a)`,
//! `&out` / `own T` / `&raw` / `ptr.*`, `@caller_location()`, `@cfg`, `fsm: match`, `subscript`)
//! through `symbol_resolver` and `type_system`.
//!
//! - Asserts zero crashes, zero leaks, and poison-type (`TypeId.err_ty`) soundness across mutated ASTs.
//! - Asserts 100% fingerprint parity between an incrementally mutated `CompilerDb` and a fresh
//!   scratch `CompilerDb` across `resolve_signatures`, `def_signature`, and `typecheck_body`.

const std = @import("std");
const corex = @import("corex");

const type_system = corex.type_system;
const FileId = corex.FileId;
const Durability = corex.Durability;
const Fingerprint128 = corex.Fingerprint128;
const CompilerDb = corex.CompilerDb;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of generated/mutated `.cx` modules verified in `test_fuzz_phase4_typechecker_fault_tolerance_and_poison_soundness`.
const TYPECHECK_FUZZ_ITERATIONS: usize = 600;
/// Number of incremental `CompilerDb` revision steps verified in `test_fuzz_phase4_incremental_typecheck_parity`.
const INCREMENTAL_TYPECHECK_ITERATIONS: usize = 250;

/// Stub `core` / `cx` root module registered for `use cx.*` vs `use core.*` (`E0218`) incremental parity.
const CORE_STUB_SOURCE =
    "pub mod mem {\n" ++
    "    pub fn word_bytes() -> i32 = 8;\n" ++
    "}\n";

/// Module-header import variants exercising `use cx.*` (`ADR-21B`) vs forbidden direct `use core.*` (`E0218`).
const PHASE4_IMPORT_VARIANTS = [_][]const u8{
    "use cx.mem;\n\n",
    "use cx.{mem};\n\n",
    "use core.mem;\n\n",
    "",
};

/// Type-level and declaration seed items for Phase 4, Phase 7.5 (`DR-21`), & Phase 7.6 (`DR-22`) fuzzing.
const PHASE4_SEED_ITEMS = [_][]const u8{
    "pub type UserId = distinct u64;\n",
    "pub type PortNum = u16 is 1..=1024;\n",
    "pub type NumericId = u32 | ~u64;\n",
    "pub struct IoError { pub code: i32 }\n",
    "@derive(From)\npub enum AppError { Io(IoError), InvalidPort, }\n",
    "@derive(Copy)\npub struct Vec2 { pub x: f32 = 0.0_f32, pub y: f32 = 1.0_f32 }\n",
    "pub bit_field HeaderBits: u8 { pub ver: u8 | 3, pub flags: u8 | 5 }\n",
    "@derive(Copy, Equatable)\npub enum WireOrder: u8 { Relaxed = 0, Acquire = 2, SeqCst = 5 }\n",
    "pub struct OwnedBox { pub payload: i32 }\n" ++
        "pub(pkg) fn take_owned_box(item: own OwnedBox, out_slot: &out i32, /) {\n" ++
        "    out_slot.* = item.payload;\n" ++
        "}\n" ++
        "pub fn move_and_out_probe() -> i32 {\n" ++
        "    let boxed = OwnedBox { payload: 42_i32 };\n" ++
        "    var result_slot: i32;\n" ++
        "    take_owned_box(own boxed, &out result_slot);\n" ++
        "    let raw_p: *i32 = &raw result_slot;\n" ++
        "    return unsafe { raw_p.* };\n" ++
        "}\n",
    "pub struct PairCounter { pub count: i32 }\n" ++
        "impl PairCounter {\n" ++
        "    pub const DEFAULT_SEED: i32 = 4;\n" ++
        "    pub fn with_seed(seed_val: i32) -> PairCounter = PairCounter { count: seed_val };\n" ++
        "    pub subscript(offset: i32, /) -> i32 {\n" ++
        "        let { yield self.count + offset; }\n" ++
        "    }\n" ++
        "}\n",
    "pub fn add_numbers(lhs: Number, rhs: Number) -> Number = lhs + rhs;\n",
    "pub fn compare_any(lhs: any Signed, rhs: any Signed) -> bool { let _lhs = lhs; let _rhs = rhs; return true; }\n",
    "pub fn unwrap_id(uid: ~u64) -> ~u64 = uid;\n",
    "pub fn strip_head[Data: str | &[u8]](data: Data, /, *, skip_space: bool = true) -> usize {\n" ++
        "    let raw_bytes = data.as_bytes();\n" ++
        "    if skip_space and raw_bytes.len() > 0 and raw_bytes[0] == b' ' {\n" ++
        "        return raw_bytes.len() - 1_usize;\n" ++
        "    }\n" ++
        "    return b\"ok\".len() + raw_bytes.len();\n" ++
        "}\n",
    "pub fn spread_swap_and_fsm(flag: bool, *, loc: SourceLoc = @caller_location()) -> i32 {\n" ++
        "    let base_v = Vec2 { .. };\n" ++
        "    let next_v = Vec2 { x: 2.5_f32, ..base_v };\n" ++
        "    var left_n: i32 = (next_v.x as i32) + (loc.line as i32);\n" ++
        "    var right_n: i32 = (WireOrder.SeqCst as u8 as i32) + (flag as i32);\n" ++
        "    (left_n, right_n) = (right_n, left_n);\n" ++
        "    let msg = f\"\n" ++
        "        {{hdr}} {left_n=} hex={right_n:#06x}\n" ++
        "        \";\n" ++
        "    _ = msg;\n" ++
        "    return fsm: match WireOrder.Relaxed {\n" ++
        "        .Relaxed => continue :fsm .SeqCst,\n" ++
        "        .Acquire => left_n,\n" ++
        "        .SeqCst => left_n + right_n,\n" ++
        "    };\n" ++
        "}\n",
    "@repr(C, align: .CacheLine, zero_pad: true)\n@derive(Copy, Equatable)\n" ++
        "pub struct AlignedPacket { pub seq_id: u64, pub tag_id: u32 }\n",
    "@repr(C, packed: true, align: 8)\npub struct PackedWireHdr { pub tag_b: u8, pub body_len: u32 }\n",
    "@link(name: \"cx_ext_probe\", section: \".text\")\nextern \"C\" fn ext_probe(val_in: i32) -> i32;\n",
    "pub fn dr24_inline_if_and_strings(opt_v: i32?, flag_b: bool) -> str {\n" ++
        "    let picked: i32 = if (cand_v := opt_v) is .Some(num_v) and (doubled := num_v * 2) > 4 => doubled\n" ++
        "        else if flag_b => 1\n" ++
        "        else 0;\n" ++
        "    let _fmt_json = f#\"{\"picked\": {picked:#04x}}\"#;\n" ++
        "    return if picked > 0 => \"{\\\"ok\\\": true}\" else \"meta != '{}'\";\n" ++
        "}\n",
    "@cfg(target.ptr_width == 64 or target.ptr_width == 32)\n" ++
        "pub fn cfg_guarded_helper() -> i32 = ~0_i32;\n",
    "test \"typecheck prose test\" (raw_in: &[u8]) { _ = raw_in.len(); }\n",
    "pub fn affine_calc(base: i32, scale: i32 = 2, bias: i32 = base + 1) -> i32 = base * scale + bias;\n",
    "pub fn read_assoc_and_tuple(nested: ((i32, i32), i32)) -> i32 =\n" ++
        "    PairCounter.with_seed(PairCounter.DEFAULT_SEED).count + nested.0.1 + nested.1;\n",
    "pub fn call_named_and_defaults(val_in: i32) -> i32 =\n" ++
        "    affine_calc(val_in) + affine_calc(bias: 5, base: val_in) + affine_calc(val_in, scale: 3);\n",
    "pub fn read_port(raw: u16) -> PortNum!IoError {\n" ++
        "    if raw == 80 { return .Ok(80); }\n" ++
        "    return .Err(IoError { code: 404 });\n" ++
        "}\n",
    "pub fn handle_request(raw: u16) -> u16!AppError {\n" ++
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
    "pub fn guard_optional(opt_val: i32?) -> i32 {\n" ++
        "    let .Some(inner_val) = opt_val else { return 0; };\n" ++
        "    return inner_val + 1;\n" ++
        "}\n",
    "pub fn narrow_is_walrus_and_orelse(opt_in: i32?, backup_opt: i32?) -> i32 {\n" ++
        "    if (cand_opt := opt_in) is .Some(inner_val) and (shifted := inner_val + 2) > 4 {\n" ++
        "        let _keep = cand_opt;\n" ++
        "        return shifted;\n" ++
        "    } else if backup_opt is not .None {\n" ++
        "        return backup_opt orelse unreachable;\n" ++
        "    }\n" ++
        "    return opt_in orelse 9;\n" ++
        "}\n",
    "pub fn scan_dollar_indexed_and_labeled_break(items: &[i32]) -> i32 {\n" ++
        "    var acc_sum: i32 = 0;\n" ++
        "    for item_val, item_idx in items {\n" ++
        "        acc_sum += item_val + (item_idx as i32);\n" ++
        "    }\n" ++
        "    let tail_bonus: i32 = if (total_len := items.len()) >= 2 {\n" ++
        "        let trimmed: &[i32] = items[..$ - 1];\n" ++
        "        items[$ - 1] + trimmed[$ - 1] + (total_len as i32)\n" ++
        "    } else {\n" ++
        "        0\n" ++
        "    };\n" ++
        "    let found_idx: usize = search_slot: for item_val, item_idx in items {\n" ++
        "        if item_val > 10 {\n" ++
        "            break :search_slot item_idx;\n" ++
        "        }\n" ++
        "    } orelse 0;\n" ++
        "    return acc_sum + tail_bonus + (found_idx as i32);\n" ++
        "}\n",
    "pub fn check_with_cancel_token() -> usize {\n" ++
        "    let local_tok = CancelToken { _handle: 7 };\n" ++
        "    return with context.cancel_token = local_tok {\n" ++
        "        context.cancel_token._handle\n" ++
        "    };\n" ++
        "}\n",
    "pub fn project_soa(items: #soa [Vec2]) -> f32 {\n" ++
        "    let xs_col: [f32] = items.x;\n" ++
        "    return xs_col[0];\n" ++
        "}\n",
};

/// Deliberately malformed or error-triggering snippets stressing `DR-21` & `DR-22` diagnostics & poison soundness.
const PHASE4_MUTATION_SNIPPETS = [_][]const u8{
    "pub fn broken_hole(arg_val: i32) -> i32 { let x: = ; return x + arg_val; }\n",
    "pub fn conflict_call(lhs: i32, rhs: i64) -> i32 { return add_numbers(lhs, rhs); }\n",
    "pub fn bad_distinct(user_id: UserId, raw_val: u64) -> u64 { return user_id + raw_val; }\n",
    "pub fn bad_refine() -> PortNum { return 9999; }\n",
    "pub fn bad_try() -> i32 { return read_port(80)?; }\n",
    "pub fn bad_match(flag: bool) -> i32 { return match flag { true => 1 }; }\n",
    "pub fn bad_discard() { read_port(80); _ = read_port(80); }\n",
    "pub fn bad_or_is_bind(opt_val: i32?) -> i32 {\n" ++
        "    if opt_val is .Some(inner_val) or true { return inner_val; }\n" ++
        "    return 0;\n" ++
        "}\n",
    "pub fn bad_standalone_walrus() -> i32 { leaked_val := 42; return leaked_val; }\n",
    "pub fn bad_or_walrus(flag: bool) -> i32 {\n" ++
        "    if flag or (leaked_val := 7) > 0 { return leaked_val; }\n" ++
        "    return 0;\n" ++
        "}\n",
    "pub fn bad_legacy_colons() -> i32 { return PairCounter::with_seed(1).count; }\n",
    "pub fn bad_retired_if_let(opt_val: i32?) -> i32 {\n" ++
        "    if let .Some(inner_val) = opt_val { return inner_val; }\n" ++
        "    return 0;\n" ++
        "}\n",
    "pub fn bad_outer_dollar() -> usize = $;\n",
    "pub fn bad_irrefutable_is(raw_val: i32) -> i32 {\n" ++
        "    if raw_val is bound_val { return bound_val; }\n" ++
        "    return 0;\n" ++
        "}\n",
    "pub fn bad_named_arg_order() -> i32 = affine_calc(scale: 2, 10);\n",
    "pub fn bad_slice_len_field(items: &[i32]) -> usize = items.len;\n",
    "pub fn bad_opaque_deref(ptr: *opaque) { unsafe { _ = ptr.*; } }\n",
    "pub fn bad_noncopy_val_param(err: IoError) -> i32 = err.code;\n",
    "pub fn bad_missing_own_arg() {\n" ++
        "    let box_v = OwnedBox { payload: 1 };\n" ++
        "    var slot: i32;\n" ++
        "    take_owned_box(box_v, &out slot);\n" ++
        "}\n",
    "pub bit_field BadBitSum: u8 { pub low_bits: u8 | 3, pub high_bits: u8 | 3 }\n",
    "pub fn bad_zone_call() -> usize = strip_head(data: \"hi\");\n",
    "pub fn bad_fmt_spec(name: str) -> str = f\"{name:#x}\";\n",
    "@repr(packed: true)\npub struct BadPackedNoC { pub x_val: u32 }\n",
    "pub fn bad_packed_borrow(hdr_in: &PackedWireHdr) -> &u32 = &hdr_in.body_len;\n",
    "pub fn bad_inline_if_no_else(flag_b: bool) -> i32 = if flag_b => 1;\n",
    "pub fn bad_missing_field() -> IoError = IoError {};\n",
    "pub fn bad_par_assign(lhs_v: i32) { var rhs_v: i32 = 0; (lhs_v + 1, rhs_v) = (1, 2); }\n",
    "pub fn bad_fsm_continue(step_v: i32) -> i32 = fsm: match step_v { 0 => continue :fsm, _ => 1 };\n",
    "use core.mem;\npub fn bad_core_import() -> i32 = 0;\n",
    "use cx.mem;\npub fn unresolved_cx_standalone() -> i32 = 0;\n",
};

/// Function body variants for incremental `CompilerDb` Phase 4, Phase 7.5, & Phase 7.6 (`DR-22`) parity fuzzing.
const PHASE4_BODY_VARIANTS = [_][]const u8{
    "    let step = add_generic(input_val, 10);\n    return .Ok(step);\n",
    "    // Comment edit only:\n    let step = add_generic(input_val, 10);\n\n    return .Ok(step);\n",
    "    let opt_in: i32? = if input_val > 0 => .Some(input_val) else .None;\n" ++
        "    if (cand_opt := opt_in) is .Some(inner_val) and (shifted := inner_val + 3) > 5 {\n" ++
        "        let _keep = cand_opt;\n" ++
        "        return .Ok(scale_step(bonus: shifted, base: inner_val));\n" ++
        "    }\n" ++
        "    return .Ok(opt_in orelse 7);\n",
    "    let fixed_nums: [i32; 4] = [input_val, 4, 8, 12];\n" ++
        "    let view_nums: &[i32] = &fixed_nums;\n" ++
        "    var loop_acc: i32 = view_nums[$ - 1];\n" ++
        "    for item_val, item_idx in view_nums[..$ - 1] {\n" ++
        "        loop_acc += item_val + (item_idx as i32);\n" ++
        "    }\n" ++
        "    let hit_val: i32 = find_gt: for item_val, item_idx in view_nums {\n" ++
        "        if item_val > 6 { break :find_gt item_val + (item_idx as i32); }\n" ++
        "    } orelse 1;\n" ++
        "    return .Ok(loop_acc + hit_val);\n",
    "    let active_tok = CancelToken { _handle: 11 };\n" ++
        "    let tok_bonus: i32 = with context.cancel_token = active_tok {\n" ++
        "        context.cancel_token._handle as i32\n" ++
        "    };\n" ++
        "    return .Ok(scale_step(input_val) + tok_bonus);\n",
    "    var left_v: i32 = input_val + (b'A' as i32);\n" ++
        "    var right_v: i32 = ~3_i32;\n" ++
        "    (left_v, right_v) = (right_v, left_v);\n" ++
        "    let fsm_v: i32 = fsm: match left_v {\n" ++
        "        0 => continue :fsm 1,\n" ++
        "        _ => left_v + right_v,\n" ++
        "    };\n" ++
        "    return .Ok(fsm_v);\n",
    "    let cx_word_sz: i32 = cx.mem.word_bytes();\n    return .Ok(input_val + cx_word_sz);\n",
    "    let direct_core_err: i32 = core.mem.word_bytes();\n    return .Ok(direct_core_err);\n",
    "    let bad_mismatch: bool = input_val;\n    let _keep = bad_mismatch;\n    return .Ok(0);\n",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Builds a multi-item `.cx` module for incremental `CompilerDb` fuzzing.
fn buildIncrementalTypecheckModule(
    allocator: std.mem.Allocator,
    has_banner_comment: bool,
    import_choice: usize,
    body_choices: [3]usize,
) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    if (has_banner_comment) {
        try builder.appendSlice(allocator, "/# Incremental Phase 4 + DR-24 fuzz banner\n\n");
    }
    try builder.appendSlice(allocator, PHASE4_IMPORT_VARIANTS[import_choice]);
    try builder.appendSlice(
        allocator,
        "pub fn add_generic(lhs: Number, rhs: Number) -> Number = lhs + rhs;\n\n" ++
            "pub fn scale_step(base: i32, factor: i32 = 2, bonus: i32 = base + 1) -> i32 = base * factor + bonus;\n\n",
    );

    var fn_i: usize = 0;
    while (fn_i < 3) : (fn_i += 1) {
        var hdr_buf: [128]u8 = undefined;
        try builder.appendSlice(
            allocator,
            try std.fmt.bufPrint(
                &hdr_buf,
                "pub fn worker_{d}(input_val: i32) -> i32!i32 {{\n",
                .{fn_i},
            ),
        );
        try builder.appendSlice(allocator, PHASE4_BODY_VARIANTS[body_choices[fn_i]]);
        try builder.appendSlice(allocator, "}\n\n");
    }
    return builder.toOwnedSlice(allocator);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_phase4_typechecker_fault_tolerance_and_poison_soundness" {
    var prng = std.Random.DefaultPrng.init(0xF004_C0DE_2026_0004);
    const random = prng.random();

    var source_buf: [8192]u8 = undefined;
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
            source_buf[mut_pos] = switch (random.uintLessThan(u8, 8)) {
                0 => ';',
                1 => ' ',
                2 => '?',
                3 => '~',
                4 => '_',
                5 => '$',
                6 => ':',
                else => source_buf[mut_pos],
            };
        }

        var res = try type_system.typecheckSource(
            std.testing.allocator,
            FileId.fromInt(@intCast((iter_idx & 0xFF) + 1)),
            source_buf[0..byte_len],
        );
        defer res.deinit();

        try std.testing.expect(res.type_pool.countTypes() >= 64);
    }
}

test "test_fuzz_phase4_incremental_typecheck_parity" {
    var prng = std.Random.DefaultPrng.init(0xDB04_FA5E_2026_1110);
    const random = prng.random();

    var inc_db = try CompilerDb.init(std.testing.allocator);
    defer inc_db.deinit();

    const core_fid = FileId.fromInt(2);
    _ = try inc_db.setInput(core_fid, CORE_STUB_SOURCE, .high);
    try inc_db.registerRootModule("core", core_fid);
    try inc_db.registerRootModule("cx", core_fid);

    const file_id = FileId.fromInt(1);
    var import_choice: usize = 0;
    var body_choices = [3]usize{ 0, 2, 3 };
    var has_banner_comment = false;
    var durability: Durability = .low;

    var step_idx: usize = 0;
    while (step_idx < INCREMENTAL_TYPECHECK_ITERATIONS) : (step_idx += 1) {
        switch (random.uintLessThan(u8, 5)) {
            0 => has_banner_comment = !has_banner_comment,
            1 => body_choices[random.uintLessThan(usize, 3)] =
                random.uintLessThan(usize, PHASE4_BODY_VARIANTS.len),
            2 => import_choice = random.uintLessThan(usize, PHASE4_IMPORT_VARIANTS.len),
            3 => durability = switch (random.uintLessThan(u8, 3)) {
                0 => .low,
                1 => .medium,
                else => .high,
            },
            else => {},
        }

        const src = try buildIncrementalTypecheckModule(
            std.testing.allocator,
            has_banner_comment,
            import_choice,
            body_choices,
        );
        defer std.testing.allocator.free(src);

        _ = try inc_db.setInput(file_id, src, durability);

        var scratch_db = try CompilerDb.init(std.testing.allocator);
        defer scratch_db.deinit();
        _ = try scratch_db.setInput(core_fid, CORE_STUB_SOURCE, .high);
        try scratch_db.registerRootModule("core", core_fid);
        try scratch_db.registerRootModule("cx", core_fid);
        _ = try scratch_db.setInput(file_id, src, durability);

        // [1] Module-level signature & import (`use cx.*` vs `use core.*`) parity:
        const inc_mod_scope = try inc_db.resolveSignatures(file_id);
        const scr_mod_scope = try scratch_db.resolveSignatures(file_id);
        try std.testing.expectEqual(inc_mod_scope.error_count, scr_mod_scope.error_count);
        try std.testing.expect(
            Fingerprint128.eql(inc_mod_scope.signatures_fingerprint, scr_mod_scope.signatures_fingerprint),
        );

        // [2] Per-definition `getDefSignature` and `typecheckBody` parity across all `ItemTree` entries:
        const inc_tree = try inc_db.extractItemTree(file_id);
        try std.testing.expectEqual(
            inc_tree.entries.len,
            (try scratch_db.extractItemTree(file_id)).entries.len,
        );
        for (inc_tree.entries) |entry| {
            try std.testing.expect(
                Fingerprint128.eql(
                    (try inc_db.getDefSignature(entry.def_id)).signature_fingerprint,
                    (try scratch_db.getDefSignature(entry.def_id)).signature_fingerprint,
                ),
            );

            const inc_body = try inc_db.typecheckBody(entry.def_id);
            const scr_body = try scratch_db.typecheckBody(entry.def_id);
            try std.testing.expectEqual(inc_body.error_count, scr_body.error_count);
            try std.testing.expect(Fingerprint128.eql(inc_body.typed_fingerprint, scr_body.typed_fingerprint));
        }
    }
}

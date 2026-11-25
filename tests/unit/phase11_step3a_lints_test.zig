//! Phase 11.1c (`RDG-25`) Step 3A Unit Tests (`tests/unit/phase11_step3a_lints_test.zig`)
//!
//! Verifies all 14 single-pass Lexer, Parser/CST, and `SymbolTable` lint rules (`W0101`–`W0104`,
//! `W0119`, `W0121`–`W0123`, `W0201`–`W0203`, `W0402`, `W0404`, `W0406`), `SuggestionFix` rewrite
//! convergence, false-positive soundness guards (`Δt`, `'ab'` rollback, `rustc #110923`, `@cfg`
//! inactive token guard, struct shorthand `Point { x, y: _y }`, `0xdeadbeef_u32` 1-pass fusion,
//! intra-package `W0201` renames), `SymbolFlags.is_mutated` pre-wiring, and incremental splicing.

const std = @import("std");
const corex = @import("corex");

const CompilerDb = corex.CompilerDb;
const FileId = corex.FileId;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const FixApplicability = corex.diagnostic.FixApplicability;
const RuleId = corex.diagnostic.RuleId;
const SuggestedFix = corex.SuggestedFix;
const TransactionalPatcher = corex.TransactionalPatcher;
const lint_filter = corex.lint_filter;

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic with `code`.
fn hasDiagnosticCode(sink: *const DiagnosticSink, code: DiagnosticCode) bool {
    for (sink.asSlice()) |diag_item| {
        if (diag_item.code == code) return true;
    }
    return false;
}

/// Counts diagnostics in `sink` matching `code`.
fn countDiagnosticCode(sink: *const DiagnosticSink, code: DiagnosticCode) usize {
    var count: usize = 0;
    for (sink.asSlice()) |diag_item| {
        if (diag_item.code == code) count += 1;
    }
    return count;
}

/// Collects all `SuggestedFix` entries (filtering to `.machine_applicable` unless `include_unsafe`) and patches `source`.
fn applyProjectedFixes(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    source: []const u8,
    sink: *const DiagnosticSink,
    is_including_unsafe: bool,
) ![]u8 {
    var fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
    defer fixes.deinit(allocator);
    for (sink.asSlice()) |diag_item| {
        for (diag_item.suggestions) |sug| {
            if (sug.applicability == .machine_applicable or
                (is_including_unsafe and sug.applicability == .maybe_incorrect))
            {
                var accepted_fix = sug;
                accepted_fix.applicability = .machine_applicable;
                try fixes.append(allocator, accepted_fix);
            }
        }
    }
    const res = try TransactionalPatcher.apply(allocator, source, file_id, fixes.items, &db.interner);
    return res.patched_source;
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_dr25_w0101_rollback_guard_w0102_trojan_controls_and_w0104_unicode_impostors" {
    const allocator = std.testing.allocator;
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    // [1] Multi-char `'ab'` and `'\'b'` emit `E0102` and roll back `W0101`:
    const fid_char = FileId.fromInt(801);
    try db.setFilePackageId(fid_char, .root);
    try db.setFilePath(fid_char, "D:/ws/src/char_guard.cx");
    _ = try db.setInput(
        fid_char,
        "pub fn demo() -> char {\n    let bad = '\\'b';\n    return bad;\n}\n",
        .low,
    );
    const char_sink = try db.projectFileDiagnostics(fid_char);
    try std.testing.expect(hasDiagnosticCode(char_sink, .e0102_unterminated_string_literal));
    try std.testing.expect(!hasDiagnosticCode(char_sink, .w0101_redundant_escape_sequence));

    // [2] Byte-0 UTF-8 BOM is clean; mid-file `U+FEFF` and bidi `U+202E` emit `W0102` (`Auto`):
    const fid_trojan = FileId.fromInt(802);
    try db.setFilePackageId(fid_trojan, .root);
    try db.setFilePath(fid_trojan, "D:/ws/src/trojan.cx");
    const trojan_src = "\xEF\xBB\xBFpub fn check_bidi() -> str {\n    // hidden\u{202E}note\n    return \"ab\u{202E}cd\";\n}\n";
    _ = try db.setInput(fid_trojan, trojan_src, .low);
    const trojan_sink = try db.projectFileDiagnostics(fid_trojan);
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(trojan_sink, .w0102_unicode_trojan_control));
    const patched_trojan = try applyProjectedFixes(allocator, &db, fid_trojan, trojan_src, trojan_sink, false);
    defer allocator.free(patched_trojan);
    try std.testing.expect(std.mem.indexOf(u8, patched_trojan, "// hiddennote\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_trojan, "\"ab\\u{202E}cd\"") != null);

    // [3] `W0104`: canonical CoreX glyphs & pure Cyrillic prose are clean; mixed-word `"Сache"` & em-dash flag `Unsafe`:
    const fid_uni = FileId.fromInt(803);
    try db.setFilePackageId(fid_uni, .root);
    try db.setFilePath(fid_uni, "D:/ws/src/uni_text.cx");
    const clean_uni_src =
        "// Canonical – … § × ≤ ≥ ≠ → ╭─▸ ✓ ✗ ⚠ Привет мир\n" ++
        "pub fn banner() -> str {\n    \"Привет – ok…\"\n}\n";
    _ = try db.setInput(fid_uni, clean_uni_src, .low);
    const clean_uni_sink = try db.projectFileDiagnostics(fid_uni);
    try std.testing.expectEqual(@as(usize, 0), clean_uni_sink.countDiagnostics());

    const bad_uni_src =
        "// Title \u{2014} summary\n" ++
        "pub fn label() -> str {\n    return \"\u{0421}ache\";\n}\n";
    _ = try db.setInput(fid_uni, bad_uni_src, .low);
    const bad_uni_sink = try db.projectFileDiagnostics(fid_uni);
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(bad_uni_sink, .w0104_ambiguous_unicode_text));
    for (bad_uni_sink.asSlice()) |diag_item| {
        if (diag_item.code == .w0104_ambiguous_unicode_text) {
            try std.testing.expectEqual(FixApplicability.maybe_incorrect, diag_item.suggestions[0].applicability);
        }
    }
    const patched_uni = try applyProjectedFixes(allocator, &db, fid_uni, bad_uni_src, bad_uni_sink, true);
    defer allocator.free(patched_uni);
    try std.testing.expect(std.mem.indexOf(u8, patched_uni, "// Title \u{2013} summary\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_uni, "\"Cache\"") != null);
}

test "test_dr25_w0103_scientific_greek_allowlist_mixed_script_and_skeleton_collision" {
    const allocator = std.testing.allocator;
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    // [1] `Δt`, `μs`, and pure single-script non-Latin identifiers pass with 0 warnings:
    const fid_sci = FileId.fromInt(804);
    try db.setFilePackageId(fid_sci, .root);
    try db.setFilePath(fid_sci, "D:/ws/src/physics.cx");
    const sci_src =
        "pub fn step_sim(Δt: f64, μs: f64) -> f64 {\n" ++
        "    let λ_max = Δt + μs;\n" ++
        "    λ_max * 2.0\n" ++
        "}\n";
    _ = try db.setInput(fid_sci, sci_src, .low);
    const sci_sink = try db.projectFileDiagnostics(fid_sci);
    try std.testing.expectEqual(@as(usize, 0), sci_sink.countDiagnostics());

    // [2] Mixed-script `pаypal` (`U+0430`) and skeleton collision (`scope_val` vs `scоpe_val` `U+043E`) emit `W0103`:
    const fid_conf = FileId.fromInt(805);
    try db.setFilePackageId(fid_conf, .root);
    try db.setFilePath(fid_conf, "D:/ws/src/confusable.cx");
    const conf_src =
        "pub fn verify() -> i32 {\n" ++
        "    let p\u{0430}ypal = 10;\n" ++
        "    let c_ascii = 20;\n" ++
        "    let \u{0441}_ascii = 30;\n" ++
        "    return p\u{0430}ypal + c_ascii + \u{0441}_ascii;\n" ++
        "}\n";
    _ = try db.setInput(fid_conf, conf_src, .low);
    const conf_sink = try db.projectFileDiagnostics(fid_conf);
    try std.testing.expect(countDiagnosticCode(conf_sink, .w0103_confusable_ident) >= 2);
}

test "test_dr25_w0119_w0121_w0122_and_w0123_single_pass_literal_rewrites_and_guards" {
    const allocator = std.testing.allocator;
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    // [1] Guarded clean literals (`r"a\b"`, `f#"a\n{val}"#`, `3.141592653589793_f64`, `2026`, `0x10_00`, `0o0755`):
    const fid_clean = FileId.fromInt(806);
    try db.setFilePackageId(fid_clean, .root);
    try db.setFilePath(fid_clean, "D:/ws/src/lit_clean.cx");
    const clean_src =
        "pub const PI_EXACT: f64 = 3.141592653589793_f64;\n" ++
        "pub const PORT_YEAR: u32 = 2026;\n" ++
        "pub const BYTE_MASK: u32 = 0x10_00;\n" ++
        "pub const UNIX_MODE: u32 = 0o0755;\n" ++
        "pub fn format_path(val: i32) -> str {\n" ++
        "    let rx = r\"a\\b\";\n" ++
        "    _ = f#\"a\\n{val} {rx}\"#;\n" ++
        "    rx\n" ++
        "}\n";
    _ = try db.setInput(fid_clean, clean_src, .low);
    const clean_sink = try db.projectFileDiagnostics(fid_clean);
    try std.testing.expectEqual(@as(usize, 0), clean_sink.countDiagnostics());

    // [2] 1-pass `f###"a"b"###` -> `r#"a"b"#`, `r#"abc"#` -> `"abc"`, `f#"hi {val}"#` -> `f"hi {val}"`,
    //     and fused `0xdeadbeef_u32` -> `0xDEAD_BEEF_u32`:
    const fid_fix = FileId.fromInt(807);
    try db.setFilePackageId(fid_fix, .root);
    try db.setFilePath(fid_fix, "D:/ws/src/lit_fix.cx");
    const dirty_src =
        "pub fn literals(val: u32) -> u32 {\n" ++
        "    let _s1 = f###\"a\"b\"###;\n" ++
        "    let _s2 = r#\"abc\"#;\n" ++
        "    let _s3 = f#\"hi {val}\"#;\n" ++
        "    let num_dec: u32 = 100000;\n" ++
        "    let num_hex: u32 = 0xdeadbeef_u32;\n" ++
        "    return val + num_dec + num_hex;\n" ++
        "}\n";
    _ = try db.setInput(fid_fix, dirty_src, .low);
    const dirty_sink = try db.projectFileDiagnostics(fid_fix);
    try std.testing.expectEqual(@as(usize, 1), countDiagnosticCode(dirty_sink, .w0119_useless_format_string));
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(dirty_sink, .w0121_needless_raw_string_hashes));
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(dirty_sink, .w0122_ungrouped_numeric_literal));
    try std.testing.expectEqual(@as(usize, 1), countDiagnosticCode(dirty_sink, .w0123_non_upper_hex_literal));

    const patched = try applyProjectedFixes(allocator, &db, fid_fix, dirty_src, dirty_sink, false);
    defer allocator.free(patched);
    try std.testing.expect(std.mem.indexOf(u8, patched, "r#\"a\"b\"#") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched, "let _s2 = \"abc\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched, "let _s3 = f\"hi {val}\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched, "100_000") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched, "0xDEAD_BEEF_u32") != null);
}

test "test_dr25_w0201_decl_emission_and_ref_rename_w0202_cst_idioms_and_w0203_single_char" {
    const allocator = std.testing.allocator;
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    // [1] `W0201` renames declaration + references + format-string hole without emitting duplicate reference warnings:
    const fid_case = FileId.fromInt(808);
    try db.setFilePackageId(fid_case, .root);
    try db.setFilePath(fid_case, "D:/ws/src/casing.cx");
    const case_src =
        "extern \"C\" fn ForeignMixedName(p: *mut opaque);\n" ++
        "pub fn computeSum(userId: i32) -> i32 {\n" ++
        "    let _msg = f\"id={userId}\";\n" ++
        "    return userId + 1;\n" ++
        "}\n" ++
        "pub fn caller() -> i32 {\n" ++
        "    return computeSum(userId: 42);\n" ++
        "}\n";
    _ = try db.setInput(fid_case, case_src, .low);
    const case_sink = try db.projectFileDiagnostics(fid_case);
    // Only the 2 declarations (`computeSum` and `userId`) emit `W0201`; `ForeignMixedName` & references do not!
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(case_sink, .w0201_non_canonical_identifier_case));
    const patched_case = try applyProjectedFixes(allocator, &db, fid_case, case_src, case_sink, false);
    defer allocator.free(patched_case);
    try std.testing.expect(std.mem.indexOf(u8, patched_case, "pub fn compute_sum(user_id: i32) -> i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_case, "f\"id={user_id}\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_case, "return user_id + 1;") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_case, "return compute_sum(user_id: 42);") != null);

    // [2] `W0202` (`-> unit`, empty `;`, `Point { x: x }`) and `W0203` (`|v| v + 1` allowed vs `let q = 1` flagged):
    const fid_cst = FileId.fromInt(809);
    try db.setFilePackageId(fid_cst, .root);
    try db.setFilePath(fid_cst, "D:/ws/src/idioms.cx");
    const cst_src =
        "pub struct Point {\n    pub x: i32,\n    pub y: i32,\n}\n" ++
        "pub type Callback = fn() -> unit;\n" ++
        "pub fn build_point(x: i32) -> unit {\n" ++
        "    let map_fn = |v: i32| v + 1;\n" ++
        "    let q = map_fn(x);\n" ++
        "    let pt = Point { x: x, y: q };\n" ++
        "    let Point { x: x_out, y: _ } = pt;\n" ++
        "    _ = x_out;\n" ++
        "    ;\n" ++
        "}\n";
    _ = try db.setInput(fid_cst, cst_src, .low);
    const cst_sink = try db.projectFileDiagnostics(fid_cst);
    // `W0202` fires on `-> unit` (NOT `fn() -> unit`!), `x: x`, and empty `;` (= 3):
    try std.testing.expectEqual(@as(usize, 3), countDiagnosticCode(cst_sink, .w0202_non_idiomatic_construct));
    // `W0203` fires ONLY on `let q` (`x` is allowed math coord, `|v: i32| v + 1` is single-expr non-block closure):
    try std.testing.expectEqual(@as(usize, 1), countDiagnosticCode(cst_sink, .w0203_single_char_ident));
    const patched_cst = try applyProjectedFixes(allocator, &db, fid_cst, cst_src, cst_sink, false);
    defer allocator.free(patched_cst);
    try std.testing.expect(std.mem.indexOf(u8, patched_cst, "pub type Callback = fn() -> unit;") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_cst, "pub fn build_point(x: i32) {") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_cst, "Point { x, y: q }") != null);
}

test "test_dr25_w0402_struct_shorthand_w0404_surgical_use_tree_and_w0406_sig_leak_guard" {
    const allocator = std.testing.allocator;
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    // [1] `W0402` (`Unsafe`): `let Pair { left, right } = pr;` rewrites unused `right` to `right: _right`, plus private `fn`:
    const fid_unused = FileId.fromInt(810);
    try db.setFilePackageId(fid_unused, .root);
    try db.setFilePath(fid_unused, "D:/ws/src/unused.cx");
    const unused_src =
        "pub struct Pair {\n    pub left: i32,\n    pub right: i32,\n}\n" ++
        "fn dead_private_helper() -> i32 {\n    return 9;\n}\n" ++
        "pub fn take_left(pr: Pair) -> i32 {\n" ++
        "    let Pair { left, right } = pr;\n" ++
        "    return left;\n" ++
        "}\n";
    _ = try db.setInput(fid_unused, unused_src, .low);
    const unused_sink = try db.projectFileDiagnostics(fid_unused);
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(unused_sink, .w0402_unused_binding));
    for (unused_sink.asSlice()) |diag_item| {
        if (diag_item.code == .w0402_unused_binding) {
            try std.testing.expectEqual(FixApplicability.maybe_incorrect, diag_item.suggestions[0].applicability);
        }
    }
    const patched_unused = try applyProjectedFixes(allocator, &db, fid_unused, unused_src, unused_sink, true);
    defer allocator.free(patched_unused);
    try std.testing.expect(std.mem.indexOf(u8, patched_unused, "let Pair { left, right: _right } = pr;") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_unused, "fn _dead_private_helper() -> i32") != null);

    // [2] `W0404` (`Auto`): trait-method usage marks trait import used; `use sub.{alpha, beta};` prunes to `use sub.alpha;`:
    const fid_imp = FileId.fromInt(811);
    try db.setFilePackageId(fid_imp, .root);
    try db.setFilePath(fid_imp, "D:/ws/src/imports.cx");
    const imp_src =
        "pub mod traits {\n" ++
        "    pub trait Score {\n        fn score(&self) -> i32;\n    }\n" ++
        "}\n" ++
        "pub mod helpers {\n" ++
        "    pub fn alpha() -> i32 {\n        return 1;\n    }\n" ++
        "    pub fn beta() -> i32 {\n        return 2;\n    }\n" ++
        "    pub fn gamma() -> i32 {\n        return 3;\n    }\n" ++
        "}\n" ++
        "pub struct Item {\n    pub val: i32,\n}\n" ++
        "impl traits.Score for Item {\n" ++
        "    pub fn score(&self) -> i32 {\n        return self.val;\n    }\n" ++
        "}\n" ++
        "use traits.Score;\n" ++
        "use helpers.{alpha, beta};\n" ++
        "use helpers.gamma;\n" ++
        "pub fn run_item(item: Item) -> i32 {\n" ++
        "    return item.score() + alpha();\n" ++
        "}\n";
    _ = try db.setInput(fid_imp, imp_src, .low);
    const imp_sink = try db.projectFileDiagnostics(fid_imp);
    // `traits.Score` IS used via `item.score()` (`impl_method_trait`!); only `beta` and `gamma` emit `W0404`:
    try std.testing.expectEqual(@as(usize, 2), countDiagnosticCode(imp_sink, .w0404_unused_import));
    const patched_imp = try applyProjectedFixes(allocator, &db, fid_imp, imp_src, imp_sink, false);
    defer allocator.free(patched_imp);
    try std.testing.expect(std.mem.indexOf(u8, patched_imp, "use traits.Score;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_imp, "use helpers.alpha;\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_imp, "gamma") == null or
        std.mem.indexOf(u8, patched_imp, "use helpers.gamma;") == null);

    // [3] `W0406` (`Auto`) + `rustc #110923` signature leakage guard across parent & sibling modules:
    var parent_db = try CompilerDb.init(allocator);
    defer parent_db.deinit();
    const fid_lex_p = FileId.fromInt(818);
    const fid_root_p = FileId.fromInt(819);
    try parent_db.setFilePackageId(fid_lex_p, .root);
    try parent_db.setFilePackageId(fid_root_p, .root);
    try parent_db.setFilePath(fid_lex_p, "D:/ws/src/lex_mod.cx");
    try parent_db.setFilePath(fid_root_p, "D:/ws/src/lib.cx");
    const lex_mod_src =
        "pub(pkg) struct HiddenToken {\n    pub(pkg) code: i32,\n}\n" ++
        "pub(pkg) fn next_token() -> HiddenToken {\n" ++
        "    return HiddenToken { code: 7 };\n" ++
        "}\n" ++
        "pub(pkg) fn unused_cross_mod() -> i32 {\n" ++
        "    return 5;\n" ++
        "}\n";
    const parent_only_root_src =
        "pub(pkg) mod lex_mod;\n" ++
        "pub fn entry() -> i32 {\n" ++
        "    let tok = lex_mod.next_token();\n" ++
        "    return tok.code;\n" ++
        "}\n";
    _ = try parent_db.setInput(fid_lex_p, lex_mod_src, .low);
    _ = try parent_db.setInput(fid_root_p, parent_only_root_src, .low);
    try parent_db.bindExternalModule(fid_root_p, "lex_mod", fid_lex_p);
    _ = try parent_db.projectFileDiagnostics(fid_root_p);
    const parent_vis_sink = try parent_db.projectFileDiagnostics(fid_lex_p);
    // Direct parent-only access narrows `HiddenToken` (`#110923`!), `code`, and `next_token` to `pub(super)`,
    // and `unused_cross_mod` to private (`4` `W0406` diagnostics):
    try std.testing.expectEqual(@as(usize, 4), countDiagnosticCode(parent_vis_sink, .w0406_unused_pkg_visibility));
    const patched_parent_vis = try applyProjectedFixes(allocator, &parent_db, fid_lex_p, lex_mod_src, parent_vis_sink, false);
    defer allocator.free(patched_parent_vis);
    try std.testing.expect(std.mem.indexOf(u8, patched_parent_vis, "pub(super) struct HiddenToken") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_parent_vis, "fn unused_cross_mod() -> i32") != null);

    // Cousin module access outside `super` (`lib -> frontend -> lex_mod` accessed from `lib -> backend`):
    // `HiddenToken` (`#110923`), `code`, and `next_token` require `pub(pkg)`; ONLY `unused_cross_mod` (`1` diag) narrows!
    var vis_db = try CompilerDb.init(allocator);
    defer vis_db.deinit();
    const fid_lex = FileId.fromInt(820);
    const fid_frontend = FileId.fromInt(821);
    const fid_backend = FileId.fromInt(822);
    const fid_root = FileId.fromInt(823);
    try vis_db.setFilePackageId(fid_lex, .root);
    try vis_db.setFilePackageId(fid_frontend, .root);
    try vis_db.setFilePackageId(fid_backend, .root);
    try vis_db.setFilePackageId(fid_root, .root);
    try vis_db.setFilePath(fid_lex, "D:/ws/src/frontend/lex_mod.cx");
    try vis_db.setFilePath(fid_frontend, "D:/ws/src/frontend/mod.cx");
    try vis_db.setFilePath(fid_backend, "D:/ws/src/backend.cx");
    try vis_db.setFilePath(fid_root, "D:/ws/src/lib.cx");
    const frontend_mod_src = "pub(pkg) mod lex_mod;\n";
    const backend_mod_src =
        "use super.frontend.lex_mod;\n" ++
        "pub(super) fn emit_head() -> i32 {\n" ++
        "    let tok = lex_mod.next_token();\n" ++
        "    return tok.code;\n" ++
        "}\n";
    const lib_clean_src =
        "pub(pkg) mod frontend;\n" ++
        "pub(pkg) mod backend;\n" ++
        "pub fn entry() -> i32 {\n" ++
        "    return backend.emit_head();\n" ++
        "}\n";
    _ = try vis_db.setInput(fid_lex, lex_mod_src, .low);
    _ = try vis_db.setInput(fid_frontend, frontend_mod_src, .low);
    _ = try vis_db.setInput(fid_backend, backend_mod_src, .low);
    _ = try vis_db.setInput(fid_root, lib_clean_src, .low);
    try vis_db.bindExternalModule(fid_frontend, "lex_mod", fid_lex);
    try vis_db.bindExternalModule(fid_root, "frontend", fid_frontend);
    try vis_db.bindExternalModule(fid_root, "backend", fid_backend);
    _ = try vis_db.projectFileDiagnostics(fid_root);
    _ = try vis_db.projectFileDiagnostics(fid_frontend);
    _ = try vis_db.projectFileDiagnostics(fid_backend);

    const vis_sink = try vis_db.projectFileDiagnostics(fid_lex);
    try std.testing.expectEqual(@as(usize, 1), countDiagnosticCode(vis_sink, .w0406_unused_pkg_visibility));
    const patched_vis = try applyProjectedFixes(allocator, &vis_db, fid_lex, lex_mod_src, vis_sink, false);
    defer allocator.free(patched_vis);
    try std.testing.expect(std.mem.indexOf(u8, patched_vis, "pub(pkg) struct HiddenToken") != null);
    try std.testing.expect(std.mem.indexOf(u8, patched_vis, "fn unused_cross_mod() -> i32") != null);
}

test "test_dr25_symbol_is_mutated_flag_and_incremental_raw_lint_candidate_splicing" {
    const allocator = std.testing.allocator;
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    const fid = FileId.fromInt(830);
    try db.setFilePackageId(fid, .root);
    try db.setFilePath(fid, "D:/ws/src/inc_lints.cx");
    const src_v1 =
        "pub fn top_fn(val: i32) -> i32 {\n    return val + 1;\n}\n\n" ++
        "pub fn bottom_fn() -> u32 {\n    return 100000;\n}\n";
    _ = try db.setInput(fid, src_v1, .low);
    const sink_v1 = try db.projectFileDiagnostics(fid);
    try std.testing.expectEqual(@as(usize, 1), countDiagnosticCode(sink_v1, .w0122_ungrouped_numeric_literal));

    // Verify `markSymbolMutated` and `resetFnScopeForBodyRecheck` on `top_fn`'s parameter:
    var found_param_idx: corex.SymbolIndex = .none;
    for (0..db.symbol_table.countSymbols()) |raw_i| {
        const idx = corex.SymbolIndex.fromInt(@intCast(raw_i));
        const rec = db.symbol_table.getSymbol(idx);
        if (rec.kind == .param_sym and std.mem.eql(u8, rec.name_text, "val") and rec.decl_span.file_id == fid) {
            found_param_idx = idx;
            break;
        }
    }
    try std.testing.expect(!found_param_idx.isNone());
    try std.testing.expect(!db.symbol_table.getSymbol(found_param_idx).flags.is_mutated);
    db.symbol_table.markSymbolMutated(found_param_idx);
    try std.testing.expect(db.symbol_table.getSymbol(found_param_idx).flags.is_mutated);
    const param_scope = db.symbol_table.getSymbol(found_param_idx).scope_id;
    db.symbol_table.resetFnScopeForBodyRecheck(param_scope, &.{});
    try std.testing.expect(!db.symbol_table.getSymbol(found_param_idx).flags.is_mutated);

    // Apply an incremental edit inside `top_fn` (+4 bytes) and verify `bottom_fn`'s `100000` `W0122` span shifts by +4!
    const edit_pos: u32 = @intCast(std.mem.indexOf(u8, src_v1, "val + 1").?);
    const src_v2 =
        "pub fn top_fn(val: i32) -> i32 {\n    return val + 12_345;\n}\n\n" ++
        "pub fn bottom_fn() -> u32 {\n    return 100000;\n}\n";
    _ = try db.setInputWithEdit(
        fid,
        src_v2,
        .low,
        .{ .start_byte = edit_pos, .old_end_byte = edit_pos + 7, .new_end_byte = edit_pos + 12 },
    );
    const sink_v2 = try db.projectFileDiagnostics(fid);
    try std.testing.expect(db.telemetry.incremental_reparse_fast_splices >= 1);
    const expected_num_start: u32 = @intCast(std.mem.indexOf(u8, src_v2, "100000").?);
    var matched_shifted = false;
    for (sink_v2.asSlice()) |diag_item| {
        if (diag_item.code == .w0122_ungrouped_numeric_literal) {
            try std.testing.expectEqual(expected_num_start, diag_item.primary_span.start_byte);
            matched_shifted = true;
        }
    }
    try std.testing.expect(matched_shifted);
}

//! Phase 11.1c (`DR-25`) Suppression Table, `CompiledGlob64` & Auto-Fixer Structure-Aware Fuzz Suite
//!
//! Executes deterministic `std.Random.Xoroshiro128` fuzzing across `.cx` programs mutated with random
//! `@expect` / `@allow` attributes, `// corex check:` preamble/above-line/trailing directives, `CRLF`/`LF`
//! endings, non-ASCII Unicode/Trojan Source bytes, and adversarial `CompiledGlob64` path-glob patterns.
//!
//! Enforces zero panics, zero memory leaks under `std.testing.allocator`, warning-only lint severities,
//! bounded fix passes (`<= 2` on single-stage mutations), and idempotent fixed-point convergence.

const std = @import("std");
const corex = @import("corex");

const BumpArena = corex.BumpArena;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;
const FileId = corex.FileId;
const RuleId = corex.RuleId;
const Severity = corex.Severity;
const Span = corex.Span;
const StringInterner = corex.StringInterner;
const TargetSpec = corex.TargetSpec;
const VfsSourceMap = corex.VfsSourceMap;
const check_audit = corex.check_audit;
const lint_filter = corex.lint_filter;
const pkg_manifest = corex.pkg_manifest;

// --------------------------------------- CONSTS ----------------------------------------

// -------------------- Fuzzing Seed Corpora --------------------

/// Total mutated `.cx` suppression/fixer programs verified per deterministic PRNG run.
const SUPPRESSION_FIXER_FUZZ_ITERATIONS: usize = 96;

/// Total randomized `CompiledGlob64` pattern × path evaluations verified per deterministic PRNG run.
const GLOB_FUZZ_ITERATIONS: usize = 240;

/// Baseline `.cx` snippets covering lexical, CST, `TypeChecker`, and `MIR` lint sites.
const SEED_CX_PROGRAMS = [_][]const u8{
    \\pub fn compute_mask(seed: u32) -> u32 {
    \\    let mask: u32 = 0xdead_beef_u32;
    \\    let big = 1000000_u32;
    \\    return seed ^ mask ^ big;
    \\}
    ++ "\n",
    \\pub struct Point {
    \\    pub x: i32,
    \\    pub y: i32,
    \\}
    \\
    \\pub fn make_point(x: i32, flag: bool) -> Point {
    \\    ;
    \\    var y = if flag => 10 else 20;
    \\    Point { x: x, y }
    \\}
    ++ "\n",
    \\/| Computes discounted total.
    \\pub fn calc_total(maybe_v: i32?, cond_a: bool, cond_b: bool) -> i32 {
    \\    var acc = 0;
    \\    if cond_a {
    \\        if cond_b {
    \\            acc = acc + 5;
    \\        }
    \\    }
    \\    let base = match maybe_v {
    \\        .Some(inner) => inner,
    \\        .None => 1,
    \\    };
    \\    let out_sum = acc + base;
    \\    out_sum
    \\}
    ++ "\n",
    \\@derive(Copy, Clone)
    \\pub struct Tag4 {
    \\    pub id: u32,
    \\}
    \\
    \\fn tag_value(item: &Tag4) -> u32 {
    \\    let cloned = item.clone();
    \\    cloned.id
    \\}
    \\
    \\pub fn run_tag(item: Tag4, c: u32) -> u32 {
    \\    let _msg = f"static_label";
    \\    let _raw = r#"plain_raw"#;
    \\    tag_value(&item) + c
    \\}
    ++ "\n",
};

/// Valid and adversarial Scope-2 file-preamble directive lines.
const PREAMBLE_INJECTIONS = [_][]const u8{
    "",
    "// corex check: file-expect(W0123, W0122) -- fuzz preamble\n",
    "// corex check: file-allow(single-char-ident, unused-binding) -- fuzz file allow\n",
    "// corex check: file-expect(non-idiomatic-syntax)\n",
    "// corex check: file-allow(*) -- invalid wildcard\n",
    "// corex check: file-expect(style) -- invalid category\n",
    "// corex check: file-allow(E0401) -- non-suppressible error\n",
    "// corex check: unknown-action(W0123) -- bad action\n",
};

/// Valid and adversarial Scope-3 attribute / above-line directive prefixes injected before `pub fn`.
const ITEM_ATTR_INJECTIONS = [_][]const u8{
    "",
    "@expect(W0123, W0209, reason: \"fuzz item expect\")\n",
    "@allow(W0203, reason: \"fuzz item allow\")\n",
    "@expect(single-use-temp, collapsible-if, reason: \"todo\")\n",
    "// corex check: expect(W0202, W0405) -- above-line hoist candidate\n",
    "@allow\n",
    "@expect(all)\n",
    "@expect(collapsible - if, reason: \"spaced hyphen error\")\n",
};

/// Valid and adversarial Scope-4 trailing comment suffixes appended to interior lines.
const TRAILING_LINE_INJECTIONS = [_][]const u8{
    "",
    " // corex check: expect(W0123, W0208) -- trailing expect",
    " // corex check: allow(W0202) -- trailing allow",
    " // corex check: expect(W0412)",
    " // hidden\u{202E}bidi",
    " // mixed \u{0421}ache \u{2014} note",
};

/// Unicode, Trojan Source, and raw byte snippets spliced during fuzzing.
const UNICODE_MUTATION_SNIPPETS = [_][]const u8{
    "\u{202E}",
    "\u{2066}",
    "\u{200B}",
    "\u{FEFF}",
    "\u{0430}",
    "\u{2014}",
    "\u{00A0}",
    "Δt",
    "Привет",
    "\xFF\xFE",
};

/// Valid and malformed glob fragments used to synthesize fuzzed `CompiledGlob64` inputs.
const GLOB_FRAGMENTS = [_][]const u8{
    "src/**/*.cx",
    "tests/**/*.{cx,cxi}",
    "bench/*_[0-9].cx",
    "crates/{core,net,rpc}/src/*.cx",
    "**/generated/**",
    "?_file_[a-z].cx",
    "../escape/**/*.cx",
    "/abs/root/*.cx",
    "src/{unclosed,alt/*.cx",
    "src/[unclosed/*.cx",
    "{a,b,c,d,e}{f,g,h,i}",
    "a/**/b/**/c/**/d/**/e/**/f/**/g/**/h/**/i/**/j/**/k/**/l/**/m/**/n/**/o/**/p/**/q/*.cx",
};

/// Candidate relative paths (mixing Windows `\` and POSIX `/`) tested against `CompiledGlob64`.
const CANDIDATE_PATHS = [_][]const u8{
    "src/main.cx",
    "src\\net\\http.cx",
    "./tests/unit/lint_test.cx",
    ".\\tests\\fuzz\\seed.cxi",
    "crates\\rpc\\src\\wire.cx",
    "pkg/generated/v1/schema.cx",
    "x_file_m.cx",
    "",
};

// -------------------------------------- INTERNALS --------------------------------------

// ------------------ Fuzz Mutation Generators ------------------

/// Builds a deterministically mutated `.cx` source buffer from `SEED_CX_PROGRAMS` using `random`.
fn buildMutatedLintSource(allocator: std.mem.Allocator, random: std.Random) !struct {
    source: []u8,
    is_pure_valid_seed: bool,
} {
    var out: std.ArrayListUnmanaged(u8) = .empty;
    errdefer out.deinit(allocator);

    const use_crlf = random.boolean();
    const preamble_idx = random.uintLessThan(usize, PREAMBLE_INJECTIONS.len);
    const attr_idx = random.uintLessThan(usize, ITEM_ATTR_INJECTIONS.len);
    const trail_idx = random.uintLessThan(usize, TRAILING_LINE_INJECTIONS.len);
    const seed = SEED_CX_PROGRAMS[random.uintLessThan(usize, SEED_CX_PROGRAMS.len)];
    const inject_raw_corrupt = random.uintLessThan(u8, 8) == 0;

    const is_pure_valid = preamble_idx <= 3 and attr_idx <= 4 and !inject_raw_corrupt;

    try out.appendSlice(allocator, PREAMBLE_INJECTIONS[preamble_idx]);

    var line_it = std.mem.splitScalar(u8, seed, '\n');
    var has_injected_attr = false;
    var line_no: usize = 0;
    while (line_it.next()) |raw_line| : (line_no += 1) {
        if (raw_line.len == 0 and line_it.peek() == null) break;
        if (!has_injected_attr and std.mem.startsWith(u8, raw_line, "pub fn ")) {
            try out.appendSlice(allocator, ITEM_ATTR_INJECTIONS[attr_idx]);
            has_injected_attr = true;
        }
        try out.appendSlice(allocator, raw_line);
        if (line_no == 2 and raw_line.len > 0) {
            try out.appendSlice(allocator, TRAILING_LINE_INJECTIONS[trail_idx]);
        }
        if (use_crlf) {
            try out.appendSlice(allocator, "\r\n");
        } else {
            try out.append(allocator, '\n');
        }
    }

    if (inject_raw_corrupt and out.items.len > 8) {
        const mut_snippet = UNICODE_MUTATION_SNIPPETS[random.uintLessThan(usize, UNICODE_MUTATION_SNIPPETS.len)];
        const insert_at = random.uintLessThan(usize, out.items.len);
        try out.insertSlice(allocator, insert_at, mut_snippet);
    }

    return .{
        .source = try out.toOwnedSlice(allocator),
        .is_pure_valid_seed = is_pure_valid,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_fuzz_dr25_suppression_glob_and_fixer_no_panic" {
    const allocator = std.testing.allocator;
    var prng = std.Random.Xoroshiro128.init(0xD225_111C_F022_0044);
    const random = prng.random();

    // [1] Fuzz `CompiledGlob64` compilation & Windows `\` / POSIX `/` path matching (`0` panics, `0` leaks):
    var glob_i: usize = 0;
    while (glob_i < GLOB_FUZZ_ITERATIONS) : (glob_i += 1) {
        var arena = BumpArena.init(allocator);
        defer arena.deinit();
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        const base_pat = GLOB_FRAGMENTS[random.uintLessThan(usize, GLOB_FRAGMENTS.len)];
        var pat_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer pat_buf.deinit(allocator);
        try pat_buf.appendSlice(allocator, base_pat);

        if (random.uintLessThan(u8, 4) == 0 and pat_buf.items.len > 2) {
            const cut = random.uintLessThan(usize, pat_buf.items.len);
            pat_buf.items.len = cut;
        }

        if (try pkg_manifest.compileGlob64(&arena, &interner, pat_buf.items, Span.ZERO, &sink)) |compiled| {
            for (CANDIDATE_PATHS) |cand_path| {
                const first_hit = compiled.matchesPath(cand_path);
                // Deterministic replay & slash-normalization parity:
                const flipped = try allocator.dupe(u8, cand_path);
                defer allocator.free(flipped);
                for (flipped) |*ch_ptr| {
                    if (ch_ptr.* == '\\') ch_ptr.* = '/';
                }
                try std.testing.expectEqual(first_hit, compiled.matchesPath(flipped));
            }
        }
    }

    // [2] Fuzz 4-scope `SuppressionTable`, Unicode/Trojan lexing, CLI `--only`/`--disable`, & `applyCheckFixesOnDb`:
    var iter: usize = 0;
    while (iter < SUPPRESSION_FIXER_FUZZ_ITERATIONS) : (iter += 1) {
        const mutated = try buildMutatedLintSource(allocator, random);
        defer allocator.free(mutated.source);

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var vfs_map = VfsSourceMap.init(allocator, &interner);
        defer vfs_map.deinit(std.testing.io);
        var db = try CompilerDb.init(allocator);
        defer db.deinit();

        const target = if (random.uintLessThan(u8, 4) == 0)
            TargetSpec.WASM32_UNKNOWN_WASI
        else
            TargetSpec.X86_64_LINUX_GNU;
        db.setTargetSpec(target);

        const fid = try vfs_map.setOverlay("D:/ws/src/fuzz_case.cx", mutated.source, .root);
        try db.setFilePackageId(fid, .root);
        try db.setFilePath(fid, "D:/ws/src/fuzz_case.cx");
        _ = try db.setInput(fid, mutated.source, .low);

        const settings: lint_filter.LintSettings = .{
            .min_grouped_int_digits = if (random.boolean()) 5 else 6,
            .require_suppression_reason = random.boolean(),
        };
        try db.setPackageLintSemanticSettings(.root, settings, null);
        try db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);

        if (random.uintLessThan(u8, 5) == 0) {
            const r_a: RuleId = @fromBackingInt(@intCast(random.uintLessThan(u8, 44)));
            const r_b: RuleId = @fromBackingInt(@intCast(random.uintLessThan(u8, 44)));
            db.setCliLintFilter(.{
                .has_only = random.boolean(),
                .only_mask = r_a.bit() | r_b.bit(),
                .disable_mask = if (random.boolean()) r_b.bit() else 0,
            });
        }

        const pre_sink = try db.projectFileDiagnostics(fid);
        const had_baseline_errors = pre_sink.hasErrors();
        for (pre_sink.asSlice()) |diag_item| {
            if (diag_item.code.asLintRuleId() != null) {
                // Every built-in lint rule (`0..43`) MUST emit `Severity.warning`, never `.err`!
                try std.testing.expectEqual(Severity.warning, diag_item.severity);
            }
        }

        const allow_unsafe = random.boolean();
        const fix_report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .vfs = &vfs_map,
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = allow_unsafe,
        });
        try std.testing.expect(fix_report.pass_count <= check_audit.MAX_CHECK_FIX_PASSES);

        if (!had_baseline_errors and !fix_report.is_rolled_back) {
            const post_sink = try db.projectFileDiagnostics(fid);
            try std.testing.expectEqual(@as(u32, 0), post_sink.error_count);

            const after_pass1 = try allocator.dupe(u8, try db.getSourceText(fid));
            defer allocator.free(after_pass1);

            // Verify strict idempotent fixed-point convergence on immediate re-run (`<= 2` passes, `0` new edits):
            const second_report = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
                .vfs = &vfs_map,
                .candidate_files = &.{fid},
                .allow_unsafe_fixes = allow_unsafe,
            });
            try std.testing.expect(!second_report.is_rolled_back);
            try std.testing.expectEqual(@as(u32, 0), second_report.applied_fix_count);
            try std.testing.expectEqual(@as(u32, 0), second_report.modified_file_count);
            try std.testing.expect(second_report.pass_count <= 2);
            try std.testing.expectEqualStrings(after_pass1, try db.getSourceText(fid));
        }
    }
}

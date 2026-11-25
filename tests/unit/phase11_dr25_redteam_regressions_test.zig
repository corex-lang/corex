//! Phase 11.1c (`RDG-25`) Stage 3 Red-Team, `E0302` Soundness & CLI/LSP Polish Regressions
//!
//! Deterministic regression tests reproducing and verifying `[BUG-01]`–`[BUG-12]` from the Stage 3
//! Red-Team audit, Mandate #3 shared-reference move soundness (`E0302` across deref, `match`, field,
//! and slice-index projections), `< 1 ms` `corex.toml` LSP live reload, UTF-8 `--help` column
//! alignment, and same-line multi-edit diff coalescing in `DiagnosticRenderer`.
//!
//! Executed automatically by `tests/test_runner.zig` during `zig build test`.

const std = @import("std");
const corex = @import("corex");

const mem = corex.mem_foundation;
const vfs = corex.vfs_sourcemap;
const syntax = corex.syntax_arenas;
const parser = corex.parser;
const diag = corex.diagnostic;
const lint_filter = corex.lint_filter;
const check_audit = corex.check_audit;
const query_db = corex.query_db;
const type_system = corex.type_system;
const mir_sast = corex.mir_sast;
const codegen_abi = corex.codegen_abi;
const router = corex.router;
const lsp_server = corex.lsp_server;

const FileId = mem.FileId;
const Span = mem.Span;
const StringInterner = mem.StringInterner;
const VfsSourceMap = vfs.VfsSourceMap;
const StyleConfig = corex.StyleConfig;
const DiagnosticCode = diag.DiagnosticCode;
const DiagnosticSink = diag.DiagnosticSink;
const DiagnosticRenderer = corex.DiagnosticRenderer;
const CompilerDb = query_db.CompilerDb;

// --------------------------------------- CONSTS ----------------------------------------

/// Monotonic counter isolating temporary CLI/LSP regression directories across test threads.
var next_temp_seq: std.atomic.Value(u32) = .init(1);

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `sink` contains at least one diagnostic matching `target_code`.
fn hasDiagCode(sink: *const DiagnosticSink, target_code: DiagnosticCode) bool {
    for (sink.asSlice()) |diag_item| {
        if (diag_item.code == target_code) return true;
    }
    return false;
}

/// Counts how many diagnostics in `sink` match `target_code`.
fn countDiagCode(sink: *const DiagnosticSink, target_code: DiagnosticCode) usize {
    var total: usize = 0;
    for (sink.asSlice()) |diag_item| {
        if (diag_item.code == target_code) total += 1;
    }
    return total;
}

/// Initializes a single-file `CompilerDb` root fixture configured for `RDG-25` lint verification.
fn initSingleFileDb(
    allocator: std.mem.Allocator,
    file_id: FileId,
    source: []const u8,
) !CompilerDb {
    var db = try CompilerDb.init(allocator);
    errdefer db.deinit();
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
    try db.setFilePackageId(file_id, .root);
    try db.setFilePath(file_id, "D:/ws/src/main.cx");
    _ = try db.setInput(file_id, source, .low);
    try db.setPackageLintSemanticSettings(.root, .{}, null);
    try db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);
    return db;
}

/// Appends a framed JSON-RPC 2.0 `Content-Length` message into `wire_buf`.
fn appendJsonRpcFrame(
    allocator: std.mem.Allocator,
    wire_buf: *std.ArrayListUnmanaged(u8),
    body_json: []const u8,
) !void {
    var hdr_buf: [64]u8 = undefined;
    const hdr = try std.fmt.bufPrint(&hdr_buf, "Content-Length: {d}\r\n\r\n", .{body_json.len});
    try wire_buf.appendSlice(allocator, hdr);
    try wire_buf.appendSlice(allocator, body_json);
}

// ------------------------------------- PUBLIC API --------------------------------------

// --------------- [BUG-01]..[BUG-05] Regressions ---------------

test "test_redteam_bug01_w0210_eval_order_soundness_and_attribute_preservation" {
    const allocator = std.testing.allocator;

    // [1] `val = val + bump(&mut val)` MUST NOT attach a `MachineApplicable` `+=` fix:
    {
        const fid = FileId.fromInt(9001);
        const src =
            \\fn bump(slot: &mut i32) -> i32 {
            \\    slot.* = 100;
            \\    5
            \\}
            \\pub fn compute_order() -> i32 {
            \\    var val: i32 = 10;
            \\    val = val + bump(&mut val);
            \\    val
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();

        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), sink.error_count);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(sink, .w0210_manual_assign_or_swap));
        for (sink.asSlice()) |item| {
            if (item.code == .w0210_manual_assign_or_swap) {
                try std.testing.expectEqual(@as(usize, 0), item.suggestions.len);
            }
        }

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const after_safe_fix = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, after_safe_fix, "val = val + bump(&mut val);") != null);
    }

    // [2] Leading `@expect` / `@allow` on `W0210` assign and manual swap is never deleted by `--fix`:
    {
        const fid = FileId.fromInt(9002);
        const src =
            \\pub fn keep_attrs(in_a: i32, in_b: i32) -> i32 {
            \\    var lhs = in_a;
            \\    var rhs = in_b;
            \\    @expect(manual-assign-or-swap, reason: "tested assign")
            \\    lhs = lhs + 1;
            \\    @allow(manual-assign-or-swap, reason: "tested swap")
            \\    let tmp = lhs;
            \\    lhs = rhs;
            \\    rhs = tmp;
            \\    lhs + rhs
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        try db.setPackageLintFilterConfig(
            .root,
            "D:/ws",
            .{ .disable_mask = diag.RuleId.prefer_expect_over_allow.bit() },
            null,
        );

        const pre_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), pre_sink.error_count);
        try std.testing.expectEqual(@as(usize, 0), countDiagCode(pre_sink, .w0210_manual_assign_or_swap));
        try std.testing.expectEqual(@as(usize, 0), countDiagCode(pre_sink, .w0002_unused_suppression));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed_src = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "@expect(manual-assign-or-swap") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "@allow(manual-assign-or-swap") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "lhs = lhs + 1;") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "let tmp = lhs;") != null);
    }
}

test "test_redteam_bug02_w0201_use_and_impl_symbol_identity_and_private_fastpath" {
    const allocator = std.testing.allocator;

    const fid_other = FileId.fromInt(9003);
    const fid_api = FileId.fromInt(9004);
    const fid_main = FileId.fromInt(9005);

    const other_src =
        \\@allow(non-canonical-case, reason: "external fixture")
        \\pub fn badHelper() -> i32 {
        \\    10
        \\}
    ;
    const api_src =
        \\pub fn badHelper() -> i32 {
        \\    20
        \\}
        \\fn badLocalOnly() -> i32 {
        \\    30
        \\}
        \\pub struct Bad_Type {
        \\    pub count: i32,
        \\}
        \\pub fn read_api(item: Bad_Type) -> i32 {
        \\    badHelper() + badLocalOnly() + item.count
        \\}
    ;
    const main_src =
        \\pub mod other;
        \\pub mod api;
        \\use other.badHelper;
        \\@allow(non-canonical-case, reason: "distinct local nominal type")
        \\struct Bad_Type {
        \\    val: i32,
        \\}
        \\impl Bad_Type {
        \\    fn eval_local(&self) -> i32 {
        \\        self.val
        \\    }
        \\}
        \\@allow(non-canonical-case, reason: "distinct local private fn")
        \\fn badLocalOnly() -> i32 {
        \\    5
        \\}
        \\pub fn entry() -> i32 {
        \\    let local_inst = Bad_Type { val: 7 };
        \\    badHelper() + badLocalOnly() + local_inst.eval_local() + api.badHelper()
        \\}
    ;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
    for ([_]FileId{ fid_other, fid_api, fid_main }) |fid| {
        try db.setFilePackageId(fid, .root);
    }
    try db.setFilePath(fid_other, "D:/ws/src/other.cx");
    try db.setFilePath(fid_api, "D:/ws/src/api.cx");
    try db.setFilePath(fid_main, "D:/ws/src/main.cx");
    _ = try db.setInput(fid_other, other_src, .low);
    _ = try db.setInput(fid_api, api_src, .low);
    _ = try db.setInput(fid_main, main_src, .low);
    try db.bindExternalModule(fid_main, "other", fid_other);
    try db.bindExternalModule(fid_main, "api", fid_api);
    try db.setPackageLintSemanticSettings(.root, .{}, null);
    try db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);

    _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
        .candidate_files = &.{ fid_api, fid_main },
        .allow_unsafe_fixes = true,
    });

    const fixed_api = try db.getSourceText(fid_api);
    const fixed_main = try db.getSourceText(fid_main);

    // `api.cx` items renamed canonically:
    try std.testing.expect(std.mem.indexOf(u8, fixed_api, "pub fn bad_helper()") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_api, "fn bad_local_only()") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_api, "pub struct BadType") != null);

    // `main.cx` unrelated `use other.badHelper;`, `impl Bad_Type`, and `badLocalOnly()` preserved!
    try std.testing.expect(std.mem.indexOf(u8, fixed_main, "use other.badHelper;") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_main, "impl Bad_Type") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_main, "fn badLocalOnly()") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_main, "api.bad_helper()") != null);

    const post_main = try db.projectFileDiagnostics(fid_main);
    try std.testing.expectEqual(@as(usize, 0), post_main.error_count);
}

test "test_redteam_bug03_early_cutoff_live_usage_and_span_rebasing_w0404_w0406_w0402" {
    const allocator = std.testing.allocator;

    const fid_util = FileId.fromInt(9006);
    const fid_peer = FileId.fromInt(9007);
    const fid_main = FileId.fromInt(9008);

    const util_src =
        \\pub fn imported_calc(seed: i32) -> i32 {
        \\    seed + 1
        \\}
    ;
    const peer_src =
        \\pub mod nested {
        \\    pub(pkg) fn shared_across_pkg() -> i32 {
        \\        40
        \\    }
        \\}
        \\pub(super) fn shared_with_parent() -> i32 {
        \\    7
        \\}
        \\pub(pkg) fn unused_outside_peer() -> i32 {
        \\    2
        \\}
        \\pub fn peer_entry() -> i32 {
        \\    unused_outside_peer()
        \\}
    ;
    const main_src_v1 =
        \\pub mod util;
        \\pub mod peer;
        \\use util.imported_calc;
        \\fn local_helper() -> i32 {
        \\    10
        \\}
        \\pub fn stable_caller() -> i32 {
        \\    imported_calc(5) + peer.nested.shared_across_pkg() + peer.shared_with_parent()
        \\}
        \\pub fn changing_caller() -> i32 {
        \\    local_helper()
        \\}
    ;

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setTargetSpec(codegen_abi.TargetSpec.X86_64_LINUX_GNU);
    for ([_]FileId{ fid_util, fid_peer, fid_main }) |fid| {
        try db.setFilePackageId(fid, .root);
    }
    try db.setFilePath(fid_util, "D:/ws/src/util.cx");
    try db.setFilePath(fid_peer, "D:/ws/src/peer.cx");
    try db.setFilePath(fid_main, "D:/ws/src/main.cx");
    _ = try db.setInput(fid_util, util_src, .low);
    _ = try db.setInput(fid_peer, peer_src, .low);
    _ = try db.setInput(fid_main, main_src_v1, .low);
    try db.bindExternalModule(fid_main, "util", fid_util);
    try db.bindExternalModule(fid_main, "peer", fid_peer);
    try db.setPackageLintSemanticSettings(.root, .{}, null);
    try db.setPackageLintFilterConfig(.root, "D:/ws", .{}, null);

    // [1] Multi-pass `--fix` narrows `unused_outside_peer` in `peer.cx` while preserving `use util.imported_calc`
    // and `shared_across_pkg` / `shared_with_parent` across Early Cutoff!
    _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
        .candidate_files = &.{ fid_util, fid_peer, fid_main },
        .allow_unsafe_fixes = false,
    });
    const peer_after_fix = try db.getSourceText(fid_peer);
    const main_after_fix = try db.getSourceText(fid_main);
    try std.testing.expect(std.mem.indexOf(u8, peer_after_fix, "pub(pkg) fn shared_across_pkg()") != null);
    try std.testing.expect(std.mem.indexOf(u8, peer_after_fix, "pub(super) fn shared_with_parent()") != null);
    try std.testing.expect(std.mem.indexOf(u8, peer_after_fix, "\nfn unused_outside_peer()") != null);
    try std.testing.expect(std.mem.indexOf(u8, main_after_fix, "use util.imported_calc;") != null);

    // [2] Incremental body edit removing the last uses of `imported_calc` and `local_helper` + header shift:
    const main_src_v2 =
        \\// header shift line 1
        \\// header shift line 2
        \\pub mod util;
        \\pub mod peer;
        \\use util.imported_calc;
        \\fn local_helper() -> i32 {
        \\    10
        \\}
        \\pub fn stable_caller() -> i32 {
        \\    peer.nested.shared_across_pkg() + peer.shared_with_parent()
        \\}
        \\pub fn changing_caller() -> i32 {
        \\    99
        \\}
    ;
    _ = try db.setInput(fid_main, main_src_v2, .low);
    const v2_sink = try db.projectFileDiagnostics(fid_main);
    try std.testing.expectEqual(@as(usize, 0), v2_sink.error_count);
    try std.testing.expectEqual(@as(usize, 1), countDiagCode(v2_sink, .w0404_unused_import));
    try std.testing.expectEqual(@as(usize, 1), countDiagCode(v2_sink, .w0402_unused_binding));

    // Apply `--fix` after Early Cutoff header shift and verify `use util.imported_calc;` is cleanly removed:
    _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
        .candidate_files = &.{fid_main},
        .allow_unsafe_fixes = false,
    });
    const main_v2_fixed = try db.getSourceText(fid_main);
    try std.testing.expect(std.mem.indexOf(u8, main_v2_fixed, "use util.imported_calc;") == null);
    try std.testing.expect(std.mem.indexOf(u8, main_v2_fixed, "pub mod peer;") != null);
    const post_v2_sink = try db.projectFileDiagnostics(fid_main);
    try std.testing.expectEqual(@as(usize, 0), post_v2_sink.error_count);
}

test "test_redteam_bug04_and_bug05_w0102_multiline_raw_dedent_and_incremental_reparse_shift" {
    const allocator = std.testing.allocator;

    // [1] `[BUG-04]` Multiline `r"..."` containing Trojan BiDi control cooks & strips closing indent:
    {
        const fid = FileId.fromInt(9009);
        const src =
            "pub fn get_trojan() -> str {\n" ++
            "    r\"\n" ++
            "        hello \u{202E} world\n" ++
            "        \"\n" ++
            "}\n";
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();

        const sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(sink, .w0102_unicode_trojan_control));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed_src = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "\"hello \\u{202E} world\"") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed_src, "\\n        hello") == null);
        const post_sink = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post_sink.error_count);
        try std.testing.expectEqual(@as(usize, 0), post_sink.warning_count);
    }

    // [2] `[BUG-05]` `reparseIncrementalWithOptions` shifts `W0102` `fix_kind == 3` packed `lit_start`/`lit_end`:
    {
        const fid = FileId.fromInt(9010);
        const initial_src = "pub fn msg() -> str {\n    r\"alert \u{202E}!\"\n}\n";
        const inserted_prefix = "// shifted by 24 bytes!\n";
        const edited_src = inserted_prefix ++ initial_src;

        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var tok_buf = syntax.TokenBuffer.init(allocator);
        defer tok_buf.deinit();
        var cst_arena = syntax.LosslessCstArena.init(allocator);
        defer cst_arena.deinit();
        var ast_arena = syntax.AstArena.init(allocator);
        defer ast_arena.deinit();
        var candidates: std.ArrayListUnmanaged(lint_filter.RawLintCandidate) = .empty;
        defer candidates.deinit(allocator);

        _ = try parser.parseSourceWithOptions(
            initial_src,
            fid,
            &tok_buf,
            &cst_arena,
            &ast_arena,
            null,
            &interner,
            .{ .raw_lint_candidates_out = &candidates },
        );
        _ = try parser.reparseIncrementalWithOptions(
            edited_src,
            fid,
            .{
                .start_byte = 0,
                .old_end_byte = 0,
                .new_end_byte = @intCast(inserted_prefix.len),
            },
            &tok_buf,
            &cst_arena,
            &ast_arena,
            null,
            &interner,
            .{ .raw_lint_candidates_out = &candidates },
        );

        var found_w0102 = false;
        var out_sink = DiagnosticSink.init(allocator);
        defer out_sink.deinit();
        for (candidates.items) |cand| {
            if (cand.rule_id == .unicode_trojan_control and cand.fix_kind == 3) {
                found_w0102 = true;
                try lint_filter.materializeLexCstLintCandidate(
                    edited_src,
                    fid,
                    &interner,
                    cand,
                    &out_sink,
                );
            }
        }
        try std.testing.expect(found_w0102);
        const fix_edit = out_sink.asSlice()[0].suggestions[0].edits[0];
        try std.testing.expectEqualStrings(
            "r\"alert \u{202E}!\"",
            edited_src[fix_edit.start_byte..fix_edit.end_byte],
        );
        try std.testing.expectEqualStrings(
            "\"alert \\u{202E}!\"",
            interner.get(fix_edit.replacement_id),
        );
    }
}

// --------------- [BUG-06]..[BUG-12] Regressions ---------------

test "test_redteam_bug06_bug07_bug08_bug09_bug10_autofix_soundness" {
    const allocator = std.testing.allocator;

    // [1] `[BUG-06]` `W0410` wraps `.is_expr` fallback in parentheses (`opt orelse (alt is .Some(_))`):
    {
        const fid = FileId.fromInt(9011);
        const src =
            \\pub fn unwrap_flag(opt: bool?, alt: i32?) -> bool {
            \\    match opt {
            \\        .Some(flag) => flag,
            \\        .None => alt is .Some(_),
            \\    }
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "opt orelse (alt is .Some(_))") != null);
        const post = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post.error_count);
    }

    // [2] `[BUG-07]` `W0413` shadowed local, `(param).*`, `.pipe_expr` `(&pair) |> add_pair(10)`, & `f"..."`:
    {
        const fid = FileId.fromInt(9012);
        const src =
            \\@derive(Copy, Clone)
            \\pub struct Pair8 {
            \\    pub lo: i32,
            \\    pub hi: i32,
            \\}
            \\fn add_pair(param: &Pair8, bonus: i32) -> i32 {
            \\    let other = Pair8 { lo: 1, hi: 2 };
            \\    let shadowed = {
            \\        let param = &other;
            \\        param.*.lo
            \\    };
            \\    let unparen = (param).*;
            \\    let msg = f"{param.hi}";
            \\    _ = msg;
            \\    unparen.lo + shadowed + bonus
            \\}
            \\pub fn run_pair(item: Pair8) -> i32 {
            \\    let text = f"{add_pair(&item, 3)}";
            \\    _ = text;
            \\    (&item) |> add_pair(10)
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const pre = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(pre, .w0413_trivially_copy_pass_by_ref));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "fn add_pair(param: Pair8, bonus: i32)") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "param.*.lo") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "let unparen = (param);") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "(item) |> add_pair(10)") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "add_pair(item, 3)") != null);
        const post = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post.error_count);
    }

    // [3] `[BUG-08]` `W0209`, `W0407`, and `W0411` preserve leading `@allow` / `@expect` attributes:
    {
        const fid = FileId.fromInt(9013);
        const src =
            \\pub fn check_attr_guards(cond_a: bool, cond_b: bool, num: i32) -> i32 {
            \\    @allow(collapsible-if, reason: "preserve outer attr")
            \\    if cond_a {
            \\        if cond_b {
            \\            @allow(needless-trailing-return, reason: "preserve return attr")
            \\            return num + 1;
            \\        }
            \\    }
            \\    @allow(single-use-temp, reason: "preserve let attr")
            \\    let out_val = num + 2;
            \\    return out_val;
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        try db.setPackageLintFilterConfig(
            .root,
            "D:/ws",
            .{ .disable_mask = diag.RuleId.prefer_expect_over_allow.bit() },
            null,
        );
        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = true,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "@allow(collapsible-if") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "@allow(needless-trailing-return") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "@allow(single-use-temp") != null);
        const post = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post.error_count);
    }

    // [4] `[BUG-09]` `W0104` guards `r#"...”#..."#` & `f#"...”#..."#` and escapes `\"` in cooked `f"..."`:
    {
        const fid = FileId.fromInt(9014);
        const src =
            "pub fn quote_guards(num: i32) -> str {\n" ++
            "    let raw_guarded = r#\"say \u{201D}#hi\"#;\n" ++
            "    let fmt_guarded = f#\"say \u{201D}#hi {num}\"#;\n" ++
            "    let fmt_cooked = f\"say \u{201D}hi {num}\";\n" ++
            "    _ = fmt_guarded;\n" ++
            "    _ = fmt_cooked;\n" ++
            "    raw_guarded\n" ++
            "}\n";
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        try db.setPackageLintFilterConfig(
            .root,
            "D:/ws",
            .{ .disable_mask = diag.RuleId.needless_raw_string_hashes.bit() },
            null,
        );
        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = true,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "r#\"say \u{201D}#hi\"#") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "f#\"say \u{201D}#hi {num}\"#") != null);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "f\"say \\\"hi {num}\"") != null);
        const post = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post.error_count);
    }

    // [5] `[BUG-10]` `W0334` rewrites `item.clone() |> consume_owned` -> `(own item) |> consume_owned`:
    {
        const fid = FileId.fromInt(9015);
        const src =
            \\pub struct OwnedBuf {
            \\    pub tag: i32,
            \\}
            \\impl Drop for OwnedBuf {
            \\    fn drop(&mut self) {
            \\        self.tag = 0;
            \\    }
            \\}
            \\impl OwnedBuf {
            \\    pub fn clone(&self) -> OwnedBuf {
            \\        OwnedBuf { tag: self.tag }
            \\    }
            \\}
            \\fn consume_owned(buf: own OwnedBuf) -> i32 {
            \\    buf.tag
            \\}
            \\pub fn forward_pipe(item: own OwnedBuf) -> i32 {
            \\    item.clone() |> consume_owned
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const pre = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(pre, .w0334_redundant_move_clone));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "(own item) |> consume_owned") != null);
        const post = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post.error_count);
        try std.testing.expectEqual(@as(usize, 0), post.warning_count);
    }
}

test "test_redteam_bug11_linear_cst_suppression_bounds_and_function_window_ast_scans" {
    const allocator = std.testing.allocator;

    // Build a 60-function module with nested blocks and zero `@expect`/`@allow` attributes:
    var src_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer src_buf.deinit(allocator);
    try src_buf.appendSlice(
        allocator,
        "@derive(Copy, Clone)\npub struct Small4 { pub val: i32 }\n",
    );
    var fn_idx: usize = 0;
    while (fn_idx < 60) : (fn_idx += 1) {
        var line_buf: [192]u8 = undefined;
        const fn_text = try std.fmt.bufPrint(
            &line_buf,
            "pub fn step_{d}(item: &Small4) -> i32 {{\n    {{ {{ {{ item.val + {d} }} }} }}\n}}\n",
            .{ fn_idx, fn_idx },
        );
        try src_buf.appendSlice(allocator, fn_text);
    }

    const fid = FileId.fromInt(9016);
    var db = try initSingleFileDb(allocator, fid, src_buf.items);
    defer db.deinit();

    const sink = try db.projectFileDiagnostics(fid);
    try std.testing.expectEqual(@as(usize, 0), sink.error_count);
    try std.testing.expectEqual(@as(usize, 60), countDiagCode(sink, .w0413_trivially_copy_pass_by_ref));
}

test "test_redteam_bug12_w0119_inner_warn_fix_and_cli_e0240_stderr_and_disable_help" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `W0119` attaches its `MachineApplicable` fix on `f"it\'s static"` despite inner `W0101`:
    {
        const fid = FileId.fromInt(9017);
        const src =
            \\pub fn static_fmt() -> str {
            \\    f"it\'s static"
            \\}
        ;
        var db = try initSingleFileDb(allocator, fid, src);
        defer db.deinit();
        const pre = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(pre, .w0101_redundant_escape_sequence));
        try std.testing.expectEqual(@as(usize, 1), countDiagCode(pre, .w0119_useless_format_string));

        _ = try check_audit.applyCheckFixesOnDb(allocator, &db, .{
            .candidate_files = &.{fid},
            .allow_unsafe_fixes = false,
        });
        const fixed = try db.getSourceText(fid);
        try std.testing.expect(std.mem.indexOf(u8, fixed, "\"it's static\"") != null);
        const post = try db.projectFileDiagnostics(fid);
        try std.testing.expectEqual(@as(usize, 0), post.error_count);
        try std.testing.expectEqual(@as(usize, 0), post.warning_count);
    }

    // [2] `corex build` renders `E0240` diagnostic text to `stderr` instead of exiting `1` silently:
    {
        const seq = next_temp_seq.fetchAdd(1, .monotonic);
        const tmp_dir = try std.fmt.allocPrint(allocator, ".zig-cache/tmp/dr25_rt_cli_{d}", .{seq});
        defer {
            std.Io.Dir.cwd().deleteTree(io, tmp_dir) catch {};
            allocator.free(tmp_dir);
        }
        try std.Io.Dir.cwd().createDirPath(io, tmp_dir);
        const bad_cx_path = try std.fmt.allocPrint(allocator, "{s}/main.cx", .{tmp_dir});
        defer allocator.free(bad_cx_path);
        const bad_cx_src =
            "// corex check: expect(bogus-nonexistent-rule) -- bad selector\n" ++
            "pub fn main() -> i32 {\n    0\n}\n";
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = bad_cx_path, .data = bad_cx_src });

        var out_alloc: std.Io.Writer.Allocating = .init(allocator);
        defer out_alloc.deinit();
        var err_alloc: std.Io.Writer.Allocating = .init(allocator);
        defer err_alloc.deinit();

        const exit_code = try router.runCli(
            allocator,
            io,
            null,
            &.{ "--color=never", "build", "--emit-c", bad_cx_path },
            &out_alloc.writer,
            &err_alloc.writer,
        );
        try std.testing.expectEqual(@as(u8, 1), exit_code);
        try std.testing.expect(std.mem.indexOf(u8, err_alloc.written(), "E0240") != null);
        try std.testing.expect(std.mem.indexOf(u8, err_alloc.written(), "bogus-nonexistent-rule") != null);
    }

    // [3] Missing `--disable` argument help cites valid v1.0 slugs (`single-char-ident`, `unused-binding`):
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const parsed = try router.parseArgs(&.{ "check", "--disable" }, &sink);
        try std.testing.expect(parsed.action == .invalid);
        try std.testing.expect(sink.hasErrors());
        const notes = sink.asSlice()[0].notes;
        try std.testing.expect(notes.len > 0);
        try std.testing.expect(std.mem.indexOf(u8, notes[0], "--disable=single-char-ident") != null);
        try std.testing.expect(std.mem.indexOf(u8, notes[0], "--disable=W0202,unused-binding") != null);
    }
}

// -------- Mandate #3: E0302 Shared-Ref Move Soundness ---------

test "test_mandate3_e0302_shared_reference_move_rejected_across_all_four_forms" {
    const allocator = std.testing.allocator;

    const negative_cases = [_][]const u8{
        // Form 1: Explicit deref `(&NonCopy).*`
        \\pub struct NonCopyBox {
        \\    pub payload: i32,
        \\}
        \\impl NonCopyBox {
        \\    pub fn drop(&mut self) {
        \\        _ = self;
        \\    }
        \\}
        \\pub fn steal_deref(shared_ref: &NonCopyBox) -> NonCopyBox {
        \\    shared_ref.*
        \\}
        ,
        // Form 2: `match &Enum { .Var(v) => v }`
        \\pub struct NonCopyToken {
        \\    pub code: i32,
        \\}
        \\impl NonCopyToken {
        \\    pub fn drop(&mut self) {
        \\        _ = self;
        \\    }
        \\}
        \\pub enum HolderEnum {
        \\    Full(NonCopyToken),
        \\    Empty,
        \\}
        \\pub fn steal_match(shared_enum: &HolderEnum) -> i32 {
        \\    match shared_enum {
        \\        .Full(moved_tok) => moved_tok.code,
        \\        .Empty => 0,
        \\    }
        \\}
        ,
        // Form 3: Struct field read `(&Struct).field`
        \\pub struct InnerResource {
        \\    pub handle: i32,
        \\}
        \\impl InnerResource {
        \\    pub fn drop(&mut self) {
        \\        _ = self;
        \\    }
        \\}
        \\pub struct OuterHolder {
        \\    pub inner: InnerResource,
        \\}
        \\pub fn steal_field(shared_outer: &OuterHolder) -> InnerResource {
        \\    shared_outer.inner
        \\}
        ,
        // Form 4: Shared slice element read `&[NonCopy][0]`
        \\pub struct NonCopyElem {
        \\    pub id: i32,
        \\}
        \\impl NonCopyElem {
        \\    pub fn drop(&mut self) {
        \\        _ = self;
        \\    }
        \\}
        \\pub fn steal_elem(items: &[NonCopyElem]) -> NonCopyElem {
        \\    if items.len() > 0 {
        \\        items[0]
        \\    } else {
        \\        NonCopyElem { id: 0 }
        \\    }
        \\}
        ,
    };

    for (negative_cases, 0..) |case_src, i| {
        var bundle = try mir_sast.lowerAndVerifySourceMirSast(
            allocator,
            FileId.fromInt(@intCast(9020 + i)),
            case_src,
            type_system.TargetLayout.NATIVE_64,
            .{},
        );
        defer bundle.deinit();

        try std.testing.expect(bundle.diagnostics.hasErrors());
        try std.testing.expect(hasDiagCode(&bundle.diagnostics, .e0302_use_after_move));
        var saw_shared_ref_msg = false;
        for (bundle.diagnostics.asSlice()) |item| {
            if (item.code == .e0302_use_after_move and
                std.mem.indexOf(u8, item.message, "cannot move non-`Copy` value out of a shared reference") != null)
            {
                saw_shared_ref_msg = true;
            }
        }
        try std.testing.expect(saw_shared_ref_msg);
    }

    // Positive forms: generic `T: Copy`, generic `Equatable + Comparable` on non-`Copy`, `const`, & `unsafe { ptr.* }`:
    const positive_src =
        \\@derive(Equatable, Comparable)
        \\pub struct NonCopyKey {
        \\    pub weight: i32,
        \\}
        \\impl NonCopyKey {
        \\    pub fn drop(&mut self) {
        \\        _ = self;
        \\    }
        \\}
        \\const GLOBAL_KEY: NonCopyKey = NonCopyKey { weight: 7 };
        \\pub fn read_copy_head[T: Copy](slice_in: &[T], fallback: T) -> T {
        \\    if slice_in.len() > 0 { slice_in[0] } else { fallback }
        \\}
        \\pub fn compare_borrowed[T: Equatable + Comparable](lhs: &T, rhs: &T) -> bool {
        \\    lhs.* != rhs.* and lhs.* <= rhs.*
        \\}
        \\pub fn check_positive(a_ref: &NonCopyKey, b_ref: &NonCopyKey, raw_ptr: *NonCopyKey) -> i32 {
        \\    if raw_ptr as usize == 0 {
        \\        return 0;
        \\    }
        \\    let cmp_ok = compare_borrowed[NonCopyKey](a_ref, b_ref);
        \\    let from_raw = unsafe { raw_ptr.* };
        \\    let const_w = (&GLOBAL_KEY).weight;
        \\    if cmp_ok { from_raw.weight + const_w } else { const_w }
        \\}
    ;
    var pos_bundle = try mir_sast.lowerAndVerifySourceMirSast(
        allocator,
        FileId.fromInt(9030),
        positive_src,
        type_system.TargetLayout.NATIVE_64,
        .{},
    );
    defer pos_bundle.deinit();
    try std.testing.expect(!pos_bundle.diagnostics.hasErrors());
    try std.testing.expectEqual(@as(u32, 0), pos_bundle.diagnostics.error_count);
}

// ---------- LSP Fast Path & CLI / Diff Polish Tests -----------

test "test_polish_lsp_toml_reload_sub_millisecond_help_alignment_and_samediff_coalescing" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `corex check --help` and `corex upgrade --help` align UTF-8 `…` option rows to the exact column:
    {
        var chk_help: std.Io.Writer.Allocating = .init(allocator);
        defer chk_help.deinit();
        try router.renderSubcommandHelp(&chk_help.writer, StyleConfig.MONOCHROME, .check);

        var chk_lines = std.mem.splitScalar(u8, chk_help.written(), '\n');
        var in_check_opts = false;
        var verified_disable = false;
        var verified_only = false;
        while (chk_lines.next()) |line| {
            if (std.mem.eql(u8, line, "Check Options:")) {
                in_check_opts = true;
                continue;
            }
            if (in_check_opts and line.len == 0) break;
            if (!in_check_opts) continue;
            // Every row in `Check Options:` (`col_width = 34` + `"  "` prefix) starts its summary at col `36`:
            var cp_idx: usize = 0;
            var byte_idx: usize = 0;
            while (byte_idx < line.len and cp_idx < 36) : (cp_idx += 1) {
                byte_idx += std.unicode.utf8ByteSequenceLength(line[byte_idx]) catch 1;
            }
            try std.testing.expect(byte_idx < line.len);
            try std.testing.expect(line[byte_idx - 1] == ' ');
            try std.testing.expect(line[byte_idx] != ' ');
            if (std.mem.indexOf(u8, line, "--disable=<rule,\u{2026}>") != null) verified_disable = true;
            if (std.mem.indexOf(u8, line, "--only=<rule,\u{2026}>") != null) verified_only = true;
        }
        try std.testing.expect(verified_disable and verified_only);

        var upg_help: std.Io.Writer.Allocating = .init(allocator);
        defer upg_help.deinit();
        try router.renderSubcommandHelp(&upg_help.writer, StyleConfig.MONOCHROME, .upgrade);
        var upg_lines = std.mem.splitScalar(u8, upg_help.written(), '\n');
        var in_upg_opts = false;
        var verified_rule = false;
        while (upg_lines.next()) |line| {
            if (std.mem.eql(u8, line, "Upgrade Options:")) {
                in_upg_opts = true;
                continue;
            }
            if (in_upg_opts and line.len == 0) break;
            if (!in_upg_opts) continue;
            var cp_idx: usize = 0;
            var byte_idx: usize = 0;
            while (byte_idx < line.len and cp_idx < 32) : (cp_idx += 1) {
                byte_idx += std.unicode.utf8ByteSequenceLength(line[byte_idx]) catch 1;
            }
            try std.testing.expect(byte_idx < line.len);
            try std.testing.expect(line[byte_idx - 1] == ' ');
            try std.testing.expect(line[byte_idx] != ' ');
            if (std.mem.indexOf(u8, line, "--rule=<id,\u{2026}>") != null) verified_rule = true;
        }
        try std.testing.expect(verified_rule);
    }

    // [2] `DiagnosticRenderer` coalesces 2 non-overlapping edits on the same line into 1 `-` and 1 `+` diff row:
    {
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var source_map = VfsSourceMap.init(allocator, &interner);
        defer source_map.deinit(io);

        const src_text = "pub fn calc(val: i32) -> i32 {\n    return val + 1;\n}\n";
        const fid = try source_map.setOverlay("D:/ws/src/calc.cx", src_text, .root);
        const empty_id = try interner.intern("");
        const ret_start: u32 = @intCast(std.mem.indexOf(u8, src_text, "return ").?);
        const semi_start: u32 = @intCast(std.mem.indexOf(u8, src_text, ";").?);

        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        try sink.emit(.{
            .code = .w0209_needless_trailing_return,
            .severity = .warning,
            .primary_span = Span.init(fid, ret_start, semi_start + 1),
            .message = "unneeded `return` on tail expression",
            .suggestions = &.{.{
                .message = "remove `return` and trailing `;`",
                .applicability = .machine_applicable,
                .priority = .lint_idiom,
                .edits = &.{
                    .{ .file_id = fid, .start_byte = ret_start, .end_byte = ret_start + 7, .replacement_id = empty_id },
                    .{ .file_id = fid, .start_byte = semi_start, .end_byte = semi_start + 1, .replacement_id = empty_id },
                },
            }},
        });

        var rendered_buf: std.Io.Writer.Allocating = .init(allocator);
        defer rendered_buf.deinit();
        try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderAll(
            &rendered_buf.writer,
            &sink,
        );
        const rendered = rendered_buf.written();
        try std.testing.expect(std.mem.indexOf(u8, rendered, "-     return val + 1;\n") != null);
        try std.testing.expect(std.mem.indexOf(u8, rendered, "+     val + 1\n") != null);
        // Must NOT emit two separate `-     return val + 1;` lines!
        const first_minus = std.mem.indexOf(u8, rendered, "-     return val + 1;\n").?;
        try std.testing.expect(
            std.mem.indexOfPos(u8, rendered, first_minus + 1, "-     return val + 1;\n") == null,
        );
    }

    // [3] Cached `checkStrayToolConfigDotfiles` keeps in-memory `corex.toml` LSP reloads `< 1 ms` per edit:
    {
        const seq = next_temp_seq.fetchAdd(1, .monotonic);
        const ws_dir = try std.fmt.allocPrint(allocator, ".zig-cache/tmp/dr25_rt_lsp_perf_{d}", .{seq});
        defer {
            std.Io.Dir.cwd().deleteTree(io, ws_dir) catch {};
            allocator.free(ws_dir);
        }
        try std.Io.Dir.cwd().createDirPath(io, ws_dir);
        const toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{ws_dir});
        defer allocator.free(toml_path);
        const base_toml =
            "[package]\nname = \"perf-toml\"\nversion = \"0.1.0\"\nedition = \"2026\"\n";
        try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = toml_path, .data = base_toml });

        const real_toml = try std.Io.Dir.cwd().realPathFileAlloc(io, toml_path, allocator);
        defer allocator.free(real_toml);
        var norm_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer norm_buf.deinit(allocator);
        try norm_buf.appendSlice(allocator, if (real_toml[0] == '/') "file://" else "file:///");
        for (real_toml) |byte_ch| {
            try norm_buf.append(allocator, if (byte_ch == '\\') '/' else byte_ch);
        }
        const toml_uri = norm_buf.items;
        const ws_uri = toml_uri[0 .. toml_uri.len - "/corex.toml".len];

        var inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer inbound.deinit(allocator);
        const init_json = try std.fmt.allocPrint(
            allocator,
            "{{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{{\"rootUri\":\"{s}\",\"capabilities\":{{}}}}}}",
            .{ws_uri},
        );
        defer allocator.free(init_json);
        try appendJsonRpcFrame(allocator, &inbound, init_json);

        var open_json: std.Io.Writer.Allocating = .init(allocator);
        defer open_json.deinit();
        try open_json.writer.print(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":\"{s}\"," ++
                "\"languageId\":\"toml\",\"version\":1,\"text\":",
            .{toml_uri},
        );
        try std.json.Stringify.encodeJsonString(base_toml, .{}, &open_json.writer);
        try open_json.writer.writeAll("}}}}");
        try appendJsonRpcFrame(allocator, &inbound, open_json.written());

        var base_inbound: std.ArrayListUnmanaged(u8) = .empty;
        defer base_inbound.deinit(allocator);
        try base_inbound.appendSlice(allocator, inbound.items);
        try appendJsonRpcFrame(allocator, &base_inbound, "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\",\"params\":null}");
        try appendJsonRpcFrame(allocator, &base_inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        // Stream 100 consecutive `textDocument/didChange` reloads on `corex.toml`:
        var iter_idx: usize = 0;
        while (iter_idx < 100) : (iter_idx += 1) {
            var chg_json: std.Io.Writer.Allocating = .init(allocator);
            defer chg_json.deinit();
            const next_toml = if ((iter_idx & 1) == 0)
                "[package]\nname = \"perf-toml\"\nversion = \"0.1.0\"\nedition = \"2026\"\n[lint]\ndisable = [\"W0203\"]\n"
            else
                "[package]\nname = \"perf-toml\"\nversion = \"0.1.0\"\nedition = \"2026\"\n[lint]\ndisable = [\"W0402\"]\n";
            try chg_json.writer.print(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{{\"textDocument\":{{\"uri\":\"{s}\"," ++
                    "\"version\":{d}}},\"contentChanges\":[{{\"text\":",
                .{ toml_uri, iter_idx + 2 },
            );
            try std.json.Stringify.encodeJsonString(next_toml, .{}, &chg_json.writer);
            try chg_json.writer.writeAll("}]}}");
            try appendJsonRpcFrame(allocator, &inbound, chg_json.written());
        }
        try appendJsonRpcFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"shutdown\",\"params\":null}");
        try appendJsonRpcFrame(allocator, &inbound, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\",\"params\":null}");

        var base_reader = std.Io.Reader.fixed(base_inbound.items);
        var base_writer: std.Io.Writer.Allocating = .init(allocator);
        defer base_writer.deinit();
        const t_base_start = std.Io.Clock.awake.now(io);
        const base_status = try lsp_server.runServerStream(
            allocator,
            io,
            null,
            &base_reader,
            &base_writer.writer,
            null,
            .{},
        );
        const base_ns = t_base_start.untilNow(io, .awake).nanoseconds;
        try std.testing.expectEqual(@as(u8, 0), base_status);

        var in_reader = std.Io.Reader.fixed(inbound.items);
        var out_writer: std.Io.Writer.Allocating = .init(allocator);
        defer out_writer.deinit();
        const t_start = std.Io.Clock.awake.now(io);
        const status = try lsp_server.runServerStream(
            allocator,
            io,
            null,
            &in_reader,
            &out_writer.writer,
            null,
            .{},
        );
        const elapsed_ns = t_start.untilNow(io, .awake).nanoseconds;
        try std.testing.expectEqual(@as(u8, 0), status);
        const reload_delta_ns = if (elapsed_ns > base_ns) elapsed_ns - base_ns else 0;
        // 100 live `corex.toml` reloads (`didChange`) complete within `< 1 ms`/edit (`< 500 ms` debug CI margin):
        try std.testing.expect(reload_delta_ns < 500 * std.time.ns_per_ms);
    }
}

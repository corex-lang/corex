//! Golden Snapshot Verification Suite (`tests/snapshots/snapshot_test.zig`)
//!
//! Compares rendered CLI help menus, single-line diagnostics, multi-line region diagnostics,
//! cross-file stitched diagnostics, CLI typo diagnostics, lexer token/trivia streams, parser
//! CST/AST trees and diagnostics, `corex fmt` / `corex fmt --fix` formatting outputs,
//! `CompilerDb` Early Cutoff / `ItemTree` firewall reports, Phase 5 `HIR` desugaring,
//! Block-Argument SSA `MIR` (`--dev` vs `--release`, monomorphization, `LayoutShapeKey` dedup,
//! and `R6` `ICF`), multi-frame `comptime` / `W0501` diagnostics, and Phase 6 `SAST` ownership/
//! borrow/escape/bounds diagnostics, capability witness chains, and `MIR` drop elaboration
//! against golden `.snap` files.
//!
//! Normalizes `CRLF` (`\r\n`) to `LF` (`\n`) when loading `.snap` files so snapshots match across OSes.

const std = @import("std");
const corex = @import("corex");

const router = corex.router;
const fmt_engine = corex.fmt_engine;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const CstNodeIndex = corex.CstNodeIndex;
const NodeIndex = corex.NodeIndex;
const Span = corex.Span;
const StringInterner = corex.StringInterner;
const VfsSourceMap = corex.VfsSourceMap;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const Lexer = corex.Lexer;
const Parser = corex.Parser;
const QueryKey = corex.QueryKey;
const CompilerDb = corex.CompilerDb;
const StyleConfig = corex.StyleConfig;
const DiagnosticSink = corex.DiagnosticSink;
const LabeledSpan = corex.LabeledSpan;
const DiagnosticRenderer = corex.DiagnosticRenderer;

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical Phase 6 diagnostic codes verified across SAST unit and golden snapshot suites (`DR-06`, `DR-17`, `DR-20`).
const PHASE6_DIAGNOSTIC_CODES = [_]corex.DiagnosticCode{
    .e0301_use_after_free,
    .e0302_use_after_move,
    .e0303_uninitialized_memory_read,
    .e0304_resource_or_memory_leak,
    .e0305_exclusivity_violation,
    .e0306_region_escape_violation,
    .e0307_static_buffer_overflow,
    .w0308_unused_region_allocation,
    .e0313_double_free_or_close,
    .w0314_unproven_bounds_access,
    .e0315_wire_layout_contract_violation,
    .e0316_max_stack_budget_exceeded,
    .e0320_no_alloc_contract_violation,
    .e0321_no_panic_contract_violation,
    .e0322_no_block_contract_violation,
    .e0323_trait_impl_effect_escalation,
    .e0324_package_capability_violation,
    .e0325_comptime_sandbox_violation,
    .e0326_embed_path_escape,
    .e0327_forbidden_sandbox_bypass_attribute,
    .e0328_scratch_arena_ping_pong_conflict,
    .w0329_vacated_projection_panic_abort,
    .w0330_ambient_dead_capability_in_dep,
};

// -------------------------------------- INTERNALS --------------------------------------

/// Reads `snap_path` from disk, normalizes `\r\n` to `\n`, and asserts exact equality with `actual_output`.
fn expectMatchesSnapshotFile(
    allocator: std.mem.Allocator,
    io: std.Io,
    snap_path: []const u8,
    actual_output: []const u8,
) !void {
    const raw_snap = try std.Io.Dir.cwd().readFileAlloc(io, snap_path, allocator, .limited(256 * 1024));
    defer allocator.free(raw_snap);

    var normalized_snap: std.ArrayList(u8) = .empty;
    defer normalized_snap.deinit(allocator);
    try normalized_snap.ensureTotalCapacity(allocator, raw_snap.len);

    for (raw_snap) |byte_val| {
        if (byte_val != '\r') {
            normalized_snap.appendAssumeCapacity(byte_val);
        }
    }
    try std.testing.expectEqualStrings(normalized_snap.items, actual_output);
}

/// Asserts that `sink` recorded zero errors, printing any unexpected diagnostics on failure.
fn expectZeroDiagErrors(sink: *const DiagnosticSink) !void {
    if (sink.hasErrors()) {
        for (sink.diagnostics.items) |diag_item| {
            std.debug.print(
                "Unexpected diagnostic [{s}]: {s}\n",
                .{ diag_item.code.asCodeStr(), diag_item.message },
            );
        }
    }
    try std.testing.expect(!sink.hasErrors());
}

/// Returns `true` if `sink` contains at least one diagnostic with `expected_code`.
fn hasDiagnosticCodeInSink(
    sink: *const DiagnosticSink,
    expected_code: corex.DiagnosticCode,
) bool {
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == expected_code) return true;
    }
    return false;
}

/// Registers every lowered `MirBody` inside `bundle` on `vm_engine` with its resolved `SymbolIndex`.
fn registerAllMirBodiesInVm(
    vm_engine: *corex.MirVm,
    bundle: *corex.mir.MirSourceBundle,
) !void {
    for (bundle.mir_bundle.bodies.items) |*body_ptr| {
        var sym_idx = bundle.hir_bundle.sym_table.def_to_symbol.get(
            body_ptr.def_id.asInt(),
        ) orelse corex.SymbolIndex.none;
        if (sym_idx.isNone()) {
            for (bundle.hir_bundle.hir_store.functions.items) |fn_meta| {
                if (fn_meta.name == body_ptr.name and !fn_meta.symbol_index.isNone()) {
                    sym_idx = fn_meta.symbol_index;
                    break;
                }
            }
        }
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
    }
}

/// Registers every optimized `MirBody` inside `bodies` on `vm_engine` using `sym_table` metadata.
fn registerOptimizedBodiesInVm(
    vm_engine: *corex.MirVm,
    bodies: []const corex.MirBody,
    sym_table: *const corex.SymbolTable,
) !void {
    for (bodies) |*body_ptr| {
        var sym_idx = body_ptr.symbol_index;
        if (sym_idx.isNone() and !body_ptr.def_id.isNone()) {
            sym_idx = sym_table.def_to_symbol.get(body_ptr.def_id.asInt()) orelse .none;
        }
        _ = try vm_engine.registerBody(body_ptr, sym_idx);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_snapshot_cli_help_menu" {
    var out_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try router.renderHelp(&out_writer, StyleConfig.MONOCHROME);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/cli_help.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_single_line_use_after_move" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    var src_buf: [2048]u8 = undefined;
    var src_writer = std.Io.Writer.fixed(&src_buf);
    var line_idx: usize = 1;
    while (line_idx < 40) : (line_idx += 1) {
        try src_writer.writeAll("// padding\n");
    }
    const line_40_start: u32 = @intCast(src_writer.buffered().len);
    try src_writer.writeAll("    let packet = consume_payload(buffer)\n");
    try src_writer.writeAll("    log_status(\"dispatched\")\n");
    const line_42_start: u32 = @intCast(src_writer.buffered().len);
    try src_writer.writeAll("    return read_header(buffer)\n");

    // Register with Windows backslashes to verify cross-platform `/` normalization in snapshots:
    const file_id = try source_map.setOverlay("src\\net\\socket.cx", src_writer.buffered(), .root);
    const used_span = Span.init(file_id, line_42_start + 23, line_42_start + 29);

    const labels = [_]LabeledSpan{
        .{ .span = Span.init(file_id, line_40_start + 33, line_40_start + 39), .label = "value moved here", .style = .secondary },
        .{ .span = used_span, .label = "value used here after transfer", .style = .primary },
    };
    const notes = [_][]const u8{
        "help: pass a borrowed view via `buffer.as_slice()` if `consume_payload` does not retain ownership",
    };

    var out_buf: [2048]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderDiagnostic(&out_writer, .{
        .code = .e0302_use_after_move,
        .severity = .err,
        .primary_span = used_span,
        .message = "use of moved value `buffer` after scope transfer",
        .labels = &labels,
        .notes = &notes,
    });

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_single_line.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_multi_line_region_escape" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const source_text =
        "fn build_slice() -> &[u8] {\n" ++
        "    region scratch {\n" ++
        "        let buf = scratch.alloc(64);\n" ++
        "        return buf.as_slice();\n" ++
        "    }\n" ++
        "}\n";
    const region_span = Span.init(try source_map.setOverlay("src/mem/region.cx", source_text, .root), 32, 122);

    var out_buf: [2048]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderDiagnostic(&out_writer, .{
        .code = .e0306_region_escape_violation,
        .severity = .err,
        .primary_span = region_span,
        .message = "value escapes lexical arena or stack region",
        .labels = &.{.{
            .span = region_span,
            .label = "region `scratch` ends here before returned slice is consumed",
            .style = .primary,
        }},
        .notes = &.{"help: allocate in caller-provided arena or return an owned container"},
    });

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_multi_line.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_cross_file_type_mismatch" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const main_src =
        "use net::http::connect;\n" ++
        "fn start() {\n" ++
        "    connect(\"8080\");\n" ++
        "}\n";
    const call_arg_span = Span.init(
        try source_map.setOverlay("src\\app\\main.cx", main_src, .root),
        49,
        55,
    );
    const param_decl_span = Span.init(
        try source_map.setOverlay("src\\net\\http.cx", "pub fn connect(port: u16) {\n}\n", .root),
        15,
        24,
    );

    var out_buf: [2048]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderDiagnostic(&out_writer, .{
        .code = .e0401_type_mismatch,
        .severity = .err,
        .primary_span = call_arg_span,
        .message = "mismatched types in call to `connect`",
        .labels = &.{
            .{ .span = call_arg_span, .label = "expected `u16`, found `str`", .style = .primary },
            .{ .span = param_decl_span, .label = "parameter `port` declared here", .style = .secondary },
        },
        .notes = &.{"help: pass an integer literal such as `8080`"},
    });

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_cross_file.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_cli_unknown_flag_typo_suggestion" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    _ = try router.parseArgs(&.{"--hlp"}, &sink);

    var out_buf: [1024]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderAll(&out_writer, &sink);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/cli_unknown_flag.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_lexer_token_stream_and_trivia" {
    const sample_source =
        "#!/usr/bin/env corex\n" ++
        "//! Lexer snapshot module\n" ++
        "const MAX_STEPS: usize = 0x10_00;\n" ++
        "pub fn step_count(val: i32) -> Result[i32, IoError] {\n" ++
        "    for i in 0..10 {\n" ++
        "        let msg = \"step={val.max(1)} {r#\"ok\"#}\\n\";\n" ++
        "    }\n" ++
        "    return Ok(val +% 1);\n" ++
        "}\n";

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try corex.tokenize(sample_source, FileId.fromInt(0), &token_buf, &sink, null);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed = try cst_arena.reconstructSource(
        std.testing.allocator,
        sample_source,
        &token_buf,
    );
    defer std.testing.allocator.free(reconstructed);

    var out_buf: [8192]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    var i: u32 = 0;
    while (i < @as(u32, @intCast(token_buf.countTokens()))) : (i += 1) {
        const tok_id = TokenIndex.fromInt(i);
        for (token_buf.getLeadingTrivia(tok_id)) |piece| {
            try out_writer.print(
                "  lead  {s} [{d}..{d}]\n",
                .{ @tagName(piece.kind), piece.byte_offset, piece.byte_offset + piece.byte_len },
            );
        }
        const rec = token_buf.getToken(tok_id);
        const end_byte: u32 = rec.byte_offset + @as(u32, rec.byte_len);
        const lexeme = sample_source[rec.byte_offset..end_byte];
        try out_writer.print(
            "#{d:0>2} {s} [{d}..{d}] nl={s} err={s} `{s}`\n",
            .{
                i,
                @tagName(rec.kind),
                rec.byte_offset,
                end_byte,
                if (rec.flags.has_leading_newline) "1" else "0",
                if (rec.flags.has_lexer_error) "1" else "0",
                lexeme,
            },
        );
    }
    try out_writer.print(
        "lossless_roundtrip: {s}\n",
        .{if (std.mem.eql(u8, sample_source, reconstructed)) "true" else "false"},
    );

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/lexer_token_stream.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_lexer_errors_e0101_to_e0104" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const err_source =
        "let bad_esc = \"\\xGG\";\n" ++
        "let bad_chr = 'ab';\n" ++
        "let bad_num = 0x_1F;\n" ++
        "let overflow = 99;\n";
    const file_id = try source_map.setOverlay("src\\lexer\\errors.cx", err_source, .root);

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    var lexer_instance = Lexer.initWithOptions(
        err_source,
        file_id,
        &token_buf,
        &sink,
        &interner,
        .{ .max_tokens = 16 },
    );
    try lexer_instance.tokenize();

    var out_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderAll(&out_writer, &sink);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_lexer_errors.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_lexer_warnings_w0101_w0201" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const warn_source =
        "let badCamel = \"hello \\'world\";\n" ++
        "struct Bad_Type {}\n" ++
        "const MAX__LIMIT: u32 = 10;\n";
    const file_id = try source_map.setOverlay("src\\lexer\\warnings.cx", warn_source, .root);

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try corex.tokenize(warn_source, file_id, &token_buf, &sink, &interner);

    var out_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderAll(&out_writer, &sink);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_lexer_warnings.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_parser_cst_and_ast_tree" {
    const sample_source =
        "pub struct Metric[T] {\n" ++
        "    pub val: T,\n" ++
        "}\n" ++
        "pub fn render[T](opt: Option[T]) -> View {\n" ++
        "    let .Some(item) = opt else {\n" ++
        "        return Empty;\n" ++
        "    };\n" ++
        "    let score = item |> compute() catch 0;\n" ++
        "    let label = match score {\n" ++
        "        0 => \"idle\",\n" ++
        "        _ => \"active\",\n" ++
        "    };\n" ++
        "    Card(padding: 8) {\n" ++
        "        Text(value: label);\n" ++
        "    }\n" ++
        "}\n";

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    _ = try corex.parseSource(
        sample_source,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        null,
    );
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);

    var out_buf: [16384]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);

    try out_writer.print("=== CST ({d} nodes) ===\n", .{cst_arena.countNodes()});
    var i: usize = 0;
    while (i < cst_arena.countNodes()) : (i += 1) {
        const rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(i)));
        var first_tok = rec.token.asInt();
        var last_tok = first_tok;
        var j: usize = i;
        while (j < i + @as(usize, rec.subtree_size)) : (j += 1) {
            const child_tok = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(j))).token.asInt();
            if (child_tok < first_tok) first_tok = child_tok;
            if (child_tok > last_tok) last_tok = child_tok;
        }
        try out_writer.print(
            "cst[{d:0>3}] {s} size={d} tok={d}..{d}\n",
            .{ i, @tagName(rec.kind), rec.subtree_size, first_tok, last_tok },
        );
    }

    try out_writer.print("=== AST ({d} nodes) ===\n", .{ast_arena.countNodes()});
    i = 0;
    while (i < ast_arena.countNodes()) : (i += 1) {
        const ast_id = NodeIndex.fromInt(@intCast(i));
        const ast_rec = ast_arena.getNode(ast_id);
        try out_writer.print(
            "ast[{d:0>2}] {s} cst={d} main_tok={d}\n",
            .{ i, @tagName(ast_rec.tag), ast_arena.getCstOrigin(ast_id).asInt(), ast_rec.main_token.asInt() },
        );
    }

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/parser_cst_ast.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_parser_errors_e0201_to_e0203" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const err_source =
        "fn check_cmp(a: i32, b: i32) -> bool {\n" ++
        "    return a < b < 10;\n" ++
        "}\n" ++
        "fn unclosed_delim(x: i32 {\n" ++
        "    return ((x + 1));\n" ++
        "}\n";
    const file_id = try source_map.setOverlay("src\\parser\\errors.cx", err_source, .root);

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try corex.tokenize(err_source, file_id, &token_buf, &sink, &interner);
    var parser_instance = Parser.initWithOptions(
        err_source,
        file_id,
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
        .{ .max_depth = 6 },
    );
    _ = try parser_instance.parse();

    var out_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(&source_map, &interner, StyleConfig.MONOCHROME).renderAll(&out_writer, &sink);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_parser_errors.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_fmt_showcases" {
    const sample_source =
        "use std::io::{Write, self, Read, BufReader as Br};\n" ++
        "use core::mem;\n" ++
        "const MIN_PORT: u16 = 80;\n" ++
        "const MAX_PORT: u16 = 65535;\n" ++
        "pub struct Metric[T] {\n" ++
        "    pub val: T,\n" ++
        "}\n" ++
        "pub fn render_dashboard[T](opt_val: Option[T], raw_score: i32) -> View {\n" ++
        "    let .Some(item) = opt_val else {\n" ++
        "        return Empty;\n" ++
        "    };\n" ++
        "    let table = [\n" ++
        "        1, 20, 300, 4, 50, 600, 7, 80, 900, 10,\n" ++
        "    ];\n" ++
        "    let score = raw_score\n" ++
        "        |> compute_step()\n" ++
        "        |> clamp_score(0, 100);\n" ++
        "    let total = table\n" ++
        "        .iter()\n" ++
        "        .sum_all();\n" ++
        "    let broken_pt = Point {\n" ++
        "        x: score,\n" ++
        "        y: total,\n" ++
        "    };\n" ++
        "    let label = match (score) {\n" ++
        "        0 => \"idle\",\n" ++
        "        _ => \"active\",\n" ++
        "    };\n" ++
        "    Card(padding: 8) {\n" ++
        "        Text(value: label);\n" ++
        "    }\n" ++
        "}\n";

    var fmt_res = try fmt_engine.formatSource(std.testing.allocator, sample_source, FileId.fromInt(0));
    defer fmt_res.deinit(std.testing.allocator);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/fmt_showcases.snap",
        fmt_res.formatted_text,
    );
}

test "test_snapshot_fmt_comments_and_directives" {
    const sample_source =
        "//! Module header doc comment\n" ++
        "// Leading comment on Point\n" ++
        "pub struct Point {\n" ++
        "    pub x: i32; // trailing comment on x\n" ++
        "    // leading comment on y\n" ++
        "    pub y: i32\n" ++
        "}\n" ++
        "pub fn empty_containers(\n" ++
        "    // dangling comment in empty params\n" ++
        ") {\n" ++
        "    // dangling comment in empty block\n" ++
        "}\n" ++
        "pub fn empty_list_and_call() {\n" ++
        "    let arr = [\n" ++
        "        // dangling comment in empty array\n" ++
        "    ];\n" ++
        "    let res = call_fn(\n" ++
        "        // dangling comment in empty args\n" ++
        "    );\n" ++
        "}\n" ++
        "// corex fmt: off\n" ++
        "const   RAW_TABLE:   [i32; 4] = [ 1,   2,  3,    4 ];\n" ++
        "// corex fmt: on\n" ++
        "// Trailing EOF comment\n";

    var fmt_res = try fmt_engine.formatSource(std.testing.allocator, sample_source, FileId.fromInt(0));
    defer fmt_res.deinit(std.testing.allocator);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/fmt_comments_and_directives.snap",
        fmt_res.formatted_text,
    );
}

test "test_snapshot_fmt_fix_normalization" {
    const unfixed_source =
        "const max_retry_limit: u32 = 10\n" ++
        "pub struct frame_header {\n" ++
        "    pub PayloadBytes: u32,\n" ++
        "}\n" ++
        "pub fn ComputeFrameTotal(frame_header: frame_header) -> u32 {\n" ++
        "    ;\n" ++
        "    let LocalSum = frame_header.PayloadBytes + max_retry_limit\n" ++
        "    if (LocalSum > 0) {\n" ++
        "        return LocalSum\n" ++
        "    };\n" ++
        "    return 0\n" ++
        "}\n";

    var fmt_res = try fmt_engine.formatSourceWithOptions(
        std.testing.allocator,
        unfixed_source,
        FileId.fromInt(0),
        .{ .is_fix_mode = true },
    );
    defer fmt_res.deinit(std.testing.allocator);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/fmt_fix_normalization.snap",
        fmt_res.formatted_text,
    );
}

test "test_snapshot_query_db_early_cutoff" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const stdlib_file = FileId.fromInt(1);
    const app_file = FileId.fromInt(2);

    _ = try db.setInput(
        stdlib_file,
        "pub fn clamp_val(val: i32) -> i32 { return val; }\n",
        .high,
    );
    const app_v1 =
        "pub fn foo(val: i32) -> i32 {\n    return val + 1;\n}\n" ++
        "pub fn bar(val: i32) -> i32 {\n    return val * 2;\n}\n";
    const rev_init = try db.setInput(app_file, app_v1, .low);

    const stdlib_def = (try db.extractItemTree(stdlib_file)).entries[0].def_id;
    const app_tree_v1 = try db.extractItemTree(app_file);
    const def_foo = app_tree_v1.entries[0].def_id;
    const def_bar = app_tree_v1.entries[1].def_id;

    _ = try db.verifySastMir(stdlib_def);
    _ = try db.verifySastMir(def_foo);
    _ = try db.verifySastMir(def_bar);

    var out_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);

    try out_writer.print(
        "=== Revision {d} (Initial Build: stdlib=high, app=low) ===\n",
        .{rev_init.asInt()},
    );
    try out_writer.print(
        "exec[parse_cst]={d} exec[lower_ast]={d} exec[item_tree]={d} exec[typecheck_body]={d} exec[verify_sast_mir]={d}\n",
        .{
            db.telemetry.countExecutions(.parse_cst),
            db.telemetry.countExecutions(.lower_ast),
            db.telemetry.countExecutions(.item_tree),
            db.telemetry.countExecutions(.typecheck_body),
            db.telemetry.countExecutions(.verify_sast_mir),
        },
    );
    try out_writer.print(
        "early_cutoffs={d} durability_fast_paths={d} green_hits={d}\n",
        .{ db.telemetry.early_cutoff_hits, db.telemetry.durability_fast_path_hits, db.telemetry.green_hits },
    );
    try out_writer.print(
        "foo: sig_changed=R{d} body_changed=R{d} sast_verified=R{d}\n",
        .{
            db.getMemoHeader(QueryKey.forDef(.def_signature, def_foo)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_foo)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, def_foo)).?.verified_at.asInt(),
        },
    );
    try out_writer.print(
        "bar: sig_changed=R{d} body_changed=R{d} sast_verified=R{d}\n\n",
        .{
            db.getMemoHeader(QueryKey.forDef(.def_signature, def_bar)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_bar)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, def_bar)).?.verified_at.asInt(),
        },
    );

    // Revision 3: Comment & whitespace edit in `app_file`:
    const app_v2 =
        "// Header comment\npub fn foo(   val: i32 ) -> i32 {\n    // inner\n    return val + 1;\n}\n" ++
        "pub fn bar(val: i32) -> i32 {\n    return val * 2;\n}\n";
    const rev_comment = try db.setInput(app_file, app_v2, .low);
    _ = try db.verifySastMir(stdlib_def);
    _ = try db.verifySastMir(def_foo);
    _ = try db.verifySastMir(def_bar);

    const lower_memo = db.getMemoHeader(QueryKey.forFile(.lower_ast, app_file)).?;
    const stdlib_memo = db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, stdlib_def)).?;
    try out_writer.print(
        "=== Revision {d} (Comment & Whitespace Edit in app) ===\n",
        .{rev_comment.asInt()},
    );
    try out_writer.print(
        "exec[parse_cst]={d} exec[lower_ast]={d} exec[item_tree]={d} exec[typecheck_body]={d} exec[verify_sast_mir]={d}\n",
        .{
            db.telemetry.countExecutions(.parse_cst),
            db.telemetry.countExecutions(.lower_ast),
            db.telemetry.countExecutions(.item_tree),
            db.telemetry.countExecutions(.typecheck_body),
            db.telemetry.countExecutions(.verify_sast_mir),
        },
    );
    try out_writer.print(
        "early_cutoffs={d} durability_fast_paths={d} green_hits={d}\n",
        .{ db.telemetry.early_cutoff_hits, db.telemetry.durability_fast_path_hits, db.telemetry.green_hits },
    );
    try out_writer.print(
        "app.lower_ast: verified=R{d} changed=R{d} (backdated!)\n",
        .{ lower_memo.verified_at.asInt(), lower_memo.changed_at.asInt() },
    );
    try out_writer.print(
        "stdlib.sast: verified=R{d} changed=R{d} min_durability={s}\n\n",
        .{ stdlib_memo.verified_at.asInt(), stdlib_memo.changed_at.asInt(), @tagName(stdlib_memo.min_durability) },
    );

    // Revision 4: Body edit in `foo` + 50-line shift before `bar`:
    const fifty_lines: *const [50]u8 = &@splat('\n');
    const app_v3 =
        "pub fn foo(val: i32) -> i32 {\n    let shifted = val + 99;\n" ++
        fifty_lines ++
        "    return shifted;\n}\n" ++
        "pub fn bar(val: i32) -> i32 {\n    return val * 2;\n}\n";
    const rev_body = try db.setInput(app_file, app_v3, .low);
    _ = try db.verifySastMir(def_bar);
    _ = try db.verifySastMir(def_foo);

    try out_writer.print(
        "=== Revision {d} (Body Edit in foo + 50-Line Shift Before bar) ===\n",
        .{rev_body.asInt()},
    );
    try out_writer.print(
        "exec[parse_cst]={d} exec[lower_ast]={d} exec[item_tree]={d} exec[typecheck_body]={d} exec[verify_sast_mir]={d}\n",
        .{
            db.telemetry.countExecutions(.parse_cst),
            db.telemetry.countExecutions(.lower_ast),
            db.telemetry.countExecutions(.item_tree),
            db.telemetry.countExecutions(.typecheck_body),
            db.telemetry.countExecutions(.verify_sast_mir),
        },
    );
    try out_writer.print(
        "early_cutoffs={d} durability_fast_paths={d} green_hits={d}\n",
        .{ db.telemetry.early_cutoff_hits, db.telemetry.durability_fast_path_hits, db.telemetry.green_hits },
    );
    try out_writer.print(
        "foo: sig_changed=R{d} body_changed=R{d} typed_changed=R{d} sast_verified=R{d}\n",
        .{
            db.getMemoHeader(QueryKey.forDef(.def_signature, def_foo)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_foo)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.typecheck_body, def_foo)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, def_foo)).?.verified_at.asInt(),
        },
    );
    try out_writer.print(
        "bar: sig_changed=R{d} body_changed=R{d} typed_changed=R{d} sast_verified=R{d}\n",
        .{
            db.getMemoHeader(QueryKey.forDef(.def_signature, def_bar)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.body_ast_proj, def_bar)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.typecheck_body, def_bar)).?.changed_at.asInt(),
            db.getMemoHeader(QueryKey.forDef(.verify_sast_mir, def_bar)).?.verified_at.asInt(),
        },
    );

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/query_db_early_cutoff.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_diag_phase4_type_errors" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const phase4_err_src =
        "pub type UserId = distinct u64;\n" ++
        "pub type SystemPort = u16 is 1..=1024;\n" ++
        "pub fn add_same(lhs: Number, rhs: Number) -> Number {\n" ++
        "    return lhs + rhs;\n" ++
        "}\n" ++
        "pub fn check_errors(\n" ++
        "    packet_length: i32,\n" ++
        "    other_val: i64,\n" ++
        "    user_id: UserId,\n" ++
        "    raw_id: u64,\n" ++
        "    opt_byte: u8?,\n" ++
        ") -> SystemPort {\n" ++
        "    let _typo = packet_lenght + 1;\n" ++
        "    let _conflict = add_same(packet_length, other_val);\n" ++
        "    let _mixed = user_id + raw_id;\n" ++
        "    let _missing = match opt_byte {\n" ++
        "        .Some(val) => val,\n" ++
        "    };\n" ++
        "    return 8080;\n" ++
        "}\n";

    const file_id = try source_map.setOverlay(
        "src\\typecheck\\phase4_errors.cx",
        phase4_err_src,
        .root,
    );
    var tc_res = try corex.typecheckSource(std.testing.allocator, file_id, phase4_err_src);
    defer tc_res.deinit();

    var out_buf: [16384]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(
        &source_map,
        &interner,
        StyleConfig.MONOCHROME,
    ).renderAll(&out_writer, &tc_res.diagnostics);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_phase4_type_errors.snap",
        out_writer.buffered(),
    );
}

test "test_snapshot_phase5_hir_desugaring" {
    const hir_showcase_src =
        "pub const ENABLE_BONUS: bool = true;\n" ++
        "pub struct IoError {\n" ++
        "    pub code: i32,\n" ++
        "}\n" ++
        "pub enum AppError {\n" ++
        "    @from Io(IoError),\n" ++
        "    Invalid,\n" ++
        "}\n" ++
        "pub struct SampleRow {\n" ++
        "    pub weight: i32,\n" ++
        "    pub tag: u32,\n" ++
        "}\n" ++
        "pub bit_field PacketFlags : u16 {\n" ++
        "    pub is_live: bool | 1,\n" ++
        "    pub tag: u16 | 15,\n" ++
        "}\n" ++
        "pub fn scale_step(num: i32, factor: i32) -> i32 {\n" ++
        "    return num * factor;\n" ++
        "}\n" ++
        "pub fn read_raw(is_ok: bool) -> Result[i32, IoError] {\n" ++
        "    if is_ok {\n" ++
        "        return .Ok(20);\n" ++
        "    }\n" ++
        "    return .Err(IoError { code: 404 });\n" ++
        "}\n" ++
        "pub fn lift_value(is_ok: bool, seed_val: i32) -> Result[i32, AppError] {\n" ++
        "    let raw_val = read_raw(is_ok)?;\n" ++
        "    let piped = seed_val |> scale_step(2);\n" ++
        "    return .Ok(piped + raw_val);\n" ++
        "}\n" ++
        "pub fn showcase_hir(opt_in: i32?, is_ok: bool) -> i32 {\n" ++
        "    let .Some(unwrapped) = opt_in else {\n" ++
        "        return 0;\n" ++
        "    };\n" ++
        "    let recovered = lift_value(is_ok, unwrapped) catch |err| match err {\n" ++
        "        .Io(io_err) => io_err.code,\n" ++
        "        .Invalid => -1,\n" ++
        "    };\n" ++
        "    var rows: #soa [SampleRow; 2] = @default_init[#soa [SampleRow; 2]]();\n" ++
        "    rows[0].weight = recovered;\n" ++
        "    rows.weight[1] += 3;\n" ++
        "    var flags = PacketFlags { is_live: false, tag: 2 };\n" ++
        "    flags.is_live = true;\n" ++
        "    flags.tag = 5;\n" ++
        "    let bonus: i32 = comptime if ENABLE_BONUS { 10 } else { 0 };\n" ++
        "    var unrolled_sum: i32 = 0;\n" ++
        "    comptime for step in 0..3 {\n" ++
        "        unrolled_sum += step;\n" ++
        "    }\n" ++
        "    return rows[0].weight + rows[1].weight + (flags.tag as i32) + bonus + unrolled_sum;\n" ++
        "}\n";

    var bundle = try corex.lowerSourceToHir(
        std.testing.allocator,
        hir_showcase_src,
        corex.TargetLayout.NATIVE_64,
    );
    defer bundle.deinit();
    try expectZeroDiagErrors(&bundle.diagnostics);

    const rendered_hir = try corex.renderHir(
        std.testing.allocator,
        &bundle.hir_store,
        &bundle.pool,
        &bundle.sym_table,
        &bundle.interner,
    );
    defer std.testing.allocator.free(rendered_hir);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/hir_desugaring.snap",
        rendered_hir,
    );
}

test "test_snapshot_phase5_mir_ssa_dev_vs_release" {
    const mir_showcase_src =
        "pub struct AccumPair {\n" ++
        "    pub total: i64,\n" ++
        "    pub steps: i64,\n" ++
        "}\n" ++
        "pub fn showcase_ssa_cfg(limit: i64, mode_tag: i64) -> Result[i64, i64] {\n" ++
        "    var audit_log: i64 = 0;\n" ++
        "    defer {\n" ++
        "        audit_log += 1;\n" ++
        "    }\n" ++
        "    errdefer {\n" ++
        "        audit_log += 10;\n" ++
        "    }\n" ++
        "    var pair = AccumPair { total: 0, steps: 0 };\n" ++
        "    var idx: i64 = 0;\n" ++
        "    while idx < limit {\n" ++
        "        let delta: i64 = if idx % 2 == 0 { idx + 2 } else { idx + 1 };\n" ++
        "        pair.total = pair.total + delta;\n" ++
        "        pair.steps = pair.steps + 1;\n" ++
        "        idx = idx + 1;\n" ++
        "    }\n" ++
        "    if mode_tag == 2 {\n" ++
        "        return .Err(-1);\n" ++
        "    }\n" ++
        "    let bonus: i64 = match mode_tag {\n" ++
        "        0 => 10,\n" ++
        "        1 => 20,\n" ++
        "        _ => 30,\n" ++
        "    };\n" ++
        "    return .Ok(pair.total + pair.steps + bonus + audit_log);\n" ++
        "}\n";

    var bundle = try corex.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(0),
        mir_showcase_src,
        corex.TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try expectZeroDiagErrors(&bundle.hir_bundle.diagnostics);

    var dev_sink = DiagnosticSink.init(std.testing.allocator);
    defer dev_sink.deinit();
    var dev_res = try corex.optimizeMirModule(
        std.testing.allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{
            .is_release_mode = false,
            .is_preserving_pre_strip_mir = true,
            .target_layout = corex.TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = mir_showcase_src,
                .tokens = &bundle.hir_bundle.tokens,
                .cst_arena = &bundle.hir_bundle.cst_arena,
            },
        },
        &dev_sink,
    );
    defer dev_res.deinit();
    try std.testing.expect(!dev_sink.hasErrors());

    var rel_sink = DiagnosticSink.init(std.testing.allocator);
    defer rel_sink.deinit();
    var rel_res = try corex.optimizeMirModule(
        std.testing.allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{
            .is_release_mode = true,
            .is_preserving_pre_strip_mir = false,
            .target_layout = corex.TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = mir_showcase_src,
                .tokens = &bundle.hir_bundle.tokens,
                .cst_arena = &bundle.hir_bundle.cst_arena,
            },
        },
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());

    const pre_strip_body = &dev_res.pre_strip_bodies.items[0];
    const dev_body = dev_res.findBodyByName(&bundle.hir_bundle.interner, "showcase_ssa_cfg").?;
    const rel_body = rel_res.findBodyByName(&bundle.hir_bundle.interner, "showcase_ssa_cfg").?;

    const pre_strip_dump = try corex.renderMir(
        std.testing.allocator,
        pre_strip_body,
        &bundle.hir_bundle.interner,
    );
    defer std.testing.allocator.free(pre_strip_dump);

    const dev_dump = try corex.renderMir(
        std.testing.allocator,
        dev_body,
        &bundle.hir_bundle.interner,
    );
    defer std.testing.allocator.free(dev_dump);

    const rel_dump = try corex.renderMir(
        std.testing.allocator,
        rel_body,
        &bundle.hir_bundle.interner,
    );
    defer std.testing.allocator.free(rel_dump);

    var combined_out: std.ArrayList(u8) = .empty;
    defer combined_out.deinit(std.testing.allocator);
    try combined_out.appendSlice(
        std.testing.allocator,
        "=== [1] Lowered Pre-Strip MIR (Ghost Ops Intact) ===\n",
    );
    try combined_out.appendSlice(std.testing.allocator, pre_strip_dump);
    try combined_out.appendSlice(
        std.testing.allocator,
        "\n=== [2] --dev Optimized MIR (D1..D5) ===\n",
    );
    try combined_out.appendSlice(std.testing.allocator, dev_dump);
    try combined_out.appendSlice(
        std.testing.allocator,
        "\n=== [3] --release Optimized MIR (D1..D5 + R1..R6) ===\n",
    );
    try combined_out.appendSlice(std.testing.allocator, rel_dump);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/mir_ssa_dev_vs_release.snap",
        combined_out.items,
    );
}

test "test_snapshot_phase5_mir_monomorph_and_icf" {
    const mono_icf_src =
        "pub fn scale_add(val: Number, factor: Number) -> Number {\n" ++
        "    return val * factor + val;\n" ++
        "}\n" ++
        "pub fn select_ptr[T](take_left: bool, left_ref: T, right_ref: T) -> T {\n" ++
        "    if take_left {\n" ++
        "        return left_ref;\n" ++
        "    }\n" ++
        "    return right_ref;\n" ++
        "}\n" ++
        "@inline(never)\n" ++
        "pub fn hash_lane_a(lhs: i64, rhs: i64) -> i64 {\n" ++
        "    let sum_val = lhs + rhs;\n" ++
        "    return sum_val * 3 - lhs;\n" ++
        "}\n" ++
        "@inline(never)\n" ++
        "pub fn hash_lane_b(first: i64, second: i64) -> i64 {\n" ++
        "    let combined = first + second;\n" ++
        "    return combined * 3 - first;\n" ++
        "}\n" ++
        "pub fn run_mono_icf_entry(seed_val: i64) -> i64 {\n" ++
        "    let u_left: u32 = 11;\n" ++
        "    let u_right: u32 = 22;\n" ++
        "    let i_left: i32 = 33;\n" ++
        "    let i_right: i32 = 44;\n" ++
        "    let two_i64: i64 = 2;\n" ++
        "    let four_u32: u32 = 4;\n" ++
        "    let three_u32: u32 = 3;\n" ++
        "    let chosen_u = select_ptr(true, &u_left, &u_right);\n" ++
        "    let chosen_i = select_ptr(false, &i_left, &i_right);\n" ++
        "    let scaled_i64 = scale_add(seed_val, two_i64);\n" ++
        "    let scaled_u32 = scale_add(four_u32, three_u32) as i64;\n" ++
        "    return (*chosen_u as i64) + (*chosen_i as i64) + scaled_i64 + scaled_u32 +\n" ++
        "        hash_lane_a(seed_val, 5) + hash_lane_b(seed_val, 5);\n" ++
        "}\n";

    var bundle = try corex.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(0),
        mono_icf_src,
        corex.TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();
    try expectZeroDiagErrors(&bundle.hir_bundle.diagnostics);

    var rel_sink = DiagnosticSink.init(std.testing.allocator);
    defer rel_sink.deinit();
    var rel_res = try corex.optimizeMirModule(
        std.testing.allocator,
        bundle.mir_bundle.bodies.items,
        &bundle.hir_bundle.pool,
        &bundle.hir_bundle.sym_table,
        &bundle.hir_bundle.interner,
        .{
            .is_release_mode = true,
            .is_preserving_pre_strip_mir = false,
            .target_layout = corex.TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = mono_icf_src,
                .tokens = &bundle.hir_bundle.tokens,
                .cst_arena = &bundle.hir_bundle.cst_arena,
            },
        },
        &rel_sink,
    );
    defer rel_res.deinit();
    try std.testing.expect(!rel_sink.hasErrors());
    try std.testing.expect(rel_res.dedup_merged_count >= 1);
    try std.testing.expect(rel_res.icf_folded_count >= 1);

    var combined_out: std.ArrayList(u8) = .empty;
    defer combined_out.deinit(std.testing.allocator);

    var hdr_buf: [256]u8 = undefined;
    var hdr_writer = std.Io.Writer.fixed(&hdr_buf);
    try hdr_writer.print(
        "=== Phase 5 Monomorphization, LayoutShapeKey Dedup & R6 ICF Summary ===\n" ++
            "bodies={d} dedup_merged_count={d} icf_merged_count={d}\n\n",
        .{ rel_res.bodies.items.len, rel_res.dedup_merged_count, rel_res.icf_folded_count },
    );
    try combined_out.appendSlice(std.testing.allocator, hdr_writer.buffered());

    for (rel_res.bodies.items, 0..) |*body_item, i| {
        if (i > 0) try combined_out.append(std.testing.allocator, '\n');
        const body_dump = try corex.renderMir(
            std.testing.allocator,
            body_item,
            &bundle.hir_bundle.interner,
        );
        defer std.testing.allocator.free(body_dump);
        try combined_out.appendSlice(std.testing.allocator, body_dump);
    }

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/mir_monomorph_icf.snap",
        combined_out.items,
    );
}

test "test_snapshot_diag_phase5_comptime_stack_trace_and_w0501" {
    const phase5_err_src =
        "pub fn spin_inner(seed_val: i64) -> i64 {\n" ++
        "    var cursor: i64 = seed_val;\n" ++
        "    while cursor > 0 {\n" ++
        "        cursor += 1;\n" ++
        "    }\n" ++
        "    return cursor;\n" ++
        "}\n" ++
        "pub fn spin_outer() -> i64 {\n" ++
        "    return spin_inner(1);\n" ++
        "}\n" ++
        "pub fn oob_inner(index_val: usize) -> i32 {\n" ++
        "    let items: [i32; 3] = [10, 20, 30];\n" ++
        "    return items[index_val];\n" ++
        "}\n" ++
        "pub fn oob_outer() -> i32 {\n" ++
        "    return oob_inner(3);\n" ++
        "}\n" ++
        "pub fn assert_inner(limit_val: i64) -> i64 {\n" ++
        "    @compile_assert(limit_val > 0, \"limit must be positive\");\n" ++
        "    return limit_val;\n" ++
        "}\n" ++
        "pub fn assert_outer() -> i64 {\n" ++
        "    return assert_inner(0);\n" ++
        "}\n" ++
        "@inline\n" ++
        "pub fn rec_inline_step(depth: i64) -> i64 {\n" ++
        "    if depth <= 0 {\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "    return 1 + rec_inline_step(depth - 1);\n" ++
        "}\n" ++
        "pub fn call_rec_inline(seed_val: i64) -> i64 {\n" ++
        "    return rec_inline_step(seed_val);\n" ++
        "}\n";

    var bundle = try corex.lowerSourceToMir(
        std.testing.allocator,
        FileId.fromInt(0),
        phase5_err_src,
        corex.TargetLayout.NATIVE_64,
        .{},
    );
    defer bundle.deinit();

    var source_map = VfsSourceMap.init(std.testing.allocator, &bundle.hir_bundle.interner);
    defer source_map.deinit(std.testing.io);
    const vfs_file_id = try source_map.setOverlay(
        "src\\comptime\\phase5_errors.cx",
        phase5_err_src,
        .root,
    );
    try std.testing.expectEqual(FileId.fromInt(0), vfs_file_id);

    var file_tokens: std.AutoHashMapUnmanaged(u32, *const TokenBuffer) = .empty;
    defer file_tokens.deinit(std.testing.allocator);
    try file_tokens.put(std.testing.allocator, vfs_file_id.asInt(), &bundle.hir_bundle.tokens);

    var rodata_pool = corex.RodataPool.init(std.testing.allocator);
    defer rodata_pool.deinit();
    var diag_sink = DiagnosticSink.init(std.testing.allocator);
    defer diag_sink.deinit();

    // [1] `E0501` step budget exceeded with `--comptime-limit` help note + call-stack trace:
    {
        var vm_step = try corex.MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &diag_sink,
            .{ .step_budget = 64, .file_tokens = &file_tokens },
        );
        defer vm_step.deinit();
        try registerAllMirBodiesInVm(&vm_step, &bundle);
        const spin_outer = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "spin_outer",
        ).?;
        try std.testing.expectError(error.StepLimitExceeded, vm_step.evalBody(spin_outer, &.{}));
    }

    // [2] `E0504` spatial out-of-bounds read + `E0510` `@compile_assert` failure with call-stack traces:
    {
        var vm_trap = try corex.MirVm.init(
            std.testing.allocator,
            &bundle.hir_bundle.interner,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &rodata_pool,
            null,
            &diag_sink,
            .{ .file_tokens = &file_tokens },
        );
        defer vm_trap.deinit();
        try registerAllMirBodiesInVm(&vm_trap, &bundle);

        const oob_outer = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "oob_outer",
        ).?;
        try std.testing.expectError(error.OutOfBounds, vm_trap.evalBody(oob_outer, &.{}));

        const assert_outer = bundle.mir_bundle.findBodyByName(
            &bundle.hir_bundle.interner,
            "assert_outer",
        ).?;
        try std.testing.expectError(
            error.CompileAssertionFailed,
            vm_trap.evalBody(assert_outer, &.{}),
        );
    }

    // [3] `W0501` `@inline` inlining budget / recursion warning in `--release` `optimizeMirModule`:
    {
        var rel_res = try corex.optimizeMirModule(
            std.testing.allocator,
            bundle.mir_bundle.bodies.items,
            &bundle.hir_bundle.pool,
            &bundle.hir_bundle.sym_table,
            &bundle.hir_bundle.interner,
            .{
                .is_release_mode = true,
                .is_preserving_pre_strip_mir = false,
                .target_layout = corex.TargetLayout.NATIVE_64,
                .syntax_view = .{
                    .source = phase5_err_src,
                    .tokens = &bundle.hir_bundle.tokens,
                    .cst_arena = &bundle.hir_bundle.cst_arena,
                },
            },
            &diag_sink,
        );
        defer rel_res.deinit();
    }

    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0501_comptime_step_limit_exceeded));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0504_comptime_out_of_bounds));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0510_compile_assertion_failed));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .w0501_inlining_budget_exceeded));

    var out_buf: [32768]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(
        &source_map,
        &bundle.hir_bundle.interner,
        StyleConfig.MONOCHROME,
    ).renderAll(&out_writer, &diag_sink);

    const rendered_text = out_writer.buffered();
    try std.testing.expect(std.mem.indexOf(u8, rendered_text, "src/comptime/phase5_errors.cx") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered_text, "src\\comptime\\phase5_errors.cx") == null);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_phase5_comptime_errors.snap",
        rendered_text,
    );
}

test "test_snapshot_phase6_sast_ownership_region_and_bounds_diagnostics" {
    for (PHASE6_DIAGNOSTIC_CODES) |phase6_code| {
        try std.testing.expectEqual(@as(usize, 5), phase6_code.asCodeStr().len);
    }

    const phase6_ownership_src =
        "pub struct Vec[T] {\n" ++
        "    pub len: usize,\n" ++
        "}\n" ++
        "pub struct BumpArena {\n" ++
        "    pub used: usize,\n" ++
        "}\n" ++
        "pub struct Context {\n" ++
        "    pub allocator: usize,\n" ++
        "    pub scratch: [BumpArena; 2],\n" ++
        "}\n" ++
        "pub fn consume_vec(own _items: sink Vec[i64]) {}\n" ++
        "pub fn head_slice(items: &[i64]) -> &[i64] {\n" ++
        "    return items;\n" ++
        "}\n" ++
        "pub fn mutate_arr(mut arr: inout [i64; 4]) {\n" ++
        "    arr[0] = 99;\n" ++
        "}\n" ++
        "pub fn reset(_arena: &BumpArena) {}\n" ++
        "pub fn wire_size_mismatch(word: u32) -> u64 {\n" ++
        "    return @bit_cast[u64](word);\n" ++
        "}\n" ++
        "pub fn use_after_move() -> usize {\n" ++
        "    let items = Vec { len: 4 };\n" ++
        "    consume_vec(items);\n" ++
        "    return items.len;\n" ++
        "}\n" ++
        "pub fn borrow_conflict() -> usize {\n" ++
        "    var arr: [i64; 4] = [1, 2, 3, 4];\n" ++
        "    let view = head_slice(&arr);\n" ++
        "    mutate_arr(arr);\n" ++
        "    return view.len;\n" ++
        "}\n" ++
        "pub fn stack_escape() -> &i64 {\n" ++
        "    let local_val: i64 = 77;\n" ++
        "    return &local_val;\n" ++
        "}\n" ++
        "pub fn scratch_conflict(ctx: &Context) -> usize {\n" ++
        "    let live_ref = &ctx.scratch[0];\n" ++
        "    reset(&ctx.scratch[0]);\n" ++
        "    return live_ref.used;\n" ++
        "}\n" ++
        "pub fn static_oob() -> i64 {\n" ++
        "    let fixed: [i64; 3] = [1, 2, 3];\n" ++
        "    return fixed[3];\n" ++
        "}\n" ++
        "pub fn unproven_strict_bounds(slice_in: &[i64], raw_idx: usize) -> i64 {\n" ++
        "    return slice_in[raw_idx];\n" ++
        "}\n";

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    const vfs_file_id = try source_map.setOverlay(
        "src\\sast\\phase6_ownership_errors.cx",
        phase6_ownership_src,
        .root,
    );
    try std.testing.expectEqual(FileId.fromInt(0), vfs_file_id);

    var token_buffer = TokenBuffer.init(std.testing.allocator);
    defer token_buffer.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var diag_sink = DiagnosticSink.init(std.testing.allocator);
    defer diag_sink.deinit();
    var lowering_sink = DiagnosticSink.init(std.testing.allocator);
    defer lowering_sink.deinit();

    _ = try corex.parseSource(
        phase6_ownership_src,
        vfs_file_id,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &lowering_sink,
        &interner,
    );
    try expectZeroDiagErrors(&lowering_sink);

    var sym_table = try corex.SymbolTable.init(std.testing.allocator, &interner);
    defer sym_table.deinit();
    _ = try corex.collectFileModuleItems(
        &sym_table,
        &interner,
        vfs_file_id,
        phase6_ownership_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diag_sink,
    );
    try corex.resolveFileUseImports(
        &sym_table,
        &interner,
        vfs_file_id,
        phase6_ownership_src,
        &token_buffer,
        &cst_arena,
        &diag_sink,
    );

    var pool = try corex.InternPool.init(std.testing.allocator);
    defer pool.deinit();
    var checker = try corex.TypeChecker.init(
        std.testing.allocator,
        &interner,
        &pool,
        &sym_table,
        vfs_file_id,
        phase6_ownership_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &diag_sink,
    );
    defer checker.deinit();
    checker.target_layout = corex.TargetLayout.NATIVE_64;
    try checker.resolveModuleSignatures();
    try checker.checkFileBodies();

    var side_tables = try checker.extractFileSemanticSideTables(std.testing.allocator);
    defer side_tables.deinit();
    var hir_store = try corex.hir.lowerFileToHir(
        std.testing.allocator,
        vfs_file_id,
        phase6_ownership_src,
        &token_buffer,
        &cst_arena,
        &ast_arena,
        &interner,
        &pool,
        &sym_table,
        &side_tables,
        &lowering_sink,
        corex.TargetLayout.NATIVE_64,
        .{},
    );
    defer hir_store.deinit();
    try expectZeroDiagErrors(&lowering_sink);

    var mir_module = try corex.mir.lowerHirToMirForSast(
        std.testing.allocator,
        &hir_store,
        &pool,
        &sym_table,
        &interner,
        &lowering_sink,
    );
    defer mir_module.deinit();
    try expectZeroDiagErrors(&lowering_sink);

    var sast_res = try corex.analyzeAndElaborateMirModule(
        std.testing.allocator,
        mir_module.bodies.items,
        &pool,
        &sym_table,
        &interner,
        .{
            .is_sast_strict = true,
            .diagnostic_sink = &diag_sink,
            .source_text = phase6_ownership_src,
            .token_buffer = &token_buffer,
            .cst_arena = &cst_arena,
        },
    );
    defer sast_res.deinit();

    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0302_use_after_move));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0305_exclusivity_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0306_region_escape_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0307_static_buffer_overflow));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0315_wire_layout_contract_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .e0328_scratch_arena_ping_pong_conflict));
    try std.testing.expect(hasDiagnosticCodeInSink(&diag_sink, .w0314_unproven_bounds_access));

    var out_buf: [65536]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(
        &source_map,
        &interner,
        StyleConfig.MONOCHROME,
    ).renderAll(&out_writer, &diag_sink);

    const rendered_text = out_writer.buffered();
    try std.testing.expect(
        std.mem.indexOf(u8, rendered_text, "src/sast/phase6_ownership_errors.cx") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, rendered_text, "src\\sast\\phase6_ownership_errors.cx") == null,
    );

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_phase6_sast_errors.snap",
        rendered_text,
    );
}

test "test_snapshot_phase6_capability_contracts_and_witness_chains" {
    const phase6_cap_src =
        "extern \"C\" fn raw_c_hook() -> i32;\n" ++
        "fn open_file() -> i32;\n" ++
        "pub struct Context {\n" ++
        "    pub allocator: usize,\n" ++
        "}\n" ++
        "fn fs_sync_leaf() -> i32 {\n" ++
        "    return open_file();\n" ++
        "}\n" ++
        "fn fs_sync_mid() -> i32 {\n" ++
        "    return fs_sync_leaf();\n" ++
        "}\n" ++
        "@max_stack(32)\n" ++
        "pub fn rec_climb(depth: i32) -> i32 {\n" ++
        "    if depth <= 0 {\n" ++
        "        return 0;\n" ++
        "    }\n" ++
        "    return rec_climb(depth - 1) + 1;\n" ++
        "}\n" ++
        "fn alloc_leaf(ctx: &Context) -> usize {\n" ++
        "    return ctx.allocator;\n" ++
        "}\n" ++
        "fn alloc_mid(ctx: &Context) -> usize {\n" ++
        "    return alloc_leaf(ctx);\n" ++
        "}\n" ++
        "@no_alloc\n" ++
        "pub fn no_alloc_entry(ctx: &Context) -> usize {\n" ++
        "    return alloc_mid(ctx);\n" ++
        "}\n" ++
        "fn panic_leaf(items: &[i32], idx: usize) -> i32 {\n" ++
        "    return items[idx];\n" ++
        "}\n" ++
        "fn panic_mid(items: &[i32], idx: usize) -> i32 {\n" ++
        "    return panic_leaf(items, idx);\n" ++
        "}\n" ++
        "@no_panic\n" ++
        "pub fn no_panic_entry(items: &[i32], idx: usize) -> i32 {\n" ++
        "    return panic_mid(items, idx);\n" ++
        "}\n" ++
        "@no_block\n" ++
        "pub fn no_block_entry() -> i32 {\n" ++
        "    return fs_sync_mid();\n" ++
        "}\n" ++
        "comptime fn bad_comptime_probe() -> i32 {\n" ++
        "    return fs_sync_mid();\n" ++
        "}\n" ++
        "fn dead_private_ffi() -> i32 {\n" ++
        "    return unsafe { raw_c_hook() };\n" ++
        "}\n";

    var sast_bundle = try corex.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(0),
        phase6_cap_src,
        corex.TargetLayout.NATIVE_64,
        .{
            .package_policy = .{
                .package_name = "untrusted_codec",
                .policy_span = Span.init(FileId.fromInt(0), 0, 34),
                .allowed_caps = corex.EffectCapabilityMask.EMPTY,
                .is_third_party_dependency = true,
                .enforcement_scope = .surface,
            },
        },
    );
    defer sast_bundle.deinit();

    var source_map = VfsSourceMap.init(std.testing.allocator, &sast_bundle.interner);
    defer source_map.deinit(std.testing.io);
    const vfs_file_id = try source_map.setOverlay(
        "src\\sast\\phase6_capability_errors.cx",
        phase6_cap_src,
        .root,
    );
    try std.testing.expectEqual(FileId.fromInt(0), vfs_file_id);

    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .e0316_max_stack_budget_exceeded));
    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .e0320_no_alloc_contract_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .e0321_no_panic_contract_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .e0322_no_block_contract_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .e0324_package_capability_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .e0325_comptime_sandbox_violation));
    try std.testing.expect(hasDiagnosticCodeInSink(&sast_bundle.diagnostics, .w0330_ambient_dead_capability_in_dep));

    var out_buf: [65536]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    try DiagnosticRenderer.init(
        &source_map,
        &sast_bundle.interner,
        StyleConfig.MONOCHROME,
    ).renderAll(&out_writer, &sast_bundle.diagnostics);

    const rendered_text = out_writer.buffered();
    try std.testing.expect(
        std.mem.indexOf(u8, rendered_text, "src/sast/phase6_capability_errors.cx") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, rendered_text, "src\\sast\\phase6_capability_errors.cx") == null,
    );
    try std.testing.expect(std.mem.indexOf(u8, rendered_text, corex.Glyphs.POINTER_SOLID) != null);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/diag_phase6_capabilities.snap",
        rendered_text,
    );
}

test "test_snapshot_phase6_mir_drop_elaboration_and_dev_release_parity" {
    const drop_showcase_src =
        "pub trait Drop {\n" ++
        "    fn drop(&mut self);\n" ++
        "}\n" ++
        "pub struct TrackedGuard {\n" ++
        "    pub id: i64,\n" ++
        "}\n" ++
        "impl Drop for TrackedGuard {\n" ++
        "    pub fn drop(&mut self) {\n" ++
        "        @drop_trace(self.id);\n" ++
        "    }\n" ++
        "}\n" ++
        "pub fn consume_guard(own item: sink TrackedGuard) -> i64 {\n" ++
        "    return item.id;\n" ++
        "}\n" ++
        "@no_panic\n" ++
        "pub fn run_drop_and_bce_showcase(take_branch: bool, probe_idx: usize) -> i64 {\n" ++
        "    let outer_guard = TrackedGuard { id: 100 };\n" ++
        "    let cond_guard = TrackedGuard { id: 200 };\n" ++
        "    let weights: [i64; 4] = [3, 5, 7, 11];\n" ++
        "    let slice_view: &[i64] = &weights;\n" ++
        "    var total: i64 = 0;\n" ++
        "    if take_branch {\n" ++
        "        total = consume_guard(cond_guard);\n" ++
        "    }\n" ++
        "    if probe_idx < slice_view.len {\n" ++
        "        total = total +% slice_view[probe_idx];\n" ++
        "    }\n" ++
        "    return total +% outer_guard.id;\n" ++
        "}\n" ++
        "pub fn entry_moved() -> i64 {\n" ++
        "    return run_drop_and_bce_showcase(true, 2);\n" ++
        "}\n" ++
        "pub fn entry_kept() -> i64 {\n" ++
        "    return run_drop_and_bce_showcase(false, 1);\n" ++
        "}\n";

    var sast_bundle = try corex.lowerAndVerifySourceMirSast(
        std.testing.allocator,
        FileId.fromInt(0),
        drop_showcase_src,
        corex.TargetLayout.NATIVE_64,
        .{ .is_sast_strict = true },
    );
    defer sast_bundle.deinit();
    try expectZeroDiagErrors(&sast_bundle.diagnostics);
    try std.testing.expectEqual(@as(usize, 0), sast_bundle.diagnostics.diagnostics.items.len);
    try std.testing.expect(sast_bundle.sast_result.eliminated_bounds_checks > 0);
    try std.testing.expect(sast_bundle.sast_result.emitted_drops >= 2);

    var dev_sink = DiagnosticSink.init(std.testing.allocator);
    defer dev_sink.deinit();
    var dev_res = try corex.optimizeMirModule(
        std.testing.allocator,
        sast_bundle.mir_module.bodies.items,
        &sast_bundle.pool,
        &sast_bundle.sym_table,
        &sast_bundle.interner,
        .{
            .is_release_mode = false,
            .is_preserving_pre_strip_mir = false,
            .target_layout = corex.TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = drop_showcase_src,
                .tokens = &sast_bundle.token_buffer,
                .cst_arena = &sast_bundle.cst_arena,
            },
        },
        &dev_sink,
    );
    defer dev_res.deinit();
    try expectZeroDiagErrors(&dev_sink);

    var rel_sink = DiagnosticSink.init(std.testing.allocator);
    defer rel_sink.deinit();
    var rel_res = try corex.optimizeMirModule(
        std.testing.allocator,
        sast_bundle.mir_module.bodies.items,
        &sast_bundle.pool,
        &sast_bundle.sym_table,
        &sast_bundle.interner,
        .{
            .is_release_mode = true,
            .is_preserving_pre_strip_mir = false,
            .target_layout = corex.TargetLayout.NATIVE_64,
            .syntax_view = .{
                .source = drop_showcase_src,
                .tokens = &sast_bundle.token_buffer,
                .cst_arena = &sast_bundle.cst_arena,
            },
        },
        &rel_sink,
    );
    defer rel_res.deinit();
    try expectZeroDiagErrors(&rel_sink);

    // Execute both `entry_moved` and `entry_kept` in `MirVm` under `--dev` and `--release`:
    var rodata_dev = corex.RodataPool.init(std.testing.allocator);
    defer rodata_dev.deinit();
    var rodata_rel = corex.RodataPool.init(std.testing.allocator);
    defer rodata_rel.deinit();

    const entry_names = [_]struct {
        /// Entrypoint function name registered in `MirVm`.
        name: []const u8,
        /// Expected deterministic signed integer return value.
        expected_scalar: i64,
    }{
        .{ .name = "entry_moved", .expected_scalar = 307 },
        .{ .name = "entry_kept", .expected_scalar = 105 },
    };

    for (entry_names) |entry_case| {
        var vm_dev = try corex.MirVm.init(
            std.testing.allocator,
            &sast_bundle.interner,
            &sast_bundle.pool,
            &sast_bundle.sym_table,
            &rodata_dev,
            null,
            &dev_sink,
            .{ .target_layout = corex.TargetLayout.NATIVE_64 },
        );
        defer vm_dev.deinit();
        try registerOptimizedBodiesInVm(&vm_dev, dev_res.bodies.items, &sast_bundle.sym_table);

        var vm_rel = try corex.MirVm.init(
            std.testing.allocator,
            &sast_bundle.interner,
            &sast_bundle.pool,
            &sast_bundle.sym_table,
            &rodata_rel,
            null,
            &rel_sink,
            .{ .target_layout = corex.TargetLayout.NATIVE_64 },
        );
        defer vm_rel.deinit();
        try registerOptimizedBodiesInVm(&vm_rel, rel_res.bodies.items, &sast_bundle.sym_table);

        const dev_entry = dev_res.findBodyByName(&sast_bundle.interner, entry_case.name).?;
        const rel_entry = rel_res.findBodyByName(&sast_bundle.interner, entry_case.name).?;

        const dev_val = try vm_dev.evalBody(dev_entry, &.{});
        const rel_val = try vm_rel.evalBody(rel_entry, &.{});
        try std.testing.expectEqual(entry_case.expected_scalar, dev_val.slot.scalar_i64);
        try std.testing.expectEqual(dev_val.slot.scalar_i64, rel_val.slot.scalar_i64);
        try std.testing.expectEqualSlices(i64, &[_]i64{ 200, 100 }, vm_dev.asDropTraceSlice());
        try std.testing.expectEqualSlices(i64, vm_dev.asDropTraceSlice(), vm_rel.asDropTraceSlice());
        try std.testing.expectEqual(@as(u32, 0), vm_dev.countUnfreedHeapAllocations());
        try std.testing.expectEqual(@as(u32, 0), vm_rel.countUnfreedHeapAllocations());
    }

    const elaborated_body = sast_bundle.mir_module.findBodyByName(
        &sast_bundle.interner,
        "run_drop_and_bce_showcase",
    ).?;
    const dev_showcase = dev_res.findBodyByName(
        &sast_bundle.interner,
        "run_drop_and_bce_showcase",
    ).?;
    const rel_showcase = rel_res.findBodyByName(
        &sast_bundle.interner,
        "run_drop_and_bce_showcase",
    ).?;

    const elaborated_dump = try corex.renderMir(
        std.testing.allocator,
        elaborated_body,
        &sast_bundle.interner,
    );
    defer std.testing.allocator.free(elaborated_dump);
    try std.testing.expect(std.mem.indexOf(u8, elaborated_dump, "intrinsic_op.drop_in_place") != null);
    try std.testing.expect(std.mem.indexOf(u8, elaborated_dump, "intrinsic_op.drop_if_live") != null);

    const dev_dump = try corex.renderMir(
        std.testing.allocator,
        dev_showcase,
        &sast_bundle.interner,
    );
    defer std.testing.allocator.free(dev_dump);

    const rel_dump = try corex.renderMir(
        std.testing.allocator,
        rel_showcase,
        &sast_bundle.interner,
    );
    defer std.testing.allocator.free(rel_dump);

    var combined_out: std.ArrayList(u8) = .empty;
    defer combined_out.deinit(std.testing.allocator);
    try combined_out.appendSlice(
        std.testing.allocator,
        "=== [1] SAST-Elaborated Pre-Strip MIR (Drop Glue & Pentagon BCE) ===\n",
    );
    try combined_out.appendSlice(std.testing.allocator, elaborated_dump);
    try combined_out.appendSlice(
        std.testing.allocator,
        "\n=== [2] --dev Optimized MIR (D1..D5) ===\n",
    );
    try combined_out.appendSlice(std.testing.allocator, dev_dump);
    try combined_out.appendSlice(
        std.testing.allocator,
        "\n=== [3] --release Optimized MIR (D1..D5 + R1..R6) ===\n",
    );
    try combined_out.appendSlice(std.testing.allocator, rel_dump);

    try expectMatchesSnapshotFile(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots/mir_phase6_drop_elaboration.snap",
        combined_out.items,
    );
}

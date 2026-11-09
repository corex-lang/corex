//! Golden Snapshot Verification Suite (`tests/snapshots/snapshot_test.zig`)
//!
//! Compares rendered CLI help menus, single-line diagnostics, multi-line region diagnostics,
//! cross-file stitched diagnostics, and CLI typo diagnostics against golden `.snap` files.
//!
//! Normalizes `CRLF` (`\r\n`) to `LF` (`\n`) when loading `.snap` files so snapshots match across OSes.

const std = @import("std");
const corex = @import("corex");

const router = corex.router;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const Span = corex.Span;
const StringInterner = corex.StringInterner;
const VfsSourceMap = corex.VfsSourceMap;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const Lexer = corex.Lexer;
const StyleConfig = corex.StyleConfig;
const DiagnosticSink = corex.DiagnosticSink;
const LabeledSpan = corex.LabeledSpan;
const DiagnosticRenderer = corex.DiagnosticRenderer;

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

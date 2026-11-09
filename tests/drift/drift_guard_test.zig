//! Repository-Wide Drift Guards (`tests/drift/drift_guard_test.zig`)
//!
//! Enforces zero colored emojis across the entire repository, 100% parity between `router.zig`
//! tables and `corex --help`, `DIAGNOSTIC_CATALOG` subsystem prefix integrity, and `< 150` column
//! line length plus 90-character top-level section dividers across all `.zig` source files.
//!
//! Prevents code/documentation drift and stylistic regressions automatically during `zig build test`.

const std = @import("std");
const corex = @import("corex");

const style = corex.style;
const router = corex.router;
const diagnostic = corex.diagnostic;
const lexer = corex.lexer;
const syntax = corex.syntax_arenas;
const TokenKind = corex.TokenKind;
const CstNodeKind = syntax.CstNodeKind;
const AstTag = syntax.AstTag;
const TokenSet128 = corex.TokenSet128;
const DiagnosticCode = corex.DiagnosticCode;
const StyleConfig = corex.StyleConfig;

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical 90-character top-level section dividers required by `.agents/skills/docs/SKILL.md` Section 3.
const CANONICAL_TOP_DIVIDERS = [_]struct {
    /// Center-padded section label (`" TYPES "`, `" CONSTS "`, etc.).
    label: []const u8,
    /// Exact 90-character canonical divider line.
    expected: []const u8,
}{
    .{
        .label = " TYPES ",
        .expected = "// ---------------------------------------- TYPES ----------------------------------------",
    },
    .{
        .label = " CONSTS ",
        .expected = "// --------------------------------------- CONSTS ----------------------------------------",
    },
    .{
        .label = " INTERNALS ",
        .expected = "// -------------------------------------- INTERNALS --------------------------------------",
    },
    .{
        .label = " PUBLIC API ",
        .expected = "// ------------------------------------- PUBLIC API --------------------------------------",
    },
    .{
        .label = " MAIN ",
        .expected = "// ---------------------------------------- MAIN -----------------------------------------",
    },
};

// -------------------------------------- INTERNALS --------------------------------------

/// Asserts that `file_path` contains zero banned colored emojis (`style.hasBannedEmoji == false`).
fn checkFileZeroBannedEmojis(allocator: std.mem.Allocator, io: std.Io, file_path: []const u8) !void {
    const content = try std.Io.Dir.cwd().readFileAlloc(io, file_path, allocator, .limited(16 * 1024 * 1024));
    defer allocator.free(content);

    if (style.hasBannedEmoji(content)) {
        std.debug.print("Drift Guard 1 violation: banned colored emoji in `{s}`\n", .{file_path});
        return error.BannedColoredEmojiFound;
    }
}

/// Recursively walks `dir_path` and asserts zero banned colored emojis in every file.
fn walkDirectoryZeroBannedEmojis(allocator: std.mem.Allocator, io: std.Io, dir_path: []const u8) !void {
    var opened_dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer opened_dir.close(io);

    var walker = try opened_dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next(io)) |entry| {
        if (entry.kind != .file) continue;
        const full_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ dir_path, entry.path });
        defer allocator.free(full_path);
        try checkFileZeroBannedEmojis(allocator, io, full_path);
    }
}

/// Asserts that every line in `zig_path` is `< 150` columns and top-level dividers are 90 characters wide.
fn checkZigFileFormattingAndDividers(
    allocator: std.mem.Allocator,
    io: std.Io,
    zig_path: []const u8,
) !void {
    const content = try std.Io.Dir.cwd().readFileAlloc(io, zig_path, allocator, .limited(16 * 1024 * 1024));
    defer allocator.free(content);

    var line_iter = std.mem.splitScalar(u8, content, '\n');
    var line_num: usize = 1;
    var prev_top_divider_idx: ?usize = null;
    while (line_iter.next()) |raw_line| : (line_num += 1) {
        const line = if (raw_line.len > 0 and raw_line[raw_line.len - 1] == '\r')
            raw_line[0 .. raw_line.len - 1]
        else
            raw_line;

        if (line.len >= 150) {
            std.debug.print(
                "Drift Guard 4 violation: `{s}:{d}` has {d} bytes (>= 150)\n",
                .{ zig_path, line_num, line.len },
            );
            return error.LineTooLong;
        }

        for (CANONICAL_TOP_DIVIDERS, 0..) |divider_spec, i| {
            if (std.mem.startsWith(u8, line, "// ---") and std.mem.indexOf(u8, line, divider_spec.label) != null) {
                try std.testing.expectEqual(@as(usize, 90), line.len);
                try std.testing.expectEqualStrings(divider_spec.expected, line);
                if (prev_top_divider_idx) |prev_idx| {
                    try std.testing.expect(prev_idx < i);
                }
                prev_top_divider_idx = i;
            }
        }

        const trimmed = std.mem.trimStart(u8, line, " ");
        if (std.mem.startsWith(u8, trimmed, "// ---") and std.mem.endsWith(u8, trimmed, "---")) {
            try std.testing.expect(trimmed.len == 90 or trimmed.len == 65);
            const after_prefix = trimmed[3..];
            var left_dashes: usize = 0;
            while (left_dashes < after_prefix.len and after_prefix[left_dashes] == '-') : (left_dashes += 1) {}
            var right_dashes: usize = 0;
            while (right_dashes < after_prefix.len and
                after_prefix[after_prefix.len - 1 - right_dashes] == '-') : (right_dashes += 1)
            {}
            try std.testing.expect(left_dashes == right_dashes or left_dashes + 1 == right_dashes);
        }
    }
}

/// Recursively walks `dir_path` and checks all `.zig` files for `< 150` columns and 90-char dividers.
fn walkZigDirectoryFormatting(allocator: std.mem.Allocator, io: std.Io, dir_path: []const u8) !void {
    var opened_dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer opened_dir.close(io);

    var walker = try opened_dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.path, ".zig")) continue;
        const full_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ dir_path, entry.path });
        defer allocator.free(full_path);
        try checkZigFileFormattingAndDividers(allocator, io, full_path);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_drift_guard_zero_colored_emojis_across_repository" {
    for ([_][]const u8{ "stage0", "tests", "bench", "docs", ".agents" }) |dir_name| {
        try walkDirectoryZeroBannedEmojis(std.testing.allocator, std.testing.io, dir_name);
    }
    for ([_][]const u8{ "PLAN.md", "CHANGELOG.md", "README.md", "build.zig" }) |file_name| {
        try checkFileZeroBannedEmojis(std.testing.allocator, std.testing.io, file_name);
    }
}

test "test_drift_guard_cli_subcommands_and_flags_documented_in_help" {
    var help_buf: [8192]u8 = undefined;
    var help_writer = std.Io.Writer.fixed(&help_buf);
    try router.renderHelp(&help_writer, StyleConfig.MONOCHROME);
    const help_output = help_writer.buffered();

    for (router.SUBCOMMANDS) |sub_desc| {
        try std.testing.expect(std.mem.indexOf(u8, help_output, sub_desc.name) != null);
        try std.testing.expect(std.mem.indexOf(u8, help_output, sub_desc.summary) != null);
    }
    for (router.GLOBAL_FLAGS) |flag_desc| {
        try std.testing.expect(std.mem.indexOf(u8, help_output, flag_desc.long_flag) != null);
        try std.testing.expect(std.mem.indexOf(u8, help_output, flag_desc.summary) != null);
        if (flag_desc.short_flag) |short_str| {
            try std.testing.expect(std.mem.indexOf(u8, help_output, short_str) != null);
        }
    }
}

test "test_drift_guard_diagnostic_catalog_uniqueness_and_subsystem_prefixes" {
    const catalog = diagnostic.DIAGNOSTIC_CATALOG;
    try std.testing.expect(catalog.len > 0);

    for (catalog, 0..) |entry, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(entry.code)));
        try std.testing.expectEqual(@as(usize, 5), entry.code_str.len);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);

        try std.testing.expectEqual(
            @as(u8, if (entry.default_severity == .err) 'E' else 'W'),
            entry.code_str[0],
        );
        try std.testing.expectEqual(@as(u8, '0'), entry.code_str[1]);
        try std.testing.expect(entry.code_str[2] >= '0' and entry.code_str[2] <= '5');
        try std.testing.expect(std.ascii.isDigit(entry.code_str[3]));
        try std.testing.expect(std.ascii.isDigit(entry.code_str[4]));

        var j: usize = i + 1;
        while (j < catalog.len) : (j += 1) {
            try std.testing.expect(!std.mem.eql(u8, entry.code_str, catalog[j].code_str));
        }
    }
}

test "test_drift_guard_zig_files_column_150_and_section_dividers" {
    for ([_][]const u8{ "stage0", "tests", "bench" }) |dir_name| {
        try walkZigDirectoryFormatting(std.testing.allocator, std.testing.io, dir_name);
    }
    try checkZigFileFormattingAndDividers(std.testing.allocator, std.testing.io, "build.zig");
}

test "test_drift_guard_phase1_token_kind_contiguity_and_keyword_table" {
    const token_enum_info = @typeInfo(TokenKind).@"enum";
    const token_values = std.enums.values(TokenKind);
    try std.testing.expectEqual(@as(usize, 112), token_enum_info.field_names.len);
    try std.testing.expectEqual(@as(usize, 112), token_values.len);

    inline for (token_values, 0..) |tok_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(tok_val));
        try std.testing.expectEqual(tok_val, @as(TokenKind, @enumFromInt(@as(u8, @intCast(i)))));
        try std.testing.expectEqualStrings(token_enum_info.field_names[i], @tagName(tok_val));
    }

    const keys = lexer.KEYWORD_OR_PRIM_MAP.keys();
    const values = lexer.KEYWORD_OR_PRIM_MAP.values();
    try std.testing.expectEqual(@as(usize, 64), keys.len);

    var keyword_seen: [45]bool = @splat(false);
    var prim_count: usize = 0;
    for (values) |kind_val| {
        const backing = @backingInt(kind_val);
        if (backing < 45) {
            try std.testing.expect(!keyword_seen[backing]);
            keyword_seen[backing] = true;
        } else {
            try std.testing.expectEqual(TokenKind.prim_type, kind_val);
            prim_count += 1;
        }
    }
    for (keyword_seen) |was_seen| {
        try std.testing.expect(was_seen);
    }
    try std.testing.expectEqual(@as(usize, 19), prim_count);
}

test "test_drift_guard_phase2_cst_node_kind_ast_tag_and_parser_diagnostics" {
    // [1] Verify `CstNodeKind` enum contiguity (`0..N-1`):
    const cst_enum_info = @typeInfo(CstNodeKind).@"enum";
    const cst_values = std.enums.values(CstNodeKind);
    try std.testing.expectEqual(cst_enum_info.field_names.len, cst_values.len);
    inline for (cst_values, 0..) |cst_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(cst_val));
        try std.testing.expectEqual(cst_val, @as(CstNodeKind, @enumFromInt(@as(u8, @intCast(i)))));
        try std.testing.expectEqualStrings(cst_enum_info.field_names[i], @tagName(cst_val));
    }

    // [2] Verify `AstTag` enum contiguity (`0..M-1`):
    const ast_enum_info = @typeInfo(AstTag).@"enum";
    const ast_values = std.enums.values(AstTag);
    try std.testing.expectEqual(ast_enum_info.field_names.len, ast_values.len);
    inline for (ast_values, 0..) |ast_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(ast_val));
        try std.testing.expectEqual(ast_val, @as(AstTag, @enumFromInt(@as(u8, @intCast(i)))));
        try std.testing.expectEqualStrings(ast_enum_info.field_names[i], @tagName(ast_val));
    }

    // [3] Verify `TokenSet128` covers all 112 `TokenKind`s (`@backingInt(tok) < 128`):
    const token_values = std.enums.values(TokenKind);
    try std.testing.expectEqual(@as(usize, 112), token_values.len);
    var full_set = TokenSet128.EMPTY;
    for (token_values) |tok_val| {
        try std.testing.expect(@backingInt(tok_val) < 128);
        full_set = full_set.unionWith(TokenSet128.initOne(tok_val));
        try std.testing.expect(full_set.contains(tok_val));
    }

    // [4] Verify parser diagnostic codes (`E0201`, `E0202`, `E0203`, `W0201`) in `DIAGNOSTIC_CATALOG`:
    try std.testing.expectEqualStrings(
        "E0201",
        DiagnosticCode.e0201_unexpected_token.asCodeStr(),
    );
    try std.testing.expectEqualStrings(
        "E0202",
        DiagnosticCode.e0202_unclosed_delimiter.asCodeStr(),
    );
    try std.testing.expectEqualStrings(
        "E0203",
        DiagnosticCode.e0203_parse_depth_exceeded.asCodeStr(),
    );
    try std.testing.expectEqualStrings(
        "W0201",
        DiagnosticCode.w0201_non_canonical_identifier_case.asCodeStr(),
    );
}

test "test_drift_guard_phase3_query_db_fmt_engine_and_cli_flags" {
    // [1] Verify `QueryStage` 10-stage enum contiguity (`0..9`) and `query_db` layout parity:
    const stage_values = std.enums.values(corex.QueryStage);
    try std.testing.expectEqual(@as(usize, 10), stage_values.len);
    inline for (stage_values, 0..) |stage_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(stage_val));
    }
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.Revision));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.Durability));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.Fingerprint128));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.DefId));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.QueryKey));
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(corex.MemoHeader));

    // [2] Verify `DocOp`, `GroupMode`, and 8-byte `DocInst` layout parity (`DR-14` Section 1.2):
    const doc_op_values = std.enums.values(corex.DocOp);
    try std.testing.expectEqual(@as(usize, 13), doc_op_values.len);
    inline for (doc_op_values, 0..) |op_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(op_val));
    }
    const group_mode_values = std.enums.values(corex.GroupMode);
    try std.testing.expectEqual(@as(usize, 3), group_mode_values.len);
    inline for (group_mode_values, 0..) |mode_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(mode_val));
    }
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.DocInst));

    // [3] Verify `FMT_FLAGS` (`--check`, `--fix`) parity in `stage0/src/cli/router.zig`:
    try std.testing.expectEqual(@as(usize, 2), router.FMT_FLAGS.len);
    try std.testing.expectEqualStrings("--check", router.FMT_FLAGS[0].long_flag);
    try std.testing.expectEqualStrings("--fix", router.FMT_FLAGS[1].long_flag);
    for (router.FMT_FLAGS, 0..) |fmt_flag, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(fmt_flag.id)));
        try std.testing.expect(fmt_flag.summary.len > 0);
    }
}

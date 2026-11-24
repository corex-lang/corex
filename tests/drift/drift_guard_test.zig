//! Repository-Wide Drift Guards (`tests/drift/drift_guard_test.zig`)
//!
//! Enforces zero colored emojis across the entire repository, 100% parity between `router.zig`
//! tables and `corex --help`, `DIAGNOSTIC_CATALOG` subsystem prefix integrity, Phase 1–10 IR/VM/
//! SAST/ABI/Async/Pkg struct layouts, `DR-08`/`DR-11`/`DR-16`–`DR-23` seams, enum contiguity, and
//! diagnostic coverage, plus `< 150` column line length and 90-char dividers in `.zig`/`.cx` files.
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
            const cp_len = std.unicode.utf8CountCodepoints(trimmed) catch unreachable;
            if ((trimmed.len != 90 or cp_len != 90) and (trimmed.len != 65 or cp_len != 65)) {
                std.debug.print(
                    "Drift Guard 4 divider width violation: `{s}:{d}` has {d}B/{d}cp (expected 90 or 65)\n",
                    .{ zig_path, line_num, trimmed.len, cp_len },
                );
            }
            try std.testing.expect(
                (trimmed.len == 90 and cp_len == 90) or (trimmed.len == 65 and cp_len == 65),
            );
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

/// Asserts that `EnumType` has strictly contiguous integer backing tags `0 .. N - 1`.
fn expectContiguousEnum(comptime EnumType: type) !void {
    @setEvalBranchQuota(20_000);
    const enum_info = @typeInfo(EnumType).@"enum";
    const TagInt = enum_info.tag_type;
    const enum_values = std.enums.values(EnumType);
    try std.testing.expectEqual(enum_info.field_names.len, enum_values.len);
    inline for (enum_values, 0..) |enum_val, i| {
        const expected_tag: TagInt = @intCast(i);
        try std.testing.expectEqual(expected_tag, @backingInt(enum_val));
        try std.testing.expectEqual(enum_val, @as(EnumType, @fromBackingInt(@intCast(expected_tag))));
        try std.testing.expectEqualStrings(enum_info.field_names[i], @tagName(enum_val));
    }
}

/// Scans all `.zig` files under `dir_path` and marks `has_found[i] = true` whenever `identifiers[i]` appears.
fn markReferencedIdentifiersInDir(
    allocator: std.mem.Allocator,
    io: std.Io,
    dir_path: []const u8,
    identifiers: []const []const u8,
    has_found: []bool,
) !void {
    var opened_dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer opened_dir.close(io);

    var walker = try opened_dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.path, ".zig")) continue;
        if (std.mem.endsWith(u8, entry.path, "diagnostic.zig")) continue;
        const full_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ dir_path, entry.path });
        defer allocator.free(full_path);
        const content = try std.Io.Dir.cwd().readFileAlloc(
            io,
            full_path,
            allocator,
            .limited(16 * 1024 * 1024),
        );
        defer allocator.free(content);

        for (identifiers, 0..) |ident_name, i| {
            if (!has_found[i] and std.mem.indexOf(u8, content, ident_name) != null) {
                has_found[i] = true;
            }
        }
    }
}

/// Counts non-comment, non-blank source lines in `zig_path` (excluding blank lines and `//` comment lines).
fn countNonCommentNonBlankLines(
    allocator: std.mem.Allocator,
    io: std.Io,
    zig_path: []const u8,
) !usize {
    const content = try std.Io.Dir.cwd().readFileAlloc(io, zig_path, allocator, .limited(4 * 1024 * 1024));
    defer allocator.free(content);

    var code_line_count: usize = 0;
    var line_iter = std.mem.splitScalar(u8, content, '\n');
    while (line_iter.next()) |raw_line| {
        const trimmed = std.mem.trim(u8, raw_line, " \t\r");
        if (trimmed.len == 0 or std.mem.startsWith(u8, trimmed, "//")) continue;
        code_line_count += 1;
    }
    return code_line_count;
}

/// Verifies `< 150` col lines, 90/65-char dividers, and `corex fmt` idempotency (`!is_changed`) on `cx_path`.
fn checkCxFileFormattingAndDividers(
    allocator: std.mem.Allocator,
    io: std.Io,
    cx_path: []const u8,
) !void {
    const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
        io,
        cx_path,
        allocator,
        .limited(4 * 1024 * 1024),
    );
    defer allocator.free(raw_bytes);

    var norm_buf = try std.ArrayList(u8).initCapacity(allocator, raw_bytes.len);
    defer norm_buf.deinit(allocator);
    for (raw_bytes) |byte_val| {
        if (byte_val != '\r') norm_buf.appendAssumeCapacity(byte_val);
    }

    try checkZigFileFormattingAndDividers(allocator, io, cx_path);

    var fmt_res = try corex.formatSourceWithOptions(
        allocator,
        norm_buf.items,
        corex.FileId.fromInt(0),
        .{},
    );
    defer fmt_res.deinit(allocator);
    try std.testing.expect(!fmt_res.has_syntax_errors);
    if (fmt_res.is_changed) {
        std.debug.print("Drift Guard Phase 7: `{s}` is not formatted canonically\n", .{cx_path});
    }
    try std.testing.expect(!fmt_res.is_changed);
}

/// Walks `dir_path` recursively and verifies every `.cx` file (`>= min_expected_count`) passes `checkCxFileFormattingAndDividers`.
fn walkCxDirectoryFormatting(
    allocator: std.mem.Allocator,
    io: std.Io,
    dir_path: []const u8,
    min_expected_count: usize,
) !void {
    var opened_dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer opened_dir.close(io);

    var walker = try opened_dir.walk(allocator);
    defer walker.deinit();

    var found_cx_count: usize = 0;
    while (try walker.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.path, ".cx")) continue;
        const full_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ dir_path, entry.path });
        defer allocator.free(full_path);
        try checkCxFileFormattingAndDividers(allocator, io, full_path);
        found_cx_count += 1;
    }
    try std.testing.expect(found_cx_count >= min_expected_count);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_drift_guard_zero_colored_emojis_across_repository" {
    for ([_][]const u8{ "stage0", "core", "stdlib", "tests", "bench", "docs", ".agents" }) |dir_name| {
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
    try checkZigFileFormattingAndDividers(std.testing.allocator, std.testing.io, "stage0/src/corex_llvm.h");
    try checkZigFileFormattingAndDividers(std.testing.allocator, std.testing.io, "stage0/src/corex_llvm.cpp");
}

test "test_drift_guard_phase1_token_kind_contiguity_and_keyword_table" {
    @setEvalBranchQuota(20_000);
    const token_enum_info = @typeInfo(TokenKind).@"enum";
    const token_values = std.enums.values(TokenKind);
    try std.testing.expectEqual(@as(usize, 121), token_enum_info.field_names.len);
    try std.testing.expectEqual(@as(usize, 121), token_values.len);

    inline for (token_values, 0..) |tok_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(tok_val));
        try std.testing.expectEqual(tok_val, @as(TokenKind, @fromBackingInt(@intCast(@as(u8, @intCast(i))))));
        try std.testing.expectEqualStrings(token_enum_info.field_names[i], @tagName(tok_val));
    }

    const keys = lexer.KEYWORD_OR_PRIM_MAP.keys();
    const values = lexer.KEYWORD_OR_PRIM_MAP.values();
    try std.testing.expectEqual(@as(usize, 70), keys.len);

    var has_seen_keyword: [50]bool = @splat(false);
    var prim_count: usize = 0;
    for (values) |kind_val| {
        const backing = @backingInt(kind_val);
        if (backing < 50) {
            try std.testing.expect(!has_seen_keyword[backing]);
            has_seen_keyword[backing] = true;
        } else {
            try std.testing.expectEqual(TokenKind.prim_type, kind_val);
            prim_count += 1;
        }
    }
    for (has_seen_keyword) |has_seen| {
        try std.testing.expect(has_seen);
    }
    try std.testing.expectEqual(@as(usize, 20), prim_count);
    try std.testing.expectEqual(TokenKind.prim_type, lexer.KEYWORD_OR_PRIM_MAP.get("opaque").?);
}

test "test_drift_guard_phase2_cst_node_kind_ast_tag_and_parser_diagnostics" {
    @setEvalBranchQuota(20_000);
    // [1] Verify `CstNodeKind` enum contiguity (`0..N-1`):
    const cst_enum_info = @typeInfo(CstNodeKind).@"enum";
    const cst_values = std.enums.values(CstNodeKind);
    try std.testing.expectEqual(cst_enum_info.field_names.len, cst_values.len);
    inline for (cst_values, 0..) |cst_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(cst_val));
        try std.testing.expectEqual(cst_val, @as(CstNodeKind, @fromBackingInt(@intCast(@as(u8, @intCast(i))))));
        try std.testing.expectEqualStrings(cst_enum_info.field_names[i], @tagName(cst_val));
    }

    // [2] Verify `AstTag` enum contiguity (`0..M-1`):
    const ast_enum_info = @typeInfo(AstTag).@"enum";
    const ast_values = std.enums.values(AstTag);
    try std.testing.expectEqual(ast_enum_info.field_names.len, ast_values.len);
    inline for (ast_values, 0..) |ast_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(ast_val));
        try std.testing.expectEqual(ast_val, @as(AstTag, @fromBackingInt(@intCast(@as(u8, @intCast(i))))));
        try std.testing.expectEqualStrings(ast_enum_info.field_names[i], @tagName(ast_val));
    }

    // [3] Verify `TokenSet128` covers all 121 `TokenKind`s (`@backingInt(tok) < 128`):
    const token_values = std.enums.values(TokenKind);
    try std.testing.expectEqual(@as(usize, 121), token_values.len);
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
    // [1] Verify `QueryStage` 14-stage enum contiguity (`0..13`) and `query_db` layout parity:
    const stage_values = std.enums.values(corex.QueryStage);
    try std.testing.expectEqual(@as(usize, 14), stage_values.len);
    inline for (stage_values, 0..) |stage_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(stage_val));
    }
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.Revision));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.Durability));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.Fingerprint128));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.DefId));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.QueryKey));
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(corex.MemoHeader));

    // [2] Verify `DocOp`, `GroupMode`, and 8-byte `DocInst` layout parity (`DR-14` Section 1.2 & `DR-22` §3.4):
    const doc_op_values = std.enums.values(corex.DocOp);
    try std.testing.expectEqual(@as(usize, 14), doc_op_values.len);
    try std.testing.expectEqual(@as(u8, 13), @backingInt(corex.DocOp.multiline_string));
    inline for (doc_op_values, 0..) |op_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(op_val));
    }
    const group_mode_values = std.enums.values(corex.GroupMode);
    try std.testing.expectEqual(@as(usize, 3), group_mode_values.len);
    inline for (group_mode_values, 0..) |mode_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(mode_val));
    }
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.DocInst));

    // [3] Verify `FMT_FLAGS` (`--check`, `--fix`, `--internal-core`) and `UPGRADE_FLAGS` parity in `stage0/src/cli/router.zig`:
    try std.testing.expectEqual(@as(usize, 3), router.FMT_FLAGS.len);
    try std.testing.expectEqualStrings("--check", router.FMT_FLAGS[0].long_flag);
    try std.testing.expectEqualStrings("--fix", router.FMT_FLAGS[1].long_flag);
    try std.testing.expectEqualStrings("--internal-core", router.FMT_FLAGS[2].long_flag);
    for (router.FMT_FLAGS, 0..) |fmt_flag, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(fmt_flag.id)));
        try std.testing.expect(fmt_flag.summary.len > 0);
    }

    try std.testing.expectEqual(@as(usize, 6), router.UPGRADE_FLAGS.len);
    try std.testing.expectEqualStrings("--accept-caps", router.UPGRADE_FLAGS[0].long_flag);
    try std.testing.expectEqualStrings("--check", router.UPGRADE_FLAGS[1].long_flag);
    try std.testing.expectEqualStrings("--explain", router.UPGRADE_FLAGS[2].long_flag);
    try std.testing.expectEqualStrings("--internal-core", router.UPGRADE_FLAGS[3].long_flag);
    try std.testing.expectEqualStrings("--list", router.UPGRADE_FLAGS[4].long_flag);
    try std.testing.expectEqualStrings("--rule", router.UPGRADE_FLAGS[5].long_flag);
    for (router.UPGRADE_FLAGS, 0..) |upg_flag, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(upg_flag.id)));
        try std.testing.expect(upg_flag.summary.len > 0);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.UPGRADE_FLAGS[i - 1].long_flag, upg_flag.long_flag),
            );
        }
    }
}

test "test_drift_guard_phase4_type_node_layout_type_groups_and_diagnostics" {
    // [1] Verify 14-byte SoA `TypeNode` column layout and `TypeTag` enum contiguity (`DR-04` Section 2.1):
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.TypeTag));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.TypeFlags));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.ParamMode));
    try std.testing.expectEqual(
        @as(usize, 14),
        @sizeOf(corex.TypeTag) + @sizeOf(corex.TypeFlags) + 3 * @sizeOf(u32),
    );

    const type_tag_values = std.enums.values(corex.TypeTag);
    inline for (type_tag_values, 0..) |tag_val, i| {
        try std.testing.expectEqual(@as(u8, @intCast(i)), @backingInt(tag_val));
    }

    // [2] Verify Constrained Type Groups in `TypeGroupMask` (`32..44`, slot `37` retired by `ADR-22D`):
    var grp_slot: u32 = 32;
    while (grp_slot <= 44) : (grp_slot += 1) {
        const grp_id = corex.TypeId.fromInt(grp_slot);
        if (grp_slot == 37) {
            try std.testing.expectEqual(corex.TypeId._retired_group_numeric, grp_id);
            try std.testing.expect(!grp_id.isBuiltinGroup());
            try std.testing.expectEqual(@as(u32, 0), corex.TypeGroupMask.forBuiltinGroup(grp_id));
        } else {
            try std.testing.expect(grp_id.isBuiltinGroup());
            try std.testing.expect(corex.TypeGroupMask.forBuiltinGroup(grp_id) != 0);
        }
    }

    // [3] Verify Phase 4 diagnostic codes (`E0400`–`E0415`, `W0401`, `W0402`, `E0502`):
    try std.testing.expectEqualStrings("E0400", DiagnosticCode.e0400_ambiguous_overload.asCodeStr());
    try std.testing.expectEqualStrings("E0401", DiagnosticCode.e0401_type_mismatch.asCodeStr());
    try std.testing.expectEqualStrings("E0402", DiagnosticCode.e0402_unsatisfied_trait_bound.asCodeStr());
    try std.testing.expectEqualStrings("E0403", DiagnosticCode.e0403_unresolved_symbol.asCodeStr());
    try std.testing.expectEqualStrings("E0404", DiagnosticCode.e0404_bind_once_group_conflict.asCodeStr());
    try std.testing.expectEqualStrings("E0405", DiagnosticCode.e0405_distinct_type_mixing.asCodeStr());
    try std.testing.expectEqualStrings("E0406", DiagnosticCode.e0406_range_refinement_violation.asCodeStr());
    try std.testing.expectEqualStrings("E0407", DiagnosticCode.e0407_invalid_contextual_variant.asCodeStr());
    try std.testing.expectEqualStrings("E0408", DiagnosticCode.e0408_duplicate_definition.asCodeStr());
    try std.testing.expectEqualStrings("E0409", DiagnosticCode.e0409_private_symbol_access.asCodeStr());
    try std.testing.expectEqualStrings("E0410", DiagnosticCode.e0410_try_outside_fallible_fn.asCodeStr());
    try std.testing.expectEqualStrings("E0411", DiagnosticCode.e0411_missing_from_error_conversion.asCodeStr());
    try std.testing.expectEqualStrings("E0412", DiagnosticCode.e0412_let_else_not_diverging.asCodeStr());
    try std.testing.expectEqualStrings("E0413", DiagnosticCode.e0413_unhandled_must_use_or_result.asCodeStr());
    try std.testing.expectEqualStrings("E0414", DiagnosticCode.e0414_bare_wildcard_result_discard.asCodeStr());
    try std.testing.expectEqualStrings("E0415", DiagnosticCode.e0415_non_exhaustive_match.asCodeStr());
    try std.testing.expectEqualStrings("W0401", DiagnosticCode.w0401_unreachable_pattern_arm.asCodeStr());
    try std.testing.expectEqualStrings("W0402", DiagnosticCode.w0402_unused_binding.asCodeStr());
    try std.testing.expectEqualStrings("E0502", DiagnosticCode.e0502_integer_constant_overflow.asCodeStr());
}

test "test_drift_guard_phase5_hir_mir_vm_opt_layouts_cli_flags_and_diagnostics" {
    // [1] Verify exact byte sizes of all canonical Phase 5 structs and handles:
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.HirTag));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.HirFlags));
    try std.testing.expectEqual(
        @as(usize, 18),
        @sizeOf(corex.HirTag) +
            @sizeOf(corex.HirFlags) +
            @sizeOf(corex.TypeId) +
            @sizeOf(corex.TokenIndex) +
            @sizeOf(corex.HirNode.Data),
    );
    try std.testing.expectEqual(@as(usize, 20), @sizeOf(corex.HirNode));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.BitSpec));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.LocalDecl));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.MirPlace));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.MirProjection));
    try std.testing.expectEqual(
        @as(usize, 16),
        @sizeOf(corex.MirOp) +
            @sizeOf(corex.InstFlags) +
            @sizeOf(u16) +
            @sizeOf(corex.TypeId) +
            @sizeOf(corex.MirInst.Operands),
    );
    try std.testing.expectEqual(@as(usize, 12), @sizeOf(corex.MirTerminator));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.MirBasicBlock));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.MirOutgoingEdge));
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.ComptimeAllocId));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.SymbolicPtr));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.RegSlot));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.ProvenanceEntry));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.LayoutShapeKey));

    // [2] Verify contiguity (`0..N-1`) of all Phase 5 IR and intrinsic enums:
    try expectContiguousEnum(corex.HirTag);
    try expectContiguousEnum(corex.MirOp);
    try expectContiguousEnum(corex.BinOpKind);
    try expectContiguousEnum(corex.UnaryOpKind);
    try expectContiguousEnum(corex.TerminatorKind);
    try expectContiguousEnum(corex.IntrinsicKind);

    // [3] Verify `router.COMPILE_FLAGS` alphabetical sorting, summaries, subcommand help, and `parseArgs`:
    try std.testing.expectEqual(@as(usize, 25), router.COMPILE_FLAGS.len);
    const expected_compile_flags = [_][]const u8{
        "--comptime-limit",
        "--define",
        "--dev",
        "--diff-backends",
        "--emit-c",
        "--emit-llvm",
        "--emit-obj",
        "--features",
        "--frozen",
        "--fuzz",
        "--include-dir",
        "--internal-core",
        "--lib",
        "--lib-dir",
        "--link",
        "--locked",
        "--manifest-path",
        "--no-default-features",
        "--offline",
        "--ofmt",
        "--output",
        "--release",
        "--sast-strict",
        "--target",
        "--verify-checksums",
    };
    try std.testing.expectEqualStrings("-F", router.COMPILE_FLAGS[7].short_flag.?);
    for (router.COMPILE_FLAGS, 0..) |comp_flag, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(comp_flag.id)));
        try std.testing.expectEqualStrings(expected_compile_flags[i], comp_flag.long_flag);
        try std.testing.expect(comp_flag.summary.len > 0);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.COMPILE_FLAGS[i - 1].long_flag, comp_flag.long_flag),
            );
        }
    }

    const compile_subcommands = [_]router.SubcommandId{ .build, .run, .check, .test_cmd };
    for (compile_subcommands) |sub_id| {
        var sub_help_buf: [16384]u8 = undefined;
        var sub_help_writer = std.Io.Writer.fixed(&sub_help_buf);
        try router.renderSubcommandHelp(&sub_help_writer, StyleConfig.MONOCHROME, sub_id);
        const sub_help_out = sub_help_writer.buffered();
        for (router.COMPILE_FLAGS) |comp_flag| {
            try std.testing.expect(std.mem.indexOf(u8, sub_help_out, comp_flag.long_flag) != null);
            if (comp_flag.short_flag) |short_s| {
                try std.testing.expect(std.mem.indexOf(u8, sub_help_out, short_s) != null);
            }
            try std.testing.expect(std.mem.indexOf(u8, sub_help_out, comp_flag.summary) != null);
        }

        if (sub_id == .@"test") {
            try std.testing.expectEqual(@as(usize, 2), router.TEST_FLAGS.len);
            try std.testing.expectEqualStrings("--seed", router.TEST_FLAGS[0].long_flag);
            try std.testing.expectEqualStrings("--sim", router.TEST_FLAGS[1].long_flag);
            for (router.TEST_FLAGS) |tst_flag| {
                try std.testing.expect(std.mem.indexOf(u8, sub_help_out, tst_flag.long_flag) != null);
                try std.testing.expect(std.mem.indexOf(u8, sub_help_out, tst_flag.summary) != null);
            }
        }

        const sub_name = sub_id.asDescriptor().name;
        var dev_sink = corex.DiagnosticSink.init(std.testing.allocator);
        defer dev_sink.deinit();
        const parsed_dev = try router.parseArgs(
            &.{ sub_name, "--dev", "--comptime-limit=250000" },
            &dev_sink,
        );
        try std.testing.expect(!dev_sink.hasErrors());
        try std.testing.expect(!parsed_dev.is_release_mode);
        try std.testing.expectEqual(@as(u64, 250_000), parsed_dev.comptime_step_limit);

        var rel_sink = corex.DiagnosticSink.init(std.testing.allocator);
        defer rel_sink.deinit();
        const parsed_rel = try router.parseArgs(
            &.{ sub_name, "--release", "--comptime-limit=500000" },
            &rel_sink,
        );
        try std.testing.expect(!rel_sink.hasErrors());
        try std.testing.expect(parsed_rel.is_release_mode);
        try std.testing.expectEqual(@as(u64, 500_000), parsed_rel.comptime_step_limit);
    }

    // [4] Verify all 11 Phase 5 diagnostic codes (`E0501`–`E0510`, `W0501`) and test suite coverage:
    const phase5_specs = [_]struct {
        /// Canonical Phase 5 `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0501_comptime_step_limit_exceeded, .expected_str = "E0501" },
        .{ .code = .e0502_integer_constant_overflow, .expected_str = "E0502" },
        .{ .code = .e0503_forbidden_comptime_operation, .expected_str = "E0503" },
        .{ .code = .e0504_comptime_out_of_bounds, .expected_str = "E0504" },
        .{ .code = .e0505_comptime_uninitialized_read, .expected_str = "E0505" },
        .{ .code = .e0506_comptime_invalid_pointer, .expected_str = "E0506" },
        .{ .code = .e0507_comptime_arithmetic_trap, .expected_str = "E0507" },
        .{ .code = .e0508_comptime_resource_limit_exceeded, .expected_str = "E0508" },
        .{ .code = .e0509_comptime_evaluation_cycle, .expected_str = "E0509" },
        .{ .code = .e0510_compile_assertion_failed, .expected_str = "E0510" },
        .{ .code = .w0501_inlining_budget_exceeded, .expected_str = "W0501" },
    };

    var tag_identifiers: [phase5_specs.len][]const u8 = undefined;
    var has_test_reference: [phase5_specs.len]bool = @splat(false);
    for (phase5_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots",
        &tag_identifiers,
        &has_test_reference,
    );
    for (has_test_reference, 0..) |has_ref, i| {
        if (!has_ref) {
            std.debug.print(
                "Phase 5 diagnostic `{s}` is not referenced in `tests/unit/` or `tests/snapshots/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_ref);
    }
}

test "test_drift_guard_phase6_sast_layouts_seams_cli_and_diagnostics" {
    // [1] Verify exact Phase 6 SAST, summary, MovePath, and Pentagon byte-layout invariants:
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(corex.FnRegionSummary));
    try std.testing.expectEqual(@as(usize, 34), corex.FnRegionSummary.OBSERVABLE_SUMMARY_BYTES);
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(corex.EffectCapabilityMask));
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(corex.FnContractScratchMask));
    try std.testing.expectEqual(@as(usize, 12), @sizeOf(corex.WitnessCallEdge));
    try std.testing.expectEqual(@as(usize, 20), @sizeOf(corex.MovePathNode));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.Intv));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.PentagonSubRow));
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.type_system.TypeFlags));

    // [2] Verify contiguity (`0..N-1`) of Phase 6 ownership, witness, and capability-scope enums:
    try expectContiguousEnum(corex.OwnershipTier);
    try expectContiguousEnum(corex.WitnessEdgeKind);
    try expectContiguousEnum(corex.mir_sast.CapEnforcementScope);

    // [3] Verify `--sast-strict` CLI flag parsing and `DR-20` seams (`trace_sink` & `is_secret`):
    var strict_sink = corex.DiagnosticSink.init(std.testing.allocator);
    defer strict_sink.deinit();
    const parsed_strict = try router.parseArgs(&.{ "check", "--sast-strict" }, &strict_sink);
    try std.testing.expect(!strict_sink.hasErrors());
    try std.testing.expect(parsed_strict.is_sast_strict);

    var default_sink = corex.DiagnosticSink.init(std.testing.allocator);
    defer default_sink.deinit();
    const parsed_default = try router.parseArgs(&.{"check"}, &default_sink);
    try std.testing.expect(!default_sink.hasErrors());
    try std.testing.expect(!parsed_default.is_sast_strict);

    const trace_sink_layout = corex.ContextFieldLayout.fromFieldName("trace_sink");
    try std.testing.expect(trace_sink_layout != null);
    try std.testing.expectEqual(corex.ContextFieldKind.trace_sink, trace_sink_layout.?.kind);

    try std.testing.expect(!(corex.type_system.TypeFlags{}).is_secret);
    try std.testing.expect((corex.type_system.TypeFlags{ .is_secret = true }).is_secret);

    // [4] Verify all 23 Phase 6 diagnostic codes (`E03xx` & `W03xx`) and test suite coverage:
    const phase6_specs = [_]struct {
        /// Canonical Phase 6 `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0301_use_after_free, .expected_str = "E0301" },
        .{ .code = .e0302_use_after_move, .expected_str = "E0302" },
        .{ .code = .e0303_uninitialized_memory_read, .expected_str = "E0303" },
        .{ .code = .e0304_resource_or_memory_leak, .expected_str = "E0304" },
        .{ .code = .e0305_exclusivity_violation, .expected_str = "E0305" },
        .{ .code = .e0306_region_escape_violation, .expected_str = "E0306" },
        .{ .code = .e0307_static_buffer_overflow, .expected_str = "E0307" },
        .{ .code = .e0313_double_free_or_close, .expected_str = "E0313" },
        .{ .code = .e0315_wire_layout_contract_violation, .expected_str = "E0315" },
        .{ .code = .e0316_max_stack_budget_exceeded, .expected_str = "E0316" },
        .{ .code = .e0320_no_alloc_contract_violation, .expected_str = "E0320" },
        .{ .code = .e0321_no_panic_contract_violation, .expected_str = "E0321" },
        .{ .code = .e0322_no_block_contract_violation, .expected_str = "E0322" },
        .{ .code = .e0323_trait_impl_effect_escalation, .expected_str = "E0323" },
        .{ .code = .e0324_package_capability_violation, .expected_str = "E0324" },
        .{ .code = .e0325_comptime_sandbox_violation, .expected_str = "E0325" },
        .{ .code = .e0326_embed_path_escape, .expected_str = "E0326" },
        .{ .code = .e0327_forbidden_sandbox_bypass_attribute, .expected_str = "E0327" },
        .{ .code = .e0328_scratch_arena_ping_pong_conflict, .expected_str = "E0328" },
        .{ .code = .w0308_unused_region_allocation, .expected_str = "W0308" },
        .{ .code = .w0314_unproven_bounds_access, .expected_str = "W0314" },
        .{ .code = .w0329_vacated_projection_panic_abort, .expected_str = "W0329" },
        .{ .code = .w0330_ambient_dead_capability_in_dep, .expected_str = "W0330" },
    };

    var tag_identifiers: [phase6_specs.len][]const u8 = undefined;
    var has_test_reference: [phase6_specs.len]bool = @splat(false);
    for (phase6_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots",
        &tag_identifiers,
        &has_test_reference,
    );
    for (has_test_reference, 0..) |has_ref, i| {
        if (!has_ref) {
            std.debug.print(
                "Phase 6 diagnostic `{s}` is not referenced in `tests/unit/` or `tests/snapshots/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_ref);
    }

    // [5] Verify canonical intrinsic, built-in attribute, and 12-bit `DR-17` capability lookup tables:
    try expectContiguousEnum(corex.type_system.IntrinsicKind);
    try std.testing.expectEqual(
        @typeInfo(corex.type_system.IntrinsicKind).@"enum".field_names.len,
        corex.type_system.INTRINSIC_NAME_MAP.keys().len,
    );
    inline for (std.enums.values(corex.type_system.IntrinsicKind)) |intrinsic_val| {
        try std.testing.expectEqual(
            intrinsic_val,
            corex.type_system.INTRINSIC_NAME_MAP.get(@tagName(intrinsic_val)).?,
        );
    }

    const required_phase6_attrs = [_][]const u8{
        "ifunc",
        "linear",
        "local",
        "max_stack",
        "no_alloc",
        "no_block",
        "no_panic",
        "secret",
        "std_cap_boundary",
        "zero_pad",
    };
    for (required_phase6_attrs) |attr_name| {
        try std.testing.expect(corex.type_system.BUILTIN_ATTRIBUTE_MAP.has(attr_name));
    }

    const canonical_caps = [_]struct {
        /// Canonical lowercase `DR-17` §2.1 capability name.
        snake_name: []const u8,
        /// Canonical `PascalCase` `DR-17` §2.1 capability name.
        pascal_name: []const u8,
        /// Expected distinct single-bit position (`0..11`).
        expected_bit: u16,
    }{
        .{ .snake_name = "fs", .pascal_name = "Fs", .expected_bit = 1 << 0 },
        .{ .snake_name = "net", .pascal_name = "Net", .expected_bit = 1 << 1 },
        .{ .snake_name = "env", .pascal_name = "Env", .expected_bit = 1 << 2 },
        .{ .snake_name = "process", .pascal_name = "Process", .expected_bit = 1 << 3 },
        .{ .snake_name = "ffi", .pascal_name = "Ffi", .expected_bit = 1 << 4 },
        .{ .snake_name = "unsafe_op", .pascal_name = "UnsafeOp", .expected_bit = 1 << 5 },
        .{ .snake_name = "alloc", .pascal_name = "Alloc", .expected_bit = 1 << 6 },
        .{ .snake_name = "may_panic", .pascal_name = "MayPanic", .expected_bit = 1 << 7 },
        .{ .snake_name = "clock", .pascal_name = "Clock", .expected_bit = 1 << 8 },
        .{ .snake_name = "entropy", .pascal_name = "Entropy", .expected_bit = 1 << 9 },
        .{ .snake_name = "blocking_sync", .pascal_name = "BlockingSync", .expected_bit = 1 << 10 },
        .{ .snake_name = "indirect_opaque", .pascal_name = "IndirectOpaque", .expected_bit = 1 << 11 },
    };
    var combined_cap_bits: u16 = 0;
    for (canonical_caps) |cap_spec| {
        try std.testing.expectEqual(
            cap_spec.expected_bit,
            corex.symbol_resolver.CAPABILITY_NAME_MAP.get(cap_spec.snake_name).?,
        );
        try std.testing.expectEqual(
            cap_spec.expected_bit,
            corex.symbol_resolver.CAPABILITY_NAME_MAP.get(cap_spec.pascal_name).?,
        );
        combined_cap_bits |= cap_spec.expected_bit;
    }
    try std.testing.expectEqual(@as(u16, 0x0FFF), combined_cap_bits);
}

test "test_drift_guard_phase7_abi_codegen_seam_layouts_and_core" {
    // [1] Verify exact Phase 7 ABI, layout, Pentagon range, loop-contract, and dev-seam byte sizes:
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.TargetSpec));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.NicheSpec));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.ResolvedTypeLayout));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.AbiParamRecipe));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.ProvenValueRange));
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.mir.LoopContractMeta));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.MirBasicBlock));
    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.CxDevSeamHeader));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.CxGotSlotMeta));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.CxTypeLayoutRecord));
    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.CxReloadControlBlock));

    // [2] Verify Apple Silicon (`aarch64-macos`) `128B` (`2^7`) `@cache_aligned` layout invariant (`D-10A`).
    try std.testing.expectEqual(
        @as(u8, 7),
        corex.TargetSpec.AARCH64_MACOS.asTargetLayout().cache_line_align_log2,
    );
    try std.testing.expectEqual(
        @as(u8, 6),
        corex.TargetSpec.X86_64_LINUX.asTargetLayout().cache_line_align_log2,
    );

    // [3] Verify `stage0/src/codegen_dev_seam.zig` stays strictly `< 200` lines (`Prune-04`).
    const seam_bytes = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "stage0/src/codegen_dev_seam.zig",
        std.testing.allocator,
        .limited(1024 * 1024),
    );
    defer std.testing.allocator.free(seam_bytes);
    var seam_line_count: usize = 1;
    for (seam_bytes) |byte_val| {
        if (byte_val == '\n') seam_line_count += 1;
    }
    if (seam_bytes.len > 0 and seam_bytes[seam_bytes.len - 1] == '\n') {
        seam_line_count -= 1;
    }
    try std.testing.expect(seam_line_count < 200);

    // [4] Verify all `core/**/*.cx` and `stdlib/cx/**/*.cx` files obey `< 150` cols, 90/65-char dividers, and `corex fmt --check`:
    try walkCxDirectoryFormatting(std.testing.allocator, std.testing.io, "core", 14);
    try walkCxDirectoryFormatting(std.testing.allocator, std.testing.io, "stdlib/cx", 5);

    // [5] Verify Phase 7 diagnostics (`E0006`, `E0007`, `E0008`) and test-suite references:
    const phase7_specs = [_]struct {
        /// Canonical Phase 7 `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0006_invalid_target_triple, .expected_str = "E0006" },
        .{ .code = .e0007_codegen_backend_failure, .expected_str = "E0007" },
        .{ .code = .e0008_linker_invocation_failed, .expected_str = "E0008" },
    };

    var tag_identifiers: [phase7_specs.len][]const u8 = undefined;
    var has_test_reference: [phase7_specs.len]bool = @splat(false);
    for (phase7_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    for (has_test_reference, 0..) |has_ref, i| {
        if (!has_ref) {
            std.debug.print(
                "Phase 7 diagnostic `{s}` is not referenced in `tests/unit/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_ref);
    }
}

test "test_drift_guard_phase7_5_dr21_surface_syntax_and_diagnostics" {
    // [1] Verify retired tokens and canonical `121`-variant `TokenKind` ordinals (`DR-21`, `DR-22` §3.1 & `DR-24` §2.1):
    try std.testing.expect(!@hasField(TokenKind, "coloncolon"));
    try std.testing.expect(!@hasDecl(TokenKind, "colon_colon"));
    try std.testing.expect(!@hasField(TokenKind, "kw_ref"));
    try std.testing.expect(!@hasField(TokenKind, "ampamp"));
    try std.testing.expect(!@hasDecl(TokenKind, "amp_amp"));
    try std.testing.expectEqual(@as(u8, 16), @backingInt(TokenKind.kw_subscript));
    try std.testing.expectEqual(@as(u8, 27), @backingInt(TokenKind.kw_with));
    try std.testing.expectEqual(@as(u8, 28), @backingInt(TokenKind.kw_context));
    try std.testing.expectEqual(@as(u8, 40), @backingInt(TokenKind.kw_orelse));
    try std.testing.expectEqual(@as(u8, 41), @backingInt(TokenKind.kw_unreachable));
    try std.testing.expectEqual(@as(u8, 42), @backingInt(TokenKind.kw_yield));
    try std.testing.expectEqual(@as(u8, 58), @backingInt(TokenKind.byte_lit));
    try std.testing.expectEqual(@as(u8, 59), @backingInt(TokenKind.byte_string_lit));
    try std.testing.expectEqual(@as(u8, 60), @backingInt(TokenKind.fmt_string_lit));
    try std.testing.expectEqual(@as(u8, 73), @backingInt(TokenKind.dotdotdot));
    try std.testing.expectEqual(@as(u8, 81), @backingInt(TokenKind.colon_eq));
    try std.testing.expectEqual(@as(u8, 82), @backingInt(TokenKind.dollar));

    // [2] Verify `--internal-core` CLI flag parsing and subcommand `--help` parity across `check`, `fmt`, and `upgrade`:
    var internal_sink = corex.DiagnosticSink.init(std.testing.allocator);
    defer internal_sink.deinit();
    const parsed_internal = try router.parseArgs(&.{ "check", "--internal-core" }, &internal_sink);
    try std.testing.expect(!internal_sink.hasErrors());
    try std.testing.expect(parsed_internal.is_internal_core);

    const parsed_fmt_internal = try router.parseArgs(&.{ "fmt", "--internal-core" }, &internal_sink);
    try std.testing.expect(!internal_sink.hasErrors());
    try std.testing.expect(parsed_fmt_internal.is_internal_core);

    const parsed_upg_internal = try router.parseArgs(&.{ "upgrade", "--internal-core" }, &internal_sink);
    try std.testing.expect(!internal_sink.hasErrors());
    try std.testing.expect(parsed_upg_internal.is_internal_core);

    var fmt_help_buf: [2048]u8 = undefined;
    var fmt_help_writer = std.Io.Writer.fixed(&fmt_help_buf);
    try router.renderSubcommandHelp(&fmt_help_writer, corex.StyleConfig.MONOCHROME, .fmt);
    try std.testing.expect(std.mem.indexOf(u8, fmt_help_writer.buffered(), "--internal-core") != null);

    var upg_help_buf: [2048]u8 = undefined;
    var upg_help_writer = std.Io.Writer.fixed(&upg_help_buf);
    try router.renderSubcommandHelp(&upg_help_writer, corex.StyleConfig.MONOCHROME, .upgrade);
    try std.testing.expect(std.mem.indexOf(u8, upg_help_writer.buffered(), "--internal-core") != null);

    var default_sink = corex.DiagnosticSink.init(std.testing.allocator);
    defer default_sink.deinit();
    const parsed_default = try router.parseArgs(&.{"check"}, &default_sink);
    try std.testing.expect(!default_sink.hasErrors());
    try std.testing.expect(!parsed_default.is_internal_core);

    // [3] Verify 10-slot `ContextFieldKind` contiguity (`0..9`) and `ContextFieldLayout` lookup (`SE-08`, `DR-08`):
    try expectContiguousEnum(corex.ContextFieldKind);
    try std.testing.expectEqual(@as(usize, 10), std.enums.values(corex.ContextFieldKind).len);
    const expected_ctx_slots = [_]struct {
        /// Canonical `Context` field identifier.
        name: []const u8,
        /// Expected `ContextFieldKind` slot discriminant (`0..9`).
        kind: corex.ContextFieldKind,
    }{
        .{ .name = "allocator", .kind = .allocator },
        .{ .name = "scratch", .kind = .scratch },
        .{ .name = "rng_seed", .kind = .rng_seed },
        .{ .name = "trace_sink", .kind = .trace_sink },
        .{ .name = "temp_allocator", .kind = .temp_allocator },
        .{ .name = "logger", .kind = .logger },
        .{ .name = "diagnostics", .kind = .diagnostics },
        .{ .name = "cancel_token", .kind = .cancel_token },
        .{ .name = "reactor", .kind = .reactor },
        .{ .name = "reactor_ctx", .kind = .reactor_ctx },
    };
    for (expected_ctx_slots, 0..) |slot_spec, i| {
        const resolved = corex.ContextFieldLayout.fromFieldName(slot_spec.name);
        try std.testing.expect(resolved != null);
        try std.testing.expectEqual(slot_spec.kind, resolved.?.kind);
        try std.testing.expectEqual(@as(u8, @intCast(i)), resolved.?.slot_ordinal);
    }

    // [4] Verify all 8 `DR-21` `DiagnosticCode` tags (`146` total catalog entries) and test coverage:
    try std.testing.expectEqual(@as(usize, 146), diagnostic.DIAGNOSTIC_CATALOG.len);
    const dr21_specs = [_]struct {
        /// Canonical Phase 7.5 `DR-21` `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0112_retired_path_separator, .expected_str = "E0112" },
        .{ .code = .e0214_invalid_condition_binding, .expected_str = "E0214" },
        .{ .code = .e0215_invalid_walrus_position, .expected_str = "E0215" },
        .{ .code = .e0216_retired_if_while_let, .expected_str = "E0216" },
        .{ .code = .e0218_direct_core_import_forbidden, .expected_str = "E0218" },
        .{ .code = .e0416_invalid_dollar_length_expr, .expected_str = "E0416" },
        .{ .code = .e0418_irrefutable_is_binding, .expected_str = "E0418" },
        .{ .code = .e0419_invalid_call_arguments, .expected_str = "E0419" },
    };

    var tag_identifiers: [dr21_specs.len][]const u8 = undefined;
    var has_test_reference: [dr21_specs.len]bool = @splat(false);
    for (dr21_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots",
        &tag_identifiers,
        &has_test_reference,
    );
    for (has_test_reference, 0..) |has_ref, i| {
        if (!has_ref) {
            std.debug.print(
                "Phase 7.5 diagnostic `{s}` is not referenced in `tests/unit/` or `tests/snapshots/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_ref);
    }
}

test "test_drift_guard_phase7_6_dr22_surface_syntax_upgrade_rules_and_diagnostics" {
    // [1] Verify `UPGRADE_RULE_CATALOG` (`UR-21-00`–`UR-24-06`) contiguous parity:
    try expectContiguousEnum(corex.UpgradeRuleId);
    const upgrade_catalog = corex.upgrade_rules.UPGRADE_RULE_CATALOG;
    try std.testing.expectEqual(@as(usize, 29), upgrade_catalog.len);

    const expected_rule_codes = [_][]const u8{
        "UR-21-00",
        "UR-21-01",
        "UR-21-02",
        "UR-21-03",
        "UR-21-04",
        "UR-21-05",
        "UR-21-06",
        "UR-21-07",
        "UR-22-00",
        "UR-22-01",
        "UR-22-02",
        "UR-22-03",
        "UR-22-04",
        "UR-22-05",
        "UR-22-06",
        "UR-23-00",
        "UR-23-01",
        "UR-23-02",
        "UR-23-03",
        "UR-23-04",
        "UR-23-05",
        "UR-23-06",
        "UR-24-00",
        "UR-24-01",
        "UR-24-02",
        "UR-24-03",
        "UR-24-04",
        "UR-24-05",
        "UR-24-06",
    };
    for (upgrade_catalog, 0..) |rule_desc, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(rule_desc.id)));
        try std.testing.expectEqualStrings(expected_rule_codes[i], rule_desc.rule_code);
        try std.testing.expect(rule_desc.summary.len > 0);
        try std.testing.expectEqual(
            rule_desc.id,
            corex.upgrade_rules.lookupUpgradeRule(rule_desc.rule_code).?,
        );
        var j: usize = i + 1;
        while (j < upgrade_catalog.len) : (j += 1) {
            try std.testing.expect(!std.mem.eql(u8, rule_desc.rule_code, upgrade_catalog[j].rule_code));
        }
    }

    // [2] Verify `DR-22` built-in attributes (`builder`, `builder_item`, `cfg`, `constructor`) & `FmtSpec`:
    const required_dr22_attrs = [_][]const u8{
        "builder",
        "builder_item",
        "cfg",
        "constructor",
    };
    for (required_dr22_attrs) |attr_name| {
        try std.testing.expect(corex.type_system.BUILTIN_ATTRIBUTE_MAP.has(attr_name));
    }
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.FmtSpec));
    try std.testing.expectEqual(@as(u32, 22), corex.TypeId.opaque_ty.toU32());
    try std.testing.expectEqual(@as(u32, 45), corex.TypeId.source_loc_ty.toU32());
    try std.testing.expectEqual(@as(u32, 46), corex.TypeId.fmt_spec_ty.toU32());
    try std.testing.expectEqual(@as(u32, 47), corex.TypeId.fmt_args_ty.toU32());
    try std.testing.expectEqual(@as(u32, 48), corex.TypeId.bencher_ty.toU32());
    try std.testing.expectEqual(@as(u32, 49), corex.TypeId.task_group_base_ty.toU32());
    try std.testing.expectEqual(@as(u32, 50), corex.TypeId.task_handle_base_ty.toU32());

    // [3] Verify all 33 `DR-22` `DiagnosticCode` tags (`E0113`–`E0117`, `E0219`–`E0228`, `E0420`–`E0437`):
    const dr22_specs = [_]struct {
        /// Canonical Phase 7.6 `DR-22` `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0113_retired_logical_and, .expected_str = "E0113" },
        .{ .code = .e0114_invalid_brace_escape, .expected_str = "E0114" },
        .{ .code = .e0115_multiline_string_opening, .expected_str = "E0115" },
        .{ .code = .e0116_multiline_string_indent, .expected_str = "E0116" },
        .{ .code = .e0117_non_ascii_byte_literal, .expected_str = "E0117" },
        .{ .code = .e0219_retired_logical_or, .expected_str = "E0219" },
        .{ .code = .e0220_retired_bang_prefix, .expected_str = "E0220" },
        .{ .code = .e0221_retired_mutability_or_param_mode, .expected_str = "E0221" },
        .{ .code = .e0222_chained_result_type, .expected_str = "E0222" },
        .{ .code = .e0223_retired_attribute_eq, .expected_str = "E0223" },
        .{ .code = .e0224_retired_semicolon_member_sep, .expected_str = "E0224" },
        .{ .code = .e0225_retired_noalloc_attribute, .expected_str = "E0225" },
        .{ .code = .e0226_retired_const_raw_ptr, .expected_str = "E0226" },
        .{ .code = .e0227_retired_prefix_deref, .expected_str = "E0227" },
        .{ .code = .e0228_invalid_param_zone_separator, .expected_str = "E0228" },
        .{ .code = .e0420_missing_call_site_own, .expected_str = "E0420" },
        .{ .code = .e0421_non_copy_value_parameter, .expected_str = "E0421" },
        .{ .code = .e0422_out_param_contract_violation, .expected_str = "E0422" },
        .{ .code = .e0423_invalid_bitfield_or_enum_cast, .expected_str = "E0423" },
        .{ .code = .e0424_retired_slice_field_access, .expected_str = "E0424" },
        .{ .code = .e0425_invalid_opaque_type_usage, .expected_str = "E0425" },
        .{ .code = .e0426_non_trailing_generic_default, .expected_str = "E0426" },
        .{ .code = .e0427_invalid_error_composition, .expected_str = "E0427" },
        .{ .code = .e0428_named_arg_for_positional_only, .expected_str = "E0428" },
        .{ .code = .e0429_positional_arg_for_keyword_only, .expected_str = "E0429" },
        .{ .code = .e0430_non_default_after_default_param, .expected_str = "E0430" },
        .{ .code = .e0431_invalid_format_specifier, .expected_str = "E0431" },
        .{ .code = .e0432_missing_struct_field_initializer, .expected_str = "E0432" },
        .{ .code = .e0433_inaccessible_field_or_visibility, .expected_str = "E0433" },
        .{ .code = .e0434_invalid_parallel_assign_target, .expected_str = "E0434" },
        .{ .code = .e0435_invalid_cfg_predicate, .expected_str = "E0435" },
        .{ .code = .e0436_builder_item_outside_scope, .expected_str = "E0436" },
        .{ .code = .e0437_invalid_labeled_match_continue, .expected_str = "E0437" },
    };
    try std.testing.expectEqual(@as(usize, 33), dr22_specs.len);

    var tag_identifiers: [dr22_specs.len][]const u8 = undefined;
    var has_src_reference: [dr22_specs.len]bool = @splat(false);
    var has_test_reference: [dr22_specs.len]bool = @splat(false);
    for (dr22_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "stage0/src",
        &tag_identifiers,
        &has_src_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/snapshots",
        &tag_identifiers,
        &has_test_reference,
    );
    for (0..dr22_specs.len) |i| {
        if (!has_src_reference[i]) {
            std.debug.print(
                "Phase 7.6 diagnostic `{s}` is not referenced in `stage0/src/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_src_reference[i]);
        if (!has_test_reference[i]) {
            std.debug.print(
                "Phase 7.6 diagnostic `{s}` is not referenced in `tests/unit/` or `tests/snapshots/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_test_reference[i]);
    }
}

test "test_drift_guard_phase8_cross_compile_ffi_async_seams_and_diagnostics" {
    // [1] Verify 9 alphabetical `router.CLI_SUBCOMMANDS` (`bench` through `upgrade`) & `TRANSLATE_C_FLAGS`:
    const expected_subcommands = [_][]const u8{
        "bench",
        "build",
        "check",
        "fmt",
        "lsp",
        "run",
        "test",
        "translate-c",
        "upgrade",
    };
    try std.testing.expectEqual(@as(usize, 9), router.CLI_SUBCOMMANDS.len);
    for (router.CLI_SUBCOMMANDS, 0..) |sub_desc, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(sub_desc.id)));
        try std.testing.expectEqualStrings(expected_subcommands[i], sub_desc.name);
        try std.testing.expect(sub_desc.summary.len > 0);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.CLI_SUBCOMMANDS[i - 1].name, sub_desc.name),
            );
        }
    }

    try std.testing.expectEqual(@as(usize, 5), router.TRANSLATE_C_FLAGS.len);
    var tc_help_buf: [2048]u8 = undefined;
    var tc_help_writer = std.Io.Writer.fixed(&tc_help_buf);
    try router.renderSubcommandHelp(&tc_help_writer, StyleConfig.MONOCHROME, .translate_c);
    const tc_help_text = tc_help_writer.buffered();
    for (router.TRANSLATE_C_FLAGS, 0..) |tc_flag, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(tc_flag.id)));
        try std.testing.expect(std.mem.indexOf(u8, tc_help_text, tc_flag.long_flag) != null);
        try std.testing.expect(std.mem.indexOf(u8, tc_help_text, tc_flag.summary) != null);
        if (tc_flag.short_flag) |short_s| {
            try std.testing.expect(std.mem.indexOf(u8, tc_help_text, short_s) != null);
        }
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.TRANSLATE_C_FLAGS[i - 1].long_flag, tc_flag.long_flag),
            );
        }
    }

    const required_phase8_attrs = [_][]const u8{
        "borrowed",
        "byte_len",
        "consumes",
        "escapes",
        "free_with",
        "link_lib",
        "may_be_null",
        "non_null",
        "not_send",
        "not_sync",
        "null_terminated",
        "out_param",
        "owned_by_caller",
        "slice_len",
        "thread_local",
        "trusted",
        "wasm_export",
        "wasm_import",
    };
    for (required_phase8_attrs) |attr_name| {
        try std.testing.expect(corex.type_system.BUILTIN_ATTRIBUTE_MAP.has(attr_name));
    }

    // [2] Verify 11 canonical `TargetSpec` entries (`@sizeOf == 4`) with 11 distinct `archOsTag()` values:
    try std.testing.expectEqual(@as(usize, 4), @sizeOf(corex.TargetSpec));
    try std.testing.expectEqual(@as(usize, 11), corex.TargetSpec.ALL_CANONICAL_TARGETS.len);
    for (corex.TargetSpec.ALL_CANONICAL_TARGETS, 0..) |lhs_spec, i| {
        try std.testing.expect(corex.TargetSpec.isValidTriple(lhs_spec.arch, lhs_spec.os, lhs_spec.abi));
        var j: usize = i + 1;
        while (j < corex.TargetSpec.ALL_CANONICAL_TARGETS.len) : (j += 1) {
            const rhs_spec = corex.TargetSpec.ALL_CANONICAL_TARGETS[j];
            try std.testing.expect(lhs_spec.archOsTag() != rhs_spec.archOsTag());
        }
    }

    // [3] Verify `stage0/src/sim_seam.zig` `< 250` LOC cap and binary-exact proactor & coroutine struct sizes:
    const sim_seam_bytes = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "stage0/src/sim_seam.zig",
        std.testing.allocator,
        .limited(1024 * 1024),
    );
    defer std.testing.allocator.free(sim_seam_bytes);
    var sim_line_count: usize = 1;
    for (sim_seam_bytes) |byte_val| {
        if (byte_val == '\n') sim_line_count += 1;
    }
    if (sim_seam_bytes.len > 0 and sim_seam_bytes[sim_seam_bytes.len - 1] == '\n') {
        sim_line_count -= 1;
    }
    try std.testing.expect(sim_line_count < 250);

    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.InFlightOpSlot));
    try std.testing.expectEqual(@as(usize, 64), @alignOf(corex.InFlightOpSlot));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.ReactorCqe));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.SuspendPointMeta));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.CoroFrameLayout));
    try std.testing.expectEqual(@as(usize, 8 * @sizeOf(usize)), @sizeOf(corex.sim_seam.ReactorVTable));

    const core_async_bytes = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "core/async.cx",
        std.testing.allocator,
        .limited(1024 * 1024),
    );
    defer std.testing.allocator.free(core_async_bytes);
    for ([_][]const u8{
        "pub monotonic_ns: usize,",
        "pub wall_epoch_ns: usize,",
        "pub fill_rng: usize,",
        "pub submit_io: usize,",
        "pub cancel_io: usize,",
        "pub poll_or_park: usize,",
        "pub yield_task: usize,",
        "pub buggify_gate: usize,",
    }) |vtable_field_decl| {
        try std.testing.expect(std.mem.indexOf(u8, core_async_bytes, vtable_field_decl) != null);
    }

    // [4] Verify all 8 Phase 8 `DiagnosticCode` tags (`E0009`, `E0308`–`E0312`, `E0317`, `E0438`)
    //     in `DIAGNOSTIC_CATALOG`, `stage0/src/`, and `tests/unit/`:
    const phase8_specs = [_]struct {
        /// Canonical Phase 8 `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0009_c_header_translation_failed, .expected_str = "E0009" },
        .{ .code = .e0308_unterminated_cstr_ffi, .expected_str = "E0308" },
        .{ .code = .e0309_concurrent_exclusivity_or_escape, .expected_str = "E0309" },
        .{ .code = .e0310_mismatched_ffi_deallocator, .expected_str = "E0310" },
        .{ .code = .e0311_unchecked_nullable_ffi_ptr, .expected_str = "E0311" },
        .{ .code = .e0312_unproven_ffi_slice_len, .expected_str = "E0312" },
        .{ .code = .e0317_async_inline_frame_exceeded, .expected_str = "E0317" },
        .{ .code = .e0438_await_outside_async_context, .expected_str = "E0438" },
    };
    try std.testing.expectEqual(@as(usize, 8), phase8_specs.len);

    var tag_identifiers: [phase8_specs.len][]const u8 = undefined;
    var has_src_reference: [phase8_specs.len]bool = @splat(false);
    var has_test_reference: [phase8_specs.len]bool = @splat(false);
    for (phase8_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "stage0/src",
        &tag_identifiers,
        &has_src_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    for (0..phase8_specs.len) |i| {
        if (!has_src_reference[i]) {
            std.debug.print(
                "Phase 8 diagnostic `{s}` is not referenced in `stage0/src/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_src_reference[i]);
        if (!has_test_reference[i]) {
            std.debug.print(
                "Phase 8 diagnostic `{s}` is not referenced in `tests/unit/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_test_reference[i]);
    }
}

test "test_drift_guard_phase9_pkg_seams_diagnostics_and_cli" {
    // [1] Verify `TokenKind` stays frozen at `121` (`0..120`) and `router.SUBCOMMANDS.len` stays frozen at `9`:
    try expectContiguousEnum(TokenKind);
    try std.testing.expectEqual(@as(usize, 121), std.enums.values(TokenKind).len);
    const frozen_subcommands = [_][]const u8{
        "bench",
        "build",
        "check",
        "fmt",
        "lsp",
        "run",
        "test",
        "translate-c",
        "upgrade",
    };
    try std.testing.expectEqual(@as(usize, 9), router.SUBCOMMANDS.len);
    for (router.SUBCOMMANDS, 0..) |sub_desc, i| {
        try std.testing.expectEqualStrings(frozen_subcommands[i], sub_desc.name);
    }
    try expectContiguousEnum(router.CompileFlagId);
    try std.testing.expectEqual(@as(usize, 25), router.COMPILE_FLAGS.len);
    try std.testing.expectEqual(
        std.math.Order.lt,
        std.mem.order(u8, "--offline", "--ofmt"),
    );
    var pkg_cli_sink = corex.DiagnosticSink.init(std.testing.allocator);
    defer pkg_cli_sink.deinit();
    const parsed_pkg_cli = try router.parseArgs(
        &.{
            "check",
            "-F",
            "tls,simd",
            "--no-default-features",
            "--frozen",
            "--locked",
            "--offline",
            "--verify-checksums",
            "--manifest-path=ws/corex.toml",
        },
        &pkg_cli_sink,
    );
    try std.testing.expect(!pkg_cli_sink.hasErrors());
    try std.testing.expect(parsed_pkg_cli.has_no_default_features);
    try std.testing.expect(parsed_pkg_cli.is_frozen);
    try std.testing.expect(parsed_pkg_cli.is_locked);
    try std.testing.expect(parsed_pkg_cli.is_offline);
    try std.testing.expect(parsed_pkg_cli.is_verifying_checksums);
    try std.testing.expectEqualStrings("ws/corex.toml", parsed_pkg_cli.manifest_path.?);
    try std.testing.expectEqual(@as(usize, 2), parsed_pkg_cli.features.len);

    var script_cli_sink = corex.DiagnosticSink.init(std.testing.allocator);
    defer script_cli_sink.deinit();
    const parsed_script_cli = try router.parseArgs(&.{"tool.cx"}, &script_cli_sink);
    try std.testing.expect(!script_cli_sink.hasErrors());
    try std.testing.expectEqual(router.SubcommandId.run, parsed_script_cli.action.execute_subcommand.subcommand);

    // [2] Verify `pkg_conflict_seam.zig` (`<= 35` non-comment/non-blank LOC) and exact binary seam layouts:
    const conflict_seam_loc = try countNonCommentNonBlankLines(
        std.testing.allocator,
        std.testing.io,
        "stage0/src/pkg_conflict_seam.zig",
    );
    try std.testing.expect(conflict_seam_loc <= 35);
    try expectContiguousEnum(corex.IncompatKind);
    try std.testing.expectEqual(@as(usize, 1), @sizeOf(corex.IncompatKind));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.IncompatTerm));
    try std.testing.expectEqual(@as(usize, 4), @alignOf(corex.IncompatTerm));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.IncompatNode));
    try std.testing.expectEqual(@as(usize, 4), @alignOf(corex.IncompatNode));
    try std.testing.expectEqual(@as(usize, 24), @sizeOf(corex.TomlSpanAnchor));
    try std.testing.expectEqual(@as(usize, 4), @alignOf(corex.TomlSpanAnchor));

    // [3] Verify `pkg_cxi_seam.zig` (`<= 35` non-comment/non-blank LOC) and exact `.cxi` binary record layouts:
    const cxi_seam_loc = try countNonCommentNonBlankLines(
        std.testing.allocator,
        std.testing.io,
        "stage0/src/pkg_cxi_seam.zig",
    );
    try std.testing.expect(cxi_seam_loc <= 35);
    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.CxiHeader));
    try std.testing.expectEqual(@as(usize, 8), @alignOf(corex.CxiHeader));
    try std.testing.expectEqual(@as(usize, 64), @sizeOf(corex.CxiFnRecord));
    try std.testing.expectEqual(@as(usize, 8), @alignOf(corex.CxiFnRecord));
    try std.testing.expectEqual(@as(usize, 40), @sizeOf(corex.CxiTypeRecord));
    try std.testing.expectEqual(@as(usize, 8), @alignOf(corex.CxiTypeRecord));

    // [4] Verify `TomlToken`, `TomlCstNode`, `CxTreeHeader`, `CxTreeEntry`, and `SeriesKey` layouts:
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(corex.pkg_manifest.TomlToken));
    try std.testing.expectEqual(@as(usize, 16), @sizeOf(corex.pkg_manifest.TomlCstNode));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(corex.vfs_sourcemap.CxTreeHeader));
    try std.testing.expectEqual(@as(usize, 8), @alignOf(corex.vfs_sourcemap.CxTreeHeader));
    try std.testing.expectEqual(@as(usize, 48), @sizeOf(corex.vfs_sourcemap.CxTreeEntry));
    try std.testing.expectEqual(@as(usize, 8), @alignOf(corex.vfs_sourcemap.CxTreeEntry));
    try std.testing.expectEqual(@as(usize, 12), @sizeOf(corex.SeriesKey));
    try std.testing.expectEqual(@as(usize, 4), @alignOf(corex.SeriesKey));

    // [5] Verify all 7 new Phase 9 `DiagnosticCode` tags (`E0010`–`E0016`) + reused `DR-17` codes (`E0324`–`E0327`,
    //     `E0435`, `W0330`) in `DIAGNOSTIC_CATALOG`, `stage0/src/`, and `tests/unit/`:
    try std.testing.expectEqual(@as(usize, 146), diagnostic.DIAGNOSTIC_CATALOG.len);
    try std.testing.expectEqual(
        DiagnosticCode.e0435_invalid_cfg_predicate,
        DiagnosticCode.e0435_unknown_cfg_feature,
    );
    const phase9_specs = [_]struct {
        /// Canonical Phase 9 or reused `DR-17`/`DR-22` `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0010_unsatisfiable_dependency_graph, .expected_str = "E0010" },
        .{ .code = .e0011_native_links_collision, .expected_str = "E0011" },
        .{ .code = .e0012_cross_major_cxi_type_mismatch, .expected_str = "E0012" },
        .{ .code = .e0013_invalid_manifest_or_pkg_name, .expected_str = "E0013" },
        .{ .code = .e0014_lockfile_drift_or_corrupt, .expected_str = "E0014" },
        .{ .code = .e0015_cache_integrity_mismatch, .expected_str = "E0015" },
        .{ .code = .e0016_offline_or_fetch_failed, .expected_str = "E0016" },
        .{ .code = .e0324_package_capability_violation, .expected_str = "E0324" },
        .{ .code = .e0325_comptime_sandbox_violation, .expected_str = "E0325" },
        .{ .code = .e0326_embed_path_escape, .expected_str = "E0326" },
        .{ .code = .e0327_forbidden_sandbox_bypass_attribute, .expected_str = "E0327" },
        .{ .code = .e0435_invalid_cfg_predicate, .expected_str = "E0435" },
        .{ .code = .w0330_ambient_dead_capability_in_dep, .expected_str = "W0330" },
    };
    try std.testing.expectEqual(@as(usize, 13), phase9_specs.len);

    var tag_identifiers: [phase9_specs.len][]const u8 = undefined;
    var has_src_reference: [phase9_specs.len]bool = @splat(false);
    var has_test_reference: [phase9_specs.len]bool = @splat(false);
    for (phase9_specs, 0..) |spec, i| {
        const entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, entry.code_str);
        try std.testing.expect(entry.title.len > 0);
        try std.testing.expect(entry.explanation.len > 0);
        tag_identifiers[i] = @tagName(spec.code);
    }

    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "stage0/src",
        &tag_identifiers,
        &has_src_reference,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &tag_identifiers,
        &has_test_reference,
    );
    for (0..phase9_specs.len) |i| {
        if (!has_src_reference[i]) {
            std.debug.print(
                "Phase 9 diagnostic `{s}` is not referenced in `stage0/src/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_src_reference[i]);
        if (!has_test_reference[i]) {
            std.debug.print(
                "Phase 9 diagnostic `{s}` is not referenced in `tests/unit/`\n",
                .{tag_identifiers[i]},
            );
        }
        try std.testing.expect(has_test_reference[i]);
    }
}

test "test_drift_guard_phase10_tooling_lsp_check_and_upgrade" {
    // [1] Verify `DIAGNOSTIC_CATALOG` (`146` contiguous entries) and `W0202` / `W0403` coverage:
    try expectContiguousEnum(DiagnosticCode);
    try std.testing.expectEqual(@as(usize, 146), diagnostic.DIAGNOSTIC_CATALOG.len);
    try std.testing.expectEqual(@as(usize, 146), std.enums.values(DiagnosticCode).len);

    const phase10_diag_specs = [_]struct {
        /// Canonical Phase 10 `DiagnosticCode` tag exercised by `check` and `upgrade`.
        code: DiagnosticCode,
        /// Expected 5-character CLI diagnostic code string.
        expected_str: []const u8,
    }{
        .{ .code = .w0202_non_idiomatic_construct, .expected_str = "W0202" },
        .{ .code = .w0403_deprecated_symbol, .expected_str = "W0403" },
    };
    var diag_tag_names: [phase10_diag_specs.len][]const u8 = undefined;
    var has_src_ref: [phase10_diag_specs.len]bool = @splat(false);
    var has_test_ref: [phase10_diag_specs.len]bool = @splat(false);
    for (phase10_diag_specs, 0..) |spec, i| {
        const cat_entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqual(spec.code, cat_entry.code);
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, cat_entry.code_str);
        try std.testing.expectEqual(corex.Severity.warning, cat_entry.default_severity);
        try std.testing.expect(cat_entry.title.len > 0);
        try std.testing.expect(cat_entry.explanation.len > 0);
        diag_tag_names[i] = @tagName(spec.code);
    }
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "stage0/src",
        &diag_tag_names,
        &has_src_ref,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &diag_tag_names,
        &has_test_ref,
    );
    for (0..phase10_diag_specs.len) |i| {
        try std.testing.expect(has_src_ref[i]);
        try std.testing.expect(has_test_ref[i]);
    }

    // [2] Verify frozen `SUBCOMMANDS` (`9`), `TokenKind` (`121`), and `COMPILE_FLAGS` (`25`):
    try expectContiguousEnum(router.SubcommandId);
    try std.testing.expectEqual(@as(usize, 9), router.SUBCOMMANDS.len);
    try expectContiguousEnum(TokenKind);
    try std.testing.expectEqual(@as(usize, 121), std.enums.values(TokenKind).len);
    try expectContiguousEnum(router.CompileFlagId);
    try std.testing.expectEqual(@as(usize, 25), router.COMPILE_FLAGS.len);

    // [3] Verify `CHECK_FLAGS` (`4` sorted entries), `UPGRADE_FLAGS` (`6`), and `LSP_FLAGS` (`2`) + `--help` parity:
    try expectContiguousEnum(router.CheckFlagId);
    const expected_check_flags = [_][]const u8{
        "--caps",
        "--deny-warnings",
        "--explain-caps",
        "--fix",
    };
    try std.testing.expectEqual(@as(usize, 4), router.CHECK_FLAGS.len);
    var sub_help_buf: [8192]u8 = undefined;
    var check_help_writer = std.Io.Writer.fixed(&sub_help_buf);
    try router.renderSubcommandHelp(&check_help_writer, StyleConfig.MONOCHROME, .check);
    const check_help_text = check_help_writer.buffered();
    for (router.CHECK_FLAGS, 0..) |chk_desc, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(chk_desc.id)));
        try std.testing.expectEqualStrings(expected_check_flags[i], chk_desc.long_flag);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.CHECK_FLAGS[i - 1].long_flag, chk_desc.long_flag),
            );
        }
        try std.testing.expect(std.mem.indexOf(u8, check_help_text, chk_desc.long_flag) != null);
        try std.testing.expect(std.mem.indexOf(u8, check_help_text, chk_desc.summary) != null);
    }

    try expectContiguousEnum(router.UpgradeFlagId);
    const expected_upgrade_flags = [_][]const u8{
        "--accept-caps",
        "--check",
        "--explain",
        "--internal-core",
        "--list",
        "--rule",
    };
    try std.testing.expectEqual(@as(usize, 6), router.UPGRADE_FLAGS.len);
    var upgrade_help_writer = std.Io.Writer.fixed(&sub_help_buf);
    try router.renderSubcommandHelp(&upgrade_help_writer, StyleConfig.MONOCHROME, .upgrade);
    const upgrade_help_text = upgrade_help_writer.buffered();
    for (router.UPGRADE_FLAGS, 0..) |upg_desc, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(upg_desc.id)));
        try std.testing.expectEqualStrings(expected_upgrade_flags[i], upg_desc.long_flag);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.UPGRADE_FLAGS[i - 1].long_flag, upg_desc.long_flag),
            );
        }
        try std.testing.expect(std.mem.indexOf(u8, upgrade_help_text, upg_desc.long_flag) != null);
        try std.testing.expect(std.mem.indexOf(u8, upgrade_help_text, upg_desc.summary) != null);
    }

    try expectContiguousEnum(router.LspFlagId);
    const expected_lsp_flags = [_][]const u8{
        "--internal-core",
        "--stdio",
    };
    try std.testing.expectEqual(@as(usize, 2), router.LSP_FLAGS.len);
    var lsp_help_writer = std.Io.Writer.fixed(&sub_help_buf);
    try router.renderSubcommandHelp(&lsp_help_writer, StyleConfig.MONOCHROME, .lsp);
    const lsp_help_text = lsp_help_writer.buffered();
    for (router.LSP_FLAGS, 0..) |lsp_desc, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(lsp_desc.id)));
        try std.testing.expectEqualStrings(expected_lsp_flags[i], lsp_desc.long_flag);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.LSP_FLAGS[i - 1].long_flag, lsp_desc.long_flag),
            );
        }
        try std.testing.expect(std.mem.indexOf(u8, lsp_help_text, lsp_desc.long_flag) != null);
        try std.testing.expect(std.mem.indexOf(u8, lsp_help_text, lsp_desc.summary) != null);
    }

    // [4] Verify `UPGRADE_RULE_CATALOG` (`29` contiguous rules `UR-21-00`–`UR-24-06`):
    try expectContiguousEnum(corex.UpgradeRuleId);
    try std.testing.expectEqual(@as(usize, 29), corex.UPGRADE_RULE_COUNT);
    try std.testing.expectEqual(@as(usize, 29), corex.UPGRADE_RULE_CATALOG.len);
    const expected_rule_codes = [_][]const u8{
        "UR-21-00",
        "UR-21-01",
        "UR-21-02",
        "UR-21-03",
        "UR-21-04",
        "UR-21-05",
        "UR-21-06",
        "UR-21-07",
        "UR-22-00",
        "UR-22-01",
        "UR-22-02",
        "UR-22-03",
        "UR-22-04",
        "UR-22-05",
        "UR-22-06",
        "UR-23-00",
        "UR-23-01",
        "UR-23-02",
        "UR-23-03",
        "UR-23-04",
        "UR-23-05",
        "UR-23-06",
        "UR-24-00",
        "UR-24-01",
        "UR-24-02",
        "UR-24-03",
        "UR-24-04",
        "UR-24-05",
        "UR-24-06",
    };
    for (corex.UPGRADE_RULE_CATALOG, 0..) |rule_desc, i| {
        try std.testing.expectEqual(i, @as(usize, rule_desc.id.asInt()));
        try std.testing.expectEqualStrings(expected_rule_codes[i], rule_desc.rule_code);
        try std.testing.expectEqual(rule_desc.id, corex.lookupUpgradeRule(rule_desc.rule_code).?);
        try std.testing.expect(rule_desc.summary.len > 0);
    }

    // [5] Verify bounded VFS overlay and LSP untrusted-input resource caps (`AGENTS.md` §2):
    try std.testing.expectEqual(@as(usize, 256), corex.MAX_OPEN_OVERLAYS);
    try std.testing.expectEqual(@as(usize, 64 * 1024 * 1024), corex.MAX_OPEN_OVERLAY_BYTES);
    try std.testing.expectEqual(@as(usize, 8 * 1024), corex.lsp_server.MAX_LSP_HEADER_BYTES);
    try std.testing.expectEqual(@as(usize, 16 * 1024 * 1024), corex.lsp_server.MAX_LSP_CONTENT_LENGTH);
    try std.testing.expectEqual(@as(usize, 64), corex.lsp_server.MAX_LSP_JSON_DEPTH);
    try std.testing.expectEqual(@as(usize, 4096), corex.lsp_server.MAX_LSP_URI_BYTES);
    try std.testing.expectEqual(@as(usize, 512), corex.lsp_server.MAX_CLIENT_URI_MAP_ENTRIES);
    try std.testing.expectEqual(@as(usize, 1024 * 1024), corex.lsp_server.MAX_CLIENT_URI_MAP_BYTES);
    try std.testing.expectEqual(@as(usize, 64), corex.lsp_server.MAX_SEMANTIC_TOKEN_CACHE_ENTRIES);
    try std.testing.expectEqual(@as(usize, 8 * 1024 * 1024), corex.lsp_server.MAX_SEMANTIC_TOKEN_CACHE_BYTES);
}

test "test_drift_guard_phase106_dr23_diagnostics_tokens_and_upgrade_rules" {
    // [1] Verify `TokenKind` is locked at `121` variants (`7` spare bits in `TokenSet128`, `DR-23` §2.1 & `DR-24` §2.1):
    try expectContiguousEnum(TokenKind);
    const token_count = std.enums.values(TokenKind).len;
    try std.testing.expectEqual(@as(usize, 121), token_count);
    try std.testing.expectEqual(@as(usize, 7), 128 - token_count);
    try std.testing.expect(!@hasField(TokenKind, "kw_elif"));
    try std.testing.expect(!@hasField(TokenKind, "kw_elsif"));
    try std.testing.expect(!@hasField(TokenKind, "kw_elseif"));

    // [2] Verify all 10 `DR-23` `DiagnosticCode` tags (`146` total catalog entries) and `.err` severity:
    try expectContiguousEnum(DiagnosticCode);
    try std.testing.expectEqual(@as(usize, 146), diagnostic.DIAGNOSTIC_CATALOG.len);
    const dr23_diag_specs = [_]struct {
        /// Canonical Phase 10.6 `DR-23` `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI diagnostic code string.
        expected_str: []const u8,
    }{
        .{ .code = .e0118_block_doc_comment_forbidden, .expected_str = "E0118" },
        .{ .code = .e0229_misplaced_module_doc_comment, .expected_str = "E0229" },
        .{ .code = .e0230_unattached_doc_comment, .expected_str = "E0230" },
        .{ .code = .e0231_visibility_on_impl_block, .expected_str = "E0231" },
        .{ .code = .e0232_inline_method_in_type_decl, .expected_str = "E0232" },
        .{ .code = .e0233_invalid_elif_keyword, .expected_str = "E0233" },
        .{ .code = .e0234_non_binding_wildcard_let_var, .expected_str = "E0234" },
        .{ .code = .e0235_all_wildcard_destructuring_assign, .expected_str = "E0235" },
        .{ .code = .e0236_missing_colon_before_type, .expected_str = "E0236" },
        .{ .code = .e0439_pointless_unit_or_used_discard, .expected_str = "E0439" },
    };
    try std.testing.expectEqual(@as(usize, 10), dr23_diag_specs.len);

    var diag_tag_names: [dr23_diag_specs.len][]const u8 = undefined;
    var has_src_ref: [dr23_diag_specs.len]bool = @splat(false);
    var has_test_ref: [dr23_diag_specs.len]bool = @splat(false);
    for (dr23_diag_specs, 0..) |spec, i| {
        const cat_entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqual(spec.code, cat_entry.code);
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, cat_entry.code_str);
        try std.testing.expectEqual(corex.Severity.err, cat_entry.default_severity);
        try std.testing.expect(cat_entry.title.len > 0);
        try std.testing.expect(cat_entry.explanation.len > 0);
        diag_tag_names[i] = @tagName(spec.code);
    }
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "stage0/src",
        &diag_tag_names,
        &has_src_ref,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &diag_tag_names,
        &has_test_ref,
    );
    for (0..dr23_diag_specs.len) |i| {
        if (!has_src_ref[i]) {
            std.debug.print(
                "Phase 10.6 diagnostic `{s}` is not referenced in `stage0/src/`\n",
                .{diag_tag_names[i]},
            );
        }
        try std.testing.expect(has_src_ref[i]);
        if (!has_test_ref[i]) {
            std.debug.print(
                "Phase 10.6 diagnostic `{s}` is not referenced in `tests/unit/`\n",
                .{diag_tag_names[i]},
            );
        }
        try std.testing.expect(has_test_ref[i]);
    }

    // [3] Verify all 7 `DR-23` `UpgradeRuleId` entries (`UR-23-00`–`UR-23-06`) under `.dr23_phase106`:
    try expectContiguousEnum(corex.UpgradeRuleId);
    try std.testing.expectEqual(@as(usize, 29), corex.UPGRADE_RULE_COUNT);
    const dr23_rule_specs = [_]struct {
        /// Canonical `DR-23` `UpgradeRuleId` tag (`15..21`).
        id: corex.UpgradeRuleId,
        /// Expected `"UR-23-XX"` rule code string.
        rule_code: []const u8,
    }{
        .{ .id = .ur_23_00_block_doc_comments_to_line_docs, .rule_code = "UR-23-00" },
        .{ .id = .ur_23_01_doc_comment_placement_and_attachment, .rule_code = "UR-23-01" },
        .{ .id = .ur_23_02_elif_to_else_if, .rule_code = "UR-23-02" },
        .{ .id = .ur_23_03_impl_visibility_and_inline_type_methods, .rule_code = "UR-23-03" },
        .{ .id = .ur_23_04_canonical_wildcard_discard_stmt, .rule_code = "UR-23-04" },
        .{ .id = .ur_23_05_foreign_scalar_type_names, .rule_code = "UR-23-05" },
        .{ .id = .ur_23_06_missing_colon_before_type, .rule_code = "UR-23-06" },
    };
    for (dr23_rule_specs) |rule_spec| {
        const desc = corex.UPGRADE_RULE_CATALOG[rule_spec.id.asInt()];
        try std.testing.expectEqual(rule_spec.id, desc.id);
        try std.testing.expectEqualStrings(rule_spec.rule_code, desc.rule_code);
        try std.testing.expectEqual(corex.upgrade_rules.UpgradeWave.dr23_phase106, desc.wave);
        try std.testing.expectEqual(rule_spec.id, corex.lookupUpgradeRule(rule_spec.rule_code).?);
        try std.testing.expect(desc.summary.len > 0);
    }

    // [4] Verify `ADR-23D` O(1) foreign-scalar suggestion lookup tables (`DR-23` §2.1 & §3.1):
    const foreign_scalar_pairs = [_]struct {
        /// Foreign-language scalar spelling rejected as a built-in primitive.
        foreign_name: []const u8,
        /// Canonical CoreX lowercase `PRIM_TYPE` replacement.
        canonical_prim: []const u8,
    }{
        .{ .foreign_name = "U32", .canonical_prim = "u32" },
        .{ .foreign_name = "UInt32", .canonical_prim = "u32" },
        .{ .foreign_name = "Bool", .canonical_prim = "bool" },
        .{ .foreign_name = "Float64", .canonical_prim = "f64" },
        .{ .foreign_name = "USize", .canonical_prim = "usize" },
        .{ .foreign_name = "Void", .canonical_prim = "unit" },
        .{ .foreign_name = "Opaque", .canonical_prim = "opaque" },
    };
    for (foreign_scalar_pairs) |pair| {
        try std.testing.expectEqualStrings(
            pair.canonical_prim,
            corex.symbol_resolver.lookupUnambiguousForeignScalar(pair.foreign_name).?,
        );
        try std.testing.expectEqualStrings(
            pair.canonical_prim,
            corex.symbol_resolver.lookupForeignScalarHint(pair.foreign_name).?,
        );
    }
    try std.testing.expect(corex.symbol_resolver.lookupUnambiguousForeignScalar("PacketHeader") == null);
}

test "test_drift_guard_phase111b_dr24_diagnostics_tokens_and_upgrade_rules" {
    // [1] Verify `TokenKind.fmt_string_lit == 60` (`121` variants `< 128`), `TriviaKind` (`9` variants, `0` block comments),
    //     and `AstTag.fmt_string_lit`:
    try expectContiguousEnum(TokenKind);
    try std.testing.expectEqual(@as(usize, 121), std.enums.values(TokenKind).len);
    try std.testing.expectEqual(@as(u8, 60), @backingInt(TokenKind.fmt_string_lit));
    try std.testing.expectEqual(@as(u8, 120), @backingInt(TokenKind.eof));
    try std.testing.expect(!@hasField(TokenKind, "kw_then"));

    try expectContiguousEnum(corex.syntax_arenas.TriviaKind);
    try std.testing.expectEqual(@as(usize, 9), std.enums.values(corex.syntax_arenas.TriviaKind).len);
    try std.testing.expect(!@hasField(corex.syntax_arenas.TriviaKind, "block_comment"));
    try std.testing.expect(@hasField(AstTag, "fmt_string_lit"));

    // [2] Verify all 8 new `DR-24` `DiagnosticCode` tags (`146` total catalog entries) and `stage0/src` + `tests/unit` coverage:
    try expectContiguousEnum(DiagnosticCode);
    try std.testing.expectEqual(@as(usize, 146), diagnostic.DIAGNOSTIC_CATALOG.len);
    const dr24_diag_specs = [_]struct {
        /// Canonical Phase 11.1b `DR-24` `DiagnosticCode` tag.
        code: DiagnosticCode,
        /// Expected 5-character CLI diagnostic code string.
        expected_str: []const u8,
        /// Expected default diagnostic severity.
        expected_sev: corex.Severity,
    }{
        .{ .code = .e0237_inline_if_missing_else, .expected_str = "E0237", .expected_sev = .err },
        .{ .code = .e0238_mixed_if_arrow_and_block, .expected_str = "E0238", .expected_sev = .err },
        .{ .code = .e0239_retired_layout_or_link_attribute, .expected_str = "E0239", .expected_sev = .err },
        .{ .code = .e0440_invalid_repr_or_inline_attribute, .expected_str = "E0440", .expected_sev = .err },
        .{ .code = .e0441_unaligned_packed_field_borrow, .expected_str = "E0441", .expected_sev = .err },
        .{ .code = .w0119_useless_format_string, .expected_str = "W0119", .expected_sev = .warning },
        .{ .code = .w0120_uninterpolated_fmt_placeholder, .expected_str = "W0120", .expected_sev = .warning },
        .{ .code = .w0333_redundant_private_contract, .expected_str = "W0333", .expected_sev = .warning },
    };

    var diag_tag_names: [dr24_diag_specs.len][]const u8 = undefined;
    var has_src_ref: [dr24_diag_specs.len]bool = @splat(false);
    var has_test_ref: [dr24_diag_specs.len]bool = @splat(false);
    for (dr24_diag_specs, 0..) |spec, i| {
        const cat_entry = diagnostic.DIAGNOSTIC_CATALOG[@backingInt(spec.code)];
        try std.testing.expectEqual(spec.code, cat_entry.code);
        try std.testing.expectEqualStrings(spec.expected_str, spec.code.asCodeStr());
        try std.testing.expectEqualStrings(spec.expected_str, cat_entry.code_str);
        try std.testing.expectEqual(spec.expected_sev, cat_entry.default_severity);
        try std.testing.expect(cat_entry.title.len > 0);
        try std.testing.expect(cat_entry.explanation.len > 0);
        diag_tag_names[i] = @tagName(spec.code);
    }
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "stage0/src",
        &diag_tag_names,
        &has_src_ref,
    );
    try markReferencedIdentifiersInDir(
        std.testing.allocator,
        std.testing.io,
        "tests/unit",
        &diag_tag_names,
        &has_test_ref,
    );
    for (0..dr24_diag_specs.len) |i| {
        if (!has_src_ref[i]) {
            std.debug.print(
                "Phase 11.1b diagnostic `{s}` is not referenced in `stage0/src/`\n",
                .{diag_tag_names[i]},
            );
        }
        try std.testing.expect(has_src_ref[i]);
        if (!has_test_ref[i]) {
            std.debug.print(
                "Phase 11.1b diagnostic `{s}` is not referenced in `tests/unit/`\n",
                .{diag_tag_names[i]},
            );
        }
        try std.testing.expect(has_test_ref[i]);
    }

    // [3] Verify all 7 `DR-24` `UpgradeRuleId` entries (`UR-24-00`–`UR-24-06`, indices `22..28`) under `.dr24_phase111b`:
    try expectContiguousEnum(corex.UpgradeRuleId);
    try std.testing.expectEqual(@as(usize, 29), corex.UPGRADE_RULE_COUNT);
    const dr24_rule_codes = [_][]const u8{
        "UR-24-00",
        "UR-24-01",
        "UR-24-02",
        "UR-24-03",
        "UR-24-04",
        "UR-24-05",
        "UR-24-06",
    };
    for (dr24_rule_codes, 0..) |expected_code, offset| {
        const rule_idx = 22 + offset;
        const desc = corex.UPGRADE_RULE_CATALOG[rule_idx];
        try std.testing.expectEqual(@as(usize, rule_idx), @as(usize, desc.id.asInt()));
        try std.testing.expectEqualStrings(expected_code, desc.rule_code);
        try std.testing.expectEqual(corex.upgrade_rules.UpgradeWave.dr24_phase111b, desc.wave);
        try std.testing.expectEqual(desc.id, corex.lookupUpgradeRule(expected_code).?);
        try std.testing.expect(desc.summary.len > 0);
    }
}

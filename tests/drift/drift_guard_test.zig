//! Repository-Wide Drift Guards (`tests/drift/drift_guard_test.zig`)
//!
//! Enforces zero colored emojis across the entire repository, 100% parity between `router.zig`
//! tables and `corex --help`, `DIAGNOSTIC_CATALOG` subsystem prefix integrity, Phase 1–5 IR/VM/opt
//! struct layouts, enum contiguity, and diagnostic test coverage, plus `< 150` column line length
//! and 90-character top-level section dividers across all `.zig` source files.
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

/// Asserts that `EnumType` has strictly contiguous integer backing tags `0 .. N - 1`.
fn expectContiguousEnum(comptime EnumType: type) !void {
    const enum_info = @typeInfo(EnumType).@"enum";
    const TagInt = enum_info.tag_type;
    const enum_values = std.enums.values(EnumType);
    try std.testing.expectEqual(enum_info.field_names.len, enum_values.len);
    inline for (enum_values, 0..) |enum_val, i| {
        const expected_tag: TagInt = @intCast(i);
        try std.testing.expectEqual(expected_tag, @backingInt(enum_val));
        try std.testing.expectEqual(enum_val, @as(EnumType, @enumFromInt(expected_tag)));
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

    var has_seen_keyword: [45]bool = @splat(false);
    var prim_count: usize = 0;
    for (values) |kind_val| {
        const backing = @backingInt(kind_val);
        if (backing < 45) {
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

    // [2] Verify 11 Constrained Type Groups in `TypeGroupMask` (`32..42`):
    var grp_slot: u32 = 32;
    while (grp_slot <= 42) : (grp_slot += 1) {
        const grp_id = corex.TypeId.fromInt(grp_slot);
        try std.testing.expect(grp_id.isBuiltinGroup());
        try std.testing.expect(corex.TypeGroupMask.forBuiltinGroup(grp_id) != 0);
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
    try std.testing.expectEqual(@as(usize, 3), router.COMPILE_FLAGS.len);
    try std.testing.expectEqualStrings("--comptime-limit", router.COMPILE_FLAGS[0].long_flag);
    try std.testing.expectEqualStrings("--dev", router.COMPILE_FLAGS[1].long_flag);
    try std.testing.expectEqualStrings("--release", router.COMPILE_FLAGS[2].long_flag);
    for (router.COMPILE_FLAGS, 0..) |comp_flag, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(comp_flag.id)));
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
        var sub_help_buf: [8192]u8 = undefined;
        var sub_help_writer = std.Io.Writer.fixed(&sub_help_buf);
        try router.renderSubcommandHelp(&sub_help_writer, StyleConfig.MONOCHROME, sub_id);
        const sub_help_out = sub_help_writer.buffered();
        for (router.COMPILE_FLAGS) |comp_flag| {
            try std.testing.expect(std.mem.indexOf(u8, sub_help_out, comp_flag.long_flag) != null);
            try std.testing.expect(std.mem.indexOf(u8, sub_help_out, comp_flag.summary) != null);
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

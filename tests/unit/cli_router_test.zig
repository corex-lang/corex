//! Unit Tests for CLI Style, Box Drawing & Command Router (`tests/unit/cli_router_test.zig`)
//!
//! Verifies `ColorMode`, `Glyphs`, `measureVisibleWidth`, `CardRenderer`, `TableRenderer`,
//! `renderProgressBar`, `computeLevenshteinDistance`, `parseArgs`, and `runCli`.
//!
//! Ensures all CLI surfaces remain strictly monochrome Unicode + ANSI with zero colored emojis.

const std = @import("std");
const corex = @import("corex");

const style = corex.style;
const box_draw = corex.box_draw;
const router = corex.router;
const ColorMode = corex.ColorMode;
const Glyphs = corex.Glyphs;
const StyleConfig = corex.StyleConfig;
const DiagnosticSink = corex.DiagnosticSink;

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------- Style & Box-Drawing Tests ------------------

test "test_color_mode_parsing_and_visible_width_calculation" {
    try std.testing.expectEqual(ColorMode.auto, ColorMode.parse("auto").?);
    try std.testing.expectEqual(ColorMode.always, ColorMode.parse("always").?);
    try std.testing.expectEqual(ColorMode.never, ColorMode.parse("never").?);
    try std.testing.expect(ColorMode.parse("invalid") == null);

    try std.testing.expectEqualStrings("auto", ColorMode.auto.asStr());
    try std.testing.expectEqualStrings("always", ColorMode.always.asStr());
    try std.testing.expectEqualStrings("never", ColorMode.never.asStr());

    var header_buf: [256]u8 = undefined;
    var header_writer = std.Io.Writer.fixed(&header_buf);
    try StyleConfig.COLORED.writeStatusHeader(&header_writer, .success, Glyphs.SUCCESS, "check", "verified");
    try std.testing.expectEqual(@as(usize, 17), style.measureVisibleWidth(header_writer.buffered()));
}

test "test_box_draw_card_table_and_progress_bar_rendering" {
    // [1] Untitled card rendering:
    var card_buf: [512]u8 = undefined;
    var card_writer = std.Io.Writer.fixed(&card_buf);
    try box_draw.CardRenderer.init(StyleConfig.MONOCHROME).renderCard(
        &card_writer,
        "",
        &.{ "first line", "second line" },
    );
    try std.testing.expect(std.mem.indexOf(u8, card_writer.buffered(), "╭─────────────╮") != null);
    try std.testing.expect(std.mem.indexOf(u8, card_writer.buffered(), "╰─────────────╯") != null);

    // [2] 1/8th-block progress bar at 0%, 50%, 62.5%, and 100%:
    var bar_buf: [128]u8 = undefined;
    var bar_writer = std.Io.Writer.fixed(&bar_buf);
    try box_draw.renderProgressBar(StyleConfig.MONOCHROME, &bar_writer, 4, 0.0);
    try std.testing.expectEqualStrings("    ", bar_writer.buffered());

    bar_writer = std.Io.Writer.fixed(&bar_buf);
    try box_draw.renderProgressBar(StyleConfig.MONOCHROME, &bar_writer, 4, 0.625);
    try std.testing.expectEqualStrings("██▌ ", bar_writer.buffered());

    bar_writer = std.Io.Writer.fixed(&bar_buf);
    try box_draw.renderProgressBar(StyleConfig.MONOCHROME, &bar_writer, 4, 1.5);
    try std.testing.expectEqualStrings("████", bar_writer.buffered());
}

// ----------------- Levenshtein & Router Tests -----------------

test "test_levenshtein_distance_and_cli_arg_parsing_matrix" {
    try std.testing.expectEqual(@as(usize, 0), router.computeLevenshteinDistance("upgrade", "upgrade"));
    try std.testing.expectEqual(@as(usize, 1), router.computeLevenshteinDistance("upgrad", "upgrade"));
    try std.testing.expectEqual(@as(usize, 2), router.computeLevenshteinDistance("upgarde", "upgrade"));
    try std.testing.expectEqual(@as(usize, 5), router.computeLevenshteinDistance("", "build"));
    try std.testing.expectEqual(
        std.math.maxInt(usize),
        router.computeLevenshteinDistance(&@as([64]u8, @splat('a')), "build"),
    );

    try std.testing.expect(router.suggestSubcommand("completely_unrelated_token") == null);
    try std.testing.expect(router.suggestGlobalFlag("--completely-unrelated-flag") == null);

    // [1] Empty arguments default to `.show_help`:
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        const parsed = try router.parseArgs(&.{}, &sink);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expectEqual(@as(?router.SubcommandId, null), parsed.action.show_help);
    }

    // [2] Subcommand with `--` pass-through arguments and `--color always`:
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        const parsed = try router.parseArgs(&.{ "--color", "always", "run", "app.cx", "--", "--flag-for-app" }, &sink);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expectEqual(ColorMode.always, parsed.color_mode);
        try std.testing.expectEqual(router.SubcommandId.run, parsed.action.execute_subcommand.subcommand);
        try std.testing.expectEqual(@as(usize, 2), parsed.action.execute_subcommand.positional_args.len);
        try std.testing.expectEqualStrings("--flag-for-app", parsed.action.execute_subcommand.positional_args[1]);
    }

    // [3] Missing value for `--color` emits `E0003`:
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        try std.testing.expectEqual(
            router.CommandAction.invalid,
            (try router.parseArgs(&.{"--color"}, &sink)).action,
        );
        try std.testing.expect(sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0003_missing_cli_argument, sink.asSlice()[0].code);
    }

    // [4] Invalid value for `--color=bad` emits `E0001`:
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        _ = try router.parseArgs(&.{"--color=bad"}, &sink);
        try std.testing.expect(sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0001_unknown_cli_flag, sink.asSlice()[0].code);
    }
}

test "test_run_cli_lifecycle_version_check_and_missing_file_error" {
    var out_buf: [4096]u8 = undefined;
    var err_buf: [4096]u8 = undefined;

    // [1] `corex --version`:
    var out_writer = std.Io.Writer.fixed(&out_buf);
    var err_writer = std.Io.Writer.fixed(&err_buf);
    const ver_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{"--version"},
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), ver_exit);
    try std.testing.expectEqualStrings("corex 0.1.0-dev (stage0 zig 0.17.0)\n", out_writer.buffered());

    // [2] `corex --color=never check build.zig`:
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const check_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "check", "build.zig" },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), check_exit);
    try std.testing.expectEqualStrings("✓ check: Phase 0 bootstrap foundation verified\n", out_writer.buffered());

    // [3] `corex --color=never check missing_file_xyz.cx` -> returns exit code `1` with `E0004`:
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const missing_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "check", "missing_file_xyz.cx" },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 1), missing_exit);
    try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "error[E0004]") != null);
}

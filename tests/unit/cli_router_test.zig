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

    // [5] Compilation flags (`--comptime-limit`, `--dev`, `--release`) on `build`/`run`/`check`/`test`:
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        const parsed_rel = try router.parseArgs(
            &.{ "build", "--release", "--comptime-limit=50000", "main.cx" },
            &sink,
        );
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(parsed_rel.is_release_mode);
        try std.testing.expectEqual(@as(u64, 50_000), parsed_rel.comptime_step_limit);
        try std.testing.expect(parsed_rel.action.execute_subcommand.is_release_mode);
        try std.testing.expectEqual(@as(u64, 50_000), parsed_rel.action.execute_subcommand.comptime_step_limit);

        const parsed_dev = try router.parseArgs(
            &.{ "check", "--dev", "--internal-core", "--comptime-limit", "1234" },
            &sink,
        );
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(!parsed_dev.is_release_mode);
        try std.testing.expect(parsed_dev.is_internal_core);
        try std.testing.expect(parsed_dev.action.execute_subcommand.is_internal_core);
        try std.testing.expectEqual(@as(u64, 1_234), parsed_dev.comptime_step_limit);

        try std.testing.expectEqualStrings("--release", router.suggestFlagForSubcommand("--relase", .build).?);
        try std.testing.expectEqualStrings(
            "--comptime-limit",
            router.suggestFlagForSubcommand("--comptime-limt", .check).?,
        );
    }

    // [6] Conflicting `--dev` + `--release`, missing `--comptime-limit` value, and zero/non-numeric rejection:
    {
        var conflict_sink = DiagnosticSink.init(std.testing.allocator);
        defer conflict_sink.deinit();
        _ = try router.parseArgs(&.{ "build", "--dev", "--release" }, &conflict_sink);
        try std.testing.expect(conflict_sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0001_unknown_cli_flag, conflict_sink.asSlice()[0].code);

        var missing_sink = DiagnosticSink.init(std.testing.allocator);
        defer missing_sink.deinit();
        _ = try router.parseArgs(&.{ "test", "--comptime-limit" }, &missing_sink);
        try std.testing.expect(missing_sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0003_missing_cli_argument, missing_sink.asSlice()[0].code);

        var zero_sink = DiagnosticSink.init(std.testing.allocator);
        defer zero_sink.deinit();
        _ = try router.parseArgs(&.{ "run", "--comptime-limit=0" }, &zero_sink);
        try std.testing.expect(zero_sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0001_unknown_cli_flag, zero_sink.asSlice()[0].code);

        var help_buf: [8192]u8 = undefined;
        var help_writer = std.Io.Writer.fixed(&help_buf);
        try router.renderSubcommandHelp(&help_writer, StyleConfig.MONOCHROME, .build);
        try std.testing.expect(std.mem.indexOf(u8, help_writer.buffered(), "--comptime-limit=<steps>") != null);
        try std.testing.expect(std.mem.indexOf(u8, help_writer.buffered(), "--dev") != null);
        try std.testing.expect(std.mem.indexOf(u8, help_writer.buffered(), "--release") != null);
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

    // [2] `corex --color=never check <valid.cx>` verifies real `.cx` source; `build.zig` is rejected with `E0001`:
    const valid_cx_path = ".zig-cache/test_cli_router_lifecycle_check.cx";
    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = valid_cx_path,
        .data = "pub fn add_pair(lhs: i32, rhs: i32) -> i32 {\n    return lhs + rhs;\n}\n",
    });
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, valid_cx_path) catch {};

    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const check_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "check", valid_cx_path },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), check_exit);
    try std.testing.expectEqualStrings(
        "✓ check: test_cli_router_lifecycle_check\n",
        out_writer.buffered(),
    );

    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const non_cx_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "check", "build.zig" },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 1), non_cx_exit);
    try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "error[E0001]") != null);

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

test "test_cli_router_internal_core_flag_on_fmt_and_upgrade" {
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    const parsed_fmt = try router.parseArgs(
        &.{ "fmt", "--internal-core", "core/primitives.cx" },
        &sink,
    );
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(parsed_fmt.is_internal_core);
    try std.testing.expectEqual(router.SubcommandId.fmt, parsed_fmt.action.execute_subcommand.subcommand);
    try std.testing.expect(parsed_fmt.action.execute_subcommand.is_internal_core);

    const parsed_upg = try router.parseArgs(
        &.{ "upgrade", "--internal-core", "core/primitives.cx" },
        &sink,
    );
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(parsed_upg.is_internal_core);
    try std.testing.expectEqual(router.SubcommandId.upgrade, parsed_upg.action.execute_subcommand.subcommand);
    try std.testing.expect(parsed_upg.action.execute_subcommand.is_internal_core);

    try std.testing.expectEqualStrings(
        "--internal-core",
        router.suggestFlagForSubcommand("--internal-cor", .fmt).?,
    );
    try std.testing.expectEqualStrings(
        "--internal-core",
        router.suggestFlagForSubcommand("--internal-cor", .upgrade).?,
    );

    const scratch_cx_path = ".zig-cache/test_cli_router_internal_core.cx";
    {
        const scratch_file = try std.Io.Dir.cwd().createFile(std.testing.io, scratch_cx_path, .{});
        defer scratch_file.close(std.testing.io);
        try scratch_file.writePositionalAll(
            std.testing.io,
            "pub fn identity_byte(val: u8) -> u8 {\n    return val;\n}\n",
            0,
        );
    }
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, scratch_cx_path) catch {};

    var out_buf: [4096]u8 = undefined;
    var err_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    var err_writer = std.Io.Writer.fixed(&err_buf);
    const upg_exit = try router.runCli(
        std.testing.allocator,
        std.testing.io,
        null,
        &.{ "--color=never", "upgrade", "--internal-core", scratch_cx_path },
        &out_writer,
        &err_writer,
    );
    try std.testing.expectEqual(@as(u8, 0), upg_exit);

    var fmt_help_buf: [4096]u8 = undefined;
    var fmt_help_writer = std.Io.Writer.fixed(&fmt_help_buf);
    try router.renderSubcommandHelp(&fmt_help_writer, StyleConfig.MONOCHROME, .fmt);
    try std.testing.expect(std.mem.indexOf(u8, fmt_help_writer.buffered(), "--internal-core") != null);

    var upg_help_buf: [4096]u8 = undefined;
    var upg_help_writer = std.Io.Writer.fixed(&upg_help_buf);
    try router.renderSubcommandHelp(&upg_help_writer, StyleConfig.MONOCHROME, .upgrade);
    try std.testing.expect(std.mem.indexOf(u8, upg_help_writer.buffered(), "Upgrade Options:") != null);
    try std.testing.expect(std.mem.indexOf(u8, upg_help_writer.buffered(), "--internal-core") != null);
}

// ---------------- Translate-C & Cross-Compile -----------------

test "test_cli_alphabetical_subcommands_help_snapshot_and_cross_compile_flags" {
    // [1] Verify 9 alphabetical `CLI_SUBCOMMANDS` / `SUBCOMMANDS` (`0..8`) and $O(1)$ `fromName` lookup:
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
    try std.testing.expectEqual(expected_subcommands.len, router.CLI_SUBCOMMANDS.len);
    try std.testing.expectEqual(expected_subcommands.len, router.SUBCOMMANDS.len);
    for (router.CLI_SUBCOMMANDS, 0..) |sub_desc, i| {
        try std.testing.expectEqual(i, @as(usize, @backingInt(sub_desc.id)));
        try std.testing.expectEqualStrings(expected_subcommands[i], sub_desc.name);
        try std.testing.expectEqual(sub_desc.id, router.SubcommandId.fromName(sub_desc.name).?);
        if (i > 0) {
            try std.testing.expectEqual(
                std.math.Order.lt,
                std.mem.order(u8, router.CLI_SUBCOMMANDS[i - 1].name, sub_desc.name),
            );
        }
    }
    try std.testing.expectEqual(router.SubcommandId.@"test", router.SubcommandId.test_cmd);
    try std.testing.expect(router.SubcommandId.fromName("unknown-cmd") == null);

    // [2] Verify byte-for-byte parity between `renderHelp` and `tests/snapshots/cli_help.snap`:
    {
        var global_help_buf: [4096]u8 = undefined;
        var global_help_writer = std.Io.Writer.fixed(&global_help_buf);
        try router.renderHelp(&global_help_writer, StyleConfig.MONOCHROME);

        const raw_snap = try std.Io.Dir.cwd().readFileAlloc(
            std.testing.io,
            "tests/snapshots/cli_help.snap",
            std.testing.allocator,
            .limited(64 * 1024),
        );
        defer std.testing.allocator.free(raw_snap);

        var norm_snap: std.ArrayListUnmanaged(u8) = .empty;
        defer norm_snap.deinit(std.testing.allocator);
        for (raw_snap) |byte_val| {
            if (byte_val != '\r') try norm_snap.append(std.testing.allocator, byte_val);
        }
        try std.testing.expectEqualStrings(norm_snap.items, global_help_writer.buffered());
    }

    // [3] Verify `COMPILE_FLAGS` (`--link`, `--emit-obj`, `-l`/`--lib`, `-L`/`--lib-dir`, `-I`, `-D`):
    {
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        const parsed_build = try router.parseArgs(
            &.{
                "build",
                "--link=static",
                "--emit-obj",
                "-DFEAT_FAST=1",
                "--define",
                "NDEBUG",
                "-Iinclude",
                "-I",
                "vendor/inc",
                "-lsqlite3",
                "-l",
                "m",
                "--lib=user32.def",
                "-L/usr/local/lib",
                "-L",
                "vendor/lib",
                "--lib-dir=build/deps",
                "-o",
                "build/app.o",
                "--target=x86_64-linux-musl",
                "src/main.cx",
            },
            &sink,
        );
        try std.testing.expect(!sink.hasErrors());
        const exec_info = parsed_build.action.execute_subcommand;
        try std.testing.expectEqual(corex.codegen_abi.LinkMode.static, exec_info.link_mode);
        try std.testing.expect(exec_info.is_emit_obj);
        try std.testing.expectEqual(@as(usize, 2), exec_info.c_defines.len);
        try std.testing.expectEqualStrings("FEAT_FAST", exec_info.c_defines[0].name);
        try std.testing.expectEqualStrings("1", exec_info.c_defines[0].value.?);
        try std.testing.expectEqualStrings("NDEBUG", exec_info.c_defines[1].name);
        try std.testing.expect(exec_info.c_defines[1].value == null);
        try std.testing.expectEqual(@as(usize, 2), exec_info.include_dirs.len);
        try std.testing.expectEqualStrings("include", exec_info.include_dirs[0]);
        try std.testing.expectEqualStrings("vendor/inc", exec_info.include_dirs[1]);
        try std.testing.expectEqual(@as(usize, 3), exec_info.extra_libs.len);
        try std.testing.expectEqualStrings("sqlite3", exec_info.extra_libs[0]);
        try std.testing.expectEqualStrings("m", exec_info.extra_libs[1]);
        try std.testing.expectEqualStrings("user32.def", exec_info.extra_libs[2]);
        try std.testing.expectEqual(@as(usize, 3), exec_info.lib_dirs.len);
        try std.testing.expectEqualStrings("/usr/local/lib", exec_info.lib_dirs[0]);
        try std.testing.expectEqualStrings("vendor/lib", exec_info.lib_dirs[1]);
        try std.testing.expectEqualStrings("build/deps", exec_info.lib_dirs[2]);
        try std.testing.expectEqualStrings("build/app.o", exec_info.output_path.?);
        try std.testing.expectEqual(
            corex.codegen_abi.TargetSpec.X86_64_LINUX_MUSL,
            exec_info.target_spec.?,
        );

        const parsed_dyn = try router.parseArgs(&.{ "build", "--link", "dynamic", "app.cx" }, &sink);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expectEqual(corex.codegen_abi.LinkMode.dynamic, parsed_dyn.link_mode);
    }

    // [4] Verify invalid `--link` mode (`E0001`), missing `--link` (`E0003`), and `--emit-obj` + `--emit-c` conflict:
    {
        var bad_link_sink = DiagnosticSink.init(std.testing.allocator);
        defer bad_link_sink.deinit();
        _ = try router.parseArgs(&.{ "build", "--link=bogus", "app.cx" }, &bad_link_sink);
        try std.testing.expect(bad_link_sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0001_unknown_cli_flag, bad_link_sink.asSlice()[0].code);

        var missing_link_sink = DiagnosticSink.init(std.testing.allocator);
        defer missing_link_sink.deinit();
        _ = try router.parseArgs(&.{ "build", "--link" }, &missing_link_sink);
        try std.testing.expect(missing_link_sink.hasErrors());
        try std.testing.expectEqual(
            corex.DiagnosticCode.e0003_missing_cli_argument,
            missing_link_sink.asSlice()[0].code,
        );

        var emit_conflict_sink = DiagnosticSink.init(std.testing.allocator);
        defer emit_conflict_sink.deinit();
        _ = try router.parseArgs(&.{ "build", "--emit-obj", "--emit-c", "app.cx" }, &emit_conflict_sink);
        try std.testing.expect(emit_conflict_sink.hasErrors());
        try std.testing.expectEqual(
            corex.DiagnosticCode.e0001_unknown_cli_flag,
            emit_conflict_sink.asSlice()[0].code,
        );
    }
}

test "test_cli_translate_c_arg_parsing_help_and_end_to_end_execution" {
    // [1] Verify `TRANSLATE_C_FLAGS`, `corex translate-c --help`, and `parseArgs` flag extraction:
    {
        try std.testing.expectEqual(@as(usize, 5), router.TRANSLATE_C_FLAGS.len);
        var tc_help_buf: [4096]u8 = undefined;
        var tc_help_writer = std.Io.Writer.fixed(&tc_help_buf);
        try router.renderSubcommandHelp(&tc_help_writer, StyleConfig.MONOCHROME, .translate_c);
        const tc_help_text = tc_help_writer.buffered();
        try std.testing.expect(std.mem.indexOf(u8, tc_help_text, "Translate-C Options:") != null);
        try std.testing.expect(std.mem.indexOf(u8, tc_help_text, "Usage: corex translate-c [OPTIONS] <header.h>") != null);
        for (router.TRANSLATE_C_FLAGS) |tc_flag| {
            try std.testing.expect(std.mem.indexOf(u8, tc_help_text, tc_flag.long_flag) != null);
            try std.testing.expect(std.mem.indexOf(u8, tc_help_text, tc_flag.summary) != null);
        }

        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();
        const parsed_tc = try router.parseArgs(
            &.{
                "translate-c",
                "-DAPI_LEVEL=3",
                "--define=ENABLE_SIMD",
                "-Iinclude",
                "--include-dir=third_party/inc",
                "--internal-core",
                "--target=aarch64-apple-darwin",
                "-o",
                "out/api.cx",
                "include/api.h",
            },
            &sink,
        );
        try std.testing.expect(!sink.hasErrors());
        const tc_exec = parsed_tc.action.execute_subcommand;
        try std.testing.expectEqual(router.SubcommandId.translate_c, tc_exec.subcommand);
        try std.testing.expect(tc_exec.is_internal_core);
        try std.testing.expectEqual(@as(usize, 2), tc_exec.c_defines.len);
        try std.testing.expectEqualStrings("API_LEVEL", tc_exec.c_defines[0].name);
        try std.testing.expectEqualStrings("3", tc_exec.c_defines[0].value.?);
        try std.testing.expectEqualStrings("ENABLE_SIMD", tc_exec.c_defines[1].name);
        try std.testing.expect(tc_exec.c_defines[1].value == null);
        try std.testing.expectEqual(@as(usize, 2), tc_exec.include_dirs.len);
        try std.testing.expectEqualStrings("include", tc_exec.include_dirs[0]);
        try std.testing.expectEqualStrings("third_party/inc", tc_exec.include_dirs[1]);
        try std.testing.expectEqualStrings("out/api.cx", tc_exec.output_path.?);
        try std.testing.expectEqual(
            corex.codegen_abi.TargetSpec.AARCH64_APPLE_DARWIN,
            tc_exec.target_spec.?,
        );
        try std.testing.expectEqual(@as(usize, 1), tc_exec.positional_args.len);
        try std.testing.expectEqualStrings("include/api.h", tc_exec.positional_args[0]);

        // Compile-only flags (`-ofmt=c`, `--release`) and bad `-D123` emit `E0001` on `translate-c`:
        var bad_tc_sink = DiagnosticSink.init(std.testing.allocator);
        defer bad_tc_sink.deinit();
        _ = try router.parseArgs(&.{ "translate-c", "-ofmt=c", "api.h" }, &bad_tc_sink);
        try std.testing.expect(bad_tc_sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0001_unknown_cli_flag, bad_tc_sink.asSlice()[0].code);

        var bad_def_sink = DiagnosticSink.init(std.testing.allocator);
        defer bad_def_sink.deinit();
        _ = try router.parseArgs(&.{ "translate-c", "-D123=bad", "api.h" }, &bad_def_sink);
        try std.testing.expect(bad_def_sink.hasErrors());
        try std.testing.expectEqual(corex.DiagnosticCode.e0001_unknown_cli_flag, bad_def_sink.asSlice()[0].code);
    }

    // [2] End-to-end `runCli` execution of `corex translate-c` (stdout mode, `-o` atomic file mode, and error codes):
    const scratch_root = ".zig-cache/test_cli_translate_c";
    const inc_subdir = ".zig-cache/test_cli_translate_c/inc";
    const sibling_hdr_path = ".zig-cache/test_cli_translate_c/sibling.h";
    const extra_hdr_path = ".zig-cache/test_cli_translate_c/inc/extra_cfg.h";
    const main_hdr_path = ".zig-cache/test_cli_translate_c/sample_api.h";
    const bad_hdr_path = ".zig-cache/test_cli_translate_c/bad_header.h";
    const out_cx_path = ".zig-cache/test_cli_translate_c/generated_bindings.cx";

    try std.Io.Dir.cwd().createDirPath(std.testing.io, inc_subdir);
    defer std.Io.Dir.cwd().deleteTree(std.testing.io, scratch_root) catch {};

    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = sibling_hdr_path,
        .data = "typedef unsigned int SiblingFlags;\n",
    });
    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = extra_hdr_path,
        .data = "#define EXTRA_SCALE 8\n",
    });
    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = main_hdr_path,
        .data =
        \\#include <stdint.h>
        \\#include "sibling.h"
        \\#include "extra_cfg.h"
        \\
        \\#if defined(CLI_MODE) && CLI_MODE == 2
        \\#define ACTIVE_PORT 8080
        \\#else
        \\#define ACTIVE_PORT 80
        \\#endif
        \\
        \\struct WireHeader {
        \\    int kind : 10;
        \\    short flags : 10;
        \\};
        \\
        \\int open_channel(const char *endpoint, SiblingFlags flags);
        \\
        ,
    });
    try std.Io.Dir.cwd().writeFile(std.testing.io, .{
        .sub_path = bad_hdr_path,
        .data = "#error unsupported C header configuration\n",
    });

    var out_buf: [16384]u8 = undefined;
    var err_buf: [8192]u8 = undefined;

    // (a) Direct stdout emission (`-o` omitted) targeting `x86_64-linux-gnu`:
    {
        var out_writer = std.Io.Writer.fixed(&out_buf);
        var err_writer = std.Io.Writer.fixed(&err_buf);
        const exit_code = try router.runCli(
            std.testing.allocator,
            std.testing.io,
            null,
            &.{
                "--color=never",
                "translate-c",
                "-DCLI_MODE=2",
                "-I",
                inc_subdir,
                "--target=x86_64-linux-gnu",
                main_hdr_path,
            },
            &out_writer,
            &err_writer,
        );
        try std.testing.expectEqual(@as(u8, 0), exit_code);
        try std.testing.expectEqual(@as(usize, 0), err_writer.buffered().len);
        const stdout_cx = out_writer.buffered();
        try std.testing.expect(std.mem.indexOf(u8, stdout_cx, "use cx.ffi.{") != null);
        try std.testing.expect(std.mem.indexOf(u8, stdout_cx, "pub const ACTIVE_PORT: i64 = 8080_i64;") != null);
        try std.testing.expect(std.mem.indexOf(u8, stdout_cx, "pub const EXTRA_SCALE: i64 = 8_i64;") != null);
        try std.testing.expect(std.mem.indexOf(u8, stdout_cx, "pub extern \"C\" fn open_channel(") != null);
    }

    // (b) Atomic `-o <path>` file emission with `--internal-core` and `--target=x86_64-windows-msvc`:
    {
        var out_writer = std.Io.Writer.fixed(&out_buf);
        var err_writer = std.Io.Writer.fixed(&err_buf);
        const exit_code = try router.runCli(
            std.testing.allocator,
            std.testing.io,
            null,
            &.{
                "--color=never",
                "translate-c",
                "--internal-core",
                "-I",
                inc_subdir,
                "--target=x86_64-windows-msvc",
                "-o",
                out_cx_path,
                main_hdr_path,
            },
            &out_writer,
            &err_writer,
        );
        try std.testing.expectEqual(@as(u8, 0), exit_code);
        try std.testing.expectEqualStrings(
            "✓ translate-c: " ++ out_cx_path ++ "\n",
            out_writer.buffered(),
        );
        const disk_cx = try std.Io.Dir.cwd().readFileAlloc(
            std.testing.io,
            out_cx_path,
            std.testing.allocator,
            .limited(64 * 1024),
        );
        defer std.testing.allocator.free(disk_cx);
        try std.testing.expect(std.mem.indexOf(u8, disk_cx, "use core.ffi.{") != null);
        try std.testing.expect(std.mem.indexOf(u8, disk_cx, "pub const ACTIVE_PORT: i64 = 80_i64;") != null);
    }

    // (c) Missing `<header.h>` (`E0003`), missing file (`E0004`), and C `#error` (`E0009`):
    {
        var out_writer = std.Io.Writer.fixed(&out_buf);
        var err_writer = std.Io.Writer.fixed(&err_buf);
        const missing_arg_exit = try router.runCli(
            std.testing.allocator,
            std.testing.io,
            null,
            &.{ "--color=never", "translate-c" },
            &out_writer,
            &err_writer,
        );
        try std.testing.expectEqual(@as(u8, 1), missing_arg_exit);
        try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "error[E0003]") != null);

        out_writer = std.Io.Writer.fixed(&out_buf);
        err_writer = std.Io.Writer.fixed(&err_buf);
        const missing_file_exit = try router.runCli(
            std.testing.allocator,
            std.testing.io,
            null,
            &.{ "--color=never", "translate-c", ".zig-cache/nonexistent_header_xyz.h" },
            &out_writer,
            &err_writer,
        );
        try std.testing.expectEqual(@as(u8, 1), missing_file_exit);
        try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "error[E0004]") != null);

        out_writer = std.Io.Writer.fixed(&out_buf);
        err_writer = std.Io.Writer.fixed(&err_buf);
        const c_err_exit = try router.runCli(
            std.testing.allocator,
            std.testing.io,
            null,
            &.{ "--color=never", "translate-c", bad_hdr_path },
            &out_writer,
            &err_writer,
        );
        try std.testing.expectEqual(@as(u8, 1), c_err_exit);
        try std.testing.expect(std.mem.indexOf(u8, err_writer.buffered(), "error[E0009]") != null);
    }
}

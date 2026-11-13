//! CLI Command Router, Dynamic Metadata Registry & Typo Suggestion Engine
//!
//! Defines the canonical `SUBCOMMANDS` (`build`, `run`, `check`, `test`, `fmt`, `upgrade`, `lsp`, `bench`)
//! and `GLOBAL_FLAGS` (`-h`/`--help`, `-V`/`--version`, `--color=<when>`) metadata tables.
//!
//! Parses command-line arguments in a single pass, emits `E0001`/`E0002` diagnostics with stack-allocated
//! Levenshtein typo suggestions (`help: did you mean \`…\`?`), and renders the monochrome help menu.

const std = @import("std");
const mem = @import("../mem_foundation.zig");
const vfs = @import("../vfs_sourcemap.zig");
const style = @import("style.zig");
const box_draw = @import("box_draw.zig");
const diag = @import("../diag/diagnostic.zig");
const renderer = @import("../diag/renderer.zig");
const bench_harness = @import("../bench/harness.zig");
const fmt_engine = @import("../fmt_engine.zig");
const query_db = @import("../query_db.zig");

const ColorMode = style.ColorMode;
const Glyphs = style.Glyphs;
const StyleConfig = style.StyleConfig;
const CardRenderer = box_draw.CardRenderer;
const DiagnosticSink = diag.DiagnosticSink;
const DiagnosticRenderer = renderer.DiagnosticRenderer;

// ---------------------------------------- TYPES ----------------------------------------

/// Canonical CoreX CLI subcommand identifiers indexed 1-to-1 into `SUBCOMMANDS`.
pub const SubcommandId = enum(u8) {
    /// `corex build` – compile package or source file into a native or WebAssembly artifact.
    build = 0,
    /// `corex run` – compile and immediately execute a CoreX binary.
    run = 1,
    /// `corex check` – run fast syntax, type, region, and SAST verification without codegen.
    check = 2,
    /// `corex test` – compile and execute unit, snapshot, and safety verification suites.
    @"test" = 3,
    /// `corex fmt` – format CoreX source files canonically using the lossless CST.
    fmt = 4,
    /// `corex upgrade` – apply automated AST/CST migrations and machine-applicable fixes.
    upgrade = 5,
    /// `corex lsp` – start the CoreX Language Server Protocol (LSP) daemon over stdio.
    lsp = 6,
    /// `corex bench` – run statistical performance benchmarks and emit monochrome report tables.
    bench = 7,

    /// Ergonomic identifier alias for `.@"test"`.
    pub const test_cmd: SubcommandId = .@"test";

    /// Returns the static `SubcommandDescriptor` for this `SubcommandId` in $O(1)$ time.
    pub inline fn asDescriptor(self: SubcommandId) SubcommandDescriptor {
        return SUBCOMMANDS[@backingInt(self)];
    }

    /// Returns the canonical CLI subcommand token string (e.g., `"build"`).
    pub inline fn asName(self: SubcommandId) []const u8 {
        return self.asDescriptor().name;
    }

    /// Resolves a CLI token string to its `SubcommandId` if it matches a canonical subcommand.
    pub fn fromName(name_str: []const u8) ?SubcommandId {
        for (SUBCOMMANDS) |descriptor| {
            if (std.mem.eql(u8, descriptor.name, name_str)) {
                return descriptor.id;
            }
        }
        return null;
    }
};

/// Static metadata entry in `SUBCOMMANDS` driving both CLI dispatch and `corex --help`.
pub const SubcommandDescriptor = struct {
    /// Strongly typed subcommand enum tag.
    id: SubcommandId,
    /// Exact CLI subcommand token.
    name: []const u8,
    /// Positional argument synopsis for help rendering.
    usage: []const u8,
    /// Concise one-line summary displayed in `corex --help`.
    summary: []const u8,
};

/// Canonical global CLI option identifiers indexed 1-to-1 into `GLOBAL_FLAGS`.
pub const GlobalFlagId = enum(u8) {
    /// `-h` / `--help` – display help menu.
    help = 0,
    /// `-V` / `--version` – display toolchain version.
    version = 1,
    /// `--color=<when>` – configure terminal ANSI color output.
    color = 2,
};

/// Static metadata entry in `GLOBAL_FLAGS` driving both flag parsing and `corex --help`.
pub const GlobalFlagDescriptor = struct {
    /// Strongly typed global flag enum tag.
    id: GlobalFlagId,
    /// Optional short flag token (e.g., `"-h"`).
    short_flag: ?[]const u8,
    /// Canonical long flag token (e.g., `"--help"`).
    long_flag: []const u8,
    /// Optional value placeholder suffix (e.g., `"=<when>"`).
    value_suffix: ?[]const u8 = null,
    /// Concise one-line summary displayed in `corex --help`.
    summary: []const u8,
};

/// Subcommand-specific CLI option identifiers for `corex fmt` (`FMT_FLAGS`).
pub const FmtFlagId = enum(u8) {
    /// `--check` – verify formatting without writing files (`0`).
    check = 0,
    /// `--fix` – apply canonical identifier casing and missing `;` autofixes (`1`).
    fix = 1,
};

/// Static metadata entry in `FMT_FLAGS` describing `corex fmt` flags.
pub const FmtFlagDescriptor = struct {
    /// Strongly typed `corex fmt` flag enum tag.
    id: FmtFlagId,
    /// Canonical long flag token (e.g., `"--check"`).
    long_flag: []const u8,
    /// Concise one-line summary.
    summary: []const u8,
};

/// Subcommand-specific CLI option identifiers for compilation/verification subcommands (`COMPILE_FLAGS`).
pub const CompileFlagId = enum(u8) {
    /// `--comptime-limit=<steps>` – configure `MirVm` compile-time execution step budget (`0`).
    comptime_limit = 0,
    /// `--dev` – compile in fast development mode (`1`).
    dev = 1,
    /// `--release` – compile in production release mode (`2`).
    release = 2,
    /// `--sast-strict` – emit `W0314` warnings on unproven bounds checks (`3`).
    sast_strict = 3,
};

/// Static metadata entry in `COMPILE_FLAGS` describing `build`/`run`/`check`/`test` flags.
pub const CompileFlagDescriptor = struct {
    /// Strongly typed compilation flag enum tag.
    id: CompileFlagId,
    /// Canonical long flag token (e.g., `"--comptime-limit"`).
    long_flag: []const u8,
    /// Optional value placeholder suffix (e.g., `"=<steps>"`).
    value_suffix: ?[]const u8 = null,
    /// Concise one-line summary displayed in subcommand `--help`.
    summary: []const u8,
};

/// Resolved CLI action produced by `parseArgs`.
pub const CommandAction = union(enum) {
    /// Render the global or subcommand-specific `--help` menu and exit `0`.
    show_help: ?SubcommandId,
    /// Render the `--version` banner and exit `0`.
    show_version: void,
    /// Execute the selected `subcommand` with remaining `positional_args`.
    execute_subcommand: struct {
        /// Target subcommand to run.
        subcommand: SubcommandId,
        /// Slice of positional arguments allocated in `DiagnosticSink.arena`.
        positional_args: []const []const u8,
        /// Whether `--check` was passed (e.g., `corex fmt --check`).
        is_check_only: bool = false,
        /// Whether `--fix` was passed (e.g., `corex fmt --fix`).
        is_fix_mode: bool = false,
        /// Maximum `MirVm` compile-time execution step budget (`--comptime-limit`).
        comptime_step_limit: u64 = DEFAULT_COMPTIME_STEP_LIMIT,
        /// Whether `--release` optimization mode was selected (`false` for `--dev` default).
        is_release_mode: bool = false,
        /// Whether `--sast-strict` was passed to warn (`W0314`) on unproven bounds checks.
        is_sast_strict: bool = false,
    },
    /// Invalid CLI invocation; errors have been emitted into `DiagnosticSink`.
    invalid: void,
};

/// Result of parsing process command-line arguments via `parseArgs`.
pub const ParsedCommand = struct {
    /// Requested terminal color policy (`auto` by default).
    color_mode: ColorMode = .auto,
    /// Resolved command action to execute.
    action: CommandAction = .{ .show_help = null },
    /// Whether `--check` was passed on `corex fmt`.
    is_check_only: bool = false,
    /// Whether `--fix` was passed on `corex fmt`.
    is_fix_mode: bool = false,
    /// Maximum `MirVm` compile-time execution step budget (`--comptime-limit`).
    comptime_step_limit: u64 = DEFAULT_COMPTIME_STEP_LIMIT,
    /// Whether `--release` optimization mode was selected (`false` for `--dev` default).
    is_release_mode: bool = false,
    /// Whether `--sast-strict` was passed on a compile/check subcommand.
    is_sast_strict: bool = false,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical Stage 0 toolchain version string.
pub const COREX_VERSION: []const u8 = "0.1.0-dev";
/// Default compile-time virtual machine instruction step fuel budget (`DR-05` Section 3.3).
pub const DEFAULT_COMPTIME_STEP_LIMIT: u64 = 10_000_000;
/// Maximum Levenshtein edit distance eligible for typo suggestions.
pub const MAX_EDIT_DISTANCE: usize = 2;

/// Canonical subcommand table (`phase0_spec.md` Section 9.1).
pub const SUBCOMMANDS = [_]SubcommandDescriptor{
    .{
        .id = .build,
        .name = "build",
        .usage = "[path]",
        .summary = "Compile a CoreX package or source file into a native or WebAssembly artifact",
    },
    .{
        .id = .run,
        .name = "run",
        .usage = "[path] [-- args…]",
        .summary = "Compile and immediately execute a CoreX binary",
    },
    .{
        .id = .check,
        .name = "check",
        .usage = "[path…]",
        .summary = "Run fast syntax, type, region, and SAST verification without codegen",
    },
    .{
        .id = .@"test",
        .name = "test",
        .usage = "[filter]",
        .summary = "Compile and execute unit, snapshot, and safety verification suites",
    },
    .{
        .id = .fmt,
        .name = "fmt",
        .usage = "[path…]",
        .summary = "Format CoreX source files canonically using the lossless CST",
    },
    .{
        .id = .upgrade,
        .name = "upgrade",
        .usage = "[path…]",
        .summary = "Apply automated AST/CST migrations and machine-applicable fixes",
    },
    .{
        .id = .lsp,
        .name = "lsp",
        .usage = "",
        .summary = "Start the CoreX Language Server Protocol (LSP) daemon over stdio",
    },
    .{
        .id = .bench,
        .name = "bench",
        .usage = "[filter]",
        .summary = "Run statistical performance benchmarks and emit monochrome report tables",
    },
};

/// Canonical global option table (`phase0_spec.md` Section 9.1).
pub const GLOBAL_FLAGS = [_]GlobalFlagDescriptor{
    .{
        .id = .help,
        .short_flag = "-h",
        .long_flag = "--help",
        .value_suffix = null,
        .summary = "Display this help menu or subcommand documentation",
    },
    .{
        .id = .version,
        .short_flag = "-V",
        .long_flag = "--version",
        .value_suffix = null,
        .summary = "Display the CoreX toolchain version",
    },
    .{
        .id = .color,
        .short_flag = null,
        .long_flag = "--color",
        .value_suffix = "=<when>",
        .summary = "Configure terminal ANSI color output (default: auto)",
    },
};

/// Canonical `corex fmt` option table (`DR-14` Section 1.5).
pub const FMT_FLAGS = [_]FmtFlagDescriptor{
    .{
        .id = .check,
        .long_flag = "--check",
        .summary = "Verify that source files are formatted without writing changes to disk",
    },
    .{
        .id = .fix,
        .long_flag = "--fix",
        .summary = "Apply canonical identifier casing and missing semicolon autofixes",
    },
};

/// Canonical compilation and verification option table (`build`, `run`, `check`, `test`).
pub const COMPILE_FLAGS = [_]CompileFlagDescriptor{
    .{
        .id = .comptime_limit,
        .long_flag = "--comptime-limit",
        .value_suffix = "=<steps>",
        .summary = std.fmt.comptimePrint(
            "Set maximum compile-time VM execution step budget (default: {d})",
            .{DEFAULT_COMPTIME_STEP_LIMIT},
        ),
    },
    .{
        .id = .dev,
        .long_flag = "--dev",
        .value_suffix = null,
        .summary = "Compile in fast development mode with local constant folding",
    },
    .{
        .id = .release,
        .long_flag = "--release",
        .value_suffix = null,
        .summary = "Compile in production release mode with full SSA optimization",
    },
    .{
        .id = .sast_strict,
        .long_flag = "--sast-strict",
        .value_suffix = null,
        .summary = "Emit W0314 warnings when array or slice bounds checks cannot be statically elided",
    },
};

// -------------------------------------- INTERNALS --------------------------------------

/// Extracts a strictly positive ASCII decimal step count (`> 0`), rejecting empty, signed, or zero values.
fn extractPositiveStepLimit(raw_val: []const u8) ?u64 {
    if (raw_val.len == 0) return null;
    for (raw_val) |byte_val| {
        if (!std.ascii.isDigit(byte_val)) return null;
    }
    const parsed_val = std.fmt.parseUnsigned(u64, raw_val, 10) catch return null;
    return if (parsed_val > 0) parsed_val else null;
}

/// Emits an `E0001` diagnostic when `--comptime-limit` receives a non-numeric, negative, or zero value.
fn emitInvalidComptimeLimitDiagnostic(sink: *DiagnosticSink, raw_step_val: []const u8) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "invalid step count `{s}` for `--comptime-limit`; expected positive integer > 0",
            .{raw_step_val},
        ),
        .notes = &.{"help: pass a positive integer such as `--comptime-limit=10000000`"},
    });
}

/// Emits an `E0001` diagnostic when both `--dev` and `--release` are passed together.
fn emitConflictingOptFlagsDiagnostic(sink: *DiagnosticSink) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = "conflicting CLI optimization flags `--dev` and `--release`",
        .notes = &.{"help: pass either `--dev` or `--release`, not both"},
    });
}

/// Emits an `E0001` diagnostic for an unrecognized CLI flag, attaching a typo hint if within distance 2.
fn emitUnknownFlagDiagnostic(
    sink: *DiagnosticSink,
    unknown_flag: []const u8,
    subcommand: ?SubcommandId,
) !void {
    const msg = try std.fmt.allocPrint(sink.arena.asAllocator(), "unknown CLI option `{s}`", .{unknown_flag});
    if (suggestFlagForSubcommand(unknown_flag, subcommand)) |suggested_flag| {
        try sink.emit(.{
            .code = .e0001_unknown_cli_flag,
            .severity = .err,
            .message = msg,
            .notes = &.{try std.fmt.allocPrint(sink.arena.asAllocator(), "help: did you mean `{s}`?", .{suggested_flag})},
        });
    } else {
        try sink.emit(.{
            .code = .e0001_unknown_cli_flag,
            .severity = .err,
            .message = msg,
            .notes = &.{"help: run `corex --help` to see all available options"},
        });
    }
}

/// Emits an `E0002` diagnostic for an unrecognized CLI subcommand, attaching a typo hint if within distance 2.
fn emitUnknownSubcommandDiagnostic(sink: *DiagnosticSink, unknown_cmd: []const u8) !void {
    const msg = try std.fmt.allocPrint(sink.arena.asAllocator(), "unknown CLI subcommand `{s}`", .{unknown_cmd});
    if (suggestSubcommand(unknown_cmd)) |suggested_cmd| {
        try sink.emit(.{
            .code = .e0002_unknown_cli_subcommand,
            .severity = .err,
            .message = msg,
            .notes = &.{try std.fmt.allocPrint(sink.arena.asAllocator(), "help: did you mean `{s}`?", .{suggested_cmd})},
        });
    } else {
        try sink.emit(.{
            .code = .e0002_unknown_cli_subcommand,
            .severity = .err,
            .message = msg,
            .notes = &.{"help: run `corex --help` to see all available subcommands"},
        });
    }
}

/// Emits an `E0001` diagnostic when `--color` receives an invalid value.
fn emitInvalidColorValueDiagnostic(sink: *DiagnosticSink, raw_color_val: []const u8) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "invalid color value `{s}` for `--color`",
            .{raw_color_val},
        ),
        .notes = &.{"help: valid values for `--color` are `auto`, `always`, or `never`"},
    });
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Computes bounded Wagner–Fischer Levenshtein edit distance using a fixed stack buffer (zero heap allocations).
pub fn computeLevenshteinDistance(input_text: []const u8, candidate_text: []const u8) usize {
    if (input_text.len > 63 or candidate_text.len > 63) {
        return std.math.maxInt(usize);
    }
    if (std.mem.eql(u8, input_text, candidate_text)) return 0;
    if (input_text.len == 0) return candidate_text.len;
    if (candidate_text.len == 0) return input_text.len;

    var row_buffer: [64]usize = undefined;
    var j: usize = 0;
    while (j <= candidate_text.len) : (j += 1) {
        row_buffer[j] = j;
    }

    for (input_text, 0..) |input_byte, i| {
        var prev_diagonal = row_buffer[0];
        row_buffer[0] = i + 1;
        for (candidate_text, 0..) |cand_byte, col_idx| {
            const old_upper = row_buffer[col_idx + 1];
            row_buffer[col_idx + 1] = @min(
                @min(row_buffer[col_idx] + 1, old_upper + 1),
                prev_diagonal + @as(usize, if (input_byte == cand_byte) 0 else 1),
            );
            prev_diagonal = old_upper;
        }
    }
    return row_buffer[candidate_text.len];
}

/// Returns the closest subcommand name in `SUBCOMMANDS` within edit distance `<= 2`, or `null`.
pub fn suggestSubcommand(unknown_subcommand: []const u8) ?[]const u8 {
    var best_match: ?[]const u8 = null;
    var best_distance: usize = MAX_EDIT_DISTANCE + 1;
    for (SUBCOMMANDS) |descriptor| {
        const dist = computeLevenshteinDistance(unknown_subcommand, descriptor.name);
        if (dist < best_distance) {
            best_distance = dist;
            best_match = descriptor.name;
        }
    }
    return best_match;
}

/// Returns the closest global flag in `GLOBAL_FLAGS` within edit distance `<= 2`, or `null`.
pub fn suggestGlobalFlag(unknown_flag: []const u8) ?[]const u8 {
    return suggestFlagForSubcommand(unknown_flag, null);
}

/// Returns `true` if `subcommand` accepts `COMPILE_FLAGS` (`build`, `run`, `check`, `test`).
pub inline fn isCompileSubcommand(subcommand: SubcommandId) bool {
    return switch (subcommand) {
        .build, .run, .check, .@"test" => true,
        else => false,
    };
}

/// Returns the closest global or subcommand-specific flag within edit distance `<= 2`, or `null`.
pub fn suggestFlagForSubcommand(unknown_flag: []const u8, subcommand: ?SubcommandId) ?[]const u8 {
    const flag_name = if (std.mem.indexOfScalar(u8, unknown_flag, '=')) |eq_idx|
        unknown_flag[0..eq_idx]
    else
        unknown_flag;

    var best_match: ?[]const u8 = null;
    var best_distance: usize = MAX_EDIT_DISTANCE + 1;
    for (GLOBAL_FLAGS) |descriptor| {
        const long_dist = computeLevenshteinDistance(flag_name, descriptor.long_flag);
        if (long_dist < best_distance) {
            best_distance = long_dist;
            best_match = descriptor.long_flag;
        }
        if (descriptor.short_flag) |short_str| {
            const short_dist = computeLevenshteinDistance(flag_name, short_str);
            if (short_dist < best_distance) {
                best_distance = short_dist;
                best_match = short_str;
            }
        }
    }
    if (subcommand == .fmt) {
        for (FMT_FLAGS) |fmt_desc| {
            const fmt_dist = computeLevenshteinDistance(flag_name, fmt_desc.long_flag);
            if (fmt_dist < best_distance) {
                best_distance = fmt_dist;
                best_match = fmt_desc.long_flag;
            }
        }
    } else if (subcommand) |sub_id| {
        if (isCompileSubcommand(sub_id)) {
            for (COMPILE_FLAGS) |comp_desc| {
                const comp_dist = computeLevenshteinDistance(flag_name, comp_desc.long_flag);
                if (comp_dist < best_distance) {
                    best_distance = comp_dist;
                    best_match = comp_desc.long_flag;
                }
            }
        }
    }
    return best_match;
}

/// Parses CLI arguments (excluding `argv[0]`), emitting `E0001`/`E0002`/`E0003` into `sink` on error.
pub fn parseArgs(raw_args: []const []const u8, sink: *DiagnosticSink) !ParsedCommand {
    var color_mode: ColorMode = .auto;
    var has_help_flag = false;
    var has_version_flag = false;
    var is_check_only = false;
    var is_fix_mode = false;
    var comptime_step_limit: u64 = DEFAULT_COMPTIME_STEP_LIMIT;
    var has_seen_dev = false;
    var has_seen_release = false;
    var is_sast_strict = false;
    var selected_subcommand: ?SubcommandId = null;
    var positional_list: std.ArrayList([]const u8) = .empty;
    var is_after_double_dash = false;

    var arg_idx: usize = 0;
    while (arg_idx < raw_args.len) : (arg_idx += 1) {
        const arg_text = raw_args[arg_idx];
        if (!is_after_double_dash and std.mem.eql(u8, arg_text, "--")) {
            is_after_double_dash = true;
            continue;
        }

        if (!is_after_double_dash and std.mem.startsWith(u8, arg_text, "-")) {
            const is_compile_sub = selected_subcommand != null and isCompileSubcommand(selected_subcommand.?);
            if (std.mem.eql(u8, arg_text, "-h") or std.mem.eql(u8, arg_text, "--help")) {
                has_help_flag = true;
            } else if (std.mem.eql(u8, arg_text, "-V") or std.mem.eql(u8, arg_text, "--version")) {
                has_version_flag = true;
            } else if (selected_subcommand == .fmt and std.mem.eql(u8, arg_text, "--check")) {
                is_check_only = true;
            } else if (selected_subcommand == .fmt and std.mem.eql(u8, arg_text, "--fix")) {
                is_fix_mode = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--dev")) {
                if (has_seen_release) {
                    try emitConflictingOptFlagsDiagnostic(sink);
                }
                has_seen_dev = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--release")) {
                if (has_seen_dev) {
                    try emitConflictingOptFlagsDiagnostic(sink);
                }
                has_seen_release = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--sast-strict")) {
                is_sast_strict = true;
            } else if (is_compile_sub and std.mem.startsWith(u8, arg_text, "--comptime-limit=")) {
                const raw_val = arg_text["--comptime-limit=".len..];
                if (extractPositiveStepLimit(raw_val)) |parsed_steps| {
                    comptime_step_limit = parsed_steps;
                } else {
                    try emitInvalidComptimeLimitDiagnostic(sink, raw_val);
                }
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--comptime-limit")) {
                if (arg_idx + 1 >= raw_args.len) {
                    try sink.emit(.{
                        .code = .e0003_missing_cli_argument,
                        .severity = .err,
                        .message = "missing step count for `--comptime-limit`; expected positive integer",
                        .notes = &.{"help: pass `--comptime-limit=<steps>` (e.g., `--comptime-limit=10000000`)"},
                    });
                } else {
                    arg_idx += 1;
                    const next_val = raw_args[arg_idx];
                    if (extractPositiveStepLimit(next_val)) |parsed_steps| {
                        comptime_step_limit = parsed_steps;
                    } else {
                        try emitInvalidComptimeLimitDiagnostic(sink, next_val);
                    }
                }
            } else if (std.mem.startsWith(u8, arg_text, "--color=")) {
                const raw_val = arg_text["--color=".len..];
                if (ColorMode.parse(raw_val)) |parsed_mode| {
                    color_mode = parsed_mode;
                } else {
                    try emitInvalidColorValueDiagnostic(sink, raw_val);
                }
            } else if (std.mem.eql(u8, arg_text, "--color")) {
                if (arg_idx + 1 >= raw_args.len) {
                    try sink.emit(.{
                        .code = .e0003_missing_cli_argument,
                        .severity = .err,
                        .message = "missing value for `--color`; expected `auto`, `always`, or `never`",
                        .notes = &.{"help: pass `--color=auto`, `--color=always`, or `--color=never`"},
                    });
                } else {
                    arg_idx += 1;
                    const next_val = raw_args[arg_idx];
                    if (ColorMode.parse(next_val)) |parsed_mode| {
                        color_mode = parsed_mode;
                    } else {
                        try emitInvalidColorValueDiagnostic(sink, next_val);
                    }
                }
            } else {
                try emitUnknownFlagDiagnostic(sink, arg_text, selected_subcommand);
            }
            continue;
        }

        if (selected_subcommand == null) {
            if (SubcommandId.fromName(arg_text)) |sub_id| {
                selected_subcommand = sub_id;
            } else {
                try emitUnknownSubcommandDiagnostic(sink, arg_text);
            }
        } else {
            try positional_list.append(sink.arena.asAllocator(), arg_text);
        }
    }

    if (sink.hasErrors()) {
        return .{ .color_mode = color_mode, .action = .invalid };
    }
    if (has_help_flag) {
        return .{ .color_mode = color_mode, .action = .{ .show_help = selected_subcommand } };
    }
    if (has_version_flag) {
        return .{ .color_mode = color_mode, .action = .show_version };
    }
    if (selected_subcommand) |sub_id| {
        return .{
            .color_mode = color_mode,
            .is_check_only = is_check_only,
            .is_fix_mode = is_fix_mode,
            .comptime_step_limit = comptime_step_limit,
            .is_release_mode = has_seen_release,
            .is_sast_strict = is_sast_strict,
            .action = .{
                .execute_subcommand = .{
                    .subcommand = sub_id,
                    .positional_args = positional_list.items,
                    .is_check_only = is_check_only,
                    .is_fix_mode = is_fix_mode,
                    .comptime_step_limit = comptime_step_limit,
                    .is_release_mode = has_seen_release,
                    .is_sast_strict = is_sast_strict,
                },
            },
        };
    }
    return .{ .color_mode = color_mode, .action = .{ .show_help = null } };
}

/// Renders the monochrome Unicode `corex --help` menu dynamically from `SUBCOMMANDS` and `GLOBAL_FLAGS`.
pub fn renderHelp(writer: *std.Io.Writer, style_config: StyleConfig) std.Io.Writer.Error!void {
    // [1] Render rounded header banner card:
    try CardRenderer.init(style_config).renderCard(
        writer,
        "corex " ++ COREX_VERSION,
        &.{
            "Build reliable software effortlessly at systems-level speed",
            "Usage: corex [OPTIONS] <COMMAND> [ARGS]…",
        },
    );
    try writer.writeByte('\n');

    // [2] Render canonical `SUBCOMMANDS` section:
    try style_config.writeStyled(writer, .bold, "Commands:");
    try writer.writeByte('\n');
    for (SUBCOMMANDS) |descriptor| {
        try writer.writeAll("  ");
        try style_config.writeStyled(writer, .dim, Glyphs.POINTER_SOLID);
        try writer.writeByte(' ');
        try style_config.writeStyled(writer, .bold, descriptor.name);
        if (descriptor.name.len < 10) {
            try writer.splatByteAll(' ', 10 - descriptor.name.len);
        } else {
            try writer.writeByte(' ');
        }
        try writer.writeAll(descriptor.summary);
        try writer.writeByte('\n');
    }
    try writer.writeByte('\n');

    // [3] Render canonical `GLOBAL_FLAGS` section:
    try style_config.writeStyled(writer, .bold, "Global Options:");
    try writer.writeByte('\n');
    for (GLOBAL_FLAGS) |flag_desc| {
        var flag_label_buf: [64]u8 = undefined;
        var label_writer = std.Io.Writer.fixed(&flag_label_buf);
        if (flag_desc.short_flag) |short_str| {
            label_writer.print("{s}, {s}", .{ short_str, flag_desc.long_flag }) catch unreachable;
        } else {
            label_writer.print("    {s}", .{flag_desc.long_flag}) catch unreachable;
        }
        if (flag_desc.value_suffix) |suffix_str| {
            label_writer.writeAll(suffix_str) catch unreachable;
        }
        const formatted_flag = label_writer.buffered();

        try writer.writeAll("  ");
        try style_config.writeStyled(writer, .bold, formatted_flag);
        if (formatted_flag.len < 20) {
            try writer.splatByteAll(' ', 20 - formatted_flag.len);
        } else {
            try writer.writeByte(' ');
        }
        try writer.writeAll(flag_desc.summary);
        try writer.writeByte('\n');
    }
}

/// Renders subcommand-specific `--help` (`corex <subcommand> --help`) including scoped options.
pub fn renderSubcommandHelp(
    writer: *std.Io.Writer,
    style_config: StyleConfig,
    subcommand: SubcommandId,
) std.Io.Writer.Error!void {
    const sub_desc = subcommand.asDescriptor();
    var title_buf: [64]u8 = undefined;
    var title_writer = std.Io.Writer.fixed(&title_buf);
    title_writer.print("corex {s}", .{sub_desc.name}) catch unreachable;

    var usage_buf: [128]u8 = undefined;
    var usage_writer = std.Io.Writer.fixed(&usage_buf);
    if (sub_desc.usage.len > 0) {
        usage_writer.print("Usage: corex {s} [OPTIONS] {s}", .{ sub_desc.name, sub_desc.usage }) catch unreachable;
    } else {
        usage_writer.print("Usage: corex {s} [OPTIONS]", .{sub_desc.name}) catch unreachable;
    }

    try CardRenderer.init(style_config).renderCard(
        writer,
        title_writer.buffered(),
        &.{ sub_desc.summary, usage_writer.buffered() },
    );
    try writer.writeByte('\n');

    if (isCompileSubcommand(subcommand)) {
        try style_config.writeStyled(writer, .bold, "Compile Options:");
        try writer.writeByte('\n');
        for (COMPILE_FLAGS) |comp_desc| {
            var flag_buf: [64]u8 = undefined;
            var flag_writer = std.Io.Writer.fixed(&flag_buf);
            flag_writer.print("    {s}", .{comp_desc.long_flag}) catch unreachable;
            if (comp_desc.value_suffix) |suffix_str| {
                flag_writer.writeAll(suffix_str) catch unreachable;
            }
            const formatted_flag = flag_writer.buffered();
            try writer.writeAll("  ");
            try style_config.writeStyled(writer, .bold, formatted_flag);
            if (formatted_flag.len < 28) {
                try writer.splatByteAll(' ', 28 - formatted_flag.len);
            } else {
                try writer.writeByte(' ');
            }
            try writer.writeAll(comp_desc.summary);
            try writer.writeByte('\n');
        }
        try writer.writeByte('\n');
    } else if (subcommand == .fmt) {
        try style_config.writeStyled(writer, .bold, "Format Options:");
        try writer.writeByte('\n');
        for (FMT_FLAGS) |fmt_desc| {
            var flag_buf: [64]u8 = undefined;
            var flag_writer = std.Io.Writer.fixed(&flag_buf);
            flag_writer.print("    {s}", .{fmt_desc.long_flag}) catch unreachable;
            const formatted_flag = flag_writer.buffered();
            try writer.writeAll("  ");
            try style_config.writeStyled(writer, .bold, formatted_flag);
            if (formatted_flag.len < 20) {
                try writer.splatByteAll(' ', 20 - formatted_flag.len);
            } else {
                try writer.writeByte(' ');
            }
            try writer.writeAll(fmt_desc.summary);
            try writer.writeByte('\n');
        }
        try writer.writeByte('\n');
    }

    try style_config.writeStyled(writer, .bold, "Global Options:");
    try writer.writeByte('\n');
    for (GLOBAL_FLAGS) |flag_desc| {
        var flag_label_buf: [64]u8 = undefined;
        var label_writer = std.Io.Writer.fixed(&flag_label_buf);
        if (flag_desc.short_flag) |short_str| {
            label_writer.print("{s}, {s}", .{ short_str, flag_desc.long_flag }) catch unreachable;
        } else {
            label_writer.print("    {s}", .{flag_desc.long_flag}) catch unreachable;
        }
        if (flag_desc.value_suffix) |suffix_str| {
            label_writer.writeAll(suffix_str) catch unreachable;
        }
        const formatted_flag = label_writer.buffered();

        try writer.writeAll("  ");
        try style_config.writeStyled(writer, .bold, formatted_flag);
        if (formatted_flag.len < 20) {
            try writer.splatByteAll(' ', 20 - formatted_flag.len);
        } else {
            try writer.writeByte(' ');
        }
        try writer.writeAll(flag_desc.summary);
        try writer.writeByte('\n');
    }
}

/// Renders the canonical `corex --version` line into `writer`.
pub fn renderVersion(writer: *std.Io.Writer) std.Io.Writer.Error!void {
    try writer.writeAll("corex " ++ COREX_VERSION ++ " (stage0 zig 0.17.0)\n");
}

/// Executes the full Stage 0 CLI lifecycle (`parseArgs` -> dispatch -> diagnostic rendering) and returns the exit code.
pub fn runCli(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    raw_args: []const []const u8,
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
) !u8 {
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    var interner = try mem.StringInterner.init(allocator);
    defer interner.deinit();

    var source_map = vfs.VfsSourceMap.init(allocator, &interner);
    defer source_map.deinit(io);

    const parsed_cmd = try parseArgs(raw_args, &sink);
    const stdout_style: StyleConfig = .{
        .is_color_enabled = style.isColorEnabled(parsed_cmd.color_mode, io, std.Io.File.stdout(), environ_map),
    };
    const stderr_style: StyleConfig = .{
        .is_color_enabled = style.isColorEnabled(parsed_cmd.color_mode, io, std.Io.File.stderr(), environ_map),
    };

    switch (parsed_cmd.action) {
        .invalid => {
            try DiagnosticRenderer.init(&source_map, &interner, stderr_style).renderAll(stderr_writer, &sink);
            return 1;
        },
        .show_help => |sub_opt| {
            if (sub_opt) |sub_id| {
                try renderSubcommandHelp(stdout_writer, stdout_style, sub_id);
            } else {
                try renderHelp(stdout_writer, stdout_style);
            }
            return 0;
        },
        .show_version => {
            try renderVersion(stdout_writer);
            return 0;
        },
        .execute_subcommand => |exec_info| {
            if (exec_info.subcommand == .bench) {
                try bench_harness.runDefaultPhase0Suite(allocator, io, stdout_writer, stdout_style);
                return 0;
            }
            if (exec_info.subcommand == .fmt) {
                var has_unformatted_or_error = false;
                for (exec_info.positional_args) |file_arg| {
                    const raw_source = std.Io.Dir.cwd().readFileAlloc(
                        io,
                        file_arg,
                        allocator,
                        .limited(vfs.MAX_SOURCE_FILE_BYTES),
                    ) catch {
                        try sink.emit(.{
                            .code = .e0004_source_file_io_error,
                            .severity = .err,
                            .message = try std.fmt.allocPrint(
                                sink.arena.asAllocator(),
                                "failed to open or read source file `{s}`",
                                .{file_arg},
                            ),
                        });
                        continue;
                    };
                    defer allocator.free(raw_source);

                    const file_id = try source_map.setOverlay(file_arg, raw_source, .root);
                    _ = try source_map.getLineIndex(file_id);

                    var fmt_res = try fmt_engine.formatSourceWithOptions(
                        allocator,
                        raw_source,
                        file_id,
                        .{ .is_fix_mode = exec_info.is_fix_mode },
                    );
                    defer fmt_res.deinit(allocator);

                    if (fmt_res.has_syntax_errors) {
                        has_unformatted_or_error = true;
                        var err_msg_buf: [512]u8 = undefined;
                        const err_msg = std.fmt.bufPrint(
                            &err_msg_buf,
                            "syntax errors in {s}",
                            .{file_arg},
                        ) catch file_arg;
                        try stderr_style.writeStatusHeader(
                            stderr_writer,
                            .err,
                            Glyphs.FAILURE,
                            "fmt",
                            err_msg,
                        );
                        try stderr_writer.writeByte('\n');
                        continue;
                    }

                    if (fmt_res.is_changed) {
                        if (exec_info.is_check_only) {
                            has_unformatted_or_error = true;
                            try stderr_style.writeStatusHeader(
                                stderr_writer,
                                .err,
                                Glyphs.FAILURE,
                                "fmt --check",
                                file_arg,
                            );
                            try stderr_writer.writeByte('\n');
                        } else {
                            std.Io.Dir.cwd().writeFile(io, .{
                                .sub_path = file_arg,
                                .data = fmt_res.formatted_text,
                            }) catch {
                                try sink.emit(.{
                                    .code = .e0004_source_file_io_error,
                                    .severity = .err,
                                    .message = try std.fmt.allocPrint(
                                        sink.arena.asAllocator(),
                                        "failed to write formatted source file `{s}`",
                                        .{file_arg},
                                    ),
                                });
                                continue;
                            };
                        }
                    }
                }
                if (sink.hasErrors()) {
                    try DiagnosticRenderer.init(&source_map, &interner, stderr_style).renderAll(
                        stderr_writer,
                        &sink,
                    );
                    return 1;
                }
                if (has_unformatted_or_error) {
                    return 1;
                }
                try stdout_style.writeStatusHeader(
                    stdout_writer,
                    .success,
                    Glyphs.SUCCESS,
                    exec_info.subcommand.asName(),
                    "CoreX source files formatted canonically",
                );
                try stdout_writer.writeByte('\n');
                return 0;
            }
            var cx_file_ids: std.ArrayListUnmanaged(mem.FileId) = .empty;
            defer cx_file_ids.deinit(allocator);
            var embed_sandbox_root: []const u8 = ".";

            for (exec_info.positional_args) |file_arg| {
                const file_id = source_map.resolveOrCreatePath(io, file_arg, .root) catch {
                    try sink.emit(.{
                        .code = .e0004_source_file_io_error,
                        .severity = .err,
                        .message = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "failed to open or read source file `{s}`",
                            .{file_arg},
                        ),
                    });
                    continue;
                };
                _ = try source_map.getLineIndex(file_id);
                if (std.mem.endsWith(u8, file_arg, ".cx")) {
                    if (cx_file_ids.items.len == 0) {
                        embed_sandbox_root = std.fs.path.dirname(file_arg) orelse ".";
                    }
                    try cx_file_ids.append(allocator, file_id);
                }
            }
            if (sink.hasErrors()) {
                try DiagnosticRenderer.init(&source_map, &interner, stderr_style).renderAll(stderr_writer, &sink);
                return 1;
            }
            if (exec_info.subcommand == .check and cx_file_ids.items.len > 0) {
                var db = try query_db.CompilerDb.init(allocator);
                defer db.deinit();
                db.setSastStrict(exec_info.is_sast_strict);
                db.setComptimeStepLimit(exec_info.comptime_step_limit);
                db.setEmbedSandbox(embed_sandbox_root, null);
                db.setEmbedIo(io);

                for (cx_file_ids.items) |cx_fid| {
                    const file_bytes = source_map.getFileSource(cx_fid) orelse "";
                    _ = try db.setInput(cx_fid, file_bytes, .low);
                }

                const diag_renderer = DiagnosticRenderer.init(&source_map, &interner, stderr_style);
                var has_check_errors = false;

                for (cx_file_ids.items) |cx_fid| {
                    const parsed_art = try db.parseCst(cx_fid);
                    if (parsed_art.diagnostics.diagnostics.items.len > 0) {
                        try diag_renderer.renderAll(stderr_writer, &parsed_art.diagnostics);
                        if (parsed_art.diagnostics.hasErrors()) has_check_errors = true;
                    }

                    const sig_art = try db.resolveSignatures(cx_fid);
                    if (db.getSignatureDiagnostics(cx_fid)) |sig_sink| {
                        if (sig_sink.diagnostics.items.len > 0) {
                            try diag_renderer.renderAll(stderr_writer, sig_sink);
                        }
                        if (sig_sink.hasErrors()) has_check_errors = true;
                    }
                    if (sig_art.error_count > 0) has_check_errors = true;

                    const item_tree = try db.extractItemTree(cx_fid);
                    for (item_tree.entries) |entry| {
                        const typed_art = try db.typecheckBody(entry.def_id);
                        if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                            if (body_sink.diagnostics.items.len > 0) {
                                try diag_renderer.renderAll(stderr_writer, body_sink);
                            }
                            if (body_sink.hasErrors()) has_check_errors = true;
                        }
                        if (typed_art.error_count > 0) has_check_errors = true;

                        const sast_art = try db.verifySastMir(entry.def_id);
                        if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                            if (sast_sink.diagnostics.items.len > 0) {
                                try diag_renderer.renderAll(stderr_writer, sast_sink);
                            }
                            if (sast_sink.hasErrors()) has_check_errors = true;
                        }
                        if (!sast_art.is_verified_sound) has_check_errors = true;

                        if (!has_check_errors and
                            (entry.kind == .const_decl or entry.kind == .extern_block))
                        {
                            const ct_art_opt: ?query_db.ComptimeEvalArtifact =
                                db.evalComptimeDef(entry.def_id) catch |ct_err| switch (ct_err) {
                                    error.OutOfMemory => return error.OutOfMemory,
                                    else => blk: {
                                        has_check_errors = true;
                                        break :blk null;
                                    },
                                };
                            if (db.getComptimeDiagnostics(entry.def_id)) |ct_sink| {
                                if (ct_sink.diagnostics.items.len > 0) {
                                    try diag_renderer.renderAll(stderr_writer, ct_sink);
                                }
                                if (ct_sink.hasErrors()) has_check_errors = true;
                            }
                            if (ct_art_opt) |ct_art| {
                                if (ct_art.has_errors) has_check_errors = true;
                            }
                        }
                    }
                }

                if (has_check_errors) {
                    return 1;
                }
            }
            try stdout_style.writeStatusHeader(
                stdout_writer,
                .success,
                Glyphs.SUCCESS,
                exec_info.subcommand.asName(),
                "Phase 0 bootstrap foundation verified",
            );
            try stdout_writer.writeByte('\n');
            return 0;
        },
    }
}

comptime {
    for (SUBCOMMANDS, 0..) |descriptor, i| {
        std.debug.assert(@backingInt(descriptor.id) == i);
    }
    for (GLOBAL_FLAGS, 0..) |flag_desc, i| {
        std.debug.assert(@backingInt(flag_desc.id) == i);
    }
    for (FMT_FLAGS, 0..) |fmt_desc, i| {
        std.debug.assert(@backingInt(fmt_desc.id) == i);
    }
    for (COMPILE_FLAGS, 0..) |comp_desc, i| {
        std.debug.assert(@backingInt(comp_desc.id) == i);
    }
}

test "test_cli_router_subcommands_flags_and_typo_suggestions" {
    try std.testing.expectEqualStrings("build", suggestSubcommand("biuld").?);
    try std.testing.expectEqualStrings("check", suggestSubcommand("chck").?);
    try std.testing.expectEqualStrings("--help", suggestGlobalFlag("--hlp").?);
    try std.testing.expectEqualStrings("--version", suggestGlobalFlag("--verison").?);

    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    const parsed = try parseArgs(&.{ "--color=never", "check", "main.cx" }, &sink);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(ColorMode.never, parsed.color_mode);
    try std.testing.expectEqual(SubcommandId.check, parsed.action.execute_subcommand.subcommand);
    try std.testing.expectEqual(@as(usize, 1), parsed.action.execute_subcommand.positional_args.len);

    // `--check` and `--fix` are valid on `fmt`, and typo suggestions include `FMT_FLAGS`:
    try std.testing.expectEqualStrings("--check", suggestFlagForSubcommand("--chck", .fmt).?);
    try std.testing.expectEqualStrings("--fix", suggestFlagForSubcommand("--fx", .fmt).?);

    const parsed_fmt = try parseArgs(&.{ "fmt", "--check", "--fix" }, &sink);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(parsed_fmt.is_check_only);
    try std.testing.expect(parsed_fmt.is_fix_mode);

    // Passing `--check` to a non-`fmt` subcommand emits `E0001`:
    var err_sink = DiagnosticSink.init(std.testing.allocator);
    defer err_sink.deinit();
    const invalid_cmd = try parseArgs(&.{ "build", "--check" }, &err_sink);
    try std.testing.expect(err_sink.hasErrors());
    try std.testing.expectEqual(CommandAction.invalid, invalid_cmd.action);
}

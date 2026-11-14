//! CLI Command Router, Dynamic Metadata Registry & Typo Suggestion Engine
//!
//! Defines the canonical `SUBCOMMANDS` (`build`, `run`, `check`, `test`, `fmt`, `upgrade`, `lsp`, `bench`)
//! and `GLOBAL_FLAGS` (`-h`/`--help`, `-V`/`--version`, `--color=<when>`) metadata tables.
//!
//! Parses command-line arguments in a single pass, emits `E0001`/`E0002` diagnostics with stack-allocated
//! Levenshtein typo suggestions (`help: did you mean \`…\`?`), and renders the monochrome help menu.

const std = @import("std");
const builtin = @import("builtin");
const mem = @import("../mem_foundation.zig");
const vfs = @import("../vfs_sourcemap.zig");
const style = @import("style.zig");
const box_draw = @import("box_draw.zig");
const diag = @import("../diag/diagnostic.zig");
const renderer = @import("../diag/renderer.zig");
const bench_harness = @import("../bench/harness.zig");
const fmt_engine = @import("../fmt_engine.zig");
const query_db = @import("../query_db.zig");
const codegen_abi = @import("../codegen_abi.zig");
const diff_oracle = @import("../diff_oracle.zig");

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

/// Codegen backend family selectable via `--ofmt=<c|llvm>` / `-ofmt=<c|llvm>`.
pub const OutputFormat = enum(u8) {
    /// Tier A deterministic ISO C99 backend (`-ofmt=c`).
    c = 0,
    /// Tier B LLVM 20–23 backend (`-ofmt=llvm`, default).
    llvm = 1,

    /// Parses `"c"` or `"llvm"` into an `OutputFormat`.
    pub fn parse(raw_format: []const u8) ?OutputFormat {
        if (std.mem.eql(u8, raw_format, "c")) return .c;
        if (std.mem.eql(u8, raw_format, "llvm")) return .llvm;
        return null;
    }
};

/// Subcommand-specific CLI option identifiers for compilation/verification subcommands (`COMPILE_FLAGS`).
pub const CompileFlagId = enum(u8) {
    /// `--comptime-limit=<steps>` – configure `MirVm` compile-time execution step budget (`0`).
    comptime_limit = 0,
    /// `--dev` – compile in fast development mode (`1`).
    dev = 1,
    /// `--diff-backends` – run 4-tier `MirVm` / C99 / LLVM differential oracle (`2`).
    diff_backends = 2,
    /// `--emit-c` – emit deterministic ISO C99 source text (`3`).
    emit_c = 3,
    /// `--emit-llvm` – emit deterministic LLVM 20–23 `.ll` IR text (`4`).
    emit_llvm = 4,
    /// `--fuzz` – instrument output with `SanitizerCoverage` edge counters (`5`).
    fuzz = 5,
    /// `--ofmt=<c|llvm>` – select Tier A (`c`) or Tier B (`llvm`) codegen backend (`6`).
    ofmt = 6,
    /// `--output=<path>` – write compiled artifact to `<path>` (`7`).
    output = 7,
    /// `--release` – compile in production release mode (`8`).
    release = 8,
    /// `--sast-strict` – emit `W0314` warnings on unproven bounds checks (`9`).
    sast_strict = 9,
    /// `--target=<triple>` – select cross-compilation target triple (`10`).
    target = 10,
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
        /// Number of `positional_args` preceding `--` (remaining entries are `run_args`).
        pre_dash_arg_count: usize = 0,
        /// Arguments forwarded after `--` to child binary during `corex run`.
        run_args: []const []const u8 = &.{},
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
        /// Whether `--diff-backends` 4-tier differential verification was enabled.
        is_diff_backends: bool = false,
        /// Whether `--emit-c` textual C99 emission was requested.
        is_emit_c: bool = false,
        /// Whether `--emit-llvm` textual LLVM `.ll` IR emission was requested.
        is_emit_llvm: bool = false,
        /// Whether `--fuzz` `SanitizerCoverage` instrumentation was requested.
        is_fuzz_enabled: bool = false,
        /// Selected codegen backend family (`llvm` by default, or `c` with `-ofmt=c`).
        output_format: OutputFormat = .llvm,
        /// Optional explicit output artifact path (`-o <path>` / `--output=<path>`).
        output_path: ?[]const u8 = null,
        /// Optional explicit target specification (`--target=<triple>`).
        target_spec: ?codegen_abi.TargetSpec = null,
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
    /// Whether `--diff-backends` was passed on `corex test`.
    is_diff_backends: bool = false,
    /// Whether `--emit-c` was passed on a compile subcommand.
    is_emit_c: bool = false,
    /// Whether `--emit-llvm` was passed on a compile subcommand.
    is_emit_llvm: bool = false,
    /// Whether `--fuzz` was passed on a compile subcommand.
    is_fuzz_enabled: bool = false,
    /// Selected codegen backend family (`llvm` by default).
    output_format: OutputFormat = .llvm,
    /// Optional explicit output path (`-o` / `--output`).
    output_path: ?[]const u8 = null,
    /// Optional explicit target specification (`--target`).
    target_spec: ?codegen_abi.TargetSpec = null,
    /// Arguments passed after `--` (forwarded to the child executable on `corex run`).
    run_args: []const []const u8 = &.{},
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
            "Set maximum compile-time VM step budget (default: {d})",
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
        .id = .diff_backends,
        .long_flag = "--diff-backends",
        .value_suffix = null,
        .summary = "Verify 4-tier parity across MirVm, C99, and LLVM backends",
    },
    .{
        .id = .emit_c,
        .long_flag = "--emit-c",
        .value_suffix = null,
        .summary = "Emit deterministic ISO C99 source text without linking",
    },
    .{
        .id = .emit_llvm,
        .long_flag = "--emit-llvm",
        .value_suffix = null,
        .summary = "Emit deterministic LLVM 20–23 IR text without linking",
    },
    .{
        .id = .fuzz,
        .long_flag = "--fuzz",
        .value_suffix = null,
        .summary = "Instrument compiled output with SanitizerCoverage counters",
    },
    .{
        .id = .ofmt,
        .long_flag = "--ofmt",
        .value_suffix = "=<c|llvm>",
        .summary = "Select Tier A C99 (`c`) or Tier B LLVM (`llvm`) backend",
    },
    .{
        .id = .output,
        .long_flag = "--output",
        .value_suffix = "=<path>",
        .summary = "Write compiled binary, object, or IR artifact to `<path>`",
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
        .summary = "Emit W0314 warnings when bounds checks cannot be elided",
    },
    .{
        .id = .target,
        .long_flag = "--target",
        .value_suffix = "=<triple>",
        .summary = "Cross-compile for target triple (e.g., `wasm32-wasi`)",
    },
};

/// Maximum recursive `mod <name>;` discovery depth across workspace module trees.
const MAX_MODULE_DISCOVERY_DEPTH: u32 = 64;
/// $O(1)$ lookup table of package/directory hub basenames whose child modules live directly in `parent_dir`.
const HUB_MODULE_BASENAME_SET = std.StaticStringMap(void).initComptime(.{
    .{ "lib.cx", {} },
    .{ "main.cx", {} },
    .{ "mod.cx", {} },
    .{ "root.cx", {} },
});
/// Monotonic atomic counter preventing scratch-path collisions across concurrent `corex run` calls.
var next_run_scratch_seq = std.atomic.Value(u32).init(1);

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

/// Emits an `E0001` diagnostic when both `--emit-c` and `--emit-llvm` are passed together.
fn emitConflictingEmitFlagsDiagnostic(sink: *DiagnosticSink) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = "conflicting CLI emission flags `--emit-c` and `--emit-llvm`",
        .notes = &.{"help: pass either `--emit-c` or `--emit-llvm`, not both"},
    });
}

/// Emits an `E0001` diagnostic when `--ofmt` / `-ofmt` receives an unsupported backend name.
fn emitInvalidOutputFormatDiagnostic(sink: *DiagnosticSink, raw_fmt_val: []const u8) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "invalid backend format `{s}` for `--ofmt`",
            .{raw_fmt_val},
        ),
        .notes = &.{"help: valid backend formats for `--ofmt` / `-ofmt` are `c` or `llvm`"},
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

/// Orders UTF-8 relative paths ascending for deterministic directory traversal.
fn isLessThanUtf8Path(_: void, lhs_path: []u8, rhs_path: []u8) bool {
    return std.mem.order(u8, lhs_path, rhs_path) == .lt;
}

/// Appends `.cx` file paths inside `dir_path` (sorted lexicographically) into `out_paths`, or returns `false` if not a dir.
fn collectDirectoryCxPaths(
    allocator: std.mem.Allocator,
    io: std.Io,
    dir_path: []const u8,
    out_paths: *std.ArrayListUnmanaged([]u8),
) !bool {
    var opened_dir = std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true }) catch return false;
    defer opened_dir.close(io);

    const start_idx = out_paths.items.len;
    var walker = try opened_dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next(io)) |entry| {
        if (entry.kind != .file or !std.mem.endsWith(u8, entry.path, ".cx")) continue;
        const joined_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ dir_path, entry.path });
        errdefer allocator.free(joined_path);
        for (joined_path) |*ch_ptr| {
            if (ch_ptr.* == '\\') ch_ptr.* = '/';
        }
        try out_paths.append(allocator, joined_path);
    }

    std.mem.sort([]u8, out_paths.items[start_idx..], {}, isLessThanUtf8Path);
    return true;
}

/// Recursively discovers and binds external `mod <name>;` `.cx` files reachable from `parent_fid`.
fn discoverExternalSubmodulesRecursive(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs.VfsSourceMap,
    db: *query_db.CompilerDb,
    parent_fid: mem.FileId,
    parent_path: []const u8,
    durability: query_db.Durability,
    pkg_id: vfs.PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    has_core_mention_out: *bool,
    depth: u32,
) !void {
    if (depth >= MAX_MODULE_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return;
    try visited_fids.put(allocator, parent_fid.asInt(), {});

    _ = source_map.getLineIndex(parent_fid) catch {};
    const parent_src = source_map.getFileSource(parent_fid) orelse "";
    if (!has_core_mention_out.* and std.mem.indexOf(u8, parent_src, "core") != null) {
        has_core_mention_out.* = true;
    }
    _ = try db.setInput(parent_fid, parent_src, durability);

    var ext_mod_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer ext_mod_names.deinit(allocator);
    {
        const parsed_art = try db.parseCst(parent_fid);
        const item_entries = (try db.extractItemTree(parent_fid)).entries;
        for (item_entries) |entry| {
            if (entry.kind != .mod_decl or entry.name_text.len == 0) continue;
            if (!entry.ast_node.isNone() and
                parsed_art.ast_arena.getNode(entry.ast_node).rhs.tag == .extra)
            {
                continue;
            }
            try ext_mod_names.append(allocator, entry.name_text);
        }
    }

    const parent_dir = std.fs.path.dirname(parent_path) orelse ".";
    const parent_base = std.fs.path.basename(parent_path);
    const parent_stem = std.fs.path.stem(parent_path);
    const is_hub_file = HUB_MODULE_BASENAME_SET.has(parent_base);

    for (ext_mod_names.items) |mod_name| {
        var cand_paths: [4]?[]u8 = @splat(null);
        defer {
            for (cand_paths) |maybe_p| {
                if (maybe_p) |owned_p| allocator.free(owned_p);
            }
        }
        var cand_len: usize = 0;
        if (!is_hub_file) {
            cand_paths[cand_len] = try std.fmt.allocPrint(
                allocator,
                "{s}/{s}/{s}.cx",
                .{ parent_dir, parent_stem, mod_name },
            );
            cand_len += 1;
            cand_paths[cand_len] = try std.fmt.allocPrint(
                allocator,
                "{s}/{s}/{s}/mod.cx",
                .{ parent_dir, parent_stem, mod_name },
            );
            cand_len += 1;
        }
        cand_paths[cand_len] = try std.fmt.allocPrint(
            allocator,
            "{s}/{s}.cx",
            .{ parent_dir, mod_name },
        );
        cand_len += 1;
        cand_paths[cand_len] = try std.fmt.allocPrint(
            allocator,
            "{s}/{s}/mod.cx",
            .{ parent_dir, mod_name },
        );
        cand_len += 1;

        var idx: usize = 0;
        while (idx < cand_len) : (idx += 1) {
            const cand_str = cand_paths[idx].?;
            if (source_map.resolveOrCreatePath(io, cand_str, pkg_id)) |child_fid| {
                _ = try source_map.getLineIndex(child_fid);
                try db.bindExternalModule(parent_fid, mod_name, child_fid);
                try discoverExternalSubmodulesRecursive(
                    allocator,
                    io,
                    source_map,
                    db,
                    child_fid,
                    cand_str,
                    durability,
                    pkg_id,
                    visited_fids,
                    has_core_mention_out,
                    depth + 1,
                );
                break;
            } else |_| {}
        }
    }
}

/// Registers `core/root.cx` (and its `core/` submodule tree) on `db` when available on disk.
fn registerWorkspaceCoreModuleIfNeeded(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs.VfsSourceMap,
    db: *query_db.CompilerDb,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    const core_root_path = "core/root.cx";
    const core_fid = source_map.resolveOrCreatePath(io, core_root_path, .std_core) catch return;
    _ = try source_map.getLineIndex(core_fid);
    var has_dummy_core_mention = true;
    try discoverExternalSubmodulesRecursive(
        allocator,
        io,
        source_map,
        db,
        core_fid,
        core_root_path,
        .high,
        .std_core,
        visited_fids,
        &has_dummy_core_mention,
        0,
    );
    try db.registerRootModule("core", core_fid);
}

/// Returns `true` if `file_id` declares a top-level `fn main` entrypoint.
fn fileDeclaresMainEntrypoint(db: *query_db.CompilerDb, file_id: mem.FileId) !bool {
    const item_tree = try db.extractItemTree(file_id);
    for (item_tree.entries) |entry| {
        if (entry.kind == .fn_decl and std.mem.eql(u8, entry.name_text, "main")) {
            return true;
        }
    }
    return false;
}

/// Verifies all reachable module files from `root_files` and renders any front-end/SAST/comptime diagnostics.
fn verifyAndRenderModuleDiagnostics(
    allocator: std.mem.Allocator,
    db: *query_db.CompilerDb,
    root_files: []const mem.FileId,
    diag_renderer: DiagnosticRenderer,
    stderr_writer: *std.Io.Writer,
) !bool {
    var reachable_files: std.ArrayListUnmanaged(mem.FileId) = .empty;
    defer reachable_files.deinit(allocator);
    if (root_files.len > 0) {
        try db.collectReachableModuleFiles(root_files[0], root_files[1..], &reachable_files);
    }

    var has_errors = false;
    for (reachable_files.items) |mod_fid| {
        const parsed_art = try db.parseCst(mod_fid);
        if (parsed_art.diagnostics.diagnostics.items.len > 0) {
            try diag_renderer.renderAll(stderr_writer, &parsed_art.diagnostics);
            if (parsed_art.diagnostics.hasErrors()) has_errors = true;
        }

        const sig_err_count = (try db.resolveSignatures(mod_fid)).error_count;
        if (db.getSignatureDiagnostics(mod_fid)) |sig_sink| {
            if (sig_sink.diagnostics.items.len > 0) {
                try diag_renderer.renderAll(stderr_writer, sig_sink);
            }
            if (sig_sink.hasErrors()) has_errors = true;
        }
        if (sig_err_count > 0) has_errors = true;

        const item_entries = (try db.extractItemTree(mod_fid)).entries;
        for (item_entries) |entry| {
            const body_err_count = (try db.typecheckBody(entry.def_id)).error_count;
            if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                if (body_sink.diagnostics.items.len > 0) {
                    try diag_renderer.renderAll(stderr_writer, body_sink);
                }
                if (body_sink.hasErrors()) has_errors = true;
            }
            if (body_err_count > 0) has_errors = true;

            const is_verified_sound = (try db.verifySastMir(entry.def_id)).is_verified_sound;
            if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                if (sast_sink.diagnostics.items.len > 0) {
                    try diag_renderer.renderAll(stderr_writer, sast_sink);
                }
                if (sast_sink.hasErrors()) has_errors = true;
            }
            if (!is_verified_sound) has_errors = true;

            if (!has_errors and (entry.kind == .const_decl or entry.kind == .extern_block)) {
                const ct_art_opt: ?query_db.ComptimeEvalArtifact =
                    db.evalComptimeDef(entry.def_id) catch |ct_err| switch (ct_err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => blk: {
                            has_errors = true;
                            break :blk null;
                        },
                    };
                if (db.getComptimeDiagnostics(entry.def_id)) |ct_sink| {
                    if (ct_sink.diagnostics.items.len > 0) {
                        try diag_renderer.renderAll(stderr_writer, ct_sink);
                    }
                    if (ct_sink.hasErrors()) has_errors = true;
                }
                if (ct_art_opt) |ct_art| {
                    if (ct_art.has_errors) has_errors = true;
                }
            }
        }
    }
    return has_errors;
}

/// Builds a `CodegenBackend` matching `(output_format, target_spec, is_release_mode, is_fuzz_enabled)`.
fn buildConfiguredBackend(
    output_format: OutputFormat,
    target_spec: codegen_abi.TargetSpec,
    is_release_mode: bool,
    is_fuzz_enabled: bool,
) codegen_abi.CodegenBackend {
    return switch (output_format) {
        .c => .{
            .tier_a_c99 = .{
                .target = target_spec,
                .is_release_mode = is_release_mode,
                .is_fuzz_instrumented = is_fuzz_enabled,
                .has_line_directives = true,
            },
        },
        .llvm => .{
            .tier_b_llvm = .{
                .target = target_spec,
                .opt_level = if (is_release_mode) .release_fast_o2 else .debug_o0,
                .is_release_mode = is_release_mode,
                .is_fuzz_instrumented = is_fuzz_enabled,
            },
        },
    };
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

/// Parses CLI arguments (excluding `argv[0]`), emitting `E0001`/`E0002`/`E0003`/`E0006` into `sink` on error.
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
    var is_diff_backends = false;
    var is_emit_c = false;
    var is_emit_llvm = false;
    var is_fuzz_enabled = false;
    var output_format: OutputFormat = .llvm;
    var output_path: ?[]const u8 = null;
    var target_spec: ?codegen_abi.TargetSpec = null;
    var selected_subcommand: ?SubcommandId = null;
    var positional_list: std.ArrayList([]const u8) = .empty;
    var is_after_double_dash = false;
    var pre_dash_count: ?usize = null;

    var arg_idx: usize = 0;
    while (arg_idx < raw_args.len) : (arg_idx += 1) {
        const arg_text = raw_args[arg_idx];
        if (!is_after_double_dash and std.mem.eql(u8, arg_text, "--")) {
            is_after_double_dash = true;
            pre_dash_count = positional_list.items.len;
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
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--diff-backends")) {
                is_diff_backends = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--emit-c")) {
                if (is_emit_llvm) {
                    try emitConflictingEmitFlagsDiagnostic(sink);
                }
                is_emit_c = true;
                output_format = .c;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--emit-llvm")) {
                if (is_emit_c) {
                    try emitConflictingEmitFlagsDiagnostic(sink);
                }
                is_emit_llvm = true;
                output_format = .llvm;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--fuzz")) {
                is_fuzz_enabled = true;
            } else if (is_compile_sub and (std.mem.startsWith(u8, arg_text, "--ofmt=") or
                std.mem.startsWith(u8, arg_text, "-ofmt=")))
            {
                const eq_pos = std.mem.indexOfScalar(u8, arg_text, '=').?;
                const raw_fmt = arg_text[eq_pos + 1 ..];
                if (OutputFormat.parse(raw_fmt)) |parsed_fmt| {
                    output_format = parsed_fmt;
                } else {
                    try emitInvalidOutputFormatDiagnostic(sink, raw_fmt);
                }
            } else if (is_compile_sub and (std.mem.eql(u8, arg_text, "--ofmt") or
                std.mem.eql(u8, arg_text, "-ofmt")))
            {
                if (arg_idx + 1 >= raw_args.len) {
                    try sink.emit(.{
                        .code = .e0003_missing_cli_argument,
                        .severity = .err,
                        .message = "missing backend format for `--ofmt`; expected `c` or `llvm`",
                        .notes = &.{"help: pass `--ofmt=c` (`-ofmt=c`) or `--ofmt=llvm` (`-ofmt=llvm`)"},
                    });
                } else {
                    arg_idx += 1;
                    const next_fmt = raw_args[arg_idx];
                    if (OutputFormat.parse(next_fmt)) |parsed_fmt| {
                        output_format = parsed_fmt;
                    } else {
                        try emitInvalidOutputFormatDiagnostic(sink, next_fmt);
                    }
                }
            } else if (is_compile_sub and (std.mem.startsWith(u8, arg_text, "--output=") or
                std.mem.startsWith(u8, arg_text, "-o=")))
            {
                const eq_pos = std.mem.indexOfScalar(u8, arg_text, '=').?;
                const raw_out = arg_text[eq_pos + 1 ..];
                if (raw_out.len == 0) {
                    try sink.emit(.{
                        .code = .e0003_missing_cli_argument,
                        .severity = .err,
                        .message = "missing file path for `--output` / `-o`",
                        .notes = &.{"help: pass `--output=<path>` or `-o <path>`"},
                    });
                } else {
                    output_path = try sink.arena.asAllocator().dupe(u8, raw_out);
                }
            } else if (is_compile_sub and (std.mem.eql(u8, arg_text, "--output") or
                std.mem.eql(u8, arg_text, "-o")))
            {
                if (arg_idx + 1 >= raw_args.len or raw_args[arg_idx + 1].len == 0) {
                    try sink.emit(.{
                        .code = .e0003_missing_cli_argument,
                        .severity = .err,
                        .message = "missing file path for `--output` / `-o`",
                        .notes = &.{"help: pass `--output=<path>` or `-o <path>`"},
                    });
                } else {
                    arg_idx += 1;
                    output_path = try sink.arena.asAllocator().dupe(u8, raw_args[arg_idx]);
                }
            } else if (is_compile_sub and std.mem.startsWith(u8, arg_text, "--target=")) {
                const raw_triple = arg_text["--target=".len..];
                target_spec = try codegen_abi.TargetSpec.parseOrEmitInvalidTarget(
                    raw_triple,
                    mem.Span.ZERO,
                    sink,
                );
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--target")) {
                if (arg_idx + 1 >= raw_args.len) {
                    try sink.emit(.{
                        .code = .e0003_missing_cli_argument,
                        .severity = .err,
                        .message = "missing target triple for `--target`",
                        .notes = &.{"help: pass `--target=<triple>` (e.g., `--target=wasm32-wasi`)"},
                    });
                } else {
                    arg_idx += 1;
                    target_spec = try codegen_abi.TargetSpec.parseOrEmitInvalidTarget(
                        raw_args[arg_idx],
                        mem.Span.ZERO,
                        sink,
                    );
                }
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
        const split_pos = pre_dash_count orelse positional_list.items.len;
        const forwarded_run_args = positional_list.items[split_pos..];
        return .{
            .color_mode = color_mode,
            .is_check_only = is_check_only,
            .is_fix_mode = is_fix_mode,
            .comptime_step_limit = comptime_step_limit,
            .is_release_mode = has_seen_release,
            .is_sast_strict = is_sast_strict,
            .is_diff_backends = is_diff_backends,
            .is_emit_c = is_emit_c,
            .is_emit_llvm = is_emit_llvm,
            .is_fuzz_enabled = is_fuzz_enabled,
            .output_format = output_format,
            .output_path = output_path,
            .target_spec = target_spec,
            .run_args = forwarded_run_args,
            .action = .{
                .execute_subcommand = .{
                    .subcommand = sub_id,
                    .positional_args = positional_list.items,
                    .pre_dash_arg_count = split_pos,
                    .run_args = forwarded_run_args,
                    .is_check_only = is_check_only,
                    .is_fix_mode = is_fix_mode,
                    .comptime_step_limit = comptime_step_limit,
                    .is_release_mode = has_seen_release,
                    .is_sast_strict = is_sast_strict,
                    .is_diff_backends = is_diff_backends,
                    .is_emit_c = is_emit_c,
                    .is_emit_llvm = is_emit_llvm,
                    .is_fuzz_enabled = is_fuzz_enabled,
                    .output_format = output_format,
                    .output_path = output_path,
                    .target_spec = target_spec,
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
                var expanded_fmt_paths: std.ArrayListUnmanaged([]u8) = .empty;
                defer {
                    for (expanded_fmt_paths.items) |owned_p| allocator.free(owned_p);
                    expanded_fmt_paths.deinit(allocator);
                }
                for (exec_info.positional_args) |raw_arg| {
                    if (!(try collectDirectoryCxPaths(allocator, io, raw_arg, &expanded_fmt_paths))) {
                        const duped_arg = try allocator.dupe(u8, raw_arg);
                        errdefer allocator.free(duped_arg);
                        try expanded_fmt_paths.append(allocator, duped_arg);
                    }
                }

                var has_unformatted_or_error = false;
                for (expanded_fmt_paths.items) |file_arg| {
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

            const input_positional = if (exec_info.subcommand == .run)
                exec_info.positional_args[0..exec_info.pre_dash_arg_count]
            else
                exec_info.positional_args;

            var expanded_paths: std.ArrayListUnmanaged([]u8) = .empty;
            defer {
                for (expanded_paths.items) |owned_p| allocator.free(owned_p);
                expanded_paths.deinit(allocator);
            }
            for (input_positional) |raw_arg| {
                const allow_dir = exec_info.subcommand == .check or exec_info.subcommand == .@"test";
                if (!allow_dir or !(try collectDirectoryCxPaths(allocator, io, raw_arg, &expanded_paths))) {
                    const duped_arg = try allocator.dupe(u8, raw_arg);
                    errdefer allocator.free(duped_arg);
                    try expanded_paths.append(allocator, duped_arg);
                }
            }

            var cx_file_ids: std.ArrayListUnmanaged(mem.FileId) = .empty;
            defer cx_file_ids.deinit(allocator);
            var cx_file_paths: std.ArrayListUnmanaged([]const u8) = .empty;
            defer cx_file_paths.deinit(allocator);
            var embed_sandbox_root: []const u8 = ".";

            for (expanded_paths.items) |file_arg| {
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
                    try cx_file_paths.append(allocator, file_arg);
                }
            }
            if (sink.hasErrors()) {
                try DiagnosticRenderer.init(&source_map, &interner, stderr_style).renderAll(stderr_writer, &sink);
                return 1;
            }

            if (isCompileSubcommand(exec_info.subcommand) and cx_file_ids.items.len > 0) {
                var db = try query_db.CompilerDb.init(allocator);
                defer db.deinit();
                db.setSastStrict(exec_info.is_sast_strict);
                db.setComptimeStepLimit(exec_info.comptime_step_limit);
                db.setEmbedSandbox(embed_sandbox_root, null);
                db.setEmbedIo(io);
                if (exec_info.target_spec) |explicit_target| {
                    db.setTargetSpec(explicit_target);
                }

                var visited_fids: std.AutoHashMapUnmanaged(u32, void) = .empty;
                defer visited_fids.deinit(allocator);
                var has_core_mention = false;

                for (cx_file_ids.items, cx_file_paths.items) |cx_fid, cx_path| {
                    try discoverExternalSubmodulesRecursive(
                        allocator,
                        io,
                        &source_map,
                        &db,
                        cx_fid,
                        cx_path,
                        .low,
                        .root,
                        &visited_fids,
                        &has_core_mention,
                        0,
                    );
                }
                if (has_core_mention) {
                    try registerWorkspaceCoreModuleIfNeeded(
                        allocator,
                        io,
                        &source_map,
                        &db,
                        &visited_fids,
                    );
                }

                const diag_renderer = DiagnosticRenderer.init(&source_map, &interner, stderr_style);
                if (try verifyAndRenderModuleDiagnostics(
                    allocator,
                    &db,
                    cx_file_ids.items,
                    diag_renderer,
                    stderr_writer,
                )) {
                    return 1;
                }

                switch (exec_info.subcommand) {
                    .check => {},
                    .build => {
                        const active_target = exec_info.target_spec orelse codegen_abi.TargetSpec.host();
                        const has_main = try fileDeclaresMainEntrypoint(&db, cx_file_ids.items[0]);
                        const artifact_kind: codegen_abi.OutputArtifactKind =
                            if (exec_info.is_emit_c or exec_info.is_emit_llvm)
                                .source_text
                            else if (has_main)
                                .executable
                            else
                                .object_file;

                        const stem = std.fs.path.stem(cx_file_paths.items[0]);
                        const default_ext: []const u8 = switch (artifact_kind) {
                            .source_text => if (exec_info.output_format == .c) ".c" else ".ll",
                            .executable => active_target.executableExtension(),
                            .object_file => active_target.objectExtension(),
                        };
                        const default_out = try std.fmt.allocPrint(
                            allocator,
                            "build/{s}{s}",
                            .{ stem, default_ext },
                        );
                        defer allocator.free(default_out);
                        const final_out_path = exec_info.output_path orelse default_out;

                        const backend = buildConfiguredBackend(
                            exec_info.output_format,
                            active_target,
                            exec_info.is_release_mode,
                            exec_info.is_fuzz_enabled,
                        );
                        var build_art = db.compileModuleArtifact(cx_file_ids.items[0], backend, .{
                            .module_name = stem,
                            .extra_file_ids = cx_file_ids.items[1..],
                            .vfs_source_map = &source_map,
                            .is_dev_got_enabled = false,
                            .artifact_kind = artifact_kind,
                            .output_path = final_out_path,
                            .io = io,
                            .environ_map = environ_map,
                            .diagnostic_sink = &sink,
                        }) catch |comp_err| switch (comp_err) {
                            error.OutOfMemory => return error.OutOfMemory,
                            else => {
                                if (sink.hasErrors()) {
                                    try diag_renderer.renderAll(stderr_writer, &sink);
                                }
                                return 1;
                            },
                        };
                        defer build_art.deinit(allocator);

                        try stdout_style.writeStatusHeader(
                            stdout_writer,
                            .success,
                            Glyphs.SUCCESS,
                            "build",
                            final_out_path,
                        );
                        try stdout_writer.writeByte('\n');
                        return 0;
                    },
                    .run => {
                        const host_target = exec_info.target_spec orelse codegen_abi.TargetSpec.host();
                        if (!std.meta.eql(host_target.arch, codegen_abi.TargetSpec.host().arch) or
                            !std.meta.eql(host_target.os, codegen_abi.TargetSpec.host().os))
                        {
                            try sink.emit(.{
                                .code = .e0006_invalid_target_triple,
                                .severity = .err,
                                .message = "cannot execute cross-compiled target directly via `corex run`",
                                .notes = &.{"help: use `corex build --target=<triple>` to emit a cross-target binary"},
                            });
                            try diag_renderer.renderAll(stderr_writer, &sink);
                            return 1;
                        }

                        const run_seq = next_run_scratch_seq.fetchAdd(1, .monotonic);
                        const scratch_dir = try std.fmt.allocPrint(
                            allocator,
                            ".zig-cache/cx_run_{d}",
                            .{run_seq},
                        );
                        defer allocator.free(scratch_dir);
                        defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};

                        const stem = std.fs.path.stem(cx_file_paths.items[0]);
                        const temp_exe_path = try std.fmt.allocPrint(
                            allocator,
                            "{s}/{s}{s}",
                            .{ scratch_dir, stem, host_target.executableExtension() },
                        );
                        defer allocator.free(temp_exe_path);
                        const final_exe_path = exec_info.output_path orelse temp_exe_path;

                        const backend = buildConfiguredBackend(
                            exec_info.output_format,
                            host_target,
                            exec_info.is_release_mode,
                            exec_info.is_fuzz_enabled,
                        );
                        var run_art = db.compileModuleArtifact(cx_file_ids.items[0], backend, .{
                            .module_name = stem,
                            .extra_file_ids = cx_file_ids.items[1..],
                            .vfs_source_map = &source_map,
                            .is_dev_got_enabled = false,
                            .artifact_kind = .executable,
                            .output_path = final_exe_path,
                            .io = io,
                            .environ_map = environ_map,
                            .diagnostic_sink = &sink,
                        }) catch |comp_err| switch (comp_err) {
                            error.OutOfMemory => return error.OutOfMemory,
                            else => {
                                if (sink.hasErrors()) {
                                    try diag_renderer.renderAll(stderr_writer, &sink);
                                }
                                return 1;
                            },
                        };
                        defer run_art.deinit(allocator);

                        var child_argv: std.ArrayListUnmanaged([]const u8) = .empty;
                        defer child_argv.deinit(allocator);
                        try child_argv.append(allocator, final_exe_path);
                        try child_argv.appendSlice(allocator, exec_info.run_args);

                        const child_res = std.process.run(allocator, io, .{
                            .argv = child_argv.items,
                            .environ_map = environ_map,
                        }) catch {
                            try sink.emit(.{
                                .code = .e0007_codegen_backend_failure,
                                .severity = .err,
                                .message = "failed to spawn compiled CoreX executable",
                            });
                            try diag_renderer.renderAll(stderr_writer, &sink);
                            return 1;
                        };
                        defer allocator.free(child_res.stdout);
                        defer allocator.free(child_res.stderr);

                        if (child_res.stdout.len > 0) try stdout_writer.writeAll(child_res.stdout);
                        if (child_res.stderr.len > 0) try stderr_writer.writeAll(child_res.stderr);
                        return switch (child_res.term) {
                            .exited => |status_code| status_code,
                            else => if (builtin.os.tag == .windows) 101 else 134,
                        };
                    },
                    .@"test" => {
                        if (exec_info.is_diff_backends) {
                            var tested_main_count: usize = 0;
                            for (cx_file_ids.items) |test_fid| {
                                if (!(try fileDeclaresMainEntrypoint(&db, test_fid))) continue;
                                tested_main_count += 1;
                                var oracle_report = diff_oracle.runFourTierDiffOracleOnDb(
                                    allocator,
                                    &db,
                                    test_fid,
                                    .{
                                        .io = io,
                                        .environ_map = environ_map,
                                        .vfs_source_map = &source_map,
                                        .workspace_root = embed_sandbox_root,
                                        .comptime_step_limit = exec_info.comptime_step_limit,
                                        .diagnostic_sink = &sink,
                                    },
                                ) catch |oracle_err| switch (oracle_err) {
                                    error.OutOfMemory => return error.OutOfMemory,
                                    else => {
                                        if (sink.hasErrors()) {
                                            try diag_renderer.renderAll(stderr_writer, &sink);
                                        }
                                        return 1;
                                    },
                                };
                                defer oracle_report.deinit(allocator);
                                if (!oracle_report.is_all_matching) {
                                    try stderr_writer.writeAll(oracle_report.rendered_diff_table);
                                    return 1;
                                }
                            }
                            var msg_buf: [128]u8 = undefined;
                            const status_msg = std.fmt.bufPrint(
                                &msg_buf,
                                "4-tier differential oracle verified ({d} module(s))",
                                .{tested_main_count},
                            ) catch "4-tier differential oracle verified";
                            try stdout_style.writeStatusHeader(
                                stdout_writer,
                                .success,
                                Glyphs.SUCCESS,
                                "test",
                                status_msg,
                            );
                            try stdout_writer.writeByte('\n');
                            return 0;
                        }
                    },
                    else => {},
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

// ---------------------------------------- MAIN -----------------------------------------

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

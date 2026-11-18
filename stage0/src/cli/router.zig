//! CLI Command Router, Dynamic Metadata Registry & Typo Suggestion Engine
//!
//! Defines the canonical `CLI_SUBCOMMANDS` (`SUBCOMMANDS`), `GLOBAL_FLAGS`, `COMPILE_FLAGS`,
//! `TRANSLATE_C_FLAGS`, `FMT_FLAGS`, and `UPGRADE_FLAGS` metadata tables.
//!
//! Parses command-line arguments in a single pass, dispatches compilation, C11/C23 header translation,
//! formatting, and verification workflows, emits `E0001`–`E0006` diagnostics with stack-allocated
//! Levenshtein typo suggestions (`help: did you mean \`…\`?`), and renders monochrome help menus.

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
const c_frontend = @import("../c_frontend.zig");
const c_translate = @import("../c_translate.zig");

const ColorMode = style.ColorMode;
const Glyphs = style.Glyphs;
const StyleConfig = style.StyleConfig;
const CardRenderer = box_draw.CardRenderer;
const DiagnosticSink = diag.DiagnosticSink;
const DiagnosticRenderer = renderer.DiagnosticRenderer;

// ---------------------------------------- TYPES ----------------------------------------

/// Canonical CoreX CLI subcommand identifiers indexed 1-to-1 (alphabetically) into `SUBCOMMANDS`.
pub const SubcommandId = enum(u8) {
    /// `corex bench` – run statistical performance benchmarks and emit monochrome report tables (`0`).
    bench = 0,
    /// `corex build` – compile package or source file into a native or WebAssembly artifact (`1`).
    build = 1,
    /// `corex check` – run fast syntax, type, region, and SAST verification without codegen (`2`).
    check = 2,
    /// `corex fmt` – format CoreX source files canonically using the lossless CST (`3`).
    fmt = 3,
    /// `corex lsp` – start the CoreX Language Server Protocol (LSP) daemon over stdio (`4`).
    lsp = 4,
    /// `corex run` – compile and immediately execute a CoreX binary (`5`).
    run = 5,
    /// `corex test` – compile and execute unit, snapshot, and safety verification suites (`6`).
    @"test" = 6,
    /// `corex translate-c` – translate a C11/C23 header into canonical CoreX (`.cx`) bindings (`7`).
    translate_c = 7,
    /// `corex upgrade` – apply automated AST/CST migrations and machine-applicable fixes (`8`).
    upgrade = 8,

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

    /// Resolves a CLI token string to its `SubcommandId` in $O(1)$ time via `SUBCOMMAND_NAME_MAP`.
    pub inline fn fromName(name_str: []const u8) ?SubcommandId {
        return SUBCOMMAND_NAME_MAP.get(name_str);
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
    /// `--internal-core` – permit direct `core.*` kernel imports without `E0218` (`2`).
    internal_core = 2,
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

/// Subcommand-specific CLI option identifiers for `corex upgrade` (`UPGRADE_FLAGS`).
pub const UpgradeFlagId = enum(u8) {
    /// `--internal-core` – permit direct `core.*` kernel imports without `E0218` (`0`).
    internal_core = 0,
};

/// Static metadata entry in `UPGRADE_FLAGS` describing `corex upgrade` flags.
pub const UpgradeFlagDescriptor = struct {
    /// Strongly typed `corex upgrade` flag enum tag.
    id: UpgradeFlagId,
    /// Canonical long flag token (e.g., `"--internal-core"`).
    long_flag: []const u8,
    /// Concise one-line summary.
    summary: []const u8,
};

/// Subcommand-specific CLI option identifiers for `corex translate-c` (`TRANSLATE_C_FLAGS`).
pub const TranslateCFlagId = enum(u8) {
    /// `--define=<name[=val]>` / `-D` – define C preprocessor macro (`0`).
    define = 0,
    /// `--include-dir=<dir>` / `-I` – add C `#include` search directory (`1`).
    include_dir = 1,
    /// `--internal-core` – emit `use core.ffi.*` instead of `use cx.ffi.*` (`2`).
    internal_core = 2,
    /// `--output=<path>` / `-o` – write translated `.cx` bindings to `<path>` (`3`).
    output = 3,
    /// `--target=<triple>` – select target C ABI triple (`4`).
    target = 4,
};

/// Static metadata entry in `TRANSLATE_C_FLAGS` describing `corex translate-c` flags.
pub const TranslateCFlagDescriptor = struct {
    /// Strongly typed `corex translate-c` flag enum tag.
    id: TranslateCFlagId,
    /// Optional short flag token (e.g., `"-D"`, `"-I"`, `"-o"`).
    short_flag: ?[]const u8 = null,
    /// Canonical long flag token (e.g., `"--define"`).
    long_flag: []const u8,
    /// Optional value placeholder suffix (e.g., `"=<dir>"`).
    value_suffix: ?[]const u8 = null,
    /// Concise one-line summary displayed in `corex translate-c --help`.
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
    /// `--define=<name[=val]>` / `-D` – define C preprocessor macro for `@c_import` (`1`).
    define = 1,
    /// `--dev` – compile in fast development mode (`2`).
    dev = 2,
    /// `--diff-backends` – run 4-tier `MirVm` / C99 / LLVM differential oracle (`3`).
    diff_backends = 3,
    /// `--emit-c` – emit deterministic ISO C99 source text (`4`).
    emit_c = 4,
    /// `--emit-llvm` – emit deterministic LLVM 20–23 `.ll` IR text (`5`).
    emit_llvm = 5,
    /// `--emit-obj` – emit relocatable `.o` / `.obj` object file without linking (`6`).
    emit_obj = 6,
    /// `--fuzz` – instrument output with `SanitizerCoverage` edge counters (`7`).
    fuzz = 7,
    /// `--include-dir=<dir>` / `-I` – add C `#include` search directory (`8`).
    include_dir = 8,
    /// `--internal-core` – permit direct `core.*` kernel imports without `E0218` (`9`).
    internal_core = 9,
    /// `--lib=<name_or_def>` / `-l` – link C library or `.def`/`.lib`/`.a` input (`10`).
    lib = 10,
    /// `--lib-dir=<dir>` / `-L` – add library search directory (`11`).
    lib_dir = 11,
    /// `--link=<auto|static|dynamic>` – configure binary linkage mode (`12`).
    link = 12,
    /// `--ofmt=<c|llvm>` – select Tier A (`c`) or Tier B (`llvm`) codegen backend (`13`).
    ofmt = 13,
    /// `--output=<path>` / `-o` – write compiled artifact to `<path>` (`14`).
    output = 14,
    /// `--release` – compile in production release mode (`15`).
    release = 15,
    /// `--sast-strict` – emit `W0314` warnings on unproven bounds checks (`16`).
    sast_strict = 16,
    /// `--target=<triple>` – select cross-compilation target triple (`17`).
    target = 17,
};

/// Static metadata entry in `COMPILE_FLAGS` describing `build`/`run`/`check`/`test` flags.
pub const CompileFlagDescriptor = struct {
    /// Strongly typed compilation flag enum tag.
    id: CompileFlagId,
    /// Optional short flag token (e.g., `"-D"`, `"-I"`, `"-l"`, `"-L"`, `"-o"`).
    short_flag: ?[]const u8 = null,
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
        /// Whether `--emit-obj` relocatable object file emission was requested.
        is_emit_obj: bool = false,
        /// Whether `--fuzz` `SanitizerCoverage` instrumentation was requested.
        is_fuzz_enabled: bool = false,
        /// Whether `--internal-core` was passed to permit direct `core.*` kernel imports.
        is_internal_core: bool = false,
        /// Selected codegen backend family (`llvm` by default, or `c` with `-ofmt=c`).
        output_format: OutputFormat = .llvm,
        /// Selected binary linkage mode (`auto` by default, `static`, or `dynamic`).
        link_mode: codegen_abi.LinkMode = .auto,
        /// Arena-allocated `-D` / `--define` C preprocessor macro definitions.
        c_defines: []const c_frontend.MacroDefine = &.{},
        /// Arena-allocated `-I` / `--include-dir` C `#include` search directories.
        include_dirs: []const []const u8 = &.{},
        /// Arena-allocated `-l` / `--lib` C libraries or `.def`/`.lib`/`.a` inputs.
        extra_libs: []const []const u8 = &.{},
        /// Arena-allocated `-L` / `--lib-dir` library search directories.
        lib_dirs: []const []const u8 = &.{},
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
    /// Whether `--emit-obj` was passed on a compile subcommand.
    is_emit_obj: bool = false,
    /// Whether `--fuzz` was passed on a compile subcommand.
    is_fuzz_enabled: bool = false,
    /// Whether `--internal-core` was passed on a compile/check/translate-c/fmt/upgrade subcommand.
    is_internal_core: bool = false,
    /// Selected codegen backend family (`llvm` by default).
    output_format: OutputFormat = .llvm,
    /// Selected binary linkage mode (`auto` by default, `static`, or `dynamic`).
    link_mode: codegen_abi.LinkMode = .auto,
    /// Arena-allocated `-D` / `--define` C preprocessor macro definitions.
    c_defines: []const c_frontend.MacroDefine = &.{},
    /// Arena-allocated `-I` / `--include-dir` C `#include` search directories.
    include_dirs: []const []const u8 = &.{},
    /// Arena-allocated `-l` / `--lib` C libraries or `.def`/`.lib`/`.a` inputs.
    extra_libs: []const []const u8 = &.{},
    /// Arena-allocated `-L` / `--lib-dir` library search directories.
    lib_dirs: []const []const u8 = &.{},
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

/// Canonical alphabetical subcommand table (`PLAN.md` Phase 8 & `AGENTS.md` Section 6).
pub const SUBCOMMANDS = [_]SubcommandDescriptor{
    .{
        .id = .bench,
        .name = "bench",
        .usage = "[filter]",
        .summary = "Run statistical performance benchmarks and emit monochrome report tables",
    },
    .{
        .id = .build,
        .name = "build",
        .usage = "[path]",
        .summary = "Compile a CoreX package or source file into a native or WebAssembly artifact",
    },
    .{
        .id = .check,
        .name = "check",
        .usage = "[path…]",
        .summary = "Run fast syntax, type, region, and SAST verification without codegen",
    },
    .{
        .id = .fmt,
        .name = "fmt",
        .usage = "[path…]",
        .summary = "Format CoreX source files canonically using the lossless CST",
    },
    .{
        .id = .lsp,
        .name = "lsp",
        .usage = "",
        .summary = "Start the CoreX Language Server Protocol (LSP) daemon over stdio",
    },
    .{
        .id = .run,
        .name = "run",
        .usage = "[path] [-- args…]",
        .summary = "Compile and immediately execute a CoreX binary",
    },
    .{
        .id = .@"test",
        .name = "test",
        .usage = "[filter]",
        .summary = "Compile and execute unit, snapshot, and safety verification suites",
    },
    .{
        .id = .translate_c,
        .name = "translate-c",
        .usage = "<header.h>",
        .summary = "Translate a C11/C23 header into canonical CoreX (.cx) bindings",
    },
    .{
        .id = .upgrade,
        .name = "upgrade",
        .usage = "[path…]",
        .summary = "Apply automated AST/CST migrations and machine-applicable fixes",
    },
};

/// Canonical Phase 8 alias for the 9-entry alphabetical `SUBCOMMANDS` registry.
pub const CLI_SUBCOMMANDS = SUBCOMMANDS;

/// $O(1)$ compile-time lookup table mapping CLI subcommand tokens to `SubcommandId`.
const SUBCOMMAND_NAME_MAP = std.StaticStringMap(SubcommandId).initComptime(blk: {
    var entries: [SUBCOMMANDS.len]struct { []const u8, SubcommandId } = undefined;
    for (SUBCOMMANDS, 0..) |descriptor, i| {
        entries[i] = .{ descriptor.name, descriptor.id };
    }
    break :blk entries;
});

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

/// Canonical `corex fmt` option table (`DR-14` Section 1.5 & `DR-21` `ADR-21B`).
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
    .{
        .id = .internal_core,
        .long_flag = "--internal-core",
        .summary = "Permit direct `core.*` kernel imports without `E0218`",
    },
};

/// Canonical `corex upgrade` option table (`DR-21` `ADR-21B`).
pub const UPGRADE_FLAGS = [_]UpgradeFlagDescriptor{
    .{
        .id = .internal_core,
        .long_flag = "--internal-core",
        .summary = "Permit direct `core.*` kernel imports without `E0218`",
    },
};

/// Canonical alphabetical `corex translate-c` option table (`DR-10` Section 2 & `PLAN.md` Phase 8).
pub const TRANSLATE_C_FLAGS = [_]TranslateCFlagDescriptor{
    .{
        .id = .define,
        .short_flag = "-D",
        .long_flag = "--define",
        .value_suffix = "=<name[=val]>",
        .summary = "Define C preprocessor macro (`-D <name[=val]>`)",
    },
    .{
        .id = .include_dir,
        .short_flag = "-I",
        .long_flag = "--include-dir",
        .value_suffix = "=<dir>",
        .summary = "Add C `#include` search directory (`-I <dir>`)",
    },
    .{
        .id = .internal_core,
        .short_flag = null,
        .long_flag = "--internal-core",
        .value_suffix = null,
        .summary = "Emit `use core.ffi.*` instead of `use cx.ffi.*`",
    },
    .{
        .id = .output,
        .short_flag = "-o",
        .long_flag = "--output",
        .value_suffix = "=<path>",
        .summary = "Write translated `.cx` bindings atomically to `<path>`",
    },
    .{
        .id = .target,
        .short_flag = null,
        .long_flag = "--target",
        .value_suffix = "=<triple>",
        .summary = "Select target C ABI triple (default: host)",
    },
};

/// Canonical alphabetical compilation and verification option table (`build`, `run`, `check`, `test`).
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
        .id = .define,
        .short_flag = "-D",
        .long_flag = "--define",
        .value_suffix = "=<name[=val]>",
        .summary = "Define C preprocessor macro (`-D <name[=val]>`)",
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
        .id = .emit_obj,
        .long_flag = "--emit-obj",
        .value_suffix = null,
        .summary = "Emit relocatable `.o` / `.obj` object file without linking",
    },
    .{
        .id = .fuzz,
        .long_flag = "--fuzz",
        .value_suffix = null,
        .summary = "Instrument compiled output with SanitizerCoverage counters",
    },
    .{
        .id = .include_dir,
        .short_flag = "-I",
        .long_flag = "--include-dir",
        .value_suffix = "=<dir>",
        .summary = "Add C `#include` search directory (`-I <dir>`)",
    },
    .{
        .id = .internal_core,
        .long_flag = "--internal-core",
        .value_suffix = null,
        .summary = "Permit direct `core.*` kernel imports without `E0218`",
    },
    .{
        .id = .lib,
        .short_flag = "-l",
        .long_flag = "--lib",
        .value_suffix = "=<name_or_def>",
        .summary = "Link C library or `.def`/`.lib`/`.a` input (`-l <name>`)",
    },
    .{
        .id = .lib_dir,
        .short_flag = "-L",
        .long_flag = "--lib-dir",
        .value_suffix = "=<dir>",
        .summary = "Add library search directory (`-L <dir>`)",
    },
    .{
        .id = .link,
        .long_flag = "--link",
        .value_suffix = "=<auto|static|dynamic>",
        .summary = "Configure binary linkage mode (`auto`, `static`, or `dynamic`)",
    },
    .{
        .id = .ofmt,
        .long_flag = "--ofmt",
        .value_suffix = "=<c|llvm>",
        .summary = "Select Tier A C99 (`c`) or Tier B LLVM (`llvm`) backend",
    },
    .{
        .id = .output,
        .short_flag = "-o",
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

/// Resolves `arg_text` dynamically against `FMT_FLAGS` without hardcoded string drift.
fn matchFmtFlag(arg_text: []const u8) ?FmtFlagId {
    inline for (FMT_FLAGS) |fmt_desc| {
        if (std.mem.eql(u8, arg_text, fmt_desc.long_flag)) return fmt_desc.id;
    }
    return null;
}

/// Resolves `arg_text` dynamically against `UPGRADE_FLAGS` without hardcoded string drift.
fn matchUpgradeFlag(arg_text: []const u8) ?UpgradeFlagId {
    inline for (UPGRADE_FLAGS) |upg_desc| {
        if (std.mem.eql(u8, arg_text, upg_desc.long_flag)) return upg_desc.id;
    }
    return null;
}

/// Extracts a strictly positive ASCII decimal step count (`> 0`), rejecting empty, signed, or zero values.
fn extractPositiveStepLimit(raw_val: []const u8) ?u64 {
    if (raw_val.len == 0) return null;
    for (raw_val) |byte_val| {
        if (!std.ascii.isDigit(byte_val)) return null;
    }
    const parsed_val = std.fmt.parseUnsigned(u64, raw_val, 10) catch return null;
    return if (parsed_val > 0) parsed_val else null;
}

/// Extracts a C preprocessor `MacroDefine` (`NAME` or `NAME=VALUE`), validating the ASCII identifier.
fn extractMacroDefine(
    arena_alloc: std.mem.Allocator,
    raw_spec: []const u8,
) !?c_frontend.MacroDefine {
    if (raw_spec.len == 0) return null;
    const eq_idx_opt = std.mem.indexOfScalar(u8, raw_spec, '=');
    const raw_name = if (eq_idx_opt) |eq_idx| raw_spec[0..eq_idx] else raw_spec;
    if (raw_name.len == 0) return null;
    if (!std.ascii.isAlphabetic(raw_name[0]) and raw_name[0] != '_') return null;
    for (raw_name[1..]) |byte_val| {
        if (!std.ascii.isAlphanumeric(byte_val) and byte_val != '_') return null;
    }
    const owned_name = try arena_alloc.dupe(u8, raw_name);
    const owned_val: ?[]const u8 = if (eq_idx_opt) |eq_idx|
        try arena_alloc.dupe(u8, raw_spec[eq_idx + 1 ..])
    else
        null;
    return .{ .name = owned_name, .value = owned_val };
}

/// Emits an `E0003` diagnostic for a missing CLI option argument.
fn emitMissingCliArgDiagnostic(
    sink: *DiagnosticSink,
    message_text: []const u8,
    help_note: []const u8,
) !void {
    try sink.emit(.{
        .code = .e0003_missing_cli_argument,
        .severity = .err,
        .message = message_text,
        .notes = &.{help_note},
    });
}

/// Matches `--long=<val>`, `--long <val>`, `-S<val>`, or `-S <val>` and extracts its arena-cloned value.
fn tryExtractStringFlagValue(
    raw_args: []const []const u8,
    arg_idx: *usize,
    long_flag: []const u8,
    short_flag: []const u8,
    missing_msg: []const u8,
    missing_help: []const u8,
    sink: *DiagnosticSink,
    out_value: *?[]const u8,
) !bool {
    const arg_text = raw_args[arg_idx.*];
    if (std.mem.startsWith(u8, arg_text, long_flag) and
        arg_text.len > long_flag.len and
        arg_text[long_flag.len] == '=')
    {
        const raw_val = arg_text[long_flag.len + 1 ..];
        if (raw_val.len == 0) {
            try emitMissingCliArgDiagnostic(sink, missing_msg, missing_help);
            out_value.* = null;
        } else {
            out_value.* = try sink.arena.asAllocator().dupe(u8, raw_val);
        }
        return true;
    }
    if (std.mem.eql(u8, arg_text, long_flag) or std.mem.eql(u8, arg_text, short_flag)) {
        if (arg_idx.* + 1 >= raw_args.len or raw_args[arg_idx.* + 1].len == 0) {
            try emitMissingCliArgDiagnostic(sink, missing_msg, missing_help);
            out_value.* = null;
        } else {
            arg_idx.* += 1;
            out_value.* = try sink.arena.asAllocator().dupe(u8, raw_args[arg_idx.*]);
        }
        return true;
    }
    if (short_flag.len == 2 and std.mem.startsWith(u8, arg_text, short_flag) and arg_text.len > 2) {
        const raw_val = if (arg_text[2] == '=') arg_text[3..] else arg_text[2..];
        if (raw_val.len == 0) {
            try emitMissingCliArgDiagnostic(sink, missing_msg, missing_help);
            out_value.* = null;
        } else {
            out_value.* = try sink.arena.asAllocator().dupe(u8, raw_val);
        }
        return true;
    }
    return false;
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

/// Emits an `E0001` diagnostic when `--define` / `-D` receives an invalid C macro identifier.
fn emitInvalidMacroDefineDiagnostic(sink: *DiagnosticSink, raw_define_spec: []const u8) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "invalid C macro definition `{s}` for `--define` / `-D`",
            .{raw_define_spec},
        ),
        .notes = &.{"help: pass a valid C identifier such as `-DFOO` or `--define=FOO=1`"},
    });
}

/// Emits an `E0001` diagnostic when `--link` receives an unsupported linkage mode.
fn emitInvalidLinkModeDiagnostic(sink: *DiagnosticSink, raw_link_val: []const u8) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = try std.fmt.allocPrint(
            sink.arena.asAllocator(),
            "invalid linkage mode `{s}` for `--link`",
            .{raw_link_val},
        ),
        .notes = &.{"help: valid modes for `--link` are `auto`, `static`, or `dynamic`"},
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

/// Emits an `E0001` diagnostic when mutually exclusive `--emit-c`, `--emit-llvm`, or `--emit-obj` flags collide.
fn emitConflictingEmitFlagsDiagnostic(sink: *DiagnosticSink) !void {
    try sink.emit(.{
        .code = .e0001_unknown_cli_flag,
        .severity = .err,
        .message = "conflicting CLI emission flags among `--emit-c`, `--emit-llvm`, and `--emit-obj`",
        .notes = &.{"help: pass at most one of `--emit-c`, `--emit-llvm`, or `--emit-obj`"},
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
    if (!has_core_mention_out.* and
        (std.mem.indexOf(u8, parent_src, "cx") != null or std.mem.indexOf(u8, parent_src, "core") != null))
    {
        has_core_mention_out.* = true;
    }
    _ = try db.setInput(parent_fid, parent_src, durability);
    if (pkg_id != .root) {
        try db.setFilePackageId(parent_fid, pkg_id);
    }

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
    try db.registerRootModule("cx", core_fid);
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

/// Renders a single aligned CLI option row (`short_flag`, `long_flag`, `value_suffix`, and `summary`).
fn renderOptionLine(
    writer: *std.Io.Writer,
    style_config: StyleConfig,
    short_flag: ?[]const u8,
    long_flag: []const u8,
    value_suffix: ?[]const u8,
    col_width: usize,
    summary: []const u8,
) std.Io.Writer.Error!void {
    var flag_buf: [64]u8 = undefined;
    var flag_writer = std.Io.Writer.fixed(&flag_buf);
    if (short_flag) |short_str| {
        flag_writer.print("{s}, {s}", .{ short_str, long_flag }) catch unreachable;
    } else {
        flag_writer.print("    {s}", .{long_flag}) catch unreachable;
    }
    if (value_suffix) |suffix_str| {
        flag_writer.writeAll(suffix_str) catch unreachable;
    }
    const formatted_flag = flag_writer.buffered();
    try writer.writeAll("  ");
    try style_config.writeStyled(writer, .bold, formatted_flag);
    if (formatted_flag.len < col_width) {
        try writer.splatByteAll(' ', col_width - formatted_flag.len);
    } else {
        try writer.writeByte(' ');
    }
    try writer.writeAll(summary);
    try writer.writeByte('\n');
}

/// Loads `file_path` into `source_map` with its `LineIndex`, emitting `E0004` or `E0005` on failure.
fn loadSourceFileIntoVfs(
    io: std.Io,
    source_map: *vfs.VfsSourceMap,
    file_path: []const u8,
    sink: *DiagnosticSink,
) !?mem.FileId {
    const file_id = source_map.resolveOrCreatePath(io, file_path, .root) catch |vfs_err| switch (vfs_err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.FileTooLarge => {
            try sink.emit(.{
                .code = .e0005_source_file_size_exceeded,
                .severity = .err,
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "source file `{s}` exceeds the 64 MiB maximum size limit",
                    .{file_path},
                ),
            });
            return null;
        },
        else => {
            try sink.emit(.{
                .code = .e0004_source_file_io_error,
                .severity = .err,
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "failed to open or read source file `{s}`",
                    .{file_path},
                ),
            });
            return null;
        },
    };
    _ = try source_map.getLineIndex(file_id);
    return file_id;
}

/// Executes `corex translate-c <header.h>` and writes canonical `.cx` bindings to `-o <path>` or `stdout_writer`.
fn executeTranslateCSubcommand(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs.VfsSourceMap,
    interner: *mem.StringInterner,
    sink: *DiagnosticSink,
    positional_args: []const []const u8,
    target_spec_opt: ?codegen_abi.TargetSpec,
    c_defines: []const c_frontend.MacroDefine,
    include_dirs: []const []const u8,
    is_internal_core: bool,
    output_path_opt: ?[]const u8,
    stdout_style: StyleConfig,
    stderr_style: StyleConfig,
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
) !u8 {
    // [1] Require a single `<header.h>` positional input path:
    if (positional_args.len == 0) {
        try emitMissingCliArgDiagnostic(
            sink,
            "missing required `<header.h>` argument for `corex translate-c`",
            "help: run `corex translate-c <header.h>` or `corex translate-c -o bindings.cx <header.h>`",
        );
        try DiagnosticRenderer.init(source_map, interner, stderr_style).renderAll(stderr_writer, sink);
        return 1;
    }
    if (positional_args.len > 1) {
        try sink.emit(.{
            .code = .e0001_unknown_cli_flag,
            .severity = .err,
            .message = try std.fmt.allocPrint(
                sink.arena.asAllocator(),
                "unexpected extra positional argument `{s}` for `corex translate-c`",
                .{positional_args[1]},
            ),
            .notes = &.{"help: `corex translate-c` accepts a single `<header.h>` path"},
        });
        try DiagnosticRenderer.init(source_map, interner, stderr_style).renderAll(stderr_writer, sink);
        return 1;
    }

    // [2] Load `<header.h>` into `VfsSourceMap` so `E0009` C spans render with source snippets:
    const header_path = positional_args[0];
    const active_target = target_spec_opt orelse codegen_abi.TargetSpec.host();
    const header_fid = (try loadSourceFileIntoVfs(io, source_map, header_path, sink)) orelse {
        try DiagnosticRenderer.init(source_map, interner, stderr_style).renderAll(stderr_writer, sink);
        return 1;
    };
    const header_source = source_map.getFileSource(header_fid) orelse "";

    // [3] Assemble `-I` search directories plus `<header.h>`'s parent directory for `#include "…"`:
    var effective_include_dirs: std.ArrayListUnmanaged([]const u8) = .empty;
    defer effective_include_dirs.deinit(allocator);
    try effective_include_dirs.appendSlice(allocator, include_dirs);
    const header_dir = std.fs.path.dirname(header_path) orelse ".";
    var has_header_dir = false;
    for (effective_include_dirs.items) |existing_dir| {
        if (std.mem.eql(u8, existing_dir, header_dir)) {
            has_header_dir = true;
            break;
        }
    }
    if (!has_header_dir) {
        try effective_include_dirs.append(allocator, header_dir);
    }

    // [4] Preprocess, parse, and translate C11/C23 declarations into formatted CoreX v1.0 `.cx` source:
    const translated_cx = c_translate.translateHeaderSource(
        allocator,
        header_source,
        header_path,
        header_fid,
        .{
            .target = active_target,
            .defines = c_defines,
            .include_dirs = effective_include_dirs.items,
            .include_loader = .{ .host_fs = io },
        },
        .{
            .is_internal_core = is_internal_core,
        },
        sink,
    ) catch |trans_err| switch (trans_err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            if (sink.hasErrors()) {
                try DiagnosticRenderer.init(source_map, interner, stderr_style).renderAll(stderr_writer, sink);
            }
            return 1;
        },
    };
    defer allocator.free(translated_cx);

    if (sink.hasErrors()) {
        try DiagnosticRenderer.init(source_map, interner, stderr_style).renderAll(stderr_writer, sink);
        return 1;
    }

    // [5] Emit atomically to `-o <path>` or write directly to `stdout_writer`:
    if (output_path_opt) |dest_path| {
        codegen_abi.writeArtifactAtomic(io, allocator, dest_path, translated_cx) catch {
            try sink.emit(.{
                .code = .e0004_source_file_io_error,
                .severity = .err,
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "failed to write translated CoreX bindings file `{s}`",
                    .{dest_path},
                ),
            });
            try DiagnosticRenderer.init(source_map, interner, stderr_style).renderAll(stderr_writer, sink);
            return 1;
        };
        try stdout_style.writeStatusHeader(
            stdout_writer,
            .success,
            Glyphs.SUCCESS,
            "translate-c",
            dest_path,
        );
        try stdout_writer.writeByte('\n');
        return 0;
    }

    try stdout_writer.writeAll(translated_cx);
    return 0;
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
    const is_long_input = std.mem.startsWith(u8, flag_name, "--");

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
    } else if (subcommand == .upgrade) {
        for (UPGRADE_FLAGS) |upg_desc| {
            const upg_dist = computeLevenshteinDistance(flag_name, upg_desc.long_flag);
            if (upg_dist < best_distance) {
                best_distance = upg_dist;
                best_match = upg_desc.long_flag;
            }
        }
    } else if (subcommand == .translate_c) {
        for (TRANSLATE_C_FLAGS) |tc_desc| {
            const tc_dist = computeLevenshteinDistance(flag_name, tc_desc.long_flag);
            if (tc_dist < best_distance) {
                best_distance = tc_dist;
                best_match = tc_desc.long_flag;
            }
            if (!is_long_input) {
                if (tc_desc.short_flag) |short_str| {
                    const short_dist = computeLevenshteinDistance(flag_name, short_str);
                    if (short_dist < best_distance) {
                        best_distance = short_dist;
                        best_match = short_str;
                    }
                }
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
                if (!is_long_input) {
                    if (comp_desc.short_flag) |short_str| {
                        const short_dist = computeLevenshteinDistance(flag_name, short_str);
                        if (short_dist < best_distance) {
                            best_distance = short_dist;
                            best_match = short_str;
                        }
                    }
                }
            }
        }
    }
    return best_match;
}

/// Parses CLI arguments (excluding `argv[0]`), emitting `E0001`/`E0002`/`E0003`/`E0006` into `sink` on error.
pub fn parseArgs(raw_args: []const []const u8, sink: *DiagnosticSink) !ParsedCommand {
    const arena_alloc = sink.arena.asAllocator();
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
    var is_emit_obj = false;
    var is_fuzz_enabled = false;
    var is_internal_core = false;
    var output_format: OutputFormat = .llvm;
    var link_mode: codegen_abi.LinkMode = .auto;
    var c_defines_list: std.ArrayListUnmanaged(c_frontend.MacroDefine) = .empty;
    var include_dirs_list: std.ArrayListUnmanaged([]const u8) = .empty;
    var extra_libs_list: std.ArrayListUnmanaged([]const u8) = .empty;
    var lib_dirs_list: std.ArrayListUnmanaged([]const u8) = .empty;
    var output_path: ?[]const u8 = null;
    var target_spec: ?codegen_abi.TargetSpec = null;
    var selected_subcommand: ?SubcommandId = null;
    var positional_list: std.ArrayListUnmanaged([]const u8) = .empty;
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
            const is_compile_or_translate = is_compile_sub or selected_subcommand == .translate_c;
            const is_ofmt_spelling = std.mem.eql(u8, arg_text, "-ofmt") or
                std.mem.startsWith(u8, arg_text, "-ofmt=");
            var extracted_str: ?[]const u8 = null;

            if (std.mem.eql(u8, arg_text, "-h") or std.mem.eql(u8, arg_text, "--help")) {
                has_help_flag = true;
            } else if (std.mem.eql(u8, arg_text, "-V") or std.mem.eql(u8, arg_text, "--version")) {
                has_version_flag = true;
            } else if (selected_subcommand == .fmt and matchFmtFlag(arg_text) != null) {
                switch (matchFmtFlag(arg_text).?) {
                    .check => is_check_only = true,
                    .fix => is_fix_mode = true,
                    .internal_core => is_internal_core = true,
                }
            } else if (selected_subcommand == .upgrade and matchUpgradeFlag(arg_text) != null) {
                switch (matchUpgradeFlag(arg_text).?) {
                    .internal_core => is_internal_core = true,
                }
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
                if (is_emit_llvm or is_emit_obj) {
                    try emitConflictingEmitFlagsDiagnostic(sink);
                }
                is_emit_c = true;
                output_format = .c;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--emit-llvm")) {
                if (is_emit_c or is_emit_obj) {
                    try emitConflictingEmitFlagsDiagnostic(sink);
                }
                is_emit_llvm = true;
                output_format = .llvm;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--emit-obj")) {
                if (is_emit_c or is_emit_llvm) {
                    try emitConflictingEmitFlagsDiagnostic(sink);
                }
                is_emit_obj = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--fuzz")) {
                is_fuzz_enabled = true;
            } else if (is_compile_or_translate and
                std.mem.eql(u8, arg_text, COMPILE_FLAGS[@backingInt(CompileFlagId.internal_core)].long_flag))
            {
                is_internal_core = true;
            } else if (is_compile_or_translate and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--define",
                "-D",
                "missing macro definition for `--define` / `-D`",
                "help: pass `--define=<name[=val]>` or `-D <name[=val]>`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |raw_spec| {
                    if (try extractMacroDefine(arena_alloc, raw_spec)) |macro_def| {
                        try c_defines_list.append(arena_alloc, macro_def);
                    } else {
                        try emitInvalidMacroDefineDiagnostic(sink, raw_spec);
                    }
                }
            } else if (is_compile_or_translate and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--include-dir",
                "-I",
                "missing directory path for `--include-dir` / `-I`",
                "help: pass `--include-dir=<dir>` or `-I <dir>`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |dir_str| {
                    try include_dirs_list.append(arena_alloc, dir_str);
                }
            } else if (is_compile_sub and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--lib",
                "-l",
                "missing library name or `.def`/`.lib`/`.a` path for `--lib` / `-l`",
                "help: pass `--lib=<name_or_def>` or `-l <name>`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |lib_str| {
                    try extra_libs_list.append(arena_alloc, lib_str);
                }
            } else if (is_compile_sub and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--lib-dir",
                "-L",
                "missing directory path for `--lib-dir` / `-L`",
                "help: pass `--lib-dir=<dir>` or `-L <dir>`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |lib_dir_str| {
                    try lib_dirs_list.append(arena_alloc, lib_dir_str);
                }
            } else if (is_compile_sub and std.mem.startsWith(u8, arg_text, "--link=")) {
                const raw_link = arg_text["--link=".len..];
                if (codegen_abi.LinkMode.fromStr(raw_link)) |parsed_link| {
                    link_mode = parsed_link;
                } else {
                    try emitInvalidLinkModeDiagnostic(sink, raw_link);
                }
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--link")) {
                if (arg_idx + 1 >= raw_args.len) {
                    try emitMissingCliArgDiagnostic(
                        sink,
                        "missing linkage mode for `--link`; expected `auto`, `static`, or `dynamic`",
                        "help: pass `--link=auto`, `--link=static`, or `--link=dynamic`",
                    );
                } else {
                    arg_idx += 1;
                    if (codegen_abi.LinkMode.fromStr(raw_args[arg_idx])) |parsed_link| {
                        link_mode = parsed_link;
                    } else {
                        try emitInvalidLinkModeDiagnostic(sink, raw_args[arg_idx]);
                    }
                }
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
                    try emitMissingCliArgDiagnostic(
                        sink,
                        "missing backend format for `--ofmt`; expected `c` or `llvm`",
                        "help: pass `--ofmt=c` (`-ofmt=c`) or `--ofmt=llvm` (`-ofmt=llvm`)",
                    );
                } else {
                    arg_idx += 1;
                    const next_fmt = raw_args[arg_idx];
                    if (OutputFormat.parse(next_fmt)) |parsed_fmt| {
                        output_format = parsed_fmt;
                    } else {
                        try emitInvalidOutputFormatDiagnostic(sink, next_fmt);
                    }
                }
            } else if (is_compile_or_translate and !is_ofmt_spelling and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--output",
                "-o",
                "missing file path for `--output` / `-o`",
                "help: pass `--output=<path>` or `-o <path>`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |out_str| {
                    output_path = out_str;
                }
            } else if (is_compile_or_translate and std.mem.startsWith(u8, arg_text, "--target=")) {
                const raw_triple = arg_text["--target=".len..];
                target_spec = try codegen_abi.TargetSpec.parseOrEmitInvalidTarget(
                    raw_triple,
                    mem.Span.ZERO,
                    sink,
                );
            } else if (is_compile_or_translate and std.mem.eql(u8, arg_text, "--target")) {
                if (arg_idx + 1 >= raw_args.len) {
                    try emitMissingCliArgDiagnostic(
                        sink,
                        "missing target triple for `--target`",
                        "help: pass `--target=<triple>` (e.g., `--target=wasm32-wasi`)",
                    );
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
                    try emitMissingCliArgDiagnostic(
                        sink,
                        "missing step count for `--comptime-limit`; expected positive integer",
                        "help: pass `--comptime-limit=<steps>` (e.g., `--comptime-limit=10000000`)",
                    );
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
                    try emitMissingCliArgDiagnostic(
                        sink,
                        "missing value for `--color`; expected `auto`, `always`, or `never`",
                        "help: pass `--color=auto`, `--color=always`, or `--color=never`",
                    );
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
            try positional_list.append(arena_alloc, arg_text);
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
            .is_emit_obj = is_emit_obj,
            .is_fuzz_enabled = is_fuzz_enabled,
            .is_internal_core = is_internal_core,
            .output_format = output_format,
            .link_mode = link_mode,
            .c_defines = c_defines_list.items,
            .include_dirs = include_dirs_list.items,
            .extra_libs = extra_libs_list.items,
            .lib_dirs = lib_dirs_list.items,
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
                    .is_emit_obj = is_emit_obj,
                    .is_fuzz_enabled = is_fuzz_enabled,
                    .is_internal_core = is_internal_core,
                    .output_format = output_format,
                    .link_mode = link_mode,
                    .c_defines = c_defines_list.items,
                    .include_dirs = include_dirs_list.items,
                    .extra_libs = extra_libs_list.items,
                    .lib_dirs = lib_dirs_list.items,
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

    // [2] Render canonical alphabetical `SUBCOMMANDS` section:
    try style_config.writeStyled(writer, .bold, "Commands:");
    try writer.writeByte('\n');
    for (SUBCOMMANDS) |descriptor| {
        try writer.writeAll("  ");
        try style_config.writeStyled(writer, .dim, Glyphs.POINTER_SOLID);
        try writer.writeByte(' ');
        try style_config.writeStyled(writer, .bold, descriptor.name);
        const pad_spaces: usize = if (descriptor.name.len < 13) 13 - descriptor.name.len else 2;
        try writer.splatByteAll(' ', pad_spaces);
        try writer.writeAll(descriptor.summary);
        try writer.writeByte('\n');
    }
    try writer.writeByte('\n');

    // [3] Render canonical `GLOBAL_FLAGS` section:
    try style_config.writeStyled(writer, .bold, "Global Options:");
    try writer.writeByte('\n');
    for (GLOBAL_FLAGS) |flag_desc| {
        try renderOptionLine(
            writer,
            style_config,
            flag_desc.short_flag,
            flag_desc.long_flag,
            flag_desc.value_suffix,
            20,
            flag_desc.summary,
        );
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
            try renderOptionLine(
                writer,
                style_config,
                comp_desc.short_flag,
                comp_desc.long_flag,
                comp_desc.value_suffix,
                34,
                comp_desc.summary,
            );
        }
        try writer.writeByte('\n');
    } else if (subcommand == .translate_c) {
        try style_config.writeStyled(writer, .bold, "Translate-C Options:");
        try writer.writeByte('\n');
        for (TRANSLATE_C_FLAGS) |tc_desc| {
            try renderOptionLine(
                writer,
                style_config,
                tc_desc.short_flag,
                tc_desc.long_flag,
                tc_desc.value_suffix,
                28,
                tc_desc.summary,
            );
        }
        try writer.writeByte('\n');
    } else if (subcommand == .fmt) {
        try style_config.writeStyled(writer, .bold, "Format Options:");
        try writer.writeByte('\n');
        for (FMT_FLAGS) |fmt_desc| {
            try renderOptionLine(
                writer,
                style_config,
                null,
                fmt_desc.long_flag,
                null,
                22,
                fmt_desc.summary,
            );
        }
        try writer.writeByte('\n');
    } else if (subcommand == .upgrade) {
        try style_config.writeStyled(writer, .bold, "Upgrade Options:");
        try writer.writeByte('\n');
        for (UPGRADE_FLAGS) |upg_desc| {
            try renderOptionLine(
                writer,
                style_config,
                null,
                upg_desc.long_flag,
                null,
                22,
                upg_desc.summary,
            );
        }
        try writer.writeByte('\n');
    }

    try style_config.writeStyled(writer, .bold, "Global Options:");
    try writer.writeByte('\n');
    for (GLOBAL_FLAGS) |flag_desc| {
        try renderOptionLine(
            writer,
            style_config,
            flag_desc.short_flag,
            flag_desc.long_flag,
            flag_desc.value_suffix,
            20,
            flag_desc.summary,
        );
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
            if (exec_info.subcommand == .translate_c) {
                return executeTranslateCSubcommand(
                    allocator,
                    io,
                    &source_map,
                    &interner,
                    &sink,
                    exec_info.positional_args,
                    exec_info.target_spec,
                    exec_info.c_defines,
                    exec_info.include_dirs,
                    exec_info.is_internal_core,
                    exec_info.output_path,
                    stdout_style,
                    stderr_style,
                    stdout_writer,
                    stderr_writer,
                );
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
                const allow_dir = exec_info.subcommand == .check or
                    exec_info.subcommand == .@"test" or
                    exec_info.subcommand == .upgrade;
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
                const file_id = (try loadSourceFileIntoVfs(io, &source_map, file_arg, &sink)) orelse continue;
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

            if ((isCompileSubcommand(exec_info.subcommand) or exec_info.subcommand == .upgrade) and
                cx_file_ids.items.len > 0)
            {
                var db = try query_db.CompilerDb.init(allocator);
                defer db.deinit();
                db.setSastStrict(exec_info.is_sast_strict);
                if (exec_info.is_internal_core) {
                    try db.setInternalCore(true);
                }
                db.setIncludeTests(exec_info.subcommand == .@"test");
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
                            else if (exec_info.is_emit_obj)
                                .object_file
                            else if (has_main)
                                .executable
                            else
                                .object_file;

                        const stem = std.fs.path.stem(cx_file_paths.items[0]);
                        const default_ext: []const u8 = switch (artifact_kind) {
                            .source_text => if (exec_info.output_format == .c) ".c" else ".ll",
                            .executable => active_target.executableExtension(),
                            .object_file => active_target.objectExtension(),
                            .static_library => active_target.defaultStaticLibExtension(),
                            .shared_library => active_target.defaultSharedLibExtension(),
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
                            .link_mode = exec_info.link_mode,
                            .extra_libs = exec_info.extra_libs,
                            .lib_dirs = exec_info.lib_dirs,
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
                        const run_artifact_kind: codegen_abi.OutputArtifactKind =
                            if (exec_info.is_emit_obj) .object_file else .executable;
                        const run_ext = if (exec_info.is_emit_obj)
                            host_target.objectExtension()
                        else
                            host_target.executableExtension();
                        const temp_exe_path = try std.fmt.allocPrint(
                            allocator,
                            "{s}/{s}{s}",
                            .{ scratch_dir, stem, run_ext },
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
                            .artifact_kind = run_artifact_kind,
                            .link_mode = exec_info.link_mode,
                            .extra_libs = exec_info.extra_libs,
                            .lib_dirs = exec_info.lib_dirs,
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

                        if (exec_info.is_emit_obj) {
                            try stdout_style.writeStatusHeader(
                                stdout_writer,
                                .success,
                                Glyphs.SUCCESS,
                                "run",
                                final_exe_path,
                            );
                            try stdout_writer.writeByte('\n');
                            return 0;
                        }

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
    std.debug.assert(SUBCOMMANDS.len == 9);
    std.debug.assert(CLI_SUBCOMMANDS.len == SUBCOMMANDS.len);
    std.debug.assert(SUBCOMMAND_NAME_MAP.keys().len == SUBCOMMANDS.len);
    for (SUBCOMMANDS, 0..) |descriptor, i| {
        std.debug.assert(@backingInt(descriptor.id) == i);
        std.debug.assert(SubcommandId.fromName(descriptor.name) == descriptor.id);
        if (i > 0) {
            std.debug.assert(std.mem.order(u8, SUBCOMMANDS[i - 1].name, descriptor.name) == .lt);
        }
    }
    for (GLOBAL_FLAGS, 0..) |flag_desc, i| {
        std.debug.assert(@backingInt(flag_desc.id) == i);
    }
    std.debug.assert(FMT_FLAGS.len == 3);
    for (FMT_FLAGS, 0..) |fmt_desc, i| {
        std.debug.assert(@backingInt(fmt_desc.id) == i);
    }
    std.debug.assert(UPGRADE_FLAGS.len == 1);
    for (UPGRADE_FLAGS, 0..) |upg_desc, i| {
        std.debug.assert(@backingInt(upg_desc.id) == i);
    }
    std.debug.assert(TRANSLATE_C_FLAGS.len == 5);
    for (TRANSLATE_C_FLAGS, 0..) |tc_desc, i| {
        std.debug.assert(@backingInt(tc_desc.id) == i);
        if (i > 0) {
            std.debug.assert(std.mem.order(u8, TRANSLATE_C_FLAGS[i - 1].long_flag, tc_desc.long_flag) == .lt);
        }
    }
    std.debug.assert(COMPILE_FLAGS.len == 18);
    for (COMPILE_FLAGS, 0..) |comp_desc, i| {
        std.debug.assert(@backingInt(comp_desc.id) == i);
        if (i > 0) {
            std.debug.assert(std.mem.order(u8, COMPILE_FLAGS[i - 1].long_flag, comp_desc.long_flag) == .lt);
        }
    }
}

test "test_cli_router_subcommands_flags_and_typo_suggestions" {
    try std.testing.expectEqual(@as(usize, 9), CLI_SUBCOMMANDS.len);
    try std.testing.expectEqual(@as(usize, 5), TRANSLATE_C_FLAGS.len);
    try std.testing.expectEqual(@as(usize, 18), COMPILE_FLAGS.len);
    try std.testing.expectEqualStrings("build", suggestSubcommand("biuld").?);
    try std.testing.expectEqualStrings("check", suggestSubcommand("chck").?);
    try std.testing.expectEqualStrings("translate-c", suggestSubcommand("translate-x").?);
    try std.testing.expectEqualStrings("--help", suggestGlobalFlag("--hlp").?);
    try std.testing.expectEqualStrings("--version", suggestGlobalFlag("--verison").?);
    try std.testing.expectEqualStrings("--internal-core", suggestFlagForSubcommand("--internal-cor", .build).?);
    try std.testing.expectEqualStrings("--include-dir", suggestFlagForSubcommand("--include-dr", .translate_c).?);

    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    const parsed = try parseArgs(&.{ "--color=never", "check", "main.cx" }, &sink);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(ColorMode.never, parsed.color_mode);
    try std.testing.expect(!parsed.is_internal_core);
    try std.testing.expectEqual(SubcommandId.check, parsed.action.execute_subcommand.subcommand);
    try std.testing.expectEqual(@as(usize, 1), parsed.action.execute_subcommand.positional_args.len);

    const parsed_core = try parseArgs(&.{ "check", "--internal-core", "core/root.cx" }, &sink);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(parsed_core.is_internal_core);
    try std.testing.expect(parsed_core.action.execute_subcommand.is_internal_core);

    // `--check`, `--fix`, and `--internal-core` are valid on `fmt`/`upgrade`, driven by `FMT_FLAGS` & `UPGRADE_FLAGS`:
    try std.testing.expectEqual(@as(usize, 3), FMT_FLAGS.len);
    try std.testing.expectEqual(@as(usize, 1), UPGRADE_FLAGS.len);
    try std.testing.expectEqualStrings("--check", suggestFlagForSubcommand("--chck", .fmt).?);
    try std.testing.expectEqualStrings("--fix", suggestFlagForSubcommand("--fx", .fmt).?);
    try std.testing.expectEqualStrings("--internal-core", suggestFlagForSubcommand("--internal-cor", .fmt).?);
    try std.testing.expectEqualStrings("--internal-core", suggestFlagForSubcommand("--internal-cor", .upgrade).?);

    const parsed_fmt = try parseArgs(&.{ "fmt", "--check", "--fix", "--internal-core" }, &sink);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(parsed_fmt.is_check_only);
    try std.testing.expect(parsed_fmt.is_fix_mode);
    try std.testing.expect(parsed_fmt.is_internal_core);

    // Passing `--check` to a non-`fmt` subcommand emits `E0001`:
    var err_sink = DiagnosticSink.init(std.testing.allocator);
    defer err_sink.deinit();
    const invalid_cmd = try parseArgs(&.{ "build", "--check" }, &err_sink);
    try std.testing.expect(err_sink.hasErrors());
    try std.testing.expectEqual(CommandAction.invalid, invalid_cmd.action);
}

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
const syntax_arenas = @import("../syntax_arenas.zig");
const parser = @import("../parser.zig");
const symbol_resolver = @import("../symbol_resolver.zig");
const mir_sast = @import("../mir_sast.zig");
const pkg_manifest = @import("../pkg_manifest.zig");
const pkg_cache = @import("../pkg_cache.zig");
const pkg_resolver = @import("../pkg_resolver.zig");

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
        if (std.mem.eql(u8, raw_format, "c")) {
            return .c;
        } else if (std.mem.eql(u8, raw_format, "llvm")) {
            return .llvm;
        }
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
    /// `--features=<feat,…>` / `-F` – activate package feature flags (`7`).
    features = 7,
    /// `--frozen` – require up-to-date `corex.lock` and warm offline cache (`8`).
    frozen = 8,
    /// `--fuzz` – instrument output with `SanitizerCoverage` edge counters (`9`).
    fuzz = 9,
    /// `--include-dir=<dir>` / `-I` – add C `#include` search directory (`10`).
    include_dir = 10,
    /// `--internal-core` – permit direct `core.*` kernel imports without `E0218` (`11`).
    internal_core = 11,
    /// `--lib=<name_or_def>` / `-l` – link C library or `.def`/`.lib`/`.a` input (`12`).
    lib = 12,
    /// `--lib-dir=<dir>` / `-L` – add library search directory (`13`).
    lib_dir = 13,
    /// `--link=<auto|static|dynamic>` – configure binary linkage mode (`14`).
    link = 14,
    /// `--locked` – require `corex.lock` to match `corex.toml` without modifying lockfile (`15`).
    locked = 15,
    /// `--manifest-path=<path>` – explicit path to `corex.toml` or single-file `.cx` script (`16`).
    manifest_path = 16,
    /// `--no-default-features` – do not activate the `default` feature on the target package (`17`).
    no_default_features = 17,
    /// `--offline` – resolve and build strictly from local `COREX_HOME` cache (`18`).
    offline = 18,
    /// `--ofmt=<c|llvm>` – select Tier A (`c`) or Tier B (`llvm`) codegen backend (`19`).
    ofmt = 19,
    /// `--output=<path>` / `-o` – write compiled artifact to `<path>` (`20`).
    output = 20,
    /// `--release` – compile in production release mode (`21`).
    release = 21,
    /// `--sast-strict` – emit `W0314` warnings on unproven bounds checks (`22`).
    sast_strict = 22,
    /// `--target=<triple>` – select cross-compilation target triple (`23`).
    target = 23,
    /// `--verify-checksums` – re-verify `BLAKE3` digests of all cached `.cxtree` and blob artifacts (`24`).
    verify_checksums = 24,
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

/// Resolved subcommand execution payload carried inside `CommandAction.execute_subcommand`.
pub const ExecuteSubcommandAction = struct {
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
    /// Arena-allocated `-F` / `--features` package feature tokens.
    features: []const []const u8 = &.{},
    /// Optional explicit `--manifest-path=<path>` pointing to `corex.toml` or `.cx` script.
    manifest_path: ?[]const u8 = null,
    /// Whether `--locked` (or `--frozen`) was passed.
    is_locked: bool = false,
    /// Whether `--offline` (or `--frozen`) was passed.
    is_offline: bool = false,
    /// Whether `--frozen` was passed.
    is_frozen: bool = false,
    /// Whether `--no-default-features` was passed.
    has_no_default_features: bool = false,
    /// Whether `--verify-checksums` was passed.
    is_verifying_checksums: bool = false,
};

/// Resolved CLI action produced by `parseArgs`.
pub const CommandAction = union(enum) {
    /// Render the global or subcommand-specific `--help` menu and exit `0`.
    show_help: ?SubcommandId,
    /// Render the `--version` banner and exit `0`.
    show_version: void,
    /// Execute the selected `subcommand` with remaining `positional_args`.
    execute_subcommand: ExecuteSubcommandAction,
    /// Invalid CLI invocation; errors have been emitted into `DiagnosticSink`.
    invalid: void,
};

/// Resolved `COREX_HOME` and `COREX_HERMETIC` environment variables (`DR-11` §3.5).
pub const ToolchainEnvConfig = struct {
    /// Owned `COREX_HOME` cache root directory path.
    corex_home_dir: []u8,
    /// `true` when `COREX_HERMETIC=1` is set (`--frozen` + `--offline` + zero ambient nondeterminism).
    is_hermetic: bool = false,

    /// Releases `corex_home_dir` back to `allocator`.
    pub fn deinit(self: *ToolchainEnvConfig, allocator: std.mem.Allocator) void {
        allocator.free(self.corex_home_dir);
        self.* = undefined;
    }
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
    /// Arena-allocated `-F` / `--features` package feature tokens.
    features: []const []const u8 = &.{},
    /// Optional explicit `--manifest-path=<path>`.
    manifest_path: ?[]const u8 = null,
    /// Whether `--locked` (or `--frozen`) was passed.
    is_locked: bool = false,
    /// Whether `--offline` (or `--frozen`) was passed.
    is_offline: bool = false,
    /// Whether `--frozen` was passed.
    is_frozen: bool = false,
    /// Whether `--no-default-features` was passed.
    has_no_default_features: bool = false,
    /// Whether `--verify-checksums` was passed.
    is_verifying_checksums: bool = false,
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
        .id = .features,
        .short_flag = "-F",
        .long_flag = "--features",
        .value_suffix = "=<feat,…>",
        .summary = "Space- or comma-separated package features to activate",
    },
    .{
        .id = .frozen,
        .long_flag = "--frozen",
        .value_suffix = null,
        .summary = "Require up-to-date `corex.lock` and warm offline cache",
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
        .id = .locked,
        .long_flag = "--locked",
        .value_suffix = null,
        .summary = "Require `corex.lock` to match `corex.toml` without modifying lockfile",
    },
    .{
        .id = .manifest_path,
        .long_flag = "--manifest-path",
        .value_suffix = "=<path>",
        .summary = "Explicit path to `corex.toml` or single-file `.cx` script",
    },
    .{
        .id = .no_default_features,
        .long_flag = "--no-default-features",
        .value_suffix = null,
        .summary = "Do not activate the `default` feature on the target package",
    },
    .{
        .id = .offline,
        .long_flag = "--offline",
        .value_suffix = null,
        .summary = "Resolve and build strictly from local `COREX_HOME` cache",
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
    .{
        .id = .verify_checksums,
        .long_flag = "--verify-checksums",
        .value_suffix = null,
        .summary = "Re-verify BLAKE3 digests of all cached `.cxtree` and blob artifacts",
    },
};

/// Maximum CLI `-F` / `--features` tokens accepted per invocation (`AGENTS.md` §2).
const MAX_CLI_FEATURES: usize = 256;
/// Maximum parent directory hops searched upward when discovering `corex.toml`.
const MAX_MANIFEST_ANCESTOR_HOPS: usize = 64;

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
    pkg_files_out: ?*std.ArrayListUnmanaged(mem.FileId),
    has_core_mention_out: *bool,
    depth: u32,
) !void {
    if (depth >= MAX_MODULE_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return;
    try visited_fids.put(allocator, parent_fid.asInt(), {});
    if (pkg_files_out) |out_list| {
        try out_list.append(allocator, parent_fid);
    }

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
        for ((try db.extractItemTree(parent_fid)).entries) |entry| {
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
                    pkg_files_out,
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
        null,
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

        var entry_idx: usize = 0;
        while (entry_idx < (try db.extractItemTree(mod_fid)).entries.len) : (entry_idx += 1) {
            const entry = (try db.extractItemTree(mod_fid)).entries[entry_idx];
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
    var seen_include_dirs: std.StringHashMapUnmanaged(void) = .empty;
    defer seen_include_dirs.deinit(allocator);
    for (include_dirs) |inc_dir| {
        if (!(try seen_include_dirs.getOrPut(allocator, inc_dir)).found_existing) {
            try effective_include_dirs.append(allocator, inc_dir);
        }
    }
    const header_dir = std.fs.path.dirname(header_path) orelse ".";
    if (!seen_include_dirs.contains(header_dir)) {
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

/// Splits a comma- or whitespace-separated `-F` / `--features` string into `out_features` (`<= MAX_CLI_FEATURES`).
fn extractCliFeatureTokens(
    arena_alloc: std.mem.Allocator,
    raw_spec: []const u8,
    out_features: *std.ArrayListUnmanaged([]const u8),
) !void {
    var seen_features: std.StringHashMapUnmanaged(void) = .empty;
    defer seen_features.deinit(arena_alloc);
    for (out_features.items) |existing_feat| {
        try seen_features.put(arena_alloc, existing_feat, {});
    }

    var cursor: usize = 0;
    while (cursor < raw_spec.len and out_features.items.len < MAX_CLI_FEATURES) {
        while (cursor < raw_spec.len and
            (raw_spec[cursor] == ',' or std.ascii.isWhitespace(raw_spec[cursor]))) : (cursor += 1)
        {}
        const start = cursor;
        while (cursor < raw_spec.len and
            raw_spec[cursor] != ',' and !std.ascii.isWhitespace(raw_spec[cursor])) : (cursor += 1)
        {}
        if (cursor > start) {
            const token_slice = raw_spec[start..cursor];
            if (!seen_features.contains(token_slice)) {
                const duped_feat = try arena_alloc.dupe(u8, token_slice);
                try seen_features.put(arena_alloc, duped_feat, {});
                try out_features.append(arena_alloc, duped_feat);
            }
        }
    }
}

/// Walks upward from `start_dir` up to `MAX_MANIFEST_ANCESTOR_HOPS` directories looking for `corex.toml`.
fn discoverNearestManifestFromDirUpward(
    allocator: std.mem.Allocator,
    io: std.Io,
    start_dir: []const u8,
) !?[]u8 {
    const start_real = std.Io.Dir.cwd().realPathFileAlloc(io, start_dir, allocator) catch {
        const fallback_toml = try std.fs.path.join(allocator, &.{ start_dir, "corex.toml" });
        if (std.Io.Dir.cwd().openFile(io, fallback_toml, .{ .mode = .read_only })) |local_file| {
            local_file.close(io);
            return fallback_toml;
        } else |_| {
            allocator.free(fallback_toml);
            return null;
        }
    };
    defer allocator.free(start_real);

    var cur_dir: []const u8 = start_real;
    var hop: usize = 0;
    while (hop < MAX_MANIFEST_ANCESTOR_HOPS) : (hop += 1) {
        const cand_toml = try std.fs.path.join(allocator, &.{ cur_dir, "corex.toml" });
        if (std.Io.Dir.cwd().openFile(io, cand_toml, .{ .mode = .read_only })) |opened| {
            opened.close(io);
            return cand_toml;
        } else |_| {
            allocator.free(cand_toml);
        }
        const parent_opt = std.fs.path.dirname(cur_dir) orelse break;
        if (std.mem.eql(u8, parent_opt, cur_dir)) break;
        cur_dir = parent_opt;
    }
    return null;
}

/// Walks upward from `.` up to `MAX_MANIFEST_ANCESTOR_HOPS` directories looking for `corex.toml`.
fn discoverNearestManifestUpward(allocator: std.mem.Allocator, io: std.Io) !?[]u8 {
    return discoverNearestManifestFromDirUpward(allocator, io, ".");
}

/// Returns `true` when `cx_path` is a `src/` or configured entry/member source file of `toml_path`.
fn isCxFileOwnedByManifest(
    allocator: std.mem.Allocator,
    io: std.Io,
    interner: *mem.StringInterner,
    source_map: *vfs.VfsSourceMap,
    toml_path: []const u8,
    cx_path: []const u8,
    cfg_env: *const symbol_resolver.CfgEnv,
) !bool {
    const raw_canon_cx = std.Io.Dir.cwd().realPathFileAlloc(io, cx_path, allocator) catch return false;
    defer allocator.free(raw_canon_cx);
    const norm_cx = try allocator.alloc(u8, raw_canon_cx.len);
    defer allocator.free(norm_cx);
    for (raw_canon_cx, 0..) |ch_val, i| {
        norm_cx[i] = if (ch_val == '\\') '/' else ch_val;
    }

    if (std.Io.Dir.cwd().realPathFileAlloc(io, std.fs.path.dirname(toml_path) orelse ".", allocator)) |raw_canon_toml_dir| {
        defer allocator.free(raw_canon_toml_dir);
        const norm_toml_dir = try allocator.alloc(u8, raw_canon_toml_dir.len);
        defer allocator.free(norm_toml_dir);
        for (raw_canon_toml_dir, 0..) |ch_val, i| {
            norm_toml_dir[i] = if (ch_val == '\\') '/' else ch_val;
        }
        const src_prefix = try std.fmt.allocPrint(allocator, "{s}/src/", .{std.mem.trimEnd(u8, norm_toml_dir, "/")});
        defer allocator.free(src_prefix);
        if (std.mem.startsWith(u8, norm_cx, src_prefix)) return true;
    } else |_| {}

    var probe_sink = DiagnosticSink.init(allocator);
    defer probe_sink.deinit();
    const toml_fid = (loadSourceFileIntoVfs(io, source_map, toml_path, &probe_sink) catch null) orelse return false;
    var bundle = pkg_manifest.loadWorkspaceManifestBundle(
        io,
        allocator,
        interner,
        toml_path,
        toml_fid,
        cfg_env,
        &probe_sink,
    ) catch return false;
    defer bundle.deinit();
    if (probe_sink.hasErrors()) return false;

    for (bundle.members) |member| {
        if (std.Io.Dir.cwd().realPathFileAlloc(io, member.abs_dir, allocator)) |raw_mem_dir| {
            defer allocator.free(raw_mem_dir);
            const norm_mem_dir = try allocator.alloc(u8, raw_mem_dir.len);
            defer allocator.free(norm_mem_dir);
            for (raw_mem_dir, 0..) |ch_val, i| {
                norm_mem_dir[i] = if (ch_val == '\\') '/' else ch_val;
            }
            const mem_src_prefix = try std.fmt.allocPrint(allocator, "{s}/src/", .{std.mem.trimEnd(u8, norm_mem_dir, "/")});
            defer allocator.free(mem_src_prefix);
            if (std.mem.startsWith(u8, norm_cx, mem_src_prefix)) return true;
        } else |_| {}

        var cand_rels: [8][]const u8 = undefined;
        var cand_len: usize = 0;
        if (member.manifest.package) |pkg_meta| {
            if (pkg_meta.root_module != .empty and cand_len < cand_rels.len) {
                cand_rels[cand_len] = interner.get(pkg_meta.root_module);
                cand_len += 1;
            }
        }
        if (member.manifest.lib_target) |lib_tgt| {
            if (lib_tgt.path != .empty and cand_len < cand_rels.len) {
                cand_rels[cand_len] = interner.get(lib_tgt.path);
                cand_len += 1;
            }
        }
        for (member.manifest.bin_targets) |bin_tgt| {
            if (bin_tgt.path != .empty and cand_len < cand_rels.len) {
                cand_rels[cand_len] = interner.get(bin_tgt.path);
                cand_len += 1;
            }
        }
        for (cand_rels[0..cand_len]) |rel_entry| {
            const joined = try std.fs.path.join(allocator, &.{ member.abs_dir, rel_entry });
            defer allocator.free(joined);
            if (std.Io.Dir.cwd().realPathFileAlloc(io, joined, allocator)) |canon_entry| {
                defer allocator.free(canon_entry);
                var is_match = canon_entry.len == norm_cx.len;
                if (is_match) {
                    for (canon_entry, 0..) |ch_val, i| {
                        const norm_ch: u8 = if (ch_val == '\\') '/' else ch_val;
                        if (norm_ch != norm_cx[i]) {
                            is_match = false;
                            break;
                        }
                    }
                }
                if (is_match) return true;
            } else |_| {}
        }
    }
    return false;
}

/// Recursively discovers and binds `mod <name>;` submodules inside a mounted virtual `/cx/<pkg>@<ver>/…` `.cxtree`.
fn discoverVirtualCxTreeSubmodulesRecursive(
    allocator: std.mem.Allocator,
    source_map: *vfs.VfsSourceMap,
    db: *query_db.CompilerDb,
    parent_fid: mem.FileId,
    parent_vpath: []const u8,
    pkg_id: vfs.PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    pkg_files_out: *std.ArrayListUnmanaged(mem.FileId),
    has_core_mention_out: *bool,
    sink: *DiagnosticSink,
    depth: u32,
) !bool {
    if (depth >= MAX_MODULE_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return true;
    try visited_fids.put(allocator, parent_fid.asInt(), {});
    try pkg_files_out.append(allocator, parent_fid);

    const parent_src = source_map.faultCxTreeFile(parent_fid) catch |fault_err| {
        if (fault_err == error.CacheIntegrityMismatch) {
            try sink.emit(.{
                .code = .e0015_cache_integrity_mismatch,
                .severity = .err,
                .primary_span = mem.Span.init(parent_fid, 0, 0),
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "cached `.cxtree` source blob `{s}` failed BLAKE3 integrity verification",
                    .{parent_vpath},
                ),
            });
        } else {
            try sink.emit(.{
                .code = .e0004_source_file_io_error,
                .severity = .err,
                .primary_span = mem.Span.init(parent_fid, 0, 0),
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "failed to read `.cxtree` module `{s}`",
                    .{parent_vpath},
                ),
            });
        }
        return false;
    };
    _ = source_map.getLineIndex(parent_fid) catch {};
    if (!has_core_mention_out.* and
        (std.mem.indexOf(u8, parent_src, "cx") != null or std.mem.indexOf(u8, parent_src, "core") != null))
    {
        has_core_mention_out.* = true;
    }

    _ = try db.setInput(parent_fid, parent_src, .high);
    try db.setFilePackageId(parent_fid, pkg_id);
    try db.setFilePath(parent_fid, parent_vpath);

    var ext_mod_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer ext_mod_names.deinit(allocator);
    {
        const parsed_art = try db.parseCst(parent_fid);
        for ((try db.extractItemTree(parent_fid)).entries) |entry| {
            if (entry.kind != .mod_decl or entry.name_text.len == 0) continue;
            if (!entry.ast_node.isNone() and
                parsed_art.ast_arena.getNode(entry.ast_node).rhs.tag == .extra)
            {
                continue;
            }
            try ext_mod_names.append(allocator, entry.name_text);
        }
    }

    const parent_dir = std.fs.path.dirname(parent_vpath) orelse "";
    const parent_base = std.fs.path.basename(parent_vpath);
    const parent_stem = std.fs.path.stem(parent_vpath);
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
        cand_paths[cand_len] = try std.fmt.allocPrint(allocator, "{s}/{s}.cx", .{ parent_dir, mod_name });
        cand_len += 1;
        cand_paths[cand_len] = try std.fmt.allocPrint(allocator, "{s}/{s}/mod.cx", .{ parent_dir, mod_name });
        cand_len += 1;

        var idx: usize = 0;
        while (idx < cand_len) : (idx += 1) {
            const cand_vpath = cand_paths[idx].?;
            const vpath_id = source_map.interner.lookup(cand_vpath) orelse continue;
            const child_fid = source_map.path_to_file_id.get(vpath_id) orelse continue;
            try db.bindExternalModule(parent_fid, mod_name, child_fid);
            if (!(try discoverVirtualCxTreeSubmodulesRecursive(
                allocator,
                source_map,
                db,
                child_fid,
                cand_vpath,
                pkg_id,
                visited_fids,
                pkg_files_out,
                has_core_mention_out,
                sink,
                depth + 1,
            ))) return false;
            break;
        }
    }
    return true;
}

/// Scans a `.cx` source buffer for active inline `use "…" as …;` imports and bare top-level `use <root>…;` identifiers.
fn scanRootCxSourceImports(
    allocator: std.mem.Allocator,
    interner: *mem.StringInterner,
    cfg_env: *const symbol_resolver.CfgEnv,
    file_id: mem.FileId,
    source: []const u8,
    inline_out: *std.ArrayListUnmanaged(symbol_resolver.InlineUseImport),
    bare_roots_out: *std.ArrayListUnmanaged([]u8),
    sink: *DiagnosticSink,
) !void {
    var tok_buf = syntax_arenas.TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = syntax_arenas.LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = syntax_arenas.AstArena.init(allocator);
    defer ast_arena.deinit();
    var local_parse_sink = DiagnosticSink.init(allocator);
    defer local_parse_sink.deinit();

    _ = try parser.parseSource(
        source,
        file_id,
        &tok_buf,
        &cst_arena,
        &ast_arena,
        &local_parse_sink,
        interner,
    );

    const extracted_inlines = try symbol_resolver.extractActiveInlineUseImports(
        allocator,
        interner,
        cfg_env,
        file_id,
        source,
        &tok_buf,
        &cst_arena,
        sink,
    );
    defer allocator.free(extracted_inlines);
    for (extracted_inlines) |inl_item| {
        try inline_out.append(allocator, inl_item);
    }

    // Collect first identifier segment of bare `use <ident>…;` declarations for zero-friction auto-sync:
    var seen_bare_roots: std.StringHashMapUnmanaged(void) = .empty;
    defer seen_bare_roots.deinit(allocator);
    for (bare_roots_out.items) |existing_root| {
        try seen_bare_roots.put(allocator, existing_root, {});
    }
    var cursor: usize = 0;
    const node_cnt = cst_arena.countNodes();
    while (cursor < node_cnt) : (cursor += 1) {
        const node_id = mem.CstNodeIndex.fromInt(@intCast(cursor));
        const node = cst_arena.getNode(node_id);
        if (node.kind != .use_item) continue;
        if (parser.extractInlineUseDeclView(source, file_id, &tok_buf, &cst_arena, node_id, .none) != null) {
            cursor += @max(@as(usize, node.subtree_size), 1) - 1;
            continue;
        }
        const sub_end = @min(cursor + @max(@as(usize, node.subtree_size), 1), node_cnt);
        var sub_cur = cursor + 1;
        while (sub_cur < sub_end) : (sub_cur += 1) {
            const sub_node = cst_arena.getNode(mem.CstNodeIndex.fromInt(@intCast(sub_cur)));
            if (sub_node.kind != .use_tree) continue;
            const tree_end = @min(sub_cur + @max(@as(usize, sub_node.subtree_size), 1), sub_end);
            var leaf_cur = sub_cur + 1;
            while (leaf_cur < tree_end) : (leaf_cur += 1) {
                const leaf = cst_arena.getNode(mem.CstNodeIndex.fromInt(@intCast(leaf_cur)));
                if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
                    !leaf.token.isNone() and leaf.token.asInt() < tok_buf.countTokens())
                {
                    const tok_rec = tok_buf.getToken(leaf.token);
                    if (tok_rec.kind == .ident) {
                        const seg_slice = source[tok_rec.byte_offset .. tok_rec.byte_offset + tok_rec.byte_len];
                        if (!pkg_manifest.RESERVED_PKG_NAME_MAP.has(seg_slice) and !seen_bare_roots.contains(seg_slice)) {
                            const duped_root = try allocator.dupe(u8, seg_slice);
                            try seen_bare_roots.put(allocator, duped_root, {});
                            try bare_roots_out.append(allocator, duped_root);
                        }
                        break;
                    }
                }
            }
            break;
        }
        cursor = sub_end - 1;
    }
}

/// Mounted executable `[[bin]]` target entry for `.root` multi-binary workspaces.
const RootBinEntry = struct {
    /// Executable binary target name (`[[bin]].name` or `pkg_node.canonical_name`).
    bin_name: []const u8,
    /// Mounted `FileId` of the binary entry `.cx` file.
    bin_fid: mem.FileId,
};

/// Resolves, mounts, verifies, locks, and compiles/runs/tests a Mode-A (`corex.toml`) or Mode-B (`.cx` script) project.
fn executePackageOrScriptWorkflow(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    source_map: *vfs.VfsSourceMap,
    interner: *mem.StringInterner,
    sink: *DiagnosticSink,
    exec_info: ExecuteSubcommandAction,
    env_cfg: ToolchainEnvConfig,
    manifest_bundle: *pkg_manifest.WorkspaceManifestBundle,
    lockfile_path: []const u8,
    script_entry_fid: ?mem.FileId,
    script_entry_path: ?[]const u8,
    pre_scanned_inlines: []const symbol_resolver.InlineUseImport,
    pre_scanned_bare_roots: []const []const u8,
    stdout_style: StyleConfig,
    stderr_style: StyleConfig,
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
) !u8 {
    const diag_renderer = DiagnosticRenderer.init(source_map, interner, stderr_style);
    const active_target = exec_info.target_spec orelse codegen_abi.TargetSpec.host();
    const is_effective_frozen = exec_info.is_frozen or env_cfg.is_hermetic;
    const is_effective_locked = exec_info.is_locked or is_effective_frozen;
    const is_effective_offline = exec_info.is_offline or is_effective_frozen;

    // [1] Parse existing `corex.lock` if present on disk:
    var lock_arena = mem.BumpArena.init(allocator);
    defer lock_arena.deinit();
    var existing_lock_val: ?pkg_manifest.Lockfile = null;
    if (std.Io.Dir.cwd().readFileAlloc(
        io,
        lockfile_path,
        allocator,
        .limited(pkg_manifest.MAX_TOML_BYTES),
    )) |lock_bytes| {
        defer allocator.free(lock_bytes);
        const lock_fid = try source_map.setOverlay(lockfile_path, lock_bytes, .root);
        _ = try source_map.getLineIndex(lock_fid);
        existing_lock_val = try pkg_manifest.parseLockfile(
            allocator,
            &lock_arena,
            interner,
            lock_fid,
            lock_bytes,
            if (is_effective_locked) manifest_bundle.root_manifest_blake3 else null,
            sink,
        );
        if (sink.hasErrors()) {
            try diag_renderer.renderAll(stderr_writer, sink);
            return 1;
        }
    } else |_| {}

    // [2] Resolve full dependency graph (`Bounded-MVS` -> `PubGrub CDCL` + cryptographic CAS checks):
    var resolved_opt = try pkg_resolver.resolveProjectGraph(
        allocator,
        interner,
        source_map,
        manifest_bundle,
        if (existing_lock_val) |*lck| lck else null,
        .{
            .io = io,
            .target_spec = active_target,
            .cli_features = exec_info.features,
            .has_no_default_features = exec_info.has_no_default_features,
            .is_including_tests = exec_info.subcommand == .@"test",
            .is_locked = is_effective_locked,
            .is_offline = is_effective_offline,
            .is_frozen = is_effective_frozen,
            .is_verifying_checksums = exec_info.is_verifying_checksums,
            .corex_home_dir = env_cfg.corex_home_dir,
            .environ_map = environ_map,
            .inline_imports = pre_scanned_inlines,
            .unresolved_use_roots = pre_scanned_bare_roots,
        },
        sink,
    );
    if (resolved_opt == null or sink.hasErrors()) {
        if (resolved_opt) |*res_g| res_g.deinit(allocator);
        try diag_renderer.renderAll(stderr_writer, sink);
        return 1;
    }
    var resolved = resolved_opt.?;
    defer resolved.deinit(allocator);

    // Refresh `root_manifest_blake3` if unlocked auto-sync updated `corex.toml` on disk:
    var active_manifest_b3 = manifest_bundle.root_manifest_blake3;
    if (resolved.has_auto_synced_manifest and !manifest_bundle.is_script) {
        const cfg_for_reload = symbol_resolver.CfgEnv.fromTargetSpec(active_target, exec_info.subcommand == .@"test");
        var reloaded = try pkg_manifest.loadWorkspaceManifestBundle(
            io,
            allocator,
            interner,
            manifest_bundle.root_manifest_path,
            manifest_bundle.root_manifest.file_id,
            &cfg_for_reload,
            null,
        );
        defer reloaded.deinit();
        active_manifest_b3 = reloaded.root_manifest_blake3;
    }

    // [3] Mount all resolved packages into `VfsSourceMap` & `CompilerDb`:
    var cache = try pkg_cache.PkgCache.init(
        allocator,
        env_cfg.corex_home_dir,
        pkg_cache.DEFAULT_MAX_LRU_ENTRIES,
        pkg_cache.DEFAULT_MAX_LRU_BYTES,
    );
    defer cache.deinit();
    const blobs_dir = try std.fmt.allocPrint(allocator, "{s}/blobs", .{cache.cas_root});
    defer allocator.free(blobs_dir);

    var db = try query_db.CompilerDb.init(allocator);
    defer db.deinit();
    db.setPackageGraphMounted(true);
    db.setVfsSourceMap(source_map);
    db.setSastStrict(exec_info.is_sast_strict);
    if (exec_info.is_internal_core) {
        try db.setInternalCore(true);
    }
    db.setIncludeTests(exec_info.subcommand == .@"test");
    db.setComptimeStepLimit(exec_info.comptime_step_limit);
    db.setEmbedSandbox(manifest_bundle.workspace_root_dir, null);
    db.setEmbedIo(io);
    db.setTargetSpec(active_target);

    if (exec_info.c_defines.len > 0 or exec_info.include_dirs.len > 0) {
        var raw_defs: std.ArrayListUnmanaged([]u8) = .empty;
        defer {
            for (raw_defs.items) |owned_d| allocator.free(owned_d);
            raw_defs.deinit(allocator);
        }
        for (exec_info.c_defines) |mdef| {
            if (mdef.value) |mval| {
                try raw_defs.append(allocator, try std.fmt.allocPrint(allocator, "{s}={s}", .{ mdef.name, mval }));
            } else {
                try raw_defs.append(allocator, try allocator.dupe(u8, mdef.name));
            }
        }
        try db.setCImportConfig(raw_defs.items, exec_info.include_dirs);
    }

    var visited_fids: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited_fids.deinit(allocator);
    var has_core_mention = false;

    var pkg_root_fids: std.AutoHashMapUnmanaged(vfs.PackageId, mem.FileId) = .empty;
    defer pkg_root_fids.deinit(allocator);
    var pkg_files_owned: std.AutoHashMapUnmanaged(vfs.PackageId, std.ArrayListUnmanaged(mem.FileId)) = .empty;
    defer {
        var pf_it = pkg_files_owned.valueIterator();
        while (pf_it.next()) |list_ptr| list_ptr.deinit(allocator);
        pkg_files_owned.deinit(allocator);
    }
    var pkg_order: std.ArrayListUnmanaged(vfs.PackageId) = .empty;
    defer pkg_order.deinit(allocator);

    var root_bin_entries: std.ArrayListUnmanaged(RootBinEntry) = .empty;
    defer root_bin_entries.deinit(allocator);
    var root_lib_fid_opt: ?mem.FileId = null;
    var root_lib_custom_snake: ?[]const u8 = null;

    var primary_root_fid: mem.FileId = .none;
    var primary_stem: []const u8 = "app";

    for (resolved.packages) |pkg_node| {
        try pkg_order.append(allocator, pkg_node.pkg_id);
        const files_gop = try pkg_files_owned.getOrPut(allocator, pkg_node.pkg_id);
        if (!files_gop.found_existing) files_gop.value_ptr.* = .empty;

        const ver_str = try pkg_node.version.formatAlloc(allocator, interner);
        defer allocator.free(ver_str);

        const is_virtual_cxtree = (pkg_node.pkg_id != .root) and
            (pkg_node.source_kind != .workspace_member) and
            (pkg_node.source_kind != .local_path) and
            (pkg_node.cxtree_blake3 != null);

        var node_root_fid: mem.FileId = .none;
        if (is_virtual_cxtree) {
            const cxtree_bytes = cache.readVerifiedCxTreeAlloc(
                io,
                pkg_node.cxtree_blake3.?,
                sink,
                pkg_node.manifest_span,
            ) catch |cx_err| {
                if (cx_err != error.CacheIntegrityMismatch) {
                    try sink.emit(.{
                        .code = if (is_effective_offline) .e0016_offline_or_fetch_failed else .e0015_cache_integrity_mismatch,
                        .severity = .err,
                        .primary_span = pkg_node.manifest_span,
                        .message = "missing or unreadable `.cxtree` package manifest in `COREX_HOME`",
                    });
                }
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            };
            defer allocator.free(cxtree_bytes);

            if (exec_info.is_verifying_checksums) {
                if (vfs.validateCxTreeBytes(allocator, cxtree_bytes)) |view| {
                    for (view.entries) |t_entry| {
                        const verified_b = cache.readVerifiedBlobAlloc(
                            io,
                            t_entry.file_blake3,
                            sink,
                            pkg_node.manifest_span,
                        ) catch {
                            if (!sink.hasErrors()) {
                                try sink.emit(.{
                                    .code = .e0015_cache_integrity_mismatch,
                                    .severity = .err,
                                    .primary_span = pkg_node.manifest_span,
                                    .message = "missing or corrupt cached blob during `--verify-checksums`",
                                });
                            }
                            try diag_renderer.renderAll(stderr_writer, sink);
                            return 1;
                        };
                        defer allocator.free(verified_b);
                        if (verified_b.len != @as(usize, t_entry.file_size)) {
                            try sink.emit(.{
                                .code = .e0015_cache_integrity_mismatch,
                                .severity = .err,
                                .primary_span = pkg_node.manifest_span,
                                .message = "cached blob byte length does not match `.cxtree` `file_size`",
                            });
                            try diag_renderer.renderAll(stderr_writer, sink);
                            return 1;
                        }
                        const hex = std.fmt.bytesToHex(t_entry.file_blake3, .lower);
                        const obao_primary = try std.fmt.allocPrint(
                            allocator,
                            "{s}/{s}/{s}.obao",
                            .{ blobs_dir, hex[0..2], hex[2..64] },
                        );
                        defer allocator.free(obao_primary);
                        const obao_opt: ?[]u8 = std.Io.Dir.cwd().readFileAlloc(
                            io,
                            obao_primary,
                            allocator,
                            .limited(pkg_cache.MAX_CACHED_BLOB_BYTES),
                        ) catch |obao_err| blk_obao: {
                            if (obao_err != error.FileNotFound) {
                                try sink.emit(.{
                                    .code = .e0015_cache_integrity_mismatch,
                                    .severity = .err,
                                    .primary_span = pkg_node.manifest_span,
                                    .message = "unreadable companion `.obao` Bao outboard file in `COREX_HOME`",
                                });
                                try diag_renderer.renderAll(stderr_writer, sink);
                                return 1;
                            }
                            const obao_fallback = try std.fmt.allocPrint(
                                allocator,
                                "{s}/{s}/{s}/{s}.obao",
                                .{ blobs_dir, hex[0..2], hex[2..4], hex[0..64] },
                            );
                            defer allocator.free(obao_fallback);
                            break :blk_obao std.Io.Dir.cwd().readFileAlloc(
                                io,
                                obao_fallback,
                                allocator,
                                .limited(pkg_cache.MAX_CACHED_BLOB_BYTES),
                            ) catch |fb_err| {
                                if (fb_err != error.FileNotFound or verified_b.len >= pkg_cache.BAO_OUTBOARD_MIN_BYTES) {
                                    try sink.emit(.{
                                        .code = .e0015_cache_integrity_mismatch,
                                        .severity = .err,
                                        .primary_span = pkg_node.manifest_span,
                                        .message = "missing or unreadable `.obao` Bao outboard for `>= 64 KiB` cached blob",
                                    });
                                    try diag_renderer.renderAll(stderr_writer, sink);
                                    return 1;
                                }
                                break :blk_obao null;
                            };
                        };
                        if (obao_opt) |obao_bytes| {
                            defer allocator.free(obao_bytes);
                            pkg_cache.verifyBaoOutboard(
                                t_entry.file_blake3,
                                obao_bytes,
                                verified_b,
                                sink,
                                pkg_node.manifest_span,
                            ) catch {
                                try diag_renderer.renderAll(stderr_writer, sink);
                                return 1;
                            };
                        }
                    }
                } else |_| {
                    try sink.emit(.{
                        .code = .e0015_cache_integrity_mismatch,
                        .severity = .err,
                        .primary_span = pkg_node.manifest_span,
                        .message = "cached `.cxtree` failed `--verify-checksums` structural validation",
                    });
                    try diag_renderer.renderAll(stderr_writer, sink);
                    return 1;
                }
            }

            const mounted_ids = try source_map.mountCxTreePackage(
                io,
                pkg_node.pkg_id,
                pkg_node.canonical_name,
                ver_str,
                cxtree_bytes,
                blobs_dir,
            );
            defer allocator.free(mounted_ids);

            const entry_rel = pkg_node.lib_root_rel_path orelse pkg_node.bin_root_rel_path orelse "src/root.cx";
            const entry_vpath = try std.fmt.allocPrint(
                allocator,
                "/cx/{s}@{s}/{s}",
                .{ pkg_node.canonical_name, ver_str, entry_rel },
            );
            defer allocator.free(entry_vpath);

            const vpath_id = source_map.interner.lookup(entry_vpath) orelse {
                try sink.emit(.{
                    .code = .e0013_invalid_manifest_or_pkg_name,
                    .severity = .err,
                    .primary_span = pkg_node.manifest_span,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "package `{s}` is missing entry module `{s}` inside `.cxtree`",
                        .{ pkg_node.canonical_name, entry_rel },
                    ),
                });
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            };
            node_root_fid = source_map.path_to_file_id.get(vpath_id) orelse .none;
            if (node_root_fid.isNone()) {
                try sink.emit(.{
                    .code = .e0004_source_file_io_error,
                    .severity = .err,
                    .primary_span = pkg_node.manifest_span,
                    .message = "failed to resolve mounted `.cxtree` root `FileId`",
                });
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            }
            if (!(try discoverVirtualCxTreeSubmodulesRecursive(
                allocator,
                source_map,
                &db,
                node_root_fid,
                entry_vpath,
                pkg_node.pkg_id,
                &visited_fids,
                files_gop.value_ptr,
                &has_core_mention,
                sink,
                0,
            ))) {
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            }
            const virtual_prefix = try std.fmt.allocPrint(
                allocator,
                "/cx/{s}@{s}",
                .{ pkg_node.canonical_name, ver_str },
            );
            defer allocator.free(virtual_prefix);
            try db.setPackageEmbedJail(pkg_node.pkg_id, .{
                .cxtree_only = .{
                    .pkg_id = pkg_node.pkg_id,
                    .virtual_root_prefix = virtual_prefix,
                },
            });
        } else if (pkg_node.pkg_id == .root and script_entry_fid != null) {
            node_root_fid = script_entry_fid.?;
            const s_path = script_entry_path.?;
            primary_stem = std.fs.path.stem(s_path);
            try discoverExternalSubmodulesRecursive(
                allocator,
                io,
                source_map,
                &db,
                node_root_fid,
                s_path,
                .low,
                .root,
                &visited_fids,
                files_gop.value_ptr,
                &has_core_mention,
                0,
            );
            try db.setFilePath(node_root_fid, s_path);
            try db.setPackageEmbedJail(.root, .{ .host_dir_jailed = pkg_node.package_root_path });
            if (pkg_node.pkg_id == .root) {
                primary_root_fid = node_root_fid;
            }
        } else {
            var root_pkg_manifest: *const pkg_manifest.Manifest = &manifest_bundle.root_manifest;
            if (pkg_node.pkg_id == .root and root_pkg_manifest.package == null) {
                for (manifest_bundle.members) |*ws_mem| {
                    if (ws_mem.manifest.package) |mem_pkg| {
                        if (std.mem.eql(u8, interner.get(mem_pkg.name_kebab), pkg_node.canonical_name)) {
                            root_pkg_manifest = &ws_mem.manifest;
                            break;
                        }
                    }
                }
            }
            const has_root_bins = pkg_node.pkg_id == .root and
                (pkg_node.bin_root_rel_path != null or root_pkg_manifest.bin_targets.len > 0);
            const is_bin_preferred = (pkg_node.pkg_id == .root) and
                (exec_info.subcommand == .run or (exec_info.subcommand == .build and has_root_bins));
            const dur: query_db.Durability = if (pkg_node.pkg_id == .root) .low else .medium;

            if (pkg_node.pkg_id == .root and
                ((pkg_node.lib_root_rel_path != null and has_root_bins) or root_pkg_manifest.bin_targets.len > 1))
            {
                if (pkg_node.lib_root_rel_path) |lib_rel| {
                    const lib_full_path = try std.fs.path.join(allocator, &.{ pkg_node.package_root_path, lib_rel });
                    defer allocator.free(lib_full_path);
                    const lib_fid = source_map.resolveOrCreatePath(io, lib_full_path, .root) catch {
                        try sink.emit(.{
                            .code = .e0004_source_file_io_error,
                            .severity = .err,
                            .primary_span = pkg_node.manifest_span,
                            .message = try std.fmt.allocPrint(
                                sink.arena.asAllocator(),
                                "failed to open package entry module `{s}`",
                                .{lib_full_path},
                            ),
                        });
                        try diag_renderer.renderAll(stderr_writer, sink);
                        return 1;
                    };
                    _ = try source_map.getLineIndex(lib_fid);
                    try discoverExternalSubmodulesRecursive(
                        allocator,
                        io,
                        source_map,
                        &db,
                        lib_fid,
                        lib_full_path,
                        .low,
                        .root,
                        &visited_fids,
                        files_gop.value_ptr,
                        &has_core_mention,
                        0,
                    );
                    try db.setFilePath(lib_fid, lib_full_path);
                    root_lib_fid_opt = lib_fid;
                    if (root_pkg_manifest.lib_target) |lib_tgt| {
                        if (lib_tgt.name_snake != .empty and interner.get(lib_tgt.name_snake).len > 0) {
                            root_lib_custom_snake = interner.get(lib_tgt.name_snake);
                        }
                    }
                }

                if (root_pkg_manifest.bin_targets.len > 0) {
                    for (root_pkg_manifest.bin_targets) |bin_tgt| {
                        const bin_rel = if (bin_tgt.path != .empty and interner.get(bin_tgt.path).len > 0)
                            interner.get(bin_tgt.path)
                        else
                            (pkg_node.bin_root_rel_path orelse "src/main.cx");
                        const bin_name = if (bin_tgt.name_kebab != .empty and interner.get(bin_tgt.name_kebab).len > 0)
                            interner.get(bin_tgt.name_kebab)
                        else
                            pkg_node.canonical_name;
                        const bin_full_path = try std.fs.path.join(allocator, &.{ pkg_node.package_root_path, bin_rel });
                        defer allocator.free(bin_full_path);
                        const bin_fid = source_map.resolveOrCreatePath(io, bin_full_path, .root) catch {
                            try sink.emit(.{
                                .code = .e0004_source_file_io_error,
                                .severity = .err,
                                .primary_span = pkg_node.manifest_span,
                                .message = try std.fmt.allocPrint(
                                    sink.arena.asAllocator(),
                                    "failed to open package entry module `{s}`",
                                    .{bin_full_path},
                                ),
                            });
                            try diag_renderer.renderAll(stderr_writer, sink);
                            return 1;
                        };
                        _ = try source_map.getLineIndex(bin_fid);
                        try discoverExternalSubmodulesRecursive(
                            allocator,
                            io,
                            source_map,
                            &db,
                            bin_fid,
                            bin_full_path,
                            .low,
                            .root,
                            &visited_fids,
                            files_gop.value_ptr,
                            &has_core_mention,
                            0,
                        );
                        try db.setFilePath(bin_fid, bin_full_path);
                        try root_bin_entries.append(allocator, .{ .bin_name = bin_name, .bin_fid = bin_fid });
                    }
                } else if (pkg_node.bin_root_rel_path) |bin_rel| {
                    const bin_full_path = try std.fs.path.join(allocator, &.{ pkg_node.package_root_path, bin_rel });
                    defer allocator.free(bin_full_path);
                    if (source_map.resolveOrCreatePath(io, bin_full_path, .root)) |bin_fid| {
                        _ = source_map.getLineIndex(bin_fid) catch {};
                        try discoverExternalSubmodulesRecursive(
                            allocator,
                            io,
                            source_map,
                            &db,
                            bin_fid,
                            bin_full_path,
                            .low,
                            .root,
                            &visited_fids,
                            files_gop.value_ptr,
                            &has_core_mention,
                            0,
                        );
                        try db.setFilePath(bin_fid, bin_full_path);
                        try root_bin_entries.append(allocator, .{
                            .bin_name = pkg_node.canonical_name,
                            .bin_fid = bin_fid,
                        });
                    } else |_| {
                        if (root_lib_fid_opt == null) {
                            try sink.emit(.{
                                .code = .e0004_source_file_io_error,
                                .severity = .err,
                                .primary_span = pkg_node.manifest_span,
                                .message = try std.fmt.allocPrint(
                                    sink.arena.asAllocator(),
                                    "failed to open package entry module `{s}`",
                                    .{bin_full_path},
                                ),
                            });
                            try diag_renderer.renderAll(stderr_writer, sink);
                            return 1;
                        }
                    }
                }

                node_root_fid = root_lib_fid_opt orelse root_bin_entries.items[0].bin_fid;
                if (is_bin_preferred and root_bin_entries.items.len > 0) {
                    primary_root_fid = root_bin_entries.items[0].bin_fid;
                    primary_stem = root_bin_entries.items[0].bin_name;
                } else {
                    primary_root_fid = node_root_fid;
                    primary_stem = pkg_node.canonical_name;
                }
            } else {
                const chosen_rel = if (is_bin_preferred)
                    (pkg_node.bin_root_rel_path orelse pkg_node.lib_root_rel_path orelse "src/main.cx")
                else
                    (pkg_node.lib_root_rel_path orelse pkg_node.bin_root_rel_path orelse "src/root.cx");
                const full_entry_path = try std.fs.path.join(allocator, &.{ pkg_node.package_root_path, chosen_rel });
                defer allocator.free(full_entry_path);

                node_root_fid = source_map.resolveOrCreatePath(io, full_entry_path, pkg_node.pkg_id) catch {
                    try sink.emit(.{
                        .code = .e0004_source_file_io_error,
                        .severity = .err,
                        .primary_span = pkg_node.manifest_span,
                        .message = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "failed to open package entry module `{s}`",
                            .{full_entry_path},
                        ),
                    });
                    try diag_renderer.renderAll(stderr_writer, sink);
                    return 1;
                };
                _ = try source_map.getLineIndex(node_root_fid);
                if (pkg_node.pkg_id == .root) {
                    primary_root_fid = node_root_fid;
                    primary_stem = if (is_bin_preferred and root_pkg_manifest.bin_targets.len > 0 and
                        root_pkg_manifest.bin_targets[0].name_kebab != .empty and
                        interner.get(root_pkg_manifest.bin_targets[0].name_kebab).len > 0)
                        interner.get(root_pkg_manifest.bin_targets[0].name_kebab)
                    else
                        pkg_node.canonical_name;
                }
                try discoverExternalSubmodulesRecursive(
                    allocator,
                    io,
                    source_map,
                    &db,
                    node_root_fid,
                    full_entry_path,
                    dur,
                    pkg_node.pkg_id,
                    &visited_fids,
                    files_gop.value_ptr,
                    &has_core_mention,
                    0,
                );
                try db.setFilePath(node_root_fid, full_entry_path);
            }
            try db.setPackageEmbedJail(pkg_node.pkg_id, .{ .host_dir_jailed = pkg_node.package_root_path });
        }

        try pkg_root_fids.put(allocator, pkg_node.pkg_id, node_root_fid);
        try db.registerPackageRootFile(pkg_node.pkg_id, node_root_fid);
        if (pkg_node.pkg_id == .root) {
            if (root_lib_fid_opt) |lib_fid| {
                if (pkg_node.default_snake_name.len > 0) {
                    try db.bindPackageDepFile(.root, try db.interner.intern(pkg_node.default_snake_name), lib_fid);
                }
                if (root_lib_custom_snake) |custom_snake| {
                    if (!std.mem.eql(u8, custom_snake, pkg_node.default_snake_name)) {
                        try db.bindPackageDepFile(.root, try db.interner.intern(custom_snake), lib_fid);
                    }
                }
            }
        }
        try db.setPackageCfgFeatures(
            pkg_node.pkg_id,
            pkg_node.enabled_features,
            if (pkg_node.has_feature_manifest) pkg_node.declared_features else null,
        );
        var pkg_policy = pkg_node.cap_policy;
        if (pkg_node.pkg_id != .root) {
            for (manifest_bundle.root_manifest.dependencies) |dep_spec| {
                if (dep_spec.has_comptime_io_cap and
                    std.mem.eql(u8, interner.get(dep_spec.package_kebab), pkg_node.canonical_name))
                {
                    pkg_policy.has_comptime_io_cap = true;
                    break;
                }
            }
            if (!pkg_policy.has_comptime_io_cap) {
                for (manifest_bundle.members) |ws_mem| {
                    for (ws_mem.manifest.dependencies) |dep_spec| {
                        if (dep_spec.has_comptime_io_cap and
                            std.mem.eql(u8, interner.get(dep_spec.package_kebab), pkg_node.canonical_name))
                        {
                            pkg_policy.has_comptime_io_cap = true;
                            break;
                        }
                    }
                    if (pkg_policy.has_comptime_io_cap) break;
                }
            }
            if (!pkg_policy.has_comptime_io_cap) {
                if (manifest_bundle.root_manifest.workspace) |ws_cfg| {
                    for (ws_cfg.dependencies) |dep_spec| {
                        if (dep_spec.has_comptime_io_cap and
                            std.mem.eql(u8, interner.get(dep_spec.package_kebab), pkg_node.canonical_name))
                        {
                            pkg_policy.has_comptime_io_cap = true;
                            break;
                        }
                    }
                }
            }
        }
        try db.setPackageCapPolicy(pkg_node.pkg_id, pkg_policy);
        try db.symbol_table.setPackageIdentityMeta(
            &db.interner,
            pkg_node.pkg_id,
            pkg_node.canonical_name,
            ver_str,
            root_lib_custom_snake orelse pkg_node.default_snake_name,
            node_root_fid,
        );
        try db.symbol_table.markPackageDepsConfigured(pkg_node.pkg_id);
    }

    // Bind per-package dependency edges `(caller_pkg, alias_sym) -> target_root_fid` and build `WorkspacePackageEdge`s:
    var cap_edges: std.ArrayListUnmanaged(mir_sast.WorkspacePackageEdge) = .empty;
    defer cap_edges.deinit(allocator);
    for (resolved.packages) |pkg_node| {
        for (pkg_node.dependencies) |dep_bind| {
            const target_fid = pkg_root_fids.get(dep_bind.target_pkg_id) orelse continue;
            try db.bindPackageDepFile(pkg_node.pkg_id, try db.interner.intern(dep_bind.alias_text), target_fid);

            // Compute edge `allow_caps` ceiling for `verifyWorkspaceCapabilitySandbox`:
            var target_eff_allow = mir_sast.EffectCapabilityMask.fromBits(0x0FFF);
            for (resolved.packages) |cand_target| {
                if (cand_target.pkg_id == dep_bind.target_pkg_id) {
                    target_eff_allow = cand_target.cap_policy.asEffectiveAllowedCaps();
                    break;
                }
            }
            if (dep_bind.explicit_allow_caps) |exp_allow| {
                const non_os: u16 = 0x0FFF & ~mir_sast.EffectCapabilityMask.LOCKFILE_CAP_BITS;
                target_eff_allow = mir_sast.EffectCapabilityMask.fromBits(
                    target_eff_allow.asBits() & (exp_allow.asBits() | non_os) & ~dep_bind.explicit_deny_caps.asBits(),
                );
            } else if (!dep_bind.explicit_deny_caps.isEmpty()) {
                target_eff_allow = mir_sast.EffectCapabilityMask.fromBits(
                    target_eff_allow.asBits() & ~dep_bind.explicit_deny_caps.asBits(),
                );
            }
            try cap_edges.append(allocator, .{
                .caller_pkg = pkg_node.pkg_id,
                .callee_pkg = dep_bind.target_pkg_id,
                .edge_label = dep_bind.alias_text,
                .edge_span = dep_bind.decl_span,
                .allow_caps = target_eff_allow,
            });
        }
    }

    if (has_core_mention) {
        try registerWorkspaceCoreModuleIfNeeded(
            allocator,
            io,
            source_map,
            &db,
            &visited_fids,
        );
    }

    // [4] Run front-end, typechecker, MIR SAST, and comptime verification across ALL mounted packages:
    var root_verify_slices: std.ArrayListUnmanaged(mem.FileId) = .empty;
    defer root_verify_slices.deinit(allocator);
    if (!primary_root_fid.isNone()) {
        try root_verify_slices.append(allocator, primary_root_fid);
    }
    if (pkg_files_owned.get(.root)) |root_list| {
        for (root_list.items) |rfid| {
            if (rfid != primary_root_fid) try root_verify_slices.append(allocator, rfid);
        }
    }

    var all_verify_slices: std.ArrayListUnmanaged(mem.FileId) = .empty;
    defer all_verify_slices.deinit(allocator);
    var verify_seen: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer verify_seen.deinit(allocator);
    for (root_verify_slices.items) |rfid| {
        if (!(try verify_seen.getOrPut(allocator, rfid.asInt())).found_existing) {
            try all_verify_slices.append(allocator, rfid);
        }
    }
    for (pkg_order.items) |pkg_id| {
        if (pkg_files_owned.get(pkg_id)) |pkg_list| {
            for (pkg_list.items) |pfid| {
                if (!(try verify_seen.getOrPut(allocator, pfid.asInt())).found_existing) {
                    try all_verify_slices.append(allocator, pfid);
                }
            }
        }
    }
    if (try verifyAndRenderModuleDiagnostics(
        allocator,
        &db,
        all_verify_slices.items,
        diag_renderer,
        stderr_writer,
    )) {
        return 1;
    }
    if (source_map.hasIntegrityErrorFile() != null) {
        try sink.emit(.{
            .code = .e0015_cache_integrity_mismatch,
            .severity = .err,
            .message = "cached `.cxtree` blob failed lazy BLAKE3 integrity verification",
        });
        try diag_renderer.renderAll(stderr_writer, sink);
        return 1;
    }

    // [5] Verify whole-workspace capability sandbox (`E0324` non-laundering & `W0330` dead capabilities):
    var pkg_files_slices: std.AutoHashMapUnmanaged(vfs.PackageId, []const mem.FileId) = .empty;
    defer pkg_files_slices.deinit(allocator);
    var pfs_it = pkg_files_owned.iterator();
    while (pfs_it.next()) |kv| {
        try pkg_files_slices.put(allocator, kv.key_ptr.*, kv.value_ptr.items);
    }

    const cap_reports = try db.verifyWorkspaceCapabilitySandbox(
        allocator,
        pkg_order.items,
        &pkg_files_slices,
        cap_edges.items,
        sink,
    );
    defer allocator.free(cap_reports);

    if (sink.diagnostics.items.len > 0) {
        try diag_renderer.renderAll(stderr_writer, sink);
        if (sink.hasErrors()) return 1;
    }

    // [6] Compute `.cxi` digests, verify `--locked` `.cxi` parity (`E0015`), publish `.cxi`, and write `corex.lock`:
    var cxi_digests: std.AutoHashMapUnmanaged(vfs.PackageId, [32]u8) = .empty;
    defer cxi_digests.deinit(allocator);
    var cap_summaries: std.AutoHashMapUnmanaged(vfs.PackageId, mir_sast.PackageCapSummary) = .empty;
    defer cap_summaries.deinit(allocator);

    for (resolved.packages) |pkg_node| {
        const p_files = pkg_files_slices.get(pkg_node.pkg_id) orelse &.{};
        var cxi_art = try db.computePackageCxiSummary(allocator, pkg_node.pkg_id, p_files);
        defer cxi_art.deinit(allocator);

        if (is_effective_locked and pkg_node.pkg_id != .root and
            pkg_node.source_kind != .workspace_member and pkg_node.source_kind != .local_path)
        {
            if (pkg_node.locked_cxi_blake3) |expected_cxi| {
                const empty_cxi = @import("../pkg_cxi_seam.zig").computeCxiBlake3(0, 0, &.{});
                if (!std.mem.eql(u8, &expected_cxi, &empty_cxi) and
                    !std.crypto.timing_safe.eql([32]u8, cxi_art.cxi_blake3, expected_cxi))
                {
                    try sink.emit(.{
                        .code = .e0015_cache_integrity_mismatch,
                        .severity = .err,
                        .primary_span = pkg_node.manifest_span,
                        .message = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "compiled `.cxi` digest for `{s}` does not match `corex.lock` `cxi_blake3`",
                            .{pkg_node.canonical_name},
                        ),
                    });
                    try diag_renderer.renderAll(stderr_writer, sink);
                    return 1;
                }
            }
        }
        cache.publishCxiSummary(io, cxi_art.bytes, cxi_art.cxi_blake3, null, pkg_node.manifest_span) catch {};
        try cxi_digests.put(allocator, pkg_node.pkg_id, cxi_art.cxi_blake3);
        try cap_summaries.put(allocator, pkg_node.pkg_id, cxi_art.caps);
    }

    if (!is_effective_locked) {
        var out_lock_arena = mem.BumpArena.init(allocator);
        defer out_lock_arena.deinit();
        const built_lock = try pkg_resolver.buildLockfileFromResolvedGraph(
            &out_lock_arena,
            allocator,
            interner,
            active_manifest_b3,
            &resolved,
            &cxi_digests,
            &cap_summaries,
        );
        const lock_text = try pkg_manifest.serializeLockfile(allocator, &built_lock, interner);
        defer allocator.free(lock_text);
        codegen_abi.writeArtifactAtomic(io, allocator, lockfile_path, lock_text) catch {};
    }

    // [7] Merge `ordered_native_link_libs` (`links = "…"`) + CLI `-l` `extra_libs` and execute subcommand:
    var merged_libs: std.ArrayListUnmanaged([]const u8) = .empty;
    defer merged_libs.deinit(allocator);
    var seen_libs: std.StringHashMapUnmanaged(void) = .empty;
    defer seen_libs.deinit(allocator);
    for (resolved.ordered_native_link_libs) |nat_lib| {
        if (!(try seen_libs.getOrPut(allocator, nat_lib)).found_existing) {
            try merged_libs.append(allocator, nat_lib);
        }
    }
    for (exec_info.extra_libs) |cli_lib| {
        if (!(try seen_libs.getOrPut(allocator, cli_lib)).found_existing) {
            try merged_libs.append(allocator, cli_lib);
        }
    }

    switch (exec_info.subcommand) {
        .check => {
            try stdout_style.writeStatusHeader(
                stdout_writer,
                .success,
                Glyphs.SUCCESS,
                "check",
                primary_stem,
            );
            try stdout_writer.writeByte('\n');
            return 0;
        },
        .build => {
            const backend = buildConfiguredBackend(
                exec_info.output_format,
                active_target,
                exec_info.is_release_mode,
                exec_info.is_fuzz_enabled,
            );

            if (root_bin_entries.items.len > 1 and exec_info.output_path == null and
                !exec_info.is_emit_c and !exec_info.is_emit_llvm and !exec_info.is_emit_obj)
            {
                const bin_ext = active_target.executableExtension();
                for (root_bin_entries.items) |bin_entry| {
                    var bin_extra_files: std.ArrayListUnmanaged(mem.FileId) = .empty;
                    defer bin_extra_files.deinit(allocator);
                    for (all_verify_slices.items) |cand_fid| {
                        if (cand_fid == bin_entry.bin_fid) continue;
                        var is_sibling_bin = false;
                        for (root_bin_entries.items) |other_bin| {
                            if (other_bin.bin_fid != bin_entry.bin_fid and cand_fid == other_bin.bin_fid) {
                                is_sibling_bin = true;
                                break;
                            }
                        }
                        if (!is_sibling_bin) try bin_extra_files.append(allocator, cand_fid);
                    }

                    const bin_out_path = try std.fmt.allocPrint(
                        allocator,
                        "{s}/build/{s}{s}",
                        .{ manifest_bundle.workspace_root_dir, bin_entry.bin_name, bin_ext },
                    );
                    defer allocator.free(bin_out_path);

                    var multi_art = db.compileModuleArtifact(bin_entry.bin_fid, backend, .{
                        .module_name = bin_entry.bin_name,
                        .extra_file_ids = bin_extra_files.items,
                        .vfs_source_map = source_map,
                        .is_dev_got_enabled = false,
                        .artifact_kind = .executable,
                        .link_mode = exec_info.link_mode,
                        .extra_libs = merged_libs.items,
                        .lib_dirs = exec_info.lib_dirs,
                        .output_path = bin_out_path,
                        .io = io,
                        .environ_map = environ_map,
                        .diagnostic_sink = sink,
                    }) catch |comp_err| switch (comp_err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => {
                            try renderCompileFailureDiagnostics(
                                allocator,
                                &db,
                                bin_entry.bin_fid,
                                all_verify_slices.items,
                                exec_info.is_release_mode,
                                sink,
                                diag_renderer,
                                stderr_writer,
                            );
                            return 1;
                        },
                    };
                    defer multi_art.deinit(allocator);

                    try stdout_style.writeStatusHeader(
                        stdout_writer,
                        .success,
                        Glyphs.SUCCESS,
                        "build",
                        bin_out_path,
                    );
                    try stdout_writer.writeByte('\n');
                }
                return 0;
            }

            const has_main = try fileDeclaresMainEntrypoint(&db, primary_root_fid);
            const artifact_kind: codegen_abi.OutputArtifactKind =
                if (exec_info.is_emit_c or exec_info.is_emit_llvm)
                    .source_text
                else if (exec_info.is_emit_obj)
                    .object_file
                else if (has_main)
                    .executable
                else
                    .object_file;

            const default_ext: []const u8 = switch (artifact_kind) {
                .source_text => if (exec_info.output_format == .c) ".c" else ".ll",
                .executable => active_target.executableExtension(),
                .object_file => active_target.objectExtension(),
                .static_library => active_target.defaultStaticLibExtension(),
                .shared_library => active_target.defaultSharedLibExtension(),
            };
            const default_out = try std.fmt.allocPrint(
                allocator,
                "{s}/build/{s}{s}",
                .{ manifest_bundle.workspace_root_dir, primary_stem, default_ext },
            );
            defer allocator.free(default_out);
            const final_out_path = exec_info.output_path orelse default_out;

            var filtered_extra_files: std.ArrayListUnmanaged(mem.FileId) = .empty;
            defer filtered_extra_files.deinit(allocator);
            for (all_verify_slices.items) |cand_fid| {
                if (cand_fid == primary_root_fid) continue;
                var is_sibling_bin = false;
                for (root_bin_entries.items) |other_bin| {
                    if (other_bin.bin_fid != primary_root_fid and cand_fid == other_bin.bin_fid) {
                        is_sibling_bin = true;
                        break;
                    }
                }
                if (!is_sibling_bin) try filtered_extra_files.append(allocator, cand_fid);
            }

            var build_art = db.compileModuleArtifact(primary_root_fid, backend, .{
                .module_name = primary_stem,
                .extra_file_ids = filtered_extra_files.items,
                .vfs_source_map = source_map,
                .is_dev_got_enabled = false,
                .artifact_kind = artifact_kind,
                .link_mode = exec_info.link_mode,
                .extra_libs = merged_libs.items,
                .lib_dirs = exec_info.lib_dirs,
                .output_path = final_out_path,
                .io = io,
                .environ_map = environ_map,
                .diagnostic_sink = sink,
            }) catch |comp_err| switch (comp_err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => {
                    try renderCompileFailureDiagnostics(
                        allocator,
                        &db,
                        primary_root_fid,
                        all_verify_slices.items,
                        exec_info.is_release_mode,
                        sink,
                        diag_renderer,
                        stderr_writer,
                    );
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
            if (!std.meta.eql(active_target.arch, codegen_abi.TargetSpec.host().arch) or
                !std.meta.eql(active_target.os, codegen_abi.TargetSpec.host().os))
            {
                try sink.emit(.{
                    .code = .e0006_invalid_target_triple,
                    .severity = .err,
                    .message = "cannot execute cross-compiled target directly via `corex run`",
                    .notes = &.{"help: use `corex build --target=<triple>` to emit a cross-target binary"},
                });
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            }

            const scratch_dir = try std.fmt.allocPrint(
                allocator,
                ".zig-cache/cx_run_{d}",
                .{next_run_scratch_seq.fetchAdd(1, .monotonic)},
            );
            defer allocator.free(scratch_dir);
            defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};

            const run_artifact_kind: codegen_abi.OutputArtifactKind =
                if (exec_info.is_emit_obj) .object_file else .executable;
            const run_ext = if (exec_info.is_emit_obj)
                active_target.objectExtension()
            else
                active_target.executableExtension();
            const temp_exe_path = try std.fmt.allocPrint(
                allocator,
                "{s}/{s}{s}",
                .{ scratch_dir, primary_stem, run_ext },
            );
            defer allocator.free(temp_exe_path);
            const final_exe_path = exec_info.output_path orelse temp_exe_path;

            const backend = buildConfiguredBackend(
                exec_info.output_format,
                active_target,
                exec_info.is_release_mode,
                exec_info.is_fuzz_enabled,
            );
            var run_extra_files: std.ArrayListUnmanaged(mem.FileId) = .empty;
            defer run_extra_files.deinit(allocator);
            for (all_verify_slices.items) |cand_fid| {
                if (cand_fid == primary_root_fid) continue;
                var is_sibling_bin = false;
                for (root_bin_entries.items) |other_bin| {
                    if (other_bin.bin_fid != primary_root_fid and cand_fid == other_bin.bin_fid) {
                        is_sibling_bin = true;
                        break;
                    }
                }
                if (!is_sibling_bin) try run_extra_files.append(allocator, cand_fid);
            }
            var run_art = db.compileModuleArtifact(primary_root_fid, backend, .{
                .module_name = primary_stem,
                .extra_file_ids = run_extra_files.items,
                .vfs_source_map = source_map,
                .is_dev_got_enabled = false,
                .artifact_kind = run_artifact_kind,
                .link_mode = exec_info.link_mode,
                .extra_libs = merged_libs.items,
                .lib_dirs = exec_info.lib_dirs,
                .output_path = final_exe_path,
                .io = io,
                .environ_map = environ_map,
                .diagnostic_sink = sink,
            }) catch |comp_err| switch (comp_err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => {
                    try renderCompileFailureDiagnostics(
                        allocator,
                        &db,
                        primary_root_fid,
                        all_verify_slices.items,
                        exec_info.is_release_mode,
                        sink,
                        diag_renderer,
                        stderr_writer,
                    );
                    return 1;
                },
            };
            defer run_art.deinit(allocator);

            if (exec_info.is_emit_obj) {
                try stdout_style.writeStatusHeader(stdout_writer, .success, Glyphs.SUCCESS, "run", final_exe_path);
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
                try diag_renderer.renderAll(stderr_writer, sink);
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
                for (root_verify_slices.items) |test_fid| {
                    if (!(try fileDeclaresMainEntrypoint(&db, test_fid))) continue;
                    tested_main_count += 1;
                    var oracle_report = diff_oracle.runFourTierDiffOracleOnDb(
                        allocator,
                        &db,
                        test_fid,
                        .{
                            .io = io,
                            .environ_map = environ_map,
                            .vfs_source_map = source_map,
                            .workspace_root = manifest_bundle.workspace_root_dir,
                            .comptime_step_limit = exec_info.comptime_step_limit,
                            .diagnostic_sink = sink,
                        },
                    ) catch |oracle_err| switch (oracle_err) {
                        error.OutOfMemory => return error.OutOfMemory,
                        else => {
                            if (sink.hasErrors()) {
                                try diag_renderer.renderAll(stderr_writer, sink);
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
            try stdout_style.writeStatusHeader(
                stdout_writer,
                .success,
                Glyphs.SUCCESS,
                "test",
                primary_stem,
            );
            try stdout_writer.writeByte('\n');
            return 0;
        },
        else => return 0,
    }
}

/// Renders diagnostics from `sink` or `db` when `compileModuleArtifact` aborts so `stderr` is never empty.
fn renderCompileFailureDiagnostics(
    allocator: std.mem.Allocator,
    db: *query_db.CompilerDb,
    primary_root_fid: mem.FileId,
    verify_files: []const mem.FileId,
    is_release_mode: bool,
    sink: *DiagnosticSink,
    diag_renderer: DiagnosticRenderer,
    stderr_writer: *std.Io.Writer,
) !void {
    if (sink.diagnostics.items.len > 0) {
        try diag_renderer.renderAll(stderr_writer, sink);
        return;
    }
    if (try verifyAndRenderModuleDiagnostics(allocator, db, verify_files, diag_renderer, stderr_writer)) {
        return;
    }
    if (db.getOptimizedMirDiagnostics(primary_root_fid, is_release_mode)) |opt_sink| {
        if (opt_sink.diagnostics.items.len > 0) {
            try diag_renderer.renderAll(stderr_writer, opt_sink);
            return;
        }
    }
    try sink.emit(.{
        .code = .e0007_codegen_backend_failure,
        .severity = .err,
        .primary_span = mem.Span.init(primary_root_fid, 0, 0),
        .message = "module compilation aborted due to front-end or MIR verification errors",
    });
    try diag_renderer.renderAll(stderr_writer, sink);
}

/// Loads `toml_path`, scans root workspace `.cx` imports, and executes Mode A (`executePackageOrScriptWorkflow`).
fn executeManifestTomlMode(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    source_map: *vfs.VfsSourceMap,
    interner: *mem.StringInterner,
    sink: *DiagnosticSink,
    exec_info: ExecuteSubcommandAction,
    env_cfg: ToolchainEnvConfig,
    cfg_env: *const symbol_resolver.CfgEnv,
    toml_path: []const u8,
    diag_renderer: DiagnosticRenderer,
    stdout_style: StyleConfig,
    stderr_style: StyleConfig,
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
) !u8 {
    const toml_fid = (try loadSourceFileIntoVfs(io, source_map, toml_path, sink)) orelse {
        try diag_renderer.renderAll(stderr_writer, sink);
        return 1;
    };
    var bundle = pkg_manifest.loadWorkspaceManifestBundle(
        io,
        allocator,
        interner,
        toml_path,
        toml_fid,
        cfg_env,
        sink,
    ) catch |load_err| switch (load_err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            if (!sink.hasErrors()) {
                try sink.emit(.{
                    .code = .e0004_source_file_io_error,
                    .severity = .err,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "failed to load manifest `{s}`",
                        .{toml_path},
                    ),
                });
            }
            try diag_renderer.renderAll(stderr_writer, sink);
            return 1;
        },
    };
    defer bundle.deinit();
    if (sink.hasErrors()) {
        try diag_renderer.renderAll(stderr_writer, sink);
        return 1;
    }

    var scanned_inlines: std.ArrayListUnmanaged(symbol_resolver.InlineUseImport) = .empty;
    defer {
        for (scanned_inlines.items) |inl| allocator.free(inl.spec_text);
        scanned_inlines.deinit(allocator);
    }
    var scanned_bare_roots: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (scanned_bare_roots.items) |br| allocator.free(br);
        scanned_bare_roots.deinit(allocator);
    }
    const primary_idx = bundle.primary_member_index orelse 0;
    const primary_dir = if (primary_idx < bundle.members.len)
        bundle.members[primary_idx].abs_dir
    else
        bundle.workspace_root_dir;
    var root_cx_paths: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (root_cx_paths.items) |p_str| allocator.free(p_str);
        root_cx_paths.deinit(allocator);
    }
    _ = try collectDirectoryCxPaths(allocator, io, primary_dir, &root_cx_paths);
    for (root_cx_paths.items) |rcx_path| {
        if (loadSourceFileIntoVfs(io, source_map, rcx_path, sink) catch null) |rcx_fid| {
            const rcx_src = source_map.getFileSource(rcx_fid) orelse "";
            try scanRootCxSourceImports(
                allocator,
                interner,
                cfg_env,
                rcx_fid,
                rcx_src,
                &scanned_inlines,
                &scanned_bare_roots,
                sink,
            );
        }
    }
    if (sink.hasErrors()) {
        try diag_renderer.renderAll(stderr_writer, sink);
        return 1;
    }

    const lock_path = try std.fs.path.join(allocator, &.{ bundle.workspace_root_dir, "corex.lock" });
    defer allocator.free(lock_path);
    return try executePackageOrScriptWorkflow(
        allocator,
        io,
        environ_map,
        source_map,
        interner,
        sink,
        exec_info,
        env_cfg,
        &bundle,
        lock_path,
        null,
        null,
        scanned_inlines.items,
        scanned_bare_roots.items,
        stdout_style,
        stderr_style,
        stdout_writer,
        stderr_writer,
    );
}

/// Inspects CLI flags and inputs for Mode A (`corex.toml`) or Mode B (`.cx` script), returning `null` for Mode C.
fn tryExecutePackageOrScriptMode(
    allocator: std.mem.Allocator,
    io: std.Io,
    environ_map: ?*const std.process.Environ.Map,
    source_map: *vfs.VfsSourceMap,
    interner: *mem.StringInterner,
    sink: *DiagnosticSink,
    exec_info: ExecuteSubcommandAction,
    input_positional: []const []const u8,
    stdout_style: StyleConfig,
    stderr_style: StyleConfig,
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
) !?u8 {
    if (!isCompileSubcommand(exec_info.subcommand)) return null;
    const diag_renderer = DiagnosticRenderer.init(source_map, interner, stderr_style);
    const active_target = exec_info.target_spec orelse codegen_abi.TargetSpec.host();
    const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(active_target, exec_info.subcommand == .@"test");

    var env_cfg = try resolveToolchainEnvConfig(allocator, environ_map);
    defer env_cfg.deinit(allocator);

    // [1] Determine candidate `corex.toml` or `.cx` script path:
    var owned_manifest_toml: ?[]u8 = null;
    defer if (owned_manifest_toml) |buf| allocator.free(buf);
    var candidate_script_path: ?[]const u8 = null;

    if (exec_info.manifest_path) |explicit_mp| {
        if (std.mem.endsWith(u8, explicit_mp, ".cx")) {
            candidate_script_path = explicit_mp;
        } else if (std.Io.Dir.cwd().openDir(io, explicit_mp, .{})) |opened_d| {
            var dir_mut = opened_d;
            dir_mut.close(io);
            owned_manifest_toml = try std.fs.path.join(allocator, &.{ explicit_mp, "corex.toml" });
        } else |_| {
            owned_manifest_toml = try allocator.dupe(u8, explicit_mp);
        }
    } else if (input_positional.len == 1) {
        const single_arg = input_positional[0];
        if (std.mem.endsWith(u8, single_arg, "corex.toml") or std.mem.endsWith(u8, single_arg, ".toml")) {
            owned_manifest_toml = try allocator.dupe(u8, single_arg);
        } else if (std.Io.Dir.cwd().openDir(io, single_arg, .{})) |opened_d| {
            var dir_mut = opened_d;
            dir_mut.close(io);
            const joined_toml = try std.fs.path.join(allocator, &.{ single_arg, "corex.toml" });
            if (std.Io.Dir.cwd().openFile(io, joined_toml, .{ .mode = .read_only })) |tf| {
                tf.close(io);
                owned_manifest_toml = joined_toml;
            } else |_| {
                allocator.free(joined_toml);
            }
        } else |_| {
            if (std.mem.endsWith(u8, single_arg, ".cx")) {
                candidate_script_path = single_arg;
            }
        }
    } else if (input_positional.len == 0) {
        owned_manifest_toml = try discoverNearestManifestUpward(allocator, io);
    }

    const has_explicit_pkg_flags = exec_info.is_locked or
        exec_info.is_frozen or
        exec_info.is_offline or
        exec_info.manifest_path != null or
        exec_info.features.len > 0 or
        exec_info.has_no_default_features or
        exec_info.is_verifying_checksums;

    // [2] Mode A: `corex.toml` Manifest / Workspace Mode:
    if (owned_manifest_toml) |toml_path| {
        return try executeManifestTomlMode(
            allocator,
            io,
            environ_map,
            source_map,
            interner,
            sink,
            exec_info,
            env_cfg,
            &cfg_env,
            toml_path,
            diag_renderer,
            stdout_style,
            stderr_style,
            stdout_writer,
            stderr_writer,
        );
    }

    if (candidate_script_path == null and input_positional.len > 1 and
        (exec_info.is_locked or exec_info.is_frozen or env_cfg.is_hermetic))
    {
        if (try discoverNearestManifestUpward(allocator, io)) |anc_toml| {
            defer allocator.free(anc_toml);
            return try executeManifestTomlMode(
                allocator,
                io,
                environ_map,
                source_map,
                interner,
                sink,
                exec_info,
                env_cfg,
                &cfg_env,
                anc_toml,
                diag_renderer,
                stdout_style,
                stderr_style,
                stdout_writer,
                stderr_writer,
            );
        }
        try sink.emit(.{
            .code = .e0014_lockfile_drift_or_corrupt,
            .severity = .err,
            .message = "cannot enforce `--locked` / `--frozen` without a `corex.toml` manifest or `corex.lock`",
        });
        try diag_renderer.renderAll(stderr_writer, sink);
        return 1;
    }

    // [3] Mode B: Single-File `.cx` Script (`#!` / `---` TOML frontmatter or inline `use "<spec>" as <alias>;`):
    if (candidate_script_path) |script_path| {
        const raw_script = std.Io.Dir.cwd().readFileAlloc(
            io,
            script_path,
            allocator,
            .limited(vfs.MAX_SOURCE_FILE_BYTES),
        ) catch {
            if (has_explicit_pkg_flags) {
                _ = try loadSourceFileIntoVfs(io, source_map, script_path, sink);
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            }
            return null;
        };
        defer allocator.free(raw_script);

        const raw_fid = try source_map.setOverlay(script_path, raw_script, .root);
        _ = try source_map.getLineIndex(raw_fid);

        var fm_arena = mem.BumpArena.init(allocator);
        defer fm_arena.deinit();
        const extracted_fm = (try pkg_manifest.extractScriptFrontmatter(&fm_arena, raw_fid, raw_script, sink)) orelse {
            try diag_renderer.renderAll(stderr_writer, sink);
            return 1;
        };
        if (sink.hasErrors()) {
            try diag_renderer.renderAll(stderr_writer, sink);
            return 1;
        }

        var scanned_inlines: std.ArrayListUnmanaged(symbol_resolver.InlineUseImport) = .empty;
        defer {
            for (scanned_inlines.items) |inl| allocator.free(inl.spec_text);
            scanned_inlines.deinit(allocator);
        }
        var scanned_bare_roots: std.ArrayListUnmanaged([]u8) = .empty;
        defer {
            for (scanned_bare_roots.items) |br| allocator.free(br);
            scanned_bare_roots.deinit(allocator);
        }

        const cx_body_src = if (extracted_fm.prefix_end_byte > 0) extracted_fm.blanked_cx_source else raw_script;
        try scanRootCxSourceImports(
            allocator,
            interner,
            &cfg_env,
            raw_fid,
            cx_body_src,
            &scanned_inlines,
            &scanned_bare_roots,
            sink,
        );
        if (sink.hasErrors()) {
            try diag_renderer.renderAll(stderr_writer, sink);
            return 1;
        }

        if (!extracted_fm.has_frontmatter and scanned_inlines.items.len == 0 and exec_info.manifest_path == null) {
            if (try discoverNearestManifestFromDirUpward(
                allocator,
                io,
                std.fs.path.dirname(script_path) orelse ".",
            )) |anc_toml| {
                defer allocator.free(anc_toml);
                if (has_explicit_pkg_flags or try isCxFileOwnedByManifest(
                    allocator,
                    io,
                    interner,
                    source_map,
                    anc_toml,
                    script_path,
                    &cfg_env,
                )) {
                    return try executeManifestTomlMode(
                        allocator,
                        io,
                        environ_map,
                        source_map,
                        interner,
                        sink,
                        exec_info,
                        env_cfg,
                        &cfg_env,
                        anc_toml,
                        diag_renderer,
                        stdout_style,
                        stderr_style,
                        stdout_writer,
                        stderr_writer,
                    );
                }
            }
            if (!has_explicit_pkg_flags) {
                if (extracted_fm.prefix_end_byte > 0) {
                    // Shebang-only standalone `.cx` script; keep `#!` blanked in `source_map` and run fast Mode C:
                    _ = try source_map.getLineIndex(
                        try source_map.setOverlay(script_path, extracted_fm.blanked_cx_source, .root),
                    );
                }
                return null;
            }
        }

        const script_fid = try source_map.setOverlay(script_path, cx_body_src, .root);
        _ = try source_map.getLineIndex(script_fid);

        var manifest_arena = mem.BumpArena.init(allocator);
        defer manifest_arena.deinit();
        var script_manifest: pkg_manifest.Manifest = undefined;
        if (extracted_fm.has_frontmatter) {
            var parsed_fm = try pkg_manifest.parseScriptFrontmatterManifest(
                allocator,
                &manifest_arena,
                interner,
                script_fid,
                raw_script,
                extracted_fm,
                &cfg_env,
                sink,
            );
            defer parsed_fm.doc.deinit(allocator);
            if (sink.hasErrors()) {
                try diag_renderer.renderAll(stderr_writer, sink);
                return 1;
            }
            script_manifest = parsed_fm.manifest;
        } else {
            script_manifest = .{
                .file_id = script_fid,
                .is_script = true,
                .package = .{
                    .name_kebab = try interner.intern("script-pkg"),
                    .module_snake = try interner.intern("script_pkg"),
                    .version = .{ .major = 0, .minor = 1, .patch = 0 },
                    .edition = try interner.intern(pkg_manifest.DEFAULT_COREX_EDITION),
                    .publish = .{ .is_allowed = false },
                },
            };
            script_manifest.root_manifest_blake3 = pkg_manifest.computeNormalizedManifestBlake3(
                &script_manifest,
                interner,
            );
        }

        // Fold inline `use "…"` specs into `script_manifest.root_manifest_blake3` so `--locked` catches inline edits:
        if (scanned_inlines.items.len > 0) {
            var inl_h = std.crypto.hash.Blake3.init(.{});
            inl_h.update(&script_manifest.root_manifest_blake3);
            for (scanned_inlines.items) |inl| {
                inl_h.update(inl.alias_text);
                inl_h.update(&[1]u8{0});
                inl_h.update(inl.spec_text);
                inl_h.update(&[1]u8{0});
            }
            inl_h.final(&script_manifest.root_manifest_blake3);
        }

        const script_dir = std.fs.path.dirname(script_path) orelse ".";
        var bundle = try pkg_manifest.buildBundleFromSingleManifest(
            allocator,
            script_dir,
            script_path,
            script_manifest,
            true,
        );
        defer bundle.deinit();

        const script_lock_path = try pkg_manifest.computeScriptLockfilePath(
            io,
            allocator,
            env_cfg.corex_home_dir,
            script_path,
        );
        defer allocator.free(script_lock_path);

        return try executePackageOrScriptWorkflow(
            allocator,
            io,
            environ_map,
            source_map,
            interner,
            sink,
            exec_info,
            env_cfg,
            &bundle,
            script_lock_path,
            script_fid,
            script_path,
            scanned_inlines.items,
            &.{},
            stdout_style,
            stderr_style,
            stdout_writer,
            stderr_writer,
        );
    }

    return null;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Resolves `COREX_HOME` and `COREX_HERMETIC=1` from `environ_map` (`DR-11` §3.5).
pub fn resolveToolchainEnvConfig(
    allocator: std.mem.Allocator,
    environ_map: ?*const std.process.Environ.Map,
) !ToolchainEnvConfig {
    const home_dir = try pkg_cache.resolveCorexHome(allocator, environ_map);
    var is_hermetic = false;
    if (environ_map) |env_m| {
        if (env_m.get("COREX_HERMETIC")) |raw_hermetic| {
            const trimmed = std.mem.trim(u8, raw_hermetic, " \t\r\n");
            is_hermetic = std.mem.eql(u8, trimmed, "1") or std.ascii.eqlIgnoreCase(trimmed, "true");
        }
    }
    return .{
        .corex_home_dir = home_dir,
        .is_hermetic = is_hermetic,
    };
}

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
    var features_list: std.ArrayListUnmanaged([]const u8) = .empty;
    var manifest_path: ?[]const u8 = null;
    var is_locked = false;
    var is_offline = false;
    var is_frozen = false;
    var has_no_default_features = false;
    var is_verifying_checksums = false;
    var selected_subcommand: ?SubcommandId = null;
    var positional_list: std.ArrayListUnmanaged([]const u8) = .empty;
    var is_after_double_dash = false;
    var is_direct_script_invocation = false;
    var pre_dash_count: ?usize = null;
    const has_direct_script_target = blk_script: {
        for (raw_args) |cand_arg| {
            if (std.mem.eql(u8, cand_arg, "--")) break;
            if (std.mem.startsWith(u8, cand_arg, "-")) continue;
            break :blk_script SubcommandId.fromName(cand_arg) == null and std.mem.endsWith(u8, cand_arg, ".cx");
        }
        break :blk_script false;
    };

    var arg_idx: usize = 0;
    while (arg_idx < raw_args.len) : (arg_idx += 1) {
        const arg_text = raw_args[arg_idx];
        if (!is_after_double_dash and std.mem.eql(u8, arg_text, "--")) {
            is_after_double_dash = true;
            pre_dash_count = positional_list.items.len;
            continue;
        }

        if (!is_after_double_dash and std.mem.startsWith(u8, arg_text, "-")) {
            const is_compile_sub = (selected_subcommand != null and isCompileSubcommand(selected_subcommand.?)) or
                (selected_subcommand == null and has_direct_script_target);
            const is_compile_or_translate = is_compile_sub or selected_subcommand == .translate_c;
            const is_ofmt_spelling = std.mem.eql(u8, arg_text, "-ofmt") or
                std.mem.startsWith(u8, arg_text, "-ofmt=");
            var extracted_str: ?[]const u8 = null;

            if (std.mem.eql(u8, arg_text, "-h") or std.mem.eql(u8, arg_text, "--help")) {
                has_help_flag = true;
            } else if (std.mem.eql(u8, arg_text, "-V") or std.mem.eql(u8, arg_text, "--version")) {
                has_version_flag = true;
            } else if (selected_subcommand == .fmt and blk_fmt: {
                if (matchFmtFlag(arg_text)) |fmt_flag| {
                    switch (fmt_flag) {
                        .check => is_check_only = true,
                        .fix => is_fix_mode = true,
                        .internal_core => is_internal_core = true,
                    }
                    break :blk_fmt true;
                }
                break :blk_fmt false;
            }) {} else if (selected_subcommand == .upgrade and blk_upg: {
                if (matchUpgradeFlag(arg_text)) |upg_flag| {
                    switch (upg_flag) {
                        .internal_core => is_internal_core = true,
                    }
                    break :blk_upg true;
                }
                break :blk_upg false;
            }) {} else if (is_compile_sub and std.mem.eql(u8, arg_text, "--dev")) {
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
            } else if (is_compile_sub and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--features",
                "-F",
                "missing feature list for `--features` / `-F`",
                "help: pass `--features=tls,json` or `-F tls`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |feat_spec| {
                    try extractCliFeatureTokens(arena_alloc, feat_spec, &features_list);
                }
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--frozen")) {
                is_frozen = true;
                is_locked = true;
                is_offline = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--locked")) {
                is_locked = true;
            } else if (is_compile_sub and try tryExtractStringFlagValue(
                raw_args,
                &arg_idx,
                "--manifest-path",
                "",
                "missing path for `--manifest-path`",
                "help: pass `--manifest-path=corex.toml`",
                sink,
                &extracted_str,
            )) {
                if (extracted_str) |manifest_str| {
                    manifest_path = manifest_str;
                }
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--no-default-features")) {
                has_no_default_features = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--offline")) {
                is_offline = true;
            } else if (is_compile_sub and std.mem.eql(u8, arg_text, "--verify-checksums")) {
                is_verifying_checksums = true;
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
            } else if (std.mem.endsWith(u8, arg_text, ".cx")) {
                selected_subcommand = .run;
                is_direct_script_invocation = true;
                try positional_list.append(arena_alloc, arg_text);
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
        const split_pos = pre_dash_count orelse
            if (is_direct_script_invocation and positional_list.items.len > 1)
                @as(usize, 1)
            else
                positional_list.items.len;
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
            .features = features_list.items,
            .manifest_path = manifest_path,
            .is_locked = is_locked,
            .is_offline = is_offline,
            .is_frozen = is_frozen,
            .has_no_default_features = has_no_default_features,
            .is_verifying_checksums = is_verifying_checksums,
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
                    .features = features_list.items,
                    .manifest_path = manifest_path,
                    .is_locked = is_locked,
                    .is_offline = is_offline,
                    .is_frozen = is_frozen,
                    .has_no_default_features = has_no_default_features,
                    .is_verifying_checksums = is_verifying_checksums,
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

            if (try tryExecutePackageOrScriptMode(
                allocator,
                io,
                environ_map,
                &source_map,
                &interner,
                &sink,
                exec_info,
                input_positional,
                stdout_style,
                stderr_style,
                stdout_writer,
                stderr_writer,
            )) |pkg_exit_code| {
                return pkg_exit_code;
            }

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
                        null,
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
                                try renderCompileFailureDiagnostics(
                                    allocator,
                                    &db,
                                    cx_file_ids.items[0],
                                    cx_file_ids.items,
                                    exec_info.is_release_mode,
                                    &sink,
                                    diag_renderer,
                                    stderr_writer,
                                );
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

                        const scratch_dir = try std.fmt.allocPrint(
                            allocator,
                            ".zig-cache/cx_run_{d}",
                            .{next_run_scratch_seq.fetchAdd(1, .monotonic)},
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
                                try renderCompileFailureDiagnostics(
                                    allocator,
                                    &db,
                                    cx_file_ids.items[0],
                                    cx_file_ids.items,
                                    exec_info.is_release_mode,
                                    &sink,
                                    diag_renderer,
                                    stderr_writer,
                                );
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
    std.debug.assert(COMPILE_FLAGS.len == 25);
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
    try std.testing.expectEqual(@as(usize, 25), COMPILE_FLAGS.len);
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

    const parsed_pkg = try parseArgs(&.{
        "build",
        "-F",
        "tls,json",
        "--frozen",
        "--no-default-features",
        "--verify-checksums",
        "--manifest-path=corex.toml",
    }, &sink);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(@as(usize, 2), parsed_pkg.features.len);
    try std.testing.expectEqualStrings("tls", parsed_pkg.features[0]);
    try std.testing.expectEqualStrings("json", parsed_pkg.features[1]);
    try std.testing.expect(parsed_pkg.is_frozen);
    try std.testing.expect(parsed_pkg.is_locked);
    try std.testing.expect(parsed_pkg.is_offline);
    try std.testing.expect(parsed_pkg.has_no_default_features);
    try std.testing.expect(parsed_pkg.is_verifying_checksums);
    try std.testing.expectEqualStrings("corex.toml", parsed_pkg.manifest_path.?);

    // Passing `--check` to a non-`fmt` subcommand emits `E0001`:
    var err_sink = DiagnosticSink.init(std.testing.allocator);
    defer err_sink.deinit();
    const invalid_cmd = try parseArgs(&.{ "build", "--check" }, &err_sink);
    try std.testing.expect(err_sink.hasErrors());
    try std.testing.expectEqual(CommandAction.invalid, invalid_cmd.action);
}

test "test_cli_router_package_mode_mount_cxtree_lockfile_and_frozen_check" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const scratch_dir = ".zig-cache/test_cli_pkg_mode_e2e";
    std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};

    const reg_dir = scratch_dir ++ "/reg";
    const home_dir = scratch_dir ++ "/home";
    const proj_dir = scratch_dir ++ "/proj";
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/co/re");
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/packages/corex-math-1.2.0/src");
    try std.Io.Dir.cwd().createDirPath(io, home_dir);
    try std.Io.Dir.cwd().createDirPath(io, proj_dir ++ "/src");

    // External dependency with both root `pub struct Vec2` and submodule `mod ops;` using `use pkg.Vec2;`:
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/packages/corex-math-1.2.0/src/root.cx",
        .data = "pub mod ops;\npub struct Vec2 {\n    pub x: i32,\n    pub y: i32,\n}\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/packages/corex-math-1.2.0/src/ops.cx",
        .data = "use pkg.Vec2;\npub fn sum_vec(val: Vec2) -> i32 = val.x + val.y;\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/co/re/corex-math",
        .data = "{\"name\":\"corex-math\",\"vers\":\"1.2.0\",\"deps\":[],\"features\":{\"default\":[]}}\n",
    });

    const manifest_path = proj_dir ++ "/corex.toml";
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = manifest_path,
        .data = "[package]\nname = \"calc-cli\"\nversion = \"0.1.0\"\nedition = \"2026\"\n\n[dependencies]\ncorex-math = \"^1.0.0\"\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = proj_dir ++ "/src/main.cx",
        .data = "use corex_math.Vec2;\n" ++
            "use corex_math.ops.sum_vec;\n\n" ++
            "pub fn main() -> i32 {\n" ++
            "    let pt = Vec2 { x: 19, y: 23 };\n" ++
            "    return sum_vec(pt);\n" ++
            "}\n",
    });

    var env_map = std.process.Environ.Map.init(allocator);
    defer env_map.deinit();
    try env_map.put("COREX_HOME", home_dir);
    try env_map.put("COREX_REGISTRY_DIR", reg_dir);

    var out_buf: [4096]u8 = undefined;
    var err_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    var err_writer = std.Io.Writer.fixed(&err_buf);
    const mp_flag = "--manifest-path=" ++ manifest_path;

    // [1] Unlocked `corex check` resolves `corex-math 1.2.0`, mounts `.cxtree`, verifies `use pkg.Vec2`, and writes `corex.lock`:
    const exit_check = try runCli(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", mp_flag },
        &out_writer,
        &err_writer,
    );
    if (exit_check != 0) {
        std.debug.print("E2E stderr:\n{s}\n", .{err_writer.buffered()});
    }
    try std.testing.expectEqual(@as(u8, 0), exit_check);

    // [2] Subsequent `--frozen` (`--locked` + `--offline`) check with `COREX_REGISTRY_DIR` removed succeeds purely from CAS + `corex.lock`:
    _ = env_map.swapRemove("COREX_REGISTRY_DIR");
    out_writer = std.Io.Writer.fixed(&out_buf);
    err_writer = std.Io.Writer.fixed(&err_buf);
    const exit_frozen = try runCli(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--frozen", "--verify-checksums", mp_flag },
        &out_writer,
        &err_writer,
    );
    if (exit_frozen != 0) {
        std.debug.print("Frozen stderr:\n{s}\n", .{err_writer.buffered()});
    }
    try std.testing.expectEqual(@as(u8, 0), exit_frozen);
}

test "test_direct_script_invocation_and_dual_lib_bin_scope" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] Direct `corex script.cx arg1` and `corex --offline script.cx` route to `.run` with 9 canonical subcommands:
    try std.testing.expectEqual(@as(usize, 9), SUBCOMMANDS.len);
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const parsed = try parseArgs(&.{ "hello.cx", "user_arg" }, &sink);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(parsed.action == .execute_subcommand);
        try std.testing.expectEqual(SubcommandId.run, parsed.action.execute_subcommand.subcommand);
        try std.testing.expectEqual(@as(usize, 1), parsed.action.execute_subcommand.pre_dash_arg_count);
        try std.testing.expectEqual(@as(usize, 1), parsed.run_args.len);
        try std.testing.expectEqualStrings("user_arg", parsed.run_args[0]);
    }
    {
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();
        const parsed_off = try parseArgs(&.{ "--offline", "hello.cx" }, &sink);
        try std.testing.expect(!sink.hasErrors());
        try std.testing.expect(parsed_off.is_offline);
        try std.testing.expectEqual(SubcommandId.run, parsed_off.action.execute_subcommand.subcommand);
    }

    // [2] Dual `[lib]` + `[[bin]]` package registers `lib` as `.root` scope (`use pkg.…` & `use <pkg_name>.…`):
    const tmp_root = ".zig-cache/router_dual_lib_bin_test";
    std.Io.Dir.cwd().deleteTree(io, tmp_root) catch {};
    defer std.Io.Dir.cwd().deleteTree(io, tmp_root) catch {};
    const src_dir = tmp_root ++ "/src";
    const home_dir = tmp_root ++ "/home";
    try std.Io.Dir.cwd().createDirPath(io, src_dir);
    try std.Io.Dir.cwd().createDirPath(io, home_dir);

    const manifest_path = tmp_root ++ "/corex.toml";
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = manifest_path,
        .data = "[package]\nname = \"dual-demo\"\nversion = \"0.1.0\"\n" ++
            "[lib]\npath = \"src/root.cx\"\n" ++
            "[[bin]]\nname = \"dual-cli\"\npath = \"src/main.cx\"\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = src_dir ++ "/root.cx",
        .data = "pub fn answer() -> i32 { return 42; }\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = src_dir ++ "/main.cx",
        .data = "use pkg.answer;\nuse dual_demo.answer as named_answer;\n" ++
            "pub fn main() -> i32 { return answer() - named_answer(); }\n",
    });

    var env_map = std.process.Environ.Map.init(allocator);
    defer env_map.deinit();
    try env_map.put("COREX_HOME", home_dir);

    var out_buf: [4096]u8 = undefined;
    var err_buf: [4096]u8 = undefined;
    var out_writer = std.Io.Writer.fixed(&out_buf);
    var err_writer = std.Io.Writer.fixed(&err_buf);
    const exit_check = try runCli(
        allocator,
        io,
        &env_map,
        &.{ "--color=never", "check", "--manifest-path=" ++ manifest_path },
        &out_writer,
        &err_writer,
    );
    if (exit_check != 0) {
        std.debug.print("Dual lib+bin stderr:\n{s}\n", .{err_writer.buffered()});
    }
    try std.testing.expectEqual(@as(u8, 0), exit_check);
}

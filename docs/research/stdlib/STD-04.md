# Phase 11.3 Standard Library Specification (STD-04): Declarative CLI and Monochrome Terminal Engine, simdjson and Lossless-TOML Serde, and Deterministic Simulation, Fuzzing, and MAD Benchmarking

Completing **Phase 11.3** of **CoreX** (`.cx`) delivers the final four Tier-3 and Tier-4 bootstrap standard library modules – `stdlib/cx/cli.cx`, `stdlib/cx/serde.cx`, `stdlib/cx/test.cx`, and `stdlib/cx/bench.cx` – required to build, verify, and self-host `compiler/*.cx` in Phase 12 without external third-party packages or Stage-0 legacy syntax. Across all four modules, public APIs conform strictly to the locked CoreX v1.0 surface specification (`DR-21` and `DR-22`): the unified `cx.*` root namespace and `.` path separator, payload-first `T!E` and `T?` algebraic types, second-class Mutable Value Semantics (MVS) parameter modes (`&T`, `&mut T`, `own T`, `&out T`) partitioned by `/` positional-only and `*` keyword-only zones, word-based boolean logic (`and`, `or`, `not`) paired with `~x` bitwise complement, zero-allocation stack `FmtArgs`, `.rodata`-backed `@caller_location()` defaults, and first-class `test "…"` and `bench "…"` declarations. Every untrusted input boundary (`argv`, JSON-RPC frames, `corex.toml` manifests, and fuzz corpora) executes via non-backtracking linear DFAs or SIMD/SWAR block pipelines with explicit compile-time and runtime resource caps (`MAX_FLAG_LEN = 64`, `MAX_JSON_DEPTH = 64`, `MAX_TOML_DEPTH = 64`, `MAX_LSP_FRAME_BYTES = 16 MiB`, `MAX_DIFF_COST = 4,096`), and all terminal surfaces emit strictly monochrome Unicode box-drawing and geometric glyphs (`╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠\u{FE0E}`) honoring `NO_COLOR` and `--color=always|auto|never` with zero colored emojis.

Architecturally, `cx.cli` validates declarative `@cli_command`, `@cli_subcommand`, `@arg`, and `@flag` schemas inside `MirVm` at `comptime` (`DR-05`) – catching duplicate short/long flags and out-of-order flag declarations at compile time while freezing formatted `--help` cards into `.rodata` – and parses OS `argv` in a single zero-allocation pass backed by a 195-byte stack-resident Optimal String Alignment (Damerau–Levenshtein) typo matcher and a streaming monochrome terminal engine for multi-span diagnostics, Myers O(ND) unified diffs, auto-sized tables, and `DECSET 2026` TTY spinners. `cx.serde` pairs a two-stage `simdjson` 64-bit `JsonTape` (`>= 1.5 GB/s` target throughput, zero-copy unescaped string slicing for `< 10 ms` P99 `corex lsp` JSON-RPC framing, two-tier `comptime` struct specialization, and Eisel–Lemire float parsing) with a TOML v1.1.0-compliant lossless concrete syntax tree (`8 B` `TomlToken` + `16 B` `TomlCstNode`) that emits surgical `ByteTextEdit` patches to `corex.toml` without disturbing inline or section-header comments.

For verification and performance gating, `cx.test` unifies parallel unit and golden `.snap` execution with a single-process deterministic `Context` simulation harness (`corex test --sim --seed`, `DR-18`) – driving virtual monotonic time, Burckhardt Probabilistic Concurrency Testing (PCT) task interleaving, simulated fsync/network faults, and prefix-digest-verified exhaustive `System` and `Arena` `OOM` countdown sweeps from a single `SplitMix64` → `Xoshiro256**` stream – and an in-process `SanitizerCoverage` fuzzing engine (`corex test --fuzz`) featuring 32-byte SIMD 8-bit counter hit-bucketing, 16 KiB `TORC` comparison/division rings, `@derive(Arbitrary)` `ChoiceCursor` generation, and 5-pass shortlex crash shrinking into `tests/fuzz/corpus/`. Finally, `cx.bench` pairs register- and memory-safe `black_box` compiler barriers with adaptive monotonic batch calibration, **Median Absolute Deviation (`1.4826 × MAD`)** 50%-breakdown-point outlier filtering (isolating fast-path `Median` and `StdDev` from OS preemption spikes while preserving raw `P95` and `P99` tail metrics), and per-iteration `Arena` and `System` peak memory tracking. Hardware PMU cycle/cache-miss counters (`perf_event_open` / `kpc`), multi-node VOPR cluster simulation, and 120 FPS `cx.tui` / `cx.ui` engines remain deferred to Phase 13+ per `DR-20` `Prune-07`.

---

## 1. Declarative Zero-Allocation CLI and Canonical Monochrome Terminal Engine (cx.cli)

`cx.cli` (`stdlib/cx/cli.cx`) serves simultaneously as the user-facing standard library CLI package and as the shared terminal engine imported by `compiler/main.cx` (the unified `corex` router), `compiler/diag.cx` (`DiagnosticRenderer`), `compiler/upgrade.cx` (`TransactionalPatcher` `--dry-run` diffs), `corex check --caps`, and `corex bench`. Unlike Rust's `clap_derive` – which depends on `syn`/`quote` procedural macros that re-parse token streams from scratch (imposing a 3.73x–3.78x single-threaded compile-time penalty relative to reflection in developer benchmarks by Amos Wenger) – or imperative runtime builders whose manual help strings drift from parser logic, `cx.cli` validates declarative `@attribute_schema` structs inside `MirVm` at `comptime` and freezes static dispatch and `--help` tables directly into `.rodata`.

> **Visual – Comptime Schema Freezing Eliminates Runtime Heap Allocations Across CLI Parsing and Monochrome Rendering:** Top: Declarative struct and enum attributes are validated once inside MirVm at compile time – enforcing flag uniqueness and alphabetical order – and emitted as .rodata descriptors consumed by a zero-allocation argv state machine and a 195-byte stack Damerau–Levenshtein matcher. Bottom: The four shared monochrome rendering primitives strictly obey NO_COLOR and avoid colored emojis.

### 1.1 Compile-Time Attribute Schemas, Alphabetical Drift Guard, and Zero-Alloc argv DFA

Under `DR-05`'s Signature Firewall, `@cli_command`, `@cli_subcommand`, `@arg`, and `@flag` are passive, type-checked `@attribute_schema` structs validated during Phase-2 bidirectional checking – giving `corex lsp` sub-millisecond autocomplete and hover documentation inside attribute arguments – while schema verification and help synthesis run inside `MirVm` during Phase-3 constant evaluation. When `validate_cli_schema[T]()` executes in `MirVm`, it walks `@type_info[T]()` and enforces four compile-time invariants via `@compile_assert` before machine code generation begins. First, no two `@arg` or `@flag` fields on a struct may share a `short: char` (`'o'`) or `long: str` (`"output"`), nor shadow built-in `-h` / `--help`, `-V` / `--version`, or `--color` flags unless `override_builtin_help: true` is declared; on `@cli_subcommand` enums, all variant names and `alias` strings must likewise be pairwise disjoint. Second, to guarantee zero documentation and help-table drift, non-positional `@flag` and `@arg` fields must be declared in strict ASCII lexicographical order of their `long` name (followed by `@arg(positional: true)` fields in consumption order), and `@cli_subcommand` enum variants must be declared in strict alphabetical order of subcommand name (matching `PLAN.md`: `add`, `bench`, `build`, `check`, `fmt`, `lsp`, `remove`, `run`, `semver-check`, `test`, `translate-c`, `update`, `upgrade`). Third, `MirVm` verifies that every `@flag` field is `bool` or `u8` (for countable flags such as `-vvv`) and every `@arg` field implements `FromCliStr` (`str`, `cx.path.Path`, `Integer`, `Float`, `bool`, `cx.net.SocketAddr`, fieldless `enum`s, or `T?`). Fourth, `render_help_text[T]() -> str` pre-computes display widths for every flag signature (`-o, --output <PATH>`), `[env: …]` hint, and default literal, formats a monochrome box-drawn `--help` card, and interns the resulting string into `.rodata` (`AllocTag = 2`) so `--help` executes a single `write` syscall with zero runtime string formatting.

At runtime, `parse_from_slice[T](raw_args: &[str]) -> T!CliError` runs a **single-pass, non-backtracking DFA** over `&[str]` verified `@no_alloc` (`0` heap allocations). Every `str` or `Path` field in `T` borrows its UTF-8 slice directly from `raw_args` – which on Linux and macOS slices the kernel's initial process-stack `argv` block directly (`rho_static`), and on Windows slices a single startup `Arena` transcoding of `GetCommandLineW`. The DFA handles subcommand variant dispatch, `--long val`, `--long=val`, negatable `--no-<long>`, `-s val`, `-s=val`, attached short values (`-j8`, `-ofmt=c`), POSIX short-flag clusters (`-vq` toggling `-v` and `-q` in place, or `-vo app.bin` binding `app.bin` to trailing valued `-o`), the `--` literal positional separator, and zero-alloc `cx.env.var_borrowed` environment fallbacks when an optional CLI flag is omitted.

### 1.2 Stack-Allocated Damerau–Levenshtein Typo Suggestion and Monochrome Terminal Primitives

When the `argv` DFA rejects an unknown flag (`--sast-strcit`) or subcommand (`corex bulid`), allocating a heap edit-distance matrix would violate `cx.cli`'s `@no_alloc` contract. Instead, `damerau_levenshtein_osa` computes **Optimal String Alignment (restricted Damerau–Levenshtein distance)** across three rolling 65-byte stack rows (`prev2`, `prev1`, `curr`: `195 bytes` total stack memory, bounded by `MAX_FLAG_LEN = 64`). Adjacent transpositions (`ab` ↔ `ba`) cost `1` edit instead of `2` substitutions, length deltas exceeding `max_dist` (`2` for tokens > 3 bytes, `1` for short tokens) return immediately in O(1), and each outer iteration tracks `row_min` to abort early whenever all row entries exceed `max_dist`.

All CLI diagnostics, diffs, tables, and progress indicators across `corex` and user applications share five zero-emoji monochrome primitives in `cx.cli`:

| Primitive | Core Data Structure & Hard Bounds | Monochrome Typography & Streaming Mechanics | Primary Toolchain Consumers |
| :--- | :--- | :--- | :--- |
| **`Style` & `TermCaps`** | `Style` (`2 B` ANSI SGR + color), `ColorChoice` (`.Auto`, `.Always`, `.Never`) | Checks `NO_COLOR` (non-empty disables ANSI color), `TERM == "dumb"`, `--color`, and `isatty(fd)` once. Zero colored emojis; `glyphs.WARN` appends `U+FE0E` (`"⚠\u{FE0E}"`) to force text presentation. | Universal across `corex` & user CLI apps |
| **`SnippetRenderer`** | `DiagReportView`, `LabeledSpanView`, stack `[BridgeLane; 8]` (`MAX_MULTILINE_LANES = 8`) | Streams `╭─ ✗ E0306 │ title` headers, `▸ file:line:col` pointers, line gutters (`│`), single-line `───▸` underline carets, and 8-lane non-crossing vertical multiline bridges (`╭─` → `│` → `╰─▸`) via `cx.str.display_width` (`wcwidth`) with **0 heap allocations**. | `compiler/diag.cx`, `corex check`, `cx.serde.toml` diagnostics |
| **`TransactionalPatcher` & `MyersDiff`** | `ByteTextEdit { start_byte, end_byte, replacement }`, Myers O(ND) (`MAX_DIFF_COST = 4,096`) | Verifies strictly sorted, non-overlapping byte spans before atomic `UnlinkAndReplace` disk commit (`Prune-02`). Trims shared prefix/suffix lines and computes minimal edit hunks (`context_lines = 3`), rendering `╭─ ▸ Diff ─╮` frames with `│ -` and `│ +` gutters. | `corex upgrade --dry-run`, `corex fix`, `cx.serde.toml`, `cx.test` |
| **`TableRenderer`** | `ColumnSpec { header, align, min_width, max_width }`, stack `[u16; 16]` widths (`MAX_TABLE_COLS = 16`) | Measures ANSI-stripped cell `display_width` and streams `╭─┬─╮`, `├─┼─┤`, `│ │ │`, `╰─┴─╯` box tables with `.Left`, `.Right`, and `.Center` padding plus `…` width clamping. | `corex bench`, `corex check --caps`, `--help` |
| **`ProgressSpinner`** | `ProgressSpinner` (`frame_idx: u8`, `last_draw: Instant`, `caps: TermCaps`) | Advances 10-frame Braille sequence `⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏` at `>= 80 ms` intervals bracketed inside `DECSET 2026` (`\x1b[?2026h\r\x1b[2K…\x1b[?2026l`) on interactive TTYs; degrades cleanly on non-TTY pipes/CI. | `corex build`, `corex test --fuzz`, `pkg` fetch |

### 1.3 Canonical Public API Signatures for stdlib/cx/cli.cx

```rust
// File: stdlib/cx/cli.cx
mod cli;

use cx.col.Vec;
use cx.io.{IoError, Writer};
use cx.mem.Arena;
use cx.time.Instant;

// ============================================================================
// [1] MONOCHROME GLYPH VOCABULARY & TERMINAL STYLE ENGINE (AGENTS.md §5)
// ============================================================================

pub mod glyphs {
    pub const CORNER_TL: str = "╭";
    pub const CORNER_TR: str = "╮";
    pub const CORNER_BL: str = "╰";
    pub const CORNER_BR: str = "╯";
    pub const HORIZ: str     = "─";
    pub const VERT: str      = "│";
    pub const TEE_RIGHT: str = "├";
    pub const TEE_LEFT: str  = "┤";
    pub const TEE_DOWN: str  = "┬";
    pub const TEE_UP: str    = "┴";
    pub const CROSS: str     = "┼";
    pub const ELLIPSIS_V: str = "⋮";
    pub const POINTER: str   = "▸";
    pub const BULLET: str    = "•";
    pub const PASS: str      = "✓";
    pub const FAIL: str      = "✗";
    pub const WARN: str      = "⚠\u{FE0E}"; // VS15 forces monochrome text glyph
    pub const BRAILLE_FRAMES: [str; 10] = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"];
    pub const BLOCK_EIGHTHS: [str; 8]   = ["▏", "▎", "▍", "▌", "▋", "▊", "▉", "█"];
}

@derive(Copy, Equatable)
pub enum ColorChoice: u8 {
    Auto   = 0,
    Always = 1,
    Never  = 2,
}

@derive(Copy, Equatable)
pub enum AnsiColor: u8 {
    Default = 0,
    Red     = 1,
    Green   = 2,
    Yellow  = 3,
    Blue    = 4,
    Cyan    = 5,
    Magenta = 6,
    Gray    = 7,
}

@derive(Copy, Equatable)
pub bit_field StyleFlags: u8 {
    pub bold:      bool | 1,
    pub dim:       bool | 1,
    pub underline: bool | 1,
    pub reverse:   bool | 1,
    pub _reserved: u8   | 4,
}

@derive(Copy, Equatable)
pub struct Style {
    pub fg: AnsiColor = .Default,
    pub flags: StyleFlags = StyleFlags { bold: false, dim: false, underline: false, reverse: false, _reserved: 0 },
}

@derive(Copy, Equatable)
pub struct TermCaps {
    pub color_enabled: bool = false,
    pub is_tty: bool = false,
    pub sync_output_2026: bool = false,
    pub width_cols: u16 = 80,
}

impl TermCaps {
    @no_alloc
    pub fn detect(fd: i32, /, *, choice: ColorChoice = .Auto) -> Self;
}

// ============================================================================
// [2] DECLARATIVE COMPTIME-VALIDATED CLI ATTRIBUTE SCHEMAS & PARSER
// ============================================================================

pub const MAX_FLAG_LEN: usize = 64;
pub const MAX_TYPO_DIST: u8   = 2;

@attribute_schema(targets: .Struct | .Enum)
pub struct CliCommandAttr {
    pub name: str,
    pub version: str = "0.0.1",
    pub about: str = "",
    pub override_builtin_help: bool = false,
}

@attribute_schema(targets: .EnumVariant)
pub struct CliSubcommandAttr {
    pub name: str,
    pub alias: str? = .None,
    pub about: str = "",
}

@attribute_schema(targets: .StructField)
pub struct ArgAttr {
    pub short: char? = .None,
    pub long: str = "",
    pub value_name: str = "VAL",
    pub help: str = "",
    pub env: str? = .None,
    pub positional: bool = false,
}

@attribute_schema(targets: .StructField)
pub struct FlagAttr {
    pub short: char? = .None,
    pub long: str,
    pub help: str = "",
    pub negatable: bool = false,
}

pub trait FromCliStr {
    fn parse_cli_str(raw: str, /) -> Self!str;
}

@derive(Equatable)
pub enum CliError {
    HelpRequested(str),
    VersionRequested(str),
    MissingRequiredArg { flag_or_pos: str, help_hint: str },
    MissingFlagValue { flag: str, value_name: str },
    UnknownFlag { token: str, suggestion: str? },
    UnknownSubcommand { token: str, suggestion: str? },
    UnexpectedPositional { token: str },
    InvalidValue { flag: str, raw: str, reason: str },
}

/// Validates duplicate short/long flags, reserved flags, and strict alphabetical ordering in MirVm.
pub comptime fn validate_cli_schema[T]();

/// Synthesizes and freezes the monochrome box-drawn `--help` card into `.rodata` at compile time.
pub comptime fn render_help_text[T]() -> str;

/// Zero-allocation single-pass `argv` parser borrowing `str` slices directly from `raw_args`.
@no_alloc
pub fn parse_from_slice[T](raw_args: &[str], /) -> T!CliError;

/// Parses OS `argv` (touching `arena` only if OS UTF-16->UTF-8 startup transcoding is needed on Windows).
pub fn parse_args[T](arena: &mut Arena, /) -> T!CliError;

/// Stack-allocated 3-row Optimal String Alignment (Damerau-Levenshtein) matcher (`195 B` stack, 0 heap).
@no_alloc @no_panic
pub fn damerau_levenshtein_osa(a: str, b: str, /, *, max_dist: u8 = MAX_TYPO_DIST) -> u8;

@no_alloc @no_panic
pub fn suggest_closest_token(unknown: str, candidates: &[str], /, *, max_dist: u8 = MAX_TYPO_DIST) -> str?;

@no_alloc
pub fn write_cli_error[W: Writer](out: &mut W, err: &CliError, /, *, caps: TermCaps) -> unit!IoError;

// ============================================================================
// [3] MONOCHROME MULTI-SPAN DIAGNOSTICS, UNIFIED DIFFS, TABLES & SPINNERS
// ============================================================================

pub const MAX_MULTILINE_LANES: usize = 8;
pub const MAX_DIFF_COST: usize       = 4_096;
pub const MAX_TABLE_COLS: usize      = 16;

@derive(Copy, Equatable)
pub enum DiagSeverity: u8 {
    Error   = 0,
    Warning = 1,
    Note    = 2,
    Help    = 3,
}

@derive(Copy, Equatable)
pub struct SourceSpanView {
    pub file_path: str,
    pub source: str,
    pub start_byte: u32,
    pub end_byte: u32,
    pub start_line: u32, // 0-based line index from SIMD LineIndex
    pub end_line: u32,
}

@derive(Copy)
pub struct LabeledSpanView {
    pub span: SourceSpanView,
    pub label: str,
    pub is_primary: bool = false,
}

pub struct DiagReportView {
    pub severity: DiagSeverity,
    pub code: str,
    pub title: str,
    pub spans: &[LabeledSpanView],
    pub notes: &[str] = &[],
    pub help: str? = .None,
}

/// Streams a multi-span diagnostic with 8-lane Unicode multiline bridges and 0 heap allocations.
@no_alloc
pub fn render_diagnostic[W: Writer](
    out: &mut W,
    report: &DiagReportView,
    /,
    *,
    caps: TermCaps,
) -> unit!IoError;

@derive(Copy, Equatable)
pub struct ByteTextEdit {
    pub start_byte: u32,
    pub end_byte: u32,
    pub replacement: str,
}

@derive(From)
pub enum PatchError {
    UnsortedOrOverlappingEdits { index: usize },
    OutOfBoundsEdit { end_byte: u32, source_len: u32 },
    Io(IoError),
}

pub struct TransactionalPatcher {
    arena: &mut Arena,
    staged_files: Vec[(str, Vec[ByteTextEdit])],
}

impl TransactionalPatcher {
    pub fn new(arena: &mut Arena, /) -> Self;
    pub fn stage_edits(&mut self, file_path: str, edits: &[ByteTextEdit], /) -> unit!PatchError;
    pub fn apply_in_memory(arena: &mut Arena, source: str, edits: &[ByteTextEdit], /) -> str!PatchError;
    pub fn preview_unified_diff[W: Writer](
        &self,
        out: &mut W,
        file_path: str,
        old_src: str,
        new_src: str,
        /,
        *,
        context_lines: usize = 3,
        caps: TermCaps,
    ) -> unit!IoError;
    pub fn commit_atomic(own self) -> unit!PatchError;
}

@derive(Copy, Equatable)
pub enum ColAlign: u8 { Left = 0, Right = 1, Center = 2 }

@derive(Copy)
pub struct ColumnSpec {
    pub header: str,
    pub align: ColAlign = .Left,
    pub min_width: u16 = 0,
    pub max_width: u16 = 64,
}

@no_alloc
pub fn render_box_table[W: Writer](
    out: &mut W,
    columns: &[ColumnSpec],
    rows: &[&[str]],
    /,
    *,
    title: str? = .None,
    caps: TermCaps,
) -> unit!IoError;

pub struct ProgressSpinner {
    caps: TermCaps,
    frame_idx: u8,
    started_at: Instant,
    last_draw: Instant,
    active: bool,
}

impl ProgressSpinner {
    @no_alloc
    pub fn start(caps: TermCaps, /) -> Self;
    @no_alloc
    pub fn tick[W: Writer](&mut self, out: &mut W, phase: str, detail: str, /) -> unit!IoError;
    @no_alloc
    pub fn finish[W: Writer](&mut self, out: &mut W, summary: str, /, *, ok: bool = true) -> unit!IoError;
}
```

### 1.4 Reference Implementation: Comptime Validator, Zero-Alloc argv DFA, Stack OSA & Multi-Span Renderer

```rust
// File: stdlib/cx/cli_impl.cx (Core reference implementation for stdlib/cx/cli.cx)
mod cli_impl;

use cx.cli.{
    ArgAttr, CliCommandAttr, CliError, DiagReportView, FlagAttr, FromCliStr,
    MAX_FLAG_LEN, MAX_MULTILINE_LANES, MAX_TYPO_DIST, TermCaps, glyphs,
};
use cx.io.{IoError, Writer};
use cx.meta.TypeInfo;

comptime fn ascii_lt(a: str, b: str, /) -> bool {
    let ab = a.as_bytes();
    let bb = b.as_bytes();
    let limit = if ab.len() < bb.len() { ab.len() } else { bb.len() };
    var i: usize = 0;
    while i < limit {
        if ab[i] != bb[i] {
            return ab[i] < bb[i];
        }
        i += 1;
    }
    ab.len() < bb.len()
}

pub comptime fn validate_cli_schema[T]() {
    const INFO: TypeInfo = @type_info[T]();
    comptime match INFO.kind {
        .Struct(s_info) => {
            var prev_long: str = "";
            var seen_positional = false;
            var i: usize = 0;
            while i < s_info.fields.len() {
                let f_i = s_info.fields[i];
                let arg_i = f_i.get_attr[ArgAttr]();
                let flg_i = f_i.get_attr[FlagAttr]();

                @compile_assert(
                    not (arg_i is .Some(_) and flg_i is .Some(_)),
                    "field cannot carry both @arg and @flag",
                );

                let (long_i, short_i, is_pos_i) = if arg_i is .Some(a) {
                    (a.long, a.short, a.positional)
                } else if flg_i is .Some(fl) {
                    (fl.long, fl.short, false)
                } else {
                    ("", .None, false)
                };

                if is_pos_i {
                    seen_positional = true;
                } else if not long_i.is_empty() {
                    @compile_assert(
                        not seen_positional,
                        "non-positional @arg/@flag fields must precede positional @arg fields",
                    );
                    if not prev_long.is_empty() {
                        @compile_assert(
                            ascii_lt(prev_long, long_i),
                            "@arg/@flag fields must be declared in strict alphabetical order of `long` name",
                        );
                    }
                    prev_long = long_i;
                }

                var j: usize = i + 1;
                while j < s_info.fields.len() {
                    let f_j = s_info.fields[j];
                    let (long_j, short_j) = if f_j.get_attr[ArgAttr]() is .Some(aj) {
                        (aj.long, aj.short)
                    } else if f_j.get_attr[FlagAttr]() is .Some(fj) {
                        (fj.long, fj.short)
                    } else {
                        ("", .None)
                    };
                    if not long_i.is_empty() and not long_j.is_empty() {
                        @compile_assert(long_i != long_j, "duplicate CLI long flag name");
                    }
                    if short_i is .Some(si) and short_j is .Some(sj) {
                        @compile_assert(si != sj, "duplicate CLI short flag character");
                    }
                    j += 1;
                }
                i += 1;
            }
        }
        _ => @compile_error("@cli_command schema requires a struct or subcommand enum"),
    }
}

/// 3-row Optimal String Alignment (Damerau-Levenshtein) using 195 bytes of stack memory (0 heap).
@no_alloc @no_panic
pub fn damerau_levenshtein_osa(a: str, b: str, /, *, max_dist: u8 = MAX_TYPO_DIST) -> u8 {
    let ab = a.as_bytes();
    let bb = b.as_bytes();
    let m = ab.len();
    let n = bb.len();
    let cap_exceeded = max_dist +| 1_u8;

    if m > MAX_FLAG_LEN or n > MAX_FLAG_LEN {
        return cap_exceeded;
    }
    let len_diff = if m > n { m - n } else { n - m };
    if len_diff > (max_dist as usize) {
        return cap_exceeded;
    }

    var row_prev2: [u8; 65] = [0; 65];
    var row_prev1: [u8; 65] = [0; 65];
    var row_curr:  [u8; 65] = [0; 65];

    for j in 0..=n {
        row_prev1[j] = j as u8;
    }

    for i in 1..=m {
        row_curr[0] = i as u8;
        var row_min: u8 = row_curr[0];

        for j in 1..=n {
            let sub_cost: u8 = if ab[i - 1] == bb[j - 1] { 0 } else { 1 };
            let del_v = row_prev1[j] +| 1_u8;
            let ins_v = row_curr[j - 1] +| 1_u8;
            let sub_v = row_prev1[j - 1] +| sub_cost;

            var best = if del_v < ins_v { del_v } else { ins_v };
            if sub_v < best { best = sub_v; }

            // Adjacent character transposition (`--ignroe` -> `--ignore` costs 1 edit)
            if i > 1 and j > 1 and ab[i - 1] == bb[j - 2] and ab[i - 2] == bb[j - 1] {
                let trans_v = row_prev2[j - 2] +| 1_u8;
                if trans_v < best { best = trans_v; }
            }
            row_curr[j] = best;
            if best < row_min { row_min = best; }
        }

        if row_min > max_dist {
            return cap_exceeded;
        }
        (row_prev2, row_prev1, row_curr) = (row_prev1, row_curr, row_prev2);
    }
    row_prev1[n]
}

@no_alloc @no_panic
pub fn suggest_closest_token(
    unknown: str,
    candidates: &[str],
    /,
    *,
    max_dist: u8 = MAX_TYPO_DIST,
) -> str? {
    let eff_max: u8 = if unknown.len() <= 3 { 1 } else { max_dist };
    var best_dist: u8 = eff_max +| 1_u8;
    var best_cand: str? = .None;

    for cand in candidates {
        let d = damerau_levenshtein_osa(unknown, cand, max_dist: eff_max);
        if d < best_dist {
            best_dist = d;
            best_cand = .Some(cand);
        }
    }
    best_cand
}

/// Zero-allocation single-pass `argv` parser (`raw_args[0]` = binary path, `raw_args[1..]` = args).
@no_alloc
pub fn parse_from_slice[T](raw_args: &[str], /) -> T!CliError {
    comptime { validate_cli_schema[T](); }
    const HELP_STR: str = comptime render_help_text[T]();
    const CMD_ATTR: CliCommandAttr = comptime (
        @type_info[T]().get_attr[CliCommandAttr]() orelse CliCommandAttr { name: "app", .. }
    );
    const KNOWN_FLAGS: &[str] = comptime collect_long_flag_names[T]();

    var out: T = @default_init[T]();
    var pos_cursor: usize = 0;
    var idx: usize = if raw_args.is_empty() { 0 } else { 1 };
    var passthrough_pos = false;

    while idx < raw_args.len() {
        let tok = raw_args[idx];
        let bytes = tok.as_bytes();

        if not passthrough_pos and tok == "--" {
            passthrough_pos = true;
            idx += 1;
            continue;
        }
        if not passthrough_pos and (tok == "-h" or tok == "--help") and not CMD_ATTR.override_builtin_help {
            return .Err(.HelpRequested(HELP_STR));
        }
        if not passthrough_pos and (tok == "-V" or tok == "--version") {
            return .Err(.VersionRequested(CMD_ATTR.version));
        }

        if not passthrough_pos and tok.starts_with("--") {
            let body = tok[2..];
            let (flag_name, inline_val) = if body.split_once('=') is .Some((k, v)) {
                (k, .Some(v))
            } else {
                (body, .None)
            };

            var matched = false;
            comptime for field in @type_info[T]().as_struct().fields {
                comptime if field.get_attr[FlagAttr]() is .Some(fl) {
                    if flag_name == fl.long {
                        apply_bool_or_count_flag(&mut @field(out, field), true);
                        matched = true;
                    } else if fl.negatable and flag_name.starts_with("no-") and flag_name[3..] == fl.long {
                        apply_bool_or_count_flag(&mut @field(out, field), false);
                        matched = true;
                    }
                }
                comptime if field.get_attr[ArgAttr]() is .Some(ar) and not ar.positional {
                    if flag_name == ar.long {
                        let val_str = if inline_val is .Some(v) {
                            v
                        } else {
                            idx += 1;
                            if idx >= raw_args.len() {
                                return .Err(.MissingFlagValue { flag: tok, value_name: ar.value_name });
                            }
                            raw_args[idx]
                        };
                        @field(out, field) = FromCliStr.parse_cli_str(val_str)
                            catch |reason| return .Err(.InvalidValue { flag: tok, raw: val_str, reason: reason });
                        matched = true;
                    }
                }
            }
            if not matched {
                let stripped = if flag_name.starts_with("no-") { flag_name[3..] } else { flag_name };
                let hint = suggest_closest_token(stripped, KNOWN_FLAGS);
                return .Err(.UnknownFlag { token: tok, suggestion: hint });
            }
            idx += 1;
            continue;
        }

        if not passthrough_pos and bytes.len() >= 2 and bytes[0] == b'-' {
            var cluster_i: usize = 1;
            while cluster_i < bytes.len() {
                let ch = bytes[cluster_i] as char;
                var short_matched = false;

                comptime for field in @type_info[T]().as_struct().fields {
                    comptime if field.get_attr[FlagAttr]() is .Some(fl) and fl.short is .Some(sc) {
                        if ch == sc {
                            apply_bool_or_count_flag(&mut @field(out, field), true);
                            short_matched = true;
                        }
                    }
                    comptime if field.get_attr[ArgAttr]() is .Some(ar) and ar.short is .Some(sc) {
                        if ch == sc {
                            let rest = tok[cluster_i + 1..];
                            let val_str = if not rest.is_empty() {
                                if rest.starts_with("=") { rest[1..] } else { rest }
                            } else {
                                idx += 1;
                                if idx >= raw_args.len() {
                                    return .Err(.MissingFlagValue { flag: tok, value_name: ar.value_name });
                                }
                                raw_args[idx]
                            };
                            @field(out, field) = FromCliStr.parse_cli_str(val_str)
                                catch |reason| return .Err(.InvalidValue { flag: tok, raw: val_str, reason: reason });
                            short_matched = true;
                            cluster_i = bytes.len();
                        }
                    }
                }
                if not short_matched {
                    return .Err(.UnknownFlag { token: tok, suggestion: .None });
                }
                cluster_i += 1;
            }
            idx += 1;
            continue;
        }

        var pos_matched = false;
        var cur_pos_slot: usize = 0;
        comptime for field in @type_info[T]().as_struct().fields {
            comptime if field.get_attr[ArgAttr]() is .Some(ar) and ar.positional {
                if cur_pos_slot == pos_cursor {
                    @field(out, field) = FromCliStr.parse_cli_str(tok)
                        catch |reason| return .Err(.InvalidValue { flag: ar.value_name, raw: tok, reason: reason });
                    pos_matched = true;
                }
                cur_pos_slot += 1;
            }
        }
        if not pos_matched {
            return .Err(.UnexpectedPositional { token: tok });
        }
        pos_cursor += 1;
        idx += 1;
    }
    .Ok(out)
}

@derive(Copy)
struct BridgeLane {
    active: bool = false,
    span_idx: u16 = 0,
    end_line: u32 = 0,
    is_primary: bool = false,
}

@no_alloc
pub fn render_diagnostic[W: Writer](
    out: &mut W,
    report: &DiagReportView,
    /,
    *,
    caps: TermCaps,
) -> unit!IoError {
    let badge = match report.severity {
        .Error   => glyphs.FAIL,
        .Warning => glyphs.WARN,
        .Note    => glyphs.BULLET,
        .Help    => glyphs.POINTER,
    };
    out.write_fmt("{glyphs.CORNER_TL}{glyphs.HORIZ} {badge} {report.code} {glyphs.VERT} {report.title}\n")?;

    if report.spans.is_empty() {
        out.write_fmt("{glyphs.CORNER_BL}{glyphs.HORIZ}{glyphs.HORIZ}\n")?;
        return .Ok(());
    }

    let primary = report.spans[0].span;
    out.write_fmt(
        "{glyphs.VERT}  {glyphs.POINTER} {primary.file_path}:{primary.start_line + 1}\n{glyphs.VERT}\n",
    )?;

    var lanes: [BridgeLane; MAX_MULTILINE_LANES] = [BridgeLane { .. }; MAX_MULTILINE_LANES];
    let min_line = primary.start_line;
    var max_line = primary.end_line;

    for sp, i in report.spans {
        if sp.span.file_path == primary.file_path and sp.span.end_line > max_line {
            max_line = sp.span.end_line;
        }
        if sp.span.file_path == primary.file_path and sp.span.end_line > sp.span.start_line {
            alloc_lane: for &mut lane in &mut lanes {
                if not lane.active {
                    lane = BridgeLane {
                        active: true,
                        span_idx: i as u16,
                        end_line: sp.span.end_line,
                        is_primary: sp.is_primary,
                    };
                    break :alloc_lane;
                }
            }
        }
    }

    var line_no: u32 = min_line;
    while line_no <= max_line {
        let line_text = extract_line_slice(primary.source, line_no);
        out.write_fmt("{line_no + 1:4} {glyphs.VERT} ")?;
        for &mut lane in &mut lanes {
            if lane.active {
                let sp = report.spans[lane.span_idx as usize];
                if line_no == sp.span.start_line {
                    out.write_all("╭─".as_bytes())?;
                } else if line_no == sp.span.end_line {
                    out.write_all("╰─".as_bytes())?;
                    lane.active = false;
                } else if line_no > sp.span.start_line and line_no < sp.span.end_line {
                    out.write_all("│ ".as_bytes())?;
                } else {
                    out.write_all(b"  ")?;
                }
            }
        }
        out.write_fmt("{line_text}\n")?;

        for sp in report.spans {
            if sp.span.file_path == primary.file_path
                and sp.span.start_line == line_no
                and sp.span.end_line == line_no
            {
                let (col_off, width_cols) = compute_line_display_cols(line_text, sp.span);
                out.write_fmt("     {glyphs.VERT} ")?;
                write_repeated_spaces(out, col_off)?;
                write_repeated_str(out, glyphs.HORIZ, if width_cols > 0 { width_cols } else { 1 })?;
                if not sp.label.is_empty() {
                    out.write_fmt(" {glyphs.POINTER} {sp.label}")?;
                }
                out.write_all(b"\n")?;
            }
        }
        line_no += 1;
    }

    for note in report.notes {
        out.write_fmt("{glyphs.TEE_RIGHT}{glyphs.HORIZ} {glyphs.BULLET} note: {note}\n")?;
    }
    if report.help is .Some(h) {
        out.write_fmt("{glyphs.CORNER_BL}{glyphs.HORIZ} {glyphs.POINTER} help: {h}\n")?;
    } else {
        out.write_fmt("{glyphs.CORNER_BL}{glyphs.HORIZ}{glyphs.HORIZ}\n")?;
    }
    .Ok(())
}
```

---

## 2. Two-Stage simdjson 64-Bit Tape, Comptime Serde, and Lossless Surgical TOML (cx.serde)

`cx.serde` (`stdlib/cx/serde.cx`, comprising `cx.serde.json` and `cx.serde.toml`) backs two critical self-hosted subsystems in Phase 12: `compiler/lsp_server.cx` (serving JSON-RPC 2.0 `stdio` frames under a `< 10 ms` P99 keystroke-to-diagnostic latency budget) and `compiler/pkg_manifest.cx` (parsing `corex.toml` and `corex.lock`, serializing deterministic lockfiles, and emitting comment-preserving surgical manifest edits for `corex add`, `corex remove`, `corex update`, and `corex upgrade`).

> **Visual – Contiguous 64-Bit JSON Tapes, Eisel–Lemire Float Parsing, and 16-Byte TOML CSTs Unify Wire Speed With Lossless Edits:** Top: Stage 1 classifies 64-byte blocks via carryless quote XOR and two 16-byte nibble lookup tables; Stage 2 emits 64-bit TapeWords that skip unknown JSON subtrees in O(1) and slice unescaped strings with zero copies. Middle: Eisel–Lemire float parsing reaches **1,042.38 MB/s** in published benchmarks, more than double Abseil and over five times faster than libc strtod. Bottom: Surgical TOML insertion anchors strictly after the trailing inline comment newline and before the next section header's leading comment block.

### 2.1 Stage-1 SIMD/SWAR Structural Indexing and Stage-2 64-Bit TapeWord + Eisel–Lemire Numbers

Adapting Langdale and Lemire's two-stage `simdjson` architecture (which runs 2x–5x faster than scalar state-machine JSON parsers and reaches up to 2.2 GB/s on `twitter.json` in `simdjson` benchmarks), `cx.serde.json` separates data-parallel 64-byte block indexing (**Stage 1**) from grammar verification and tape writing (**Stage 2**). Unlike C++ `simdjson`, which requires callers to allocate `SIMDJSON_PADDING` trailing bytes on every input buffer, `parse_tape` processes all full 64-byte chunks directly from `raw_utf8: &[u8]` and copies only the final `< 64`-byte tail into a stack-allocated `[u8; 64]` buffer padded with `0x20` (`' '`), making arbitrary `mmap` or `BufReader` slices safe without copying the payload.

In **Stage 1**, full 64-byte blocks pass simultaneously through Keiser–Lemire's 3-LUT SIMD UTF-8 validator (`TOO_SHORT`, `TOO_LONG`, `OVERLONG_2`, `OVERLONG_3`, `SURROGATE`, `TOO_LARGE`, `TWO_CONTS`) and a dual-target structural classifier. On `x86_64`, `aarch64`, and `wasm32` SIMD128, four `Simd[u8, 16]` (or two `Simd[u8, 32]`) vectors classify structural operators (`{`, `}`, `[`, `]`, `:`, `,`) and whitespace (`' '`, `'\t'`, `'\n'`, `'\r'`) via **two 16-byte nibble shuffle tables** intersected by bitwise AND (`cls = LO_LUT[b & 0x0F] & HI_LUT[b >> 4]`):

$$\text{LO\_LUT} = [\texttt{0x10}, 0, 0, 0, 0, 0, 0, 0, 0, \texttt{0x08}, \texttt{0x0A}, \texttt{0x04}, \texttt{0x01}, \texttt{0x0C}, 0, 0]$$
$$\text{HI\_LUT} = [\texttt{0x08}, 0, \texttt{0x11}, \texttt{0x02}, 0, \texttt{0x04}, 0, \texttt{0x04}, 0, 0, 0, 0, 0, 0, 0, 0]$$

Across all 256 byte values, `(cls & 0x07) != 0` matches `{ } [ ] : ,` and `(cls & 0x18) != 0` matches JSON whitespace with zero false positives. Inside `MirVm` `comptime` and the portable C99 bootstrap seed (`-ofmt=c`), Stage 1 falls back seamlessly to a borrow-free **`u64` SWAR classifier** scanning eight `u64` words per block (`lo7 = diff & 0x7F7F...; nonzero = lo7 +% 0x7F7F...; msb = ~(nonzero | diff) & 0x8080...`, gathered via `((msb >> 7) *% 0x0102_0408_1020_4080) >> 56`). Given raw backslash mask $B$, quote mask $Q_{\text{raw}}$, and 1-bit cross-block escape carry $\text{prev\_escaped}$ with `ODD_BITS = 0xAAAA_AAAA_AAAA_AAAA_u64`, odd-length backslash runs and unescaped string spans resolve without branches:

$$\text{pot} = B \ \& \ \sim\text{prev\_escaped}, \quad \text{code} = (((\text{pot} \ll 1) \mid \text{ODD\_BITS}) -\% \text{pot}) \oplus \text{ODD\_BITS}$$
$$\text{escaped} = \text{code} \oplus (B \mid \text{prev\_escaped}), \quad \text{prev\_escaped}' = (\text{code} \ \& \ B) \gg 63$$

Removing escaped quotes yields $Q = Q_{\text{raw}} \ \& \ \sim\text{escaped}$, and carryless prefix-XOR (`pclmulqdq` / `vmull_p64` or a 6-shift SWAR XOR cascade) XORed with `prev_in_string` produces the in-string mask $R$, updating $\text{prev\_in\_string}' = \text{u64}(\text{i64}(R) \gg 63)$ while flagging unescaped control bytes `< 0x20` whenever $(\text{ctrl}_{\text{raw}} \ \& \ R) \neq 0$. Setting $\text{scalar} = \sim(\text{op}_{\text{raw}} \mid \text{ws}_{\text{raw}} \mid R \mid Q)$, the unified structural bitmask is:

$$S = (\text{op}_{\text{raw}} \ \& \ \sim R) \;\mid\; (\text{scalar} \ \& \ \sim((\text{scalar} \ll 1) \mid \text{prev\_scalar})) \;\mid\; (Q \ \& \ R)$$

which marks every unquoted `{ } [ ] : ,`, the start byte of every unquoted scalar (`true`, `false`, `null`, numbers), and every **opening** quote `"` while omitting closing quotes so Stage 2 processes string interiors in a single pass.

In **Stage 2**, the parser iterates over set bits of $S$ (`@ctz` + `S &= S - 1`), tracks open `{` and `[` scopes on a fixed 64-entry stack (`MAX_JSON_DEPTH = 64`, zero heap allocation), and appends 64-bit **`TapeWord`** records (`(tag_u8 << 56) | payload_56`) into `arena`. Opening `'{'` or `'['` at index $i_{\text{open}}$ backpatches `bits[31:0] = i_close + 1` and `bits[55:32] = elem_count_u24` (while closing `'}'` or `']'` stores `i_open`), allowing `TapeCursor.skip_value()` to jump past arbitrarily nested JSON objects or arrays in O(1) time. For strings, when no `\` precedes the closing `"` and `len < (1 << 24)`, Stage 2 emits tag `b'"'` packing `(len << 32) | (quote_off + 1)` – borrowing the UTF-8 slice **directly from `raw_utf8` with zero copies** – and allocates into `string_buf` (tag `b's'`) only when decoding RFC 8259 escapes and UTF-16 surrogate pairs (`0xD800..=0xDBFF` + `\u` + `0xDC00..=0xDFFF`). For floating-point numbers, Stage 2 applies Clinger's exact `f64` fast path (`man < 2^53`, `|exp10| <= 22`) followed by **Eisel–Lemire (`ParseNumberF64`)** over a `comptime`-frozen 651-entry 128-bit `POW5_TABLE` (`exp10` in `-342..=308`, `10,416 bytes` / `10.4 KB` in `.rodata`, deriving binary exponents via `(exp10 * 217706) >> 16`). In `fast_float` benchmark suites cited in the literature, Eisel–Lemire reaches ~1 GB/s (`1,042.38 MB/s` vs. `430.45 MB/s` for Abseil and `190.94 MB/s` for `libc` `strtod`, while newer unrounded-scaling algorithms proposed by Russ Cox for Go 1.27 push simplicity and speed slightly further); the `< 0.1%` ambiguous midpoint or subnormal cases fall back to a stack-allocated High-Precision Decimal (`HPD`) shift-and-round routine with zero heap allocations.

### 2.2 Two-Tier Comptime Struct Serde and Sub-10 ms corex lsp JSON-RPC Framing

`@derive(Serialize, Deserialize)` inspects `@type_info[T]()` and `@serde(rename: "…", skip: false, skip_if_none: false, default_if_missing: false)` inside `MirVm` using `DR-05` §3.4's **Hybrid Two-Tier Reflection Lowering**. For compact DTOs with `<= 8` fields (Tier 1), `comptime for` unrolls serialization inline – emitting pre-concatenated `.rodata` key literals (`"\"uri\":"`) and eliding `T?` fields dynamically when `skip_if_none: true` and `@field(val, f) is .None` – and unrolls deserialization using SWAR 8-byte `u64` key comparisons plus a 64-bit `seen_mask` bitset that validates all required fields in 1 instruction while skipping unknown keys via O(1) `cursor.skip_value()`. For large protocol structs with `> 8` fields such as LSP `ServerCapabilities` (Tier 2), `MirVm` freezes a `.rodata` `[JsonFieldDesc; N]` descriptor array driven by a single shared loop, avoiding exponential CTTI binary and instruction-cache growth. In `compiler/lsp_server.cx`, `read_lsp_frame` parses `Content-Length: <N>\r\n\r\n` headers (`N <= MAX_LSP_FRAME_BYTES = 16 MiB`), checkpoints a reusable 64 KiB `Arena`, builds `JsonTape` in tens of microseconds for typical edit payloads while slicing URIs and text changes in place, and leaves over 98% of the `< 10 ms` P99 budget for `CompilerDb` semantic analysis.

### 2.3 Lossless TOML v1.1.0 TokenBuffer (8B), TomlCstArena (16B), Serializer, and Surgical Patcher

`cx.serde.toml` implements the full **TOML v1.1.0** specification (released December 18, 2025) – supporting multi-line inline tables with newlines and trailing commas, `\e` (`U+001B`) and `\xHH` basic-string escapes, optional seconds in `LocalTime` and `DateTime` (`07:32`, `2026-11-20 11:52Z`), and bare/quoted/dotted keys – plus an opt-in `TomlSpec.V1_0` strict compatibility flag. To support both deterministic `corex.lock` generation (`to_writer` / `to_slice`, formatting lexicographically sorted `[[package]]` arrays and canonical keys per `DR-11` §1.4) and comment-preserving `corex.toml` edits, `parse_cst` builds two `#soa` tables: an exact **8-byte `TomlToken`** stream (`TomlTokenBuffer`) partitioning 100% of source bytes including `Whitespace`, `Newline`, and `Comment` tokens (rejecting illegal control bytes `0x00..=0x08`, `0x0A..=0x1F`, `0x7F` per TOML v1.1.0), and an exact **16-byte `TomlCstNode`** tree (`TomlCstArena`, enforcing `MAX_TOML_DEPTH = 64` and `DEFAULT_MAX_TOML_BYTES = 16 MiB`).

To prevent the classic surgical-patching bug where appending a dependency to `[dependencies]` inserts it *below* the `# Developer test tools` comment header preceding `[dev-dependencies]`, `TomlCstNode` enforces a **Strict Trivia-Boundary Ownership Invariant**: every `KeyValue` node's `last_token` spans through any same-line horizontal whitespace, optional same-line `# inline comment`, and the terminating `\r?\n` of that line, whereas subsequent blank lines and full-line `#` comment blocks attach to the following `KeyValue` or `TableSection`. Consequently, `TomlEditor.set_key` inserts new entries at `end_byte(last_kv.last_token)` – preserving both the previous line's inline comment and the next table header's doc comments – and updates existing keys by emitting a `ByteTextEdit` strictly over `[val_node.start_byte .. val_node.end_byte)`.

### 2.4 Canonical Public API Signatures for stdlib/cx/serde.cx

```rust
// File: stdlib/cx/serde.cx
mod serde;

use cx.cli.ByteTextEdit;
use cx.col.Vec;
use cx.io.{BufReader, IoError, Reader, Writer};
use cx.mem.Arena;

// ============================================================================
// [1] SHARED @serde ATTRIBUTE SCHEMAS & GENERIC TRAITS
// ============================================================================

@derive(Copy, Equatable)
pub enum RenameRule: u8 {
    None           = 0,
    LowerCase      = 1,
    ScreamingSnake = 2,
    CamelCase      = 3,
    PascalCase     = 4,
    KebabCase      = 5,
}

@attribute_schema(targets: .Struct | .Enum)
pub struct SerdeContainerAttr {
    pub rename_all: RenameRule = .None,
    pub deny_unknown_fields: bool = false,
    pub tag: str? = .None,
}

@attribute_schema(targets: .StructField | .EnumVariant)
pub struct SerdeAttr {
    pub rename: str? = .None,
    pub skip: bool = false,
    pub skip_if_none: bool = false,
    pub default_if_missing: bool = false,
}

pub trait Serialize {
    fn serialize_json[W: Writer](&self, out: &mut W, /) -> unit!IoError;
}

pub trait Deserialize {
    fn deserialize_json(cursor: &mut json.TapeCursor, /) -> Self!json.JsonError;
}

// ============================================================================
// [2] cx.serde.json: TWO-STAGE 64-BIT SIMD/SWAR JSON TAPE & LSP FRAMING
// ============================================================================

pub mod json {
    use super.{Deserialize, Serialize};
    use cx.io.{BufReader, IoError, Reader, Writer};
    use cx.mem.Arena;

    pub const MAX_JSON_DEPTH: u32           = 64;
    pub const DEFAULT_MAX_JSON_BYTES: usize = 64 * 1024 * 1024;
    pub const MAX_LSP_FRAME_BYTES: usize    = 16 * 1024 * 1024;

    @derive(Copy, Equatable)
    pub struct JsonLimits {
        pub max_depth: u32 = MAX_JSON_DEPTH,
        pub max_bytes: usize = DEFAULT_MAX_JSON_BYTES,
    }

    @derive(Copy, Equatable)
    pub enum TapeTag: u8 {
        Root        = b'r',
        ObjectStart = b'{',
        ObjectEnd   = b'}',
        ArrayStart  = b'[',
        ArrayEnd    = b']',
        StrBorrowed = b'"', // Zero-copy slice into `raw_utf8`: (len_u24 << 32) | off_u32
        StrArena    = b's', // Unescaped slice into `string_buf`: (len_u24 << 32) | off_u32
        Int64       = b'l', // Next TapeWord holds two's-complement i64 bits
        Uint64      = b'u', // Next TapeWord holds u64 bits
        Float64     = b'd', // Next TapeWord holds IEEE-754 f64 bits
        True        = b't',
        False       = b'f',
        Null        = b'n',
    }

    /// 64-bit contiguous tape word: `(tag_u8 << 56) | payload_56`.
    @derive(Copy, Equatable)
    pub type TapeWord = distinct u64;

    impl TapeWord {
        @inline @no_alloc @no_panic
        pub fn pack(tag: TapeTag, payload: u64, /) -> Self;
        @inline @no_alloc @no_panic
        pub fn tag(self) -> TapeTag;
        @inline @no_alloc @no_panic
        pub fn payload56(self) -> u64;
        @inline @no_alloc @no_panic
        pub fn jump_idx(self) -> usize;   // Bits [31:0] on '{' / '[' / '}' / ']' / 'r'
        @inline @no_alloc @no_panic
        pub fn count_or_len(self) -> u32; // Bits
    }

    pub struct JsonTape {
        pub raw_utf8: &[u8],
        pub words: &[TapeWord],
        pub string_buf: &[u8],
    }

    impl JsonTape {
        @inline @no_alloc @no_panic
        pub fn root(&self) -> TapeCursor;
    }

    @derive(Copy)
    pub struct TapeCursor {
        pub tape: &JsonTape,
        pub idx: usize,
    }

    impl TapeCursor {
        @inline @no_alloc @no_panic
        pub fn kind(&self) -> TapeTag;
        @inline @no_alloc @no_panic
        pub fn skip_value(&mut self);
        @no_alloc
        pub fn read_str(&mut self) -> str!JsonError;
        @no_alloc
        pub fn read_i64(&mut self) -> i64!JsonError;
        @no_alloc
        pub fn read_u64(&mut self) -> u64!JsonError;
        @no_alloc
        pub fn read_f64(&mut self) -> f64!JsonError;
        @no_alloc
        pub fn read_bool(&mut self) -> bool!JsonError;
        @no_alloc
        pub fn find_object_field(&self, key: str, /) -> TapeCursor?;
        @no_alloc
        pub fn at_pointer(&self, rfc6901_ptr: str, /) -> TapeCursor?;
    }

    @derive(Copy, Equatable)
    pub enum JsonError {
        PayloadTooLarge { len: usize, max: usize },
        DepthLimitExceeded { max_depth: u32, offset: usize },
        InvalidUtf8 { offset: usize },
        UnclosedString { offset: usize },
        UnescapedControlChar { offset: usize, byte: u8 },
        InvalidEscape { offset: usize },
        InvalidUnicodeSurrogate { offset: usize },
        InvalidNumber { offset: usize },
        UnexpectedToken { offset: usize, expected: str },
        TrailingCharacters { offset: usize },
        MissingRequiredField { field: str },
        UnknownField { field: str },
    }

    /// Stage 1 + Stage 2 SIMD/SWAR 64-bit tape parser (borrows unescaped strings in place).
    pub fn parse_tape(
        arena: &mut Arena,
        raw_utf8: &[u8],
        /,
        *,
        limits: JsonLimits = JsonLimits { .. },
    ) -> JsonTape!JsonError;

    /// Exact Eisel-Lemire + stack HPD fallback float parser.
    @no_alloc @no_panic
    pub fn parse_f64_eisel_lemire(raw_num: &[u8], /) -> f64!JsonError;

    /// Typed `comptime`-specialized deserialization (Tier 1 <=8 fields inline SWAR, Tier 2 >8 fields .rodata schema).
    pub fn from_slice[T: Deserialize](
        arena: &mut Arena,
        raw_utf8: &[u8],
        /,
        *,
        limits: JsonLimits = JsonLimits { .. },
    ) -> T!JsonError;

    pub fn to_writer[T: Serialize, W: Writer](out: &mut W, val: &T, /) -> unit!IoError;
    pub fn to_slice[T: Serialize](arena: &mut Arena, val: &T, /) -> &[u8]!IoError;

    /// Zero-copy `corex lsp` JSON-RPC 2.0 `Content-Length` frame reader & writer.
    pub fn read_lsp_frame[R: Reader](
        arena: &mut Arena,
        reader: &mut BufReader[R],
        /,
        *,
        max_bytes: usize = MAX_LSP_FRAME_BYTES,
    ) -> JsonTape!LspFrameError;

    pub fn write_lsp_frame[T: Serialize, W: Writer](out: &mut W, payload: &T, /) -> unit!IoError;

    @derive(From)
    pub enum LspFrameError {
        Eof,
        Io(IoError),
        MissingContentLength,
        FrameTooLarge { len: usize, max: usize },
        MalformedHeader,
        Json(JsonError),
    }
}

// ============================================================================
// [3] cx.serde.toml: LOSSLESS 8B TOKEN / 16B CST, SERIALIZER & PATCHER
// ============================================================================

pub mod toml {
    use cx.cli.ByteTextEdit;
    use cx.col.Vec;
    use cx.io.{IoError, Writer};
    use cx.mem.Arena;

    pub const MAX_TOML_DEPTH: u16           = 64;
    pub const DEFAULT_MAX_TOML_BYTES: usize = 16 * 1024 * 1024;

    @derive(Copy, Equatable)
    pub enum TomlSpec: u8 { V1_1 = 0, V1_0 = 1 }

    @derive(Copy, Equatable)
    pub enum TomlTokenKind: u8 {
        Whitespace = 0, Newline = 1, Comment = 2,
        Dot = 3, Comma = 4, Eq = 5,
        LBracket = 6, DoubleLBracket = 7, RBracket = 8, DoubleRBracket = 9,
        LBrace = 10, RBrace = 11,
        BareKeyOrScalar = 12, BasicStr = 13, MlBasicStr = 14,
        LiteralStr = 15, MlLiteralStr = 16,
        Invalid = 17, Eof = 18,
    }

    @derive(Copy, Equatable)
    pub bit_field TomlTokenFlags: u8 {
        pub has_escapes:  bool | 1,
        pub is_crlf:      bool | 1,
        pub len_overflow: bool | 1, // True iff byte_len == 0xFFFF (lookup in large_lengths)
        pub _reserved:    u8   | 5,
    }

    /// Exact 8-byte TOML lexical token (`1 + 1 + 2 + 4 = 8 B`).
    @repr(C)
    @derive(Copy, Equatable)
    pub struct TomlToken {
        pub kind: TomlTokenKind,
        pub flags: TomlTokenFlags,
        pub byte_len: u16,
        pub byte_offset: u32,
    }

    pub struct TomlTokenBuffer {
        pub source: str,
        pub tokens: #soa Vec[TomlToken],
        pub large_lengths: Vec[(u32, u32)],
    }

    @derive(Copy, Equatable)
    pub enum TomlNodeKind: u8 {
        Document = 0, TableSection = 1, ArrayTableSection = 2,
        KeyValue = 3, DottedKey = 4, KeySegment = 5,
        BasicStr = 6, MlBasicStr = 7, LiteralStr = 8, MlLiteralStr = 9,
        Integer = 10, Float = 11, Bool = 12, DateTime = 13,
        Array = 14, InlineTable = 15, ErrorNode = 16,
    }

    @derive(Copy, Equatable)
    pub bit_field TomlNodeFlags: u8 {
        pub has_trailing_comma: bool | 1,
        pub is_multiline:       bool | 1,
        pub has_inline_comment: bool | 1,
        pub has_error:          bool | 1,
        pub _reserved:          u8   | 4,
    }

    /// Exact 16-byte lossless TOML CST node (`1 + 1 + 2 + 4 + 4 + 4 = 16 B`).
    @repr(C)
    @derive(Copy, Equatable)
    pub struct TomlCstNode {
        pub kind: TomlNodeKind,
        pub flags: TomlNodeFlags,
        pub depth: u16,
        pub first_token: u32,  // Inclusive start token (excludes leading full-line comments)
        pub last_token: u32,   // Inclusive end token (includes same-line trailing comment + \n)
        pub next_sibling: u32, // Next sibling CST index (`0xFFFF_FFFF` if last child)
    }

    pub struct TomlCstArena {
        pub tokens: TomlTokenBuffer,
        pub nodes: #soa Vec[TomlCstNode],
        pub first_child: Vec[u32], // Parallel 4B child head per CST node (`0xFFFF_FFFF` for leaves)
    }

    @derive(Copy, Equatable)
    pub enum TomlError {
        PayloadTooLarge { len: usize, max: usize },
        DepthLimitExceeded { max_depth: u16, offset: u32 },
        InvalidUtf8 { offset: u32 },
        IllegalControlCharInComment { offset: u32 },
        UnterminatedString { offset: u32 },
        InvalidEscape { offset: u32 },
        SyntaxError { offset: u32, message: str },
        DuplicateKey { offset: u32, key: str },
        ReopenedTableOrInlineExtension { offset: u32, table: str },
        V1_0ForbiddenConstruct { offset: u32, feature: str },
    }

    pub fn parse_cst(
        arena: &mut Arena,
        source: str,
        /,
        *,
        spec: TomlSpec = .V1_1,
        max_bytes: usize = DEFAULT_MAX_TOML_BYTES,
    ) -> TomlCstArena!TomlError;

    pub fn from_str[T](arena: &mut Arena, source: str, /, *, spec: TomlSpec = .V1_1) -> T!TomlError;

    /// Deterministic TOML serializer via MirVm reflection (powers canonical `corex.lock` generation).
    pub fn to_writer[T, W: Writer](out: &mut W, val: &T, /) -> unit!IoError;
    pub fn to_slice[T](arena: &mut Arena, val: &T, /) -> str!IoError;

    /// Surgical comment- and formatting-preserving manifest editor emitting disjoint `ByteTextEdit`s.
    pub struct TomlEditor {
        arena: &mut Arena,
        cst: &TomlCstArena,
        edits: Vec[ByteTextEdit],
    }

    impl TomlEditor {
        pub fn new(arena: &mut Arena, cst: &TomlCstArena, /) -> Self;
        pub fn set_key(&mut self, table_path: &[str], key: str, raw_toml_val: str, /);
        pub fn remove_key(&mut self, table_path: &[str], key: str, /) -> bool;
        pub fn array_push_unique(&mut self, table_path: &[str], key: str, raw_item_toml: str, /) -> bool;
        pub fn array_remove(&mut self, table_path: &[str], key: str, item_str_match: str, /) -> bool;
        pub fn finish_edits(&self) -> &[ByteTextEdit];
        pub fn apply_to_str(&self) -> str;
    }
}
```

### 2.5 Reference Implementations: Stage-1/Stage-2 64-Bit JsonTape, Comptime Serde & Surgical TomlCst Patcher

Below are concrete reference implementations covering: (A) `simdjson` Stage-1 (SIMD + portable `u64` SWAR), Stage-2 64-bit `TapeWord` container backpatching (`MAX_JSON_DEPTH = 64`), zero-copy/UTF-16-surrogate string decoding, and Eisel–Lemire float parsing; (B) `comptime` reflective `@serde(rename: "…", skip_if_none: true)` struct serialization; and (C) `8B`/`16B` `TomlCst` surgical key and array patching.

#### Reference Implementation A: Complete Stage-1 & Stage-2 64-Bit JsonTape + Eisel–Lemire (Zig)

```zig
//! Reference Implementation: cx.serde.json Stage-1 (SIMD + u64 SWAR) + Stage-2 64-Bit Tape + Eisel-Lemire
const std = @import("std");
const assert = std.debug.assert;

pub const MAX_JSON_DEPTH: usize = 64;
pub const ODD_BITS: u64 = 0xAAAA_AAAA_AAAA_AAAA;
pub const PAYLOAD56_MASK: u64 = 0x00FF_FFFF_FFFF_FFFF;

// Verified 2-LUT nibble classification tables across all 256 byte values (0x07 = op, 0x18 = ws)
const LO_NIBBLE_LUT = @Vector(16, u8){ 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0x08, 0x0A, 0x04, 0x01, 0x0C, 0, 0 };
const HI_NIBBLE_LUT = @Vector(16, u8){ 0x08, 0, 0x11, 0x02, 0, 0x04, 0, 0x04, 0, 0, 0, 0, 0, 0, 0, 0 };

pub const TapeWord = packed struct(u64) {
    payload: u56,
    tag: u8,

    pub inline fn init(tag_ch: u8, payload_val: u64) TapeWord {
        return .{ .tag = tag_ch, .payload = @truncate(payload_val & PAYLOAD56_MASK) };
    }
    pub inline fn jumpIdx(self: TapeWord) u32 {
        return @truncate(self.payload);
    }
    pub inline fn countOrLen(self: TapeWord) u24 {
        return @truncate(self.payload >> 32);
    }
};

pub const Stage1State = struct {
    prev_escaped: u64 = 0,   // 0 or 1
    prev_in_string: u64 = 0, // 0 or 0xFFFF_FFFF_FFFF_FFFF
    prev_scalar: u64 = 0,    // 0 or 1
    has_unescaped_ctrl: bool = false,
};

inline fn swarEqByteMask8(word: u64, target: u8) u8 {
    const splat: u64 = @as(u64, target) *% 0x0101_0101_0101_0101;
    const diff: u64 = word ^ splat;
    const lo7: u64 = diff & 0x7F7F_7F7F_7F7F_7F7F;
    const nonzero_lo7: u64 = lo7 +% 0x7F7F_7F7F_7F7F_7F7F;
    const msb: u64 = (~(nonzero_lo7 | diff)) & 0x8080_8080_8080_8080;
    return @truncate(((msb >> 7) *% 0x0102_0408_1020_4080) >> 56);
}

inline fn swarLt20Mask8(word: u64) u8 {
    const s: u64 = (word & 0xE0E0_E0E0_E0E0_E0E0) >> 5;
    const nonzero: u64 = s +% 0x7F7F_7F7F_7F7F_7F7F;
    const msb: u64 = (~nonzero) & 0x8080_8080_8080_8080;
    return @truncate(((msb >> 7) *% 0x0102_0408_1020_4080) >> 56);
}

pub fn classifyBlock64Swar(block: *const [64]u8, bs: *u64, qt: *u64, op: *u64, ws: *u64, ctrl: *u64) void {
    var b_acc: u64 = 0;
    var q_acc: u64 = 0;
    var o_acc: u64 = 0;
    var w_acc: u64 = 0;
    var c_acc: u64 = 0;

    inline for (0..8) |k| {
        const w = std.mem.readInt(u64, block[k * 8 ..][0..8], .little);
        const shift: u6 = @intCast(k * 8);
        b_acc |= @as(u64, swarEqByteMask8(w, '\\')) << shift;
        q_acc |= @as(u64, swarEqByteMask8(w, '"')) << shift;
        c_acc |= @as(u64, swarLt20Mask8(w)) << shift;

        const m_brace = swarEqByteMask8(w, '{') | swarEqByteMask8(w, '}');
        const m_brack = swarEqByteMask8(w, '[') | swarEqByteMask8(w, ']');
        const m_punct = swarEqByteMask8(w, ':') | swarEqByteMask8(w, ',');
        o_acc |= @as(u64, m_brace | m_brack | m_punct) << shift;

        const m_ws = swarEqByteMask8(w, ' ') | swarEqByteMask8(w, '\n') |
            swarEqByteMask8(w, '\t') | swarEqByteMask8(w, '\r');
        w_acc |= @as(u64, m_ws) << shift;
    }
    bs.* = b_acc;
    qt.* = q_acc;
    op.* = o_acc;
    ws.* = w_acc;
    ctrl.* = c_acc;
}

pub fn classifyBlock64Simd(block: *const [64]u8, bs: *u64, qt: *u64, op: *u64, ws: *u64, ctrl: *u64) void {
    var b_acc: u64 = 0;
    var q_acc: u64 = 0;
    var o_acc: u64 = 0;
    var w_acc: u64 = 0;
    var c_acc: u64 = 0;

    inline for (0..4) |lane| {
        const v: @Vector(16, u8) = block[lane * 16 ..][0..16].*;
        const shift: u6 = @intCast(lane * 16);

        const is_bs: u16 = @bitCast(v == @as(@Vector(16, u8), @splat('\\')));
        const is_qt: u16 = @bitCast(v == @as(@Vector(16, u8), @splat('"')));
        const is_ct: u16 = @bitCast(v < @as(@Vector(16, u8), @splat(0x20)));

        const lo_nib = v & @as(@Vector(16, u8), @splat(0x0F));
        const hi_nib = v >> @as(@Vector(16, u3), @splat(4));
        var cls: @Vector(16, u8) = undefined;
        inline for (0..16) |i| {
            cls[i] = LO_NIBBLE_LUT[lo_nib[i]] & HI_NIBBLE_LUT[hi_nib[i]];
        }
        const z: @Vector(16, u8) = @splat(0);
        const is_op: u16 = @bitCast((cls & @as(@Vector(16, u8), @splat(0x07))) != z);
        const is_ws: u16 = @bitCast((cls & @as(@Vector(16, u8), @splat(0x18))) != z);

        b_acc |= @as(u64, is_bs) << shift;
        q_acc |= @as(u64, is_qt) << shift;
        c_acc |= @as(u64, is_ct) << shift;
        o_acc |= @as(u64, is_op) << shift;
        w_acc |= @as(u64, is_ws) << shift;
    }
    bs.* = b_acc;
    qt.* = q_acc;
    op.* = o_acc;
    ws.* = w_acc;
    ctrl.* = c_acc;
}

inline fn prefixXor64(q: u64) u64 {
    var x = q;
    x ^= x << 1;
    x ^= x << 2;
    x ^= x << 4;
    x ^= x << 8;
    x ^= x << 16;
    x ^= x << 32;
    return x;
}

pub fn stage1Step64(block: *const [64]u8, state: *Stage1State, use_simd: bool) u64 {
    var bs_mask: u64 = 0;
    var qt_raw: u64 = 0;
    var op_raw: u64 = 0;
    var ws_raw: u64 = 0;
    var ctrl_raw: u64 = 0;

    if (use_simd) {
        classifyBlock64Simd(block, &bs_mask, &qt_raw, &op_raw, &ws_raw, &ctrl_raw);
    } else {
        classifyBlock64Swar(block, &bs_mask, &qt_raw, &op_raw, &ws_raw, &ctrl_raw);
    }

    const potential_escape = bs_mask & ~state.prev_escaped;
    const even_series = ((potential_escape << 1) | ODD_BITS) -% potential_escape;
    const escape_and_term = even_series ^ ODD_BITS;
    const escaped = escape_and_term ^ (bs_mask | state.prev_escaped);
    state.prev_escaped = (escape_and_term & bs_mask) >> 63;

    const quotes = qt_raw & ~escaped;
    const in_string = prefixXor64(quotes) ^ state.prev_in_string;
    state.prev_in_string = @bitCast(@as(i64, @bitCast(in_string)) >> 63);

    if ((ctrl_raw & in_string) != 0) state.has_unescaped_ctrl = true;

    const structurals = op_raw & ~in_string;
    const scalar = ~(op_raw | ws_raw | in_string | quotes);
    const follows_scalar = (scalar << 1) | state.prev_scalar;
    state.prev_scalar = scalar >> 63;

    return structurals | (scalar & ~follows_scalar) | (quotes & in_string);
}

pub fn parseJsonStringStage2(
    raw: []const u8,
    start_off: usize,
    str_buf: *std.ArrayListUnmanaged(u8),
    alloc: std.mem.Allocator,
) !TapeWord {
    var i: usize = start_off;
    var has_backslash = false;
    while (i < raw.len) : (i += 1) {
        const c = raw[i];
        if (c == '"') break;
        if (c == '\\') {
            has_backslash = true;
            i += 1;
            if (i >= raw.len) return error.UnclosedString;
        } else if (c < 0x20) {
            return error.UnescapedControlChar;
        }
    }
    if (i >= raw.len) return error.UnclosedString;
    const raw_len = i - start_off;

    if (!has_backslash and raw_len < (1 << 24) and start_off <= std.math.maxInt(u32)) {
        return TapeWord.init('"', (@as(u64, raw_len) << 32) | @as(u64, start_off));
    }

    const out_start: u32 = @intCast(str_buf.items.len);
    var p: usize = start_off;
    while (p < i) {
        const b = raw[p];
        if (b != '\\') {
            try str_buf.append(alloc, b);
            p += 1;
            continue;
        }
        p += 1;
        const esc = raw[p];
        p += 1;
        switch (esc) {
            '"', '\\', '/' => try str_buf.append(alloc, esc),
            'b' => try str_buf.append(alloc, 0x08),
            'f' => try str_buf.append(alloc, 0x0C),
            'n' => try str_buf.append(alloc, '\n'),
            'r' => try str_buf.append(alloc, '\r'),
            't' => try str_buf.append(alloc, '\t'),
            'u' => {
                if (p + 4 > i) return error.InvalidEscape;
                const cp1 = try std.fmt.parseInt(u16, raw[p .. p + 4], 16);
                p += 4;
                var scalar: u21 = cp1;
                if (cp1 >= 0xD800 and cp1 <= 0xDBFF) {
                    if (p + 6 > i or raw[p] != '\\' or raw[p + 1] != 'u') return error.InvalidUnicodeSurrogate;
                    const cp2 = try std.fmt.parseInt(u16, raw[p + 2 .. p + 6], 16);
                    if (cp2 < 0xDC00 or cp2 > 0xDFFF) return error.InvalidUnicodeSurrogate;
                    p += 6;
                    scalar = 0x10000 + (@as(u21, cp1 - 0xD800) << 10) + @as(u21, cp2 - 0xDC00);
                } else if (cp1 >= 0xDC00 and cp1 <= 0xDFFF) {
                    return error.InvalidUnicodeSurrogate;
                }
                var utf8_tmp: [4]u8 = undefined;
                const n_utf8 = try std.unicode.utf8Encode(scalar, &utf8_tmp);
                try str_buf.appendSlice(alloc, utf8_tmp[0..n_utf8]);
            },
            else => return error.InvalidEscape,
        }
    }
    const out_len = str_buf.items.len - out_start;
    return TapeWord.init('s', (@as(u64, out_len) << 32) | @as(u64, out_start));
}

/// 16-byte Powers-of-5 Entry (`651 * 16 B = 10,416 B` in `.rodata`; binary exponent derived linearly).
pub const Pow5Entry = extern struct { hi: u64, lo: u64 };

const SMALL_POW10 = [23]f64{
    1e0,  1e1,  1e2,  1e3,  1e4,  1e5,  1e6,  1e7,  1e8,  1e9,  1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
};

pub fn eiselLemireComputeF64(man: u64, exp10: i32, neg: bool, pow5_lut: []const Pow5Entry) ?f64 {
    if (man == 0) return if (neg) -0.0 else 0.0;

    if (man < (@as(u64, 1) << 53)) {
        if (exp10 >= 0 and exp10 <= 22) {
            const v = @as(f64, @floatFromInt(man)) * SMALL_POW10[@intCast(exp10)];
            return if (neg) -v else v;
        }
        if (exp10 >= -22 and exp10 < 0) {
            const v = @as(f64, @floatFromInt(man)) / SMALL_POW10[@intCast(-exp10)];
            return if (neg) -v else v;
        }
    }
    if (exp10 < -342) return if (neg) -0.0 else 0.0;
    if (exp10 > 308) return if (neg) -std.math.inf(f64) else std.math.inf(f64);

    const lz: u6 = @intCast(@clz(man));
    const norm_man: u64 = man << lz;
    const entry = pow5_lut[@intCast(exp10 - (-342))];
    const e2_pow10: i32 = (exp10 * 217706) >> 16;

    const p1: u128 = @as(u128, norm_man) * @as(u128, entry.hi);
    const w_hi: u64 = @truncate(p1 >> 64);
    const w_lo: u64 = @truncate(p1);
    const msb: i32 = @intCast(w_hi >> 63);
    var biased_e2: i32 = (63 - @as(i32, lz) + e2_pow10 + msb) + 1023;

    var n_hi: u64 = if (msb == 0) (w_hi << 1) | (w_lo >> 63) else w_hi;
    const n_lo: u64 = if (msb == 0) (w_lo << 1) else w_lo;

    if ((n_hi & 0x3FF) == 0x3FF or ((n_hi & 0x3FF) == 0 and n_lo == 0)) {
        const p2: u128 = @as(u128, norm_man) * @as(u128, entry.lo);
        var full_hi128: u128 = p1 + (p2 >> 64);
        const p2_rem: u64 = @truncate(p2);
        if (msb == 0) full_hi128 = (full_hi128 << 1) | (p2_rem >> 63);
        n_hi = @truncate(full_hi128 >> 64);
        const n_mid: u64 = @truncate(full_hi128);
        if ((n_hi & 0x3FF) == 0 and n_mid == 0) return null;
    }

    if (biased_e2 <= 0 or biased_e2 >= 0x7FF) return null;

    var mant53: u64 = ((n_hi >> 10) + 1) >> 1;
    if (mant53 == (@as(u64, 1) << 53)) {
        mant53 >>= 1;
        biased_e2 += 1;
        if (biased_e2 >= 0x7FF) return if (neg) -std.math.inf(f64) else std.math.inf(f64);
    }

    const sign_bit: u64 = if (neg) (@as(u64, 1) << 63) else 0;
    return @bitCast(sign_bit | (@as(u64, @intCast(biased_e2)) << 52) | (mant53 & 0x000F_FFFF_FFFF_FFFF));
}

const OpenScope = struct { tape_idx: u32, count: u24, is_object: bool };

/// Stage-2 Structural State Machine constructing the 64-bit `simdjson` tape (`MAX_JSON_DEPTH = 64`).
pub fn buildTapeStage2(
    alloc: std.mem.Allocator,
    raw: []const u8,
    struct_indices: []const u32,
    pow5_lut: []const Pow5Entry,
) !struct { words: []TapeWord, string_buf: []u8 } {
    var words = std.ArrayListUnmanaged(TapeWord){};
    var str_buf = std.ArrayListUnmanaged(u8){};
    var scopes: [MAX_JSON_DEPTH]OpenScope = undefined;
    var depth: usize = 0;

    try words.append(alloc, TapeWord.init('r', 0)); // Placeholder root open at index 0
    if (struct_indices.len == 0) return error.UnexpectedToken;

    const State = enum { start_val, obj_key_or_close, obj_colon, obj_comma_or_close, arr_comma_or_close, after_root };
    var st: State = .start_val;

    for (struct_indices) |byte_idx| {
        const ch = raw[byte_idx];
        value_dispatch: while (true) {
            switch (st) {
                .start_val => switch (ch) {
                    '{' => {
                        if (depth >= MAX_JSON_DEPTH) return error.DepthLimitExceeded;
                        scopes[depth] = .{ .tape_idx = @intCast(words.items.len), .count = 0, .is_object = true };
                        depth += 1;
                        try words.append(alloc, TapeWord.init('{', 0));
                        st = .obj_key_or_close;
                        break :value_dispatch;
                    },
                    '[' => {
                        if (depth >= MAX_JSON_DEPTH) return error.DepthLimitExceeded;
                        scopes[depth] = .{ .tape_idx = @intCast(words.items.len), .count = 0, .is_object = false };
                        depth += 1;
                        try words.append(alloc, TapeWord.init('[', 0));
                        if (struct_indices.len > 0) {} // Handled if next token is ']' below
                        st = .start_val;
                        // Peek empty array `[]` check handled on `]` arm below!
                        break :value_dispatch;
                    },
                    ']' => {
                        if (depth > 0 and !scopes[depth - 1].is_object and scopes[depth - 1].count == 0) {
                            st = .arr_comma_or_close;
                            continue :value_dispatch;
                        }
                        return error.UnexpectedToken;
                    },
                    '"' => try words.append(alloc, try parseJsonStringStage2(raw, byte_idx + 1, &str_buf, alloc)),
                    't' => {
                        if (!std.mem.startsWith(u8, raw[byte_idx..], "true")) return error.UnexpectedToken;
                        try words.append(alloc, TapeWord.init('t', 0));
                    },
                    'f' => {
                        if (!std.mem.startsWith(u8, raw[byte_idx..], "false")) return error.UnexpectedToken;
                        try words.append(alloc, TapeWord.init('f', 0));
                    },
                    'n' => {
                        if (!std.mem.startsWith(u8, raw[byte_idx..], "null")) return error.UnexpectedToken;
                        try words.append(alloc, TapeWord.init('n', 0));
                    },
                    '-', '0'...'9' => try appendJsonNumber(&words, alloc, raw[byte_idx..], pow5_lut),
                    else => return error.UnexpectedToken,
                },
                .obj_key_or_close => {
                    if (ch == '}' and scopes[depth - 1].count == 0) {
                        st = .obj_comma_or_close;
                        continue :value_dispatch;
                    }
                    if (ch != '"') return error.UnexpectedToken;
                    scopes[depth - 1].count +|= 1;
                    try words.append(alloc, try parseJsonStringStage2(raw, byte_idx + 1, &str_buf, alloc));
                    st = .obj_colon;
                    break :value_dispatch;
                },
                .obj_colon => {
                    if (ch != ':') return error.UnexpectedToken;
                    st = .start_val;
                    break :value_dispatch;
                },
                .obj_comma_or_close => switch (ch) {
                    ',' => {
                        if ( raw[byte_idx] == ',' ) {}
                        st = .obj_key_or_close;
                        break :value_dispatch;
                    },
                    '}' => {
                        depth -= 1;
                        const open = scopes[depth];
                        const close_idx: u32 = @intCast(words.items.len);
                        try words.append(alloc, TapeWord.init('}', open.tape_idx));
                        words.items[open.tape_idx] = TapeWord.init('{', (@as(u64, open.count) << 32) | (close_idx + 1));
                        st = if (depth == 0) .after_root else if (scopes[depth - 1].is_object) .obj_comma_or_close else .arr_comma_or_close;
                        break :value_dispatch;
                    },
                    else => return error.UnexpectedToken,
                },
                .arr_comma_or_close => switch (ch) {
                    ',' => {
                        st = .start_val;
                        break :value_dispatch;
                    },
                    ']' => {
                        depth -= 1;
                        const open = scopes[depth];
                        const close_idx: u32 = @intCast(words.items.len);
                        try words.append(alloc, TapeWord.init(']', open.tape_idx));
                        words.items[open.tape_idx] = TapeWord.init('[', (@as(u64, open.count) << 32) | (close_idx + 1));
                        st = if (depth == 0) .after_root else if (scopes[depth - 1].is_object) .obj_comma_or_close else .arr_comma_or_close;
                        break :value_dispatch;
                    },
                    else => return error.UnexpectedToken,
                },
                .after_root => return error.TrailingCharacters,
            }
            // Completed a scalar value in `start_val`
            if (depth == 0) {
                st = .after_root;
            } else if (scopes[depth - 1].is_object) {
                st = .obj_comma_or_close;
            } else {
                scopes[depth - 1].count +|= 1;
                st = .arr_comma_or_close;
            }
            break :value_dispatch;
        }
    }
    if (depth != 0 or st != .after_root) return error.UnexpectedToken;
    const end_root_idx: u64 = words.items.len;
    try words.append(alloc, TapeWord.init('r', 0));
    words.items[0] = TapeWord.init('r', end_root_idx);
    return .{ .words = try words.toOwnedSlice(alloc), .string_buf = try str_buf.toOwnedSlice(alloc) };
}

fn appendJsonNumber(
    words: *std.ArrayListUnmanaged(TapeWord),
    alloc: std.mem.Allocator,
    slice: []const u8,
    pow5_lut: []const Pow5Entry,
) !void {
    var i: usize = 0;
    const neg = slice[0] == '-';
    if (neg) i += 1;
    var man: u64 = 0;
    var digits: usize = 0;
    while (i < slice.len and slice[i] >= '0' and slice[i] <= '9') : (i += 1) {
        if (digits < 19) man = man * 10 + (slice[i] - '0');
        digits += 1;
    }
    if (digits == 0) return error.InvalidNumber;
    const is_float = (i < slice.len and (slice[i] == '.' or slice[i] == 'e' or slice[i] == 'E'));
    if (!is_float and digits <= 19) {
        if (neg) {
            const signed_v: i64 = -@as(i64, @intCast(man));
            try words.append(alloc, TapeWord.init('l', 0));
            try words.append(alloc, @bitCast(@as(u64, @bitCast(signed_v))));
        } else {
            try words.append(alloc, TapeWord.init('u', 0));
            try words.append(alloc, @bitCast(man));
        }
        return;
    }
    var exp10: i32 = 0;
    if (i < slice.len and slice[i] == '.') {
        i += 1;
        while (i < slice.len and slice[i] >= '0' and slice[i] <= '9') : (i += 1) {
            if (digits < 19) {
                man = man * 10 + (slice[i] - '0');
                exp10 -= 1;
            }
            digits += 1;
        }
    }
    if (i < slice.len and (slice[i] == 'e' or slice[i] == 'E')) {
        i += 1;
        var exp_neg = false;
        if (i < slice.len and (slice[i] == '+' or slice[i] == '-')) {
            exp_neg = (slice[i] == '-');
            i += 1;
        }
        var e_acc: i32 = 0;
        while (i < slice.len and slice[i] >= '0' and slice[i] <= '9') : (i += 1) {
            e_acc = @min(10_000, e_acc * 10 + (slice[i] - '0'));
        }
        exp10 += if (exp_neg) -e_acc else e_acc;
    }
    const f_val = eiselLemireComputeF64(man, exp10, neg, pow5_lut) orelse try std.fmt.parseFloat(f64, slice[0..i]);
    try words.append(alloc, TapeWord.init('d', 0));
    try words.append(alloc, @bitCast(@as(u64, @bitCast(f_val))));
}
```

#### Reference Implementation B: Comptime @serde(rename: "…", skip_if_none: true) Reflection (.cx)

```rust
// File: stdlib/cx/serde_derive.cx (MirVm comptime struct serializer handling rename & skip_if_none)
mod serde_derive;

use cx.io.{IoError, Writer};
use cx.meta.{TypeInfo, TypeKind};
use cx.serde.{SerdeAttr, Serialize};

pub fn derive_serialize_json[T, W: Writer](val: &T, out: &mut W, /) -> unit!IoError {
    const INFO: TypeInfo = @type_info[T]();
    comptime match INFO.kind {
        .Struct(s_info) => {
            out.write_all(b"{")?;
            var is_first = true;

            comptime for field in s_info.fields {
                const ATTR: SerdeAttr = field.get_attr[SerdeAttr]() orelse SerdeAttr { .. };
                comptime if not ATTR.skip {
                    const KEY_NAME: str = ATTR.rename orelse field.name;
                    const KEY_LITERAL: str = comptime concat_str("\"", KEY_NAME, "\":");
                    const IS_OPTION_FIELD: bool = @type_info_id(field.ty_id).kind is .Option;

                    comptime if ATTR.skip_if_none and IS_OPTION_FIELD {
                        if @field(val, field) is .Some(&inner_val) {
                            if not is_first { out.write_all(b",")?; }
                            is_first = false;
                            out.write_all(KEY_LITERAL.as_bytes())?;
                            Serialize.serialize_json(inner_val, out)?;
                        }
                    } else {
                        if not is_first { out.write_all(b",")?; }
                        is_first = false;
                        out.write_all(KEY_LITERAL.as_bytes())?;
                        Serialize.serialize_json(&@field(val, field), out)?;
                    }
                }
            }
            out.write_all(b"}")
        }
        _ => @compile_error("@derive(Serialize) requires a struct or enum"),
    }
}
```

#### Reference Implementation C: Lossless 8B/16B TomlCst Surgical Key & Array Patcher (Zig)

```zig
//! Reference Implementation: cx.serde.toml 8B TomlToken + 16B TomlCstNode Surgical Patcher
const std = @import("std");
const assert = std.debug.assert;

pub const SENTINEL_U32: u32 = 0xFFFF_FFFF;

pub const TomlTokenKind = enum(u8) {
    whitespace, newline, comment, dot, comma, eq,
    lbracket, double_lbracket, rbracket, double_rbracket,
    lbrace, rbrace, bare_or_scalar, basic_str, ml_basic_str,
    literal_str, ml_literal_str, invalid, eof,
};

pub const TomlToken = extern struct {
    kind: TomlTokenKind,
    flags: u8 = 0,
    byte_len: u16,
    byte_offset: u32,
};

pub const TomlNodeKind = enum(u8) {
    document, table_section, array_table_section, key_value,
    dotted_key, key_segment, basic_str, ml_basic_str, literal_str, ml_literal_str,
    integer, float, boolean, datetime, array, inline_table, error_node,
};

pub const TomlNodeFlags = packed struct(u8) {
    has_trailing_comma: bool = false,
    is_multiline: bool = false,
    has_inline_comment: bool = false,
    has_error: bool = false,
    _pad: u4 = 0,
};

pub const TomlCstNode = extern struct {
    kind: TomlNodeKind,
    flags: TomlNodeFlags,
    depth: u16,
    first_token: u32,
    last_token: u32,
    next_sibling: u32,
};

comptime {
    assert(@sizeOf(TomlToken) == 8);
    assert(@sizeOf(TomlCstNode) == 16);
}

pub const ByteTextEdit = struct {
    start_byte: u32,
    end_byte: u32,
    replacement: []const u8,
};

pub const TomlCstDoc = struct {
    source: []const u8,
    tokens: []const TomlToken,
    nodes: []const TomlCstNode,
    first_child: []const u32,

    pub inline fn nodeByteSpan(self: *const TomlCstDoc, node_idx: u32) struct { start: u32, end: u32 } {
        const n = self.nodes[node_idx];
        const first = self.tokens[n.first_token];
        const last = self.tokens[n.last_token];
        return .{ .start = first.byte_offset, .end = last.byte_offset + last.byte_len };
    }
};

/// Emits a surgical ByteTextEdit setting or inserting `key = raw_val` inside `[section_name]`
/// while preserving inline `# comments` on existing keys AND keeping next-header doc comments intact.
pub fn surgicalSetTableKey(
    arena: std.mem.Allocator,
    doc: *const TomlCstDoc,
    section_name: []const u8,
    key: []const u8,
    raw_val: []const u8,
) !ByteTextEdit {
    var sec_idx: u32 = doc.first_child[0];
    var target_sec: ?u32 = null;
    while (sec_idx != SENTINEL_U32) : (sec_idx = doc.nodes[sec_idx].next_sibling) {
        if (doc.nodes[sec_idx].kind == .table_section) {
            const hdr_key_idx = doc.first_child[sec_idx];
            const hdr_span = doc.nodeByteSpan(hdr_key_idx);
            if (std.mem.eql(u8, doc.source[hdr_span.start..hdr_span.end], section_name)) {
                target_sec = sec_idx;
                break;
            }
        }
    }

    if (target_sec == null) {
        const eof_off: u32 = @intCast(doc.source.len);
        const prefix = if (eof_off > 0 and doc.source[eof_off - 1] != '\n') "\n\n" else "\n";
        const text = try std.fmt.allocPrint(arena, "{s}[{s}]\n{s} = {s}\n", .{ prefix, section_name, key, raw_val });
        return .{ .start_byte = eof_off, .end_byte = eof_off, .replacement = text };
    }

    const sec_node_id = target_sec.?;
    var child_idx: u32 = doc.nodes[doc.first_child[sec_node_id]].next_sibling;
    var last_kv_idx: ?u32 = null;

    while (child_idx != SENTINEL_U32) : (child_idx = doc.nodes[child_idx].next_sibling) {
        if (doc.nodes[child_idx].kind != .key_value) continue;
        last_kv_idx = child_idx;

        const key_node_idx = doc.first_child[child_idx];
        const val_node_idx = doc.nodes[key_node_idx].next_sibling;
        const k_span = doc.nodeByteSpan(key_node_idx);

        if (std.mem.eql(u8, std.mem.trim(u8, doc.source[k_span.start..k_span.end], " \t\"'"), key)) {
            const v_span = doc.nodeByteSpan(val_node_idx);
            return .{ .start_byte = v_span.start, .end_byte = v_span.end, .replacement = raw_val };
        }
    }

    const anchor_node = last_kv_idx orelse sec_node_id;
    const anchor_tok = doc.tokens[doc.nodes[anchor_node].last_token];
    var insert_off: u32 = anchor_tok.byte_offset + anchor_tok.byte_len;

    while (insert_off < doc.source.len and (doc.source[insert_off] == ' ' or doc.source[insert_off] == '\t')) : (insert_off += 1) {}
    if (insert_off < doc.source.len and doc.source[insert_off] == '#') {
        while (insert_off < doc.source.len and doc.source[insert_off] != '\n') : (insert_off += 1) {}
    }
    if (insert_off < doc.source.len and doc.source[insert_off] == '\r') insert_off += 1;
    if (insert_off < doc.source.len and doc.source[insert_off] == '\n') {
        insert_off += 1;
        const line = try std.fmt.allocPrint(arena, "{s} = {s}\n", .{ key, raw_val });
        return .{ .start_byte = insert_off, .end_byte = insert_off, .replacement = line };
    } else {
        const line = try std.fmt.allocPrint(arena, "\n{s} = {s}\n", .{ key, raw_val });
        return .{ .start_byte = insert_off, .end_byte = insert_off, .replacement = line };
    }
}

pub fn surgicalArrayPush(
    arena: std.mem.Allocator,
    doc: *const TomlCstDoc,
    array_node_idx: u32,
    raw_item: []const u8,
) !ByteTextEdit {
    const arr = doc.nodes[array_node_idx];
    const rbracket_tok = doc.tokens[arr.last_token];
    const close_off = rbracket_tok.byte_offset;

    if (doc.first_child[array_node_idx] == SENTINEL_U32) {
        return .{ .start_byte = close_off, .end_byte = close_off, .replacement = raw_item };
    }
    if (arr.flags.is_multiline) {
        const prefix = if (arr.flags.has_trailing_comma) "    " else ",\n    ";
        const patch = try std.fmt.allocPrint(arena, "{s}{s},\n", .{ prefix, raw_item });
        return .{ .start_byte = close_off, .end_byte = close_off, .replacement = patch };
    } else {
        const sep = if (arr.flags.has_trailing_comma) " " else ", ";
        const patch = try std.fmt.allocPrint(arena, "{s}{s}", .{ sep, raw_item });
        return .{ .start_byte = close_off, .end_byte = close_off, .replacement = patch };
    }
}
```

---

## 3. Deterministic Context Simulation, SanitizerCoverage Fuzzing, and MAD Benchmarking (cx.test and cx.bench)

`cx.test` (`stdlib/cx/test.cx`) and `cx.bench` (`stdlib/cx/bench.cx`) implement CoreX's unified verification and micro-benchmarking runtime, turning `test "…"` and `bench "…"` blocks (`DR-22` `SE-16`) into parallel unit/snapshot tests, single-process deterministic `Context` simulations (`corex test --sim --seed`), zero-config `SanitizerCoverage` fuzzers (`corex test --fuzz`), and outlier-filtered benchmarks (`corex bench`).

> **Visual – Single-Stream Context Virtualization and SIMD SanitizerCoverage Unify Deterministic Simulation With Structure-Aware Fuzzing:** Top (--sim --seed): One SplitMix64-seeded Xoshiro256** stream drives task priorities, virtual monotonic timer jumps, Map hash seeds, simulated VFS/network faults, and sequential 0..N_alloc OOM sweeps; Probabilistic Concurrency Testing reaches **99% bug-detection confidence** in 35 seeds for depth-1 ordering bugs and 7,366 seeds for depth-2 races (8 tasks, 200 steps). Bottom (--fuzz): 32-byte SIMD counter sweeps, 16 KiB TORC comparison rings, and 5-pass Conjecture shortlex shrinking reduce raw crashes into Git-committed .cxfuzz reproducers.

### 3.1 Test Discovery, Parallel Runner, Myers Diff Assertions, and Golden .snap Verification

In `--test` builds, the compiler emits a static `.rodata` slice of `TestDesc` entries for all `test "…"`, `async test "…"`, and parameterized `test "…" (input: T)` items while skipping `TestItem` subtrees in O(1) via `CstNode.subtree_size` during standard `corex build` and `corex check` runs. `cx.test.run_main` filters targets via `cx.cli`, executes independent tests concurrently across `--jobs=N` worker threads (binding a private 256 KiB `Arena` and buffered output sink per test so parallel diagnostic cards never interleave), and replays all committed `tests/sim/**/*.cxsim` and `tests/fuzz/corpus/**/*.cxfuzz` (plus module-grouped `tests/fuzz/**/*.cxfuzz`) regression artifacts uninstrumented within the `< 2.0 s` cold `corex test` budget. Rich assertions (`assert_eq`, `assert_ne`, `assert_str_eq`, `assert_bytes_eq`) capture `loc: SourceLoc = @caller_location()` (`8 B` `.rodata` descriptor, `SE-17`) and render Myers O(ND) unified diffs on failure. Golden snapshot assertions (`assert_snapshot(name, actual)`) resolve `tests/snapshots/<module>__<name>.snap`, normalize CRLF (`\r\n`) to LF (`\n`) for cross-OS consistency, and atomically update `.snap` files via `UnlinkAndReplace` when `--update-snapshots` (`-u`) is passed locally (rejected when `--locked` or `CI=true` is set).

### 3.2 Single-Process Deterministic Context Simulation (--sim --seed): PCT, Virtual Time, OOM & VFS/Net Faults

Under `corex test --sim [--seed=<u64>]`, `cx.test.sim` binds the 64-byte `Context` register (`r10` on `x86_64`, `x8` on `aarch64`) to a single-threaded **`SimWorld`** (`DR-18`, `DR-20` `Fix-08B` and `Fix-18A`). A single `Xoshiro256**` stream initialized from `--seed` via four `SplitMix64` rounds (`SimPrng`) drives every non-deterministic decision in the process – including `cx.col.Map` and `Set` `Wyhash` seeds (`Fix-18A`), task wakeup priorities, simultaneous timer tie-breaking, fault coin tosses, two-phase `sim.buggify()` probes, and user `context.rng()` calls. Compile-time `MIR` SAST enforces `E0331` (banning direct host syscalls outside `Context`-routed `cx.*` shims) and `W0332` (flagging `&x as usize` pointer-to-integer casts that leak ASLR entropy, promoted to an error under `--sim-strict`), while `corex_llvm.cpp` sets `FPOpFusion::Strict` (`-ffp-contract=off`) and canonical quiet `NaN` bit patterns for cross-ISA replay parity across `x86_64` Linux and `aarch64` macOS.

`SimWorld` initializes `monotonic_ns = 1_000_000_000` (`1.0 s`) and manages timers and delayed I/O completions inside a binary min-heap of 32-byte `SimEvent { deadline_ns: u64, tie_order: u64, cqe: ReactorCqe }` entries. Virtual time never advances while `run_queue` is non-empty; only when every live task is durably blocked does `SimWorld` pop the minimum `deadline_ns` in O(log E) time, jump `monotonic_ns`, drain co-scheduled events in deterministic `tie_order`, and wake their tasks – executing multi-hour retry/lease windows in milliseconds while trapping deadlocks (`E_SIM_DEADLOCK`) immediately if both `run_queue` and `event_wheel` empty prior to root completion. Rather than naive per-step coin flips (which hit a specific ordering after 40 steps at probability `9.09 × 10^-13`), `SimScheduler` implements Burckhardt et al.'s **Probabilistic Concurrency Testing (PCT)** (ASPLOS 2010) across depths `d` in `1..=4`, assigning `n` tasks distinct initial priorities in `{d, ..., d + n - 1}` and drawing `d - 1` priority-drop steps `k_1, ..., k_{d-1}` over `k` steps to achieve worst-case single-run bug detection probability:

$$P(\text{detect}) \ge \frac{1}{n \cdot k^{d-1}}$$

On a representative `TaskGroup` test (`n = 8` tasks, `k = 200` steps), PCT reaches 99% cumulative detection confidence in 35 seeds for depth-1 ordering bugs and 7,366 seeds for depth-2 cancellation/atomicity races. On canceled `InFlightOpSlot` entries (`Fix-08B`), `SimReactor` injects 50% race-won completions (`cqe.result >= 0`) to verify that `CompletionReaper` closes orphaned descriptors without leaking (`E_SIM_LINEAR_LEAK`).

For systematic memory-fault verification, `SimFaultAllocator` intercepts **both** `System` heap allocations (`AllocTag = 0`) and `Arena` / `BumpArena` backing-slab allocations under a single `alloc_seq` counter. Calibration Pass `0` (`fail_idx = u64.MAX`) records total allocations `N_alloc` and streaming 64-bit `ExecutionDigest` checkpoints `D[0 .. N_alloc]`; passes `i = 0 .. N_alloc - 1` fail allocation `i` with `AllocError.OutOfMemory`, asserting `run_i.digest_before(i) == D[i]` (verifying determinism up to fault `i` without penalizing valid `catch` recovery) and checking zero leaked `System` blocks or `Arena` slabs on exit. Complementing `OOM` sweeps, `SimVfs` injects `EIO` / `ENOSPC`, slices reads/writes to partial `1..len` transfers, and separates `synced_bytes` from `unflushed_page_cache` so `sim.crash_remount_vfs()` discards any writes lacking `File.sync_data()`, while `SimNet` injects virtual latency jitter, packet reordering, `TimedOut` / `ConnectionReset` errors, TCP stream chunking, and one-way link partitions.

### 3.3 In-Process SanitizerCoverage Fuzzing (--fuzz): SIMD Hit-Bucketing, Havoc/TORC Mutator & Shortlex Shrinker

Under `corex test --fuzz`, Tier B (`corex_llvm.cpp`) registers `llvm::SanitizerCoveragePass` (`SCK_Edge`, `Inline8bitCounters`, `PCTable`, `TraceCmp`, `TraceDiv`) at `OptimizerLastEP` with `lld --icf=none`, and `stdlib/cx/test.cx` exports all 17 `__sanitizer_cov_*` C-ABI callbacks (`__sanitizer_cov_8bit_counters_init`, `__sanitizer_cov_pcs_init`, `__sanitizer_cov_trace_[const_]cmp{1,2,4,8}`, `__sanitizer_cov_trace_switch`, `__sanitizer_cov_trace_div{4,8}`, `gep`, `pc_indir`, and `trace_pc_guard[_init]`) marked `@no_fuzz_instrument`. Each iteration runs in-process inside a `sigsetjmp` panic frame with a rewound 256 KiB iteration `Arena`, supervised across `--jobs` workers via a 128-byte `@cache_aligned` `FuzzShmHeader` shared-memory ring to isolate native crashes (`SIGSEGV`/`SIGABRT`) and `--fuzz-timeout=1000ms` hangs.

After each execution, `FuzzWorker` sweeps `__sancov_cntrs` in `Simd[u8, 32]` vectors, skipping 32 untouched edges in one zero compare and mapping non-zero counts $c \in [1, 255]$ into AFL/LibAFL's 9 logarithmic hit-count buckets `{1, 2, 4, 8, 16, 32, 64, 128}` via the exact branchless threshold sum:

$$\text{Bucket}(c) = \begin{cases} 0 & c = 0 \\ 1 \ll \sum_{T \in \{2, 3, 4, 8, 16, 32, 128\}} \mathbb{I}(c \ge T) & c > 0 \end{cases}$$

New bucket hits clear bits in `virgin_mask` and enqueue the input into `CorpusQueue`, weighted 75% by discovery recency and 25% by execution speed and rare entry/edge coverage derived from `__sancov_pcs` (`[PC, PCFlags]` pairs where `PCFlags & 1` marks function entries). `FuzzMutator` stacks `1..=8` Havoc, `.rodata` dictionary, cross-corpus splice, and value-profile operators: `TORC4` (`1,024 × 8 B`) and `TORC8` (`512 × 16 B`) capture recent comparison and `switch` operands (`cases[0] = count`, `cases[1] = bit_width`, `cases[2..]` = constants) so Input-to-State (`I2S`) replacement substitutes runtime `arg2` spans with target constant `arg1` (and `arg1 ± 1`) in both little- and big-endian order, while `DIV` ring entries mutate dynamic divisors toward `0` to expose divide-by-zero panics. Raw `test "…" (data: &[u8])` targets receive the mutated slice directly, whereas typed `test "…" (val: T)` targets decode `T` via `comptime`-reflected `@derive(Arbitrary)` over a zero-allocation `ChoiceCursor` (`0x00` = simplest default, Zig-Zag signed ints, simplicity-tagged floats, and 1-byte continuation flags on `Vec[T]` so deleting one element preserves sibling alignment).

When a crash, panic, SAST residual check, or timeout is caught, `ShrinkEngine` re-runs `ChoiceCursor` once with `recording = true` to capture 12-byte `ChoiceSpan` nodes and iterates five deterministic shortlex passes within `--fuzz-shrink-time=5s` (`5,000 ms`) before saving `tests/fuzz/corpus/<target>/crash-<blake3_16hex>.cxfuzz`:

1.  **Recursive ChoiceSpan Hoisting & Zeroing:** Replaces outer `Group` spans with nested same-type child spans and tests `memset(0)` across whole `Group`, `Bytes`, and `Str` spans to collapse irrelevant subtrees in one check.
2.  **Delta-Debugging (`ddmin`) Chunk Deletion:** Deletes contiguous `ListElem` spans and raw byte blocks at exponentially decreasing granularities (`M/2, M/4, ..., 1`).
3.  **Coupled Length-Header + Payload Deletion:** Simultaneously deletes `k` bytes from a `Bytes`/`ListElem` span while subtracting `k` from preceding `Int` spans so length-prefixed wire frames remain valid while shrinking.
4.  **Float & String Simplicity Stepping:** Steps float simplicity tags toward `0x00` (`0.0`) and simplifies UTF-8 characters toward ASCII `'0'` / `'a'`.
5.  **Per-Byte Shortlex Binary Search:** Binary-searches every remaining non-zero byte toward `0x00` until reaching a deterministic shortlex local minimum reproducing the identical failure signature.

### 3.4 Adaptive Monotonic Benchmarking (cx.bench): black_box Barrier, 1.4826 MAD Filtering & Peak Memory Tracking

`cx.bench` (`stdlib/cx/bench.cx`) executes `bench "name" (b: &mut Bencher) { … }` items with protection against dead-code elimination, timer quantization, and OS scheduling jitter. To avoid the `google/benchmark#1340` trap where `asm volatile("" : "+m,r"(v) : : "memory")` emits full `memcpy` spills on aggregates > 8 bytes under GCC-family backends, `black_box[T]` dispatches at `comptime` on `@size_of[T]() <= 8 and @implements[T, Copy]()`: register-sized scalars use `asm volatile("" : "+r"(val))` (forcing register materialization and forgetting value provenance with zero stack spills), while aggregates > 8 bytes take `var p = &raw mut val; asm volatile("" : "+r"(p) : : "memory");` without copying `val`.

During execution, `Bencher` runs a `150 ms` warmup, geometrically doubles `batch_iters` (`1, 2, 4, ...`, max `100,000,000`) until a single batch exceeds `MIN_BATCH_NS = 2_000_000` (`2.0 ms`), and collects `sample_count` (`100` default) monotonic per-op timings $x_i = \Delta t_i / \text{batch\_iters}$ while metering `allocs_per_iter`, `bytes_per_iter`, and `peak_live_bytes` (`Arena` slab high-water mark + `System` live heap bytes) via `BenchAllocMeter` on `context.allocator`. From sorted samples, `compute_mad_stats` derives median $m$, raw $\text{MAD} = \text{median}_i(|x_i - m|)$, and normal-consistent scaled MAD $\hat{\sigma}_{\text{MAD}} = 1.4826 \times \text{MAD}$ (providing a 50% breakdown point against contaminated OS IRQ/preemption samples). Samples outside $|x_i - m| \le \max(3.0 \times \hat{\sigma}_{\text{MAD}},\; 1.5 \times \text{IQR},\; 1.0\text{ ns})$ increment `outlier_count` and are trimmed before computing fast-path `median_ns`, `mean_ns`, and Bessel-corrected `stddev_ns`, whereas **`min_ns`, `p95_ns`, and `p99_ns` are evaluated over the raw pre-trim sample array** so genuine bimodal latency spikes are never hidden from `TableRenderer` reports.

> **Visual – Scaled Median Absolute Deviation Isolates Fast-Path Variance While Locking Phase 11.3 Self-Hosting Budgets:** Top: Across 100 monotonic batch samples of an HTTP/JSON parse micro-benchmark (~153.7 ns median), scaling raw MAD by 1.4826 builds a 50%-breakdown fence that trims 3 OS context-switch spikes (14.5–22.1 µs) from fast-path StdDev (1.51 ns) while retaining full tail visibility in raw P99. Bottom: All six Phase 11.3 STD-04 verification targets required before opening Phase 12 self-hosting.

### 3.5 Canonical Public API Signatures for stdlib/cx/test.cx and stdlib/cx/bench.cx

```rust
// File: stdlib/cx/test.cx
mod test;

use cx.col.Vec;

// ============================================================================
// [1] ASSERTIONS, GOLDEN SNAPSHOTS & PARALLEL RUNNER
// ============================================================================

@attribute_schema(targets: .Function)
pub struct TestAttr {
    pub should_panic: bool = false,
    pub ignore: bool = false,
    pub timeout_ms: u64 = 5_000,
    pub sim_liveness: bool = false,
}

pub fn assert_eq[T: Equatable](left: &T, right: &T, /, msg: FmtArgs = "", *, loc: SourceLoc = @caller_location());
pub fn assert_ne[T: Equatable](left: &T, right: &T, /, msg: FmtArgs = "", *, loc: SourceLoc = @caller_location());
pub fn assert_str_eq(expected: str, actual: str, /, *, loc: SourceLoc = @caller_location());
pub fn assert_bytes_eq(expected: &[u8], actual: &[u8], /, *, loc: SourceLoc = @caller_location());

/// Verifies `actual` against `tests/snapshots/<module>__<name>.snap` (updates atomically on `-u`).
pub fn assert_snapshot(name: str, actual: str, /, *, loc: SourceLoc = @caller_location());

// ============================================================================
// [2] DETERMINISTIC CONTEXT SIMULATION HARNESS (`corex test --sim --seed`)
// ============================================================================

pub mod sim {
    use cx.time.Duration;

    pub const DEFAULT_SIM_SEEDS: u32     = 1_000;
    pub const DEFAULT_MAX_SIM_STEPS: u64 = 250_000;

    @derive(Copy, Equatable)
    pub enum ScheduleMode: u8 { Pct = 0, SwarmRandom = 1, ExhaustiveDfs = 2 }

    @derive(Copy, Equatable)
    pub enum OomMode: u8 { ExhaustiveCountdown = 0, SwarmProbabilistic = 1, Off = 2 }

    @derive(Copy, Equatable)
    pub struct SimConfig {
        pub seed: u64,
        pub schedule_mode: ScheduleMode = .Pct,
        pub pct_depth: u8 = 2,
        pub oom_mode: OomMode = .ExhaustiveCountdown,
        pub max_steps: u64 = DEFAULT_MAX_SIM_STEPS,
        pub check_determinism: bool = true,
    }

    /// SplitMix64 -> Xoshiro256** unified deterministic PRNG backing `context.rng()`.
    pub struct SimPrng {
        state: [u64; 4],
        pub draw_count: u64,
    }

    impl SimPrng {
        @no_alloc @no_panic
        pub fn from_seed(seed: u64, /) -> Self;
        @inline @no_alloc @no_panic
        pub fn next_u64(&mut self) -> u64;
        @inline @no_alloc @no_panic
        pub fn hit_ppm(&mut self, prob_ppm: u32, /) -> bool;
    }

    /// Controlled fault-injection probe: folds to constant `false` (0 instructions) in `--release`.
    @inline @no_alloc @no_panic
    pub fn buggify(*, prob_ppm: u32 = 250_000, loc: SourceLoc = @caller_location()) -> bool;

    /// Simulated VFS & Network fault-injection hooks inside `test "…"` blocks.
    pub fn set_vfs_fault_rate(io_err_ppm: u32, partial_rw_ppm: u32, /);
    pub fn crash_remount_vfs(); // Discards all SimVfs writes not committed via `File.sync_data()`
    pub fn set_net_link_policy(delay_range: (Duration, Duration), drop_ppm: u32, /);
    pub fn partition_net_oneway(from_port: u16, to_port: u16, blocked: bool, /);

    pub enum SimViolation {
        AssertionOrPanic { message: str },
        Deadlock { blocked_tasks: u32, virtual_ns: u64 },
        StepBudgetExceeded { max_steps: u64 },
        LinearOrMemoryLeak { live_system_blocks: usize, live_arena_slabs: usize, unclosed_fds: u32 },
        NondeterminismDetected { alloc_or_step_idx: u64, expected_digest: u64, actual_digest: u64 },
    }

    pub fn run_with_seed(cfg: SimConfig, body: ||, /) -> u64!SimViolation;
}

// ============================================================================
// [3] IN-PROCESS SANITIZERCOVERAGE FUZZER & SHORTLEX SHRINKER (`--fuzz`)
// ============================================================================

pub mod fuzz {
    use cx.col.Vec;

    pub const DEFAULT_FUZZ_MAX_LEN: usize   = 4_096;
    pub const DEFAULT_FUZZ_TIMEOUT_MS: u64  = 1_000;
    pub const DEFAULT_SHRINK_BUDGET_MS: u64 = 5_000;

    @derive(Copy, Equatable)
    pub enum ChoiceKind: u8 {
        Group = 0, ListElem = 1, Bool = 2, Int = 3, Float = 4, Bytes = 5, Str = 6, Variant = 7,
    }

    /// 12-byte recorded structural span used strictly during post-crash shortlex shrinking.
    @repr(C)
    @derive(Copy)
    pub struct ChoiceSpan {
        pub start_off: u32,
        pub end_off: u32,
        pub parent_idx: u16,
        pub kind: ChoiceKind,
        pub type_hash_lo: u8,
    }

    pub struct ChoiceCursor {
        raw: &[u8],
        pos: usize,
        recording: bool,
        active_parent: u16,
        pub spans: Vec[ChoiceSpan],
    }

    impl ChoiceCursor {
        @no_alloc @no_panic @no_fuzz_instrument
        pub fn fast(raw: &[u8], /) -> Self;
        @inline @no_alloc @no_panic @no_fuzz_instrument
        pub fn next_byte(&mut self) -> u8;
        pub fn draw_bool(&mut self) -> bool;
        pub fn draw_uint_range[T: Unsigned](&mut self, min: T, max: T, /) -> T;
        pub fn draw_int_zigzag[T: Signed](&mut self, min: T, max: T, /) -> T;
        pub fn draw_f64(&mut self, *, allow_special: bool = true) -> f64;
        pub fn draw_str_utf8(&mut self, *, max_bytes: usize = 256) -> str;
        pub fn draw_bytes(&mut self, *, max_bytes: usize = 512) -> &[u8];
    }

    pub trait Arbitrary {
        fn arbitrary(cursor: &mut ChoiceCursor, /) -> Self;
    }

    pub struct FuzzConfig {
        pub max_len: usize = DEFAULT_FUZZ_MAX_LEN,
        pub timeout_ms: u64 = DEFAULT_FUZZ_TIMEOUT_MS,
        pub shrink_budget_ms: u64 = DEFAULT_SHRINK_BUDGET_MS,
        pub max_runs: u64? = .None,
        pub max_time_ms: u64? = .None,
        pub dictionary: &[&[u8]] = &[],
    }
}
```

```rust
// File: stdlib/cx/bench.cx
mod bench;

use cx.cli.TermCaps;
use cx.io.{IoError, Writer};

pub const DEFAULT_WARMUP_MS: u64    = 150;
pub const DEFAULT_SAMPLE_COUNT: u32 = 100;
pub const MIN_BATCH_NS: u64         = 2_000_000; // 2.0 ms minimum batch window
pub const MAD_SIGMA_SCALE: f64      = 1.4826;    // Normal-consistent MAD scale factor

@attribute_schema(targets: .Function)
pub struct BenchAttr {
    pub warmup_ms: u64 = DEFAULT_WARMUP_MS,
    pub sample_count: u32 is 10..=10_000 = DEFAULT_SAMPLE_COUNT,
    pub outlier_z_threshold: f64 = 3.0,
}

@derive(Copy)
pub struct BenchStats {
    pub batch_iters: u64,
    pub sample_count: u32,
    pub outlier_count: u32,
    pub min_ns: f64,
    pub median_ns: f64,        // Computed on MAD-filtered inliers
    pub mean_ns: f64,          // Computed on MAD-filtered inliers
    pub stddev_ns: f64,        // Bessel-corrected SD on MAD-filtered inliers
    pub mad_ns: f64,           // Raw median(|x_i - median|)
    pub scaled_mad_ns: f64,    // 1.4826 * mad_ns
    pub p95_ns: f64,           // Computed on raw pre-trim samples (preserves tail spikes)
    pub p99_ns: f64,           // Computed on raw pre-trim samples
    pub throughput_bytes_sec: u64,
    pub allocs_per_iter: f64,
    pub bytes_per_iter: u64,
    pub peak_live_bytes: usize, // Peak Arena + System live memory high-water mark
}

pub struct Bencher {
    pub batch_iters: u64,
    bytes_processed_per_iter: u64,
}

impl Bencher {
    @inline @no_alloc @no_panic
    pub fn set_bytes(&mut self, bytes_per_iter: u64, /);

    /// Executes `body` across `batch_iters` inside the adaptive calibration & sampling harness.
    @inline
    pub fn iter[R](&mut self, body: || -> R, /);
}

/// Zero-copy compiler optimization barrier (`+r` register on <=8B Copy; `&raw mut` + memory clobber on >8B).
@inline @no_alloc @no_panic
pub fn black_box[T](var val: own T, /) -> T {
    comptime if @size_of[T]() <= 8 and @implements[T, Copy]() {
        unsafe { @asm_reg_barrier(&mut val); }
    } else {
        var ptr = &raw mut val;
        unsafe { @asm_ptr_memory_barrier(&mut ptr); }
    }
    val
}

/// Computes `1.4826 * MAD` outlier-filtered summary metrics and raw tail quantiles in place.
@no_alloc @no_panic
pub fn compute_mad_stats(raw_samples_ns: &mut [f64], /, *, z_thresh: f64 = 3.0) -> BenchStats;

@no_alloc
pub fn render_bench_summary[W: Writer](
    out: &mut W,
    results: &[(str, BenchStats)],
    /,
    *,
    caps: TermCaps,
) -> unit!IoError;
```

### 3.6 Reference Implementations: --sim PCT Scheduler + OOM Injector, --fuzz SIMD Bucketing + Mutator + Shrinker, and MAD Stats

#### Reference Implementation D: Deterministic PCT Scheduler, Virtual Clock & System/Arena OOM Sweep (Zig)

```zig
//! Reference Implementation: cx.test.sim PCT Scheduler + Virtual Timer Heap + Prefix-Digest OOM Sweep
const std = @import("std");

pub const SimPrng = struct {
    s: [4]u64,
    draw_count: u64 = 0,

    pub fn fromSeed(seed: u64) SimPrng {
        var mixed = seed;
        var st: [4]u64 = undefined;
        for (0..4) |i| {
            mixed +%= 0x9E37_79B9_7F4A_7C15;
            var w = mixed;
            w = (w ^ (w >> 30)) *% 0xBF58_476D_1CE4_E5B9;
            w = (w ^ (w >> 27)) *% 0x94D0_49BB_1331_11EB;
            st[i] = w ^ (w >> 31);
        }
        return .{ .s = st };
    }

    pub inline fn nextU64(self: *SimPrng) u64 {
        self.draw_count +%= 1;
        const res = std.math.rotl(u64, self.s[1] *% 5, 7) *% 9;
        const t = self.s[1] << 17;
        self.s[2] ^= self.s[0];
        self.s[3] ^= self.s[1];
        self.s[1] ^= self.s[2];
        self.s[0] ^= self.s[3];
        self.s[2] ^= t;
        self.s[3] = std.math.rotl(u64, self.s[3], 45);
        return res;
    }
};

pub const TimerEvent = struct {
    deadline_ns: u64,
    tie_order: u64,
    wake_task_id: u32,

    fn lessThan(_: void, a: TimerEvent, b: TimerEvent) std.math.Order {
        const cmp = std.math.order(a.deadline_ns, b.deadline_ns);
        return if (cmp != .eq) cmp else std.math.order(a.tie_order, b.tie_order);
    }
};

pub const AllocSource = enum(u8) { system_heap = 0, arena_slab = 1 };

pub const SimWorld = struct {
    gpa: std.mem.Allocator,
    prng: SimPrng,
    monotonic_ns: u64 = 1_000_000_000, // Starts at 1.0s to catch zero-init timestamp bugs
    timers: std.PriorityQueue(TimerEvent, void, TimerEvent.lessThan),
    runnable: std.ArrayListUnmanaged(u32) = .{},
    task_prio: std.AutoHashMapUnmanaged(u32, i32) = .{},
    pct_depth: u8,
    drop_steps: [8]u64 = [_]u64{std.math.maxInt(u64)} ** 8,
    step_count: u64 = 0,

    // Unified System + Arena OOM Countdown & Streaming Determinism Canary
    alloc_seq: u64 = 0,
    fail_alloc_idx: u64 = std.math.maxInt(u64),
    exec_digest: u64 = 0xCBF2_9CE4_8422_2325,
    prefix_digests: std.ArrayListUnmanaged(u64) = .{},
    live_system_blocks: usize = 0,
    live_arena_slabs: usize = 0,

    pub fn init(gpa: std.mem.Allocator, seed: u64, pct_depth: u8, est_steps: u64, fail_idx: u64) SimWorld {
        var w = SimWorld{
            .gpa = gpa,
            .prng = SimPrng.fromSeed(seed),
            .timers = std.PriorityQueue(TimerEvent, void, TimerEvent.lessThan).init(gpa, {}),
            .pct_depth = pct_depth,
            .fail_alloc_idx = fail_idx,
        };
        const drops = @min(@as(usize, pct_depth -| 1), 8);
        for (0..drops) |d_i| {
            w.drop_steps[d_i] = (w.prng.nextU64() % @max(est_steps, 1)) + 1;
        }
        return w;
    }

    pub inline fn foldDigest(self: *SimWorld, tag: u64, a: u64, b: u64) void {
        inline for (.{ tag, a, b, self.monotonic_ns }) |v| {
            self.exec_digest = (self.exec_digest ^ v) *% 0x0000_0100_0000_01B3;
        }
    }

    pub fn spawnTask(self: *SimWorld, task_id: u32) !void {
        const initial_p: i32 = @as(i32, self.pct_depth) + @as(i32, @intCast(self.task_prio.count()));
        try self.task_prio.put(self.gpa, task_id, initial_p);
        try self.runnable.append(self.gpa, task_id);
        self.foldDigest(0x50A4, task_id, @intCast(initial_p));
    }

    pub fn scheduleSleepNs(self: *SimWorld, task_id: u32, delay_ns: u64) !void {
        const deadline = self.monotonic_ns + delay_ns;
        try self.timers.add(.{
            .deadline_ns = deadline,
            .tie_order = self.prng.nextU64(),
            .wake_task_id = task_id,
        });
        self.foldDigest(0x51EE, task_id, deadline);
    }

    /// PCT Priority Dispatcher + Quiescent Virtual-Clock Advance.
    pub fn nextRunnableTask(self: *SimWorld) !?u32 {
        while (self.runnable.items.len == 0) {
            const first_ev = self.timers.removeOrNull() orelse return null;
            self.monotonic_ns = @max(self.monotonic_ns, first_ev.deadline_ns);
            try self.runnable.append(self.gpa, first_ev.wake_task_id);

            while (self.timers.peek()) |top| {
                if (top.deadline_ns != first_ev.deadline_ns) break;
                const co_ev = self.timers.remove();
                try self.runnable.append(self.gpa, co_ev.wake_task_id);
            }
        }

        self.step_count += 1;
        var best_idx: usize = 0;
        var best_prio: i32 = std.math.minInt(i32);
        for (self.runnable.items, 0..) |tid, i| {
            const p = self.task_prio.get(tid).?;
            if (p > best_prio) {
                best_prio = p;
                best_idx = i;
            }
        }
        const chosen_tid = self.runnable.orderedRemove(best_idx);

        const drops = @min(@as(usize, self.pct_depth -| 1), 8);
        for (0..drops) |d_i| {
            if (self.step_count == self.drop_steps[d_i]) {
                const lowered: i32 = @as(i32, self.pct_depth) - 1 - @as(i32, @intCast(d_i));
                try self.task_prio.put(self.gpa, chosen_tid, lowered);
            }
        }
        self.foldDigest(0x5CAED, chosen_tid, self.step_count);
        return chosen_tid;
    }

    /// Intercepts BOTH `System` heap allocations and `Arena` backing-slab growth for countdown OOM injection.
    pub fn simAllocBytes(self: *SimWorld, source: AllocSource, byte_len: usize, align_log2: u8) ![]u8 {
        const cur_idx = self.alloc_seq;
        self.alloc_seq += 1;
        try self.prefix_digests.append(self.gpa, self.exec_digest);
        self.foldDigest(0xA110C, cur_idx, byte_len);

        if (cur_idx == self.fail_alloc_idx) {
            return error.OutOfMemory;
        }
        const raw = self.gpa.rawAlloc(byte_len, @enumFromInt(align_log2), @returnAddress()) orelse return error.OutOfMemory;
        if (source == .system_heap) self.live_system_blocks += 1 else self.live_arena_slabs += 1;
        return raw[0..byte_len];
    }
};
```

#### Reference Implementation E: --fuzz SanCov Registry, SIMD Hit-Bucketing, Havoc/TORC/DIV Mutator & Shrinker (Zig)

```zig
//! Reference Implementation: cx.test.fuzz SanCov PC/Cntr Init, SIMD Bucketing, TORC/DIV Ring & Shrinker
const std = @import("std");
const assert = std.debug.assert;

pub const PcEntry = extern struct { pc: usize, flags: usize }; // flags & 1 == function entry

/// Value-profile ring buffers (`TORC4`: 1024 x 8B, `TORC8`: 512 x 16B, `DIV8`: 128 x 8B).
pub const ValueProfileRings = struct {
    pub const Pair4 = extern struct { arg1: u32, arg2: u32 };
    pub const Pair8 = extern struct { arg1: u64, arg2: u64 };

    torc4: [1024]Pair4 = [_]Pair4{.{ .arg1 = 0, .arg2 = 0 }} ** 1024,
    torc8: [512]Pair8 = [_]Pair8{.{ .arg1 = 0, .arg2 = 0 }} ** 512,
    div8: [128]u64 = [_]u64{0} ** 128,

    pub inline fn recordCmp8(self: *ValueProfileRings, caller_pc: usize, a1: u64, a2: u64) void {
        if (a1 == a2) return;
        const slot = (caller_pc ^ @as(usize, @truncate(a1 ^ a2))) & 511;
        self.torc8[slot] = .{ .arg1 = a1, .arg2 = a2 };
    }

    pub inline fn recordDiv8(self: *ValueProfileRings, caller_pc: usize, divisor: u64) void {
        if (divisor <= 1) return;
        self.div8[(caller_pc ^ @as(usize, @truncate(divisor))) & 127] = divisor;
    }
};

/// Sweeps `__sancov_cntrs` in 32-byte SIMD chunks, mapping counts to AFL's 9 logarithmic buckets
/// (`1 << count_ge(c, [2,3,4,8,16,32,128])`), updating `virgin_mask`, and zeroing counters in place.
pub fn sweepSanCovCountersSimd32(cntrs: []u8, virgin_mask: []u8) usize {
    assert(cntrs.len == virgin_mask.len);
    var newly_unlocked_buckets: usize = 0;
    var idx: usize = 0;
    const zero_vec: @Vector(32, u8) = @splat(0);
    const one_vec: @Vector(32, u8) = @splat(1);

    while (idx + 32 <= cntrs.len) : (idx += 32) {
        const c: @Vector(32, u8) = cntrs[idx..][0..32].*;
        if (@reduce(.Or, c) == 0) continue;

        var shift_k: @Vector(32, u3) = @splat(0);
        inline for (.{ 2, 3, 4, 8, 16, 32, 128 }) |thresh| {
            const ge_mask = c >= @as(@Vector(32, u8), @splat(thresh));
            shift_k += @select(u3, ge_mask, @as(@Vector(32, u3), @splat(1)), @as(@Vector(32, u3), @splat(0)));
        }
        const raw_buckets = one_vec << shift_k;
        const buckets = @select(u8, c != zero_vec, raw_buckets, zero_vec);

        const v_mask: @Vector(32, u8) = virgin_mask[idx..][0..32].*;
        const discovered = buckets & v_mask;
        if (@reduce(.Or, discovered) != 0) {
            virgin_mask[idx..][0..32].* = v_mask & ~discovered;
            newly_unlocked_buckets += @reduce(.Add, @as(@Vector(32, u16), @popCount(discovered)));
        }
        cntrs[idx..][0..32].* = zero_vec;
    }

    while (idx < cntrs.len) : (idx += 1) {
        const val = cntrs[idx];
        if (val == 0) continue;
        const k: u3 = @as(u3, @intFromBool(val >= 2)) + @as(u3, @intFromBool(val >= 3)) +
            @as(u3, @intFromBool(val >= 4)) + @as(u3, @intFromBool(val >= 8)) +
            @as(u3, @intFromBool(val >= 16)) + @as(u3, @intFromBool(val >= 32)) +
            @as(u3, @intFromBool(val >= 128));
        const b: u8 = @as(u8, 1) << k;
        const hit = b & virgin_mask[idx];
        if (hit != 0) {
            virgin_mask[idx] &= ~hit;
            newly_unlocked_buckets += @popCount(hit);
        }
        cntrs[idx] = 0;
    }
    return newly_unlocked_buckets;
}

/// Stacked Havoc + Dictionary + TORC8 Input-to-State (`I2S`) + DIV-to-Zero Mutator.
pub fn mutateHavocAndTorc(
    buf: []u8,
    cur_len: usize,
    max_len: usize,
    prng: *std.Random.Xoshiro256,
    vp: *const ValueProfileRings,
    dict: []const []const u8,
) usize {
    var len = cur_len;
    const rnd = prng.random();
    const stack_ops = rnd.intRangeAtMost(usize, 1, 8);

    for (0..stack_ops) |_| {
        switch (rnd.intRangeLessThan(u8, 0, 7)) {
            0 => {
                if (len == 0) continue;
                buf[rnd.uintLessThan(usize, len)] ^= (@as(u8, 1) << rnd.int(u3));
            },
            1 => {
                if (len < 4) continue;
                const pos = rnd.uintLessThan(usize, len - 3);
                const delta: u32 = rnd.intRangeAtMost(u32, 1, 35);
                var v = std.mem.readInt(u32, buf[pos..][0..4], .little);
                v = if (rnd.boolean()) v +% delta else v -% delta;
                std.mem.writeInt(u32, buf[pos..][0..4], if (rnd.boolean()) v else @byteSwap(v), .little);
            },
            2 => {
                if (len + 4 > max_len) continue;
                const pos = if (len == 0) 0 else rnd.uintLessThan(usize, len + 1);
                std.mem.copyBackwards(u8, buf[pos + 4 .. len + 4], buf[pos..len]);
                rnd.bytes(buf[pos .. pos + 4]);
                len += 4;
            },
            3 => {
                if (len <= 2) continue;
                const del_n = rnd.intRangeAtMost(usize, 1, @min(len - 1, 16));
                const pos = rnd.uintLessThan(usize, len - del_n + 1);
                std.mem.copyForwards(u8, buf[pos .. len - del_n], buf[pos + del_n .. len]);
                len -= del_n;
            },
            4 => {
                if (dict.len == 0) continue;
                const tok = dict[rnd.uintLessThan(usize, dict.len)];
                if (tok.len > 0 and len >= tok.len) {
                    const pos = rnd.uintLessThan(usize, len - tok.len + 1);
                    @memcpy(buf[pos .. pos + tok.len], tok);
                }
            },
            5 => { // TORC8 Input-to-State (I2S) magic-constant replacement (`arg2 -> arg1`)
                if (len < 8) continue;
                const pair = vp.torc8[rnd.uintLessThan(usize, 512)];
                if (pair.arg1 == pair.arg2) continue;
                var needle: [8]u8 = undefined;
                var repl: [8]u8 = undefined;
                const swap_endian = rnd.boolean();
                std.mem.writeInt(u64, &needle, if (swap_endian) @byteSwap(pair.arg2) else pair.arg2, .little);
                std.mem.writeInt(u64, &repl, if (swap_endian) @byteSwap(pair.arg1) else pair.arg1, .little);
                if (std.mem.indexOf(u8, buf[0..len], &needle)) |match_off| {
                    @memcpy(buf[match_off .. match_off + 8], &repl);
                }
            },
            6 => { // DIV8 value-profile mutation (`divisor -> 0` to expose DivideByZero panics)
                if (len < 8) continue;
                const div_val = vp.div8[rnd.uintLessThan(usize, 128)];
                if (div_val == 0) continue;
                var needle: [8]u8 = undefined;
                std.mem.writeInt(u64, &needle, div_val, .little);
                if (std.mem.indexOf(u8, buf[0..len], &needle)) |match_off| {
                    @memset(buf[match_off .. match_off + 8], 0);
                }
            },
            else => unreachable,
        }
    }
    return len;
}

pub const ChoiceSpan = extern struct {
    start_off: u32,
    end_off: u32,
    parent_idx: u16,
    kind: u8,
    type_hash_lo: u8,
};

/// Hierarchical Shortlex Crash Minimizer (`ChoiceSpan` zeroing -> `ddmin` -> byte binary search).
pub fn shrinkCrashShortlex(
    alloc: std.mem.Allocator,
    initial: []const u8,
    recorded_spans: []const ChoiceSpan,
    reproducesCrash: *const fn (candidate: []const u8) bool,
) ![]u8 {
    var best = try alloc.dupe(u8, initial);
    var scratch = try alloc.alloc(u8, initial.len);
    defer alloc.free(scratch);

    for (recorded_spans) |sp| {
        if (sp.end_off > best.len or sp.start_off >= sp.end_off) continue;
        @memcpy(scratch[0..best.len], best);
        @memset(scratch[sp.start_off..sp.end_off], 0);
        if (!std.mem.eql(u8, scratch[0..best.len], best) and reproducesCrash(scratch[0..best.len])) {
            @memcpy(best, scratch[0..best.len]);
        }
    }

    var progress = true;
    while (progress) {
        progress = false;

        var gran: usize = best.len / 2;
        while (gran >= 1) : (gran /= 2) {
            var pos: usize = 0;
            while (pos + gran <= best.len) {
                const new_len = best.len - gran;
                @memcpy(scratch[0..pos], best[0..pos]);
                @memcpy(scratch[pos..new_len], best[pos + gran .. best.len]);
                if (reproducesCrash(scratch[0..new_len])) {
                    best = best[0..new_len];
                    @memcpy(best, scratch[0..new_len]);
                    progress = true;
                } else {
                    pos += if (gran > 4) gran / 2 else 1;
                }
            }
        }

        for (0..best.len) |i| {
            if (best[i] == 0) continue;
            var lo: u8 = 0;
            var hi: u8 = best[i];
            while (lo < hi) {
                const mid: u8 = lo + (hi - lo) / 2;
                const saved = best[i];
                best[i] = mid;
                if (reproducesCrash(best)) {
                    hi = mid;
                    progress = true;
                } else {
                    best[i] = saved;
                    lo = mid + 1;
                }
            }
        }
    }
    return best;
}
```

#### Reference Implementation F: cx.bench 1.4826 MAD Outlier Filter & Raw Tail Quantiles (.cx)

```rust
// File: stdlib/cx/bench_stats.cx
mod bench_stats;

use cx.bench.{BenchStats, MAD_SIGMA_SCALE};
use cx.col.pdqsort_f64;
use cx.math.{abs_f64, floor_f64, ceil_f64, sqrt_f64};

@inline @no_alloc @no_panic
fn sorted_quantile(sorted: &[f64], q: f64, /) -> f64 {
    let pos = q * ((sorted.len() - 1) as f64);
    let lo = floor_f64(pos) as usize;
    let hi = ceil_f64(pos) as usize;
    let frac = pos - (lo as f64);
    sorted[lo] * (1.0 - frac) + sorted[hi] * frac
}

@no_alloc @no_panic
pub fn compute_mad_stats(raw_samples_ns: &mut [f64], /, *, z_thresh: f64 = 3.0) -> BenchStats {
    pdqsort_f64(raw_samples_ns);
    let n = raw_samples_ns.len();
    let min_v = raw_samples_ns[0];
    let raw_med = sorted_quantile(raw_samples_ns, 0.50);
    let raw_p95 = sorted_quantile(raw_samples_ns, 0.95);
    let raw_p99 = sorted_quantile(raw_samples_ns, 0.99);
    let iqr = sorted_quantile(raw_samples_ns, 0.75) - sorted_quantile(raw_samples_ns, 0.25);

    var devs: [f64; 1024] = [0.0; 1024];
    let dev_len = if n <= 1024 { n } else { 1024 };
    for i in 0..dev_len {
        devs[i] = abs_f64(raw_samples_ns[i] - raw_med);
    }
    pdqsort_f64(&mut devs[..dev_len]);
    let raw_mad = sorted_quantile(devs[..dev_len], 0.50);
    let scaled_mad = MAD_SIGMA_SCALE * raw_mad;

    // 50%-breakdown MAD fence with IQR fallback if quantized clock yields raw_mad == 0
    var fence = z_thresh * scaled_mad;
    if 1.5 * iqr > fence { fence = 1.5 * iqr; }
    if fence < 1.0 { fence = 1.0; }

    var inlier_lo: usize = 0;
    while inlier_lo < n and abs_f64(raw_samples_ns[inlier_lo] - raw_med) > fence {
        inlier_lo += 1;
    }
    var inlier_hi: usize = n;
    while inlier_hi > inlier_lo and abs_f64(raw_samples_ns[inlier_hi - 1] - raw_med) > fence {
        inlier_hi -= 1;
    }
    let inliers = if inlier_hi - inlier_lo >= 3 {
        raw_samples_ns[inlier_lo..inlier_hi]
    } else {
        raw_samples_ns[..]
    };

    var sum: f64 = 0.0;
    for x in inliers { sum += x; }
    let mean_v = sum / (inliers.len() as f64);
    var sq_sum: f64 = 0.0;
    for x in inliers {
        let d = x - mean_v;
        sq_sum += d * d;
    }
    let variance = sq_sum / ((inliers.len() - 1) as f64);

    BenchStats {
        batch_iters: 1,
        sample_count: n as u32,
        outlier_count: (n - inliers.len()) as u32,
        min_ns: min_v,
        median_ns: sorted_quantile(inliers, 0.50),
        mean_ns: mean_v,
        stddev_ns: sqrt_f64(variance),
        mad_ns: raw_mad,
        scaled_mad_ns: scaled_mad,
        p95_ns: raw_p95,
        p99_ns: raw_p99,
        throughput_bytes_sec: 0,
        allocs_per_iter: 0.0,
        bytes_per_iter: 0,
        peak_live_bytes: 0,
    }
}
```

---

## 4. Self-Hosting Parity, Untrusted-Input Bounds, and Phase 11.3 Verification Matrix

Every Phase 11.3 module maps directly onto its Phase 12 self-hosted compiler consumer (`compiler/*.cx`) and is gated by explicit untrusted-input bounds and quantitative performance thresholds before opening Phase 12.1:

| Subsystem & Source File | Phase 12 Self-Hosted Consumer(s) | Hard Untrusted-Input Bounds (`AGENTS.md` §2) | Strict Parity & Performance Target | Verification Gate Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| **`cx.cli` (`stdlib/cx/cli.cx`)** | `compiler/main.cx` (router), `compiler/diag.cx`, `compiler/upgrade.cx`, `corex check --caps` | `MAX_FLAG_LEN = 64` (`195 B` stack OSA), `MAX_MULTILINE_LANES = 8`, `MAX_DIFF_COST = 4,096`, `max_errors = 100` | **`0 B` heap allocations** in `parse_from_slice` & primary diagnostic streaming; `< 1.5 ms` CLI cold start; `< 10 KB` freestanding `.wasm` | Allocation-counter unit hook (`alloc_seq == 0`), `drift_guard_test` (`0` emojis), `NO_COLOR=1` golden snapshots |
| **`cx.serde.json` (`stdlib/cx/serde.cx`)** | `compiler/lsp_server.cx` (JSON-RPC 2.0 `stdio` framing & LSP DTOs), sparse registry NDJSON (`pkg_resolver.cx`) | `MAX_JSON_DEPTH = 64` (`[OpenScope; 64]` stack), `MAX_LSP_FRAME_BYTES = 16 MiB`, `DEFAULT_MAX_JSON_BYTES = 64 MiB`, UTF-8 3-LUT DFA | **`>= 1.5 GB/s`** 64-bit `JsonTape` throughput (`~2.2 GB/s` peak on `twitter.json`); **`< 10 ms` P99** `corex lsp` keystroke turnaround | `corex bench` throughput gate on `twitter.json` / `citm_catalog.json` + headless LSP replay stress benchmark (`bench/lsp`) |
| **`cx.serde.toml` (`stdlib/cx/serde.cx`)** | `compiler/pkg_manifest.cx` (`corex.toml` & `corex.lock` codec + `corex add`/`remove`/`upgrade` surgical edits) | `MAX_TOML_DEPTH = 64`, `DEFAULT_MAX_TOML_BYTES = 16 MiB`, strict control-char comment ban, duplicate-key & reopened-table rejection | Exact **`8 B` `TomlToken`** & **`16 B` `TomlCstNode`** SoA footprint; **100% bit-for-bit** round-trip & comment retention on untouched spans | Official `toml-test` v1.1.0 + v1.0.0 conformance suite + property fuzzer verifying `apply(source, edits)` comment retention |
| **`cx.test` (`--sim` & `--fuzz`, `stdlib/cx/test.cx`)** | All `core/`, `stdlib/cx/`, and `compiler/*.cx` suites + 4-tier `diff_oracle` (`--diff-backends`) | `DEFAULT_MAX_SIM_STEPS = 250,000`, `E0331` syscall ban, `W0332` ASLR cast guard; `DEFAULT_FUZZ_MAX_LEN = 4,096` (max `1 MiB`), `timeout = 1,000 ms`, `shrink = 5,000 ms` | **100% bit-exact `ExecutionDigest` replay** across runs and across `x86_64` / `aarch64` for identical `--seed`; `< 2.0 s` cold unit/snapshot suite; `0` crashes across `10,000,000` fuzz runs | 500-seed `--sim --check-determinism --sim-strict` cross-ISA gate + `TORC8` synthetic crash-and-shrink (`<= 16 B` in `tests/fuzz/corpus/`) gate |
| **`cx.bench` (`stdlib/cx/bench.cx`)** | `bench/` C/Rust parity suite (`<= 1.00x` vs `clang -O3` / `rustc -O`) & Phase 12 compiler throughput gates | `sample_count` bounded to `10..=10,000`, `batch_iters <= 100,000,000`, `MIN_BATCH_NS = 2.0 ms`, `1.4826 * MAD` 50%-breakdown filter | Zero `memcpy` spill in `black_box` (`+r` <= 8B, ptr+memory > 8B); clean inlier `Median`/`StdDev` + raw `P95`/`P99` + exact `Arena`/`System` peak bytes | Synthetic contaminated-sample test (asserting `3` injected `20 µs` spikes do not shift `Median` or inflate `StdDev`) + disassembly check on `black_box` |

### Phase 11.3 Sign-Off Checklist

1.  **Compile-Time Layout & Static SAST Gate:** Run `corex check --sast-strict --deny-warnings stdlib/cx/` confirming zero `E03xx`/`W03xx` memory, region-escape (`E0306`), `@no_alloc`, or `@no_panic` violations across `cli.cx`, `serde.cx`, `test.cx`, and `bench.cx`, and verifying `@size_of[TomlToken]() == 8`, `@size_of[TomlCstNode]() == 16`, `@size_of[TapeWord]() == 8`, and `@size_of[ChoiceSpan]() == 12` via `comptime` assertions.
2.  **Four-Tier Differential Backend Parity Gate:** Execute `corex test --diff-backends` over the `cx.cli`, `cx.serde.json` (SWAR vs. SIMD Stage-1 equivalence and Eisel–Lemire vs. stack HPD boundary floats), and `cx.serde.toml` suites across pre-opt `MirVm`, post-opt `MirVm`, Tier A (`-ofmt=c`), and Tier B (`LLVM`).
3.  **Tree-Shaking & Cold-Start Footprint Gate:** Compile a minimal `cx.cli` `@cli_command` binary under `--release --link=static` and `--target=wasm32-unknown-freestanding`, asserting `< 1.5 ms` native cold-start execution, `< 500 KB` stripped native CLI binary size, `< 10 KB` freestanding `.wasm` size, and zero linked symbols from `cx.serde`, `cx.test`, or `cx.net`.
4.  **Emoji & Formatting Drift Gate:** Run `corex fmt --check` and `tests/drift/drift_guard_test` across all Phase 11.3 stdlib and snapshot files, confirming 100% pass-1 formatter idempotency and zero colored emojis repository-wide before opening Phase 12.1.

//! Compiler Diagnostic Representation, Code Catalog & Transactional Patcher
//!
//! Defines the strongly typed `DiagnosticCode` registry (`E00xx`–`E05xx` and `W00xx`–`W05xx`), 16-byte
//! `TextEdit` records, arena-backed `DiagnosticSink` with a bounded 100-error cap, and `TransactionalPatcher`.
//!
//! All diagnostic strings, secondary label slices, notes, and `SuggestedFix` edit bundles are cloned
//! into `DiagnosticSink.arena` upon emission so passes never manage diagnostic buffer lifetimes manually.

const std = @import("std");
const mem = @import("../mem_foundation.zig");
const style = @import("../cli/style.zig");

const FileId = mem.FileId;
const StringId = mem.StringId;
const Span = mem.Span;
const BumpArena = mem.BumpArena;
const StringInterner = mem.StringInterner;

// ---------------------------------------- TYPES ----------------------------------------

/// Diagnostic severity level governing exit status and monochrome header glyph selection.
pub const Severity = enum(u8) {
    /// Fatal compilation error (`✗ error[E0001]`).
    err = 0,
    /// Non-fatal compiler or lint warning (`⚠︎ warning[W0001]`).
    warning = 1,
    /// Supplemental context note (`• note`).
    note = 2,
    /// Actionable remediation hint (`▸ help`).
    help = 3,

    /// Alias for `.note` matching informational diagnostic terminology.
    pub const info: Severity = .note;

    /// Returns the canonical lowercase label string for this `Severity`.
    pub fn asLabel(self: Severity) []const u8 {
        return switch (self) {
            .err => "error",
            .warning => "warning",
            .note => "note",
            .help => "help",
        };
    }

    /// Returns the strictly monochrome Unicode status glyph for this `Severity`.
    pub fn asStatusGlyph(self: Severity) []const u8 {
        return switch (self) {
            .err => style.Glyphs.FAILURE,
            .warning => style.Glyphs.WARNING,
            .note => style.Glyphs.BULLET,
            .help => style.Glyphs.POINTER_SOLID,
        };
    }

    /// Returns the semantic `StyleRole` associated with this `Severity`.
    pub fn asStyleRole(self: Severity) style.StyleRole {
        return switch (self) {
            .err => .err,
            .warning => .warning,
            .note => .note,
            .help => .help,
        };
    }
};

/// Confidence classification for automated source rewrites in `corex fix` and `corex upgrade`.
pub const FixApplicability = enum(u8) {
    /// Mathematically proven semantics-preserving transformation; applied automatically by `corex fix`.
    machine_applicable = 0,
    /// Contains user-fillable placeholders like `<expr>`; never auto-applied without confirmation.
    has_placeholders = 1,
    /// Heuristic suggestion; displayed in CLI diagnostic output only.
    maybe_incorrect = 2,
    /// Unspecified or manual prose instruction.
    unspecified = 3,
};

/// Priority tier governing conflict resolution when multiple `SuggestedFix` bundles overlap.
pub const EditPriority = enum(u8) {
    /// Highest-priority memory, lifetime, or ownership safety fix.
    memory_safety = 0,
    /// Type system or standard library API migration rewrite.
    type_migration = 1,
    /// Surface syntax canonicalization or missing delimiter repair.
    syntax_canonicalization = 2,
    /// Idiomatic lint or identifier casing normalization.
    lint_idiom = 3,
    /// Whitespace or cosmetic formatting adjustment.
    formatting = 4,
};

/// Exact 16-byte source byte replacement record (`extern struct`) using an interned `StringId`.
pub const TextEdit = extern struct {
    /// Target source file identifier.
    file_id: FileId,
    /// Inclusive starting byte offset within `file_id`.
    start_byte: u32,
    /// Exclusive ending byte offset within `file_id`.
    end_byte: u32,
    /// Interned replacement text handle in `StringInterner`.
    replacement_id: StringId,

    /// Returns the 12-byte `Span` replaced by this `TextEdit`.
    pub inline fn asSpan(self: TextEdit) Span {
        return Span.init(self.file_id, self.start_byte, self.end_byte);
    }

    /// Returns the byte length of the replaced source range (`end_byte -| start_byte`).
    pub inline fn countBytes(self: TextEdit) u32 {
        return self.end_byte -| self.start_byte;
    }
};

/// Atomic bundle of one or more `TextEdit` replacements attached to a `Diagnostic`.
pub const SuggestedFix = struct {
    /// Human-readable description of the suggested transformation.
    message: []const u8,
    /// Automated application confidence level.
    applicability: FixApplicability = .machine_applicable,
    /// Priority tier used by `TransactionalPatcher` during interval scheduling.
    priority: EditPriority = .syntax_canonicalization,
    /// Contiguous slice of byte edits that must be applied or rejected atomically.
    edits: []const TextEdit = &.{},
};

/// Visual underline style for a `LabeledSpan` inside a rendered source snippet.
pub const LabelStyle = enum(u8) {
    /// Primary focal span underlined with `^` carets.
    primary = 0,
    /// Secondary explanatory span underlined with `─` horizontal dashes.
    secondary = 1,
};

/// Annotated source byte span displayed within a diagnostic snippet box.
pub const LabeledSpan = struct {
    /// Source byte range to highlight.
    span: Span,
    /// Explanatory message rendered alongside the span underline.
    label: []const u8,
    /// Visual underline role (`.primary` or `.secondary`).
    style: LabelStyle = .primary,
};

/// Canonical non-overlapping diagnostic code registry (`PLAN.md` Section 2.5).
pub const DiagnosticCode = enum(u16) {
    // E00xx; CLI, Workspace, Manifest & VFS:
    /// Unknown CLI option or flag (`E0001`).
    e0001_unknown_cli_flag = 0,
    /// Unknown CLI subcommand (`E0002`).
    e0002_unknown_cli_subcommand = 1,
    /// Missing required CLI argument (`E0003`).
    e0003_missing_cli_argument = 2,
    /// Source file I/O read or stat failure (`E0004`).
    e0004_source_file_io_error = 3,
    /// Source file exceeds the 64 MiB maximum size cap (`E0005`).
    e0005_source_file_size_exceeded = 4,

    // E01xx; Lexical Scanning, UTF-8 & Literal Rules:
    /// Invalid UTF-8 byte sequence in source file (`E0101`).
    e0101_invalid_utf8_sequence = 5,
    /// Unterminated string or character literal (`E0102`).
    e0102_unterminated_string_literal = 6,
    /// Malformed numeric literal or invalid digit separator (`E0103`).
    e0103_invalid_numeric_literal = 7,
    /// File token count exceeds `MAX_TOKENS_PER_FILE` (`E0104`).
    e0104_token_limit_exceeded = 8,

    // E02xx; Syntax Parsing, Recovery & Casing:
    /// Unexpected token in grammar production (`E0201`).
    e0201_unexpected_token = 9,
    /// Unclosed block, group, or generic delimiter (`E0202`).
    e0202_unclosed_delimiter = 10,
    /// Parser recursion depth exceeded `MAX_PARSE_DEPTH` (`E0203`).
    e0203_parse_depth_exceeded = 11,

    // E03xx; MIR SAST Memory, Ownership, Capabilities & Exclusivity:
    /// Use of deallocated or freed value (`E0301`).
    e0301_use_after_free = 12,
    /// Use of moved value after ownership transfer (`E0302`).
    e0302_use_after_move = 13,
    /// Read of possibly uninitialized memory or binding (`E0303`).
    e0303_uninitialized_memory_read = 14,
    /// Unconsumed `@linear` resource or memory leak (`E0304`).
    e0304_resource_or_memory_leak = 15,
    /// Mutable aliasing or MVS loan exclusivity violation (`E0305`).
    e0305_exclusivity_violation = 16,
    /// Value escapes lexical arena or stack region (`E0306`).
    e0306_region_escape_violation = 17,
    /// Compile-time proven out-of-bounds buffer access (`E0307`).
    e0307_static_buffer_overflow = 18,
    /// Double free or duplicate `@linear` resource consumption (`E0313`).
    e0313_double_free_or_close = 19,
    /// `FromBytes` / `IntoBytes` wire layout contract violation (`E0315`).
    e0315_wire_layout_contract_violation = 20,
    /// Worst-case call stack exceeds `@max_stack` budget (`E0316`).
    e0316_max_stack_budget_exceeded = 21,
    /// `@no_alloc` contract violated by heap allocation (`E0320`).
    e0320_no_alloc_contract_violation = 22,
    /// `@no_panic` contract violated by residual trap path (`E0321`).
    e0321_no_panic_contract_violation = 23,
    /// `@no_block` contract violated by blocking operation (`E0322`).
    e0322_no_block_contract_violation = 24,
    /// Trait `impl` method escalates signature contract (`E0323`).
    e0323_trait_impl_effect_escalation = 25,
    /// Package exceeds authorized capability policy (`E0324`).
    e0324_package_capability_violation = 26,
    /// Forbidden capability in hermetic `comptime` context (`E0325`).
    e0325_comptime_sandbox_violation = 27,
    /// `@embed_bytes` path escapes package sandbox root (`E0326`).
    e0326_embed_path_escape = 28,
    /// Forbidden linker section or sandbox bypass attribute (`E0327`).
    e0327_forbidden_sandbox_bypass_attribute = 29,
    /// Scratch arena rewind aliases caller output arena (`E0328`).
    e0328_scratch_arena_ping_pong_conflict = 30,

    // E04xx; Type System, Inference, Traits, Bounds & Error Semantics:
    /// Ambiguous overload call in explicit overload group (`E0400`).
    e0400_ambiguous_overload = 31,
    /// Mismatched types between expected and found expressions (`E0401`).
    e0401_type_mismatch = 32,
    /// Type does not satisfy constrained trait or type group bound (`E0402`).
    e0402_unsatisfied_trait_bound = 33,
    /// Unresolved identifier or symbol in scope (`E0403`).
    e0403_unresolved_symbol = 34,
    /// Conflicting concrete types for a Bind-Once Constrained Type Group (`E0404`).
    e0404_bind_once_group_conflict = 35,
    /// Distinct nominal type mixed with underlying representation without `as` or `~T` (`E0405`).
    e0405_distinct_type_mixing = 36,
    /// Compile-time value or width violates range refinement or bit-field bounds (`E0406`).
    e0406_range_refinement_violation = 37,
    /// Contextual `.Variant` syntax cannot be resolved against expected type (`E0407`).
    e0407_invalid_contextual_variant = 38,
    /// Duplicate symbol definition in the same namespace and lexical scope (`E0408`).
    e0408_duplicate_definition = 39,
    /// Access to a private item, field, or method outside its defining module (`E0409`).
    e0409_private_symbol_access = 40,
    /// Postfix `?` operator used outside a fallible `Result` or `Option` function (`E0410`).
    e0410_try_outside_fallible_fn = 41,
    /// Propagated error type cannot be converted via `FromError` or `@from` (`E0411`).
    e0411_missing_from_error_conversion = 42,
    /// `let … else` guard block does not unconditionally diverge (`never`) (`E0412`).
    e0412_let_else_not_diverging = 43,
    /// Unhandled `Result[T, E]` or `@must_use` value in expression statement (`E0413`).
    e0413_unhandled_must_use_or_result = 44,
    /// Forbidden bare `let _ = fallible()` discard of a `Result[T, E]` without `catch` (`E0414`).
    e0414_bare_wildcard_result_discard = 45,
    /// Non-exhaustive pattern arms in `match` expression (`E0415`).
    e0415_non_exhaustive_match = 46,

    // E05xx; Comptime Virtual Machine & MIR Lowering:
    /// Compile-time execution exceeded step fuel budget (`E0501`).
    e0501_comptime_step_limit_exceeded = 47,
    /// Compile-time integer arithmetic overflow (`E0502`).
    e0502_integer_constant_overflow = 48,
    /// Forbidden non-deterministic, FFI, I/O, or raw pointer-to-integer operation in `comptime` (`E0503`).
    e0503_forbidden_comptime_operation = 49,
    /// Out-of-bounds array, slice, or virtual allocation access in `comptime` (`E0504`).
    e0504_comptime_out_of_bounds = 50,
    /// Read from uninitialized virtual memory bytes in `comptime` (`E0505`).
    e0505_comptime_uninitialized_read = 51,
    /// Null, misaligned, or dangling virtual pointer dereference in `comptime` (`E0506`).
    e0506_comptime_invalid_pointer = 52,
    /// Division by zero, remainder by zero, or invalid shift count in `comptime` (`E0507`).
    e0507_comptime_arithmetic_trap = 53,
    /// Virtual heap, call depth, loop unroll, or `@embed_bytes` cap exceeded in `comptime` (`E0508`).
    e0508_comptime_resource_limit_exceeded = 54,
    /// Cyclic dependency across `const` or `comptime` evaluations (`E0509`).
    e0509_comptime_evaluation_cycle = 55,
    /// Failed `@compile_assert` or reached `@compile_error` intrinsic (`E0510`).
    e0510_compile_assertion_failed = 56,

    // W00xx to W05xx; Subsystem Compiler Warnings:
    /// Deprecated CLI invocation or option (`W0001`).
    w0001_deprecated_cli_option = 57,
    /// Redundant character escape sequence in literal (`W0101`).
    w0101_redundant_escape_sequence = 58,
    /// Identifier does not follow canonical CoreX casing (`W0201`).
    w0201_non_canonical_identifier_case = 59,
    /// Unused region capability or linear binding (`W0308`).
    w0308_unused_region_allocation = 60,
    /// Slice or array bounds not statically proven under `--sast-strict` (`W0314`).
    w0314_unproven_bounds_access = 61,
    /// Panic inside vacated non-`Copy` projection inserts abort guard (`W0329`).
    w0329_vacated_projection_panic_abort = 62,
    /// Unreachable high-risk capability exported by dependency (`W0330`).
    w0330_ambient_dead_capability_in_dep = 63,
    /// Unreachable pattern arm in `match` expression (`W0401`).
    w0401_unreachable_pattern_arm = 64,
    /// Unused local variable binding or function parameter (`W0402`).
    w0402_unused_binding = 65,
    /// Function exceeds MIR inlining cost threshold (`W0501`).
    w0501_inlining_budget_exceeded = 66,

    /// Ergonomic alias for `.e0502_integer_constant_overflow`.
    pub const e0502_integer_overflow: DiagnosticCode = .e0502_integer_constant_overflow;

    /// Returns the static `DiagnosticDescriptor` metadata for this `DiagnosticCode` in $O(1)$ time.
    pub inline fn asDescriptor(self: DiagnosticCode) DiagnosticDescriptor {
        return DIAGNOSTIC_CATALOG[@backingInt(self)];
    }

    /// Returns the 5-character canonical code string (e.g., `"E0302"` or `"W0308"`).
    pub inline fn asCodeStr(self: DiagnosticCode) []const u8 {
        return self.asDescriptor().code_str;
    }

    /// Returns the default `Severity` for this `DiagnosticCode`.
    pub inline fn defaultSeverity(self: DiagnosticCode) Severity {
        return self.asDescriptor().default_severity;
    }

    /// Resolves a canonical 5-character code string (e.g., `"E0302"`) to its `DiagnosticCode`.
    pub fn fromCodeStr(code_str: []const u8) ?DiagnosticCode {
        for (DIAGNOSTIC_CATALOG) |descriptor| {
            if (std.mem.eql(u8, descriptor.code_str, code_str)) {
                return descriptor.code;
            }
        }
        return null;
    }
};

/// Static metadata entry in `DIAGNOSTIC_CATALOG` describing a `DiagnosticCode`.
pub const DiagnosticDescriptor = struct {
    /// Strongly typed enum tag.
    code: DiagnosticCode,
    /// Canonical 5-character prefix string (`E00xx`–`E05xx` / `W00xx`–`W05xx`).
    code_str: []const u8,
    /// Default diagnostic severity.
    default_severity: Severity,
    /// Short human-readable category title.
    title: []const u8,
    /// Concise architectural explanation of the condition and remediation.
    explanation: []const u8,
};

/// Structured compiler diagnostic emitted into `DiagnosticSink`.
pub const Diagnostic = struct {
    /// Canonical diagnostic code identifier.
    code: DiagnosticCode,
    /// Severity level (`.err`, `.warning`, `.note`, or `.help`).
    severity: Severity,
    /// Primary focal source span (`Span.ZERO` when not attached to a specific file).
    primary_span: Span = Span.ZERO,
    /// Main diagnostic headline message.
    message: []const u8,
    /// Primary and secondary annotated source spans.
    labels: []const LabeledSpan = &.{},
    /// Supplemental footer notes and `help:` messages.
    notes: []const []const u8 = &.{},
    /// Machine-applicable or heuristic `SuggestedFix` byte replacement bundles.
    suggestions: []const SuggestedFix = &.{},
};

/// Result of applying non-conflicting `SuggestedFix` bundles via `TransactionalPatcher`.
pub const PatchOutcome = struct {
    /// Newly allocated UTF-8 buffer containing the patched source text.
    patched_source: []u8,
    /// Number of `SuggestedFix` bundles transactionally accepted and applied.
    applied_count: u32,
    /// Number of candidate fixes rejected due to bounds, self-overlap, or inter-fix conflict.
    skipped_conflict_count: u32,
};

/// Internal sortable wrapper pairing a `SuggestedFix` with its earliest byte span and original index.
const IndexedFix = struct {
    /// Candidate fix bundle.
    fix: SuggestedFix,
    /// Minimum `start_byte` across all edits in `fix`.
    min_start_byte: u32,
    /// Minimum `end_byte` for the earliest edit in `fix`.
    min_end_byte: u32,
    /// Original index in `candidate_fixes` for deterministic tie-breaking.
    original_index: usize,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Default upper bound on emitted error diagnostics before halting emission (`AGENTS.md` Section 2).
pub const DEFAULT_MAX_ERRORS: u32 = 100;

/// Canonical metadata catalog indexed 1-to-1 by `@intFromEnum(DiagnosticCode)`.
pub const DIAGNOSTIC_CATALOG = [_]DiagnosticDescriptor{
    .{
        .code = .e0001_unknown_cli_flag,
        .code_str = "E0001",
        .default_severity = .err,
        .title = "unknown CLI flag",
        .explanation = "An unrecognized command-line flag or option was provided to `corex`.",
    },
    .{
        .code = .e0002_unknown_cli_subcommand,
        .code_str = "E0002",
        .default_severity = .err,
        .title = "unknown CLI subcommand",
        .explanation = "An unrecognized subcommand was provided to `corex`.",
    },
    .{
        .code = .e0003_missing_cli_argument,
        .code_str = "E0003",
        .default_severity = .err,
        .title = "missing required CLI argument",
        .explanation = "A required command-line argument or flag value was omitted.",
    },
    .{
        .code = .e0004_source_file_io_error,
        .code_str = "E0004",
        .default_severity = .err,
        .title = "source file I/O failure",
        .explanation = "The specified source file could not be opened or read from disk.",
    },
    .{
        .code = .e0005_source_file_size_exceeded,
        .code_str = "E0005",
        .default_severity = .err,
        .title = "source file exceeds maximum size cap",
        .explanation = "A source file exceeded the 64 MiB bounded input limit.",
    },
    .{
        .code = .e0101_invalid_utf8_sequence,
        .code_str = "E0101",
        .default_severity = .err,
        .title = "invalid UTF-8 byte sequence",
        .explanation = "All CoreX `.cx` source files must be encoded in valid UTF-8.",
    },
    .{
        .code = .e0102_unterminated_string_literal,
        .code_str = "E0102",
        .default_severity = .err,
        .title = "unterminated string literal",
        .explanation = "A string or character literal was not closed before end-of-line or EOF.",
    },
    .{
        .code = .e0103_invalid_numeric_literal,
        .code_str = "E0103",
        .default_severity = .err,
        .title = "malformed numeric literal",
        .explanation = "A numeric literal contained invalid digits, radix prefixes, or type suffixes.",
    },
    .{
        .code = .e0104_token_limit_exceeded,
        .code_str = "E0104",
        .default_severity = .err,
        .title = "file token count exceeds maximum cap",
        .explanation = "A source file exceeded the 4,194,304 token resource cap.",
    },
    .{
        .code = .e0201_unexpected_token,
        .code_str = "E0201",
        .default_severity = .err,
        .title = "unexpected syntax token",
        .explanation = "The parser encountered a token that cannot start or continue the current construct.",
    },
    .{
        .code = .e0202_unclosed_delimiter,
        .code_str = "E0202",
        .default_severity = .err,
        .title = "unclosed block or group delimiter",
        .explanation = "An opening `(`, `[`, or `{` delimiter was not closed by its matching delimiter.",
    },
    .{
        .code = .e0203_parse_depth_exceeded,
        .code_str = "E0203",
        .default_severity = .err,
        .title = "parser recursion depth limit exceeded",
        .explanation = "Nested syntax constructs exceeded the bounded parser recursion depth limit.",
    },
    .{
        .code = .e0301_use_after_free,
        .code_str = "E0301",
        .default_severity = .err,
        .title = "use of deallocated memory value",
        .explanation = "MIR SAST detected a read or write to memory after its owning allocation was released.",
    },
    .{
        .code = .e0302_use_after_move,
        .code_str = "E0302",
        .default_severity = .err,
        .title = "use of moved value after ownership transfer",
        .explanation = "A linear or non-copy value was accessed after ownership was transferred to another binding.",
    },
    .{
        .code = .e0303_uninitialized_memory_read,
        .code_str = "E0303",
        .default_severity = .err,
        .title = "read of possibly uninitialized value",
        .explanation = "A binding or struct field was read or moved on a control-flow path before definite initialization.",
    },
    .{
        .code = .e0304_resource_or_memory_leak,
        .code_str = "E0304",
        .default_severity = .err,
        .title = "unconsumed @linear resource or memory leak",
        .explanation = "A `@linear` capability reached scope exit or early return without explicit consumption on all paths.",
    },
    .{
        .code = .e0305_exclusivity_violation,
        .code_str = "E0305",
        .default_severity = .err,
        .title = "mutable aliasing or loan exclusivity violation",
        .explanation = "Overlapping shared (`let`) and mutable (`inout`) accesses conflict on the same storage path.",
    },
    .{
        .code = .e0306_region_escape_violation,
        .code_str = "E0306",
        .default_severity = .err,
        .title = "value escapes lexical arena or stack region",
        .explanation = "A reference or container tied to a local arena or stack frame escaped its lexical scope.",
    },
    .{
        .code = .e0307_static_buffer_overflow,
        .code_str = "E0307",
        .default_severity = .err,
        .title = "compile-time proven out-of-bounds access",
        .explanation = "Pentagon abstract interpretation proved an array or slice index falls outside valid bounds.",
    },
    .{
        .code = .e0313_double_free_or_close,
        .code_str = "E0313",
        .default_severity = .err,
        .title = "double free or duplicate @linear consumption",
        .explanation = "An allocation or `@linear` handle was explicitly released or consumed more than once on a path.",
    },
    .{
        .code = .e0315_wire_layout_contract_violation,
        .code_str = "E0315",
        .default_severity = .err,
        .title = "wire transmutation layout contract violation",
        .explanation = "Type fails `FromBytes` bit-validity or `IntoBytes` padding rules (missing `@zero_pad` or contains pointers).",
    },
    .{
        .code = .e0316_max_stack_budget_exceeded,
        .code_str = "E0316",
        .default_severity = .err,
        .title = "worst-case call stack exceeds @max_stack budget",
        .explanation = "Transitive frame size exceeds `@max_stack(N)` or enters an unbounded recursive call cycle.",
    },
    .{
        .code = .e0320_no_alloc_contract_violation,
        .code_str = "E0320",
        .default_severity = .err,
        .title = "@no_alloc contract violated by heap allocation",
        .explanation = "A `@no_alloc` function or callback transitively invokes a growable heap or backing slab allocator.",
    },
    .{
        .code = .e0321_no_panic_contract_violation,
        .code_str = "E0321",
        .default_severity = .err,
        .title = "@no_panic contract violated by residual trap path",
        .explanation = "A `@no_panic` function retains an un-elided bounds, division, overflow, narrow, or explicit panic path.",
    },
    .{
        .code = .e0322_no_block_contract_violation,
        .code_str = "E0322",
        .default_severity = .err,
        .title = "@no_block contract violated by blocking operation",
        .explanation = "A `@no_block` function transitively acquires OS locks, sleeps, frees global heap memory, or blocks on I/O.",
    },
    .{
        .code = .e0323_trait_impl_effect_escalation,
        .code_str = "E0323",
        .default_severity = .err,
        .title = "trait implementation escalates method contract",
        .explanation = "An `impl` method violates `@no_alloc`, `@no_panic`, or `@no_block` declared on the trait method signature.",
    },
    .{
        .code = .e0324_package_capability_violation,
        .code_str = "E0324",
        .default_severity = .err,
        .title = "package exceeds authorized capability policy",
        .explanation = "Inferred package capabilities exceed `corex.toml` `allow_caps`/`deny_caps` or escalate past `corex.lock`.",
    },
    .{
        .code = .e0325_comptime_sandbox_violation,
        .code_str = "E0325",
        .default_severity = .err,
        .title = "forbidden capability in hermetic comptime context",
        .explanation = "A `comptime`, `const`, or `@derive` body transitively reaches host I/O, FFI, `unsafe`, clock, or entropy.",
    },
    .{
        .code = .e0326_embed_path_escape,
        .code_str = "E0326",
        .default_severity = .err,
        .title = "@embed_bytes path escapes package sandbox root",
        .explanation = "An `@embed_bytes` path is absolute, traverses `..` outside package root, or targets a symlink/non-regular file.",
    },
    .{
        .code = .e0327_forbidden_sandbox_bypass_attribute,
        .code_str = "E0327",
        .default_severity = .err,
        .title = "forbidden linker section or sandbox bypass attribute",
        .explanation = "Attribute targets a pre-main loader/TLS/interpose section or uses `@std_cap_boundary` outside `std`.",
    },
    .{
        .code = .e0328_scratch_arena_ping_pong_conflict,
        .code_str = "E0328",
        .default_severity = .err,
        .title = "scratch arena rewind aliases caller output arena",
        .explanation = "Callee rewinds `Context.scratch[i]` while caller holds an active mutable loan on `Context.scratch[i]`.",
    },
    .{
        .code = .e0400_ambiguous_overload,
        .code_str = "E0400",
        .default_severity = .err,
        .title = "ambiguous overload call",
        .explanation = "Multiple candidate functions in the explicit overload group match the argument types equally.",
    },
    .{
        .code = .e0401_type_mismatch,
        .code_str = "E0401",
        .default_severity = .err,
        .title = "mismatched types in expression",
        .explanation = "An expression's inferred type did not match the expected type constraint.",
    },
    .{
        .code = .e0402_unsatisfied_trait_bound,
        .code_str = "E0402",
        .default_severity = .err,
        .title = "type does not satisfy constrained trait bound",
        .explanation = "A type argument did not implement the required trait or constrained type group.",
    },
    .{
        .code = .e0403_unresolved_symbol,
        .code_str = "E0403",
        .default_severity = .err,
        .title = "unresolved identifier or symbol in scope",
        .explanation = "The referenced variable, function, type, or module name is not bound in scope.",
    },
    .{
        .code = .e0404_bind_once_group_conflict,
        .code_str = "E0404",
        .default_severity = .err,
        .title = "conflicting types for bind-once type group",
        .explanation = "A bare Constrained Type Group parameter binds once across the signature; use `any Group` for independent types.",
    },
    .{
        .code = .e0405_distinct_type_mixing,
        .code_str = "E0405",
        .default_severity = .err,
        .title = "cannot mix distinct nominal type with underlying type",
        .explanation = "A `distinct` nominal type does not implicitly coerce to or from its underlying type without `as` or `~T`.",
    },
    .{
        .code = .e0406_range_refinement_violation,
        .code_str = "E0406",
        .default_severity = .err,
        .title = "compile-time value outside range refinement or integer bounds",
        .explanation = "The evaluated constant, literal, or bit-field width falls outside the target type's valid bounds.",
    },
    .{
        .code = .e0407_invalid_contextual_variant,
        .code_str = "E0407",
        .default_severity = .err,
        .title = "cannot infer contextual variant",
        .explanation = "Contextual `.Variant` syntax requires a known target `enum`, `Option[T]`, or `Result[T, E]` expected type.",
    },
    .{
        .code = .e0408_duplicate_definition,
        .code_str = "E0408",
        .default_severity = .err,
        .title = "duplicate symbol definition in scope",
        .explanation = "A symbol with this name is already defined in the same namespace within the current scope.",
    },
    .{
        .code = .e0409_private_symbol_access,
        .code_str = "E0409",
        .default_severity = .err,
        .title = "symbol or member is private",
        .explanation = "Items, struct fields, and methods without `pub` cannot be accessed outside their defining module.",
    },
    .{
        .code = .e0410_try_outside_fallible_fn,
        .code_str = "E0410",
        .default_severity = .err,
        .title = "cannot use `?` operator outside fallible function",
        .explanation = "Postfix `?` propagates `.Err` or `.None` and requires an enclosing `Result[T, E]` or `Option[T]` return type.",
    },
    .{
        .code = .e0411_missing_from_error_conversion,
        .code_str = "E0411",
        .default_severity = .err,
        .title = "cannot convert propagated error type via `?`",
        .explanation = "The enclosing error type does not match the inner error type and lacks `FromError` or `@from` upcasting.",
    },
    .{
        .code = .e0412_let_else_not_diverging,
        .code_str = "E0412",
        .default_severity = .err,
        .title = "let-else guard block must diverge",
        .explanation = "The `else` block of a `let Pattern = expr else { … }` guard must unconditionally diverge (`never`).",
    },
    .{
        .code = .e0413_unhandled_must_use_or_result,
        .code_str = "E0413",
        .default_severity = .err,
        .title = "unhandled Result or @must_use return value",
        .explanation = "Fallible `Result[T, E]` and `@must_use` values cannot be silently ignored in an expression statement.",
    },
    .{
        .code = .e0414_bare_wildcard_result_discard,
        .code_str = "E0414",
        .default_severity = .err,
        .title = "cannot discard Result with bare let _ =",
        .explanation = "Discarding a `Result[T, E]` via bare `let _ = fallible()` is forbidden; use `let _ = fallible() catch {}`.",
    },
    .{
        .code = .e0415_non_exhaustive_match,
        .code_str = "E0415",
        .default_severity = .err,
        .title = "non-exhaustive match patterns",
        .explanation = "The `match` arms do not cover every possible value of the scrutinee type.",
    },
    .{
        .code = .e0501_comptime_step_limit_exceeded,
        .code_str = "E0501",
        .default_severity = .err,
        .title = "compile-time execution exceeded step budget",
        .explanation = "A `comptime` evaluation in `MirVm` exceeded the maximum instruction fuel budget.",
    },
    .{
        .code = .e0502_integer_constant_overflow,
        .code_str = "E0502",
        .default_severity = .err,
        .title = "compile-time integer arithmetic overflow",
        .explanation = "A constant folding or `comptime` integer operation overflowed its target bit width.",
    },
    .{
        .code = .e0503_forbidden_comptime_operation,
        .code_str = "E0503",
        .default_severity = .err,
        .title = "forbidden operation in comptime context",
        .explanation = "Compile-time evaluation forbids I/O, FFI calls, non-determinism, and raw pointer-to-integer casts.",
    },
    .{
        .code = .e0504_comptime_out_of_bounds,
        .code_str = "E0504",
        .default_severity = .err,
        .title = "compile-time memory access out of bounds",
        .explanation = "A `comptime` array, slice, or virtual allocation access fell outside its allocated bounds.",
    },
    .{
        .code = .e0505_comptime_uninitialized_read,
        .code_str = "E0505",
        .default_severity = .err,
        .title = "compile-time read of uninitialized memory",
        .explanation = "A `comptime` load read from bytes whose shadow initialization bitmap was unset.",
    },
    .{
        .code = .e0506_comptime_invalid_pointer,
        .code_str = "E0506",
        .default_severity = .err,
        .title = "compile-time invalid or dangling pointer",
        .explanation = "A `comptime` dereference used a null, misaligned, or deallocated virtual allocation pointer.",
    },
    .{
        .code = .e0507_comptime_arithmetic_trap,
        .code_str = "E0507",
        .default_severity = .err,
        .title = "compile-time arithmetic trap",
        .explanation = "A `comptime` division by zero, remainder by zero, or invalid shift count occurred.",
    },
    .{
        .code = .e0508_comptime_resource_limit_exceeded,
        .code_str = "E0508",
        .default_severity = .err,
        .title = "compile-time resource limit exceeded",
        .explanation = "A `comptime` evaluation exceeded the virtual heap, call depth, unroll, or `@embed_bytes` cap.",
    },
    .{
        .code = .e0509_comptime_evaluation_cycle,
        .code_str = "E0509",
        .default_severity = .err,
        .title = "compile-time evaluation cycle detected",
        .explanation = "A `const` item or `comptime` query recursively depended on its own value before completion.",
    },
    .{
        .code = .e0510_compile_assertion_failed,
        .code_str = "E0510",
        .default_severity = .err,
        .title = "compile-time assertion or error triggered",
        .explanation = "An explicit `@compile_assert` condition evaluated to `false` or `@compile_error` was reached.",
    },
    .{
        .code = .w0001_deprecated_cli_option,
        .code_str = "W0001",
        .default_severity = .warning,
        .title = "deprecated CLI option",
        .explanation = "A deprecated command-line flag was used; prefer the canonical replacement flag.",
    },
    .{
        .code = .w0101_redundant_escape_sequence,
        .code_str = "W0101",
        .default_severity = .warning,
        .title = "redundant character escape sequence",
        .explanation = "A string or character literal used an unnecessary backslash escape.",
    },
    .{
        .code = .w0201_non_canonical_identifier_case,
        .code_str = "W0201",
        .default_severity = .warning,
        .title = "identifier does not follow canonical casing",
        .explanation = "Types must use `PascalCase`, functions/variables `snake_case`, and constants `SCREAMING_SNAKE_CASE`.",
    },
    .{
        .code = .w0308_unused_region_allocation,
        .code_str = "W0308",
        .default_severity = .warning,
        .title = "unused region or linear capability",
        .explanation = "A lexical arena or region capability was declared but never used for allocation.",
    },
    .{
        .code = .w0314_unproven_bounds_access,
        .code_str = "W0314",
        .default_severity = .warning,
        .title = "slice or array bounds not statically proven",
        .explanation = "Under `--sast-strict`, Pentagon abstract interpretation could not statically discharge this bounds check.",
    },
    .{
        .code = .w0329_vacated_projection_panic_abort,
        .code_str = "W0329",
        .default_severity = .warning,
        .title = "panic inside vacated non-Copy projection aborts",
        .explanation = "Un-elided panic inside an `inout` subscript `yield` of a non-`Copy` slot inserts an immediate abort guard.",
    },
    .{
        .code = .w0330_ambient_dead_capability_in_dep,
        .code_str = "W0330",
        .default_severity = .warning,
        .title = "unreachable high-risk capability in dependency",
        .explanation = "Dependency exports dead/unreachable functions carrying `net`, `process`, or `ffi` capabilities.",
    },
    .{
        .code = .w0401_unreachable_pattern_arm,
        .code_str = "W0401",
        .default_severity = .warning,
        .title = "unreachable match pattern arm",
        .explanation = "A `match` arm is completely subsumed by preceding patterns and can never execute.",
    },
    .{
        .code = .w0402_unused_binding,
        .code_str = "W0402",
        .default_severity = .warning,
        .title = "unused local binding or parameter",
        .explanation = "A local variable or function parameter is never read; prefix with `_` if intentionally unused.",
    },
    .{
        .code = .w0501_inlining_budget_exceeded,
        .code_str = "W0501",
        .default_severity = .warning,
        .title = "function exceeds inlining cost threshold",
        .explanation = "A function marked for inlining exceeded the MIR instruction size threshold.",
    },
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if at least one edit in `edits` targets `file_id`.
fn hasTargetFileId(edits: []const TextEdit, file_id: FileId) bool {
    for (edits) |edit_item| {
        if (edit_item.file_id == file_id) return true;
    }
    return false;
}

/// Validates that all edits in `edits` target `file_id`, lie within `source_len`, and have zero self-overlap.
fn isFixValidAndDisjoint(
    edits: []const TextEdit,
    file_id: FileId,
    source_len: usize,
    interner_count: usize,
) bool {
    for (edits) |edit_item| {
        if (edit_item.file_id != file_id) return false;
        if (edit_item.replacement_id.isNone() or edit_item.replacement_id.asInt() >= interner_count) {
            return false;
        }
        if (edit_item.start_byte > edit_item.end_byte) return false;
        if (edit_item.end_byte > source_len) return false;
    }
    for (edits, 0..) |first_edit, i| {
        var j: usize = i + 1;
        while (j < edits.len) : (j += 1) {
            if (TransactionalPatcher.hasEditConflict(first_edit, edits[j])) {
                return false;
            }
        }
    }
    return true;
}

/// Strict total ordering comparator for `IndexedFix` (`priority ASC, min_start_byte ASC, min_end_byte ASC`).
fn compareIndexedFixes(_: void, lhs_fix: IndexedFix, rhs_fix: IndexedFix) bool {
    if (@backingInt(lhs_fix.fix.priority) != @backingInt(rhs_fix.fix.priority)) {
        return @backingInt(lhs_fix.fix.priority) < @backingInt(rhs_fix.fix.priority);
    }
    if (lhs_fix.min_start_byte != rhs_fix.min_start_byte) {
        return lhs_fix.min_start_byte < rhs_fix.min_start_byte;
    }
    if (lhs_fix.min_end_byte != rhs_fix.min_end_byte) {
        return lhs_fix.min_end_byte < rhs_fix.min_end_byte;
    }
    return lhs_fix.original_index < rhs_fix.original_index;
}

/// Comparator sorting `TextEdit` records in ascending byte offset order.
fn compareEditsByOffset(_: void, first_edit: TextEdit, second_edit: TextEdit) bool {
    if (first_edit.start_byte != second_edit.start_byte) {
        return first_edit.start_byte < second_edit.start_byte;
    }
    return first_edit.end_byte < second_edit.end_byte;
}

comptime {
    std.debug.assert(@sizeOf(TextEdit) == 16);
    std.debug.assert(@alignOf(TextEdit) == 4);
    for (DIAGNOSTIC_CATALOG, 0..) |descriptor, i| {
        std.debug.assert(@backingInt(descriptor.code) == i);
        std.debug.assert(descriptor.code_str.len == 5);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Arena-backed diagnostic collector enforcing the bounded 100-error emission cap.
pub const DiagnosticSink = struct {
    /// Dedicated bump arena owning all cloned diagnostic strings and slices.
    arena: BumpArena,
    /// Contiguous list of emitted diagnostics in emission order.
    diagnostics: std.ArrayList(Diagnostic) = .empty,
    /// Total number of `.err` diagnostics accepted into `diagnostics`.
    error_count: u32 = 0,
    /// Total number of `.warning` diagnostics accepted into `diagnostics`.
    warning_count: u32 = 0,
    /// Maximum number of `.err` diagnostics permitted before halting error emission.
    max_errors: u32 = DEFAULT_MAX_ERRORS,
    /// Set to `true` once `error_count` reaches `max_errors`.
    has_reached_limit: bool = false,

    /// Initializes a `DiagnosticSink` with the default 100-error cap.
    pub fn init(backing_allocator: std.mem.Allocator) DiagnosticSink {
        return .{
            .arena = BumpArena.init(backing_allocator),
            .max_errors = DEFAULT_MAX_ERRORS,
        };
    }

    /// Initializes a `DiagnosticSink` with a custom `max_errors` cap.
    pub fn initWithLimit(backing_allocator: std.mem.Allocator, max_errors: u32) DiagnosticSink {
        return .{
            .arena = BumpArena.init(backing_allocator),
            .max_errors = max_errors,
        };
    }

    /// Releases all arena-allocated diagnostic payloads and internal storage.
    pub fn deinit(self: *DiagnosticSink) void {
        self.diagnostics.deinit(self.arena.asAllocator());
        self.arena.deinit();
    }

    /// Clones `diagnostic` into the sink's arena and records it if below `max_errors`.
    pub fn emit(self: *DiagnosticSink, diagnostic: Diagnostic) !void {
        if (diagnostic.severity == .err) {
            if (self.error_count >= self.max_errors) {
                self.has_reached_limit = true;
                return;
            }
            self.error_count += 1;
            if (self.error_count >= self.max_errors) {
                self.has_reached_limit = true;
            }
        } else if (diagnostic.severity == .warning) {
            self.warning_count += 1;
        }

        // [1] Clone message and labeled spans into the sink's bump arena:
        const cloned_labels = try self.arena.allocSlice(LabeledSpan, diagnostic.labels.len);
        for (diagnostic.labels, 0..) |label_item, i| {
            cloned_labels[i] = .{
                .span = label_item.span,
                .label = try self.arena.dupe(u8, label_item.label),
                .style = label_item.style,
            };
        }

        // [2] Clone footer notes into the sink's bump arena:
        const cloned_notes = try self.arena.allocSlice([]const u8, diagnostic.notes.len);
        for (diagnostic.notes, 0..) |note_text, i| {
            cloned_notes[i] = try self.arena.dupe(u8, note_text);
        }

        // [3] Clone suggested fixes and their `TextEdit` slices into the sink's bump arena:
        const cloned_suggestions = try self.arena.allocSlice(SuggestedFix, diagnostic.suggestions.len);
        for (diagnostic.suggestions, 0..) |suggestion_item, i| {
            cloned_suggestions[i] = .{
                .message = try self.arena.dupe(u8, suggestion_item.message),
                .applicability = suggestion_item.applicability,
                .priority = suggestion_item.priority,
                .edits = try self.arena.dupe(TextEdit, suggestion_item.edits),
            };
        }

        try self.diagnostics.append(self.arena.asAllocator(), .{
            .code = diagnostic.code,
            .severity = diagnostic.severity,
            .primary_span = diagnostic.primary_span,
            .message = try self.arena.dupe(u8, diagnostic.message),
            .labels = cloned_labels,
            .notes = cloned_notes,
            .suggestions = cloned_suggestions,
        });
    }

    /// Returns `true` if at least one error diagnostic has been emitted.
    pub inline fn hasErrors(self: *const DiagnosticSink) bool {
        return self.error_count > 0;
    }

    /// Returns the total number of stored diagnostics.
    pub inline fn countDiagnostics(self: *const DiagnosticSink) usize {
        return self.diagnostics.items.len;
    }

    /// Returns a read-only slice of all emitted diagnostics.
    pub inline fn asSlice(self: *const DiagnosticSink) []const Diagnostic {
        return self.diagnostics.items;
    }
};

/// Conflict-free priority interval scheduler and single-pass byte patcher (`DR-14` Section 2.5).
pub const TransactionalPatcher = struct {
    /// Returns `true` if `first_edit` and `second_edit` overlap or touch at a zero-width boundary.
    pub fn hasEditConflict(first_edit: TextEdit, second_edit: TextEdit) bool {
        if (first_edit.file_id != second_edit.file_id) return false;
        if (first_edit.start_byte > first_edit.end_byte or second_edit.start_byte > second_edit.end_byte) {
            return true;
        }

        const is_first_earlier = first_edit.start_byte < second_edit.start_byte or
            (first_edit.start_byte == second_edit.start_byte and first_edit.end_byte <= second_edit.end_byte);
        const early_edit = if (is_first_earlier) first_edit else second_edit;
        const late_edit = if (is_first_earlier) second_edit else first_edit;

        if (late_edit.start_byte < early_edit.end_byte) return true;
        if (late_edit.start_byte == early_edit.end_byte and
            (early_edit.countBytes() == 0 or late_edit.countBytes() == 0))
        {
            return true;
        }
        return false;
    }

    /// Validates, schedules, and splices all disjoint `.machine_applicable` fixes targeting `file_id`.
    pub fn apply(
        allocator: std.mem.Allocator,
        source: []const u8,
        file_id: FileId,
        candidate_fixes: []const SuggestedFix,
        interner: *const StringInterner,
    ) !PatchOutcome {
        // [1] Filter and validate candidate fixes (checking bounds and intra-fix self-overlap):
        var valid_candidates: std.ArrayList(IndexedFix) = .empty;
        defer valid_candidates.deinit(allocator);
        var skipped_conflict_count: u32 = 0;
        const interner_count = interner.countStrings();

        for (candidate_fixes, 0..) |candidate_fix, i| {
            if (candidate_fix.applicability != .machine_applicable or candidate_fix.edits.len == 0) {
                continue;
            }
            if (!hasTargetFileId(candidate_fix.edits, file_id)) {
                continue;
            }
            if (!isFixValidAndDisjoint(candidate_fix.edits, file_id, source.len, interner_count)) {
                skipped_conflict_count += 1;
                continue;
            }
            var min_start: u32 = std.math.maxInt(u32);
            var min_end: u32 = std.math.maxInt(u32);
            for (candidate_fix.edits) |edit_item| {
                if (edit_item.start_byte < min_start or
                    (edit_item.start_byte == min_start and edit_item.end_byte < min_end))
                {
                    min_start = edit_item.start_byte;
                    min_end = edit_item.end_byte;
                }
            }
            try valid_candidates.append(allocator, .{
                .fix = candidate_fix,
                .min_start_byte = min_start,
                .min_end_byte = min_end,
                .original_index = i,
            });
        }

        if (valid_candidates.items.len == 0) {
            return .{
                .patched_source = try allocator.dupe(u8, source),
                .applied_count = 0,
                .skipped_conflict_count = skipped_conflict_count,
            };
        }

        // [2] Sort valid candidate fixes by `(priority ASC, min_start_byte ASC, min_end_byte ASC)`:
        std.mem.sort(IndexedFix, valid_candidates.items, {}, compareIndexedFixes);

        // [3] Greedily accept fixes whose edits are mutually disjoint from all accepted edits:
        var accepted_edits: std.ArrayList(TextEdit) = .empty;
        defer accepted_edits.deinit(allocator);
        var applied_count: u32 = 0;

        for (valid_candidates.items) |indexed_candidate| {
            var has_inter_conflict = false;
            for (indexed_candidate.fix.edits) |cand_edit| {
                for (accepted_edits.items) |existing_edit| {
                    if (hasEditConflict(cand_edit, existing_edit)) {
                        has_inter_conflict = true;
                        break;
                    }
                }
                if (has_inter_conflict) break;
            }
            if (has_inter_conflict) {
                skipped_conflict_count += 1;
                continue;
            }
            try accepted_edits.appendSlice(allocator, indexed_candidate.fix.edits);
            applied_count += 1;
        }

        if (accepted_edits.items.len == 0) {
            return .{
                .patched_source = try allocator.dupe(u8, source),
                .applied_count = 0,
                .skipped_conflict_count = skipped_conflict_count,
            };
        }

        // [4] Sort accepted edits by `(start_byte ASC, end_byte ASC)` and compute output byte length:
        std.mem.sort(TextEdit, accepted_edits.items, {}, compareEditsByOffset);

        var output_byte_len: usize = source.len;
        for (accepted_edits.items) |edit_item| {
            output_byte_len -= edit_item.countBytes();
            output_byte_len = try std.math.add(usize, output_byte_len, interner.get(edit_item.replacement_id).len);
        }

        // [5] Allocate target buffer once and splice source slices with replacement text in O(N + M):
        const patched_source = try allocator.alloc(u8, output_byte_len);
        var source_cursor: usize = 0;
        var dest_cursor: usize = 0;

        for (accepted_edits.items) |edit_item| {
            const edit_start: usize = edit_item.start_byte;
            if (edit_start > source_cursor) {
                const unchanged_len = edit_start - source_cursor;
                @memcpy(patched_source[dest_cursor .. dest_cursor + unchanged_len], source[source_cursor..edit_start]);
                dest_cursor += unchanged_len;
            }
            const replacement_text = interner.get(edit_item.replacement_id);
            if (replacement_text.len > 0) {
                @memcpy(patched_source[dest_cursor .. dest_cursor + replacement_text.len], replacement_text);
                dest_cursor += replacement_text.len;
            }
            source_cursor = edit_item.end_byte;
        }
        if (source_cursor < source.len) {
            const tail_len = source.len - source_cursor;
            @memcpy(patched_source[dest_cursor .. dest_cursor + tail_len], source[source_cursor..]);
            dest_cursor += tail_len;
        }
        std.debug.assert(dest_cursor == output_byte_len);

        return .{
            .patched_source = patched_source,
            .applied_count = applied_count,
            .skipped_conflict_count = skipped_conflict_count,
        };
    }
};

comptime {
    std.debug.assert(@typeInfo(DiagnosticCode).@"enum".field_names.len == DIAGNOSTIC_CATALOG.len);
    for (DIAGNOSTIC_CATALOG, 0..) |entry, i| {
        std.debug.assert(@backingInt(entry.code) == i);
    }
}

test "test_diagnostic_sink_error_cap_and_patcher" {
    var sink = DiagnosticSink.initWithLimit(std.testing.allocator, 2);
    defer sink.deinit();

    try sink.emit(.{
        .code = .e0302_use_after_move,
        .severity = .err,
        .message = "first error",
    });
    try sink.emit(.{
        .code = .e0302_use_after_move,
        .severity = .err,
        .message = "second error",
    });
    try sink.emit(.{
        .code = .e0302_use_after_move,
        .severity = .err,
        .message = "third error dropped",
    });
    try std.testing.expectEqual(@as(u32, 2), sink.error_count);
    try std.testing.expectEqual(@as(usize, 2), sink.countDiagnostics());
    try std.testing.expect(sink.has_reached_limit);

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    const file_id = FileId.fromInt(0);
    const outcome = try TransactionalPatcher.apply(
        std.testing.allocator,
        "call(socket);",
        file_id,
        &.{.{
            .message = "borrow socket",
            .applicability = .machine_applicable,
            .priority = .memory_safety,
            .edits = &.{.{
                .file_id = file_id,
                .start_byte = 5,
                .end_byte = 11,
                .replacement_id = try interner.intern("&socket"),
            }},
        }},
        &interner,
    );
    defer std.testing.allocator.free(outcome.patched_source);
    try std.testing.expectEqual(@as(u32, 1), outcome.applied_count);
    try std.testing.expectEqualStrings("call(&socket);", outcome.patched_source);
}

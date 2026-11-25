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
    /// Invalid or unsupported compilation `--target` triple (`E0006`).
    e0006_invalid_target_triple = 5,
    /// Backend code generation or IR lowering failure (`E0007`).
    e0007_codegen_backend_failure = 6,
    /// External compiler driver or linker invocation failure (`E0008`).
    e0008_linker_invocation_failed = 7,
    /// C11/C23 header preprocessing, parsing, or `@c_import` / `translate-c` translation failure (`E0009`).
    e0009_c_header_translation_failed = 8,
    /// Unsatisfiable SemVer, feature, or `[resolution].exclude` package dependency graph (`E0010`).
    e0010_unsatisfiable_dependency_graph = 9,
    /// Two or more resolved packages declare the same native C `links` library key (`E0011`).
    e0011_native_links_collision = 10,
    /// Nominal `.cxi` type mismatch across coexisting major versions of the same package (`E0012`).
    e0012_cross_major_cxi_type_mismatch = 11,
    /// Malformed `corex.toml` manifest, script frontmatter, or non-canonical package/alias name (`E0013`).
    e0013_invalid_manifest_or_pkg_name = 12,
    /// Missing, drifted, or corrupt `corex.lock` under `--locked` or `--frozen` (`E0014`).
    e0014_lockfile_drift_or_corrupt = 13,
    /// Content-addressable cache BLAKE3, Bao, Ed25519, or RFC 6962 transparency-log mismatch (`E0015`).
    e0015_cache_integrity_mismatch = 14,
    /// Package fetch failure or missing cached artifact under `--offline` / `COREX_HERMETIC=1` (`E0016`).
    e0016_offline_or_fetch_failed = 15,
    /// Stray standalone `.corex-lint.toml` or `.corexfmt.toml` dotfile (`E0017`).
    e0017_stray_tool_config_dotfile = 16,
    /// Forbidden style-fragmenting or severity-remapping key in `corex.toml` (`E0018`).
    e0018_forbidden_tool_config_key = 17,
    /// Unknown lint rule code/slug or malformed path glob in `corex.toml` or CLI flags (`E0019`).
    e0019_invalid_lint_rule_or_glob = 18,
    /// Out-of-range `[lint.settings]` or `[lsp]` configuration value (`E0020`).
    e0020_tool_setting_out_of_range = 19,

    // E01xx; Lexical Scanning, UTF-8 & Literal Rules:
    /// Invalid UTF-8 byte sequence in source file (`E0101`).
    e0101_invalid_utf8_sequence = 20,
    /// Unterminated string or character literal (`E0102`).
    e0102_unterminated_string_literal = 21,
    /// Malformed numeric literal or invalid digit separator (`E0103`).
    e0103_invalid_numeric_literal = 22,
    /// File token count exceeds `MAX_TOKENS_PER_FILE` (`E0104`).
    e0104_token_limit_exceeded = 23,
    /// Retired `::` path separator (`E0112`).
    e0112_retired_path_separator = 24,
    /// Retired `&&` logical AND operator (`E0113`).
    e0113_retired_logical_and = 25,
    /// Unmatched `}` or invalid brace escape in interpolated `f"…"` string (`E0114`).
    e0114_invalid_brace_escape = 26,
    /// Retired `"""` delimiter or non-whitespace before closing `"` on multiline string (`E0115`).
    e0115_multiline_string_opening = 27,
    /// Under-indented multiline string content line or forbidden hard `\t` tab (`E0116`).
    e0116_multiline_string_indent = 28,
    /// Non-ASCII byte (`> 0x7F`) in `b'…'` or `b"…"` byte literal (`E0117`).
    e0117_non_ascii_byte_literal = 29,
    /// Retired block comment (`/* … */`) or 3-character doc prefix (`//!`, `///`) (`E0118`).
    e0118_block_doc_comment_forbidden = 30,

    // E02xx; Syntax Parsing, Recovery & Casing:
    /// Unexpected token in grammar production (`E0201`).
    e0201_unexpected_token = 31,
    /// Unclosed block, group, or generic delimiter (`E0202`).
    e0202_unclosed_delimiter = 32,
    /// Parser recursion depth exceeded `MAX_PARSE_DEPTH` (`E0203`).
    e0203_parse_depth_exceeded = 33,
    /// Invalid pattern binding inside a negated, disjunctive, or non-condition `is` test (`E0214`).
    e0214_invalid_condition_binding = 34,
    /// Condition `:=` binding outside a parenthesized positive `if`/`while` header (`E0215`).
    e0215_invalid_walrus_position = 35,
    /// Retired `if let` or `while let` conditional destructuring syntax (`E0216`).
    e0216_retired_if_while_let = 36,
    /// Direct `core` kernel import or path outside `--internal-core` (`E0218`).
    e0218_direct_core_import_forbidden = 37,
    /// Retired infix `||` logical OR operator (`E0219`).
    e0219_retired_logical_or = 38,
    /// Retired prefix `!` negation operator (`E0220`).
    e0220_retired_bang_prefix = 39,
    /// Retired local mutability or parameter mode spelling (`E0221`).
    e0221_retired_mutability_or_param_mode = 40,
    /// Non-associative chained `A!B!C` result type (`E0222`).
    e0222_chained_result_type = 41,
    /// Retired `=` key-value separator inside `@attribute(…)` (`E0223`).
    e0223_retired_attribute_eq = 42,
    /// Retired `;` member separator in `struct`, `union`, `enum`, or `bit_field` (`E0224`).
    e0224_retired_semicolon_member_sep = 43,
    /// Retired `@noalloc` attribute spelling (`E0225`).
    e0225_retired_noalloc_attribute = 44,
    /// Retired `*const T` raw pointer syntax (`E0226`).
    e0226_retired_const_raw_ptr = 45,
    /// Retired prefix `*ptr` dereference syntax (`E0227`).
    e0227_retired_prefix_deref = 46,
    /// Invalid `/` positional-only or `*` keyword-only parameter zone separator (`E0228`).
    e0228_invalid_param_zone_separator = 47,
    /// Misplaced `/#` module docstring outside top-of-file header (`E0229`).
    e0229_misplaced_module_doc_comment = 48,
    /// Unattached `/|` outer docstring not preceding a documentable declaration (`E0230`).
    e0230_unattached_doc_comment = 49,
    /// Redundant visibility modifier on `impl` block (`E0231`).
    e0231_visibility_on_impl_block = 50,
    /// Inline `fn` or `subscript` inside `struct`, `union`, `bit_field`, or `enum` body (`E0232`).
    e0232_inline_method_in_type_decl = 51,
    /// Invalid single-token `elif`, `elsif`, or `elseif` conditional keyword (`E0233`).
    e0233_invalid_elif_keyword = 52,
    /// Retired non-binding `let _ = …;` or `var _ = …;` wildcard declaration (`E0234`).
    e0234_non_binding_wildcard_let_var = 53,
    /// Destructuring assignment where every target leaf is `_` or `..` (`E0235`).
    e0235_all_wildcard_destructuring_assign = 54,
    /// Missing `:` separator before type annotation (`E0236`).
    e0236_missing_colon_before_type = 55,
    /// Inline `if cond => expr` missing mandatory `else expr` branch (`E0237`).
    e0237_inline_if_missing_else = 56,
    /// Mixed `=>` and `{ … }` block branches in `if` expression (`E0238`).
    e0238_mixed_if_arrow_and_block = 57,
    /// Retired standalone layout/linkage attribute or `@[…]`/`@(…)` wrapper (`E0239`).
    e0239_retired_layout_or_link_attribute = 58,
    /// Invalid, empty, category-wide, or non-suppressible lint rule selector (`E0240`).
    e0240_invalid_suppression_selector = 59,

    // E03xx; MIR SAST Memory, Ownership, Capabilities & Exclusivity:
    /// Use of deallocated or freed value (`E0301`).
    e0301_use_after_free = 60,
    /// Use of moved value after ownership transfer (`E0302`).
    e0302_use_after_move = 61,
    /// Read of possibly uninitialized memory or binding (`E0303`).
    e0303_uninitialized_memory_read = 62,
    /// Unconsumed `@linear` resource or memory leak (`E0304`).
    e0304_resource_or_memory_leak = 63,
    /// Mutable aliasing or MVS loan exclusivity violation (`E0305`).
    e0305_exclusivity_violation = 64,
    /// Value escapes lexical arena or stack region (`E0306`).
    e0306_region_escape_violation = 65,
    /// Compile-time proven out-of-bounds buffer access (`E0307`).
    e0307_static_buffer_overflow = 66,
    /// Non-NUL-terminated `str` or slice passed to `@null_terminated` C FFI parameter (`E0308`).
    e0308_unterminated_cstr_ffi = 67,
    /// Concurrent mutable aliasing, `@thread_local` capture, or borrow escape across `TaskGroup`/`async` (`E0309`).
    e0309_concurrent_exclusivity_or_escape = 68,
    /// `@owned_by_caller @free_with(fn)` FFI pointer released with mismatched deallocator (`E0310`).
    e0310_mismatched_ffi_deallocator = 69,
    /// Unchecked dereference or `@non_null` use of `@may_be_null` FFI pointer (`E0311`).
    e0311_unchecked_nullable_ffi_ptr = 70,
    /// Raw pointer and length passed to `@slice_len` / `@byte_len` FFI without proven capacity (`E0312`).
    e0312_unproven_ffi_slice_len = 71,
    /// Double free or duplicate `@linear` resource consumption (`E0313`).
    e0313_double_free_or_close = 72,
    /// `FromBytes` / `IntoBytes` wire layout contract violation (`E0315`).
    e0315_wire_layout_contract_violation = 73,
    /// Worst-case call stack exceeds `@max_stack` budget (`E0316`).
    e0316_max_stack_budget_exceeded = 74,
    /// Inline `async` state-machine frame subtree exceeds `16 KiB` cap or recurses unboxed (`E0317`).
    e0317_async_inline_frame_exceeded = 75,
    /// `@no_alloc` contract violated by heap allocation (`E0320`).
    e0320_no_alloc_contract_violation = 76,
    /// `@no_panic` contract violated by residual trap path (`E0321`).
    e0321_no_panic_contract_violation = 77,
    /// `@no_block` contract violated by blocking operation (`E0322`).
    e0322_no_block_contract_violation = 78,
    /// Trait `impl` method escalates signature contract (`E0323`).
    e0323_trait_impl_effect_escalation = 79,
    /// Package exceeds authorized capability policy (`E0324`).
    e0324_package_capability_violation = 80,
    /// Forbidden capability in hermetic `comptime` context (`E0325`).
    e0325_comptime_sandbox_violation = 81,
    /// `@embed_bytes` path escapes package sandbox root (`E0326`).
    e0326_embed_path_escape = 82,
    /// Forbidden linker section or sandbox bypass attribute (`E0327`).
    e0327_forbidden_sandbox_bypass_attribute = 83,
    /// Scratch arena rewind aliases caller output arena (`E0328`).
    e0328_scratch_arena_ping_pong_conflict = 84,

    // E04xx; Type System, Inference, Traits, Bounds & Error Semantics:
    /// Ambiguous overload call in explicit overload group (`E0400`).
    e0400_ambiguous_overload = 85,
    /// Mismatched types between expected and found expressions (`E0401`).
    e0401_type_mismatch = 86,
    /// Type does not satisfy constrained trait or type group bound (`E0402`).
    e0402_unsatisfied_trait_bound = 87,
    /// Unresolved identifier or symbol in scope (`E0403`).
    e0403_unresolved_symbol = 88,
    /// Conflicting concrete types for a Bind-Once Constrained Type Group (`E0404`).
    e0404_bind_once_group_conflict = 89,
    /// Distinct nominal type mixed with underlying representation without `as` or `~T` (`E0405`).
    e0405_distinct_type_mixing = 90,
    /// Compile-time value or width violates range refinement or bit-field bounds (`E0406`).
    e0406_range_refinement_violation = 91,
    /// Contextual `.Variant` syntax cannot be resolved against expected type (`E0407`).
    e0407_invalid_contextual_variant = 92,
    /// Duplicate symbol definition in the same namespace and lexical scope (`E0408`).
    e0408_duplicate_definition = 93,
    /// Access to a private item, field, or method outside its defining module (`E0409`).
    e0409_private_symbol_access = 94,
    /// Postfix `?` operator used outside a fallible `T!E` or `T?` function (`E0410`).
    e0410_try_outside_fallible_fn = 95,
    /// Propagated error type cannot be converted via `FromError` or `@from` (`E0411`).
    e0411_missing_from_error_conversion = 96,
    /// `let … else` guard block does not unconditionally diverge (`never`) (`E0412`).
    e0412_let_else_not_diverging = 97,
    /// Unhandled `T!E` or `@must_use` value in expression statement (`E0413`).
    e0413_unhandled_must_use_or_result = 98,
    /// Forbidden bare `_ = fallible()` discard of a `T!E` without `catch` or `.ok()` (`E0414`).
    e0414_bare_wildcard_result_discard = 99,
    /// Non-exhaustive pattern arms in `match` expression (`E0415`).
    e0415_non_exhaustive_match = 100,
    /// `$` length sentinel used outside indexable `[…]` brackets (`E0416`).
    e0416_invalid_dollar_length_expr = 101,
    /// Irrefutable bare identifier pattern in an `is` test (`E0418`).
    e0418_irrefutable_is_binding = 102,
    /// Invalid named or default call arguments at a call site (`E0419`).
    e0419_invalid_call_arguments = 103,
    /// Missing active `own` marker at call site on named non-`Copy` binding (`E0420`).
    e0420_missing_call_site_own = 104,
    /// Bare by-value parameter `x: T` where `T` is non-`Copy` (`E0421`).
    e0421_non_copy_value_parameter = 105,
    /// `&out T` parameter contract violation at call site or function exit (`E0422`).
    e0422_out_param_contract_violation = 106,
    /// `bit_field` width mismatch or invalid backed-enum, `bit_field`, or `bool` `as` cast (`E0423`).
    e0423_invalid_bitfield_or_enum_cast = 107,
    /// Retired `.len` or `.ptr` field access on slice, array, or `str` (`E0424`).
    e0424_retired_slice_field_access = 108,
    /// Invalid `opaque` value usage or direct `*opaque` dereference (`E0425`).
    e0425_invalid_opaque_type_usage = 109,
    /// Non-defaulted generic parameter follows a defaulted generic parameter (`E0426`).
    e0426_non_trailing_generic_default = 110,
    /// Invalid `@derive(From)` enum layout or Type Group on error side of `T!Group` (`E0427`).
    e0427_invalid_error_composition = 111,
    /// Named argument passed to a `/` positional-only parameter (`E0428`).
    e0428_named_arg_for_positional_only = 112,
    /// Positional argument passed to a `*` keyword-only parameter (`E0429`).
    e0429_positional_arg_for_keyword_only = 113,
    /// Non-defaulted parameter follows a defaulted parameter before `*` (`E0430`).
    e0430_non_default_after_default_param = 114,
    /// Invalid `FormatSpec` syntax or incompatible specifier for interpolated type or `@secret` (`E0431`).
    e0431_invalid_format_specifier = 115,
    /// Missing non-defaulted struct field initializer without `..` or `..base` (`E0432`).
    e0432_missing_struct_field_initializer = 116,
    /// Inaccessible private, `pub(super)`, or `pub(pkg)` symbol or struct field (`E0433`).
    e0433_inaccessible_field_or_visibility = 117,
    /// Invalid non-place or immutable target in parallel destructuring assignment (`E0434`).
    e0434_invalid_parallel_assign_target = 118,
    /// Invalid, non-boolean, or undeclared feature predicate in `@cfg(…)` (`E0435`).
    e0435_invalid_cfg_predicate = 119,
    /// `@builder_item` invoked outside an active `@builder` trailing block scope (`E0436`).
    e0436_builder_item_outside_scope = 120,
    /// Invalid labeled `match` `continue :label` target or state payload (`E0437`).
    e0437_invalid_labeled_match_continue = 121,
    /// Postfix `.await` used outside an `async fn`, `async` closure, or `async` block (`E0438`).
    e0438_await_outside_async_context = 122,
    /// Pointless `_ = expr;` discard of `unit` or already-used local/parameter (`E0439`).
    e0439_pointless_unit_or_used_discard = 123,
    /// Invalid or conflicting `@repr`, `@link`, or `@inline` schema arguments (`E0440`).
    e0440_invalid_repr_or_inline_attribute = 124,
    /// Safe `&` / `&mut` / `&out` borrow of misaligned packed struct field (`E0441`).
    e0441_unaligned_packed_field_borrow = 125,

    // E05xx; Comptime Virtual Machine & MIR Lowering:
    /// Compile-time execution exceeded step fuel budget (`E0501`).
    e0501_comptime_step_limit_exceeded = 126,
    /// Compile-time integer arithmetic overflow (`E0502`).
    e0502_integer_constant_overflow = 127,
    /// Forbidden non-deterministic, FFI, I/O, or raw pointer-to-integer operation in `comptime` (`E0503`).
    e0503_forbidden_comptime_operation = 128,
    /// Out-of-bounds array, slice, or virtual allocation access in `comptime` (`E0504`).
    e0504_comptime_out_of_bounds = 129,
    /// Read from uninitialized virtual memory bytes in `comptime` (`E0505`).
    e0505_comptime_uninitialized_read = 130,
    /// Null, misaligned, or dangling virtual pointer dereference in `comptime` (`E0506`).
    e0506_comptime_invalid_pointer = 131,
    /// Division by zero, remainder by zero, or invalid shift count in `comptime` (`E0507`).
    e0507_comptime_arithmetic_trap = 132,
    /// Virtual heap, call depth, loop unroll, or `@embed_bytes` cap exceeded in `comptime` (`E0508`).
    e0508_comptime_resource_limit_exceeded = 133,
    /// Cyclic dependency across `const` or `comptime` evaluations (`E0509`).
    e0509_comptime_evaluation_cycle = 134,
    /// Failed `@compile_assert` or reached `@compile_error` intrinsic (`E0510`).
    e0510_compile_assertion_failed = 135,

    // W00xx to W05xx; Subsystem Warnings & 44 Built-In Lint Rules (`DR-25`):
    /// Deprecated CLI invocation or option (`W0001`).
    w0001_deprecated_cli_option = 136,
    /// Unfulfilled `@expect(…)` or stale/misplaced suppression directive (`W0002`).
    w0002_unused_suppression = 137,
    /// Missing or placeholder suppression rationale under `require_suppression_reason` (`W0003`).
    w0003_missing_suppression_reason = 138,
    /// Unconditional `@allow` used where self-cleaning `@expect` fits (`W0004`).
    w0004_prefer_expect_over_allow = 139,
    /// Redundant character escape sequence in literal (`W0101`).
    w0101_redundant_escape_sequence = 140,
    /// Bidirectional override, isolate, or zero-width Trojan Source codepoint (`W0102`).
    w0102_unicode_trojan_control = 141,
    /// Mixed-script identifier or UTS #39 confusable identifier collision (`W0103`).
    w0103_confusable_ident = 142,
    /// Confusable homoglyph or standalone ASCII impostor in comment, docstring, or literal (`W0104`).
    w0104_ambiguous_unicode_text = 143,
    /// Interpolated `f"…"` / `f#"…"#` string contains zero `{…}` holes (`W0119`).
    w0119_useless_format_string = 144,
    /// Plain `"…"` passed to `FmtArgs` sink contains `{ident}` matching an in-scope binding (`W0120`).
    w0120_uninterpolated_fmt_placeholder = 145,
    /// Raw string literal `#"…"#` uses more `#` delimiters than required (`W0121`).
    w0121_needless_raw_string_hashes = 146,
    /// Numeric literal with `>= 5` ungrouped digits or irregular `_` grouping (`W0122`).
    w0122_ungrouped_numeric_literal = 147,
    /// Hexadecimal literal `0x…` contains lowercase `a`–`f` digits (`W0123`).
    w0123_non_upper_hex_literal = 148,
    /// Identifier does not follow canonical CoreX casing (`W0201`).
    w0201_non_canonical_identifier_case = 149,
    /// Non-idiomatic syntax or redundant expression construct (`W0202`).
    w0202_non_idiomatic_construct = 150,
    /// Cryptic single-character variable, parameter, or field identifier (`W0203`).
    w0203_single_char_ident = 151,
    /// Binding shadows an outer binding in the same function (`W0204`).
    w0204_shadowed_binding = 152,
    /// `bool`-returning function or method lacks predicate prefix (`W0205`).
    w0205_bool_predicate_naming = 153,
    /// Zero-parameter accessor uses redundant `get_` prefix (`W0206`).
    w0206_getter_prefix_noise = 154,
    /// `as_*` / `to_*` / `into_*` method violates 3-tier receiver/allocation contract (`W0207`).
    w0207_conversion_prefix_mismatch = 155,
    /// Explicit local type annotation duplicates literal suffix or constructor type (`W0208`).
    w0208_redundant_literal_type = 156,
    /// Explicit `return expr;` at tail of function or closure body (`W0209`).
    w0209_needless_trailing_return = 157,
    /// Verbose `x = x op y` or 3-statement temporary swap (`W0210`).
    w0210_manual_assign_or_swap = 158,
    /// Unused region capability or linear binding (`W0308`).
    w0308_unused_region_allocation = 159,
    /// Slice or array bounds not statically proven under `--sast-strict` (`W0314`).
    w0314_unproven_bounds_access = 160,
    /// Panic inside vacated non-`Copy` projection inserts abort guard (`W0329`).
    w0329_vacated_projection_panic_abort = 161,
    /// Unreachable high-risk capability exported by dependency (`W0330`).
    w0330_ambient_dead_capability_in_dep = 162,
    /// Non-seeded entropy, wall clock, or pointer-address hash in `corex test --sim` (`W0332`).
    w0332_nondeterministic_sim_source = 163,
    /// Redundant `@inline`, `@no_alloc`, `@no_panic`, or `@no_block` on private/generic/`= expr;` fn (`W0333`).
    w0333_redundant_private_contract = 164,
    /// `.clone()` on non-`Copy` binding at provable last use (`W0334`).
    w0334_redundant_move_clone = 165,
    /// Repeated string concatenation or growth inside loop without `StringBuilder` (`W0335`).
    w0335_string_concat_in_loop = 166,
    /// Unreachable pattern arm in `match` expression (`W0401`).
    w0401_unreachable_pattern_arm = 167,
    /// Unused local variable binding or function parameter (`W0402`).
    w0402_unused_binding = 168,
    /// Reference to symbol marked `@deprecated` (`W0403`).
    w0403_deprecated_symbol = 169,
    /// Unused `use` import item or alias (`W0404`).
    w0404_unused_import = 170,
    /// `var` binding or `&mut` parameter never mutated (`W0405`).
    w0405_unused_mut_binding = 171,
    /// `pub(pkg)` or `pub(super)` symbol never referenced outside its module (`W0406`).
    w0406_unused_pkg_visibility = 172,
    /// Redundant boolean literal comparison or `if cond => true else false` branch (`W0407`).
    w0407_needless_bool_branch = 173,
    /// Nested `if a { if b { … } }` without `else` branch (`W0408`).
    w0408_collapsible_if = 174,
    /// `match` with single substantive arm and `_ => {}` wildcard (`W0409`).
    w0409_simplifiable_match = 175,
    /// Verbose `match` reimplementing `orelse` or postfix `?` (`W0410`).
    w0410_manual_orelse_or_try = 176,
    /// Single-use local temporary immediately consumed on the next line (`W0411`).
    w0411_single_use_temp = 177,
    /// Redundant `.clone()` on a `Copy` receiver (`W0412`).
    w0412_clone_on_copy = 178,
    /// Immutable `&T` parameter where `T: Copy` and `sizeof(T) <= 16` (`W0413`).
    w0413_trivially_copy_pass_by_ref = 179,
    /// Identical LHS and RHS operands in comparison, logical, or bitwise operator (`W0414`).
    w0414_identical_operands = 180,
    /// Function exceeds MIR inlining cost threshold (`W0501`).
    w0501_inlining_budget_exceeded = 181,

    /// Ergonomic alias for undeclared `@cfg(cfg.feature.<name>)` predicates (`E0435`).
    pub const e0435_unknown_cfg_feature: DiagnosticCode = .e0435_invalid_cfg_predicate;
    /// Ergonomic alias for `.e0502_integer_constant_overflow`.
    pub const e0502_integer_overflow: DiagnosticCode = .e0502_integer_constant_overflow;

    /// Returns the raw integer discriminant (`0..181`) of this `DiagnosticCode`.
    pub inline fn asInt(self: DiagnosticCode) u16 {
        return @backingInt(self);
    }

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

    /// Returns the bijective `RuleId` (`0..43`) if this `DiagnosticCode` is one of the 44 built-in lint rules.
    pub inline fn asLintRuleId(self: DiagnosticCode) ?RuleId {
        const mapped = DIAG_CODE_TO_RULE_ID[@backingInt(self)];
        return if (mapped == 0xFF) null else @enumFromInt(mapped);
    }

    /// Resolves a canonical 5-character code string (e.g., `"E0302"`) to its `DiagnosticCode` in $O(1)$ time.
    pub fn fromCodeStr(code_str: []const u8) ?DiagnosticCode {
        return DIAGNOSTIC_CODE_STR_MAP.get(code_str);
    }
};

/// Dense 64-bit bitmask over all 44 CoreX v1.0 built-in lint rules (`RuleId` `0..43`).
pub const RuleMask64 = u64;

/// Strongly typed dense `0..43` rule identifier for the 44 CoreX v1.0 built-in lint rules (`DR-25` §4.2).
pub const RuleId = enum(u8) {
    /// Unfulfilled `@expect(…)` or stale/misplaced suppression (`W0002`).
    unused_suppression = 0,
    /// Missing or placeholder suppression `reason` (`W0003`).
    missing_suppression_reason = 1,
    /// Unconditional `@allow` used where `@expect` fits (`W0004`).
    prefer_expect_over_allow = 2,
    /// Redundant character escape sequence (`W0101`).
    redundant_escape_sequence = 3,
    /// Bidirectional or zero-width Trojan Source control character (`W0102`).
    unicode_trojan_control = 4,
    /// Mixed-script or UTS #39 confusable identifier (`W0103`).
    confusable_ident = 5,
    /// Ambiguous Unicode homoglyph or ASCII impostor in text (`W0104`).
    ambiguous_unicode_text = 6,
    /// Zero-hole interpolated `f"…"` string (`W0119`).
    useless_format_string = 7,
    /// Plain `"…"` string with `{ident}` in `FmtArgs` sink (`W0120`).
    uninterpolated_fmt_braces = 8,
    /// Excess `#` delimiters on raw string literal (`W0121`).
    needless_raw_string_hashes = 9,
    /// Ungrouped `>= 5`-digit or irregularly grouped numeric literal (`W0122`).
    ungrouped_numeric_literal = 10,
    /// Lowercase `a`–`f` digits in `0x…` hexadecimal literal (`W0123`).
    non_upper_hex_literal = 11,
    /// Non-canonical CoreX identifier casing (`W0201`).
    non_canonical_case = 12,
    /// Non-idiomatic syntax or redundant expression construct (`W0202`).
    non_idiomatic_syntax = 13,
    /// Cryptic single-character identifier (`W0203`).
    single_char_ident = 14,
    /// Inner binding shadows outer binding in function (`W0204`).
    shadowed_binding = 15,
    /// `bool`-returning function/method lacks predicate prefix (`W0205`).
    bool_predicate_naming = 16,
    /// Zero-parameter accessor uses redundant `get_` prefix (`W0206`).
    getter_prefix_noise = 17,
    /// `as_*` / `to_*` / `into_*` receiver/allocation contract mismatch (`W0207`).
    conversion_prefix_mismatch = 18,
    /// Redundant explicit local type duplicating literal suffix/constructor (`W0208`).
    redundant_literal_type = 19,
    /// Explicit `return expr;` at tail of body (`W0209`).
    needless_trailing_return = 20,
    /// Verbose `x = x op y` or 3-statement swap (`W0210`).
    manual_assign_or_swap = 21,
    /// Unused region allocation or linear binding (`W0308`).
    unused_region_alloc = 22,
    /// Vacated non-`Copy` projection panic abort guard (`W0329`).
    vacated_projection_abort = 23,
    /// Ambient unreachable high-risk dependency capability (`W0330`).
    ambient_dead_capability = 24,
    /// Non-deterministic host source in `corex test --sim` (`W0332`).
    nondeterministic_sim_source = 25,
    /// Redundant contract attribute on private/generic/`= expr;` fn (`W0333`).
    redundant_private_contract = 26,
    /// `.clone()` on non-`Copy` binding at provable last use (`W0334`).
    redundant_move_clone = 27,
    /// String concatenation inside loop without `StringBuilder` (`W0335`).
    string_concat_in_loop = 28,
    /// Unreachable pattern arm in `match` (`W0401`).
    unreachable_pattern = 29,
    /// Unused local variable or parameter (`W0402`).
    unused_binding = 30,
    /// Reference to `@deprecated` symbol (`W0403`).
    deprecated_use = 31,
    /// Unused `use` import item or alias (`W0404`).
    unused_import = 32,
    /// `var` binding or `&mut` parameter never mutated (`W0405`).
    unused_mut_binding = 33,
    /// `pub(pkg)` / `pub(super)` item unused outside defining module (`W0406`).
    unused_pkg_visibility = 34,
    /// Redundant boolean comparison or `if cond => true else false` (`W0407`).
    needless_bool_branch = 35,
    /// Collapsible nested `if` without `else` (`W0408`).
    collapsible_if = 36,
    /// Single-arm `match` with `_ => {}` wildcard (`W0409`).
    simplifiable_match = 37,
    /// Manual `match` reimplementing `orelse` or `?` (`W0410`).
    manual_orelse_or_try = 38,
    /// Single-use local temporary immediately consumed on next line (`W0411`).
    single_use_temp = 39,
    /// Redundant `.clone()` on `Copy` type (`W0412`).
    clone_on_copy = 40,
    /// Small `<= 16 B` `Copy` parameter passed by `&T` (`W0413`).
    trivially_copy_pass_by_ref = 41,
    /// Identical LHS and RHS operands in binary operator (`W0414`).
    identical_operands = 42,
    /// Function exceeds MIR inlining instruction budget (`W0501`).
    inlining_budget_exceeded = 43,

    /// Total count of CoreX v1.0 built-in lint rules (`44`).
    pub const COUNT: usize = 44;

    /// Returns the dense `0..43` integer index of this `RuleId`.
    pub inline fn asInt(self: RuleId) u8 {
        return @intFromEnum(self);
    }

    /// Returns the single-bit `RuleMask64` (`1 << rule_id`) for this `RuleId`.
    pub inline fn bit(self: RuleId) RuleMask64 {
        return @as(RuleMask64, 1) << @intCast(@intFromEnum(self));
    }

    /// Returns the static `LintRuleMeta` catalog entry for this `RuleId` in $O(1)$ time.
    pub inline fn asMeta(self: RuleId) LintRuleMeta {
        return DIAGNOSTIC_LINT_CATALOG[@intFromEnum(self)];
    }

    /// Returns the corresponding `DiagnosticCode` (`W0xxx`) for this `RuleId`.
    pub inline fn asDiagCode(self: RuleId) DiagnosticCode {
        return self.asMeta().diag_code;
    }

    /// Returns the canonical `kebab-case` rule slug (e.g., `"single-char-ident"`).
    pub inline fn asSlug(self: RuleId) []const u8 {
        return self.asMeta().slug;
    }
};

/// Informational taxonomy grouping for `corex explain` and `--format json` (`DR-25` §2.1).
pub const LintCategory = enum(u8) {
    /// Probable bug, Trojan Source hazard, unreachable code, or simulation nondeterminism (`4` rules).
    correctness = 0,
    /// Dubious or confusing code that may mask subtle logic bugs (`11` rules).
    suspicious = 1,
    /// Readability, self-documenting naming, and simplified control flow (`14` rules).
    clarity = 2,
    /// Canonical CoreX surface conventions and hygiene (`10` rules).
    style = 3,
    /// Zero-cost ownership, copy, and allocation performance (`5` rules).
    perf = 4,

    /// Returns the canonical lowercase category label.
    pub fn asStr(self: LintCategory) []const u8 {
        return switch (self) {
            .correctness => "correctness",
            .suspicious => "suspicious",
            .clarity => "clarity",
            .style => "style",
            .perf => "perf",
        };
    }
};

/// Compiler pipeline stage that produces candidates for a built-in lint rule (`DR-25` §4.1).
pub const LintPassStage = enum(u8) {
    /// Pass 1A lexical / `TokenBuffer` scan (`W0101`–`W0104`, `W0119`, `W0121`–`W0123`).
    token_buffer = 0,
    /// Pass 1B `LosslessCstArena` + `AstArena` walk (`W0003`, `W0004`, `W0201`–`W0203`).
    cst_ast = 1,
    /// Pass 2 `SymbolResolver` scope/module graph (`W0103`, `W0204`, `W0404`, `W0406`).
    resolve = 2,
    /// Pass 3 `TypeSystem` / typed HIR (`W0120`, `W0205`–`W0206`, `W0208`–`W0210`, `W0401`–`W0403`, `W0405`, `W0407`–`W0412`, `W0414`).
    typecheck = 3,
    /// Pass 4 `MirSast` dataflow & ownership (`W0207`, `W0308`, `W0329`–`W0335`, `W0413`).
    mir_sast = 4,
    /// Pass 5 `MirOpt` inlining cost model (`W0501`).
    mir_opt = 5,
    /// Post-pass `FulfillmentTracker` unfulfilled `@expect` / stale directive sweep (`W0002`).
    post_filter = 6,
};

/// Canonical metadata record for each of the 44 CoreX v1.0 built-in lint rules (`DR-25` §4.2).
pub const LintRuleMeta = struct {
    /// Dense `0..43` rule identifier.
    rule_id: RuleId,
    /// Bijective `W0xxx` `DiagnosticCode`.
    diag_code: DiagnosticCode,
    /// Canonical `kebab-case` rule slug (`5..40` ASCII bytes).
    slug: []const u8,
    /// Informational category (`correctness`, `suspicious`, `clarity`, `style`, `perf`).
    category: LintCategory,
    /// Compiler pass stage emitting raw candidates for this rule.
    stage: LintPassStage,
    /// Default fix applicability tier (`.machine_applicable`, `.maybe_incorrect`, or `.unspecified`).
    default_applicability: FixApplicability,
    /// Whether LSP publishes `DiagnosticTag.Unnecessary` (`1`) for dimmed editor rendering.
    is_unnecessary_tag: bool,
};

/// Classification outcome of `lookupLintRuleBySelector` (`0` heap allocations).
pub const LintSelectorLookup = union(enum) {
    /// Matched one of the 44 suppressible built-in lint rules.
    rule: RuleId,
    /// Matched a forbidden blanket or category name (`*`, `all`, `warnings`, `style`, `clarity`, etc.).
    forbidden_category_or_wildcard: void,
    /// Matched an `E0xxx` hard compiler error code (`null` if unassigned `E0xxx`).
    non_suppressible_error_code: ?DiagnosticCode,
    /// Matched a non-lint subsystem warning (`W0001` or `W0314`).
    non_suppressible_subsystem_warning: DiagnosticCode,
    /// Unrecognized rule code or slug.
    unknown: void,
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

/// Key-value tuple entry pairing a 5-character diagnostic code string with its `DiagnosticCode` tag.
const CodeKvPair = struct { []const u8, DiagnosticCode };

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
        .code = .e0006_invalid_target_triple,
        .code_str = "E0006",
        .default_severity = .err,
        .title = "invalid or unsupported target triple",
        .explanation = "The `--target` triple is malformed or not supported by this CoreX compiler.",
    },
    .{
        .code = .e0007_codegen_backend_failure,
        .code_str = "E0007",
        .default_severity = .err,
        .title = "backend code generation failure",
        .explanation = "The Tier A C99 or Tier B LLVM code generator failed to emit an artifact.",
    },
    .{
        .code = .e0008_linker_invocation_failed,
        .code_str = "E0008",
        .default_severity = .err,
        .title = "compiler driver or linker invocation failed",
        .explanation = "Invoking `zig cc` or the target system linker failed or exited non-zero.",
    },
    .{
        .code = .e0009_c_header_translation_failed,
        .code_str = "E0009",
        .default_severity = .err,
        .title = "C header translation failure",
        .explanation = "C11/C23 header preprocessing, declaration parsing, or `@c_import` / `translate-c` ingestion failed.",
    },
    .{
        .code = .e0010_unsatisfiable_dependency_graph,
        .code_str = "E0010",
        .default_severity = .err,
        .title = "unsatisfiable package dependency graph",
        .explanation = "No package version assignment satisfies all SemVer bounds, feature requirements, and `[resolution].exclude` rules.",
    },
    .{
        .code = .e0011_native_links_collision,
        .code_str = "E0011",
        .default_severity = .err,
        .title = "native C 'links' library collision",
        .explanation = "At most one resolved package in a workspace build graph may claim a given native C `links` library key.",
    },
    .{
        .code = .e0012_cross_major_cxi_type_mismatch,
        .code_str = "E0012",
        .default_severity = .err,
        .title = "cross-major nominal package type mismatch",
        .explanation = "Nominal `.cxi` types exported by coexisting major versions of the same package are distinct and cannot be mixed.",
    },
    .{
        .code = .e0013_invalid_manifest_or_pkg_name,
        .code_str = "E0013",
        .default_severity = .err,
        .title = "invalid 'corex.toml' manifest or package name",
        .explanation = "Manifests and script frontmatter must follow the single-form `corex.toml` schema and `kebab-case` naming rules.",
    },
    .{
        .code = .e0014_lockfile_drift_or_corrupt,
        .code_str = "E0014",
        .default_severity = .err,
        .title = "missing, drifted, or corrupt 'corex.lock'",
        .explanation = "`corex.lock` is malformed or out of sync with `corex.toml` while `--locked`, `--frozen`, or `COREX_HERMETIC=1` is active.",
    },
    .{
        .code = .e0015_cache_integrity_mismatch,
        .code_str = "E0015",
        .default_severity = .err,
        .title = "package cache cryptographic integrity mismatch",
        .explanation = "A package archive, `.cxtree`, blob, Ed25519 signature, or RFC 6962 transparency-log proof failed verification.",
    },
    .{
        .code = .e0016_offline_or_fetch_failed,
        .code_str = "E0016",
        .default_severity = .err,
        .title = "package fetch failed or unavailable offline",
        .explanation = "A required package artifact or sparse index entry could not be fetched or was missing from cache under `--offline`.",
    },
    .{
        .code = .e0017_stray_tool_config_dotfile,
        .code_str = "E0017",
        .default_severity = .err,
        .title = "stray standalone tool configuration file",
        .explanation = "Standalone `.corex-lint.toml` / `.corexfmt.toml` files are forbidden; " ++
            "configure `[lint]`, `[fmt]`, and `[lsp]` in `corex.toml`.",
    },
    .{
        .code = .e0018_forbidden_tool_config_key,
        .code_str = "E0018",
        .default_severity = .err,
        .title = "forbidden style-fragmenting or severity-remapping key in 'corex.toml'",
        .explanation = "`[fmt]` forbids style knobs and `[lint]` uses a flat `disable = [\"…\"]` list without per-rule severity maps.",
    },
    .{
        .code = .e0019_invalid_lint_rule_or_glob,
        .code_str = "E0019",
        .default_severity = .err,
        .title = "unknown lint rule identifier or invalid path glob pattern",
        .explanation = "A rule code/slug or path glob pattern in `corex.toml` or CLI flags is unrecognized or malformed.",
    },
    .{
        .code = .e0020_tool_setting_out_of_range,
        .code_str = "E0020",
        .default_severity = .err,
        .title = "tooling configuration threshold or setting value out of bounds",
        .explanation = "A `[lint.settings]` or `[lsp]` configuration value falls outside its allowed range or enum domain.",
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
        .code = .e0112_retired_path_separator,
        .code_str = "E0112",
        .default_severity = .err,
        .title = "retired '::' path separator",
        .explanation = "CoreX uses a unified `.` separator for modules, types, variants, and members; replace `::` with `.`.",
    },
    .{
        .code = .e0113_retired_logical_and,
        .code_str = "E0113",
        .default_severity = .err,
        .title = "retired '&&' logical AND operator",
        .explanation = "C-style `&&` has been retired in favor of the canonical `and` keyword.",
    },
    .{
        .code = .e0114_invalid_brace_escape,
        .code_str = "E0114",
        .default_severity = .err,
        .title = "unmatched '}' or invalid brace escape in interpolated string",
        .explanation = "Interpolated `f\"…\"` strings use `{{` and `}}` for literal braces; unmatched `}` and `\\{` / `\\}` are invalid.",
    },
    .{
        .code = .e0115_multiline_string_opening,
        .code_str = "E0115",
        .default_severity = .err,
        .title = "retired '\"\"\"' delimiter or invalid multiline closing quote",
        .explanation = "Triple-quoted `\"\"\"` is retired; open multiline strings with `\"<newline>` " ++
            "and place closing `\"` on its own indented line.",
    },
    .{
        .code = .e0116_multiline_string_indent,
        .code_str = "E0116",
        .default_severity = .err,
        .title = "under-indented multiline string line or forbidden '\\t' tab",
        .explanation = "Multiline content lines must match closing `\"` indentation using ASCII spaces " ++
            "(`4`-space indent; `\\t` tabs are forbidden).",
    },
    .{
        .code = .e0117_non_ascii_byte_literal,
        .code_str = "E0117",
        .default_severity = .err,
        .title = "non-ASCII byte in byte literal",
        .explanation = "Byte literals `b'…'` and `b\"…\"` only accept ASCII `0x00..0x7F` directly; use `\\xNN` for `0x80..0xFF`.",
    },
    .{
        .code = .e0118_block_doc_comment_forbidden,
        .code_str = "E0118",
        .default_severity = .err,
        .title = "retired block comment ('/* … */') or 3-character doc prefix ('///' / '//!')",
        .explanation = "Block comments and 3-character doc prefixes are retired; use `//` for comments, " ++
            "`/|` for item docs, and `/#` for module docs.",
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
        .code = .e0214_invalid_condition_binding,
        .code_str = "E0214",
        .default_severity = .err,
        .title = "invalid pattern binding in negated or disjunctive condition",
        .explanation = "Pattern bindings in `is` are forbidden under `is not`, `not`, `or`, or outside positive `if`/`while` conditions.",
    },
    .{
        .code = .e0215_invalid_walrus_position,
        .code_str = "E0215",
        .default_severity = .err,
        .title = "condition ':=' binding outside positive 'if'/'while' header",
        .explanation = "Condition bindings require parenthesized `(x := expr)` atoms along the positive `and` spine of an `if` or `while` header.",
    },
    .{
        .code = .e0216_retired_if_while_let,
        .code_str = "E0216",
        .default_severity = .err,
        .title = "retired 'if let' / 'while let' syntax",
        .explanation = "Conditional `if let` and `while let` have been retired; use `if expr is Pattern` or `while expr is Pattern`.",
    },
    .{
        .code = .e0218_direct_core_import_forbidden,
        .code_str = "E0218",
        .default_severity = .err,
        .title = "direct 'core' import forbidden outside kernel",
        .explanation = "User code must import from `cx.*` instead of `core.*` unless compiled with `--internal-core`.",
    },
    .{
        .code = .e0219_retired_logical_or,
        .code_str = "E0219",
        .default_severity = .err,
        .title = "retired infix '||' logical OR operator",
        .explanation = "Infix `||` has been retired in favor of `or`; `||` is reserved exclusively for zero-parameter closures.",
    },
    .{
        .code = .e0220_retired_bang_prefix,
        .code_str = "E0220",
        .default_severity = .err,
        .title = "retired prefix '!' negation operator",
        .explanation = "Prefix `!` has been retired; use `not` for boolean negation or `~` for bitwise complement.",
    },
    .{
        .code = .e0221_retired_mutability_or_param_mode,
        .code_str = "E0221",
        .default_severity = .err,
        .title = "retired mutability or parameter mode spelling",
        .explanation = "Use `var` for mutable bindings and `&T`, `&mut T`, `own T`, or `&out T` for parameter modes.",
    },
    .{
        .code = .e0222_chained_result_type,
        .code_str = "E0222",
        .default_severity = .err,
        .title = "non-associative chained '!' result type",
        .explanation = "Result type `T!E` is non-associative; parenthesize nested result types explicitly as `(A!B)!C` or `A!(B!C)`.",
    },
    .{
        .code = .e0223_retired_attribute_eq,
        .code_str = "E0223",
        .default_severity = .err,
        .title = "retired '=' key-value separator in attribute",
        .explanation = "Named attribute arguments use `:` (`@attr(key: value)`) rather than `=`.",
    },
    .{
        .code = .e0224_retired_semicolon_member_sep,
        .code_str = "E0224",
        .default_severity = .err,
        .title = "retired ';' member separator in nominal type",
        .explanation = "Fields and variants in `struct`, `union`, `enum`, and `bit_field` declarations must be separated by `,`.",
    },
    .{
        .code = .e0225_retired_noalloc_attribute,
        .code_str = "E0225",
        .default_severity = .err,
        .title = "retired '@noalloc' attribute spelling",
        .explanation = "Attribute `@noalloc` has been retired; use canonical `@no_alloc`.",
    },
    .{
        .code = .e0226_retired_const_raw_ptr,
        .code_str = "E0226",
        .default_severity = .err,
        .title = "retired '*const T' raw pointer syntax",
        .explanation = "Raw pointers are immutable by default (`*T`); write `*T` instead of `*const T` (or `*mut T` for mutable).",
    },
    .{
        .code = .e0227_retired_prefix_deref,
        .code_str = "E0227",
        .default_severity = .err,
        .title = "retired prefix '*ptr' dereference syntax",
        .explanation = "C-style prefix `*ptr` dereferencing has been retired; use postfix `ptr.*`.",
    },
    .{
        .code = .e0228_invalid_param_zone_separator,
        .code_str = "E0228",
        .default_severity = .err,
        .title = "invalid '/' or '*' parameter zone separator",
        .explanation = "Positional-only `/` must precede `*`, neither may repeat, `/` requires prior params, and `*` requires trailing params.",
    },
    .{
        .code = .e0229_misplaced_module_doc_comment,
        .code_str = "E0229",
        .default_severity = .err,
        .title = "misplaced module docstring ('/#')",
        .explanation = "Module docstrings (`/#`) may only appear at the top of a `.cx` file before any `/|`, non-doc comment, or item.",
    },
    .{
        .code = .e0230_unattached_doc_comment,
        .code_str = "E0230",
        .default_severity = .err,
        .title = "unattached outer docstring ('/|')",
        .explanation = "Outer docstrings (`/|`) must immediately precede a documentable item with no blank line or `//` comment.",
    },
    .{
        .code = .e0231_visibility_on_impl_block,
        .code_str = "E0231",
        .default_severity = .err,
        .title = "visibility modifier on 'impl' block",
        .explanation = "`impl` blocks do not take outer visibility modifiers (`pub impl`); declare `pub` on individual methods or items.",
    },
    .{
        .code = .e0232_inline_method_in_type_decl,
        .code_str = "E0232",
        .default_severity = .err,
        .title = "inline method or 'subscript' inside type declaration",
        .explanation = "`struct`, `union`, `bit_field`, and `enum` bodies define pure byte layouts; place methods and `subscript` items in `impl`.",
    },
    .{
        .code = .e0233_invalid_elif_keyword,
        .code_str = "E0233",
        .default_severity = .err,
        .title = "invalid 'elif' / 'elsif' / 'elseif' keyword",
        .explanation = "Single-keyword chained conditionals (`elif`, `elsif`, `elseif`) are not part of CoreX; write `else if`.",
    },
    .{
        .code = .e0234_non_binding_wildcard_let_var,
        .code_str = "E0234",
        .default_severity = .err,
        .title = "non-binding wildcard 'let _' / 'var _' declaration",
        .explanation = "Non-binding `let _ = expr;` and `var _ = expr;` have been retired; write bare `_ = expr;` to discard a value immediately.",
    },
    .{
        .code = .e0235_all_wildcard_destructuring_assign,
        .code_str = "E0235",
        .default_severity = .err,
        .title = "all-wildcard destructuring assignment",
        .explanation = "Destructuring assignments must bind at least one mutable place leaf; write bare `_ = expr;` to discard the entire value.",
    },
    .{
        .code = .e0236_missing_colon_before_type,
        .code_str = "E0236",
        .default_severity = .err,
        .title = "missing ':' before type annotation",
        .explanation = "Type annotations require a postfix `:` separator between the identifier and its type (`name: Type`).",
    },
    .{
        .code = .e0237_inline_if_missing_else,
        .code_str = "E0237",
        .default_severity = .err,
        .title = "inline 'if cond => expr' missing 'else' branch",
        .explanation = "Inline `if cond => expr` must produce a value on all paths and requires `else expr`; use `if cond { … }` for statements.",
    },
    .{
        .code = .e0238_mixed_if_arrow_and_block,
        .code_str = "E0238",
        .default_severity = .err,
        .title = "mixed '=>' and '{ … }' branches in 'if' expression",
        .explanation = "Do not mix `=>` and `{ … }` in `if`; use `if cond => a else b` for single expressions " ++
            "or `if cond { … } else { … }` for blocks.",
    },
    .{
        .code = .e0239_retired_layout_or_link_attribute,
        .code_str = "E0239",
        .default_severity = .err,
        .title = "retired standalone layout/linkage attribute or '@[…]'/'@(…)' wrapper",
        .explanation = "Layout and symbol attributes consolidate into `@repr(…)` and `@link(…)`, " ++
            "and attributes use `@attr` without outer brackets.",
    },
    .{
        .code = .e0240_invalid_suppression_selector,
        .code_str = "E0240",
        .default_severity = .err,
        .title = "invalid, empty, category-wide, or non-suppressible rule selector",
        .explanation = "`@expect`, `@allow`, and `// corex check:` require explicit `W0xxx` lint codes or `kebab-case` rule slugs.",
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
        .explanation = "Overlapping shared (`&T`) and mutable (`&mut T`) borrows conflict on the same storage path.",
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
        .code = .e0308_unterminated_cstr_ffi,
        .code_str = "E0308",
        .default_severity = .err,
        .title = "unterminated string or slice passed to `@null_terminated` C FFI",
        .explanation = "Passing a non-NUL-terminated `str` or slice to a `@null_terminated` C FFI parameter requires `CStr` conversion.",
    },
    .{
        .code = .e0309_concurrent_exclusivity_or_escape,
        .code_str = "E0309",
        .default_severity = .err,
        .title = "concurrent exclusivity, `@thread_local` capture, or escape violation",
        .explanation = "Concurrent `&mut` aliasing, `!Send`/`@thread_local` capture, or region escape crossed a `TaskGroup`/`async` boundary.",
    },
    .{
        .code = .e0310_mismatched_ffi_deallocator,
        .code_str = "E0310",
        .default_severity = .err,
        .title = "mismatched FFI deallocator or allocator domain",
        .explanation = "An `@owned_by_caller @free_with(fn)` FFI pointer was released with a mismatched deallocator or wrong allocator domain.",
    },
    .{
        .code = .e0311_unchecked_nullable_ffi_ptr,
        .code_str = "E0311",
        .default_severity = .err,
        .title = "unchecked nullable FFI pointer dereference or `@non_null` pass",
        .explanation = "An `@may_be_null` FFI pointer was dereferenced or passed to a `@non_null` consumer without a dominating null check.",
    },
    .{
        .code = .e0312_unproven_ffi_slice_len,
        .code_str = "E0312",
        .default_severity = .err,
        .title = "unproven buffer capacity at `@slice_len` / `@byte_len` FFI boundary",
        .explanation = "Raw pointer and length passed to `@slice_len` or `@byte_len` FFI lack statically proven slice capacity.",
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
        .code = .e0317_async_inline_frame_exceeded,
        .code_str = "E0317",
        .default_severity = .err,
        .title = "inline async frame exceeds 16 KiB cap or forms unboxed cycle",
        .explanation = "Inline stackless `async` frame subtree exceeds the 16 KiB (16,384 B) cap or forms an unboxed recursive cycle.",
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
        .explanation = "Attribute targets a pre-main loader/TLS/interpose section or uses `@std_cap_boundary` outside `cx` or `core`.",
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
        .explanation = "Contextual `.Variant` syntax requires a known target `enum`, `T?`, or `T!E` expected type.",
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
        .explanation = "Postfix `?` propagates `.Err` or `.None` and requires an enclosing `T!E` or `T?` return type.",
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
        .explanation = "Fallible `T!E` and `@must_use` values cannot be silently ignored in an expression statement.",
    },
    .{
        .code = .e0414_bare_wildcard_result_discard,
        .code_str = "E0414",
        .default_severity = .err,
        .title = "cannot discard Result with bare _ = fallible()",
        .explanation = "Discarding a `T!E` result via bare `_ = fallible()` is forbidden; use `fallible() catch {};` or `_ = fallible().ok();`.",
    },
    .{
        .code = .e0415_non_exhaustive_match,
        .code_str = "E0415",
        .default_severity = .err,
        .title = "non-exhaustive match patterns",
        .explanation = "The `match` arms do not cover every possible value of the scrutinee type.",
    },
    .{
        .code = .e0416_invalid_dollar_length_expr,
        .code_str = "E0416",
        .default_severity = .err,
        .title = "invalid '$' length sentinel outside indexable brackets",
        .explanation = "`$` is valid only inside `target[…]` brackets over a fixed array, slice, `#soa` slice, or `str`.",
    },
    .{
        .code = .e0418_irrefutable_is_binding,
        .code_str = "E0418",
        .default_severity = .err,
        .title = "irrefutable identifier pattern in 'is' test",
        .explanation = "Bare `x is y` binds irrefutably; use `(y := x)` for a binding, `.Variant` for an enum variant, or `y @ subpat`.",
    },
    .{
        .code = .e0419_invalid_call_arguments,
        .code_str = "E0419",
        .default_severity = .err,
        .title = "invalid named or default call arguments",
        .explanation = "Call has positional-after-named args, unknown/duplicate labels, missing required args, or indirect named/default args.",
    },
    .{
        .code = .e0420_missing_call_site_own,
        .code_str = "E0420",
        .default_severity = .err,
        .title = "missing 'own' marker at call site",
        .explanation = "Passing a named non-`Copy` binding to an `own T` parameter requires an explicit `own arg` call-site marker.",
    },
    .{
        .code = .e0421_non_copy_value_parameter,
        .code_str = "E0421",
        .default_severity = .err,
        .title = "bare by-value parameter requires Copy type",
        .explanation = "Non-`Copy` parameter `x: T` must specify `&T` (shared borrow), `&mut T` (mutable borrow), or `own T` (move).",
    },
    .{
        .code = .e0422_out_param_contract_violation,
        .code_str = "E0422",
        .default_severity = .err,
        .title = "'&out T' parameter contract violation",
        .explanation = "Call-site `&out` target holds a live `AutoDrop`/`@linear` value, or callee exits normally without initializing `&out`.",
    },
    .{
        .code = .e0423_invalid_bitfield_or_enum_cast,
        .code_str = "E0423",
        .default_severity = .err,
        .title = "invalid bit_field width or nominal integer cast",
        .explanation = "Packed `bit_field` member widths must match the backing `uN`, and `as` casts require backed enums or `bool`.",
    },
    .{
        .code = .e0424_retired_slice_field_access,
        .code_str = "E0424",
        .default_severity = .err,
        .title = "retired '.len' or '.ptr' field access on slice/array/str",
        .explanation = "Direct `.len` and `.ptr` field accesses are retired; call `.len()`, `.as_ptr()`, or `.as_mut_ptr()`.",
    },
    .{
        .code = .e0425_invalid_opaque_type_usage,
        .code_str = "E0425",
        .default_severity = .err,
        .title = "invalid unsized 'opaque' type usage",
        .explanation = "Unsized `opaque` may only appear behind `*opaque` or `*mut opaque` and cannot be dereferenced directly.",
    },
    .{
        .code = .e0426_non_trailing_generic_default,
        .code_str = "E0426",
        .default_severity = .err,
        .title = "non-defaulted generic parameter after defaulted parameter",
        .explanation = "Generic type and `const` parameters with `= Default` must trail all required generic parameters.",
    },
    .{
        .code = .e0427_invalid_error_composition,
        .code_str = "E0427",
        .default_severity = .err,
        .title = "invalid '@derive(From)' enum or Type Group error union",
        .explanation = "`@derive(From)` requires distinct single-field error variants, and compile-time Type Groups cannot appear in `T!Group`.",
    },
    .{
        .code = .e0428_named_arg_for_positional_only,
        .code_str = "E0428",
        .default_severity = .err,
        .title = "named argument passed to positional-only parameter",
        .explanation = "Parameters declared left of `/` are positional-only and cannot be passed using `label: expr` syntax.",
    },
    .{
        .code = .e0429_positional_arg_for_keyword_only,
        .code_str = "E0429",
        .default_severity = .err,
        .title = "positional argument passed to keyword-only parameter",
        .explanation = "Parameters declared right of `*` are keyword-only and must be passed with an explicit `label: expr`.",
    },
    .{
        .code = .e0430_non_default_after_default_param,
        .code_str = "E0430",
        .default_severity = .err,
        .title = "non-defaulted parameter after defaulted parameter",
        .explanation = "Before `*`, required parameters without `= default` cannot follow defaulted parameters.",
    },
    .{
        .code = .e0431_invalid_format_specifier,
        .code_str = "E0431",
        .default_severity = .err,
        .title = "invalid format specifier for interpolated expression",
        .explanation = "The `:FormatSpec` string is malformed, incompatible with the operand type, or formats a `@secret` value.",
    },
    .{
        .code = .e0432_missing_struct_field_initializer,
        .code_str = "E0432",
        .default_severity = .err,
        .title = "missing required struct field initializer",
        .explanation = "Every struct field without a declared `= default` must be initialized explicitly or via `..base`.",
    },
    .{
        .code = .e0433_inaccessible_field_or_visibility,
        .code_str = "E0433",
        .default_severity = .err,
        .title = "inaccessible private, pub(super), or pub(pkg) member",
        .explanation = "Symbol or struct field visibility prevents access, construction, functional spread, or destructuring here.",
    },
    .{
        .code = .e0434_invalid_parallel_assign_target,
        .code_str = "E0434",
        .default_severity = .err,
        .title = "invalid target in parallel destructuring assignment",
        .explanation = "Every non-`_` leaf on the left-hand side of a parallel assignment must be a mutable memory place.",
    },
    .{
        .code = .e0435_invalid_cfg_predicate,
        .code_str = "E0435",
        .default_severity = .err,
        .title = "invalid '@cfg' conditional compilation predicate",
        .explanation = "`@cfg(…)` requires a `comptime` `bool` expression over `target` and declared `cfg` features.",
    },
    .{
        .code = .e0436_builder_item_outside_scope,
        .code_str = "E0436",
        .default_severity = .err,
        .title = "'@builder_item' invoked outside '@builder' block",
        .explanation = "Functions marked `@builder_item` require an enclosing `@builder` trailing block supplying a mutable scope.",
    },
    .{
        .code = .e0437_invalid_labeled_match_continue,
        .code_str = "E0437",
        .default_severity = .err,
        .title = "invalid labeled 'match' continue target or payload",
        .explanation = "`continue :label state` must target an enclosing labeled `match` and supply the next scrutinee value.",
    },
    .{
        .code = .e0438_await_outside_async_context,
        .code_str = "E0438",
        .default_severity = .err,
        .title = "postfix `.await` outside async context",
        .explanation = "Postfix `.await` may only be used inside an `async fn`, `async` closure, or `async` block.",
    },
    .{
        .code = .e0439_pointless_unit_or_used_discard,
        .code_str = "E0439",
        .default_severity = .err,
        .title = "pointless '_ =' discard of 'unit' or already-used binding",
        .explanation = "Discarding a `unit` expression or an already-used binding via `_ = …;` is redundant; remove `_ =` or the statement.",
    },
    .{
        .code = .e0440_invalid_repr_or_inline_attribute,
        .code_str = "E0440",
        .default_severity = .err,
        .title = "invalid or conflicting '@repr', '@link', or '@inline' arguments",
        .explanation = "Validate `@repr` (`C | transparent`, `packed: bool | 1|2|4|8|16` with `C`, " ++
            "`align: N | .CacheLine`, `zero_pad: bool`) and `@inline`.",
    },
    .{
        .code = .e0441_unaligned_packed_field_borrow,
        .code_str = "E0441",
        .default_severity = .err,
        .title = "safe borrow of misaligned '@repr(C, packed: …)' field",
        .explanation = "Borrowing an unaligned packed field via `&` or `&mut` is undefined; copy `s.field` by value or use `&raw s.field`.",
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
        .code = .w0002_unused_suppression,
        .code_str = "W0002",
        .default_severity = .warning,
        .title = "unused lint suppression expectation",
        .explanation = "An `@expect(…)` or `expect(…)` directive intercepted zero matching lint warnings (or `file-*` appeared mid-file).",
    },
    .{
        .code = .w0003_missing_suppression_reason,
        .code_str = "W0003",
        .default_severity = .warning,
        .title = "missing or placeholder lint suppression reason",
        .explanation = "Suppression directives require a meaningful `reason: \"…\"` or `-- <reason>` rationale (`>= 4` non-placeholder chars).",
    },
    .{
        .code = .w0004_prefer_expect_over_allow,
        .code_str = "W0004",
        .default_severity = .warning,
        .title = "prefer '@expect' over '@allow' on handwritten items",
        .explanation = "Use self-cleaning `@expect(…)` instead of `@allow(…)` on " ++
            "non-`@cfg`, non-`@generated` items so stale suppressions surface.",
    },
    .{
        .code = .w0101_redundant_escape_sequence,
        .code_str = "W0101",
        .default_severity = .warning,
        .title = "redundant character escape sequence",
        .explanation = "A string or character literal used an unnecessary backslash escape.",
    },
    .{
        .code = .w0102_unicode_trojan_control,
        .code_str = "W0102",
        .default_severity = .warning,
        .title = "Trojan bidirectional or zero-width Unicode control codepoint",
        .explanation = "Source contains a UAX #9 bidirectional override/isolate or invisible zero-width spoofing control scalar.",
    },
    .{
        .code = .w0103_confusable_ident,
        .code_str = "W0103",
        .default_severity = .warning,
        .title = "mixed-script confusable identifier or skeleton collision",
        .explanation = "An identifier mixes confusable cross-script glyphs (`UTS #55`) or collides with an in-scope `UTS #39` skeleton.",
    },
    .{
        .code = .w0104_ambiguous_unicode_text,
        .code_str = "W0104",
        .default_severity = .warning,
        .title = "ambiguous Unicode homoglyph or typographic impostor in text",
        .explanation = "A literal or comment mixes a non-ASCII homoglyph into a Latin word or uses smart quotes, NBSP, or `U+2212` minus.",
    },
    .{
        .code = .w0119_useless_format_string,
        .code_str = "W0119",
        .default_severity = .warning,
        .title = "interpolated string contains zero '{…}' holes",
        .explanation = "Interpolated `f\"…\"` or `f#\"…\"#` has no `{…}` holes; remove `f` prefix " ++
            "to use plain `\"…\"` / `r#\"…\"#` `str`.",
    },
    .{
        .code = .w0120_uninterpolated_fmt_placeholder,
        .code_str = "W0120",
        .default_severity = .warning,
        .title = "plain string in format sink contains uninterpolated '{ident}'",
        .explanation = "Plain `\"…\"` does not interpolate `{ident}`; prepend `f` if formatting the in-scope binding was intended.",
    },
    .{
        .code = .w0121_needless_raw_string_hashes,
        .code_str = "W0121",
        .default_severity = .warning,
        .title = "needless raw string '#' guards or 'r' prefix",
        .explanation = "A raw or raw-format string uses more `#` delimiter guards than required or needs neither `\"` nor `\\`.",
    },
    .{
        .code = .w0122_ungrouped_numeric_literal,
        .code_str = "W0122",
        .default_severity = .warning,
        .title = "ungrouped or inconsistently grouped numeric literal",
        .explanation = "Multi-digit integer literals (`>= 5` digits) must group digits consistently with `_` separators.",
    },
    .{
        .code = .w0123_non_upper_hex_literal,
        .code_str = "W0123",
        .default_severity = .warning,
        .title = "non-uppercase hexadecimal literal digits or '0X' prefix",
        .explanation = "Hexadecimal literals must use a lowercase `0x` prefix and uppercase `A`–`F` digits (keeping type suffixes lowercase).",
    },
    .{
        .code = .w0201_non_canonical_identifier_case,
        .code_str = "W0201",
        .default_severity = .warning,
        .title = "identifier does not follow canonical casing",
        .explanation = "Types must use `PascalCase`, functions/variables `snake_case`, and constants `SCREAMING_SNAKE_CASE`.",
    },
    .{
        .code = .w0202_non_idiomatic_construct,
        .code_str = "W0202",
        .default_severity = .warning,
        .title = "non-idiomatic syntax or redundant expression construct",
        .explanation = "An expression or declaration uses redundant parentheses, `;`, explicit `-> unit`, or non-canonical surface spelling.",
    },
    .{
        .code = .w0203_single_char_ident,
        .code_str = "W0203",
        .default_severity = .warning,
        .title = "cryptic single-character local or parameter identifier",
        .explanation = "Single-letter bindings outside `{i, j, k, n, x, y, z, w}` and inline single-expression closures obscure intent.",
    },
    .{
        .code = .w0204_shadowed_binding,
        .code_str = "W0204",
        .default_severity = .warning,
        .title = "local binding shadows live outer 'var' or later-read variable",
        .explanation = "Shadowing a mutable `var`, an outer binding read after the inner block, or an unread same-scope `let` risks confusion.",
    },
    .{
        .code = .w0205_bool_predicate_naming,
        .code_str = "W0205",
        .default_severity = .warning,
        .title = "boolean-returning function lacks predicate naming",
        .explanation = "Non-mutating `-> bool` functions and methods should read as predicates (`is_`, `has_`, `can_`, `should_`, `contains`, …).",
    },
    .{
        .code = .w0206_getter_prefix_noise,
        .code_str = "W0206",
        .default_severity = .warning,
        .title = "redundant 'get_' prefix on O(1) property accessor",
        .explanation = "Zero-argument `&self` property accessors omit `get_` (`len()`, `header()`, reserving `get` for keyed/fallible lookups).",
    },
    .{
        .code = .w0207_conversion_prefix_mismatch,
        .code_str = "W0207",
        .default_severity = .warning,
        .title = "'as_' / 'to_' / 'into_' conversion prefix violates ownership or allocation tier",
        .explanation = "`as_*` must borrow with zero heap allocation, `to_*` must not consume `own self` on `~Copy`, " ++
            "and `into_*` must take `own self`.",
    },
    .{
        .code = .w0208_redundant_literal_type,
        .code_str = "W0208",
        .default_severity = .warning,
        .title = "redundant explicit type annotation on local binding",
        .explanation = "A local `let` or `var` repeats `: T` when the initializer already carries an explicit type suffix or nominal constructor.",
    },
    .{
        .code = .w0209_needless_trailing_return,
        .code_str = "W0209",
        .default_severity = .warning,
        .title = "needless trailing 'return' at end of body",
        .explanation = "Omit trailing `return;` in `unit` bodies and write tail `expr` directly instead of `return expr;`.",
    },
    .{
        .code = .w0210_manual_assign_or_swap,
        .code_str = "W0210",
        .default_severity = .warning,
        .title = "manual compound assignment or temporary swap",
        .explanation = "Use compound assignment (`x += y;`) instead of `x = x + y;` and parallel destructuring `(a, b) = (b, a);` for swaps.",
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
        .explanation = "Un-elided panic inside a mutable (`&mut` / `subscript`) `yield` projection of a non-`Copy` slot inserts an abort guard.",
    },
    .{
        .code = .w0330_ambient_dead_capability_in_dep,
        .code_str = "W0330",
        .default_severity = .warning,
        .title = "unreachable high-risk capability in dependency",
        .explanation = "Dependency exports dead/unreachable functions carrying `net`, `process`, or `ffi` capabilities.",
    },
    .{
        .code = .w0332_nondeterministic_sim_source,
        .code_str = "W0332",
        .default_severity = .warning,
        .title = "nondeterministic host clock or entropy source in simulation",
        .explanation = "Direct host `clock` or `entropy` syscalls bypass `Context.reactor` / `Context.rng` under `corex test --sim`.",
    },
    .{
        .code = .w0333_redundant_private_contract,
        .code_str = "W0333",
        .default_severity = .warning,
        .title = "redundant '@inline', '@no_alloc', '@no_panic', or '@no_block' attribute",
        .explanation = "Inlining and effect contracts are inferred automatically on private, generic, " ++
            "and `= expr;` functions; reserve for `pub` boundaries.",
    },
    .{
        .code = .w0334_redundant_move_clone,
        .code_str = "W0334",
        .default_severity = .warning,
        .title = "redundant '.clone()' on owned value before last use",
        .explanation = "Liveness analysis proved the cloned local `~Copy` binding is never read again; transfer ownership directly without cloning.",
    },
    .{
        .code = .w0335_string_concat_in_loop,
        .code_str = "W0335",
        .default_severity = .warning,
        .title = "repeated string or vector concatenation inside loop",
        .explanation = "Repeated `+=` or `f\"{s}…\"` re-allocation inside a loop degrades throughput; " ++
            "pre-size with `with_capacity` or use `Writer`.",
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
        .code = .w0403_deprecated_symbol,
        .code_str = "W0403",
        .default_severity = .warning,
        .title = "use of deprecated symbol",
        .explanation = "A symbol marked `@deprecated` was referenced; migrate to its replacement API or run `corex upgrade`.",
    },
    .{
        .code = .w0404_unused_import,
        .code_str = "W0404",
        .default_severity = .warning,
        .title = "unused 'use' import specifier",
        .explanation = "An imported `use` specifier has zero value, type, or trait-method references in active or `@cfg`-gated code.",
    },
    .{
        .code = .w0405_unused_mut_binding,
        .code_str = "W0405",
        .default_severity = .warning,
        .title = "mutable 'var' binding is never mutated",
        .explanation = "A `var` local variable or value parameter is never reassigned or `&mut`-borrowed; declare immutable `let` instead.",
    },
    .{
        .code = .w0406_unused_pkg_visibility,
        .code_str = "W0406",
        .default_severity = .warning,
        .title = "unused 'pub(pkg)' or 'pub(super)' cross-module visibility",
        .explanation = "An intra-package `pub(pkg)` or `pub(super)` item has zero callers outside its defining module; narrow its visibility.",
    },
    .{
        .code = .w0407_needless_bool_branch,
        .code_str = "W0407",
        .default_severity = .warning,
        .title = "needless boolean branch or literal boolean equality",
        .explanation = "Simplify `if c { return true; } else { return false; }`, `x == true`, `x == false`, and `not (a == b)` directly.",
    },
    .{
        .code = .w0408_collapsible_if,
        .code_str = "W0408",
        .default_severity = .warning,
        .title = "collapsible nested 'if' or 'else { if }'",
        .explanation = "Combine nested `if a { if b { … } }` into `if a and b { … }` and `else { if b { … } }` into `else if b { … }`.",
    },
    .{
        .code = .w0409_simplifiable_match,
        .code_str = "W0409",
        .default_severity = .warning,
        .title = "two-arm 'match' simplifiable to 'if' or 'if is'",
        .explanation = "Replace two-arm boolean `match` or single-pattern `match` with an empty `_ => {}` arm by `if` / `if x is Pattern`.",
    },
    .{
        .code = .w0410_manual_orelse_or_try,
        .code_str = "W0410",
        .default_severity = .warning,
        .title = "manual 'Option' / 'Result' 'match' reducible to 'orelse' or '?'",
        .explanation = "Express `.Some(v) => v, .None => d` as `opt orelse d` and `.Ok(v) => v, .Err(e) => return .Err(e)` as `res?`.",
    },
    .{
        .code = .w0411_single_use_temp,
        .code_str = "W0411",
        .default_severity = .warning,
        .title = "single-use temporary variable before return or condition",
        .explanation = "Inline single-use `let res = expr; return res;` or condition-tested temporaries directly into their consumer.",
    },
    .{
        .code = .w0412_clone_on_copy,
        .code_str = "W0412",
        .default_severity = .warning,
        .title = "unnecessary '.clone()' on 'Copy' type",
        .explanation = "Calling `.clone()` on a `Copy` value or `&Copy` reference is redundant; copy by value or dereference `.*` directly.",
    },
    .{
        .code = .w0413_trivially_copy_pass_by_ref,
        .code_str = "W0413",
        .default_severity = .warning,
        .title = "small 'Copy' type passed by '&T' reference",
        .explanation = "Passing register-sized `Copy` types (`<= 8 B` on 64-bit, `<= 4 B` on `wasm32`) by value avoids pointer indirection.",
    },
    .{
        .code = .w0414_identical_operands,
        .code_str = "W0414",
        .default_severity = .warning,
        .title = "identical operands on both sides of operator or branch",
        .explanation = "Comparing, combining, or branching to identical pure expressions " ++
            "(`x == x`, `a and a`, `if c => a else a`) indicates a typo.",
    },
    .{
        .code = .w0501_inlining_budget_exceeded,
        .code_str = "W0501",
        .default_severity = .warning,
        .title = "function exceeds inlining cost threshold",
        .explanation = "A function marked for inlining exceeded the MIR instruction size threshold.",
    },
};

/// Mask with all 44 v1.0 built-in lint rule bits enabled (`(1 << 44) - 1`).
pub const ALL_RULES_MASK: RuleMask64 = (@as(u64, 1) << RuleId.COUNT) - 1;

/// Canonical 44-rule CoreX v1.0 Built-In Lint Catalog (`DR-25` §2.2 & Post-Critique Ruling 1.2).
pub const DIAGNOSTIC_LINT_CATALOG = [RuleId.COUNT]LintRuleMeta{
    .{
        .rule_id = .unused_suppression,
        .diag_code = .w0002_unused_suppression,
        .slug = "unused-suppression",
        .category = .suspicious,
        .stage = .post_filter,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .missing_suppression_reason,
        .diag_code = .w0003_missing_suppression_reason,
        .slug = "missing-suppression-reason",
        .category = .clarity,
        .stage = .cst_ast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .prefer_expect_over_allow,
        .diag_code = .w0004_prefer_expect_over_allow,
        .slug = "prefer-expect-over-allow",
        .category = .clarity,
        .stage = .cst_ast,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .redundant_escape_sequence,
        .diag_code = .w0101_redundant_escape_sequence,
        .slug = "redundant-escape-sequence",
        .category = .style,
        .stage = .token_buffer,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .unicode_trojan_control,
        .diag_code = .w0102_unicode_trojan_control,
        .slug = "unicode-trojan-control",
        .category = .correctness,
        .stage = .token_buffer,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .confusable_ident,
        .diag_code = .w0103_confusable_ident,
        .slug = "confusable-ident",
        .category = .suspicious,
        .stage = .resolve,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .ambiguous_unicode_text,
        .diag_code = .w0104_ambiguous_unicode_text,
        .slug = "ambiguous-unicode-text",
        .category = .suspicious,
        .stage = .token_buffer,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .useless_format_string,
        .diag_code = .w0119_useless_format_string,
        .slug = "useless-format-string",
        .category = .clarity,
        .stage = .token_buffer,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .uninterpolated_fmt_braces,
        .diag_code = .w0120_uninterpolated_fmt_placeholder,
        .slug = "uninterpolated-fmt-braces",
        .category = .suspicious,
        .stage = .typecheck,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .needless_raw_string_hashes,
        .diag_code = .w0121_needless_raw_string_hashes,
        .slug = "needless-raw-string-hashes",
        .category = .style,
        .stage = .token_buffer,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .ungrouped_numeric_literal,
        .diag_code = .w0122_ungrouped_numeric_literal,
        .slug = "ungrouped-numeric-literal",
        .category = .clarity,
        .stage = .token_buffer,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .non_upper_hex_literal,
        .diag_code = .w0123_non_upper_hex_literal,
        .slug = "non-upper-hex-literal",
        .category = .style,
        .stage = .token_buffer,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .non_canonical_case,
        .diag_code = .w0201_non_canonical_identifier_case,
        .slug = "non-canonical-case",
        .category = .style,
        .stage = .cst_ast,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .non_idiomatic_syntax,
        .diag_code = .w0202_non_idiomatic_construct,
        .slug = "non-idiomatic-syntax",
        .category = .style,
        .stage = .cst_ast,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .single_char_ident,
        .diag_code = .w0203_single_char_ident,
        .slug = "single-char-ident",
        .category = .clarity,
        .stage = .cst_ast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .shadowed_binding,
        .diag_code = .w0204_shadowed_binding,
        .slug = "shadowed-binding",
        .category = .suspicious,
        .stage = .resolve,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .bool_predicate_naming,
        .diag_code = .w0205_bool_predicate_naming,
        .slug = "bool-predicate-naming",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .getter_prefix_noise,
        .diag_code = .w0206_getter_prefix_noise,
        .slug = "getter-prefix-noise",
        .category = .style,
        .stage = .typecheck,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .conversion_prefix_mismatch,
        .diag_code = .w0207_conversion_prefix_mismatch,
        .slug = "conversion-prefix-mismatch",
        .category = .suspicious,
        .stage = .mir_sast,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .redundant_literal_type,
        .diag_code = .w0208_redundant_literal_type,
        .slug = "redundant-literal-type",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .needless_trailing_return,
        .diag_code = .w0209_needless_trailing_return,
        .slug = "needless-trailing-return",
        .category = .style,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .manual_assign_or_swap,
        .diag_code = .w0210_manual_assign_or_swap,
        .slug = "manual-assign-or-swap",
        .category = .style,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .unused_region_alloc,
        .diag_code = .w0308_unused_region_allocation,
        .slug = "unused-region-alloc",
        .category = .suspicious,
        .stage = .mir_sast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .vacated_projection_abort,
        .diag_code = .w0329_vacated_projection_panic_abort,
        .slug = "vacated-projection-abort",
        .category = .suspicious,
        .stage = .mir_sast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .ambient_dead_capability,
        .diag_code = .w0330_ambient_dead_capability_in_dep,
        .slug = "ambient-dead-capability",
        .category = .suspicious,
        .stage = .mir_sast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .nondeterministic_sim_source,
        .diag_code = .w0332_nondeterministic_sim_source,
        .slug = "nondeterministic-sim-source",
        .category = .correctness,
        .stage = .mir_sast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .redundant_private_contract,
        .diag_code = .w0333_redundant_private_contract,
        .slug = "redundant-private-contract",
        .category = .style,
        .stage = .mir_sast,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .redundant_move_clone,
        .diag_code = .w0334_redundant_move_clone,
        .slug = "redundant-move-clone",
        .category = .perf,
        .stage = .mir_sast,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .string_concat_in_loop,
        .diag_code = .w0335_string_concat_in_loop,
        .slug = "string-concat-in-loop",
        .category = .perf,
        .stage = .mir_sast,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .unreachable_pattern,
        .diag_code = .w0401_unreachable_pattern_arm,
        .slug = "unreachable-pattern",
        .category = .correctness,
        .stage = .typecheck,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .unused_binding,
        .diag_code = .w0402_unused_binding,
        .slug = "unused-binding",
        .category = .suspicious,
        .stage = .typecheck,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .deprecated_use,
        .diag_code = .w0403_deprecated_symbol,
        .slug = "deprecated-use",
        .category = .suspicious,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .unused_import,
        .diag_code = .w0404_unused_import,
        .slug = "unused-import",
        .category = .style,
        .stage = .resolve,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .unused_mut_binding,
        .diag_code = .w0405_unused_mut_binding,
        .slug = "unused-mut-binding",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .unused_pkg_visibility,
        .diag_code = .w0406_unused_pkg_visibility,
        .slug = "unused-pkg-visibility",
        .category = .clarity,
        .stage = .resolve,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .needless_bool_branch,
        .diag_code = .w0407_needless_bool_branch,
        .slug = "needless-bool-branch",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .collapsible_if,
        .diag_code = .w0408_collapsible_if,
        .slug = "collapsible-if",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .simplifiable_match,
        .diag_code = .w0409_simplifiable_match,
        .slug = "simplifiable-match",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .manual_orelse_or_try,
        .diag_code = .w0410_manual_orelse_or_try,
        .slug = "manual-orelse-or-try",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .single_use_temp,
        .diag_code = .w0411_single_use_temp,
        .slug = "single-use-temp",
        .category = .clarity,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .clone_on_copy,
        .diag_code = .w0412_clone_on_copy,
        .slug = "clone-on-copy",
        .category = .perf,
        .stage = .typecheck,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = true,
    },
    .{
        .rule_id = .trivially_copy_pass_by_ref,
        .diag_code = .w0413_trivially_copy_pass_by_ref,
        .slug = "trivially-copy-pass-by-ref",
        .category = .perf,
        .stage = .mir_sast,
        .default_applicability = .machine_applicable,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .identical_operands,
        .diag_code = .w0414_identical_operands,
        .slug = "identical-operands",
        .category = .correctness,
        .stage = .typecheck,
        .default_applicability = .maybe_incorrect,
        .is_unnecessary_tag = false,
    },
    .{
        .rule_id = .inlining_budget_exceeded,
        .diag_code = .w0501_inlining_budget_exceeded,
        .slug = "inlining-budget-exceeded",
        .category = .perf,
        .stage = .mir_opt,
        .default_applicability = .unspecified,
        .is_unnecessary_tag = false,
    },
};

/// $O(1)$ lookup table mapping `@backingInt(DiagnosticCode)` to `RuleId` (`0xFF` = non-lint code).
pub const DIAG_CODE_TO_RULE_ID = blk: {
    var table: [DIAGNOSTIC_CATALOG.len]u8 = @splat(0xFF);
    for (DIAGNOSTIC_LINT_CATALOG) |meta| {
        table[@backingInt(meta.diag_code)] = meta.rule_id.asInt();
    }
    break :blk table;
};

/// $O(1)$ lookup table mapping numeric suffix `2..501` of `"W0xxx"` to `RuleId` (`0xFF` = unassigned/non-lint).
pub const W_NUMBER_TO_RULE_ID = blk: {
    var table: [600]u8 = @splat(0xFF);
    for (DIAGNOSTIC_LINT_CATALOG) |meta| {
        const code_str = meta.diag_code.asCodeStr();
        const num: usize = (@as(usize, code_str[1] - '0') * 1000) +
            (@as(usize, code_str[2] - '0') * 100) +
            (@as(usize, code_str[3] - '0') * 10) +
            @as(usize, code_str[4] - '0');
        table[num] = meta.rule_id.asInt();
    }
    break :blk table;
};

/// Open-addressed 64-slot `Wyhash(0)` linear-probing table mapping `kebab-case` slugs to `RuleId` (`0xFF` = empty).
pub const LINT_SLUG_HASH_TABLE = blk: {
    @setEvalBranchQuota(20_000);
    var table: [64]u8 = @splat(0xFF);
    for (DIAGNOSTIC_LINT_CATALOG, 0..) |meta, rule_idx| {
        var slot: usize = @intCast(std.hash.Wyhash.hash(0, meta.slug) & 63);
        while (table[slot] != 0xFF) : (slot = (slot + 1) & 63) {}
        table[slot] = @intCast(rule_idx);
    }
    break :blk table;
};

/// Forbidden blanket or category-wide selector keywords (`E0240` / `E0019`).
const FORBIDDEN_SELECTOR_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "*", {} },
    .{ "all", {} },
    .{ "clarity", {} },
    .{ "correctness", {} },
    .{ "lints", {} },
    .{ "perf", {} },
    .{ "style", {} },
    .{ "suspicious", {} },
    .{ "warnings", {} },
});

/// Legacy pre-`DR-25` shorthand aliases mapped to canonical v1.0 `kebab-case` slugs for typo hints.
const LEGACY_LINT_ALIAS_SUGGESTIONS = std.StaticStringMap([]const u8).initComptime(.{
    .{ "deprecated", "deprecated-use" },
    .{ "idiom", "non-idiomatic-syntax" },
    .{ "non_canonical_case", "non-canonical-case" },
    .{ "non_idiomatic", "non-idiomatic-syntax" },
    .{ "redundant_private_contract", "redundant-private-contract" },
    .{ "uninterpolated_fmt_placeholder", "uninterpolated-fmt-braces" },
    .{ "unreachable_pattern", "unreachable-pattern" },
    .{ "unused", "unused-binding" },
    .{ "unused_binding", "unused-binding" },
    .{ "unused_variables", "unused-binding" },
    .{ "useless_format_string", "useless-format-string" },
});

/// Static $O(1)$ compile-time map resolving canonical 5-character code strings to `DiagnosticCode`.
pub const DIAGNOSTIC_CODE_STR_MAP = blk: {
    @setEvalBranchQuota(30_000);
    var pairs: [DIAGNOSTIC_CATALOG.len]CodeKvPair = undefined;
    for (DIAGNOSTIC_CATALOG, 0..) |descriptor, i| {
        pairs[i] = .{ descriptor.code_str, descriptor.code };
    }
    break :blk std.StaticStringMap(DiagnosticCode).initComptime(pairs);
};

comptime {
    @setEvalBranchQuota(50_000);
    std.debug.assert(DIAGNOSTIC_CATALOG.len == 182);
    std.debug.assert(DIAGNOSTIC_CODE_STR_MAP.keys().len == DIAGNOSTIC_CATALOG.len);
    std.debug.assert(@typeInfo(DiagnosticCode).@"enum".field_names.len == DIAGNOSTIC_CATALOG.len);
    std.debug.assert(@sizeOf(RuleId) == 1);
    std.debug.assert(@sizeOf(RuleMask64) == 8);
    std.debug.assert(DIAGNOSTIC_LINT_CATALOG.len == 44);
    for (DIAGNOSTIC_CATALOG, 0..) |entry, i| {
        std.debug.assert(@backingInt(entry.code) == i);
    }

    // Verify Post-Critique Ruling 1.2 fix-tier and category counts + bijective lookup round-trips:
    var auto_count: usize = 0;
    var unsafe_count: usize = 0;
    var diag_only_count: usize = 0;
    var cat_counts: [5]usize = @splat(0);

    for (DIAGNOSTIC_LINT_CATALOG, 0..) |meta, idx| {
        std.debug.assert(meta.rule_id.asInt() == idx);
        std.debug.assert(meta.diag_code.defaultSeverity() == .warning);
        std.debug.assert(meta.diag_code.asLintRuleId().? == meta.rule_id);
        std.debug.assert(meta.slug.len >= 5 and meta.slug.len <= 40);
        for (meta.slug) |ch| {
            std.debug.assert((ch >= 'a' and ch <= 'z') or (ch >= '0' and ch <= '9') or ch == '-');
        }
        std.debug.assert(lookupLintRuleBySelector(meta.slug).rule == meta.rule_id);
        std.debug.assert(lookupLintRuleBySelector(meta.diag_code.asCodeStr()).rule == meta.rule_id);

        switch (meta.default_applicability) {
            .machine_applicable => auto_count += 1,
            .maybe_incorrect => unsafe_count += 1,
            .unspecified => diag_only_count += 1,
            .has_placeholders => unreachable,
        }
        cat_counts[@intFromEnum(meta.category)] += 1;
    }
    std.debug.assert(auto_count == 26);
    std.debug.assert(unsafe_count == 7);
    std.debug.assert(diag_only_count == 11);
    std.debug.assert(cat_counts[@intFromEnum(LintCategory.correctness)] == 4);
    std.debug.assert(cat_counts[@intFromEnum(LintCategory.suspicious)] == 11);
    std.debug.assert(cat_counts[@intFromEnum(LintCategory.clarity)] == 14);
    std.debug.assert(cat_counts[@intFromEnum(LintCategory.style)] == 10);
    std.debug.assert(cat_counts[@intFromEnum(LintCategory.perf)] == 5);
    std.debug.assert(DiagnosticCode.w0001_deprecated_cli_option.asLintRuleId() == null);
    std.debug.assert(DiagnosticCode.w0314_unproven_bounds_access.asLintRuleId() == null);
}

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

    /// Resets the sink's diagnostic list and bump arena while retaining slab capacity.
    pub fn resetRetainingCapacity(self: *DiagnosticSink) void {
        self.diagnostics = .empty;
        self.arena.resetRetainingCapacity();
        self.error_count = 0;
        self.warning_count = 0;
        self.has_reached_limit = false;
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

/// Classifies `text` (`W0xxx` code or `kebab-case` slug) in $O(1)$ time with zero heap allocations.
pub fn lookupLintRuleBySelector(text: []const u8) LintSelectorLookup {
    if (text.len == 0) return .unknown;
    if (FORBIDDEN_SELECTOR_MAP.has(text)) return .forbidden_category_or_wildcard;

    // [1] Fast 5-byte `W0xxx` / `E0xxx` prefix check:
    if (text.len == 5 and
        std.ascii.isDigit(text[1]) and
        std.ascii.isDigit(text[2]) and
        std.ascii.isDigit(text[3]) and
        std.ascii.isDigit(text[4]))
    {
        const num: usize = (@as(usize, text[1] - '0') * 1000) +
            (@as(usize, text[2] - '0') * 100) +
            (@as(usize, text[3] - '0') * 10) +
            @as(usize, text[4] - '0');
        if (text[0] == 'W') {
            if (num < W_NUMBER_TO_RULE_ID.len) {
                const mapped = W_NUMBER_TO_RULE_ID[num];
                if (mapped != 0xFF) return .{ .rule = @enumFromInt(mapped) };
            }
            if (num == 1) return .{ .non_suppressible_subsystem_warning = .w0001_deprecated_cli_option };
            if (num == 314) return .{ .non_suppressible_subsystem_warning = .w0314_unproven_bounds_access };
            return .unknown;
        }
        if (text[0] == 'E') {
            return .{ .non_suppressible_error_code = DiagnosticCode.fromCodeStr(text) };
        }
    }

    // [2] Open-addressed 64-slot `Wyhash(0)` probe for `kebab-case` rule slugs:
    if (text.len <= 48) {
        var slot: usize = @intCast(std.hash.Wyhash.hash(0, text) & 63);
        var probes: usize = 0;
        while (probes < 64) : (probes += 1) {
            const rule_idx = LINT_SLUG_HASH_TABLE[slot];
            if (rule_idx == 0xFF) break;
            if (std.mem.eql(u8, DIAGNOSTIC_LINT_CATALOG[rule_idx].slug, text)) {
                return .{ .rule = @enumFromInt(rule_idx) };
            }
            slot = (slot + 1) & 63;
        }
    }
    return .unknown;
}

/// Computes bounded Jaro-Winkler similarity in `[0.0, 1.0]` over `<= 64`-byte ASCII strings (`0` heap allocs).
pub fn jaroWinklerSimilarity(first_text: []const u8, second_text: []const u8) f64 {
    const len_a = @min(first_text.len, 64);
    const len_b = @min(second_text.len, 64);
    if (len_a == 0 and len_b == 0) return 1.0;
    if (len_a == 0 or len_b == 0) return 0.0;
    if (std.mem.eql(u8, first_text[0..len_a], second_text[0..len_b])) return 1.0;

    const max_len = @max(len_a, len_b);
    const match_dist: usize = if (max_len >= 2) (max_len / 2) - 1 else 0;

    var matched_a: u64 = 0;
    var matched_b: u64 = 0;
    var match_count: usize = 0;

    var idx_a: usize = 0;
    while (idx_a < len_a) : (idx_a += 1) {
        const win_start = idx_a -| match_dist;
        const win_end = @min(len_b, idx_a + match_dist + 1);
        var idx_b = win_start;
        while (idx_b < win_end) : (idx_b += 1) {
            const bit_b = @as(u64, 1) << @intCast(idx_b);
            if ((matched_b & bit_b) != 0) continue;
            if (first_text[idx_a] != second_text[idx_b]) continue;
            matched_a |= @as(u64, 1) << @intCast(idx_a);
            matched_b |= bit_b;
            match_count += 1;
            break;
        }
    }
    if (match_count == 0) return 0.0;

    var transpositions: usize = 0;
    var cursor_b: usize = 0;
    idx_a = 0;
    while (idx_a < len_a) : (idx_a += 1) {
        if ((matched_a & (@as(u64, 1) << @intCast(idx_a))) == 0) continue;
        while (cursor_b < len_b and (matched_b & (@as(u64, 1) << @intCast(cursor_b))) == 0) {
            cursor_b += 1;
        }
        if (cursor_b < len_b and first_text[idx_a] != second_text[cursor_b]) {
            transpositions += 1;
        }
        cursor_b += 1;
    }

    const matches_f: f64 = @floatFromInt(match_count);
    const trans_half_f: f64 = @as(f64, @floatFromInt(transpositions)) / 2.0;
    const jaro = ((matches_f / @as(f64, @floatFromInt(len_a))) +
        (matches_f / @as(f64, @floatFromInt(len_b))) +
        ((matches_f - trans_half_f) / matches_f)) / 3.0;

    var prefix_len: usize = 0;
    const max_prefix = @min(@as(usize, 4), @min(len_a, len_b));
    while (prefix_len < max_prefix and first_text[prefix_len] == second_text[prefix_len]) {
        prefix_len += 1;
    }
    return jaro + (@as(f64, @floatFromInt(prefix_len)) * 0.1 * (1.0 - jaro));
}

/// Suggests the closest canonical lint rule slug or `W0xxx` code when Jaro-Winkler `>= 0.80` (`0` heap allocs).
pub fn suggestClosestLintRule(text: []const u8) ?[]const u8 {
    if (text.len == 0 or text.len > 64) return null;
    if (LEGACY_LINT_ALIAS_SUGGESTIONS.get(text)) |legacy_target| return legacy_target;

    // Normalize `_` -> `-` and uppercase -> lowercase on stack for slug typo scoring:
    var norm_slug_buf: [64]u8 = undefined;
    var norm_code_buf: [64]u8 = undefined;
    for (text, 0..) |ch, i| {
        norm_slug_buf[i] = if (ch == '_') '-' else std.ascii.toLower(ch);
        norm_code_buf[i] = std.ascii.toUpper(ch);
    }
    const norm_slug = norm_slug_buf[0..text.len];
    const norm_code = norm_code_buf[0..text.len];

    var best_score: f64 = 0.80;
    var best_match: ?[]const u8 = null;

    for (DIAGNOSTIC_LINT_CATALOG) |meta| {
        const slug_score = jaroWinklerSimilarity(norm_slug, meta.slug);
        if (slug_score >= best_score) {
            best_score = slug_score;
            best_match = meta.slug;
        }
        const code_str = meta.diag_code.asCodeStr();
        const code_score = jaroWinklerSimilarity(norm_code, code_str);
        if (code_score > best_score) {
            best_score = code_score;
            best_match = code_str;
        }
    }
    return best_match;
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

    try std.testing.expectEqual(@as(usize, 182), DIAGNOSTIC_CATALOG.len);
    try std.testing.expectEqual(@as(usize, 44), DIAGNOSTIC_LINT_CATALOG.len);
    try std.testing.expectEqual(RuleId.single_char_ident, lookupLintRuleBySelector("single-char-ident").rule);
    try std.testing.expectEqual(RuleId.single_char_ident, lookupLintRuleBySelector("W0203").rule);
    try std.testing.expect(lookupLintRuleBySelector("style") == .forbidden_category_or_wildcard);
    try std.testing.expect(lookupLintRuleBySelector("*") == .forbidden_category_or_wildcard);
    try std.testing.expect(lookupLintRuleBySelector("E0302") == .non_suppressible_error_code);
    try std.testing.expect(lookupLintRuleBySelector("W0001") == .non_suppressible_subsystem_warning);
    try std.testing.expect(lookupLintRuleBySelector("W0314") == .non_suppressible_subsystem_warning);
    try std.testing.expectEqualStrings("single-char-ident", suggestClosestLintRule("single_char_ident").?);
    try std.testing.expectEqualStrings("collapsible-if", suggestClosestLintRule("colapsible-if").?);
    try std.testing.expectEqualStrings("non-canonical-case", suggestClosestLintRule("non_canonical_case").?);
    try std.testing.expectEqual(
        DiagnosticCode.e0118_block_doc_comment_forbidden,
        DiagnosticCode.fromCodeStr("E0118").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0237_inline_if_missing_else,
        DiagnosticCode.fromCodeStr("E0237").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0238_mixed_if_arrow_and_block,
        DiagnosticCode.fromCodeStr("E0238").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0239_retired_layout_or_link_attribute,
        DiagnosticCode.fromCodeStr("E0239").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0440_invalid_repr_or_inline_attribute,
        DiagnosticCode.fromCodeStr("E0440").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0441_unaligned_packed_field_borrow,
        DiagnosticCode.fromCodeStr("E0441").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.w0119_useless_format_string,
        DiagnosticCode.fromCodeStr("W0119").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.w0120_uninterpolated_fmt_placeholder,
        DiagnosticCode.fromCodeStr("W0120").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.w0333_redundant_private_contract,
        DiagnosticCode.fromCodeStr("W0333").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0229_misplaced_module_doc_comment,
        DiagnosticCode.fromCodeStr("E0229").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0230_unattached_doc_comment,
        DiagnosticCode.fromCodeStr("E0230").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0231_visibility_on_impl_block,
        DiagnosticCode.fromCodeStr("E0231").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0232_inline_method_in_type_decl,
        DiagnosticCode.fromCodeStr("E0232").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0233_invalid_elif_keyword,
        DiagnosticCode.fromCodeStr("E0233").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0234_non_binding_wildcard_let_var,
        DiagnosticCode.fromCodeStr("E0234").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0235_all_wildcard_destructuring_assign,
        DiagnosticCode.fromCodeStr("E0235").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0236_missing_colon_before_type,
        DiagnosticCode.fromCodeStr("E0236").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0439_pointless_unit_or_used_discard,
        DiagnosticCode.fromCodeStr("E0439").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.w0202_non_idiomatic_construct,
        DiagnosticCode.fromCodeStr("W0202").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.w0403_deprecated_symbol,
        DiagnosticCode.fromCodeStr("W0403").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0009_c_header_translation_failed,
        DiagnosticCode.fromCodeStr("E0009").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0010_unsatisfiable_dependency_graph,
        DiagnosticCode.fromCodeStr("E0010").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0016_offline_or_fetch_failed,
        DiagnosticCode.fromCodeStr("E0016").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0112_retired_path_separator,
        DiagnosticCode.fromCodeStr("E0112").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0113_retired_logical_and,
        DiagnosticCode.fromCodeStr("E0113").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0117_non_ascii_byte_literal,
        DiagnosticCode.fromCodeStr("E0117").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0218_direct_core_import_forbidden,
        DiagnosticCode.fromCodeStr("E0218").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0228_invalid_param_zone_separator,
        DiagnosticCode.fromCodeStr("E0228").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0308_unterminated_cstr_ffi,
        DiagnosticCode.fromCodeStr("E0308").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0309_concurrent_exclusivity_or_escape,
        DiagnosticCode.fromCodeStr("E0309").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0310_mismatched_ffi_deallocator,
        DiagnosticCode.fromCodeStr("E0310").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0311_unchecked_nullable_ffi_ptr,
        DiagnosticCode.fromCodeStr("E0311").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0312_unproven_ffi_slice_len,
        DiagnosticCode.fromCodeStr("E0312").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0317_async_inline_frame_exceeded,
        DiagnosticCode.fromCodeStr("E0317").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0419_invalid_call_arguments,
        DiagnosticCode.fromCodeStr("E0419").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0420_missing_call_site_own,
        DiagnosticCode.fromCodeStr("E0420").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0437_invalid_labeled_match_continue,
        DiagnosticCode.fromCodeStr("E0437").?,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0438_await_outside_async_context,
        DiagnosticCode.fromCodeStr("E0438").?,
    );
}

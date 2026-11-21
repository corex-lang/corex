//! Zero-Legacy Automated Source Upgrade Rule Catalog (`DR-14`, `DR-21`, `DR-22`, & `DR-23`)
//!
//! Defines the strongly typed rule identifiers, three-tier rewrite engine classifications, and static
//! metadata catalog (`UPGRADE_RULE_CATALOG`) governing `corex upgrade` (`UR-21-00`–`UR-23-06`).
//!
//! Enforces CoreX's Zero-Legacy Firewall (`AGENTS.md` §2): retired surface syntax and stdlib APIs are
//! migrated exclusively through deterministic token, lossless CST, and `TypeId`-aware semantic rewrites
//! rather than carrying backward-compatibility branches inside the active compiler pipeline.

const std = @import("std");
const diagnostic = @import("diag/diagnostic.zig");

const DiagnosticCode = diagnostic.DiagnosticCode;
const EditPriority = diagnostic.EditPriority;
const FixApplicability = diagnostic.FixApplicability;

// ---------------------------------------- TYPES ----------------------------------------

// ---------------------- Upgrade Taxonomy ----------------------

/// Three-tier execution stage in the `corex upgrade` rewrite pipeline (`DR-14` §2.2).
pub const UpgradeEngineTier = enum(u8) {
    /// Tier 1 raw `TokenBuffer` pre-parse lexical canonicalization shim (`UR-21-00`, `UR-22-00`, `UR-23-00`, `UR-23-02`).
    tier1_token_shim = 1,
    /// Tier 2 lossless `LosslessCstArena` + `AstArena` structural pattern rewriter.
    tier2_cst_pattern = 2,
    /// Tier 3 `CompilerDb` `TypeId`-aware semantic modernizer (`UR-21-04`–`UR-21-07`, `UR-22-06`, `UR-23-04`, `UR-23-05`).
    tier3_semantic_modernizer = 3,

    /// Returns the numeric 1-based tier index (`1`–`3`) of `self`.
    pub inline fn asNumber(self: UpgradeEngineTier) u8 {
        return @backingInt(self);
    }

    /// Returns the canonical human-readable tier label for CLI tables and `--explain` cards.
    pub inline fn asLabel(self: UpgradeEngineTier) []const u8 {
        return switch (self) {
            .tier1_token_shim => "Tier 1 Token Shim",
            .tier2_cst_pattern => "Tier 2 CST Pattern",
            .tier3_semantic_modernizer => "Tier 3 Semantic Modernizer",
        };
    }

    /// Returns `true` if `self` requires `CompilerDb` semantic `TypeId` resolution.
    pub inline fn isSemantic(self: UpgradeEngineTier) bool {
        return self == .tier3_semantic_modernizer;
    }
};

/// Language specification wave introducing a `corex upgrade` migration rule.
pub const UpgradeWave = enum(u8) {
    /// Phase 7.5 Language Ergonomics, Expressivity & Orthogonality Elevation (`DR-21`).
    dr21_phase75 = 21,
    /// Phase 7.6 Canonical Syntax Consolidation & Expressivity Elevation (`DR-22`).
    dr22_phase76 = 22,
    /// Phase 10.6 Syntactic Orthogonality, Doc-Comment Canonicalization & Zero-Legacy Purity (`DR-23`).
    dr23_phase106 = 23,

    /// Returns the canonical research specification identifier (`"DR-21"`, `"DR-22"`, or `"DR-23"`).
    pub inline fn asSpecCode(self: UpgradeWave) []const u8 {
        return switch (self) {
            .dr21_phase75 => "DR-21",
            .dr22_phase76 => "DR-22",
            .dr23_phase106 => "DR-23",
        };
    }
};

/// Contiguous 1-byte identifier for every canonical `corex upgrade` rule (`0..21`).
pub const UpgradeRuleId = enum(u8) {
    /// `UR-21-00`: Rewrites `::` path separators to `.` and root `std` module paths to `cx`.
    ur_21_00_path_coloncolon_and_std_root = 0,
    /// `UR-21-01`: Rewrites `if let $pat = $scrut $then` to `if $scrut is $pat $then`.
    ur_21_01_if_let_to_is_condition = 1,
    /// `UR-21-02`: Rewrites `while let $pat = $scrut $body` to `while $scrut is $pat $body`.
    ur_21_02_while_let_to_is_condition = 2,
    /// `UR-21-03`: Rewrites diverging `let .Some($id) = $expr else { $div; };` guards to `orelse`.
    ur_21_03_let_some_else_to_orelse = 3,
    /// `UR-21-04`: Lifts type-level generic arguments from `Type.fn[T](…)` to `Type[T].fn(…)`.
    ur_21_04_type_level_generic_args = 4,
    /// `UR-21-05`: Rewrites `$opt.unwrap_or($def)` and `$opt.unwrap()` to `orelse`.
    ur_21_05_option_unwrap_to_orelse = 5,
    /// `UR-21-06`: Rewrites `cx.mem.with_arena(&mut $arena, || $blk)` to `with context.allocator`.
    ur_21_06_with_arena_to_with_context = 6,
    /// `UR-21-07`: Rewrites `$s[$lo .. $s.len() - $k]` end-relative slice bounds to `$s[$lo..$-$k]`.
    ur_21_07_end_relative_dollar_slices = 7,
    /// `UR-22-00`: Rewrites `&&` to `and`, `@noalloc` to `@no_alloc`, `Numeric` to `Number`, and `\{`/`\}` to `{{`/`}}`.
    ur_22_00_lexical_token_canonicalization = 8,
    /// `UR-22-01`: Rewrites infix `||` to `or` (preserving closure `||`) and `let mut`/`var mut`/`mut $id` to `var`.
    ur_22_01_logical_or_and_var_bindings = 9,
    /// `UR-22-02`: Rewrites `ref`, `ref mut`, `inout`, `sink`, `set`, `own $id: $ty`, and `mut self` to `&`, `&mut`, `&out`, and `$id: own $ty`.
    ur_22_02_parameter_and_ownership_modes = 10,
    /// `UR-22-03`: Rewrites `Result[$ok, $err]` to `$ok!$err` and `Option[$t]` to `$t?` with precedence parens.
    ur_22_03_postfix_option_and_infix_result = 11,
    /// `UR-22-04`: Rewrites `@$attr($k = $v)` to `@$attr($k: $v)`, `bit_field $N: $U`, `enum $N: $I`, `,` fields, and omits `-> unit`.
    ur_22_04_attributes_enums_and_bitfields = 12,
    /// `UR-22-05`: Rewrites `*const $ty` to `*$ty`, `c_void` targets to `opaque`, `extern "c"` to `"C"`, and `@test fn` to `test "…"`.
    ur_22_05_ffi_pointers_and_prose_tests = 13,
    /// `UR-22-06`: Rewrites `!$e` to `not`/`~` by `TypeId`, prefix `*$p` to `$p.*`, and `.len`/`.ptr` to `.len()`/`.as_ptr()`.
    ur_22_06_semantic_unary_deref_and_slice_methods = 14,
    /// `UR-23-00`: Rewrites `/** … */` and `/*! … */` block doc comments to `///` or `//!` line docs (`E0118`).
    ur_23_00_block_doc_comments_to_line_docs = 15,
    /// `UR-23-01`: Hoists inline `mod` `//!` docs to outer `///`, downgrades mid-file `//!`, and attaches `///` (`E0229`, `E0230`).
    ur_23_01_doc_comment_placement_and_attachment = 16,
    /// `UR-23-02`: Rewrites `elif`, `elsif`, and `elseif` branch tokens to `"else if"` (`E0233`).
    ur_23_02_elif_to_else_if = 17,
    /// `UR-23-03`: Strips `[Vis]` on `impl` blocks and extracts inline nominal type methods into adjacent `impl` blocks (`E0231`, `E0232`).
    ur_23_03_impl_visibility_and_inline_type_methods = 18,
    /// `UR-23-04`: Rewrites wildcard `let _ =` / `var _ =` / `(_, _) =` and refines `unit` / `T!E` / `AutoDrop` discards (`E0234`–`E0439`).
    ur_23_04_canonical_wildcard_discard_stmt = 19,
    /// `UR-23-05`: Rewrites unambiguous `PascalCase` foreign scalar type names (`U32`, `Bool`, `Void`, …) to lowercase primitives (`E0403`).
    ur_23_05_foreign_scalar_type_names = 20,
    /// `UR-23-06`: Inserts missing `:` before type annotations in parameters, fields, closures, and bindings (`E0236`).
    ur_23_06_missing_colon_before_type = 21,

    /// Returns the dense zero-based catalog index (`0..21`) of `self`.
    pub inline fn asInt(self: UpgradeRuleId) u8 {
        return @backingInt(self);
    }

    /// Converts a dense zero-based index into an `UpgradeRuleId`, returning `null` if out of bounds.
    pub inline fn fromInt(raw_index: u8) ?UpgradeRuleId {
        if (raw_index >= UPGRADE_RULE_COUNT) return null;
        return @fromBackingInt(@intCast(raw_index));
    }

    /// Returns the static `UpgradeRuleDescriptor` metadata record for `self` in $O(1)$ time.
    pub inline fn asDescriptor(self: UpgradeRuleId) UpgradeRuleDescriptor {
        return UPGRADE_RULE_CATALOG[@backingInt(self)];
    }

    /// Returns the canonical `"UR-XX-YY"` rule code string for `self` in $O(1)$ time.
    pub inline fn asRuleCode(self: UpgradeRuleId) []const u8 {
        return self.asDescriptor().rule_code;
    }
};

/// Static metadata record describing a single `corex upgrade` transformation rule.
pub const UpgradeRuleDescriptor = struct {
    /// Strongly typed contiguous rule enum tag (`0..21`).
    id: UpgradeRuleId,
    /// Canonical external rule code (`"UR-21-00"`–`"UR-23-06"`).
    rule_code: []const u8,
    /// Specification wave (`DR-21`, `DR-22`, or `DR-23`) that defined this migration rule.
    wave: UpgradeWave,
    /// Execution engine tier (`Tier 1`, `Tier 2`, or `Tier 3`).
    tier: UpgradeEngineTier,
    /// Intra-pass transactional precedence (`100` highest down to `50` semantic modernizers).
    priority: u8,
    /// `TransactionalPatcher` conflict-resolution category.
    edit_priority: EditPriority,
    /// Confidence classification (`machine_applicable` for deterministic syntax/type migrations).
    applicability: FixApplicability,
    /// True if retiring rejected legacy syntax; false if modernizing valid but verbose idioms.
    is_mandatory_syntax: bool,
    /// Primary compiler error code emitted when un-upgraded code is fed directly to `corex check`.
    related_diagnostic: ?DiagnosticCode,
    /// Concise single-line summary rendered in `corex upgrade --list` and diagnostic hints.
    summary: []const u8,
};

// --------------------------------------- CONSTS ----------------------------------------

// ------------------------ Rule Catalog ------------------------

/// Total number of canonical `corex upgrade` rules across `DR-21` (`8`), `DR-22` (`7`), and `DR-23` (`7`).
pub const UPGRADE_RULE_COUNT: usize = 22;

/// Maximum multi-pass fixed-point synergy iterations executed by `corex upgrade` (`DR-21` §3.3).
pub const MAX_SYNERGY_PASSES: u8 = 4;

/// Canonical dense metadata table indexed directly by `@intFromEnum(UpgradeRuleId)`.
pub const UPGRADE_RULE_CATALOG: [UPGRADE_RULE_COUNT]UpgradeRuleDescriptor = .{
    // `DR-21` §3.3 (`UR-21-00`–`UR-21-07`):
    .{
        .id = .ur_21_00_path_coloncolon_and_std_root,
        .rule_code = "UR-21-00",
        .wave = .dr21_phase75,
        .tier = .tier1_token_shim,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0112_retired_path_separator,
        .summary = "Rewrite retired '::' path separators to '.' and root 'std' module paths to 'cx' before CST parsing.",
    },
    .{
        .id = .ur_21_01_if_let_to_is_condition,
        .rule_code = "UR-21-01",
        .wave = .dr21_phase75,
        .tier = .tier2_cst_pattern,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0216_retired_if_while_let,
        .summary = "Rewrite 'if let $pat = $scrut $then' to 'if $scrut is $pat $then' (parenthesizing trailing struct patterns).",
    },
    .{
        .id = .ur_21_02_while_let_to_is_condition,
        .rule_code = "UR-21-02",
        .wave = .dr21_phase75,
        .tier = .tier2_cst_pattern,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0216_retired_if_while_let,
        .summary = "Rewrite 'while let $pat = $scrut $body' to 'while $scrut is $pat $body'.",
    },
    .{
        .id = .ur_21_03_let_some_else_to_orelse,
        .rule_code = "UR-21-03",
        .wave = .dr21_phase75,
        .tier = .tier2_cst_pattern,
        .priority = 100,
        .edit_priority = .lint_idiom,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = false,
        .related_diagnostic = null,
        .summary = "Condense single-statement diverging 'let .Some($id) = $expr else { $div; };' guards to 'orelse $div;'.",
    },
    .{
        .id = .ur_21_04_type_level_generic_args,
        .rule_code = "UR-21-04",
        .wave = .dr21_phase75,
        .tier = .tier3_semantic_modernizer,
        .priority = 50,
        .edit_priority = .type_migration,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = null,
        .summary = "Lift nominal type generic arguments from 'Type.assoc_fn[Args](…)' to 'Type[Args].assoc_fn(…)'.",
    },
    .{
        .id = .ur_21_05_option_unwrap_to_orelse,
        .rule_code = "UR-21-05",
        .wave = .dr21_phase75,
        .tier = .tier3_semantic_modernizer,
        .priority = 50,
        .edit_priority = .lint_idiom,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = false,
        .related_diagnostic = null,
        .summary = "Modernize '$opt.unwrap_or($def)' to '$opt orelse $def' and '$opt.unwrap()' to '$opt orelse unreachable'.",
    },
    .{
        .id = .ur_21_06_with_arena_to_with_context,
        .rule_code = "UR-21-06",
        .wave = .dr21_phase75,
        .tier = .tier3_semantic_modernizer,
        .priority = 50,
        .edit_priority = .lint_idiom,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = false,
        .related_diagnostic = null,
        .summary = "Rewrite 'cx.mem.with_arena(&mut $arena, || $blk)' to 'with context.allocator = &mut $arena $blk'.",
    },
    .{
        .id = .ur_21_07_end_relative_dollar_slices,
        .rule_code = "UR-21-07",
        .wave = .dr21_phase75,
        .tier = .tier3_semantic_modernizer,
        .priority = 50,
        .edit_priority = .lint_idiom,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = false,
        .related_diagnostic = .e0416_invalid_dollar_length_expr,
        .summary = "Modernize pure slice tail bounds '$s[$lo .. $s.len() - $k]' to end-relative '$s[$lo..$-$k]'.",
    },

    // `DR-22` §3.4 (`UR-22-00`–`UR-22-06`):
    .{
        .id = .ur_22_00_lexical_token_canonicalization,
        .rule_code = "UR-22-00",
        .wave = .dr22_phase76,
        .tier = .tier1_token_shim,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0113_retired_logical_and,
        .summary = "Rewrite '&&' to 'and', '@noalloc' to '@no_alloc', 'Numeric' to 'Number', and '\\{'/'\\}' to '{{'/'}}' before CST parsing.",
    },
    .{
        .id = .ur_22_01_logical_or_and_var_bindings,
        .rule_code = "UR-22-01",
        .wave = .dr22_phase76,
        .tier = .tier2_cst_pattern,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0219_retired_logical_or,
        .summary = "Rewrite infix '||' to 'or' (preserving closure '||') and 'let mut'/'var mut'/pattern 'mut $id' to 'var'.",
    },
    .{
        .id = .ur_22_02_parameter_and_ownership_modes,
        .rule_code = "UR-22-02",
        .wave = .dr22_phase76,
        .tier = .tier2_cst_pattern,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0221_retired_mutability_or_param_mode,
        .summary = "Rewrite 'ref', 'ref mut', 'inout', 'sink', 'set', 'own $id: $ty', and 'mut self' to '&', '&mut', '&out', and '$id: own $ty'.",
    },
    .{
        .id = .ur_22_03_postfix_option_and_infix_result,
        .rule_code = "UR-22-03",
        .wave = .dr22_phase76,
        .tier = .tier2_cst_pattern,
        .priority = 95,
        .edit_priority = .type_migration,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = false,
        .related_diagnostic = .e0222_chained_result_type,
        .summary = "Rewrite 'Result[$ok, $err]' to '$ok!$err' and 'Option[$t]' to '$t?' with precedence-preserving parentheses.",
    },
    .{
        .id = .ur_22_04_attributes_enums_and_bitfields,
        .rule_code = "UR-22-04",
        .wave = .dr22_phase76,
        .tier = .tier2_cst_pattern,
        .priority = 90,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0223_retired_attribute_eq,
        .summary = "Rewrite '@$attr($k = $v)' to '@$attr($k: $v)', 'bit_field $N: $U', 'enum $N: $I', ',' fields, and omit '-> unit'.",
    },
    .{
        .id = .ur_22_05_ffi_pointers_and_prose_tests,
        .rule_code = "UR-22-05",
        .wave = .dr22_phase76,
        .tier = .tier2_cst_pattern,
        .priority = 90,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0226_retired_const_raw_ptr,
        .summary = "Rewrite '*const $ty' to '*$ty', 'c_void' targets to 'opaque', " ++
            "'extern \"c\"' to 'extern \"C\"', and '@test fn' to 'test \"…\"'.",
    },
    .{
        .id = .ur_22_06_semantic_unary_deref_and_slice_methods,
        .rule_code = "UR-22-06",
        .wave = .dr22_phase76,
        .tier = .tier3_semantic_modernizer,
        .priority = 50,
        .edit_priority = .type_migration,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0227_retired_prefix_deref,
        .summary = "Rewrite '!$e' to 'not $e' or '~$e' by TypeId, prefix '*$p' to '$p.*', and '.len'/'.ptr' to '.len()'/'.as_ptr()'.",
    },

    // `DR-23` §3.1 (`UR-23-00`–`UR-23-06`):
    .{
        .id = .ur_23_00_block_doc_comments_to_line_docs,
        .rule_code = "UR-23-00",
        .wave = .dr23_phase106,
        .tier = .tier1_token_shim,
        .priority = 100,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0118_block_doc_comment_forbidden,
        .summary = "Rewrite '/** … */' and '/*! … */' block doc comments to '///' or '//!' line doc comments.",
    },
    .{
        .id = .ur_23_01_doc_comment_placement_and_attachment,
        .rule_code = "UR-23-01",
        .wave = .dr23_phase106,
        .tier = .tier2_cst_pattern,
        .priority = 98,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0229_misplaced_module_doc_comment,
        .summary = "Hoist inline 'mod' '//!' docs to outer '///', downgrade mid-file '//!', and strip blank lines after '///'.",
    },
    .{
        .id = .ur_23_02_elif_to_else_if,
        .rule_code = "UR-23-02",
        .wave = .dr23_phase106,
        .tier = .tier1_token_shim,
        .priority = 96,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0233_invalid_elif_keyword,
        .summary = "Rewrite foreign 'elif', 'elsif', and 'elseif' branch keywords to 'else if'.",
    },
    .{
        .id = .ur_23_03_impl_visibility_and_inline_type_methods,
        .rule_code = "UR-23-03",
        .wave = .dr23_phase106,
        .tier = .tier2_cst_pattern,
        .priority = 92,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0231_visibility_on_impl_block,
        .summary = "Strip visibility modifiers on 'impl' blocks and extract inline methods from type bodies into adjacent 'impl' blocks.",
    },
    .{
        .id = .ur_23_04_canonical_wildcard_discard_stmt,
        .rule_code = "UR-23-04",
        .wave = .dr23_phase106,
        .tier = .tier3_semantic_modernizer,
        .priority = 90,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0234_non_binding_wildcard_let_var,
        .summary = "Rewrite 'let _ = $e;', 'var _ = $e;', and '(_, _) = $e;' to '_ = $e;' and refine 'unit', 'T!E', and 'AutoDrop' discards.",
    },
    .{
        .id = .ur_23_05_foreign_scalar_type_names,
        .rule_code = "UR-23-05",
        .wave = .dr23_phase106,
        .tier = .tier3_semantic_modernizer,
        .priority = 50,
        .edit_priority = .type_migration,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0403_unresolved_symbol,
        .summary = "Rewrite unambiguous foreign scalar type names ('U32', 'UInt32', 'Bool', 'Void', …) to lowercase CoreX primitives.",
    },
    .{
        .id = .ur_23_06_missing_colon_before_type,
        .rule_code = "UR-23-06",
        .wave = .dr23_phase106,
        .tier = .tier2_cst_pattern,
        .priority = 85,
        .edit_priority = .syntax_canonicalization,
        .applicability = .machine_applicable,
        .is_mandatory_syntax = true,
        .related_diagnostic = .e0236_missing_colon_before_type,
        .summary = "Insert missing ':' between identifiers and type annotations in parameters, fields, closures, and local bindings.",
    },
};

/// Static $O(1)$ lookup table mapping canonical `"UR-XX-YY"` strings to `UpgradeRuleId`.
const RULE_CODE_MAP = std.StaticStringMap(UpgradeRuleId).initComptime(.{
    .{ "UR-21-00", .ur_21_00_path_coloncolon_and_std_root },
    .{ "UR-21-01", .ur_21_01_if_let_to_is_condition },
    .{ "UR-21-02", .ur_21_02_while_let_to_is_condition },
    .{ "UR-21-03", .ur_21_03_let_some_else_to_orelse },
    .{ "UR-21-04", .ur_21_04_type_level_generic_args },
    .{ "UR-21-05", .ur_21_05_option_unwrap_to_orelse },
    .{ "UR-21-06", .ur_21_06_with_arena_to_with_context },
    .{ "UR-21-07", .ur_21_07_end_relative_dollar_slices },
    .{ "UR-22-00", .ur_22_00_lexical_token_canonicalization },
    .{ "UR-22-01", .ur_22_01_logical_or_and_var_bindings },
    .{ "UR-22-02", .ur_22_02_parameter_and_ownership_modes },
    .{ "UR-22-03", .ur_22_03_postfix_option_and_infix_result },
    .{ "UR-22-04", .ur_22_04_attributes_enums_and_bitfields },
    .{ "UR-22-05", .ur_22_05_ffi_pointers_and_prose_tests },
    .{ "UR-22-06", .ur_22_06_semantic_unary_deref_and_slice_methods },
    .{ "UR-23-00", .ur_23_00_block_doc_comments_to_line_docs },
    .{ "UR-23-01", .ur_23_01_doc_comment_placement_and_attachment },
    .{ "UR-23-02", .ur_23_02_elif_to_else_if },
    .{ "UR-23-03", .ur_23_03_impl_visibility_and_inline_type_methods },
    .{ "UR-23-04", .ur_23_04_canonical_wildcard_discard_stmt },
    .{ "UR-23-05", .ur_23_05_foreign_scalar_type_names },
    .{ "UR-23-06", .ur_23_06_missing_colon_before_type },
});

// -------------------------------------- INTERNALS --------------------------------------

// -------------------- Catalog Verification --------------------

/// Compile-time drift guard verifying 1:1 index parity between `UpgradeRuleId`, `UPGRADE_RULE_CATALOG`, and `RULE_CODE_MAP`.
fn verifyCatalogInvariantsComptime() void {
    @setEvalBranchQuota(8_192);
    std.debug.assert(std.enums.values(UpgradeRuleId).len == UPGRADE_RULE_COUNT);
    std.debug.assert(UPGRADE_RULE_CATALOG.len == UPGRADE_RULE_COUNT);

    for (UPGRADE_RULE_CATALOG, 0..) |entry, i| {
        std.debug.assert(@backingInt(entry.id) == i);
        std.debug.assert(entry.rule_code.len == 8);
        std.debug.assert(entry.summary.len > 0);
        std.debug.assert(entry.priority >= 50 and entry.priority <= 100);
        std.debug.assert(RULE_CODE_MAP.get(entry.rule_code).? == entry.id);
    }
}

comptime {
    verifyCatalogInvariantsComptime();
}

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------------- Lookup Helpers -----------------------

/// Resolves a canonical `"UR-XX-YY"` rule code string to its `UpgradeRuleId` in $O(1)$ time.
pub inline fn lookupUpgradeRule(rule_code: []const u8) ?UpgradeRuleId {
    return RULE_CODE_MAP.get(rule_code);
}

/// Resolves a canonical `"UR-XX-YY"` rule code string directly to its `UpgradeRuleDescriptor` in $O(1)$ time.
pub inline fn resolveUpgradeRuleDescriptor(rule_code: []const u8) ?UpgradeRuleDescriptor {
    return (RULE_CODE_MAP.get(rule_code) orelse return null).asDescriptor();
}

// ------------------------- Unit Tests -------------------------

test "test_upgrade_rule_catalog_dr21_dr22_and_dr23_parity_and_o1_lookup" {
    try std.testing.expectEqual(@as(usize, 22), UPGRADE_RULE_CATALOG.len);
    try std.testing.expectEqual(@as(u8, 4), MAX_SYNERGY_PASSES);

    var dr21_count: usize = 0;
    var dr22_count: usize = 0;
    var dr23_count: usize = 0;
    var tier1_count: usize = 0;
    var tier2_count: usize = 0;
    var tier3_count: usize = 0;

    for (UPGRADE_RULE_CATALOG, 0..) |descriptor, i| {
        const roundtrip_id = UpgradeRuleId.fromInt(@intCast(i)).?;
        try std.testing.expectEqual(descriptor.id, roundtrip_id);
        try std.testing.expectEqual(descriptor.id, lookupUpgradeRule(descriptor.rule_code).?);
        try std.testing.expectEqualStrings(descriptor.rule_code, descriptor.id.asRuleCode());
        try std.testing.expectEqual(
            descriptor.id,
            resolveUpgradeRuleDescriptor(descriptor.rule_code).?.id,
        );

        switch (descriptor.wave) {
            .dr21_phase75 => {
                dr21_count += 1;
                try std.testing.expectEqualStrings("DR-21", descriptor.wave.asSpecCode());
            },
            .dr22_phase76 => {
                dr22_count += 1;
                try std.testing.expectEqualStrings("DR-22", descriptor.wave.asSpecCode());
            },
            .dr23_phase106 => {
                dr23_count += 1;
                try std.testing.expectEqualStrings("DR-23", descriptor.wave.asSpecCode());
            },
        }
        switch (descriptor.tier) {
            .tier1_token_shim => {
                tier1_count += 1;
                try std.testing.expect(!descriptor.tier.isSemantic());
                try std.testing.expectEqual(@as(u8, 1), descriptor.tier.asNumber());
            },
            .tier2_cst_pattern => {
                tier2_count += 1;
                try std.testing.expect(!descriptor.tier.isSemantic());
                try std.testing.expectEqual(@as(u8, 2), descriptor.tier.asNumber());
            },
            .tier3_semantic_modernizer => {
                tier3_count += 1;
                try std.testing.expect(descriptor.tier.isSemantic());
                try std.testing.expectEqual(@as(u8, 3), descriptor.tier.asNumber());
            },
        }
    }

    try std.testing.expectEqual(@as(usize, 8), dr21_count);
    try std.testing.expectEqual(@as(usize, 7), dr22_count);
    try std.testing.expectEqual(@as(usize, 7), dr23_count);
    try std.testing.expectEqual(@as(usize, 4), tier1_count);
    try std.testing.expectEqual(@as(usize, 11), tier2_count);
    try std.testing.expectEqual(@as(usize, 7), tier3_count);

    try std.testing.expectEqual(@as(?UpgradeRuleId, null), UpgradeRuleId.fromInt(22));
    try std.testing.expectEqual(@as(?UpgradeRuleId, null), lookupUpgradeRule("UR-99-99"));
    try std.testing.expectEqual(@as(?UpgradeRuleDescriptor, null), resolveUpgradeRuleDescriptor(""));

    // Spot-check key `DR-22` §3.4 and `DR-23` §3.1 diagnostic associations and priorities:
    const ur2200 = lookupUpgradeRule("UR-22-00").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0113_retired_logical_and, ur2200.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 100), ur2200.priority);

    const ur2203 = lookupUpgradeRule("UR-22-03").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0222_chained_result_type, ur2203.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 95), ur2203.priority);

    const ur2206 = lookupUpgradeRule("UR-22-06").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0227_retired_prefix_deref, ur2206.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 50), ur2206.priority);

    const ur2300 = lookupUpgradeRule("UR-23-00").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0118_block_doc_comment_forbidden, ur2300.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 100), ur2300.priority);

    const ur2304 = lookupUpgradeRule("UR-23-04").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0234_non_binding_wildcard_let_var, ur2304.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 90), ur2304.priority);

    const ur2305 = lookupUpgradeRule("UR-23-05").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0403_unresolved_symbol, ur2305.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 50), ur2305.priority);

    const ur2306 = lookupUpgradeRule("UR-23-06").?.asDescriptor();
    try std.testing.expectEqual(DiagnosticCode.e0236_missing_colon_before_type, ur2306.related_diagnostic.?);
    try std.testing.expectEqual(@as(u8, 85), ur2306.priority);
}

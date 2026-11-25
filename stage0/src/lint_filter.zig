//! Lint Rule Registry – Four-Scope Suppression Matcher and Stale-Expect Filter (`DR-25`)
//!
//! Provides $O(1)$ bitmask fast-path and $O(\log K)$ laminar interval matching over `TokenBuffer`,
//! `LosslessCstArena`, and `LineIndex`, plus surgical `W0002` (`unused-suppression`), `W0003`
//! (`missing-suppression-reason`), `W0004` (`prefer-expect-over-allow`), and above-line `W0202`
//! (`non-idiomatic-syntax`) extraction and auto-fix synthesis.
//!
//! All 44 v1.0 built-in lint rules (`RuleId` `0..43`) fit in a single `RuleMask64` (`u64`) and emit
//! `Severity.warning`. `SuppressionTable` is 100% immutable across `project_file_diagnostics` runs;
//! mutable fulfillment state uses scratch-allocated bitmasks so `CompilerDb` memos stay thread-safe.

const std = @import("std");
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const mem = @import("mem_foundation.zig");
const vfs = @import("vfs_sourcemap.zig");
const syn = @import("syntax_arenas.zig");
const diag = @import("diag/diagnostic.zig");
const unicode_confusables = @import("unicode_confusables.zig");

pub const FileId = mem.FileId;
pub const StringId = mem.StringId;
pub const Span = mem.Span;
pub const StringInterner = mem.StringInterner;
pub const LineIndex = vfs.LineIndex;
pub const TokenIndex = mem.TokenIndex;
pub const CstNodeIndex = mem.CstNodeIndex;
pub const TokenKind = syn.TokenKind;
pub const TokenBuffer = syn.TokenBuffer;
pub const TriviaKind = syn.TriviaKind;
pub const TriviaPiece = syn.TriviaPiece;
pub const LosslessCstArena = syn.LosslessCstArena;
pub const Diagnostic = diag.Diagnostic;
pub const DiagnosticCode = diag.DiagnosticCode;
pub const DiagnosticSink = diag.DiagnosticSink;
pub const LabeledSpan = diag.LabeledSpan;
pub const TextEdit = diag.TextEdit;
pub const EditPriority = diag.EditPriority;
pub const FixApplicability = diag.FixApplicability;
pub const SuggestedFix = diag.SuggestedFix;
pub const RuleId = diag.RuleId;
pub const RuleMask64 = diag.RuleMask64;
pub const ALL_RULES_MASK = diag.ALL_RULES_MASK;

// ---------------------------------------- TYPES ----------------------------------------

/// Suppression directive mode (`expect` warns `W0002` if unfulfilled; `allow` stays silent).
pub const DirectiveMode = enum(u1) {
    /// Unconditional scoped suppression (`@allow` / `allow(…)` / `file-allow(…)`).
    allow = 0,
    /// Self-cleaning expectation (`@expect` / `expect(…)` / `file-expect(…)`; warns `W0002` when unfulfilled).
    expect = 1,
};

/// Exact 12-byte selector item slice inside a multi-rule `@expect(r1, r2)` or `// corex check:` list.
pub const SelectorItemSpan = extern struct {
    /// Inclusive start byte covering this rule selector plus any leading `, ` for surgical pruning.
    prune_start_byte: u32,
    /// Exclusive end byte covering this rule selector plus any trailing `, ` for surgical pruning.
    prune_end_byte: u32,
    /// Matched built-in lint rule identifier (`0..43`).
    rule_id: RuleId,
    /// Byte delta from `prune_start_byte` to the selector text itself (`0` unless leading `, ` is pruned).
    sel_offset_from_prune: u8 = 0,
    /// Exact byte length of the selector token(s) (`W0xxx` or `kebab-case` slug).
    sel_byte_len: u8 = 0,
    /// Explicit zero byte maintaining `12`-byte `extern struct` layout (`align(4)`).
    _pad: u8 = 0,

    /// Reconstructs the primary `Span` underlining only the selector text (`unused-binding` or `W0402`).
    pub inline fn selectorSpan(self: SelectorItemSpan, file_id: FileId) Span {
        const start_b = self.prune_start_byte + @as(u32, self.sel_offset_from_prune);
        const end_b = if (self.sel_byte_len > 0)
            start_b + @as(u32, self.sel_byte_len)
        else
            self.prune_end_byte;
        return Span.init(file_id, start_b, end_b);
    }
};

/// Raw Scope-3 AST suppression input collected during `buildSuppressionTable` / `extractFileSuppressionTable`.
pub const RawAstSuppression = struct {
    /// Half-open byte interval `[target_start_byte, target_end_byte)` of the decorated AST/CST subtree.
    target_start_byte: u32,
    /// Exclusive end byte of the decorated AST/CST subtree.
    target_end_byte: u32,
    /// Full removal start byte of the `@expect(…)` / `@allow(…)` attribute for `W0002` `--fix`.
    directive_remove_start: u32,
    /// Full removal exclusive end byte of the attribute (including line break when standalone).
    directive_remove_end: u32,
    /// Start byte of the `@expect` / `@allow` header span for `W0002` / `W0003` primary underlines.
    directive_head_start: u32 = 0,
    /// Exclusive end byte of the `@expect` / `@allow` header span.
    directive_head_end: u32 = 0,
    /// Start byte of the `allow` keyword token inside `@allow` (`0` when `mode == .expect`).
    allow_kw_start: u32 = 0,
    /// Exclusive end byte of the `allow` keyword token (`0` when `mode == .expect`).
    allow_kw_end: u32 = 0,
    /// Half-open byte range `[reason_start, reason_end)` of the author's rationale (`0..0` if omitted).
    reason_start: u32 = 0,
    /// Exclusive end byte of the rationale payload.
    reason_end: u32 = 0,
    /// Bitmask of lint rules directly listed on this attribute.
    own_mask: RuleMask64,
    /// Starting index inside `SuppressionTable.selectors`.
    selector_slice_start: u16,
    /// Count of `SelectorItemSpan` entries belonging to this attribute.
    selector_count: u8,
    /// Suppression mode (`.allow` vs `.expect`).
    mode: DirectiveMode,
    /// Deterministic CST pre-order tie-breaker when two attributes share `[target_start, target_end)`.
    decl_order: u16,
    /// `true` when the owning CST construct also carries `@cfg(…)` (exempts `W0004`).
    has_sibling_cfg: bool = false,
    /// `true` when synthesized from a standalone above-line `// corex check:` comment (`Ruling 3.3`).
    is_above_line_comment: bool = false,
};

/// Structure-of-Arrays node in the sorted Scope-3 Laminar AST Interval Tree (`DR-25` §4.2).
pub const LaminarAstSpan = struct {
    /// Inclusive start byte of the decorated AST/CST subtree.
    start_byte: u32,
    /// Exclusive end byte of the decorated AST/CST subtree.
    end_byte: u32,
    /// Full removal start byte of the `@expect` / `@allow` attribute.
    directive_remove_start: u32,
    /// Full removal exclusive end byte of the attribute.
    directive_remove_end: u32,
    /// Header start byte (`@expect` / `@allow`) for `W0002` / `W0003` underlines.
    directive_head_start: u32,
    /// Header exclusive end byte.
    directive_head_end: u32,
    /// `allow` keyword start byte for `W0004` `allow` -> `expect` auto-fix.
    allow_kw_start: u32,
    /// `allow` keyword exclusive end byte.
    allow_kw_end: u32,
    /// Inclusive start byte of the unquoted `reason` text (`0` if omitted).
    reason_start: u32,
    /// Exclusive end byte of the unquoted `reason` text (`0` if omitted).
    reason_end: u32,
    /// Rules directly listed on this attribute.
    own_mask: RuleMask64,
    /// Pre-unioned mask of `own_mask` across `self` and all enclosing `parent_idx` ancestors.
    eff_mask: RuleMask64,
    /// Immediate enclosing laminar parent index (`SuppressionTable.NONE_IDX` when root).
    parent_idx: u16,
    /// Starting offset in `SuppressionTable.selectors`.
    selector_slice_start: u16,
    /// Count of selector items in `SuppressionTable.selectors`.
    selector_count: u8,
    /// Suppression mode (`.allow` vs `.expect`).
    mode: DirectiveMode,
    /// `true` when the owning CST node carries `@cfg(…)` (exempts `W0004`).
    has_sibling_cfg: bool,
    /// `true` when synthesized from an above-line `// corex check:` comment during Pass 1.
    is_above_line_comment: bool,
};

/// Exact 40-byte mutually disjoint Scope-2 preamble or Scope-4 trailing-line directive (`DR-25` §4.2).
pub const DisjointLineSpan = extern struct {
    /// Inclusive start byte of the governed physical source line.
    line_start_byte: u32,
    /// Exclusive end byte of the governed physical source line.
    line_end_byte: u32,
    /// Inclusive start byte of the full directive deletion span for `W0002` `--fix`.
    directive_remove_start: u32,
    /// Exclusive end byte of the full directive deletion span.
    directive_remove_end: u32,
    /// Inclusive start byte of `-- <reason>` text (`0` if omitted).
    reason_start: u32,
    /// Exclusive end byte of `-- <reason>` text (`0` if omitted).
    reason_end: u32,
    /// Bitmask of lint rules listed on this directive.
    own_mask: RuleMask64,
    /// Starting offset in `SuppressionTable.selectors`.
    selector_slice_start: u16,
    /// Count of selector items in `SuppressionTable.selectors`.
    selector_count: u8,
    /// Encoded `DirectiveMode` (`0` = `allow`, `1` = `expect`).
    mode: u8,
    /// Byte offset from `directive_remove_start` to the `allow` keyword (`0` when `mode == 1`).
    allow_kw_offset: u16 = 0,
    /// Byte offset from `directive_remove_start` to the `//` comment start (`0` on full-line preamble).
    comment_start_offset: u16 = 0,
};

/// Compact 24-byte configuration-oblivious lint fact cached by upstream `CompilerDb` stages (`DR-25` §4.2).
pub const RawLintCandidate = extern struct {
    /// Built-in lint rule identifier (`0..43`).
    rule_id: RuleId,
    /// Rule-specific auto-fix variant tag (`0` = diagnostic-only).
    fix_kind: u8 = 0,
    /// Compact 16-bit auxiliary token/offset/count payload.
    aux_u16: u16 = 0,
    /// Inclusive start byte in `FileId`.
    start_byte: u32,
    /// Exclusive end byte in `FileId`.
    end_byte: u32,
    /// Originating `NodeIndex`, `TokenIndex`, or `SymbolIndex` payload.
    node_or_tok: u32 = 0,
    /// Secondary span or extended 64-bit payload for lazy `SuggestedFix` synthesis.
    aux_payload: u64 = 0,
};

/// Precompiled per-file 8-byte disabled-rule bitmask resolved from `LintDisabledMatrix` (`0` = all 44 enabled).
pub const EffectiveFileRules = extern struct {
    /// Union of disabled `RuleId` bits from `corex.toml`, `[[lint.overrides]]`, and CLI `--disable`/`--only`.
    disabled_mask: RuleMask64 = 0,

    /// Returns `true` when `rule` is active (`Severity.warning`) for this file in $O(1)$ time.
    pub inline fn isEnabled(self: EffectiveFileRules, rule: RuleId) bool {
        return (self.disabled_mask & rule.bit()) == 0;
    }
};

/// Kind of syntax/selector `E0240` error detected inside a `// corex check:` comment directive.
pub const CommentDirectiveErrorKind = enum(u8) {
    /// Unrecognized directive action name outside `{expect, allow, file-expect, file-allow}`.
    unknown_action,
    /// Missing parenthesized `(…)` rule selector list after the directive action.
    missing_parens,
    /// Empty `()` rule selector list with zero rule identifiers.
    empty_selector_list,
    /// Forbidden `*` wildcard rule selector.
    wildcard_forbidden,
    /// Forbidden category-wide (`style`, `lint`, `W02xx`) or blanket (`all`, `warnings`) selector.
    category_or_blanket_forbidden,
    /// Non-suppressible `E0xxx` compiler error code passed to a lint directive.
    non_suppressible_error_code,
    /// Warning code outside the 44 suppressible `DR-25` lint rules (e.g., `W0002`–`W0004`).
    non_suppressible_warning_code,
    /// Malformed `kebab-case` rule slug containing whitespace around `-`.
    spaced_hyphen_in_slug,
    /// Unknown `W0xxx` code or `kebab-case` lint rule slug (eligible for typo suggestion).
    unknown_lint_rule,
};

/// Deferred `E0240` diagnostic record captured while scanning `// corex check:` trivia comments.
pub const DirectiveErrorRecord = struct {
    /// Source byte range of the offending directive action or selector.
    start_byte: u32,
    /// Exclusive end byte of the offending directive action or selector.
    end_byte: u32,
    /// Specific `E0240` failure classification.
    kind: CommentDirectiveErrorKind,
};

/// Misplaced mid-file `// corex check: file-expect(…)` / `file-allow(…)` record (`W0002` auto-prune).
pub const MidFileDirectiveRecord = struct {
    /// Start byte of the `// corex check: file-*` comment for primary `W0002` underline.
    comment_start_byte: u32,
    /// Exclusive end byte of the comment.
    comment_end_byte: u32,
    /// Full removal start byte (line start when standalone, or preceding spaces when trailing).
    remove_start_byte: u32,
    /// Full removal exclusive end byte (including newline when standalone).
    remove_end_byte: u32,
    /// `true` for `file-expect`, `false` for `file-allow`.
    is_file_expect: bool,
};

/// Standalone above-line `// corex check: expect(…)` / `allow(…)` record (`W0202` hoist below `/|` docs).
pub const AboveLineHoistRecord = struct {
    /// Start byte of the standalone `// corex check:` comment.
    comment_start_byte: u32,
    /// Exclusive end byte of the standalone `// corex check:` comment.
    comment_end_byte: u32,
    /// Inclusive start byte of the comment's physical line (`delete` start when hoisting across `/|`).
    comment_line_start: u32,
    /// Exclusive end byte of the comment's physical line including `\r?\n` (`delete` end across `/|`).
    comment_line_next_start: u32,
    /// Inclusive start byte of the target item/stmt line below any `/|` docstrings.
    target_line_start: u32,
    /// Start byte of target token on `target_line_start` (`target_line_start .. target_tok_start` = indent).
    target_tok_start: u32,
    /// Start byte of raw `<selectors>` slice inside `expect(<selectors>)` / `allow(<selectors>)`.
    selectors_raw_start: u32,
    /// Exclusive end byte of raw `<selectors>` slice.
    selectors_raw_end: u32,
    /// Start byte of `-- <reason>` slice (`0` if omitted).
    reason_start: u32,
    /// Exclusive end byte of `-- <reason>` slice (`0` if omitted).
    reason_end: u32,
    /// `true` when `/|` docstrings sit between the comment and its target construct (`2`-edit hoist).
    has_intervening_doc_comments: bool,
    /// `true` when target construct carries `@cfg(…)` (keeps `@allow` instead of hoisting to `@expect`).
    target_has_cfg: bool,
    /// Original directive mode written in the comment.
    original_mode: DirectiveMode,
};

/// Immutable per-`FileId` Four-Scope Suppression Table memoized at `QueryStage.suppression_table`.
pub const SuppressionTable = struct {
    /// Sentinel `u16` index indicating no enclosing laminar AST parent.
    pub const NONE_IDX: u16 = 0xFFFF;

    /// Owning source file handle.
    file_id: FileId = .none,
    /// `true` when the file preamble or root item carries `@generated` / `Code generated … DO NOT EDIT`.
    is_generated_file: bool = false,
    /// $O(1)$ union of all rules mentioned in `file_*`, `ast_spans`, and `line_spans`.
    any_suppressed_mask: RuleMask64 = 0,
    /// Scope-2 whole-file preamble `file-allow` bitmask.
    file_allow_mask: RuleMask64 = 0,
    /// Scope-2 whole-file preamble `file-expect` bitmask.
    file_expect_mask: RuleMask64 = 0,
    /// Scope-2 preamble directives preserved for `W0002` / `W0003` auditing.
    file_directives: []const DisjointLineSpan = &.{},
    /// Scope-3 Laminar AST intervals sorted by `(start_byte ASC, end_byte DESC, decl_order ASC)`.
    ast_spans: std.MultiArrayList(LaminarAstSpan) = .empty,
    /// Scope-4 mutually disjoint physical-line spans sorted by `line_start_byte ASC`.
    line_spans: []const DisjointLineSpan = &.{},
    /// Contiguous pool of per-rule selector spans for surgical multi-rule `W0002` `--fix` edits.
    selectors: []const SelectorItemSpan = &.{},
    /// Malformed `// corex check:` comment directive errors (`E0240`).
    directive_errors: []const DirectiveErrorRecord = &.{},
    /// Mid-file `file-expect` / `file-allow` directives (`W0002`).
    mid_file_directives: []const MidFileDirectiveRecord = &.{},
    /// Standalone above-line `// corex check:` directives (`W0202` hoist below `/|`).
    above_line_hoists: []const AboveLineHoistRecord = &.{},

    /// Releases all heap slices owned by `SuppressionTable`.
    pub fn deinit(self: *SuppressionTable, allocator: Allocator) void {
        self.ast_spans.deinit(allocator);
        if (self.file_directives.len > 0) allocator.free(self.file_directives);
        if (self.line_spans.len > 0) allocator.free(self.line_spans);
        if (self.selectors.len > 0) allocator.free(self.selectors);
        if (self.directive_errors.len > 0) allocator.free(self.directive_errors);
        if (self.mid_file_directives.len > 0) allocator.free(self.mid_file_directives);
        if (self.above_line_hoists.len > 0) allocator.free(self.above_line_hoists);
        self.* = .{};
    }
};

/// Mutable per-projection fulfillment state allocated in scratch memory during `project_file_diagnostics`.
pub const FulfillmentTracker = struct {
    /// Fulfilled rule bits across Scope-2 `file_directives`.
    file_fulfilled_mask: RuleMask64 = 0,
    /// Per-span fulfilled rule bits across Scope-3 `SuppressionTable.ast_spans`.
    ast_fulfilled: []RuleMask64,
    /// Per-line fulfilled rule bits across Scope-4 `SuppressionTable.line_spans`.
    line_fulfilled: []RuleMask64,

    /// Allocates zero-initialized fulfillment arrays matching `table` dimensions.
    pub fn init(arena_alloc: Allocator, table: *const SuppressionTable) !FulfillmentTracker {
        const ast_fulfilled = try arena_alloc.alloc(RuleMask64, table.ast_spans.len);
        @memset(ast_fulfilled, 0);
        const line_fulfilled = try arena_alloc.alloc(RuleMask64, table.line_spans.len);
        @memset(line_fulfilled, 0);
        return .{
            .ast_fulfilled = ast_fulfilled,
            .line_fulfilled = line_fulfilled,
        };
    }

    /// Releases fulfillment slices when backed by a general-purpose allocator in unit tests.
    pub fn deinit(self: *FulfillmentTracker, allocator: Allocator) void {
        if (self.ast_fulfilled.len > 0) allocator.free(self.ast_fulfilled);
        if (self.line_fulfilled.len > 0) allocator.free(self.line_fulfilled);
        self.* = .{ .ast_fulfilled = &.{}, .line_fulfilled = &.{} };
    }
};

/// 128-bit content hash for `QueryStage.lint_semantic_settings` Early-Cutoff comparison.
pub const SemanticSettingsDigest = extern struct {
    /// Lower 64 bits of the canonical settings digest.
    low: u64 = 0,
    /// Upper 64 bits of the canonical settings digest.
    high: u64 = 0,

    /// Returns `true` when both 64-bit halves match `other`.
    pub inline fn eql(self: SemanticSettingsDigest, other: SemanticSettingsDigest) bool {
        return self.low == other.low and self.high == other.high;
    }
};

/// Bounded semantic parameters from `[lint.settings]` (`QueryStage.lint_semantic_settings`, `DR-25` §3.1).
pub const LintSettings = struct {
    /// Minimum ungrouped decimal digit count triggering `W0122` (`4..=12`, default `5`).
    min_grouped_int_digits: u8 = 5,
    /// Minimum ungrouped hexadecimal digit count triggering `W0122` (`4..=16`, default `5`).
    min_grouped_hex_digits: u8 = 5,
    /// Explicit `Copy` threshold override in bytes for `W0413` (`4..=16`; `null` = target word size).
    trivial_copy_max_bytes: ?u8 = null,
    /// When `true` (default), `@allow` and `allow(…)` without a rationale emit `W0003`.
    require_suppression_reason: bool = true,
    /// Sorted/deduplicated extra domain identifiers (`<= 64`) exempt from `W0203` (`single-char-ident`).
    allowed_ident_names: []const StringId = &.{},
    /// Sorted/deduplicated non-ASCII Unicode scalars (`>= 0x80`, `<= 64`) exempt from `W0104`.
    allowed_confusables: []const u21 = &.{},

    /// Resolves `trivial_copy_max_bytes`, defaulting `null` to `8` on 64-bit targets or `4` on `wasm32`.
    pub inline fn effectiveTrivialCopyMaxBytes(self: LintSettings, ptr_byte_size: u8) u8 {
        return self.trivial_copy_max_bytes orelse if (ptr_byte_size <= 4) 4 else 8;
    }

    /// Returns `true` if `ident_text` is in `{i, j, k, n, x, y, z, w}` or `self.allowed_ident_names`.
    pub fn isAllowedIdentName(
        self: LintSettings,
        interner: *const StringInterner,
        ident_text: []const u8,
    ) bool {
        if (ident_text.len == 1) {
            switch (ident_text[0]) {
                'i', 'j', 'k', 'n', 'x', 'y', 'z', 'w' => return true,
                else => {},
            }
        }
        for (self.allowed_ident_names) |allowed_id| {
            if (std.mem.eql(u8, interner.get(allowed_id), ident_text)) return true;
        }
        return false;
    }

    /// Returns `true` if non-ASCII scalar `codepoint` is explicitly permitted by `allowed_confusables`.
    pub fn isAllowedConfusable(self: LintSettings, codepoint: u21) bool {
        for (self.allowed_confusables) |allowed_cp| {
            if (allowed_cp == codepoint) return true;
        }
        return false;
    }

    /// Computes a deterministic 128-bit `Wyhash` digest over all semantic lint parameters.
    pub fn computeSemanticFingerprint(
        self: LintSettings,
        interner: *const StringInterner,
    ) SemanticSettingsDigest {
        var hasher_lo = std.hash.Wyhash.init(0x517C_C1B7_2722_0A95);
        var hasher_hi = std.hash.Wyhash.init(0x9E37_79B9_7F4A_7C15);
        const header = [4]u8{
            self.min_grouped_int_digits,
            self.min_grouped_hex_digits,
            self.trivial_copy_max_bytes orelse 0,
            @intFromBool(self.require_suppression_reason),
        };
        hasher_lo.update(&header);
        hasher_hi.update(&header);

        const ident_len_le = std.mem.nativeToLittle(u32, @intCast(self.allowed_ident_names.len));
        hasher_lo.update(std.mem.asBytes(&ident_len_le));
        hasher_hi.update(std.mem.asBytes(&ident_len_le));
        for (self.allowed_ident_names) |name_id| {
            const text = interner.get(name_id);
            const text_len_le = std.mem.nativeToLittle(u32, @intCast(text.len));
            hasher_lo.update(std.mem.asBytes(&text_len_le));
            hasher_lo.update(text);
            hasher_hi.update(std.mem.asBytes(&text_len_le));
            hasher_hi.update(text);
        }

        const conf_len_le = std.mem.nativeToLittle(u32, @intCast(self.allowed_confusables.len));
        hasher_lo.update(std.mem.asBytes(&conf_len_le));
        hasher_hi.update(std.mem.asBytes(&conf_len_le));
        for (self.allowed_confusables) |codepoint| {
            const cp_le = std.mem.nativeToLittle(u32, codepoint);
            hasher_lo.update(std.mem.asBytes(&cp_le));
            hasher_hi.update(std.mem.asBytes(&cp_le));
        }

        return .{
            .low = hasher_lo.final(),
            .high = hasher_hi.final(),
        };
    }
};

/// Ephemeral CLI `--only` and `--disable` filter applied at `QueryStage.project_file_diagnostics`.
pub const CliLintFilter = struct {
    /// `true` when one or more `--only=<r1,r2>` flags were supplied on the command line.
    has_only: bool = false,
    /// Union of rule bits explicitly selected via `--only`.
    only_mask: RuleMask64 = 0,
    /// Union of rule bits explicitly suppressed via `--disable` (`--disable` wins over `--only`).
    disable_mask: RuleMask64 = 0,

    /// Combines `base_disabled` (`corex.toml` + `[[lint.overrides]]`) with CLI `--only` and `--disable`.
    pub inline fn applyToDisabledMask(self: CliLintFilter, base_disabled: RuleMask64) RuleMask64 {
        if (self.has_only) {
            return ((ALL_RULES_MASK & ~self.only_mask) | self.disable_mask) & ALL_RULES_MASK;
        }
        return (base_disabled | self.disable_mask) & ALL_RULES_MASK;
    }

    /// Returns the mask of rules eligible for `W0002` stale-expect auditing (`DR-25` §1.4).
    pub inline fn activeAuditMask(self: CliLintFilter) RuleMask64 {
        if (self.has_only) {
            return (self.only_mask & ~self.disable_mask) & ALL_RULES_MASK;
        }
        return (ALL_RULES_MASK & ~self.disable_mask) & ALL_RULES_MASK;
    }
};

/// Temporary parsed selector token span collected before computing comma-aware `prune_*` bounds.
const RawSelectorItem = struct {
    /// Resolved `DR-25` lint rule ordinal (`0..43`).
    rule_id: RuleId,
    /// Inclusive start byte offset of the selector token in the source buffer.
    start_byte: u32,
    /// Exclusive end byte offset of the selector token in the source buffer.
    end_byte: u32,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical comment prefix introducing Scope-2 and Scope-4 lint directives (`DR-25` §1.3).
pub const CHECK_DIRECTIVE_PREFIX = "// corex check:";

/// Minimum non-whitespace character count required for a valid suppression `reason` (`Ruling 3.2`).
pub const MIN_REASON_NON_SPACE_CHARS: usize = 4;

/// Inclusive lower bound for `[lint.settings].min-grouped-int-digits` (`E0020`).
pub const MIN_GROUPED_INT_DIGITS_MIN: u8 = 4;

/// Inclusive upper bound for `[lint.settings].min-grouped-int-digits` (`E0020`).
pub const MIN_GROUPED_INT_DIGITS_MAX: u8 = 12;

/// Inclusive lower bound for `[lint.settings].min-grouped-hex-digits` (`E0020`).
pub const MIN_GROUPED_HEX_DIGITS_MIN: u8 = 4;

/// Inclusive upper bound for `[lint.settings].min-grouped-hex-digits` (`E0020`).
pub const MIN_GROUPED_HEX_DIGITS_MAX: u8 = 16;

/// Inclusive lower bound for `[lint.settings].trivial-copy-max-bytes` (`E0020`).
pub const TRIVIAL_COPY_MAX_BYTES_MIN: u8 = 4;

/// Inclusive upper bound for `[lint.settings].trivial-copy-max-bytes` (`E0020`).
pub const TRIVIAL_COPY_MAX_BYTES_MAX: u8 = 16;

/// Maximum entry count in `[lint.settings].allowed-ident-names` (`E0020`).
pub const MAX_ALLOWED_IDENT_NAMES: usize = 64;

/// Maximum entry count in `[lint.settings].allowed-confusables` (`E0020`).
pub const MAX_ALLOWED_CONFUSABLES: usize = 64;

/// Case-normalized placeholder rationale strings rejected by `W0003` (`Ruling 3.2`), sorted alphabetically.
const PLACEHOLDER_REASON_MAP = std.StaticStringMap(void).initComptime(.{
    .{"..."},
    .{"fixme"},
    .{"hack"},
    .{"lint"},
    .{"n/a"},
    .{"none"},
    .{"todo"},
    .{"xxx"},
    .{"\u{2026}"},
});

// -------------------------------------- INTERNALS --------------------------------------

/// Orders raw AST suppressions in laminar preorder `(start ASC, end DESC, decl_order ASC)`.
fn lessThanRawAst(_: void, lhs: RawAstSuppression, rhs: RawAstSuppression) bool {
    if (lhs.target_start_byte != rhs.target_start_byte) {
        return lhs.target_start_byte < rhs.target_start_byte;
    }
    if (lhs.target_end_byte != rhs.target_end_byte) {
        return lhs.target_end_byte > rhs.target_end_byte;
    }
    return lhs.decl_order < rhs.decl_order;
}

/// Orders Scope-4 line directives by `(line_start_byte ASC, directive_remove_start ASC)`.
fn lessThanLineSpan(_: void, lhs: DisjointLineSpan, rhs: DisjointLineSpan) bool {
    if (lhs.line_start_byte != rhs.line_start_byte) {
        return lhs.line_start_byte < rhs.line_start_byte;
    }
    return lhs.directive_remove_start < rhs.directive_remove_start;
}

/// Binary searches `starts` (`u32` ascending) for the largest index `idx` with `starts[idx] <= pos`.
inline fn rightmostStartAtOrBefore(starts: []const u32, pos: u32) ?usize {
    if (starts.len == 0 or pos < starts[0]) return null;
    var low: usize = 0;
    var high: usize = starts.len;
    while (low + 1 < high) {
        const mid = low + (high - low) / 2;
        if (starts[mid] <= pos) {
            low = mid;
        } else {
            high = mid;
        }
    }
    return low;
}

/// Binary searches mutually disjoint `spans` for the unique physical line containing `pos` (`O(log L)`).
inline fn findDisjointLineSpan(spans: []const DisjointLineSpan, pos: u32) ?usize {
    if (spans.len == 0 or pos < spans[0].line_start_byte) return null;
    var low: usize = 0;
    var high: usize = spans.len;
    while (low + 1 < high) {
        const mid = low + (high - low) / 2;
        if (spans[mid].line_start_byte <= pos) {
            low = mid;
        } else {
            high = mid;
        }
    }
    return if (pos < spans[low].line_end_byte) low else null;
}

/// Advances `pos` past any `\r\n` or `\n` immediately at `line_end` to include one line break in full-line deletes.
inline fn advancePastLineBreak(source: []const u8, line_end: u32) u32 {
    const idx: usize = line_end;
    if (idx < source.len) {
        if (source[idx] == '\r' and idx + 1 < source.len and source[idx + 1] == '\n') {
            return line_end + 2;
        }
        if (source[idx] == '\n') {
            return line_end + 1;
        }
    }
    return line_end;
}

/// Returns `true` if `slice` consists solely of ASCII spaces and horizontal tabs.
inline fn isHorizontalBlank(slice: []const u8) bool {
    for (slice) |byte_val| {
        if (byte_val != ' ' and byte_val != '\t') return false;
    }
    return true;
}

/// Returns `true` if `tok_kind` can participate as a word segment in a `kebab-case` lint selector.
inline fn isSelectorWordTokenKind(tok_kind: TokenKind) bool {
    return tok_kind.isIdentifier() or tok_kind.isKeyword() or tok_kind == .prim_type;
}

/// Converts `raw_items` into `SelectorItemSpan` entries with comma-aware `prune_*` ranges and appends to `dest`.
fn appendPrunableSelectorSpans(
    allocator: Allocator,
    dest: *std.ArrayListUnmanaged(SelectorItemSpan),
    raw_items: []const RawSelectorItem,
) !struct { start: u16, count: u8, mask: RuleMask64 } {
    const start_u16: u16 = @intCast(@min(dest.items.len, std.math.maxInt(u16)));
    const clamped_len: usize = @min(raw_items.len, std.math.maxInt(u8));
    var union_mask: RuleMask64 = 0;

    for (raw_items[0..clamped_len], 0..) |item, idx| {
        union_mask |= item.rule_id.bit();
        const sel_len: u8 = @intCast(@min(item.end_byte -| item.start_byte, std.math.maxInt(u8)));
        if (idx + 1 < clamped_len) {
            try dest.append(allocator, .{
                .prune_start_byte = item.start_byte,
                .prune_end_byte = raw_items[idx + 1].start_byte,
                .rule_id = item.rule_id,
                .sel_offset_from_prune = 0,
                .sel_byte_len = sel_len,
            });
        } else if (clamped_len > 1) {
            const prev_end = raw_items[idx - 1].end_byte;
            const delta_u32 = item.start_byte -| prev_end;
            try dest.append(allocator, .{
                .prune_start_byte = prev_end,
                .prune_end_byte = item.end_byte,
                .rule_id = item.rule_id,
                .sel_offset_from_prune = @intCast(@min(delta_u32, std.math.maxInt(u8))),
                .sel_byte_len = sel_len,
            });
        } else {
            try dest.append(allocator, .{
                .prune_start_byte = item.start_byte,
                .prune_end_byte = item.end_byte,
                .rule_id = item.rule_id,
                .sel_offset_from_prune = 0,
                .sel_byte_len = sel_len,
            });
        }
    }
    return .{
        .start = start_u16,
        .count = @intCast(clamped_len),
        .mask = union_mask,
    };
}

/// Checks if `comment_text` (`//…` without `\r\n`) begins with `//` + spaces + `corex` + spaces + `check:`.
/// Returns the byte offset within `comment_text` immediately after `check:`, or `null` if not a check directive.
fn matchCheckDirectiveHeader(comment_text: []const u8) ?usize {
    if (!std.mem.startsWith(u8, comment_text, "//")) return null;
    var pos: usize = 2;
    while (pos < comment_text.len and (comment_text[pos] == ' ' or comment_text[pos] == '\t')) : (pos += 1) {}
    if (!std.mem.startsWith(u8, comment_text[pos..], "corex")) return null;
    pos += "corex".len;
    const ws_start = pos;
    while (pos < comment_text.len and (comment_text[pos] == ' ' or comment_text[pos] == '\t')) : (pos += 1) {}
    if (pos == ws_start) return null;
    if (!std.mem.startsWith(u8, comment_text[pos..], "check:")) return null;
    return pos + "check:".len;
}

/// Scans `comment_text` (e.g., `/| doc text // corex check: …`) for an embedded trailing `// corex check:` suffix.
fn findEmbeddedCheckDirectiveInDocLine(doc_line: []const u8) ?usize {
    var search_from: usize = 2;
    while (std.mem.indexOfPos(u8, doc_line, search_from, "//")) |slash_pos| {
        if (slash_pos > 0 and (doc_line[slash_pos - 1] == ' ' or doc_line[slash_pos - 1] == '\t')) {
            if (matchCheckDirectiveHeader(doc_line[slash_pos..]) != null) {
                return slash_pos;
            }
        }
        search_from = slash_pos + 2;
    }
    return null;
}

/// Computes the `[start_byte, end_byte)` token span of a CST subtree (`null` if empty/synthesized only).
fn computeCstSubtreeByteBounds(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    node_idx: CstNodeIndex,
) ?struct { start_byte: u32, end_byte: u32, first_tok: TokenIndex } {
    const root = cst_arena.getNode(node_idx);
    const end_idx: usize = @min(cst_arena.countNodes(), @as(usize, node_idx.asInt()) + @max(@as(usize, 1), root.subtree_size));
    const tok_count = token_buffer.countTokens();
    var first_tok: TokenIndex = .none;

    var cur: usize = node_idx.asInt();
    while (cur < end_idx) : (cur += 1) {
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (sub.subtree_size <= 1 and !sub.flags.is_missing_or_injected and
            !sub.token.isNone() and sub.token.asInt() < tok_count)
        {
            const rec = token_buffer.getToken(sub.token);
            if (rec.flags.is_synthesized or rec.kind == .eof) continue;
            first_tok = sub.token;
            break;
        }
    }
    if (first_tok.isNone()) return null;

    var last_tok: TokenIndex = first_tok;
    var rev: usize = end_idx;
    while (rev > cur + 1) {
        rev -= 1;
        const sub = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(rev)));
        if (sub.subtree_size <= 1 and !sub.flags.is_missing_or_injected and
            !sub.token.isNone() and sub.token.asInt() < tok_count)
        {
            const rec = token_buffer.getToken(sub.token);
            if (rec.flags.is_synthesized or rec.kind == .eof) continue;
            last_tok = sub.token;
            break;
        }
    }

    const first_rec = token_buffer.getToken(first_tok);
    const last_rec = token_buffer.getToken(last_tok);
    return .{
        .start_byte = first_rec.byte_offset,
        .end_byte = last_rec.byte_offset + @as(u32, last_rec.byte_len),
        .first_tok = first_tok,
    };
}

/// Returns the attribute identifier slice of an `.attribute` CST node (`""` if malformed).
fn extractCstAttributeName(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    attr_cst: CstNodeIndex,
    name_tok_out: *TokenIndex,
) []const u8 {
    name_tok_out.* = .none;
    const attr_rec = cst_arena.getNode(attr_cst);
    const end_idx = @min(cst_arena.countNodes(), @as(usize, attr_cst.asInt()) + @max(@as(usize, 1), attr_rec.subtree_size));
    var cur: usize = attr_cst.asInt() + 1;
    while (cur < end_idx) : (cur += 1) {
        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur)));
        if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
            !leaf.token.isNone() and leaf.token.asInt() < token_buffer.countTokens())
        {
            const tok_rec = token_buffer.getToken(leaf.token);
            if (tok_rec.flags.is_synthesized or tok_rec.kind == .at) continue;
            if (tok_rec.kind.isIdentifier() or tok_rec.kind.isKeyword()) {
                name_tok_out.* = leaf.token;
                const start_b: usize = tok_rec.byte_offset;
                const end_b: usize = @min(source.len, start_b + tok_rec.byte_len);
                return source[start_b..end_b];
            }
            break;
        }
    }
    return "";
}

/// Returns `true` if `owner_cst` has a direct `.attribute` child with name `"cfg"` or `"generated"`.
fn inspectOwnerSiblingAttrs(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    owner_cst: CstNodeIndex,
) struct { has_cfg: bool, has_generated: bool } {
    var has_cfg = false;
    var has_generated = false;
    const owner_rec = cst_arena.getNode(owner_cst);
    const end_idx = @min(cst_arena.countNodes(), @as(usize, owner_cst.asInt()) + @max(@as(usize, 1), owner_rec.subtree_size));
    var child_cur: usize = owner_cst.asInt() + 1;
    while (child_cur < end_idx) {
        const child_idx = CstNodeIndex.fromInt(@intCast(child_cur));
        const child = cst_arena.getNode(child_idx);
        if (child.kind == .attribute) {
            var unused_tok: TokenIndex = .none;
            const attr_name = extractCstAttributeName(source, token_buffer, cst_arena, child_idx, &unused_tok);
            if (std.mem.eql(u8, attr_name, "cfg")) has_cfg = true;
            if (std.mem.eql(u8, attr_name, "generated")) has_generated = true;
        }
        child_cur += @max(@as(usize, 1), child.subtree_size);
    }
    return .{ .has_cfg = has_cfg, .has_generated = has_generated };
}

/// Finds the outermost non-`.file_end`, non-`.attribute` CST construct whose first real token is `target_tok`.
fn findOutermostConstructStartingAtToken(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    target_tok: TokenIndex,
) ?CstNodeIndex {
    const total = cst_arena.countNodes();
    var idx: usize = 1;
    while (idx < total) {
        const node_id = CstNodeIndex.fromInt(@intCast(idx));
        const rec = cst_arena.getNode(node_id);
        if (rec.kind == .attribute) {
            idx += @max(@as(usize, 1), rec.subtree_size);
            continue;
        }
        if (computeCstSubtreeByteBounds(token_buffer, cst_arena, node_id)) |bounds| {
            if (bounds.first_tok == target_tok) {
                return node_id;
            }
            const target_byte = token_buffer.getToken(target_tok).byte_offset;
            if (bounds.end_byte <= target_byte) {
                idx += @max(@as(usize, 1), rec.subtree_size);
                continue;
            }
        }
        idx += 1;
    }
    return null;
}

/// Extracts the interior byte range of a `"…"` or `r#"…"#` string literal token (`0..0` if non-string).
fn extractStringLiteralInteriorBounds(source: []const u8, start_byte: u32, end_byte: u32) struct { start: u32, end: u32 } {
    const start_u: usize = start_byte;
    const end_u: usize = @min(source.len, end_byte);
    if (start_u + 2 > end_u) return .{ .start = 0, .end = 0 };
    const lex = source[start_u..end_u];
    var open_idx: usize = 0;
    if (lex[0] == 'r') {
        open_idx = 1;
        while (open_idx < lex.len and lex[open_idx] == '#') : (open_idx += 1) {}
    }
    if (open_idx >= lex.len or lex[open_idx] != '"') return .{ .start = 0, .end = 0 };
    const hash_guards: usize = if (lex[0] == 'r') open_idx - 1 else 0;
    if (lex.len < open_idx + 2 + hash_guards) return .{ .start = 0, .end = 0 };
    const close_idx = lex.len - 1 - hash_guards;
    if (close_idx <= open_idx or lex[close_idx] != '"') return .{ .start = 0, .end = 0 };
    return .{
        .start = @intCast(start_u + open_idx + 1),
        .end = @intCast(start_u + close_idx),
    };
}

comptime {
    assert(@sizeOf(RuleId) == 1);
    assert(@sizeOf(RuleMask64) == 8);
    assert(@sizeOf(TextEdit) == 16);
    assert(@sizeOf(SelectorItemSpan) == 12);
    assert(@sizeOf(DisjointLineSpan) == 40);
    assert(@sizeOf(RawLintCandidate) == 24);
    assert(@sizeOf(EffectiveFileRules) == 8);
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Returns `true` when `raw_reason` has `>= 4` non-whitespace bytes and is not a placeholder (`Ruling 3.2`).
pub fn isValidSuppressionReason(raw_reason: []const u8) bool {
    const trimmed = std.mem.trim(u8, raw_reason, " \t\r\n");
    if (trimmed.len == 0) return false;

    var non_ws_bytes: usize = 0;
    for (trimmed) |byte_val| {
        if (byte_val != ' ' and byte_val != '\t' and byte_val != '\r' and byte_val != '\n') {
            non_ws_bytes += 1;
        }
    }
    if (non_ws_bytes < MIN_REASON_NON_SPACE_CHARS) return false;

    if (trimmed.len <= 8) {
        var lower_buf: [8]u8 = undefined;
        for (trimmed, 0..) |byte_val, i| {
            lower_buf[i] = std.ascii.toLower(byte_val);
        }
        if (PLACEHOLDER_REASON_MAP.has(lower_buf[0..trimmed.len])) return false;
    }
    return true;
}

/// Returns `true` if `source` carries a preamble `@generated` or `Code generated … DO NOT EDIT` marker.
pub fn isGeneratedSource(source: []const u8) bool {
    const scan_limit = @min(source.len, 2048);
    const header = source[0..scan_limit];
    if (std.mem.indexOf(u8, header, "@generated") != null) return true;
    if (std.mem.indexOf(u8, header, "Code generated") != null and
        std.mem.indexOf(u8, header, "DO NOT EDIT") != null)
    {
        return true;
    }
    return false;
}

/// Constructs the $O(\log K)$ / $O(1)$ `SuppressionTable` from collected AST attributes and line directives.
pub fn buildSuppressionTable(
    allocator: Allocator,
    file_allow_mask: RuleMask64,
    file_expect_mask: RuleMask64,
    file_directives: []const DisjointLineSpan,
    raw_ast: []RawAstSuppression,
    line_spans: []const DisjointLineSpan,
    selectors: []const SelectorItemSpan,
) !SuppressionTable {
    const sorted_lines = try allocator.dupe(DisjointLineSpan, line_spans);
    errdefer if (sorted_lines.len > 0) allocator.free(sorted_lines);
    std.mem.sort(DisjointLineSpan, sorted_lines, {}, lessThanLineSpan);

    var table = SuppressionTable{
        .any_suppressed_mask = file_allow_mask | file_expect_mask,
        .file_allow_mask = file_allow_mask,
        .file_expect_mask = file_expect_mask,
        .file_directives = try allocator.dupe(DisjointLineSpan, file_directives),
        .line_spans = sorted_lines,
        .selectors = try allocator.dupe(SelectorItemSpan, selectors),
    };
    errdefer table.deinit(allocator);

    for (sorted_lines) |line_span| {
        table.any_suppressed_mask |= line_span.own_mask;
    }

    if (raw_ast.len == 0) return table;

    // [1] Sort Scope-3 AST attributes in strict laminar preorder `(start ASC, end DESC, order ASC)`:
    std.mem.sort(RawAstSuppression, raw_ast, {}, lessThanRawAst);
    try table.ast_spans.ensureTotalCapacity(allocator, raw_ast.len);

    // [2] Link `parent_idx` and `eff_mask` in a single O(K) monotonic stack pass:
    var stack: [syn.MAX_PARSE_DEPTH]u16 = undefined;
    var stack_len: usize = 0;

    for (raw_ast, 0..) |item, i| {
        table.any_suppressed_mask |= item.own_mask;
        while (stack_len > 0) {
            const top_idx = stack[stack_len - 1];
            const top_end = table.ast_spans.items(.end_byte)[top_idx];
            if (top_end <= item.target_start_byte) {
                stack_len -= 1;
            } else {
                break;
            }
        }

        const parent: u16 = if (stack_len > 0) stack[stack_len - 1] else SuppressionTable.NONE_IDX;
        const inherited_mask: RuleMask64 = if (parent != SuppressionTable.NONE_IDX)
            table.ast_spans.items(.eff_mask)[parent]
        else
            0;

        if (parent != SuppressionTable.NONE_IDX) {
            assert(item.target_end_byte <= table.ast_spans.items(.end_byte)[parent]);
        }

        table.ast_spans.appendAssumeCapacity(.{
            .start_byte = item.target_start_byte,
            .end_byte = item.target_end_byte,
            .directive_remove_start = item.directive_remove_start,
            .directive_remove_end = item.directive_remove_end,
            .directive_head_start = item.directive_head_start,
            .directive_head_end = item.directive_head_end,
            .allow_kw_start = item.allow_kw_start,
            .allow_kw_end = item.allow_kw_end,
            .reason_start = item.reason_start,
            .reason_end = item.reason_end,
            .own_mask = item.own_mask,
            .eff_mask = item.own_mask | inherited_mask,
            .parent_idx = parent,
            .selector_slice_start = item.selector_slice_start,
            .selector_count = item.selector_count,
            .mode = item.mode,
            .has_sibling_cfg = item.has_sibling_cfg,
            .is_above_line_comment = item.is_above_line_comment,
        });

        if (stack_len < stack.len and i <= std.math.maxInt(u16)) {
            stack[stack_len] = @intCast(i);
            stack_len += 1;
        }
    }

    return table;
}

/// Walks `token_buffer` trivia and `cst_arena` `.attribute` nodes to build a file's `SuppressionTable`.
pub fn extractFileSuppressionTable(
    allocator: Allocator,
    file_id: FileId,
    source: []const u8,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    line_index: *const LineIndex,
) !SuppressionTable {
    var file_allow_mask: RuleMask64 = 0;
    var file_expect_mask: RuleMask64 = 0;
    var file_directives: std.ArrayListUnmanaged(DisjointLineSpan) = .empty;
    defer file_directives.deinit(allocator);
    var raw_ast: std.ArrayListUnmanaged(RawAstSuppression) = .empty;
    defer raw_ast.deinit(allocator);
    var line_spans: std.ArrayListUnmanaged(DisjointLineSpan) = .empty;
    defer line_spans.deinit(allocator);
    var selectors: std.ArrayListUnmanaged(SelectorItemSpan) = .empty;
    defer selectors.deinit(allocator);
    var directive_errors: std.ArrayListUnmanaged(DirectiveErrorRecord) = .empty;
    defer directive_errors.deinit(allocator);
    var mid_file_directives: std.ArrayListUnmanaged(MidFileDirectiveRecord) = .empty;
    defer mid_file_directives.deinit(allocator);
    var above_line_hoists: std.ArrayListUnmanaged(AboveLineHoistRecord) = .empty;
    defer above_line_hoists.deinit(allocator);

    var is_generated = isGeneratedSource(source);

    // [1] Find `first_code_byte` (start of first real non-EOF token):
    var first_code_byte: u32 = @intCast(source.len);
    const tok_count = token_buffer.countTokens();
    var tok_scan: usize = 0;
    while (tok_scan < tok_count) : (tok_scan += 1) {
        const rec = token_buffer.getToken(TokenIndex.fromInt(@intCast(tok_scan)));
        if (rec.kind == .eof or rec.flags.is_synthesized) continue;
        first_code_byte = rec.byte_offset;
        break;
    }

    // [2] Scan all trivia pieces (splitting `TRIVIA_FLAG_COALESCED` chunks) for `// corex check:` directives:
    var decl_order_counter: u16 = 0;
    for (token_buffer.trivia.items) |raw_piece| {
        const piece_start: usize = raw_piece.byte_offset;
        const piece_end: usize = @min(source.len, piece_start + raw_piece.byte_len);
        if (piece_start >= piece_end) continue;

        var scan_cursor = piece_start;
        while (scan_cursor < piece_end) {
            if ((raw_piece.flags & syn.TRIVIA_FLAG_COALESCED) == 0 and
                raw_piece.kind != .line_comment and
                raw_piece.kind != .doc_comment and
                raw_piece.kind != .module_doc_comment)
            {
                break;
            }
            // Advance to next `/` inside coalesced or direct comment trivia:
            if (source[scan_cursor] != '/') {
                scan_cursor += 1;
                continue;
            }
            var line_end_pos = scan_cursor;
            while (line_end_pos < piece_end and source[line_end_pos] != '\n' and source[line_end_pos] != '\r') {
                line_end_pos += 1;
            }
            const full_cmt_slice = source[scan_cursor..line_end_pos];
            defer scan_cursor = if (line_end_pos < piece_end) line_end_pos + 1 else piece_end;

            var cmt_abs_start: usize = scan_cursor;
            if (std.mem.startsWith(u8, full_cmt_slice, "/|") or std.mem.startsWith(u8, full_cmt_slice, "/#")) {
                if (findEmbeddedCheckDirectiveInDocLine(full_cmt_slice)) |embedded_rel| {
                    cmt_abs_start = scan_cursor + embedded_rel;
                } else {
                    continue;
                }
            }
            const cmt_slice = source[cmt_abs_start..line_end_pos];
            const after_header_rel = matchCheckDirectiveHeader(cmt_slice) orelse continue;

            // Parse action keyword (`file-expect`, `file-allow`, `expect`, `allow`):
            var rel_pos = after_header_rel;
            while (rel_pos < cmt_slice.len and (cmt_slice[rel_pos] == ' ' or cmt_slice[rel_pos] == '\t')) : (rel_pos += 1) {}
            const action_start = rel_pos;
            while (rel_pos < cmt_slice.len and
                (std.ascii.isAlphabetic(cmt_slice[rel_pos]) or cmt_slice[rel_pos] == '-' or cmt_slice[rel_pos] == '_'))
            {
                rel_pos += 1;
            }
            const action_str = cmt_slice[action_start..rel_pos];
            const is_file_scope = std.mem.eql(u8, action_str, "file-expect") or std.mem.eql(u8, action_str, "file-allow");
            const is_line_scope = std.mem.eql(u8, action_str, "expect") or std.mem.eql(u8, action_str, "allow");
            if (!is_file_scope and !is_line_scope) {
                const err_start: u32 = @intCast(cmt_abs_start + action_start);
                const err_end: u32 = @intCast(@max(cmt_abs_start + rel_pos, cmt_abs_start + after_header_rel));
                try directive_errors.append(allocator, .{
                    .start_byte = err_start,
                    .end_byte = err_end,
                    .kind = .unknown_action,
                });
                continue;
            }
            const mode: DirectiveMode = if (std.mem.endsWith(u8, action_str, "expect")) .expect else .allow;
            const allow_kw_abs_start: u32 = if (mode == .allow)
                @intCast(cmt_abs_start + action_start + (if (is_file_scope) "file-".len else 0))
            else
                0;

            while (rel_pos < cmt_slice.len and (cmt_slice[rel_pos] == ' ' or cmt_slice[rel_pos] == '\t')) : (rel_pos += 1) {}
            if (rel_pos >= cmt_slice.len or cmt_slice[rel_pos] != '(') {
                try directive_errors.append(allocator, .{
                    .start_byte = @intCast(cmt_abs_start + action_start),
                    .end_byte = @intCast(cmt_abs_start + rel_pos),
                    .kind = .missing_parens,
                });
                continue;
            }
            const open_paren_rel = rel_pos;
            const close_paren_rel_opt = std.mem.indexOfScalarPos(u8, cmt_slice, open_paren_rel + 1, ')');
            if (close_paren_rel_opt == null) {
                try directive_errors.append(allocator, .{
                    .start_byte = @intCast(cmt_abs_start + open_paren_rel),
                    .end_byte = @intCast(line_end_pos),
                    .kind = .missing_parens,
                });
                continue;
            }
            const close_paren_rel = close_paren_rel_opt.?;
            const args_raw = cmt_slice[open_paren_rel + 1 .. close_paren_rel];

            var parsed_raw_sels: [64]RawSelectorItem = undefined;
            var parsed_sel_count: usize = 0;
            var has_sel_err = false;

            if (std.mem.trim(u8, args_raw, " \t").len == 0) {
                has_sel_err = true;
                try directive_errors.append(allocator, .{
                    .start_byte = @intCast(cmt_abs_start + open_paren_rel),
                    .end_byte = @intCast(cmt_abs_start + close_paren_rel + 1),
                    .kind = .empty_selector_list,
                });
            } else {
                var item_cursor: usize = 0;
                while (item_cursor < args_raw.len) {
                    while (item_cursor < args_raw.len and (args_raw[item_cursor] == ' ' or args_raw[item_cursor] == '\t')) {
                        item_cursor += 1;
                    }
                    if (item_cursor >= args_raw.len) break;
                    var comma_pos = item_cursor;
                    while (comma_pos < args_raw.len and args_raw[comma_pos] != ',') : (comma_pos += 1) {}
                    const item_trimmed = std.mem.trim(u8, args_raw[item_cursor..comma_pos], " \t");
                    if (item_trimmed.len > 0) {
                        const trim_lead = std.mem.indexOf(u8, args_raw[item_cursor..comma_pos], item_trimmed).?;
                        const sel_abs_start: u32 = @intCast(cmt_abs_start + open_paren_rel + 1 + item_cursor + trim_lead);
                        const sel_abs_end: u32 = sel_abs_start + @as(u32, @intCast(item_trimmed.len));

                        if (std.mem.eql(u8, item_trimmed, "*")) {
                            has_sel_err = true;
                            try directive_errors.append(allocator, .{
                                .start_byte = sel_abs_start,
                                .end_byte = sel_abs_end,
                                .kind = .wildcard_forbidden,
                            });
                        } else if (std.mem.indexOfScalar(u8, item_trimmed, ' ') != null or
                            std.mem.indexOfScalar(u8, item_trimmed, '\t') != null)
                        {
                            has_sel_err = true;
                            try directive_errors.append(allocator, .{
                                .start_byte = sel_abs_start,
                                .end_byte = sel_abs_end,
                                .kind = .spaced_hyphen_in_slug,
                            });
                        } else switch (diag.lookupLintRuleBySelector(item_trimmed)) {
                            .rule => |matched_rule| {
                                if (parsed_sel_count < parsed_raw_sels.len) {
                                    parsed_raw_sels[parsed_sel_count] = .{
                                        .rule_id = matched_rule,
                                        .start_byte = sel_abs_start,
                                        .end_byte = sel_abs_end,
                                    };
                                    parsed_sel_count += 1;
                                }
                            },
                            .forbidden_category_or_wildcard => {
                                has_sel_err = true;
                                try directive_errors.append(allocator, .{
                                    .start_byte = sel_abs_start,
                                    .end_byte = sel_abs_end,
                                    .kind = .category_or_blanket_forbidden,
                                });
                            },
                            .non_suppressible_error_code => {
                                has_sel_err = true;
                                try directive_errors.append(allocator, .{
                                    .start_byte = sel_abs_start,
                                    .end_byte = sel_abs_end,
                                    .kind = .non_suppressible_error_code,
                                });
                            },
                            .non_suppressible_subsystem_warning => {
                                has_sel_err = true;
                                try directive_errors.append(allocator, .{
                                    .start_byte = sel_abs_start,
                                    .end_byte = sel_abs_end,
                                    .kind = .non_suppressible_warning_code,
                                });
                            },
                            .unknown => {
                                has_sel_err = true;
                                try directive_errors.append(allocator, .{
                                    .start_byte = sel_abs_start,
                                    .end_byte = sel_abs_end,
                                    .kind = .unknown_lint_rule,
                                });
                            },
                        }
                    }
                    item_cursor = if (comma_pos < args_raw.len) comma_pos + 1 else args_raw.len;
                }
            }
            if (has_sel_err or parsed_sel_count == 0) continue;

            // Parse optional `-- <reason>` suffix after `)`:
            var reason_abs_start: u32 = 0;
            var reason_abs_end: u32 = 0;
            var tail_pos = close_paren_rel + 1;
            while (tail_pos < cmt_slice.len and (cmt_slice[tail_pos] == ' ' or cmt_slice[tail_pos] == '\t')) : (tail_pos += 1) {}
            if (std.mem.startsWith(u8, cmt_slice[tail_pos..], "--")) {
                var r_start = tail_pos + 2;
                while (r_start < cmt_slice.len and (cmt_slice[r_start] == ' ' or cmt_slice[r_start] == '\t')) : (r_start += 1) {}
                const trimmed_reason = std.mem.trimEnd(u8, cmt_slice[r_start..], " \t");
                if (trimmed_reason.len > 0) {
                    reason_abs_start = @intCast(cmt_abs_start + r_start);
                    reason_abs_end = reason_abs_start + @as(u32, @intCast(trimmed_reason.len));
                }
            }

            const loc = line_index.resolveLineCol(source, @intCast(cmt_abs_start));
            const line_bounds = line_index.getLineBounds(source, loc.line - 1);
            const has_preceding_on_line = !isHorizontalBlank(source[line_bounds.start..cmt_abs_start]);

            if (is_file_scope) {
                if (cmt_abs_start < first_code_byte and !has_preceding_on_line) {
                    const sel_meta = try appendPrunableSelectorSpans(allocator, &selectors, parsed_raw_sels[0..parsed_sel_count]);
                    if (mode == .expect) {
                        file_expect_mask |= sel_meta.mask;
                    } else {
                        file_allow_mask |= sel_meta.mask;
                    }
                    const remove_start = line_bounds.start;
                    const remove_end = advancePastLineBreak(source, line_bounds.end);
                    try file_directives.append(allocator, .{
                        .line_start_byte = line_bounds.start,
                        .line_end_byte = line_bounds.end,
                        .directive_remove_start = remove_start,
                        .directive_remove_end = remove_end,
                        .reason_start = reason_abs_start,
                        .reason_end = reason_abs_end,
                        .own_mask = sel_meta.mask,
                        .selector_slice_start = sel_meta.start,
                        .selector_count = sel_meta.count,
                        .mode = @backingInt(mode),
                        .allow_kw_offset = 0,
                        .comment_start_offset = @intCast(@min(cmt_abs_start - remove_start, std.math.maxInt(u16))),
                    });
                } else {
                    var rem_start: u32 = @intCast(cmt_abs_start);
                    var rem_end: u32 = @intCast(line_end_pos);
                    if (!has_preceding_on_line) {
                        rem_start = line_bounds.start;
                        rem_end = advancePastLineBreak(source, line_bounds.end);
                    } else {
                        while (rem_start > line_bounds.start and
                            (source[rem_start - 1] == ' ' or source[rem_start - 1] == '\t'))
                        {
                            rem_start -= 1;
                        }
                    }
                    try mid_file_directives.append(allocator, .{
                        .comment_start_byte = @intCast(cmt_abs_start),
                        .comment_end_byte = @intCast(line_end_pos),
                        .remove_start_byte = rem_start,
                        .remove_end_byte = rem_end,
                        .is_file_expect = mode == .expect,
                    });
                }
            } else if (has_preceding_on_line) {
                // Scope 4 trailing physical-line directive:
                const sel_meta = try appendPrunableSelectorSpans(allocator, &selectors, parsed_raw_sels[0..parsed_sel_count]);
                var rem_start: u32 = @intCast(cmt_abs_start);
                while (rem_start > line_bounds.start and
                    (source[rem_start - 1] == ' ' or source[rem_start - 1] == '\t'))
                {
                    rem_start -= 1;
                }
                try line_spans.append(allocator, .{
                    .line_start_byte = line_bounds.start,
                    .line_end_byte = line_bounds.end,
                    .directive_remove_start = rem_start,
                    .directive_remove_end = @intCast(line_end_pos),
                    .reason_start = reason_abs_start,
                    .reason_end = reason_abs_end,
                    .own_mask = sel_meta.mask,
                    .selector_slice_start = sel_meta.start,
                    .selector_count = sel_meta.count,
                    .mode = @backingInt(mode),
                    .allow_kw_offset = if (mode == .allow)
                        @intCast(@min(allow_kw_abs_start -| rem_start, std.math.maxInt(u16)))
                    else
                        0,
                    .comment_start_offset = @intCast(@min(@as(u32, @intCast(cmt_abs_start)) -| rem_start, std.math.maxInt(u16))),
                });
            } else {
                // Standalone above-line `// corex check:` (`Ruling 3.3`: active Scope-3 `allow` + `W0202` hoist):
                var target_tok: TokenIndex = .none;
                var t_idx: usize = 0;
                while (t_idx < tok_count) : (t_idx += 1) {
                    const candidate_tok = TokenIndex.fromInt(@intCast(t_idx));
                    const rec = token_buffer.getToken(candidate_tok);
                    if (rec.kind == .eof or rec.flags.is_synthesized) continue;
                    if (rec.byte_offset >= line_end_pos) {
                        target_tok = candidate_tok;
                        break;
                    }
                }
                if (!target_tok.isNone()) {
                    const target_tok_byte = token_buffer.getToken(target_tok).byte_offset;
                    const between_slice = source[line_end_pos..target_tok_byte];
                    const has_doc_between = std.mem.indexOf(u8, between_slice, "/|") != null;
                    const target_loc = line_index.resolveLineCol(source, target_tok_byte);
                    const target_line_bounds = line_index.getLineBounds(source, target_loc.line - 1);

                    var target_has_cfg = false;
                    var target_start = target_tok_byte;
                    var target_end: u32 = @intCast(source.len);
                    if (findOutermostConstructStartingAtToken(token_buffer, cst_arena, target_tok)) |owner_cst| {
                        if (computeCstSubtreeByteBounds(token_buffer, cst_arena, owner_cst)) |bounds| {
                            target_start = bounds.start_byte;
                            target_end = bounds.end_byte;
                        }
                        target_has_cfg = inspectOwnerSiblingAttrs(source, token_buffer, cst_arena, owner_cst).has_cfg;
                    }

                    const sel_meta = try appendPrunableSelectorSpans(allocator, &selectors, parsed_raw_sels[0..parsed_sel_count]);
                    try raw_ast.append(allocator, .{
                        .target_start_byte = target_start,
                        .target_end_byte = target_end,
                        .directive_remove_start = line_bounds.start,
                        .directive_remove_end = advancePastLineBreak(source, line_bounds.end),
                        .directive_head_start = @intCast(cmt_abs_start),
                        .directive_head_end = @intCast(line_end_pos),
                        .own_mask = sel_meta.mask,
                        .selector_slice_start = sel_meta.start,
                        .selector_count = sel_meta.count,
                        .mode = .allow,
                        .decl_order = decl_order_counter,
                        .has_sibling_cfg = target_has_cfg,
                        .is_above_line_comment = true,
                    });
                    decl_order_counter +%= 1;

                    const trimmed_args = std.mem.trim(u8, args_raw, " \t");
                    const args_lead = std.mem.indexOf(u8, args_raw, trimmed_args) orelse 0;
                    const sel_raw_start: u32 = @intCast(cmt_abs_start + open_paren_rel + 1 + args_lead);
                    const sel_raw_end: u32 = sel_raw_start + @as(u32, @intCast(trimmed_args.len));

                    try above_line_hoists.append(allocator, .{
                        .comment_start_byte = @intCast(cmt_abs_start),
                        .comment_end_byte = @intCast(line_end_pos),
                        .comment_line_start = line_bounds.start,
                        .comment_line_next_start = advancePastLineBreak(source, line_bounds.end),
                        .target_line_start = target_line_bounds.start,
                        .target_tok_start = target_tok_byte,
                        .selectors_raw_start = sel_raw_start,
                        .selectors_raw_end = sel_raw_end,
                        .reason_start = reason_abs_start,
                        .reason_end = reason_abs_end,
                        .has_intervening_doc_comments = has_doc_between,
                        .target_has_cfg = target_has_cfg,
                        .original_mode = mode,
                    });
                }
            }
        }
    }

    // [3] Walk `cst_arena` in pre-order to extract Scope-3 `@expect` and `@allow` attributes:
    const cst_total = cst_arena.countNodes();
    var owner_idx: usize = 0;
    while (owner_idx < cst_total) : (owner_idx += 1) {
        const owner_cst = CstNodeIndex.fromInt(@intCast(owner_idx));
        const owner_rec = cst_arena.getNode(owner_cst);
        if (owner_rec.subtree_size <= 1 or owner_rec.kind == .attribute) continue;

        if (owner_idx <= 1) {
            if (inspectOwnerSiblingAttrs(source, token_buffer, cst_arena, owner_cst).has_generated) {
                is_generated = true;
            }
        }
        if (owner_rec.kind == .file_end) continue;

        const owner_end_idx = @min(cst_total, owner_idx + owner_rec.subtree_size);
        var cached_owner_bounds: @TypeOf(computeCstSubtreeByteBounds(token_buffer, cst_arena, owner_cst)) = null;
        var has_computed_owner_meta = false;
        var sibling_has_cfg = false;
        var child_cur: usize = owner_idx + 1;

        while (child_cur < owner_end_idx) {
            const child_cst = CstNodeIndex.fromInt(@intCast(child_cur));
            const child_rec = cst_arena.getNode(child_cst);
            const next_child_cur = child_cur + @max(@as(usize, 1), child_rec.subtree_size);
            defer child_cur = next_child_cur;

            if (child_rec.kind != .attribute) continue;
            var name_tok: TokenIndex = .none;
            const attr_name = extractCstAttributeName(source, token_buffer, cst_arena, child_cst, &name_tok);
            const is_expect = std.mem.eql(u8, attr_name, "expect");
            const is_allow = std.mem.eql(u8, attr_name, "allow");
            if (!is_expect and !is_allow) continue;

            if (!has_computed_owner_meta) {
                has_computed_owner_meta = true;
                cached_owner_bounds = computeCstSubtreeByteBounds(token_buffer, cst_arena, owner_cst);
                sibling_has_cfg = inspectOwnerSiblingAttrs(source, token_buffer, cst_arena, owner_cst).has_cfg;
            }
            const owner_bounds = cached_owner_bounds orelse break;

            const attr_bounds = computeCstSubtreeByteBounds(token_buffer, cst_arena, child_cst) orelse continue;
            const name_rec = token_buffer.getToken(name_tok);

            var attr_raw_sels: [64]RawSelectorItem = undefined;
            var attr_sel_count: usize = 0;
            var reason_start: u32 = 0;
            var reason_end: u32 = 0;

            // Collect leaf tokens inside `(...)` of `.attribute`:
            var leaf_toks: [256]TokenIndex = undefined;
            var leaf_count: usize = 0;
            var sub_i: usize = child_cur + 1;
            while (sub_i < next_child_cur and leaf_count < leaf_toks.len) : (sub_i += 1) {
                const sub_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_i)));
                if (sub_rec.subtree_size <= 1 and !sub_rec.flags.is_missing_or_injected and
                    !sub_rec.token.isNone() and sub_rec.token.asInt() < tok_count)
                {
                    const tr = token_buffer.getToken(sub_rec.token);
                    if (!tr.flags.is_synthesized and tr.kind != .eof) {
                        leaf_toks[leaf_count] = sub_rec.token;
                        leaf_count += 1;
                    }
                }
            }

            // Find opening `(` after attribute name:
            var idx_l: usize = 0;
            while (idx_l < leaf_count and token_buffer.getToken(leaf_toks[idx_l]).kind != .lparen) : (idx_l += 1) {}
            if (idx_l < leaf_count) {
                idx_l += 1;
                while (idx_l < leaf_count) {
                    const cur_tok = leaf_toks[idx_l];
                    const cur_rec = token_buffer.getToken(cur_tok);
                    if (cur_rec.kind == .rparen) break;
                    if (cur_rec.kind == .comma) {
                        idx_l += 1;
                        continue;
                    }

                    // Check `reason: "…"`:
                    if (cur_rec.kind == .ident and idx_l + 2 < leaf_count) {
                        const sep_kind = token_buffer.getToken(leaf_toks[idx_l + 1]).kind;
                        if (sep_kind == .colon or sep_kind == .eq) {
                            const key_lex = source[cur_rec.byte_offset .. cur_rec.byte_offset + cur_rec.byte_len];
                            const val_rec = token_buffer.getToken(leaf_toks[idx_l + 2]);
                            if (std.mem.eql(u8, key_lex, "reason") and val_rec.kind == .string_lit) {
                                const str_bounds = extractStringLiteralInteriorBounds(
                                    source,
                                    val_rec.byte_offset,
                                    val_rec.byte_offset + val_rec.byte_len,
                                );
                                reason_start = str_bounds.start;
                                reason_end = str_bounds.end;
                            }
                            idx_l += 3;
                            continue;
                        }
                    }

                    if (isSelectorWordTokenKind(cur_rec.kind)) {
                        const sel_start = cur_rec.byte_offset;
                        var prev_end = cur_rec.byte_offset + @as(u32, cur_rec.byte_len);
                        var is_contiguous = true;
                        idx_l += 1;
                        while (idx_l + 1 < leaf_count and
                            token_buffer.getToken(leaf_toks[idx_l]).kind == .minus and
                            isSelectorWordTokenKind(token_buffer.getToken(leaf_toks[idx_l + 1]).kind))
                        {
                            const minus_rec = token_buffer.getToken(leaf_toks[idx_l]);
                            const next_rec = token_buffer.getToken(leaf_toks[idx_l + 1]);
                            if (minus_rec.byte_offset != prev_end or next_rec.byte_offset != minus_rec.byte_offset + 1) {
                                is_contiguous = false;
                            }
                            prev_end = next_rec.byte_offset + @as(u32, next_rec.byte_len);
                            idx_l += 2;
                        }
                        if (is_contiguous and prev_end <= source.len) {
                            const raw_sel = source[sel_start..prev_end];
                            if (diag.lookupLintRuleBySelector(raw_sel) == .rule) {
                                const rule_id = diag.lookupLintRuleBySelector(raw_sel).rule;
                                if (attr_sel_count < attr_raw_sels.len) {
                                    attr_raw_sels[attr_sel_count] = .{
                                        .rule_id = rule_id,
                                        .start_byte = sel_start,
                                        .end_byte = prev_end,
                                    };
                                    attr_sel_count += 1;
                                }
                            }
                        }
                        continue;
                    }
                    idx_l += 1;
                }
            }

            if (attr_sel_count == 0) continue;
            const sel_meta = try appendPrunableSelectorSpans(allocator, &selectors, attr_raw_sels[0..attr_sel_count]);

            // Compute full attribute removal span (whole line if standalone on its line, else trailing spaces):
            const start_loc = line_index.resolveLineCol(source, attr_bounds.start_byte);
            const end_loc = line_index.resolveLineCol(source, attr_bounds.end_byte);
            const start_lb = line_index.getLineBounds(source, start_loc.line - 1);
            const end_lb = line_index.getLineBounds(source, end_loc.line - 1);

            var rem_start = attr_bounds.start_byte;
            var rem_end = attr_bounds.end_byte;
            if (isHorizontalBlank(source[start_lb.start..attr_bounds.start_byte]) and
                isHorizontalBlank(source[attr_bounds.end_byte..end_lb.end]))
            {
                rem_start = start_lb.start;
                rem_end = advancePastLineBreak(source, end_lb.end);
            } else {
                while (rem_end < end_lb.end and (source[rem_end] == ' ' or source[rem_end] == '\t')) {
                    rem_end += 1;
                }
            }

            try raw_ast.append(allocator, .{
                .target_start_byte = owner_bounds.start_byte,
                .target_end_byte = owner_bounds.end_byte,
                .directive_remove_start = rem_start,
                .directive_remove_end = rem_end,
                .directive_head_start = attr_bounds.start_byte,
                .directive_head_end = name_rec.byte_offset + @as(u32, name_rec.byte_len),
                .allow_kw_start = if (is_allow) name_rec.byte_offset else 0,
                .allow_kw_end = if (is_allow) name_rec.byte_offset + @as(u32, name_rec.byte_len) else 0,
                .reason_start = reason_start,
                .reason_end = reason_end,
                .own_mask = sel_meta.mask,
                .selector_slice_start = sel_meta.start,
                .selector_count = sel_meta.count,
                .mode = if (is_expect) .expect else .allow,
                .decl_order = decl_order_counter,
                .has_sibling_cfg = sibling_has_cfg,
                .is_above_line_comment = false,
            });
            decl_order_counter +%= 1;
        }
    }

    var built = try buildSuppressionTable(
        allocator,
        file_allow_mask,
        file_expect_mask,
        file_directives.items,
        raw_ast.items,
        line_spans.items,
        selectors.items,
    );
    errdefer built.deinit(allocator);
    built.file_id = file_id;
    built.is_generated_file = is_generated;
    built.directive_errors = try allocator.dupe(DirectiveErrorRecord, directive_errors.items);
    built.mid_file_directives = try allocator.dupe(MidFileDirectiveRecord, mid_file_directives.items);
    built.above_line_hoists = try allocator.dupe(AboveLineHoistRecord, above_line_hoists.items);
    return built;
}

/// Checks whether `cand` is suppressed across Scopes 4 -> 3 -> 2 (innermost wins) and updates `tracker`.
pub fn isCandidateSuppressed(
    table: *const SuppressionTable,
    tracker: *FulfillmentTracker,
    cand: RawLintCandidate,
) bool {
    const bit = cand.rule_id.bit();

    // [1] O(1) Fast Path (>99% of candidates exit immediately in 2 CPU instructions):
    if ((table.any_suppressed_mask & bit) == 0) return false;

    const pos = cand.start_byte;

    // [2] Scope 4 (Innermost): Single-Line Disjoint Span (`O(log L)`, 0 parent hops):
    if (findDisjointLineSpan(table.line_spans, pos)) |line_idx| {
        if ((table.line_spans[line_idx].own_mask & bit) != 0) {
            tracker.line_fulfilled[line_idx] |= bit;
            return true;
        }
    }

    // [3] Scope 3: Laminar AST Interval Tree (`O(log K)` binary search + `parent_idx` hop):
    const slice = table.ast_spans.slice();
    const starts = slice.items(.start_byte);
    if (rightmostStartAtOrBefore(starts, pos)) |initial_idx| {
        const ends = slice.items(.end_byte);
        const parents = slice.items(.parent_idx);
        const own_masks = slice.items(.own_mask);
        const eff_masks = slice.items(.eff_mask);

        var cur: u16 = @intCast(initial_idx);
        while (cur != SuppressionTable.NONE_IDX and pos >= ends[cur]) {
            cur = parents[cur];
        }
        if (cur != SuppressionTable.NONE_IDX and (eff_masks[cur] & bit) != 0) {
            while (cur != SuppressionTable.NONE_IDX and (own_masks[cur] & bit) == 0) {
                cur = parents[cur];
            }
            assert(cur != SuppressionTable.NONE_IDX);
            tracker.ast_fulfilled[cur] |= bit;
            return true;
        }
    }

    // [4] Scope 2 (Outermost In-File): Whole-File Preamble Bitmasks (`O(1)`):
    if (((table.file_expect_mask | table.file_allow_mask) & bit) != 0) {
        tracker.file_fulfilled_mask |= bit;
        return true;
    }

    return false;
}

/// Emits surgical `MachineApplicable` `TextEdit`s pruning unfulfilled `file-expect`, `@expect`, and `expect(…)` rules (`W0002`).
pub fn collectStaleExpectEdits(
    allocator: Allocator,
    file_id: FileId,
    empty_str_id: StringId,
    table: *const SuppressionTable,
    tracker: *const FulfillmentTracker,
    active_filter_mask: RuleMask64,
    out_edits: *std.ArrayListUnmanaged(TextEdit),
) !void {
    // [1] Scope 2 (`file-expect` preamble directives):
    for (table.file_directives) |file_dir| {
        if (file_dir.mode != @backingInt(DirectiveMode.expect)) continue;
        const own = file_dir.own_mask & active_filter_mask;
        if (own == 0) continue;
        const unfulfilled = own & ~tracker.file_fulfilled_mask;
        if (unfulfilled == 0) continue;

        if (unfulfilled == file_dir.own_mask) {
            try out_edits.append(allocator, .{
                .file_id = file_id,
                .start_byte = file_dir.directive_remove_start,
                .end_byte = file_dir.directive_remove_end,
                .replacement_id = empty_str_id,
            });
        } else {
            for (table.selectors[file_dir.selector_slice_start .. file_dir.selector_slice_start + file_dir.selector_count]) |sel| {
                if ((unfulfilled & sel.rule_id.bit()) != 0) {
                    try out_edits.append(allocator, .{
                        .file_id = file_id,
                        .start_byte = sel.prune_start_byte,
                        .end_byte = sel.prune_end_byte,
                        .replacement_id = empty_str_id,
                    });
                }
            }
        }
    }

    // [2] Scope 3 (`@expect` AST attributes):
    const ast_slice = table.ast_spans.slice();
    for (0..table.ast_spans.len) |idx| {
        if (ast_slice.items(.mode)[idx] != .expect) continue;
        const own = ast_slice.items(.own_mask)[idx] & active_filter_mask;
        if (own == 0) continue;
        const unfulfilled = own & ~tracker.ast_fulfilled[idx];
        if (unfulfilled == 0) continue;

        if (unfulfilled == ast_slice.items(.own_mask)[idx]) {
            try out_edits.append(allocator, .{
                .file_id = file_id,
                .start_byte = ast_slice.items(.directive_remove_start)[idx],
                .end_byte = ast_slice.items(.directive_remove_end)[idx],
                .replacement_id = empty_str_id,
            });
        } else {
            const sel_start = ast_slice.items(.selector_slice_start)[idx];
            const sel_count = ast_slice.items(.selector_count)[idx];
            for (table.selectors[sel_start .. sel_start + sel_count]) |sel| {
                if ((unfulfilled & sel.rule_id.bit()) != 0) {
                    try out_edits.append(allocator, .{
                        .file_id = file_id,
                        .start_byte = sel.prune_start_byte,
                        .end_byte = sel.prune_end_byte,
                        .replacement_id = empty_str_id,
                    });
                }
            }
        }
    }

    // [3] Scope 4 (`// corex check: expect(…)` trailing line directives):
    for (table.line_spans, 0..) |line_span, idx| {
        if (line_span.mode != @backingInt(DirectiveMode.expect)) continue;
        const own = line_span.own_mask & active_filter_mask;
        if (own == 0) continue;
        const unfulfilled = own & ~tracker.line_fulfilled[idx];
        if (unfulfilled == 0) continue;

        if (unfulfilled == line_span.own_mask) {
            try out_edits.append(allocator, .{
                .file_id = file_id,
                .start_byte = line_span.directive_remove_start,
                .end_byte = line_span.directive_remove_end,
                .replacement_id = empty_str_id,
            });
        } else {
            for (table.selectors[line_span.selector_slice_start .. line_span.selector_slice_start + line_span.selector_count]) |sel| {
                if ((unfulfilled & sel.rule_id.bit()) != 0) {
                    try out_edits.append(allocator, .{
                        .file_id = file_id,
                        .start_byte = sel.prune_start_byte,
                        .end_byte = sel.prune_end_byte,
                        .replacement_id = empty_str_id,
                    });
                }
            }
        }
    }
}

/// Emits non-suppressible `E0240` diagnostics for malformed `// corex check:` directives in `table`.
pub fn emitDirectiveErrorsIntoSink(
    source: []const u8,
    file_id: FileId,
    table: *const SuppressionTable,
    sink: *DiagnosticSink,
) !void {
    for (table.directive_errors) |err_rec| {
        const err_span = Span.init(file_id, err_rec.start_byte, err_rec.end_byte);
        const bad_text = source[err_rec.start_byte..@min(source.len, err_rec.end_byte)];
        var msg_buf: [256]u8 = undefined;
        var note_buf: [160]u8 = undefined;
        var note_slice: []const u8 = "";

        const msg = switch (err_rec.kind) {
            .unknown_action => std.fmt.bufPrint(
                &msg_buf,
                "unknown `corex check:` directive `{s}`; expected `expect`, `allow`, `file-expect`, or `file-allow`",
                .{bad_text},
            ) catch "invalid `corex check:` directive action",
            .missing_parens => "directive requires rule selectors in parentheses, e.g., `// corex check: expect(unused-binding) -- reason`",
            .empty_selector_list => "empty `corex check:` selector list is forbidden; specify at least one `W0xxx` code or `kebab-case` slug",
            .wildcard_forbidden => "wildcard `*` suppression is forbidden; list specific `W0xxx` codes or `kebab-case` slugs",
            .category_or_blanket_forbidden => std.fmt.bufPrint(
                &msg_buf,
                "category-wide or blanket suppression `{s}` is forbidden; specify individual lint rule slugs or `W0xxx` codes",
                .{bad_text},
            ) catch "category-wide or blanket suppression is forbidden",
            .non_suppressible_error_code => std.fmt.bufPrint(
                &msg_buf,
                "compiler error `{s}` cannot be suppressed; `corex check:` only applies to `W0xxx` lint warnings",
                .{bad_text},
            ) catch "compiler error cannot be suppressed",
            .non_suppressible_warning_code => std.fmt.bufPrint(
                &msg_buf,
                "warning `{s}` is not a suppressible lint rule",
                .{bad_text},
            ) catch "warning is not a suppressible lint rule",
            .spaced_hyphen_in_slug => "lint rule slug cannot contain spaces around `-`",
            .unknown_lint_rule => blk: {
                if (diag.suggestClosestLintRule(bad_text)) |suggestion| {
                    note_slice = std.fmt.bufPrint(&note_buf, "help: did you mean `{s}`?", .{suggestion}) catch "";
                }
                break :blk std.fmt.bufPrint(&msg_buf, "unknown lint rule `{s}`", .{bad_text}) catch "unknown lint rule";
            },
        };
        try sink.emit(.{
            .code = .e0240_invalid_suppression_selector,
            .severity = .err,
            .primary_span = err_span,
            .message = msg,
            .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
        });
    }
}

/// Evaluates post-pass `E0240`, `W0002`, `W0003`, `W0004`, and above-line `W0202` diagnostics and `SuggestedFix` edits.
pub fn collectStaleExpectDiagnosticsAndEdits(
    allocator: Allocator,
    source: []const u8,
    file_id: FileId,
    interner: *StringInterner,
    table: *const SuppressionTable,
    tracker: *FulfillmentTracker,
    effective_rules: EffectiveFileRules,
    active_filter_mask: RuleMask64,
    require_suppression_reason: bool,
    sink: *DiagnosticSink,
) !void {
    const empty_str_id = try interner.intern("");
    const expect_str_id = try interner.intern("expect");

    // [1] Emit `E0240` errors from malformed `// corex check:` comments (errors are never suppressible):
    try emitDirectiveErrorsIntoSink(source, file_id, table, sink);

    // [2] Emit `W0202` (`non-idiomatic-syntax`) on standalone above-line `// corex check:` comments (`Ruling 3.3`):
    if (effective_rules.isEnabled(.non_idiomatic_syntax)) {
        for (table.above_line_hoists) |hoist| {
            const cmt_span = Span.init(file_id, hoist.comment_start_byte, hoist.comment_end_byte);
            // Format `@expect(<selectors>[, reason: "<escaped>"])`:
            var attr_buf: std.ArrayListUnmanaged(u8) = .empty;
            defer attr_buf.deinit(allocator);
            const use_allow = hoist.target_has_cfg or table.is_generated_file or
                (!effective_rules.isEnabled(.prefer_expect_over_allow) and hoist.original_mode == .allow);
            try attr_buf.appendSlice(allocator, if (use_allow) "@allow(" else "@expect(");
            try attr_buf.appendSlice(allocator, source[hoist.selectors_raw_start..hoist.selectors_raw_end]);
            if (hoist.reason_end > hoist.reason_start) {
                try attr_buf.appendSlice(allocator, ", reason: \"");
                for (source[hoist.reason_start..hoist.reason_end]) |ch| {
                    if (ch == '"' or ch == '\\') try attr_buf.append(allocator, '\\');
                    try attr_buf.append(allocator, ch);
                }
                try attr_buf.append(allocator, '"');
            }
            try attr_buf.append(allocator, ')');

            var edits_buf: [2]TextEdit = undefined;
            var edit_len: usize = 0;
            if (!hoist.has_intervening_doc_comments) {
                edits_buf[0] = .{
                    .file_id = file_id,
                    .start_byte = hoist.comment_start_byte,
                    .end_byte = hoist.comment_end_byte,
                    .replacement_id = try interner.intern(attr_buf.items),
                };
                edit_len = 1;
            } else {
                const indent_slice = source[hoist.target_line_start..hoist.target_tok_start];
                var insert_buf: std.ArrayListUnmanaged(u8) = .empty;
                defer insert_buf.deinit(allocator);
                try insert_buf.appendSlice(allocator, indent_slice);
                try insert_buf.appendSlice(allocator, attr_buf.items);
                try insert_buf.append(allocator, '\n');

                edits_buf[0] = .{
                    .file_id = file_id,
                    .start_byte = hoist.comment_line_start,
                    .end_byte = hoist.comment_line_next_start,
                    .replacement_id = empty_str_id,
                };
                edits_buf[1] = .{
                    .file_id = file_id,
                    .start_byte = hoist.target_line_start,
                    .end_byte = hoist.target_line_start,
                    .replacement_id = try interner.intern(insert_buf.items),
                };
                edit_len = 2;
            }

            try sink.emit(.{
                .code = .w0202_non_idiomatic_construct,
                .severity = .warning,
                .primary_span = cmt_span,
                .message = "standalone `// corex check:` comment above an item or statement is non-idiomatic; attach `@expect` directly",
                .suggestions = &.{.{
                    .message = "hoist standalone suppression comment into an AST attribute",
                    .applicability = .machine_applicable,
                    .priority = .lint_idiom,
                    .edits = edits_buf[0..edit_len],
                }},
            });
        }
    }

    // [3] Evaluate `W0003` (`missing-suppression-reason`) and `W0004` (`prefer-expect-over-allow`) first
    //     so `@expect(W0004, …)` / `file-expect(W0003)` fulfill before `W0002` stale-expect checks run:
    const is_w0003_enabled = !table.is_generated_file and
        require_suppression_reason and
        effective_rules.isEnabled(.missing_suppression_reason);
    const is_w0004_enabled = !table.is_generated_file and
        effective_rules.isEnabled(.prefer_expect_over_allow);

    if (is_w0003_enabled) {
        for (table.file_directives) |file_dir| {
            const reason_slice = if (file_dir.reason_end > file_dir.reason_start)
                source[file_dir.reason_start..file_dir.reason_end]
            else
                "";
            if (!isValidSuppressionReason(reason_slice)) {
                const head_start = file_dir.directive_remove_start + file_dir.comment_start_offset;
                try sink.emit(.{
                    .code = .w0003_missing_suppression_reason,
                    .severity = .warning,
                    .primary_span = Span.init(file_id, head_start, file_dir.line_end_byte),
                    .message = "suppression directive requires a meaningful `-- <reason>` rationale (`>= 4` non-placeholder chars)",
                });
            }
        }
    }

    const ast_slice = table.ast_spans.slice();
    for (0..table.ast_spans.len) |idx| {
        if (ast_slice.items(.is_above_line_comment)[idx]) continue;

        if (is_w0003_enabled) {
            const r_start = ast_slice.items(.reason_start)[idx];
            const r_end = ast_slice.items(.reason_end)[idx];
            const reason_slice = if (r_end > r_start) source[r_start..r_end] else "";
            if (!isValidSuppressionReason(reason_slice)) {
                const head_start = ast_slice.items(.directive_head_start)[idx];
                const head_end = ast_slice.items(.directive_head_end)[idx];
                // Only suppressed if `file_*` or an *enclosing* parent suppresses `W0003`:
                const parent_i = ast_slice.items(.parent_idx)[idx];
                const reason_bit = RuleId.missing_suppression_reason.bit();
                const is_parent_suppressed = (((table.file_allow_mask | table.file_expect_mask) & reason_bit) != 0) or
                    (parent_i != SuppressionTable.NONE_IDX and (ast_slice.items(.eff_mask)[parent_i] & reason_bit) != 0);
                if (is_parent_suppressed) {
                    _ = isCandidateSuppressed(table, tracker, .{
                        .rule_id = .missing_suppression_reason,
                        .start_byte = head_start,
                        .end_byte = head_end,
                    });
                } else {
                    try sink.emit(.{
                        .code = .w0003_missing_suppression_reason,
                        .severity = .warning,
                        .primary_span = Span.init(file_id, head_start, head_end),
                        .message = "suppression attribute requires a meaningful `reason: \"…\"` (`>= 4` non-placeholder chars)",
                    });
                }
            }
        }

        if (is_w0004_enabled and
            ast_slice.items(.mode)[idx] == .allow and
            !ast_slice.items(.has_sibling_cfg)[idx])
        {
            const kw_start = ast_slice.items(.allow_kw_start)[idx];
            const kw_end = ast_slice.items(.allow_kw_end)[idx];
            if (!isCandidateSuppressed(table, tracker, .{
                .rule_id = .prefer_expect_over_allow,
                .start_byte = kw_start,
                .end_byte = kw_end,
            })) {
                try sink.emit(.{
                    .code = .w0004_prefer_expect_over_allow,
                    .severity = .warning,
                    .primary_span = Span.init(file_id, kw_start, kw_end),
                    .message = "prefer self-cleaning `@expect` over `@allow` on target-independent handwritten code",
                    .suggestions = &.{.{
                        .message = "replace `@allow` with `@expect`",
                        .applicability = .machine_applicable,
                        .priority = .lint_idiom,
                        .edits = &.{.{
                            .file_id = file_id,
                            .start_byte = kw_start,
                            .end_byte = kw_end,
                            .replacement_id = expect_str_id,
                        }},
                    }},
                });
            }
        }
    }

    for (table.line_spans) |line_span| {
        const cmt_start = line_span.directive_remove_start + line_span.comment_start_offset;
        if (is_w0003_enabled) {
            const reason_slice = if (line_span.reason_end > line_span.reason_start)
                source[line_span.reason_start..line_span.reason_end]
            else
                "";
            if (!isValidSuppressionReason(reason_slice)) {
                const is_outer_suppressed = (((table.file_allow_mask | table.file_expect_mask) & RuleId.missing_suppression_reason.bit()) != 0);
                if (is_outer_suppressed) {
                    tracker.file_fulfilled_mask |= RuleId.missing_suppression_reason.bit();
                } else {
                    try sink.emit(.{
                        .code = .w0003_missing_suppression_reason,
                        .severity = .warning,
                        .primary_span = Span.init(file_id, cmt_start, line_span.directive_remove_end),
                        .message = "trailing suppression directive requires a meaningful `-- <reason>` (`>= 4` non-placeholder chars)",
                    });
                }
            }
        }
        if (is_w0004_enabled and line_span.mode == @backingInt(DirectiveMode.allow)) {
            const kw_start = line_span.directive_remove_start + line_span.allow_kw_offset;
            const kw_end = kw_start + @as(u32, "allow".len);
            if (!isCandidateSuppressed(table, tracker, .{
                .rule_id = .prefer_expect_over_allow,
                .start_byte = kw_start,
                .end_byte = kw_end,
            })) {
                try sink.emit(.{
                    .code = .w0004_prefer_expect_over_allow,
                    .severity = .warning,
                    .primary_span = Span.init(file_id, kw_start, kw_end),
                    .message = "prefer self-cleaning `expect(…)` over `allow(…)` on handwritten lines",
                    .suggestions = &.{.{
                        .message = "replace `allow` with `expect`",
                        .applicability = .machine_applicable,
                        .priority = .lint_idiom,
                        .edits = &.{.{
                            .file_id = file_id,
                            .start_byte = kw_start,
                            .end_byte = kw_end,
                            .replacement_id = expect_str_id,
                        }},
                    }},
                });
            }
        }
    }

    // [4] Evaluate `W0002` (`unused-suppression`) across mid-file `file-*` and Scopes 2, 3, and 4:
    if (!effective_rules.isEnabled(.unused_suppression)) return;
    const effective_active_mask = active_filter_mask & ~effective_rules.disabled_mask;

    for (table.mid_file_directives) |mid_dir| {
        const kw = if (mid_dir.is_file_expect) "file-expect" else "file-allow";
        var msg_buf: [160]u8 = undefined;
        const msg = std.fmt.bufPrint(
            &msg_buf,
            "file-wide `corex check: {s}` directive must appear in the file preamble before any items",
            .{kw},
        ) catch "mid-file `corex check: file-*` directive has no effect";
        try sink.emit(.{
            .code = .w0002_unused_suppression,
            .severity = .warning,
            .primary_span = Span.init(file_id, mid_dir.comment_start_byte, mid_dir.comment_end_byte),
            .message = msg,
            .suggestions = &.{.{
                .message = "remove ineffective mid-file directive",
                .applicability = .machine_applicable,
                .priority = .lint_idiom,
                .edits = &.{.{
                    .file_id = file_id,
                    .start_byte = mid_dir.remove_start_byte,
                    .end_byte = mid_dir.remove_end_byte,
                    .replacement_id = empty_str_id,
                }},
            }},
        });
    }

    // Scope 2 `file-expect`:
    for (table.file_directives) |file_dir| {
        if (file_dir.mode != @backingInt(DirectiveMode.expect)) continue;
        const own = file_dir.own_mask & effective_active_mask;
        if (own == 0) continue;
        const unfulfilled = own & ~tracker.file_fulfilled_mask;
        if (unfulfilled == 0) continue;

        var note_buf: [192]u8 = undefined;
        const note_slice = if (file_dir.reason_end > file_dir.reason_start)
            std.fmt.bufPrint(
                &note_buf,
                "note: original suppression reason: \"{s}\"",
                .{source[file_dir.reason_start..file_dir.reason_end]},
            ) catch ""
        else
            "";

        if (unfulfilled == file_dir.own_mask) {
            const cmt_start = file_dir.directive_remove_start + file_dir.comment_start_offset;
            try sink.emit(.{
                .code = .w0002_unused_suppression,
                .severity = .warning,
                .primary_span = Span.init(file_id, cmt_start, file_dir.line_end_byte),
                .message = "`file-expect` suppression was not fulfilled in this file",
                .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
                .suggestions = &.{.{
                    .message = "remove unfulfilled `file-expect` directive",
                    .applicability = .machine_applicable,
                    .priority = .lint_idiom,
                    .edits = &.{.{
                        .file_id = file_id,
                        .start_byte = file_dir.directive_remove_start,
                        .end_byte = file_dir.directive_remove_end,
                        .replacement_id = empty_str_id,
                    }},
                }},
            });
        } else {
            for (table.selectors[file_dir.selector_slice_start .. file_dir.selector_slice_start + file_dir.selector_count]) |sel| {
                if ((unfulfilled & sel.rule_id.bit()) == 0) continue;
                var msg_buf: [160]u8 = undefined;
                const msg = std.fmt.bufPrint(
                    &msg_buf,
                    "`file-expect({s})` was not fulfilled in this file",
                    .{sel.rule_id.asSlug()},
                ) catch "unfulfilled `file-expect` rule selector";
                try sink.emit(.{
                    .code = .w0002_unused_suppression,
                    .severity = .warning,
                    .primary_span = sel.selectorSpan(file_id),
                    .message = msg,
                    .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
                    .suggestions = &.{.{
                        .message = "prune unfulfilled selector",
                        .applicability = .machine_applicable,
                        .priority = .lint_idiom,
                        .edits = &.{.{
                            .file_id = file_id,
                            .start_byte = sel.prune_start_byte,
                            .end_byte = sel.prune_end_byte,
                            .replacement_id = empty_str_id,
                        }},
                    }},
                });
            }
        }
    }

    // Scope 3 `@expect`:
    for (0..table.ast_spans.len) |idx| {
        if (ast_slice.items(.mode)[idx] != .expect) continue;
        const own = ast_slice.items(.own_mask)[idx] & effective_active_mask;
        if (own == 0) continue;
        const unfulfilled = own & ~tracker.ast_fulfilled[idx];
        if (unfulfilled == 0) continue;

        const r_start = ast_slice.items(.reason_start)[idx];
        const r_end = ast_slice.items(.reason_end)[idx];
        var note_buf: [192]u8 = undefined;
        const note_slice = if (r_end > r_start)
            std.fmt.bufPrint(&note_buf, "note: original suppression reason: \"{s}\"", .{source[r_start..r_end]}) catch ""
        else
            "";

        if (unfulfilled == ast_slice.items(.own_mask)[idx]) {
            const sel_first = table.selectors[ast_slice.items(.selector_slice_start)[idx]];
            var msg_buf: [160]u8 = undefined;
            const msg = if (ast_slice.items(.selector_count)[idx] == 1)
                std.fmt.bufPrint(
                    &msg_buf,
                    "`@expect({s})` was not fulfilled in this construct",
                    .{sel_first.rule_id.asSlug()},
                ) catch "`@expect` suppression was not fulfilled"
            else
                "`@expect(…)` suppression had zero fulfilled rules in this construct";
            try sink.emit(.{
                .code = .w0002_unused_suppression,
                .severity = .warning,
                .primary_span = Span.init(
                    file_id,
                    ast_slice.items(.directive_head_start)[idx],
                    ast_slice.items(.directive_head_end)[idx],
                ),
                .message = msg,
                .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
                .suggestions = &.{.{
                    .message = "remove unfulfilled `@expect` attribute",
                    .applicability = .machine_applicable,
                    .priority = .lint_idiom,
                    .edits = &.{.{
                        .file_id = file_id,
                        .start_byte = ast_slice.items(.directive_remove_start)[idx],
                        .end_byte = ast_slice.items(.directive_remove_end)[idx],
                        .replacement_id = empty_str_id,
                    }},
                }},
            });
        } else {
            const sel_start = ast_slice.items(.selector_slice_start)[idx];
            const sel_count = ast_slice.items(.selector_count)[idx];
            for (table.selectors[sel_start .. sel_start + sel_count]) |sel| {
                if ((unfulfilled & sel.rule_id.bit()) == 0) continue;
                var msg_buf: [160]u8 = undefined;
                const msg = std.fmt.bufPrint(
                    &msg_buf,
                    "`@expect({s})` was not fulfilled in this construct",
                    .{sel.rule_id.asSlug()},
                ) catch "unfulfilled `@expect` rule selector";
                try sink.emit(.{
                    .code = .w0002_unused_suppression,
                    .severity = .warning,
                    .primary_span = sel.selectorSpan(file_id),
                    .message = msg,
                    .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
                    .suggestions = &.{.{
                        .message = "prune unfulfilled selector",
                        .applicability = .machine_applicable,
                        .priority = .lint_idiom,
                        .edits = &.{.{
                            .file_id = file_id,
                            .start_byte = sel.prune_start_byte,
                            .end_byte = sel.prune_end_byte,
                            .replacement_id = empty_str_id,
                        }},
                    }},
                });
            }
        }
    }

    // Scope 4 trailing `expect(…)`:
    for (table.line_spans, 0..) |line_span, idx| {
        if (line_span.mode != @backingInt(DirectiveMode.expect)) continue;
        const own = line_span.own_mask & effective_active_mask;
        if (own == 0) continue;
        const unfulfilled = own & ~tracker.line_fulfilled[idx];
        if (unfulfilled == 0) continue;

        var note_buf: [192]u8 = undefined;
        const note_slice = if (line_span.reason_end > line_span.reason_start)
            std.fmt.bufPrint(
                &note_buf,
                "note: original suppression reason: \"{s}\"",
                .{source[line_span.reason_start..line_span.reason_end]},
            ) catch ""
        else
            "";

        if (unfulfilled == line_span.own_mask) {
            const cmt_start = line_span.directive_remove_start + line_span.comment_start_offset;
            try sink.emit(.{
                .code = .w0002_unused_suppression,
                .severity = .warning,
                .primary_span = Span.init(file_id, cmt_start, line_span.directive_remove_end),
                .message = "trailing `expect(…)` suppression was not fulfilled on this line",
                .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
                .suggestions = &.{.{
                    .message = "remove unfulfilled trailing `corex check:` directive",
                    .applicability = .machine_applicable,
                    .priority = .lint_idiom,
                    .edits = &.{.{
                        .file_id = file_id,
                        .start_byte = line_span.directive_remove_start,
                        .end_byte = line_span.directive_remove_end,
                        .replacement_id = empty_str_id,
                    }},
                }},
            });
        } else {
            for (table.selectors[line_span.selector_slice_start .. line_span.selector_slice_start + line_span.selector_count]) |sel| {
                if ((unfulfilled & sel.rule_id.bit()) == 0) continue;
                var msg_buf: [160]u8 = undefined;
                const msg = std.fmt.bufPrint(
                    &msg_buf,
                    "trailing `expect({s})` was not fulfilled on this line",
                    .{sel.rule_id.asSlug()},
                ) catch "unfulfilled trailing `expect` selector";
                try sink.emit(.{
                    .code = .w0002_unused_suppression,
                    .severity = .warning,
                    .primary_span = sel.selectorSpan(file_id),
                    .message = msg,
                    .notes = if (note_slice.len > 0) &.{note_slice} else &.{},
                    .suggestions = &.{.{
                        .message = "prune unfulfilled selector",
                        .applicability = .machine_applicable,
                        .priority = .lint_idiom,
                        .edits = &.{.{
                            .file_id = file_id,
                            .start_byte = sel.prune_start_byte,
                            .end_byte = sel.prune_end_byte,
                            .replacement_id = empty_str_id,
                        }},
                    }},
                });
            }
        }
    }
}

/// Computes the minimum `#` guard count (`>= 1` if any `"` appears, `0` otherwise) for a raw string `payload`.
pub fn computeMinRawQuoteGuardHashes(payload: []const u8) usize {
    var needed: usize = 0;
    var cursor: usize = 0;
    while (cursor < payload.len) {
        if (payload[cursor] == '"') {
            var run_hashes: usize = 0;
            var scan_idx = cursor + 1;
            while (scan_idx < payload.len and payload[scan_idx] == '#') : (scan_idx += 1) {
                run_hashes += 1;
            }
            if (run_hashes + 1 > needed) {
                needed = run_hashes + 1;
            }
            cursor = scan_idx;
            continue;
        }
        cursor += 1;
    }
    return needed;
}

/// Formats `raw_digits` (ignoring existing `_` bytes) with `_` separators every `group_width` digits from the right.
pub fn formatGroupedNumericDigits(
    allocator: Allocator,
    raw_digits: []const u8,
    group_width: usize,
    is_forcing_upper_hex: bool,
) ![]u8 {
    var digit_count: usize = 0;
    for (raw_digits) |byte_val| {
        if (byte_val != '_') digit_count += 1;
    }
    if (digit_count == 0 or group_width == 0) {
        return allocator.dupe(u8, "");
    }
    const sep_count: usize = if (digit_count > group_width) (digit_count - 1) / group_width else 0;
    var out_buf = try allocator.alloc(u8, digit_count + sep_count);
    var write_idx: usize = 0;
    var remaining_digits: usize = digit_count;
    for (raw_digits) |byte_val| {
        if (byte_val == '_') continue;
        out_buf[write_idx] = if (is_forcing_upper_hex) std.ascii.toUpper(byte_val) else byte_val;
        write_idx += 1;
        remaining_digits -= 1;
        if (remaining_digits > 0 and (remaining_digits % group_width) == 0) {
            out_buf[write_idx] = '_';
            write_idx += 1;
        }
    }
    return out_buf;
}

/// Synthesizes and emits the canonical `W0xxx` `Diagnostic` (and lazy `SuggestedFix`) for a Lexer/CST `RawLintCandidate`.
pub fn materializeLexCstLintCandidate(
    source: []const u8,
    file_id: FileId,
    interner: ?*StringInterner,
    cand: RawLintCandidate,
    sink: *DiagnosticSink,
) !void {
    const arena_alloc = sink.arena.asAllocator();
    const cand_span = Span.init(file_id, cand.start_byte, cand.end_byte);
    const start_idx: usize = @min(@as(usize, cand.start_byte), source.len);
    const end_idx: usize = @min(@max(@as(usize, cand.end_byte), start_idx), source.len);

    switch (cand.rule_id) {
        .redundant_escape_sequence => {
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = "unnecessary backslash escape; character stands for itself",
                .style = .primary,
            };
            var fixes: []const SuggestedFix = &.{};
            if (cand.fix_kind == 1 and start_idx + 1 <= end_idx) {
                if (interner) |str_interner| {
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = cand.start_byte,
                        .end_byte = cand.end_byte,
                        .replacement_id = try str_interner.intern(source[start_idx + 1 .. end_idx]),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = "remove redundant backslash escape",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                }
            }
            try sink.emit(.{
                .code = .w0101_redundant_escape_sequence,
                .severity = .warning,
                .primary_span = cand_span,
                .message = "redundant character escape sequence in literal",
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .unicode_trojan_control => {
            const codepoint: u21 = @intCast(cand.aux_payload & 0x1FFFFF);
            const msg = try std.fmt.allocPrint(
                arena_alloc,
                "bidirectional or invisible Unicode control character `U+{X:0>4}` in source",
                .{codepoint},
            );
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = "Trojan Source or invisible formatting control character",
                .style = .primary,
            };
            var fixes: []const SuggestedFix = &.{};
            if (interner) |str_interner| {
                if (cand.fix_kind == 1) {
                    const escaped_text = try std.fmt.allocPrint(arena_alloc, "\\u{{{X:0>4}}}", .{codepoint});
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = cand.start_byte,
                        .end_byte = cand.end_byte,
                        .replacement_id = try str_interner.intern(escaped_text),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = "escape invisible Unicode control character as `\\u{…}`",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                } else if (cand.fix_kind == 2) {
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = cand.start_byte,
                        .end_byte = cand.end_byte,
                        .replacement_id = try str_interner.intern(""),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = "remove invisible Unicode control character",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                } else if (cand.fix_kind == 3) {
                    const lit_start_u32 = cand.node_or_tok;
                    const lit_end_u32: u32 = @intCast(cand.aux_payload >> 32);
                    const lit_s: usize = @min(@as(usize, lit_start_u32), source.len);
                    const lit_e: usize = @min(@max(@as(usize, lit_end_u32), lit_s), source.len);
                    const raw_lit = source[lit_s..lit_e];
                    if (@import("lexer.zig").cookStringLiteral(arena_alloc, raw_lit)) |decoded_raw_body| {
                        var cooked_buf: std.ArrayListUnmanaged(u8) = .empty;
                        try cooked_buf.append(arena_alloc, '"');
                        var pos: usize = 0;
                        while (pos < decoded_raw_body.len) {
                            const byte_val = decoded_raw_body[pos];
                            if (byte_val < 0x80) {
                                switch (byte_val) {
                                    '\\' => try cooked_buf.appendSlice(arena_alloc, "\\\\"),
                                    '"' => try cooked_buf.appendSlice(arena_alloc, "\\\""),
                                    '\n' => try cooked_buf.appendSlice(arena_alloc, "\\n"),
                                    '\r' => try cooked_buf.appendSlice(arena_alloc, "\\r"),
                                    '\t' => try cooked_buf.appendSlice(arena_alloc, "\\t"),
                                    0 => try cooked_buf.appendSlice(arena_alloc, "\\0"),
                                    else => try cooked_buf.append(arena_alloc, byte_val),
                                }
                                pos += 1;
                            } else {
                                const seq_len = std.unicode.utf8ByteSequenceLength(byte_val) catch 1;
                                if (pos + seq_len <= decoded_raw_body.len) {
                                    if (std.unicode.utf8Decode(decoded_raw_body[pos .. pos + seq_len])) |inner_cp| {
                                        if (unicode_confusables.isTrojanControlCodepoint(inner_cp, @max(@as(usize, 1), pos))) {
                                            var esc_tmp: [12]u8 = undefined;
                                            const esc_str = try std.fmt.bufPrint(&esc_tmp, "\\u{{{X:0>4}}}", .{inner_cp});
                                            try cooked_buf.appendSlice(arena_alloc, esc_str);
                                        } else {
                                            try cooked_buf.appendSlice(arena_alloc, decoded_raw_body[pos .. pos + seq_len]);
                                        }
                                        pos += seq_len;
                                        continue;
                                    } else |_| {}
                                }
                                try cooked_buf.append(arena_alloc, byte_val);
                                pos += 1;
                            }
                        }
                        try cooked_buf.append(arena_alloc, '"');
                        const edits = try arena_alloc.alloc(TextEdit, 1);
                        edits[0] = .{
                            .file_id = file_id,
                            .start_byte = lit_start_u32,
                            .end_byte = lit_end_u32,
                            .replacement_id = try str_interner.intern(cooked_buf.items),
                        };
                        const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                        fix_arr[0] = .{
                            .message = "convert raw string to cooked literal and escape control characters",
                            .applicability = .machine_applicable,
                            .priority = .syntax_canonicalization,
                            .edits = edits,
                        };
                        fixes = fix_arr;
                    } else |_| {}
                }
            }
            try sink.emit(.{
                .code = .w0102_unicode_trojan_control,
                .severity = .warning,
                .primary_span = cand_span,
                .message = msg,
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .ambiguous_unicode_text => {
            const codepoint: u21 = @intCast(cand.aux_payload & 0x1FFFFF);
            var skel_buf: [3]u8 = undefined;
            const raw_skel: []const u8 = if (codepoint == 0x2014 and cand.fix_kind == 1)
                "\u{2013}"
            else if (codepoint == 0x2014)
                "-"
            else if (unicode_confusables.lookupConfusable(codepoint)) |entry|
                entry.writeSkeleton(&skel_buf)
            else
                "";

            const msg = try std.fmt.allocPrint(
                arena_alloc,
                "ambiguous or confusable Unicode character `U+{X:0>4}` in text",
                .{codepoint},
            );
            const lbl_txt = if (raw_skel.len > 0)
                try std.fmt.allocPrint(arena_alloc, "visually confusable character; consider `{s}`", .{raw_skel})
            else
                "visually confusable Unicode character";
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{ .span = cand_span, .label = lbl_txt, .style = .primary };

            var fixes: []const SuggestedFix = &.{};
            if (cand.fix_kind >= 1 and raw_skel.len > 0) {
                if (interner) |str_interner| {
                    var rep_buf: std.ArrayListUnmanaged(u8) = .empty;
                    for (raw_skel) |skel_byte| {
                        if (cand.fix_kind == 3 and skel_byte == '"') {
                            try rep_buf.appendSlice(arena_alloc, "\\\"");
                        } else if (cand.fix_kind == 4 and skel_byte == '\'') {
                            try rep_buf.appendSlice(arena_alloc, "\\'");
                        } else if ((cand.fix_kind == 3 or cand.fix_kind == 4) and skel_byte == '\\') {
                            try rep_buf.appendSlice(arena_alloc, "\\\\");
                        } else {
                            try rep_buf.append(arena_alloc, skel_byte);
                        }
                    }
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = cand.start_byte,
                        .end_byte = cand.end_byte,
                        .replacement_id = try str_interner.intern(rep_buf.items),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = "replace ambiguous Unicode character with canonical equivalent",
                        .applicability = .maybe_incorrect,
                        .priority = .lint_idiom,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                }
            }
            try sink.emit(.{
                .code = .w0104_ambiguous_unicode_text,
                .severity = .warning,
                .primary_span = cand_span,
                .message = msg,
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .useless_format_string => {
            const hash_count: usize = cand.aux_u16;
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = "format string contains zero `{…}` interpolation holes; remove `f` prefix",
                .style = .primary,
            };
            var fixes: []const SuggestedFix = &.{};
            if (cand.fix_kind == 1) {
                if (interner) |str_interner| {
                    const header_len: usize = 1 + hash_count + 1;
                    const footer_len: usize = 1 + hash_count;
                    if (end_idx >= start_idx + header_len + footer_len) {
                        const inner_raw = source[start_idx + header_len .. end_idx - footer_len];
                        const has_backslash = std.mem.indexOfScalar(u8, inner_raw, '\\') != null;
                        const has_quote = std.mem.indexOfScalar(u8, inner_raw, '"') != null;

                        var builder: std.ArrayListUnmanaged(u8) = .empty;
                        if (hash_count > 0 and has_quote and !has_backslash) {
                            var unescaped: std.ArrayListUnmanaged(u8) = .empty;
                            var idx: usize = 0;
                            while (idx < inner_raw.len) {
                                if ((inner_raw[idx] == '{' or inner_raw[idx] == '}') and
                                    idx + 1 < inner_raw.len and
                                    inner_raw[idx + 1] == inner_raw[idx])
                                {
                                    try unescaped.append(arena_alloc, inner_raw[idx]);
                                    idx += 2;
                                } else {
                                    try unescaped.append(arena_alloc, inner_raw[idx]);
                                    idx += 1;
                                }
                            }
                            const req_hashes = @max(@as(usize, 1), computeMinRawQuoteGuardHashes(unescaped.items));
                            try builder.append(arena_alloc, 'r');
                            var h_idx: usize = 0;
                            while (h_idx < req_hashes) : (h_idx += 1) try builder.append(arena_alloc, '#');
                            try builder.append(arena_alloc, '"');
                            try builder.appendSlice(arena_alloc, unescaped.items);
                            try builder.append(arena_alloc, '"');
                            h_idx = 0;
                            while (h_idx < req_hashes) : (h_idx += 1) try builder.append(arena_alloc, '#');
                        } else {
                            try builder.append(arena_alloc, '"');
                            var idx: usize = 0;
                            while (idx < inner_raw.len) {
                                if (inner_raw[idx] == '\\') {
                                    if (idx + 1 < inner_raw.len) {
                                        try builder.appendSlice(arena_alloc, inner_raw[idx .. idx + 2]);
                                        idx += 2;
                                    } else {
                                        try builder.appendSlice(arena_alloc, "\\\\");
                                        idx += 1;
                                    }
                                } else if ((inner_raw[idx] == '{' or inner_raw[idx] == '}') and
                                    idx + 1 < inner_raw.len and
                                    inner_raw[idx + 1] == inner_raw[idx])
                                {
                                    try builder.append(arena_alloc, inner_raw[idx]);
                                    idx += 2;
                                } else if (inner_raw[idx] == '"') {
                                    try builder.appendSlice(arena_alloc, "\\\"");
                                    idx += 1;
                                } else {
                                    try builder.append(arena_alloc, inner_raw[idx]);
                                    idx += 1;
                                }
                            }
                            try builder.append(arena_alloc, '"');
                        }
                        const edits = try arena_alloc.alloc(TextEdit, 1);
                        edits[0] = .{
                            .file_id = file_id,
                            .start_byte = cand.start_byte,
                            .end_byte = cand.end_byte,
                            .replacement_id = try str_interner.intern(builder.items),
                        };
                        const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                        fix_arr[0] = .{
                            .message = "remove `f` prefix from static string literal",
                            .applicability = .machine_applicable,
                            .priority = .lint_idiom,
                            .edits = edits,
                        };
                        fixes = fix_arr;
                    }
                }
            }
            try sink.emit(.{
                .code = .w0119_useless_format_string,
                .severity = .warning,
                .primary_span = cand_span,
                .message = "interpolated format string contains no `{…}` holes (`useless-format-string`)",
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .needless_raw_string_hashes => {
            const req_hashes: u32 = cand.aux_u16;
            const hash_count: u32 = @intCast(cand.aux_payload);
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = if (cand.fix_kind == 1 or cand.fix_kind == 3)
                    "raw string contains neither `\"` nor `\\`; remove raw delimiter"
                else
                    "delimiter uses more `#` quote guards than needed",
                .style = .primary,
            };
            var fixes: []const SuggestedFix = &.{};
            if (cand.fix_kind >= 1 and cand.fix_kind <= 5) {
                if (interner) |str_interner| {
                    const empty_id = try str_interner.intern("");
                    var edit_list: std.ArrayListUnmanaged(TextEdit) = .empty;
                    switch (cand.fix_kind) {
                        1 => {
                            try edit_list.append(arena_alloc, .{
                                .file_id = file_id,
                                .start_byte = cand.start_byte,
                                .end_byte = cand.start_byte + 1 + hash_count,
                                .replacement_id = empty_id,
                            });
                            if (hash_count > 0) {
                                try edit_list.append(arena_alloc, .{
                                    .file_id = file_id,
                                    .start_byte = cand.end_byte - hash_count,
                                    .end_byte = cand.end_byte,
                                    .replacement_id = empty_id,
                                });
                            }
                        },
                        2, 5 => {
                            try edit_list.append(arena_alloc, .{
                                .file_id = file_id,
                                .start_byte = cand.start_byte + 1 + req_hashes,
                                .end_byte = cand.start_byte + 1 + hash_count,
                                .replacement_id = empty_id,
                            });
                            try edit_list.append(arena_alloc, .{
                                .file_id = file_id,
                                .start_byte = cand.end_byte - hash_count,
                                .end_byte = cand.end_byte - req_hashes,
                                .replacement_id = empty_id,
                            });
                        },
                        3 => {
                            try edit_list.append(arena_alloc, .{
                                .file_id = file_id,
                                .start_byte = cand.start_byte + 1,
                                .end_byte = cand.start_byte + 2 + hash_count,
                                .replacement_id = empty_id,
                            });
                            if (hash_count > 0) {
                                try edit_list.append(arena_alloc, .{
                                    .file_id = file_id,
                                    .start_byte = cand.end_byte - hash_count,
                                    .end_byte = cand.end_byte,
                                    .replacement_id = empty_id,
                                });
                            }
                        },
                        4 => {
                            try edit_list.append(arena_alloc, .{
                                .file_id = file_id,
                                .start_byte = cand.start_byte + 2 + req_hashes,
                                .end_byte = cand.start_byte + 2 + hash_count,
                                .replacement_id = empty_id,
                            });
                            try edit_list.append(arena_alloc, .{
                                .file_id = file_id,
                                .start_byte = cand.end_byte - hash_count,
                                .end_byte = cand.end_byte - req_hashes,
                                .replacement_id = empty_id,
                            });
                        },
                        else => {},
                    }
                    if (edit_list.items.len > 0) {
                        const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                        fix_arr[0] = .{
                            .message = "simplify string literal delimiters",
                            .applicability = .machine_applicable,
                            .priority = .syntax_canonicalization,
                            .edits = edit_list.items,
                        };
                        fixes = fix_arr;
                    }
                }
            }
            try sink.emit(.{
                .code = .w0121_needless_raw_string_hashes,
                .severity = .warning,
                .primary_span = cand_span,
                .message = "unnecessary raw string prefix or `#` delimiter guards (`needless-raw-string-hashes`)",
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .ungrouped_numeric_literal => {
            const group_width: usize = cand.aux_u16 & 0xFF;
            const int_start: u32 = @intCast(cand.aux_payload >> 32);
            const int_end: u32 = @intCast(cand.aux_payload & 0xFFFF_FFFF);
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = "group integer digits with `_` separators for readability",
                .style = .primary,
            };
            var fixes: []const SuggestedFix = &.{};
            if ((cand.fix_kind == 1 or cand.fix_kind == 2) and
                int_start <= int_end and @as(usize, int_end) <= source.len)
            {
                if (interner) |str_interner| {
                    const is_fused_hex = (cand.fix_kind == 2);
                    const grouped_digits = try formatGroupedNumericDigits(
                        arena_alloc,
                        source[int_start..int_end],
                        group_width,
                        is_fused_hex,
                    );
                    const edit_start: u32 = if (is_fused_hex) cand.start_byte else int_start;
                    const rep_text = if (is_fused_hex)
                        try std.fmt.allocPrint(arena_alloc, "0x{s}", .{grouped_digits})
                    else
                        grouped_digits;
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = edit_start,
                        .end_byte = int_end,
                        .replacement_id = try str_interner.intern(rep_text),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = if (is_fused_hex)
                            "group hexadecimal digits and normalize to `0x` uppercase hex"
                        else
                            "insert canonical `_` digit-group separators",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                }
            }
            try sink.emit(.{
                .code = .w0122_ungrouped_numeric_literal,
                .severity = .warning,
                .primary_span = cand_span,
                .message = "large or inconsistently grouped numeric literal (`ungrouped-numeric-literal`)",
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .non_upper_hex_literal => {
            const mantissa_end: u32 = @intCast(cand.aux_payload >> 32);
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = "use lowercase `0x` prefix with uppercase `A`–`F` hexadecimal digits",
                .style = .primary,
            };
            var fixes: []const SuggestedFix = &.{};
            if (cand.fix_kind == 1 and cand.start_byte + 2 <= mantissa_end and
                @as(usize, mantissa_end) <= source.len)
            {
                if (interner) |str_interner| {
                    const m_end: usize = @intCast(mantissa_end);
                    var hex_buf = try arena_alloc.alloc(u8, m_end - start_idx);
                    hex_buf[0] = '0';
                    hex_buf[1] = 'x';
                    for (source[start_idx + 2 .. m_end], 2..) |byte_val, out_i| {
                        hex_buf[out_i] = std.ascii.toUpper(byte_val);
                    }
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = cand.start_byte,
                        .end_byte = mantissa_end,
                        .replacement_id = try str_interner.intern(hex_buf),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = "normalize hexadecimal literal to `0x` with uppercase digits",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                }
            }
            try sink.emit(.{
                .code = .w0123_non_upper_hex_literal,
                .severity = .warning,
                .primary_span = cand_span,
                .message = "hexadecimal literal uses uppercase `0X` or lowercase `a`–`f` digits (`non-upper-hex-literal`)",
                .labels = labels,
                .suggestions = fixes,
            });
        },
        .non_idiomatic_syntax => {
            if (cand.fix_kind == 10) {
                const labels = try arena_alloc.alloc(LabeledSpan, 1);
                labels[0] = .{
                    .span = cand_span,
                    .label = "`unit` is the default return type; omit `-> unit`",
                    .style = .primary,
                };
                var fixes: []const SuggestedFix = &.{};
                if (cand.aux_payload != std.math.maxInt(u64)) {
                    if (interner) |str_interner| {
                        const del_start: u32 = @intCast(cand.aux_payload);
                        if (del_start <= cand.end_byte) {
                            const edits = try arena_alloc.alloc(TextEdit, 1);
                            edits[0] = .{
                                .file_id = file_id,
                                .start_byte = del_start,
                                .end_byte = cand.end_byte,
                                .replacement_id = try str_interner.intern(""),
                            };
                            const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                            fix_arr[0] = .{
                                .message = "remove redundant `-> unit` return annotation",
                                .applicability = .machine_applicable,
                                .priority = .syntax_canonicalization,
                                .edits = edits,
                            };
                            fixes = fix_arr;
                        }
                    }
                }
                try sink.emit(.{
                    .code = .w0202_non_idiomatic_construct,
                    .severity = .warning,
                    .primary_span = cand_span,
                    .message = "redundant explicit `-> unit` return type annotation (`non-idiomatic-syntax`)",
                    .labels = labels,
                    .suggestions = fixes,
                });
            } else if (cand.fix_kind == 11) {
                const labels = try arena_alloc.alloc(LabeledSpan, 1);
                labels[0] = .{
                    .span = cand_span,
                    .label = "redundant empty `;` statement",
                    .style = .primary,
                };
                var fixes: []const SuggestedFix = &.{};
                if (interner) |str_interner| {
                    var del_start = start_idx;
                    var del_end = end_idx;
                    var ws_left = start_idx;
                    while (ws_left > 0 and (source[ws_left - 1] == ' ' or source[ws_left - 1] == '\t')) : (ws_left -= 1) {}
                    var ws_right = end_idx;
                    while (ws_right < source.len and (source[ws_right] == ' ' or source[ws_right] == '\t')) : (ws_right += 1) {}
                    const is_line_start = (ws_left == 0 or source[ws_left - 1] == '\n');
                    if (is_line_start and ws_right < source.len) {
                        if (source[ws_right] == '\n') {
                            del_start = ws_left;
                            del_end = ws_right + 1;
                        } else if (source[ws_right] == '\r' and ws_right + 1 < source.len and source[ws_right + 1] == '\n') {
                            del_start = ws_left;
                            del_end = ws_right + 2;
                        }
                    }
                    const edits = try arena_alloc.alloc(TextEdit, 1);
                    edits[0] = .{
                        .file_id = file_id,
                        .start_byte = @intCast(del_start),
                        .end_byte = @intCast(del_end),
                        .replacement_id = try str_interner.intern(""),
                    };
                    const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                    fix_arr[0] = .{
                        .message = "remove unnecessary `;` statement",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = edits,
                    };
                    fixes = fix_arr;
                }
                try sink.emit(.{
                    .code = .w0202_non_idiomatic_construct,
                    .severity = .warning,
                    .primary_span = cand_span,
                    .message = "unnecessary empty `;` statement in block (`non-idiomatic-syntax`)",
                    .labels = labels,
                    .suggestions = fixes,
                });
            } else if (cand.fix_kind == 12) {
                const labels = try arena_alloc.alloc(LabeledSpan, 1);
                labels[0] = .{
                    .span = cand_span,
                    .label = "use field shorthand `{ field }` instead of `{ field: field }`",
                    .style = .primary,
                };
                var fixes: []const SuggestedFix = &.{};
                if (cand.aux_payload != std.math.maxInt(u64)) {
                    if (interner) |str_interner| {
                        const field_end: u32 = @intCast(cand.aux_payload);
                        if (field_end <= cand.end_byte) {
                            const edits = try arena_alloc.alloc(TextEdit, 1);
                            edits[0] = .{
                                .file_id = file_id,
                                .start_byte = field_end,
                                .end_byte = cand.end_byte,
                                .replacement_id = try str_interner.intern(""),
                            };
                            const fix_arr = try arena_alloc.alloc(SuggestedFix, 1);
                            fix_arr[0] = .{
                                .message = "collapse redundant `field: field` to shorthand `field`",
                                .applicability = .machine_applicable,
                                .priority = .syntax_canonicalization,
                                .edits = edits,
                            };
                            fixes = fix_arr;
                        }
                    }
                }
                try sink.emit(.{
                    .code = .w0202_non_idiomatic_construct,
                    .severity = .warning,
                    .primary_span = cand_span,
                    .message = "redundant `field: field` syntax where shorthand is available (`non-idiomatic-syntax`)",
                    .labels = labels,
                    .suggestions = fixes,
                });
            }
        },
        .single_char_ident => {
            const ident_slice = source[start_idx..end_idx];
            const msg = try std.fmt.allocPrint(
                arena_alloc,
                "single-character identifier `{s}` obscures intent (`single-char-ident`)",
                .{ident_slice},
            );
            const labels = try arena_alloc.alloc(LabeledSpan, 1);
            labels[0] = .{
                .span = cand_span,
                .label = "use a descriptive multi-letter identifier (`i`, `j`, `k`, `n`, `x`, `y`, `z`, `w` allowed)",
                .style = .primary,
            };
            const help_note: []const u8 = if (ident_slice.len == 1) switch (ident_slice[0]) {
                'e' => "help: rename `e` to `err`, `elem`, or `event`",
                'c' => "help: rename `c` to `cursor`, `ch`, `byte`, or `client`",
                'r' => "help: rename `r` to `reader`, `result`, or `row`",
                'f' => "help: rename `f` to `file`, `func`, or `field`",
                's' => "help: rename `s` to `text`, `slice`, or `state`",
                'p' => "help: rename `p` to `path`, `ptr`, or `point`",
                'v' => "help: rename `v` to `value`, `val`, or `vec`",
                else => "help: choose a descriptive domain name or prefix unused bindings with `_`",
            } else "help: choose a descriptive multi-letter name";
            const notes = try arena_alloc.alloc([]const u8, 1);
            notes[0] = help_note;
            try sink.emit(.{
                .code = .w0203_single_char_ident,
                .severity = .warning,
                .primary_span = cand_span,
                .message = msg,
                .labels = labels,
                .notes = notes,
            });
        },
        else => {},
    }
}

// ---------------------------------------- TESTS ----------------------------------------

test "test_lint_filter_100k_randomized_laminar_interval_containment_parity" {
    const allocator = std.testing.allocator;
    var prng = std.Random.DefaultPrng.init(0xC0DEC0DE_20261124);
    const rng = prng.random();

    // Run 50 random laminar trees × 2,000 random queries = 100,000 verified containment queries!
    var tree_iter: usize = 0;
    while (tree_iter < 50) : (tree_iter += 1) {
        var raw_spans: [32]RawAstSuppression = undefined;
        var span_count: usize = 0;

        // Generate strictly laminar intervals recursively via sub-range partitioning:
        const Frame = struct { lo: u32, hi: u32, depth: u8 };
        var work: [32]Frame = undefined;
        var work_len: usize = 1;
        work[0] = .{ .lo = 0, .hi = 4096, .depth = 0 };

        while (work_len > 0 and span_count < raw_spans.len) {
            work_len -= 1;
            const frame = work[work_len];
            if (frame.hi - frame.lo < 16) continue;

            const pad_l = rng.uintLessThan(u32, 6);
            const pad_r = rng.uintLessThan(u32, 6);
            const start_b = frame.lo + pad_l;
            const end_b = frame.hi - pad_r;
            if (start_b + 4 >= end_b) continue;

            const rule_a: RuleId = @fromBackingInt(@intCast(rng.uintLessThan(u8, 44)));
            const rule_b: RuleId = @fromBackingInt(@intCast(rng.uintLessThan(u8, 44)));
            raw_spans[span_count] = .{
                .target_start_byte = start_b,
                .target_end_byte = end_b,
                .directive_remove_start = start_b,
                .directive_remove_end = start_b + 1,
                .own_mask = rule_a.bit() | rule_b.bit(),
                .selector_slice_start = 0,
                .selector_count = 0,
                .mode = .expect,
                .decl_order = @intCast(span_count),
            };
            span_count += 1;

            if (frame.depth < 5 and end_b - start_b >= 32 and work_len + 2 <= work.len) {
                const mid = start_b + (end_b - start_b) / 2;
                work[work_len] = .{ .lo = start_b + 1, .hi = mid, .depth = frame.depth + 1 };
                work_len += 1;
                work[work_len] = .{ .lo = mid, .hi = end_b - 1, .depth = frame.depth + 1 };
                work_len += 1;
            }
        }

        // Preserve an unsorted copy as the brute-force reference oracle:
        var oracle_copy: [32]RawAstSuppression = undefined;
        @memcpy(oracle_copy[0..span_count], raw_spans[0..span_count]);

        var table = try buildSuppressionTable(allocator, 0, 0, &.{}, raw_spans[0..span_count], &.{}, &.{});
        defer table.deinit(allocator);
        var tracker = try FulfillmentTracker.init(allocator, &table);
        defer tracker.deinit(allocator);

        var query_i: usize = 0;
        while (query_i < 2_000) : (query_i += 1) {
            const pos = rng.uintLessThan(u32, 4120);
            const rule: RuleId = @fromBackingInt(@intCast(rng.uintLessThan(u8, 44)));
            const actual = isCandidateSuppressed(&table, &tracker, .{
                .rule_id = rule,
                .start_byte = pos,
                .end_byte = pos + 1,
            });

            var expected = false;
            for (oracle_copy[0..span_count]) |ref_item| {
                if (ref_item.target_start_byte <= pos and pos < ref_item.target_end_byte and
                    (ref_item.own_mask & rule.bit()) != 0)
                {
                    expected = true;
                    break;
                }
            }
            try std.testing.expectEqual(expected, actual);
        }
    }
}

test "test_lint_filter_surgical_multi_selector_w0002_w0003_w0004_and_w0202_hoist" {
    const parser_mod = @import("parser.zig");
    const allocator = std.testing.allocator;

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    const src =
        "// corex check: file-expect(unused-import, non-upper-hex-literal) -- module migration\n\n" ++
        "// corex check: expect(single-char-ident) -- math kernel\n" ++
        "/| Computes step value.\n" ++
        "@allow(unused-binding)\n" ++
        "pub fn step(c: i32) -> i32 {\n" ++
        "    let val = c + 1; // corex check: expect(redundant-literal-type, clone-on-copy) -- test\n" ++
        "    return val;\n" ++
        "}\n";

    const file_id = FileId.fromInt(7);
    var line_index = try LineIndex.build(allocator, src);
    defer line_index.deinit(allocator);
    var token_buffer = TokenBuffer.init(allocator);
    defer token_buffer.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = syn.AstArena.init(allocator);
    defer ast_arena.deinit();

    _ = try parser_mod.parseSource(src, file_id, &token_buffer, &cst_arena, &ast_arena, null, &interner);

    var table = try extractFileSuppressionTable(allocator, file_id, src, &token_buffer, &cst_arena, &line_index);
    defer table.deinit(allocator);
    var tracker = try FulfillmentTracker.init(allocator, &table);
    defer tracker.deinit(allocator);

    // [1] O(1) fast path returns `false` on unsuppressed rules:
    try std.testing.expect(!isCandidateSuppressed(&table, &tracker, .{
        .rule_id = .collapsible_if,
        .start_byte = 180,
        .end_byte = 185,
    }));

    // [2] Above-line `// corex check: expect(single-char-ident)` registers as active Scope-3 `allow` during Pass 1:
    const c_param_off: u32 = @intCast(std.mem.indexOf(u8, src, "c: i32").?);
    try std.testing.expect(isCandidateSuppressed(&table, &tracker, .{
        .rule_id = .single_char_ident,
        .start_byte = c_param_off,
        .end_byte = c_param_off + 1,
    }));

    // [3] Fulfill `unused-import` at Scope 2 and `redundant-literal-type` at Scope 4 (leaving `non-upper-hex-literal` and `clone-on-copy` stale!):
    try std.testing.expect(isCandidateSuppressed(&table, &tracker, .{
        .rule_id = .unused_import,
        .start_byte = 0,
        .end_byte = 4,
    }));
    const let_val_off: u32 = @intCast(std.mem.indexOf(u8, src, "let val").?);
    try std.testing.expect(isCandidateSuppressed(&table, &tracker, .{
        .rule_id = .redundant_literal_type,
        .start_byte = let_val_off,
        .end_byte = let_val_off + 7,
    }));

    // [4] Collect post-pass diagnostics (`W0202` hoist, `W0003` missing reason on `@allow`, `W0004` prefer `@expect`, `W0002` partial prunes):
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    try collectStaleExpectDiagnosticsAndEdits(
        allocator,
        src,
        file_id,
        &interner,
        &table,
        &tracker,
        .{ .disabled_mask = 0 },
        ALL_RULES_MASK,
        true,
        &sink,
    );

    var saw_w0202_hoist = false;
    var saw_w0003_reason = false;
    var saw_w0004_prefer_expect = false;
    var w0002_count: usize = 0;
    var fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
    defer fixes.deinit(allocator);

    for (sink.asSlice()) |item| {
        if (item.code == .w0202_non_idiomatic_construct) saw_w0202_hoist = true;
        if (item.code == .w0003_missing_suppression_reason) saw_w0003_reason = true;
        if (item.code == .w0004_prefer_expect_over_allow) saw_w0004_prefer_expect = true;
        if (item.code == .w0002_unused_suppression) w0002_count += 1;
        for (item.suggestions) |sug| try fixes.append(allocator, sug);
    }

    try std.testing.expect(saw_w0202_hoist);
    try std.testing.expect(saw_w0003_reason);
    try std.testing.expect(saw_w0004_prefer_expect);
    try std.testing.expectEqual(@as(usize, 2), w0002_count);

    // [5] Apply all `SuggestedFix` bundles via `TransactionalPatcher` and verify exact surgical output:
    const patched = try diag.TransactionalPatcher.apply(allocator, src, file_id, fixes.items, &interner);
    defer allocator.free(patched.patched_source);

    const expected_patched =
        "// corex check: file-expect(unused-import) -- module migration\n\n" ++
        "/| Computes step value.\n" ++
        "@expect(single-char-ident, reason: \"math kernel\")\n" ++
        "@expect(unused-binding)\n" ++
        "pub fn step(c: i32) -> i32 {\n" ++
        "    let val = c + 1; // corex check: expect(redundant-literal-type) -- test\n" ++
        "    return val;\n" ++
        "}\n";
    try std.testing.expectEqualStrings(expected_patched, patched.patched_source);

    // [6] Reason validation (`Ruling 3.2`):
    try std.testing.expect(!isValidSuppressionReason(""));
    try std.testing.expect(!isValidSuppressionReason("   "));
    try std.testing.expect(!isValidSuppressionReason("abc"));
    try std.testing.expect(!isValidSuppressionReason("TODO"));
    try std.testing.expect(!isValidSuppressionReason("fixme"));
    try std.testing.expect(!isValidSuppressionReason("hack"));
    try std.testing.expect(!isValidSuppressionReason("none"));
    try std.testing.expect(!isValidSuppressionReason("lint"));
    try std.testing.expect(isValidSuppressionReason("C FFI binding"));
}

test "test_lint_filter_settings_defaults_fingerprint_and_cli_filter" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    const dx_id = try interner.intern("dx");
    const ids = [_]StringId{dx_id};
    const confusables = [_]u21{0x03B1};
    const settings_a: LintSettings = .{
        .allowed_ident_names = &ids,
        .allowed_confusables = &confusables,
    };
    const settings_default: LintSettings = .{};

    try std.testing.expectEqual(@as(u8, 8), settings_default.effectiveTrivialCopyMaxBytes(8));
    try std.testing.expectEqual(@as(u8, 4), settings_default.effectiveTrivialCopyMaxBytes(4));
    try std.testing.expect(settings_a.isAllowedIdentName(&interner, "i"));
    try std.testing.expect(settings_a.isAllowedIdentName(&interner, "dx"));
    try std.testing.expect(!settings_a.isAllowedIdentName(&interner, "c"));
    try std.testing.expect(settings_a.isAllowedConfusable(0x03B1));
    try std.testing.expect(!settings_a.isAllowedConfusable(0x03B2));
    try std.testing.expect(!settings_a.computeSemanticFingerprint(&interner).eql(
        settings_default.computeSemanticFingerprint(&interner),
    ));

    const cli_filter: CliLintFilter = .{
        .has_only = true,
        .only_mask = RuleId.unused_binding.bit() | RuleId.single_char_ident.bit(),
        .disable_mask = RuleId.single_char_ident.bit(),
    };
    const eff_disabled = cli_filter.applyToDisabledMask(0);
    try std.testing.expect((eff_disabled & RuleId.unused_binding.bit()) == 0);
    try std.testing.expect((eff_disabled & RuleId.single_char_ident.bit()) != 0);
    try std.testing.expect((eff_disabled & RuleId.deprecated_use.bit()) != 0);
    try std.testing.expectEqual(RuleId.unused_binding.bit(), cli_filter.activeAuditMask());
}

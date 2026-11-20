//! Zero-Legacy Automated Source & Manifest Upgrade Engine (`DR-14`, `DR-17`, `DR-21`, & `DR-22`)
//!
//! Implements the bounded 4-pass multi-stage rewrite pipeline (`corex upgrade` / `corex fix`) covering
//! Tier 1 pre-CST lexical shims (`UR-21-00`, `UR-22-00`), Tier 2 lossless CST/AST structural rewrites
//! (`UR-21-01`–`UR-21-03`, `UR-22-01`–`UR-22-05`), Tier 3 `CompilerDb` `TypeId`-aware semantic modernizers
//! (`UR-21-04`–`UR-21-07`, `UR-22-06`, `@deprecated` `W0403`), `corex.toml` canonicalization, and `--accept-caps`.
//!
//! Every candidate byte edit is scheduled through `TransactionalPatcher` (`16B` `TextEdit` records),
//! formatted via `fmt_engine` on completion, and protected by an atomic syntax-error-count rollback guard.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const mir_sast = @import("mir_sast.zig");
const query_db = @import("query_db.zig");
const check_audit = @import("check_audit.zig");
const fmt_engine = @import("fmt_engine.zig");
const pkg_manifest = @import("pkg_manifest.zig");
const pkg_resolver = @import("pkg_resolver.zig");
const pkg_cache = @import("pkg_cache.zig");
const codegen_abi = @import("codegen_abi.zig");
const upgrade_rules = @import("upgrade_rules.zig");
const diagnostic = @import("diag/diagnostic.zig");
const style = @import("cli/style.zig");
const box_draw = @import("cli/box_draw.zig");

const BumpArena = mem_foundation.BumpArena;
const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const StringId = mem_foundation.StringId;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
const TokenKind = syntax_arenas.TokenKind;
const CstNodeKind = syntax_arenas.CstNodeKind;
const AstTag = syntax_arenas.AstTag;
const TokenBuffer = syntax_arenas.TokenBuffer;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstArena = syntax_arenas.AstArena;
const SymbolIndex = symbol_resolver.SymbolIndex;
const TypeId = mem_foundation.TypeId;
const InternPool = type_system.InternPool;
const EffectCapabilityMask = mir_sast.EffectCapabilityMask;
const CompilerDb = query_db.CompilerDb;
const DefId = query_db.DefId;
const ItemTree = query_db.ItemTree;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const EditPriority = diagnostic.EditPriority;
const SuggestedFix = diagnostic.SuggestedFix;
const TextEdit = diagnostic.TextEdit;
const TransactionalPatcher = diagnostic.TransactionalPatcher;
const StyleConfig = style.StyleConfig;
const Glyphs = style.Glyphs;
const CardRenderer = box_draw.CardRenderer;
const TableRenderer = box_draw.TableRenderer;
const TableColumn = box_draw.TableColumn;

pub const UpgradeRuleId = upgrade_rules.UpgradeRuleId;
pub const UpgradeRuleDescriptor = upgrade_rules.UpgradeRuleDescriptor;
pub const UpgradeEngineTier = upgrade_rules.UpgradeEngineTier;
pub const UpgradeWave = upgrade_rules.UpgradeWave;

// ---------------------------------------- TYPES ----------------------------------------

// ------------------ Rule Metadata & Options -------------------

/// Canonical explanation prose and before/after `.cx` showcase paired 1-to-1 with `UpgradeRuleId`.
pub const UpgradeRuleExample = struct {
    /// Strongly typed `UpgradeRuleId` verified at compile time against `UPGRADE_RULE_CATALOG`.
    id: UpgradeRuleId,
    /// Concise architectural rationale rendered inside `corex upgrade --explain=<rule>`.
    explanation: []const u8,
    /// Legacy `.cx` snippet before applying `id`.
    before_cx: []const u8,
    /// Canonical CoreX 2026 `.cx` snippet after applying `id`.
    after_cx: []const u8,
};

/// Configuration flags governing single-file, workspace, manifest, and `--accept-caps` upgrades.
pub const UpgradeOptions = struct {
    /// Bitmask of enabled `UpgradeRuleId` variants (`bit i == 1` for `@intFromEnum(rule_id) == i`).
    rule_mask: u16 = ALL_UPGRADE_RULES_MASK,
    /// `true` when `--rule=<UR-XX-YY>` was explicitly requested (runs ONLY selected rule(s) surgically).
    has_explicit_rule_filter: bool = false,
    /// `true` when `--check` is active (verifies conformance without writing files to disk).
    is_check_only: bool = false,
    /// `true` when `--internal-core` is active (leaves `core.*` kernel paths untouched).
    is_internal_core: bool = false,
    /// `true` when `--accept-caps` or `--accept-caps=<cap,…>` was supplied on the command line.
    has_accept_caps: bool = false,
    /// Allowed `EffectCapabilityMask` bits authorized for lockfile/manifest escalation (`0x033F` for bare `--accept-caps`).
    accept_caps_filter_bits: u16 = 0,
    /// Optional explicit cross-compilation `TargetSpec` (`null` uses host target).
    target_spec: ?codegen_abi.TargetSpec = null,
    /// Maximum `MirVm` compile-time step budget during Tier 3 semantic analysis.
    comptime_step_limit: u64 = 10_000_000,
    /// Optional `std.Io` handle enabling on-demand `core` stdlib and sibling `mod` file loading.
    io: ?std.Io = null,
    /// Optional mutable `VfsSourceMap` used when binding newly discovered `mod` files on disk.
    vfs: ?*vfs_sourcemap.VfsSourceMap = null,
    /// Optional `COREX_HOME` directory path for offline cached dependency mounting.
    corex_home_dir: ?[]const u8 = null,
    /// Optional process environment map for local registry / hermetic resolution.
    environ_map: ?*const std.process.Environ.Map = null,
    /// Additional pending migration items (e.g., `--accept-caps` drift) merged during `--check`.
    extra_pending_items: []const PendingUpgradeItem = &.{},
};

// ----------------- Upgrade Outcomes & Reports -----------------

/// Result of running the Zero-Legacy upgrade pipeline on a single `.cx` source buffer.
pub const FileUpgradeResult = struct {
    /// Newly allocated UTF-8 buffer containing the upgraded (or original) `.cx` source text.
    upgraded_source: []u8,
    /// `true` when `upgraded_source` differs byte-for-byte from the input buffer.
    is_changed: bool = false,
    /// `true` when skipped due to a leading `@generated` or `DO NOT EDIT` header comment.
    is_skipped_generated: bool = false,
    /// Number of multi-pass synergy iterations executed (`0..MAX_SYNERGY_PASSES`).
    passes_executed: u8 = 0,
    /// Total number of `SuggestedFix` bundles transactionally applied across all passes.
    applied_edit_count: u32 = 0,
    /// `true` if the post-upgrade syntax-error-count soundness guard rolled back to baseline.
    is_rolled_back: bool = false,

    /// Releases `upgraded_source` using `allocator`.
    pub fn deinit(self: *FileUpgradeResult, allocator: std.mem.Allocator) void {
        allocator.free(self.upgraded_source);
        self.* = undefined;
    }
};

/// Result of canonicalizing a `corex.toml` manifest buffer (`kebab-case`, `"unsafe_op"`, `@cfg`, `edition = "2026"`).
pub const ManifestUpgradeResult = struct {
    /// Newly allocated UTF-8 buffer containing the canonicalized `corex.toml` text.
    upgraded_toml: []u8,
    /// `true` when `upgraded_toml` differs byte-for-byte from the input manifest.
    is_changed: bool = false,
    /// Total number of `SuggestedFix` bundles transactionally applied across manifest passes.
    applied_edit_count: u32 = 0,
    /// Updated normalized `BLAKE3` manifest digest (`32` bytes) for `corex.lock` synchronization.
    root_manifest_blake3: [32]u8 = @splat(0),

    /// Releases `upgraded_toml` using `allocator`.
    pub fn deinit(self: *ManifestUpgradeResult, allocator: std.mem.Allocator) void {
        allocator.free(self.upgraded_toml);
        self.* = undefined;
    }
};

/// Single package capability observation passed to `--accept-caps` policy verification and update.
pub const PackageObservedCaps = struct {
    /// Canonical `kebab-case` package name matching `LockPackage.name` and `[dependencies]` keys.
    package_kebab: []const u8,
    /// Actual surface or reachable `LOCKFILE_CAP_BITS` inferred by `MIR` SAST for this package.
    actual_surface_caps: EffectCapabilityMask,
};

/// Outcome of evaluating `--accept-caps[=<cap,…>]` across `corex.toml` and `corex.lock`.
pub const AcceptCapsOutcome = struct {
    /// Updated `corex.toml` text (owned by caller allocator).
    updated_toml: []u8,
    /// Optional updated `corex.lock` text when a lockfile was provided (owned by caller allocator).
    updated_lock: ?[]u8 = null,
    /// `true` when `updated_toml` differs from input `toml_bytes`.
    is_toml_changed: bool = false,
    /// `true` when `updated_lock` differs from input `lock_bytes`.
    is_lock_changed: bool = false,
    /// `true` when an explicit `deny_caps` ban was violated (`E0324` is never overridden by `--accept-caps`).
    has_denied_cap_violation: bool = false,
    /// Bitmask of escalated capabilities that were NOT covered by `accept_caps_filter_bits` (`0` when all accepted).
    unaccepted_escalation_bits: u16 = 0,
    /// Package name associated with the first denied or unaccepted capability escalation (`""` when none).
    offending_package: []u8 = &.{},

    /// Releases all owned buffers inside `self`.
    pub fn deinit(self: *AcceptCapsOutcome, allocator: std.mem.Allocator) void {
        allocator.free(self.updated_toml);
        if (self.updated_lock) |lock_buf| allocator.free(lock_buf);
        if (self.offending_package.len > 0) allocator.free(self.offending_package);
        self.* = undefined;
    }
};

/// Artifact category for a pending migration entry reported by `corex upgrade --check`.
pub const CheckTargetKind = enum(u8) {
    /// `.cx` source or script file requiring Zero-Legacy source upgrades.
    cx_source = 0,
    /// `corex.toml` manifest requiring schema, `edition = "2026"`, or `allow_caps` canonicalization.
    manifest_toml = 1,
    /// `corex.lock` lockfile requiring `root_manifest_blake3` or `max_caps` synchronization.
    lockfile = 2,

    /// Returns the short monochrome label rendered in `--check` status lines.
    pub inline fn asLabel(self: CheckTargetKind) []const u8 {
        return switch (self) {
            .cx_source => "source",
            .manifest_toml => "manifest",
            .lockfile => "lockfile",
        };
    }
};

/// Pending migration item reported during `corex upgrade --check` dry-run verification.
pub const PendingUpgradeItem = struct {
    /// Kind of file requiring migration.
    kind: CheckTargetKind,
    /// Display path of the file requiring migration.
    path: []const u8,
};

// ----------------- Internal Patch & CST Types -----------------

/// Precedence tiers of CoreX's 4-tier `Type` grammar (`DR-22` §3.3) for parenthesization in `UR-22-03`.
const TypeRewritePrec = enum(u8) {
    /// Open unparenthesized type slot (`|`, `+`, `is`, `fn(…) -> Type`).
    tier0_open = 0,
    /// Non-associative infix result type `Ok!Err` (`Tier 1`).
    tier1_result = 1,
    /// Prefix reference or ownership mode `&T`, `&mut T`, `&out T`, `own T`, `~T` (`Tier 2`).
    tier2_prefix = 2,
    /// Postfix optional type `T?` (`Tier 3`).
    tier3_postfix = 3,
    /// Primary atomic type (`T`, `&[T]`, `*T`, `*mut T`, `[T; N]`, `(T, U)`) (`Tier 4`).
    tier4_primary = 4,
};

/// Contiguous non-synthesized token range and byte span extracted from a `LosslessCstArena` subtree.
const CstTokenSpan = struct {
    /// First non-synthesized token index inside the CST subtree.
    first_tok: TokenIndex,
    /// Last non-synthesized token index inside the CST subtree.
    last_tok: TokenIndex,
    /// Inclusive starting byte offset of `first_tok` in source.
    start_byte: u32,
    /// Exclusive ending byte offset of `last_tok` in source.
    end_byte: u32,
};

/// Canonical capability name and single-bit mask entry for `corex.lock` / `allow_caps` formatting.
const CanonicalCapEntry = struct {
    /// Canonical capability name string (`"clock"` .. `"unsafe_op"`).
    name: []const u8,
    /// Single-bit mask in `EffectCapabilityMask` (`LOCKFILE_CAP_BITS`).
    bit: u16,
};

/// Retired bare property kind on slices, arrays, and `str` migrated by `UR-22-06`.
const RetiredSlicePropKind = enum(u8) {
    /// Retired `.is_empty` property -> `.is_empty()`.
    is_empty = 0,
    /// Retired `.len` property -> `.len()`.
    len = 1,
    /// Retired `.ptr` property -> `.as_mut_ptr()` or `.as_ptr()`.
    ptr = 2,
};

/// Arena-backed accumulator building `SuggestedFix` bundles for `TransactionalPatcher.apply`.
const FixCollector = struct {
    /// Backing general allocator for growable `fixes` list.
    allocator: std.mem.Allocator,
    /// Bump arena owning `TextEdit` slices for the current sub-stage.
    arena: BumpArena,
    /// String interner storing replacement text payloads referenced by `TextEdit.replacement_id`.
    interner: *StringInterner,
    /// Target `FileId` stamped onto emitted `TextEdit` records.
    file_id: FileId,
    /// Accumulated candidate `SuggestedFix` bundles.
    fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty,

    /// Initializes an empty `FixCollector` bound to `allocator`, `interner`, and `file_id`.
    fn init(allocator: std.mem.Allocator, interner: *StringInterner, file_id: FileId) FixCollector {
        return .{
            .allocator = allocator,
            .arena = BumpArena.init(allocator),
            .interner = interner,
            .file_id = file_id,
        };
    }

    /// Releases all `SuggestedFix` storage and the internal `BumpArena`.
    fn deinit(self: *FixCollector) void {
        self.fixes.deinit(self.allocator);
        self.arena.deinit();
        self.* = undefined;
    }

    /// Clears accumulated fixes while retaining capacity across sub-stages.
    fn resetRetainingCapacity(self: *FixCollector) void {
        self.fixes.clearRetainingCapacity();
        self.arena.resetRetainingCapacity();
    }

    /// Appends a single-edit `.machine_applicable` `SuggestedFix` replacing `[start_byte .. end_byte)`.
    fn appendSingleEdit(
        self: *FixCollector,
        priority: EditPriority,
        start_byte: u32,
        end_byte: u32,
        replacement: []const u8,
        message: []const u8,
    ) !void {
        if (start_byte > end_byte) return;
        const repl_id = try self.interner.intern(replacement);
        const edits = try self.arena.asAllocator().alloc(TextEdit, 1);
        edits[0] = .{
            .file_id = self.file_id,
            .start_byte = start_byte,
            .end_byte = end_byte,
            .replacement_id = repl_id,
        };
        try self.fixes.append(self.allocator, .{
            .message = message,
            .applicability = .machine_applicable,
            .priority = priority,
            .edits = edits,
        });
    }

    /// Appends a two-edit atomic `.machine_applicable` `SuggestedFix` bundle.
    fn appendDualEdits(
        self: *FixCollector,
        priority: EditPriority,
        first_start: u32,
        first_end: u32,
        first_repl: []const u8,
        second_start: u32,
        second_end: u32,
        second_repl: []const u8,
        message: []const u8,
    ) !void {
        const first_id = try self.interner.intern(first_repl);
        const second_id = try self.interner.intern(second_repl);
        const edits = try self.arena.asAllocator().alloc(TextEdit, 2);
        edits[0] = .{
            .file_id = self.file_id,
            .start_byte = first_start,
            .end_byte = first_end,
            .replacement_id = first_id,
        };
        edits[1] = .{
            .file_id = self.file_id,
            .start_byte = second_start,
            .end_byte = second_end,
            .replacement_id = second_id,
        };
        try self.fixes.append(self.allocator, .{
            .message = message,
            .applicability = .machine_applicable,
            .priority = priority,
            .edits = edits,
        });
    }

    /// Clones an external `.machine_applicable` `SuggestedFix` (re-interning replacements into `self.interner`).
    fn appendClonedFix(
        self: *FixCollector,
        source_interner: *const StringInterner,
        fix: SuggestedFix,
    ) !void {
        if (fix.applicability != .machine_applicable or fix.edits.len == 0) return;
        const cloned_edits = try self.arena.asAllocator().alloc(TextEdit, fix.edits.len);
        for (fix.edits, 0..) |orig_edit, i| {
            if (orig_edit.file_id != self.file_id) return;
            const text = source_interner.get(orig_edit.replacement_id);
            cloned_edits[i] = .{
                .file_id = self.file_id,
                .start_byte = orig_edit.start_byte,
                .end_byte = orig_edit.end_byte,
                .replacement_id = try self.interner.intern(text),
            };
        }
        try self.fixes.append(self.allocator, .{
            .message = try self.arena.dupe(u8, fix.message),
            .applicability = .machine_applicable,
            .priority = fix.priority,
            .edits = cloned_edits,
        });
    }
};

/// Per-file baseline, frontmatter mask, and multi-pass rewrite state inside `upgradeWorkspaceFilesInDb`.
const PerFileState = struct {
    /// Immutable baseline UTF-8 buffer for atomic soundness rollback.
    original_full: []u8,
    /// Optional canonicalized `---` script TOML frontmatter prefix.
    canonical_fm_prefix: ?[]u8 = null,
    /// Byte length of the leading `---` script frontmatter prefix (`0` for standard `.cx` files).
    fm_prefix_len: usize = 0,
    /// Working `.cx` buffer with any leading frontmatter bytes masked to spaces/newlines.
    working_masked_cx: []u8,
    /// Initial lexer + parser error count on `working_masked_cx` before any pass executes.
    baseline_syntax_errors: u32 = 0,
    /// `true` when skipped due to a leading `@generated` or `DO NOT EDIT` header comment.
    is_generated: bool = false,
    /// Number of multi-pass synergy iterations executed on this file.
    passes_run: u8 = 0,
    /// Total `SuggestedFix` bundles transactionally applied to this file.
    edits_applied: u32 = 0,
};

// --------------------------------------- CONSTS ----------------------------------------

// ------------------ Canonical Rule Examples -------------------

/// Bitmask enabling all 15 canonical Zero-Legacy upgrade rules (`0x7FFF`).
pub const ALL_UPGRADE_RULES_MASK: u16 = (@as(u16, 1) << @intCast(upgrade_rules.UPGRADE_RULE_COUNT)) - 1;

/// Maximum multi-pass fixed-point synergy iterations per file (`DR-14` §2.3 & `DR-21` §3.3).
pub const MAX_SYNERGY_PASSES: u8 = upgrade_rules.MAX_SYNERGY_PASSES;

/// Maximum leading byte prefix inspected for `@generated` or `DO NOT EDIT` header comments.
pub const GENERATED_HEADER_SCAN_LIMIT: usize = check_audit.GENERATED_HEADER_SCAN_BYTES;

/// Canonical 15-entry explanation and before/after showcase table indexed by `@backingInt(UpgradeRuleId)`.
pub const UPGRADE_RULE_EXAMPLES: [upgrade_rules.UPGRADE_RULE_COUNT]UpgradeRuleExample = .{
    .{
        .id = .ur_21_00_path_coloncolon_and_std_root,
        .explanation = "CoreX unifies module, nominal type, enum variant, and member access under '.' and " ++
            "renames the root standard library namespace from 'std' to 'cx'.",
        .before_cx =
        \\use std::collections::Vec;
        \\fn build() -> Vec[i32] {
        \\    return Vec::new();
        \\}
        ,
        .after_cx =
        \\use cx.collections.Vec;
        \\fn build() -> Vec[i32] {
        \\    return Vec.new();
        \\}
        ,
    },
    .{
        .id = .ur_21_01_if_let_to_is_condition,
        .explanation = "Pattern conditions use infix 'expr is Pattern', enabling natural 'and' chaining " ++
            "and wrapping trailing struct patterns in parentheses before '{'.",
        .before_cx =
        \\if let Some(val) = maybe_num {
        \\    use_num(val);
        \\}
        ,
        .after_cx =
        \\if maybe_num is .Some(val) {
        \\    use_num(val);
        \\}
        ,
    },
    .{
        .id = .ur_21_02_while_let_to_is_condition,
        .explanation = "Loop pattern conditions use 'while expr is Pattern' so scrutinee evaluation precedes " ++
            "the destructuring pattern and chains cleanly with boolean guards.",
        .before_cx =
        \\while let Some(item) = iter.next() {
        \\    consume(item);
        \\}
        ,
        .after_cx =
        \\while iter.next() is .Some(item) {
        \\    consume(item);
        \\}
        ,
    },
    .{
        .id = .ur_21_03_let_some_else_to_orelse,
        .explanation = "Single-binding '.Some(id)' diverging 'let … else' guards condense into concise " ++
            "value-or-diverge 'orelse' expressions while preserving 'let' vs 'var' mutability.",
        .before_cx =
        \\let .Some(mut node) = slot.take() else {
        \\    return fallback;
        \\};
        ,
        .after_cx =
        \\var node = slot.take() orelse return fallback;
        ,
    },
    .{
        .id = .ur_21_04_type_level_generic_args,
        .explanation = "Type-level generic arguments attach directly to the nominal type constructor " ++
            "'Type[Args].assoc_fn(…)' rather than trailing the associated function name.",
        .before_cx =
        \\let buf = PoolAllocator.new[Node[K, V]](cap);
        ,
        .after_cx =
        \\let buf = PoolAllocator[Node[K, V]].new(cap);
        ,
    },
    .{
        .id = .ur_21_05_option_unwrap_to_orelse,
        .explanation = "Optional '.unwrap_or(def)' and '.unwrap()' calls on verified 'T?' receivers modernize " ++
            "to first-class short-circuiting 'orelse' expressions with precedence-safe parentheses.",
        .before_cx =
        \\let port = cfg_port.unwrap_or(8080);
        \\let must = cfg_port.unwrap();
        ,
        .after_cx =
        \\let port = cfg_port orelse 8080;
        \\let must = cfg_port orelse unreachable;
        ,
    },
    .{
        .id = .ur_21_06_with_arena_to_with_context,
        .explanation = "Closure-based 'cx.mem.with_arena(arena, || { … })' statements without inner 'return' " ++
            "jumps upgrade to zero-closure lexical 'with context.allocator = arena { … }' blocks.",
        .before_cx =
        \\cx.mem.with_arena(&mut scratch, || {
        \\    process_batch();
        \\});
        ,
        .after_cx =
        \\with context.allocator = &mut scratch {
        \\    process_batch();
        \\}
        ,
    },
    .{
        .id = .ur_21_07_end_relative_dollar_slices,
        .explanation = "Pure slice tail expressions 's[lo .. s.len() - k]' condense to end-relative '$' " ++
            "bounds 's[lo..$-k]' (and 's[..$-k]' when 'lo' is literal '0').",
        .before_cx =
        \\let payload = frame[0 .. frame.len() - 4];
        ,
        .after_cx =
        \\let payload = frame[..$-4];
        ,
    },
    .{
        .id = .ur_22_00_lexical_token_canonicalization,
        .explanation = "Pre-parse lexical canonicalization replaces '&&' with 'and', '@noalloc' with " ++
            "'@no_alloc', 'Numeric' with 'Number', and string '\\{' / '\\}' escapes with '{{' / '}}'.",
        .before_cx =
        \\@noalloc
        \\fn scale[T: Numeric](val: T, ok: bool) -> str {
        \\    if ok && val > 0 { return "\{ok\}"; }
        \\    return "";
        \\}
        ,
        .after_cx =
        \\@no_alloc
        \\fn scale[T: Number](val: T, ok: bool) -> str {
        \\    if ok and val > 0 { return "{{ok}}"; }
        \\    return "";
        \\}
        ,
    },
    .{
        .id = .ur_22_01_logical_or_and_var_bindings,
        .explanation = "Infix '||' becomes 'or' (preserving zero-parameter '|| body' closures), and " ++
            "'let mut', 'var mut', and pattern 'mut id' bindings unify on 'var'.",
        .before_cx =
        \\let mut total = 0;
        \\if retry || fallback {
        \\    let cb = || total;
        \\}
        ,
        .after_cx =
        \\var total = 0;
        \\if retry or fallback {
        \\    let cb = || total;
        \\}
        ,
    },
    .{
        .id = .ur_22_02_parameter_and_ownership_modes,
        .explanation = "Legacy parameter, receiver, and call-site modes ('ref', 'ref mut', 'inout', 'sink', " ++
            "'set', 'out', 'mut self', 'mut x: T') canonicalize to '&', '&mut', '&out', 'own', and 'var'.",
        .before_cx =
        \\fn push(ref mut self, sink item: Buf, set ok: bool) {
        \\    helper(inout self.inner, out ok);
        \\}
        ,
        .after_cx =
        \\fn push(&mut self, item: own Buf, ok: &out bool) {
        \\    helper(&mut self.inner, &out ok);
        \\}
        ,
    },
    .{
        .id = .ur_22_03_postfix_option_and_infix_result,
        .explanation = "Generic 'Option[T]' and 'Result[Ok, Err]' type constructors rewrite bottom-up to " ++
            "postfix 'T?' and infix 'Ok!Err' with exact 4-tier Type precedence parentheses.",
        .before_cx =
        \\fn fetch( slot: Option[&u8] ) -> Result[Option[u32], IoError];
        ,
        .after_cx =
        \\fn fetch(slot: (&u8)?) -> u32?!IoError;
        ,
    },
    .{
        .id = .ur_22_04_attributes_enums_and_bitfields,
        .explanation = "Attribute arguments use ':', 'bit_field' and integer-backed 'enum' items use " ++
            "': BackingType', nominal members use ',', and 'fn' items omit redundant '-> unit'.",
        .before_cx =
        \\@repr(u8)
        \\enum Mode { Read = 0; Write = 1; }
        \\type Flags = bit_field u8 { ready: bool | 1; };
        \\@align(bytes = 16)
        \\fn reset() -> unit {}
        ,
        .after_cx =
        \\enum Mode: u8 { Read = 0, Write = 1 }
        \\bit_field Flags: u8 { ready: bool | 1 }
        \\@align(bytes: 16)
        \\fn reset() {}
        ,
    },
    .{
        .id = .ur_22_05_ffi_pointers_and_prose_tests,
        .explanation = "FFI declarations canonicalize '*const T' to '*T', 'c_void' to 'opaque', " ++
            "'extern \"c\"' to 'extern \"C\"', and parameterless '@test fn' items to 'test \"…\"' blocks.",
        .before_cx =
        \\use cx.ffi.c_void;
        \\extern "c" fn free(ptr: *const c_void);
        \\@test
        \\fn test_arena_reset() -> unit {}
        ,
        .after_cx =
        \\extern "C" fn free(ptr: *opaque);
        \\test "arena reset" {}
        ,
    },
    .{
        .id = .ur_22_06_semantic_unary_deref_and_slice_methods,
        .explanation = "Type-directed semantic rewrites replace '!b' with 'not b', '!mask' with '~mask', " ++
            "prefix '*ptr' with 'ptr.*', and slice/array/str '.len'/'.ptr' with '.len()'/'.as_ptr()'.",
        .before_cx =
        \\fn inspect(buf: &[u8], ptr: *i32, flag: bool, mask: u32) -> usize {
        \\    if !flag { return ~0 ^ !mask as usize; }
        \\    let v = *ptr;
        \\    return buf.len;
        \\}
        ,
        .after_cx =
        \\fn inspect(buf: &[u8], ptr: *i32, flag: bool, mask: u32) -> usize {
        \\    if not flag { return ~0 ^ ~mask as usize; }
        \\    let v = ptr.*;
        \\    return buf.len();
        \\}
        ,
    },
};

// --------------------- Static Lookup Sets ---------------------

/// $O(1)$ lookup set of integer primitive names valid as `enum Name: <IntPrim>` backing types (`UR-22-04`).
const INT_PRIM_REPR_SET = std.StaticStringMap(void).initComptime(.{
    .{ "i128", {} },
    .{ "i16", {} },
    .{ "i32", {} },
    .{ "i64", {} },
    .{ "i8", {} },
    .{ "isize", {} },
    .{ "u128", {} },
    .{ "u16", {} },
    .{ "u32", {} },
    .{ "u64", {} },
    .{ "u8", {} },
    .{ "usize", {} },
});

/// $O(1)$ map from unqualified legacy `Option`/`Result` pattern heads to contextual `.Variant` syntax (`UR-21-01`/`02`).
const UNQUALIFIED_STD_VARIANT_MAP = std.StaticStringMap([]const u8).initComptime(.{
    .{ "Err", ".Err" },
    .{ "None", ".None" },
    .{ "Ok", ".Ok" },
    .{ "Some", ".Some" },
});

/// $O(1)$ set of standard `Option` path prefix segments accepted by `UR-21-03`.
const OPTION_PREFIX_SEGMENT_SET = std.StaticStringMap(void).initComptime(.{
    .{ "Option", {} },
    .{ "cx", {} },
    .{ "option", {} },
    .{ "std", {} },
});

/// $O(1)$ map from single-token retired `self` receiver modifiers to canonical replacements (`UR-22-02`).
const RETIRED_SELF_MODE_MAP = std.StaticStringMap([]const u8).initComptime(.{
    .{ "inout", "&mut self" },
    .{ "mut", "var self" },
    .{ "ref", "&self" },
    .{ "sink", "own self" },
});

/// $O(1)$ map from retired parameter, type, and call-site mode tokens to canonical prefixes (`UR-22-02`).
const RETIRED_TYPE_MODE_MAP = std.StaticStringMap([]const u8).initComptime(.{
    .{ "inout", "&mut" },
    .{ "out", "&out" },
    .{ "ref", "&" },
    .{ "set", "&out" },
    .{ "sink", "own" },
});

/// $O(1)$ set of mutability introducers (`"mut"`, `"var"`) in parameter headers (`UR-22-02`).
const PARAM_MUT_INTRO_SET = std.StaticStringMap(void).initComptime(.{
    .{ "mut", {} },
    .{ "var", {} },
});

/// $O(1)$ set of ownership mode tokens (`"own"`, `"sink"`) in parameter headers (`UR-22-02`).
const PARAM_OWN_MODE_SET = std.StaticStringMap(void).initComptime(.{
    .{ "own", {} },
    .{ "sink", {} },
});

/// $O(1)$ set of existential/dynamic trait-bound keywords with open callable tails (`UR-22-03`).
const CALLABLE_BOUND_HEAD_SET = std.StaticStringMap(void).initComptime(.{
    .{ "any", {} },
    .{ "dyn", {} },
});

/// $O(1)$ set of unshadowed `Option` type constructor paths rewritten to `T?` (`UR-22-03`).
const CANONICAL_OPTION_HEAD_SET = std.StaticStringMap(void).initComptime(.{
    .{ "Option", {} },
    .{ "cx.option.Option", {} },
    .{ "std.option.Option", {} },
});

/// $O(1)$ set of unshadowed `Result` type constructor paths rewritten to `Ok!Err` (`UR-22-03`).
const CANONICAL_RESULT_HEAD_SET = std.StaticStringMap(void).initComptime(.{
    .{ "Result", {} },
    .{ "cx.result.Result", {} },
    .{ "std.result.Result", {} },
});

/// $O(1)$ map classifying `"never"` (`false`) vs. omissible `"unit"` (`true`) primitive return types (`UR-22-04`/`05`).
const UNIT_OR_NEVER_PRIM_MAP = std.StaticStringMap(bool).initComptime(.{
    .{ "never", false },
    .{ "unit", true },
});

/// $O(1)$ set of C representation argument spellings inside `@repr(C, <IntPrim>)` (`UR-22-04`).
const C_REPR_ARG_SET = std.StaticStringMap(void).initComptime(.{
    .{ "C", {} },
    .{ "c", {} },
});

/// $O(1)$ set of standard library root namespace segments preceding `.ffi.c_void` (`UR-22-05`).
const STDLIB_ROOT_SEG_SET = std.StaticStringMap(void).initComptime(.{
    .{ "core", {} },
    .{ "cx", {} },
    .{ "std", {} },
});

/// $O(1)$ set of qualified `with_arena` callee paths rewritten to `with context.allocator` (`UR-21-06`).
const WITH_ARENA_CALLEE_SET = std.StaticStringMap(void).initComptime(.{
    .{ "core.mem.with_arena", {} },
    .{ "cx.mem.with_arena", {} },
    .{ "mem.with_arena", {} },
});

/// $O(1)$ set of standard `mem` module receiver paths for `.with_arena(…)` calls (`UR-21-06`).
const MEM_MODULE_RECEIVER_SET = std.StaticStringMap(void).initComptime(.{
    .{ "core.mem", {} },
    .{ "cx.mem", {} },
    .{ "mem", {} },
});

/// $O(1)$ map from retired slice/array/`str` property names to `RetiredSlicePropKind` (`UR-22-06`).
const SLICE_PROP_MEMBER_MAP = std.StaticStringMap(RetiredSlicePropKind).initComptime(.{
    .{ "is_empty", .is_empty },
    .{ "len", .len },
    .{ "ptr", .ptr },
});

/// $O(1)$ set of TOML table headers owning `edition = "…"` keys (`corex.toml` canonicalization).
const MANIFEST_EDITION_SECTION_SET = std.StaticStringMap(void).initComptime(.{
    .{ "package", {} },
    .{ "workspace.package", {} },
});

/// $O(1)$ set of TOML dependency table headers scanned for inline `allow_caps` arrays (`--accept-caps`).
const MANIFEST_DEP_SECTION_SET = std.StaticStringMap(void).initComptime(.{
    .{ "build-dependencies", {} },
    .{ "dependencies", {} },
    .{ "dev-dependencies", {} },
    .{ "workspace.dependencies", {} },
});

/// $O(1)$ map from retired capability spellings to canonical `MANIFEST_CAPABILITY_MAP` names (`--accept-caps`).
const RETIRED_CAP_ALIAS_MAP = std.StaticStringMap([]const u8).initComptime(.{
    .{ "unsafe", "unsafe_op" },
});

/// $O(1)$ set of hub module basenames whose child `mod <name>;` files resolve as direct siblings.
const HUB_MODULE_BASENAME_SET = std.StaticStringMap(void).initComptime(.{
    .{ "lib.cx", {} },
    .{ "main.cx", {} },
    .{ "mod.cx", {} },
    .{ "root.cx", {} },
});

/// Maximum directory / `mod` recursion depth when binding workspace module trees in `CompilerDb`.
const MAX_UPGRADE_MOD_DISCOVERY_DEPTH: u32 = 64;

/// $O(1)$ set of retired `corex.toml` `edition` strings migrated to `"2026"` (`pkg_manifest.DEFAULT_COREX_EDITION`).
const RETIRED_EDITION_SET = std.StaticStringMap(void).initComptime(.{
    .{ "2024", {} },
    .{ "2025", {} },
});

/// Canonical ASCII-sorted `LOCKFILE_CAP_BITS` (`0x033F`) table verified at comptime against `MANIFEST_CAPABILITY_MAP`.
const CANONICAL_LOCKFILE_CAP_TABLE = [_]CanonicalCapEntry{
    .{ .name = "clock", .bit = 1 << 8 },
    .{ .name = "entropy", .bit = 1 << 9 },
    .{ .name = "env", .bit = 1 << 2 },
    .{ .name = "ffi", .bit = 1 << 4 },
    .{ .name = "fs", .bit = 1 << 0 },
    .{ .name = "net", .bit = 1 << 1 },
    .{ .name = "process", .bit = 1 << 3 },
    .{ .name = "unsafe_op", .bit = 1 << 5 },
};

// -------------------------------------- INTERNALS --------------------------------------

// --------------- Fix Collector & Token Helpers ----------------

/// Compile-time drift guard verifying 1:1 parity across `UPGRADE_RULE_CATALOG`, `UPGRADE_RULE_EXAMPLES`, and capabilities.
fn verifyUpgradeEngineInvariantsComptime() void {
    std.debug.assert(UPGRADE_RULE_EXAMPLES.len == upgrade_rules.UPGRADE_RULE_CATALOG.len);
    for (upgrade_rules.UPGRADE_RULE_CATALOG, 0..) |cat_entry, i| {
        std.debug.assert(UPGRADE_RULE_EXAMPLES[i].id == cat_entry.id);
        std.debug.assert(UPGRADE_RULE_EXAMPLES[i].explanation.len > 0);
        std.debug.assert(UPGRADE_RULE_EXAMPLES[i].before_cx.len > 0);
        std.debug.assert(UPGRADE_RULE_EXAMPLES[i].after_cx.len > 0);
    }

    var union_bits: u16 = 0;
    for (CANONICAL_LOCKFILE_CAP_TABLE, 0..) |cap_entry, i| {
        if (i > 0) {
            std.debug.assert(std.mem.order(u8, CANONICAL_LOCKFILE_CAP_TABLE[i - 1].name, cap_entry.name) == .lt);
        }
        std.debug.assert(pkg_manifest.MANIFEST_CAPABILITY_MAP.get(cap_entry.name).? == cap_entry.bit);
        union_bits |= cap_entry.bit;
    }
    std.debug.assert(union_bits == EffectCapabilityMask.LOCKFILE_CAP_BITS);
}

comptime {
    verifyUpgradeEngineInvariantsComptime();
}

/// Returns `true` if `ch_byte` is ASCII horizontal or vertical whitespace.
inline fn isAsciiWhitespace(ch_byte: u8) bool {
    return ch_byte == ' ' or ch_byte == '\t' or ch_byte == '\n' or ch_byte == '\r';
}

/// Returns `true` if `ch_byte` can appear inside a CoreX identifier (`[A-Za-z0-9_]`).
inline fn isIdentContinueByte(ch_byte: u8) bool {
    return std.ascii.isAlphanumeric(ch_byte) or ch_byte == '_';
}

/// Shared comment trivia detector (covering both explicit comment kinds and `TRIVIA_FLAG_COALESCED`).
const hasCommentsInByteRange = check_audit.hasCommentsInByteRange;

/// Computes the first and last non-synthesized token and byte bounds inside `cst_idx` (`null` if empty).
fn extractCstTokenSpan(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    cst_idx: CstNodeIndex,
) ?CstTokenSpan {
    if (cst_idx.isNone() or cst_idx.asInt() >= cst_arena.countNodes()) return null;
    const start_node: usize = cst_idx.asInt();
    const root_rec = cst_arena.getNode(cst_idx);
    const end_node: usize = @min(start_node + @max(@as(usize, root_rec.subtree_size), 1), cst_arena.countNodes());
    const tok_count = tok_buf.countTokens();

    var first_tok: TokenIndex = .none;
    var last_tok: TokenIndex = .none;
    var start_byte: u32 = 0;
    var end_byte: u32 = 0;

    var cur_idx = start_node;
    while (cur_idx < end_node) : (cur_idx += 1) {
        const node_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cur_idx)));
        if (node_rec.subtree_size > 1) continue;
        if (node_rec.token.isNone() or node_rec.token.asInt() >= tok_count) continue;
        const tok_rec = tok_buf.getToken(node_rec.token);
        if (tok_rec.flags.is_synthesized or tok_rec.kind == .eof or tok_rec.byte_len == 0) continue;
        if (first_tok.isNone()) {
            first_tok = node_rec.token;
            start_byte = tok_rec.byte_offset;
        }
        last_tok = node_rec.token;
        end_byte = tok_rec.byte_offset +| tok_rec.byte_len;
    }

    if (first_tok.isNone()) return null;
    return .{
        .first_tok = first_tok,
        .last_tok = last_tok,
        .start_byte = start_byte,
        .end_byte = end_byte,
    };
}

/// Computes the source byte span of `ast_node` via its CST origin or fallback token traversal.
fn extractAstByteSpan(
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    ast_node: NodeIndex,
) ?CstTokenSpan {
    if (ast_node.isNone() or ast_node.asInt() >= ast_arena.countNodes()) return null;
    const cst_origin = ast_arena.getCstOrigin(ast_node);
    if (!cst_origin.isNone()) {
        if (extractCstTokenSpan(cst_arena, tok_buf, cst_origin)) |cst_span| {
            return cst_span;
        }
    }
    const node = ast_arena.getNode(ast_node);
    if (node.main_token.isNone() or node.main_token.asInt() >= tok_buf.countTokens()) return null;
    const main_rec = tok_buf.getToken(node.main_token);
    if (main_rec.flags.is_synthesized or main_rec.byte_len == 0) return null;
    return .{
        .first_tok = node.main_token,
        .last_tok = node.main_token,
        .start_byte = main_rec.byte_offset,
        .end_byte = main_rec.byte_offset +| main_rec.byte_len,
    };
}

/// Counts total lexer + parser error diagnostics on a `.cx` source buffer (with script frontmatter masked).
fn countSyntaxErrors(allocator: std.mem.Allocator, file_id: FileId, raw_source: []const u8) !u32 {
    var fm_arena = BumpArena.init(allocator);
    defer fm_arena.deinit();
    const cx_view = if (try pkg_manifest.extractScriptFrontmatter(&fm_arena, file_id, raw_source, null)) |extracted|
        extracted.blanked_cx_source
    else
        raw_source;

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    _ = try parser.parseSource(cx_view, file_id, &tok_buf, &cst_arena, &ast_arena, &sink, null);
    return sink.error_count;
}

/// Masks `[0 .. mask_len)` non-newline bytes of `buffer` to ASCII `' '` (`0x20`) in place.
fn maskFrontmatterBytesInPlace(buffer: []u8, mask_len: usize) void {
    const clamped = @min(mask_len, buffer.len);
    var i: usize = 0;
    while (i < clamped) : (i += 1) {
        if (buffer[i] != '\n' and buffer[i] != '\r') {
            buffer[i] = ' ';
        }
    }
}

/// Applies accumulated fixes in `collector` onto `current_buf` via `TransactionalPatcher`, updating `current_buf`.
fn applyCollectedFixesInMemory(
    allocator: std.mem.Allocator,
    current_buf: *[]u8,
    collector: *FixCollector,
) !u32 {
    if (collector.fixes.items.len == 0) return 0;
    const outcome = try TransactionalPatcher.apply(
        allocator,
        current_buf.*,
        collector.file_id,
        collector.fixes.items,
        collector.interner,
    );
    if (outcome.applied_count == 0 or std.mem.eql(u8, current_buf.*, outcome.patched_source)) {
        allocator.free(outcome.patched_source);
        return 0;
    }
    allocator.free(current_buf.*);
    current_buf.* = outcome.patched_source;
    return outcome.applied_count;
}

// ---------------- Tier 1 Pre-CST Lexeme Shims -----------------

/// Scans `tok_buf` for local/module declarations named `std` so `UR-21-00` never rewrites shadowed `std`.
fn hasLocalStdDeclaration(source: []const u8, tok_buf: *const TokenBuffer) bool {
    const tok_count = tok_buf.countTokens();
    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const tok_idx = TokenIndex.fromInt(@intCast(i));
        const rec = tok_buf.getToken(tok_idx);
        if (rec.kind != .ident or !std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, tok_idx), "std")) continue;
        if (i > 0) {
            const prev_kind = tok_buf.getToken(TokenIndex.fromInt(@intCast(i - 1))).kind;
            switch (prev_kind) {
                .kw_mod, .kw_fn, .kw_let, .kw_var, .kw_const, .kw_as => return true,
                else => {},
            }
        }
    }
    return false;
}

/// Scans `tok_buf` for user declarations or generic type parameters named `Numeric` (`UR-22-00` shadow guard).
fn hasLocalNumericDeclaration(source: []const u8, tok_buf: *const TokenBuffer) bool {
    const tok_count = tok_buf.countTokens();
    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const tok_idx = TokenIndex.fromInt(@intCast(i));
        const rec = tok_buf.getToken(tok_idx);
        if (rec.kind != .type_ident or !std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, tok_idx), "Numeric")) continue;
        if (i > 0) {
            const prev_kind = tok_buf.getToken(TokenIndex.fromInt(@intCast(i - 1))).kind;
            switch (prev_kind) {
                .kw_type, .kw_struct, .kw_enum, .kw_union, .kw_trait, .kw_bit_field, .kw_as => return true,
                .lbracket, .comma => {
                    // Check for `[Numeric]` or `[Numeric: Bound]` type parameter declaration:
                    if (i + 1 < tok_count) {
                        const next_kind = tok_buf.getToken(TokenIndex.fromInt(@intCast(i + 1))).kind;
                        if (next_kind == .colon or next_kind == .eq) return true;
                        if ((prev_kind == .lbracket) and next_kind == .rbracket and i >= 2) {
                            const before_lbracket = tok_buf.getToken(TokenIndex.fromInt(@intCast(i - 2))).kind;
                            if (before_lbracket == .ident or before_lbracket == .kw_impl) return true;
                        }
                    }
                },
                else => {},
            }
        }
    }
    return false;
}

/// Skips a nested standard `"…"` or `"""…"""` literal inside an interpolation `{ … }` hole without emitting edits.
fn skipStandardStringInHole(source: []const u8, start_pos: usize, limit_pos: usize, is_triple: bool) usize {
    var pos = start_pos;
    while (pos < limit_pos) {
        if (is_triple) {
            if (pos + 2 < limit_pos and source[pos] == '"' and source[pos + 1] == '"' and source[pos + 2] == '"') {
                return pos + 3;
            }
        } else if (source[pos] == '"') {
            return pos + 1;
        }
        if (source[pos] == '\\') {
            if (pos + 2 < limit_pos and source[pos + 1] == 'u' and source[pos + 2] == '{') {
                pos += 3;
                while (pos < limit_pos and source[pos] != '}') : (pos += 1) {}
                if (pos < limit_pos) pos += 1;
            } else {
                pos = @min(pos + 2, limit_pos);
            }
            continue;
        }
        if (source[pos] == '{') {
            if (pos + 1 < limit_pos and source[pos + 1] == '{') {
                pos += 2;
                continue;
            }
            pos = scanHoleEndWithoutEdits(source, pos + 1, limit_pos);
            continue;
        }
        if (source[pos] == '}' and pos + 1 < limit_pos and source[pos + 1] == '}') {
            pos += 2;
            continue;
        }
        pos += 1;
    }
    return pos;
}

/// Scans to the matching `}` of a `{ … }` interpolation hole, handling single and triple-quoted raw/byte/standard strings.
fn scanHoleEndWithoutEdits(source: []const u8, start_pos: usize, limit_pos: usize) usize {
    var pos = start_pos;
    var brace_depth: u32 = 1;
    while (pos < limit_pos and brace_depth > 0) {
        const ch_byte = source[pos];
        if (ch_byte == '/' and pos + 1 < limit_pos and source[pos + 1] == '/') {
            pos += 2;
            while (pos < limit_pos and source[pos] != '\n') : (pos += 1) {}
            continue;
        }
        if (ch_byte == '/' and pos + 1 < limit_pos and source[pos + 1] == '*') {
            pos += 2;
            var comment_depth: u32 = 1;
            while (pos + 1 < limit_pos and comment_depth > 0) {
                if (source[pos] == '/' and source[pos + 1] == '*') {
                    comment_depth += 1;
                    pos += 2;
                } else if (source[pos] == '*' and source[pos + 1] == '/') {
                    comment_depth -= 1;
                    pos += 2;
                } else {
                    pos += 1;
                }
            }
            continue;
        }
        if (ch_byte == '\'' or (ch_byte == 'b' and pos + 1 < limit_pos and source[pos + 1] == '\'' and
            !(pos > start_pos and isIdentContinueByte(source[pos - 1]))))
        {
            pos += if (ch_byte == 'b') 2 else 1;
            while (pos < limit_pos and source[pos] != '\'') {
                pos += if (source[pos] == '\\' and pos + 1 < limit_pos) 2 else 1;
            }
            if (pos < limit_pos) pos += 1;
            continue;
        }
        // Skip raw (`r"…"`, `r#"…"#`, `r"""…"""`) and byte (`b"…"`, `b"""…"""`, `br"…"`, `br"""…"""`) literals:
        if ((ch_byte == 'r' or ch_byte == 'b') and pos + 1 < limit_pos) {
            const is_prev_ident = pos > start_pos and isIdentContinueByte(source[pos - 1]);
            if (!is_prev_ident) {
                var probe = pos + 1;
                if (ch_byte == 'b' and probe < limit_pos and source[probe] == 'r') probe += 1;
                var hash_count: usize = 0;
                while (probe < limit_pos and source[probe] == '#') : (probe += 1) {
                    hash_count += 1;
                }
                if (probe < limit_pos and source[probe] == '"') {
                    const is_raw = ch_byte == 'r' or (pos + 1 < limit_pos and source[pos + 1] == 'r');
                    var quote_run: usize = 0;
                    while (probe + quote_run < limit_pos and source[probe + quote_run] == '"') : (quote_run += 1) {}
                    const has_immediate_close_hashes = hash_count > 0 and
                        probe + quote_run + hash_count <= limit_pos and blk_h: {
                        var h_i: usize = 0;
                        while (h_i < hash_count) : (h_i += 1) {
                            if (source[probe + quote_run + h_i] != '#') break :blk_h false;
                        }
                        break :blk_h true;
                    };
                    const is_triple_lit = probe + 2 < limit_pos and
                        source[probe] == '"' and source[probe + 1] == '"' and source[probe + 2] == '"' and
                        quote_run >= 3 and !has_immediate_close_hashes;
                    pos = probe + (if (is_triple_lit) @as(usize, 3) else 1);
                    while (pos < limit_pos) {
                        if (!is_raw and source[pos] == '\\' and pos + 1 < limit_pos) {
                            pos += 2;
                            continue;
                        }
                        if (is_triple_lit) {
                            if (pos + 2 < limit_pos and
                                source[pos] == '"' and source[pos + 1] == '"' and source[pos + 2] == '"')
                            {
                                var matched_hashes: usize = 0;
                                while (matched_hashes < hash_count and
                                    pos + 3 + matched_hashes < limit_pos and
                                    source[pos + 3 + matched_hashes] == '#') : (matched_hashes += 1)
                                {}
                                if (matched_hashes == hash_count) {
                                    pos += 3 + hash_count;
                                    break;
                                }
                            }
                        } else if (source[pos] == '"') {
                            var matched_hashes: usize = 0;
                            while (matched_hashes < hash_count and
                                pos + 1 + matched_hashes < limit_pos and
                                source[pos + 1 + matched_hashes] == '#') : (matched_hashes += 1)
                            {}
                            if (matched_hashes == hash_count) {
                                pos += 1 + hash_count;
                                break;
                            }
                        }
                        pos += 1;
                    }
                    continue;
                }
            }
        }
        if (ch_byte == '"') {
            const is_triple = pos + 2 < limit_pos and source[pos + 1] == '"' and source[pos + 2] == '"';
            pos = skipStandardStringInHole(source, pos + (if (is_triple) @as(usize, 3) else 1), limit_pos, is_triple);
            continue;
        }
        if (ch_byte == '{') {
            brace_depth += 1;
        } else if (ch_byte == '}') {
            brace_depth -= 1;
        }
        pos += 1;
    }
    return pos;
}

/// Advances past a `{ … }` interpolation hole inside a `.string_lit` and runs Tier 1 shims on its expression slice.
fn scanStringInterpolationExpr(
    allocator: std.mem.Allocator,
    source: []const u8,
    start_pos: usize,
    limit_pos: usize,
    base_offset: u32,
    file_id: FileId,
    options: UpgradeOptions,
    has_local_std: bool,
    has_local_numeric: bool,
    depth: u8,
    collector: *FixCollector,
) anyerror!usize {
    const after_close = scanHoleEndWithoutEdits(source, start_pos, limit_pos);
    if (after_close > start_pos and after_close <= limit_pos and source[after_close - 1] == '}' and depth < 32) {
        const raw_hole = source[start_pos .. after_close - 1];
        const split = type_system.splitInterpolationHole(raw_hole);
        if (split.expr_slice.len > 0) {
            try collectTier1FixesOnSlice(
                allocator,
                split.expr_slice,
                base_offset +| @as(u32, @intCast(start_pos)),
                file_id,
                options,
                has_local_std,
                has_local_numeric,
                depth + 1,
                collector,
            );
        }
    }
    return after_close;
}

/// Deterministic non-backtracking string scanner rewriting `\{`/`\}` (`UR-22-00`) and `{ expr }` Tier 1 holes.
fn scanStandardStringBodyForBraceEscapes(
    allocator: std.mem.Allocator,
    source: []const u8,
    start_pos: usize,
    limit_pos: usize,
    base_offset: u32,
    is_triple: bool,
    file_id: FileId,
    options: UpgradeOptions,
    has_local_std: bool,
    has_local_numeric: bool,
    depth: u8,
    collector: *FixCollector,
) anyerror!usize {
    const is_ur22_00 = isRuleEnabled(options.rule_mask, .ur_22_00_lexical_token_canonicalization);
    var pos = start_pos;
    while (pos < limit_pos) {
        if (is_triple) {
            if (pos + 2 < limit_pos and source[pos] == '"' and source[pos + 1] == '"' and source[pos + 2] == '"') {
                return pos + 3;
            }
        } else if (source[pos] == '"') {
            return pos + 1;
        }

        if (source[pos] == '\\') {
            if (pos + 1 < limit_pos) {
                const escaped_byte = source[pos + 1];
                if (is_ur22_00 and escaped_byte == '{') {
                    const abs_pos = base_offset +| @as(u32, @intCast(pos));
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        abs_pos,
                        abs_pos +| 2,
                        "{{",
                        "UR-22-00: replace retired `\\{` string brace escape with `{{`",
                    );
                    pos += 2;
                    continue;
                }
                if (is_ur22_00 and escaped_byte == '}') {
                    const abs_pos = base_offset +| @as(u32, @intCast(pos));
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        abs_pos,
                        abs_pos +| 2,
                        "}}",
                        "UR-22-00: replace retired `\\}` string brace escape with `}}`",
                    );
                    pos += 2;
                    continue;
                }
                if (escaped_byte == 'u' and pos + 2 < limit_pos and source[pos + 2] == '{') {
                    pos += 3;
                    while (pos < limit_pos and source[pos] != '}') : (pos += 1) {}
                    if (pos < limit_pos) pos += 1;
                    continue;
                }
                // `\\` advances by 2 bytes so `\\{` leaves `\\` intact and sees `{` as an interpolation hole:
                pos += 2;
                continue;
            }
            return limit_pos;
        }

        if (source[pos] == '{') {
            if (pos + 1 < limit_pos and source[pos + 1] == '{') {
                pos += 2;
                continue;
            }
            pos = try scanStringInterpolationExpr(
                allocator,
                source,
                pos + 1,
                limit_pos,
                base_offset,
                file_id,
                options,
                has_local_std,
                has_local_numeric,
                depth,
                collector,
            );
            continue;
        }

        if (source[pos] == '}' and pos + 1 < limit_pos and source[pos + 1] == '}') {
            pos += 2;
            continue;
        }

        pos += 1;
    }
    return pos;
}

/// Tokenizes `source` (rebased at `base_offset`) and emits Tier 1 `UR-21-00` and `UR-22-00` fixes into `collector`.
fn collectTier1FixesOnSlice(
    allocator: std.mem.Allocator,
    source: []const u8,
    base_offset: u32,
    file_id: FileId,
    options: UpgradeOptions,
    has_local_std: bool,
    has_local_numeric: bool,
    depth: u8,
    collector: *FixCollector,
) anyerror!void {
    const is_ur21_00 = isRuleEnabled(options.rule_mask, .ur_21_00_path_coloncolon_and_std_root);
    const is_ur22_00 = isRuleEnabled(options.rule_mask, .ur_22_00_lexical_token_canonicalization);
    if (!is_ur21_00 and !is_ur22_00) return;

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var lex_sink = DiagnosticSink.init(allocator);
    defer lex_sink.deinit();

    var lex_inst = lexer.Lexer.init(source, file_id, &tok_buf, &lex_sink, collector.interner);
    _ = try lex_inst.tokenize();
    const tok_count = tok_buf.countTokens();

    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const tok_idx = TokenIndex.fromInt(@intCast(i));
        const rec = tok_buf.getToken(tok_idx);
        if (rec.flags.is_synthesized or rec.kind == .eof or rec.byte_len == 0) continue;
        const lexeme = symbol_resolver.extractTokenSlice(source, &tok_buf, tok_idx);
        const local_start = rec.byte_offset;
        const local_end = rec.byte_offset +| rec.byte_len;
        const start_byte = base_offset +| local_start;
        const end_byte = base_offset +| local_end;

        // [1] `UR-21-00`; `::` -> `.` and root `std` -> `cx`:
        if (is_ur21_00) {
            if (rec.kind == .dot and rec.byte_len == 2 and std.mem.eql(u8, lexeme, "::")) {
                try collector.appendSingleEdit(
                    .syntax_canonicalization,
                    start_byte,
                    end_byte,
                    ".",
                    "UR-21-00: replace retired `::` path separator with `.`",
                );
                continue;
            }
            if (!has_local_std and rec.kind == .ident and std.mem.eql(u8, lexeme, "std")) {
                const prev_kind: ?TokenKind = if (i > 0)
                    tok_buf.getToken(TokenIndex.fromInt(@intCast(i - 1))).kind
                else
                    null;
                const next_kind: ?TokenKind = if (i + 1 < tok_count)
                    tok_buf.getToken(TokenIndex.fromInt(@intCast(i + 1))).kind
                else
                    null;
                const is_blocked_prefix = if (prev_kind) |pk| switch (pk) {
                    .dot,
                    .kw_let,
                    .kw_var,
                    .kw_fn,
                    .kw_mod,
                    .kw_struct,
                    .kw_enum,
                    .kw_union,
                    .kw_type,
                    .kw_const,
                    .kw_trait,
                    .kw_as,
                    .colon,
                    .at,
                    => true,
                    else => false,
                } else false;

                const is_root_std_path = !is_blocked_prefix and next_kind != .colon and
                    (prev_kind == .kw_use or next_kind == .dot);
                if (is_root_std_path) {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        start_byte,
                        end_byte,
                        "cx",
                        "UR-21-00: rename root `std` module path to `cx`",
                    );
                    continue;
                }
            }
        }

        // [2] `UR-22-00`; `&&` -> `and`, `@noalloc` -> `@no_alloc`, `Numeric` -> `Number`, `\{`/`\}` -> `{{`/`}}`:
        if (is_ur22_00) {
            if (rec.kind == .kw_and and rec.byte_len == 2 and std.mem.eql(u8, lexeme, "&&")) {
                const is_needing_left_sp = local_start > 0 and !isAsciiWhitespace(source[local_start - 1]) and
                    source[local_start - 1] != '(' and source[local_start - 1] != '[' and source[local_start - 1] != '{';
                const is_needing_right_sp = @as(usize, local_end) < source.len and
                    !isAsciiWhitespace(source[local_end]) and
                    source[local_end] != ')' and source[local_end] != ']' and source[local_end] != '}' and
                    source[local_end] != ',' and source[local_end] != ';';
                const and_repl: []const u8 = if (is_needing_left_sp and is_needing_right_sp)
                    " and "
                else if (is_needing_left_sp)
                    " and"
                else if (is_needing_right_sp)
                    "and "
                else
                    "and";
                try collector.appendSingleEdit(
                    .syntax_canonicalization,
                    start_byte,
                    end_byte,
                    and_repl,
                    "UR-22-00: replace retired `&&` operator with `and`",
                );
                continue;
            }

            if (rec.kind == .at and i + 1 < tok_count) {
                const next_tok = TokenIndex.fromInt(@intCast(i + 1));
                const next_rec = tok_buf.getToken(next_tok);
                const next_end = base_offset +| (next_rec.byte_offset +| next_rec.byte_len);
                if (next_rec.kind == .ident and
                    std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, &tok_buf, next_tok), "noalloc") and
                    !hasCommentsInByteRange(source, &tok_buf, local_end, next_rec.byte_offset))
                {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        start_byte,
                        next_end,
                        "@no_alloc",
                        "UR-22-00: replace retired `@noalloc` attribute with `@no_alloc`",
                    );
                    i += 1;
                    continue;
                }
            }

            if (!has_local_numeric and rec.kind == .type_ident and std.mem.eql(u8, lexeme, "Numeric")) {
                const is_member_after_dot = i > 0 and
                    tok_buf.getToken(TokenIndex.fromInt(@intCast(i - 1))).kind == .dot;
                if (!is_member_after_dot) {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        start_byte,
                        end_byte,
                        "Number",
                        "UR-22-00: replace retired `Numeric` type group with `Number`",
                    );
                    continue;
                }
            }
        }

        if (rec.kind == .string_lit and lexeme.len >= 2 and lexeme[0] != 'r' and lexeme[0] != 'b') {
            const is_triple = lexeme.len >= 6 and std.mem.startsWith(u8, lexeme, "\"\"\"");
            const open_len: usize = if (is_triple) 3 else 1;
            _ = try scanStandardStringBodyForBraceEscapes(
                allocator,
                source,
                @as(usize, local_start) + open_len,
                @as(usize, local_end),
                base_offset,
                is_triple,
                file_id,
                options,
                has_local_std,
                has_local_numeric,
                depth,
                collector,
            );
        }
    }
}

/// Collects Sub-stage A Tier 1 pre-CST lexical rewrites (`UR-21-00` and `UR-22-00`) into `collector`.
fn collectSubstageATier1Fixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    options: UpgradeOptions,
    collector: *FixCollector,
) !void {
    const is_ur21_00 = isRuleEnabled(options.rule_mask, .ur_21_00_path_coloncolon_and_std_root);
    const is_ur22_00 = isRuleEnabled(options.rule_mask, .ur_22_00_lexical_token_canonicalization);
    if (!is_ur21_00 and !is_ur22_00) return;

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var lex_sink = DiagnosticSink.init(allocator);
    defer lex_sink.deinit();

    var lex_inst = lexer.Lexer.init(source, file_id, &tok_buf, &lex_sink, collector.interner);
    _ = try lex_inst.tokenize();

    const has_local_std = if (is_ur21_00) hasLocalStdDeclaration(source, &tok_buf) else false;
    const has_local_numeric = if (is_ur22_00) hasLocalNumericDeclaration(source, &tok_buf) else false;
    try collectTier1FixesOnSlice(
        allocator,
        source,
        0,
        file_id,
        options,
        has_local_std,
        has_local_numeric,
        0,
        collector,
    );
}

// --------------- Tier 2 CST Structural Rewrites ---------------

/// Checks whether a token kind can start a value expression after a call-site mode keyword (`ref`, `inout`, `out`).
fn isCallArgExprStartToken(kind: TokenKind) bool {
    return switch (kind) {
        .ident,
        .type_ident,
        .const_ident,
        .kw_self_val,
        .kw_self_type,
        .kw_context,
        .lparen,
        .lbracket,
        .lbrace,
        .star,
        .amp,
        .minus,
        .tilde,
        .bang,
        .kw_not,
        .kw_if,
        .kw_match,
        .kw_unsafe,
        .int_lit,
        .float_lit,
        .string_lit,
        .char_lit,
        .byte_lit,
        .byte_string_lit,
        .kw_true,
        .kw_false,
        .at,
        => true,
        else => false,
    };
}

/// Checks whether `source` declares a local type/alias named `target_name` (`"Option"`, `"Result"`, or `"c_void"`).
fn hasLocalSymbolShadow(source: []const u8, tok_buf: *const TokenBuffer, target_name: []const u8) bool {
    const tok_count = tok_buf.countTokens();
    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const tok_idx = TokenIndex.fromInt(@intCast(i));
        if (!std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, tok_idx), target_name)) continue;
        if (i > 0) {
            const prev_kind = tok_buf.getToken(TokenIndex.fromInt(@intCast(i - 1))).kind;
            switch (prev_kind) {
                .kw_struct,
                .kw_enum,
                .kw_union,
                .kw_type,
                .kw_trait,
                .kw_bit_field,
                .kw_fn,
                .kw_let,
                .kw_var,
                .kw_const,
                .kw_as,
                => return true,
                else => {},
            }
        }
    }
    return false;
}

/// Rewrites unqualified `Some`/`None`/`Ok`/`Err` pattern heads inside `[pat_first .. pat_last]` to `.Variant`.
fn formatUpgradedPatternText(
    allocator: std.mem.Allocator,
    source: []const u8,
    tok_buf: *const TokenBuffer,
    pat_first: TokenIndex,
    pat_last: TokenIndex,
    is_ur22_01_enabled: bool,
) !struct { text: []u8, is_trailing_struct_pat: bool } {
    const pat_start_byte = tok_buf.getToken(pat_first).byte_offset;
    const pat_last_rec = tok_buf.getToken(pat_last);
    const pat_end_byte = pat_last_rec.byte_offset +| pat_last_rec.byte_len;

    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);

    var cursor_byte: usize = pat_start_byte;
    var tok_i: u32 = pat_first.asInt();
    while (tok_i <= pat_last.asInt()) : (tok_i += 1) {
        const tok_idx = TokenIndex.fromInt(tok_i);
        const rec = tok_buf.getToken(tok_idx);
        if (rec.flags.is_synthesized or rec.byte_len == 0) continue;
        if (rec.byte_offset > cursor_byte) {
            try builder.appendSlice(allocator, source[cursor_byte..rec.byte_offset]);
        }
        const lex = symbol_resolver.extractTokenSlice(source, tok_buf, tok_idx);
        const prev_kind: ?TokenKind = if (tok_i > pat_first.asInt())
            tok_buf.getToken(TokenIndex.fromInt(tok_i - 1)).kind
        else
            null;

        if (rec.kind == .type_ident and prev_kind != .dot) {
            if (UNQUALIFIED_STD_VARIANT_MAP.get(lex)) |dot_variant| {
                const next_kind: ?TokenKind = if (tok_i < pat_last.asInt())
                    tok_buf.getToken(TokenIndex.fromInt(tok_i + 1)).kind
                else
                    null;
                if (next_kind != .dot and next_kind != .lbrace) {
                    try builder.appendSlice(allocator, dot_variant);
                    cursor_byte = rec.byte_offset + rec.byte_len;
                    continue;
                }
            }
        }
        if (is_ur22_01_enabled and rec.kind == .kw_mut and prev_kind != .amp and prev_kind != .star) {
            try builder.appendSlice(allocator, "var");
            cursor_byte = rec.byte_offset + rec.byte_len;
            continue;
        }

        try builder.appendSlice(allocator, lex);
        cursor_byte = rec.byte_offset + rec.byte_len;
    }
    if (cursor_byte < pat_end_byte) {
        try builder.appendSlice(allocator, source[cursor_byte..pat_end_byte]);
    }

    const is_trailing_struct_pat = pat_last_rec.kind == .rbrace;
    return .{
        .text = try builder.toOwnedSlice(allocator),
        .is_trailing_struct_pat = is_trailing_struct_pat,
    };
}

/// Checks whether `[first_tok .. last_tok]` contains a top-level low-precedence operator requiring `(…)` before `is`.
fn isScrutineeNeedingParensForIs(tok_buf: *const TokenBuffer, first_tok: TokenIndex, last_tok: TokenIndex) bool {
    if (tok_buf.getToken(last_tok).kind == .rbrace) return true;
    var depth: u32 = 0;
    var tok_i: u32 = first_tok.asInt();
    while (tok_i <= last_tok.asInt()) : (tok_i += 1) {
        const kind = tok_buf.getToken(TokenIndex.fromInt(tok_i)).kind;
        switch (kind) {
            .lparen, .lbracket, .lbrace => depth += 1,
            .rparen, .rbracket, .rbrace => depth -|= 1,
            else => {
                if (depth == 0) {
                    switch (kind) {
                        .kw_is,
                        .eqeq,
                        .bang_eq,
                        .lt,
                        .le,
                        .gt,
                        .ge,
                        .kw_and,
                        .kw_or,
                        .pipepipe,
                        .dotdot,
                        .dotdoteq,
                        .pipe_gt,
                        .kw_orelse,
                        .kw_catch,
                        .kw_as,
                        .kw_if,
                        .kw_match,
                        => return true,
                        else => {},
                    }
                }
            },
        }
    }
    return false;
}

/// Checks whether `[first_tok .. last_tok]` has a top-level operator with binding power `< 9` (requiring `(…)` around `orelse`).
fn isOrelseOperandNeedingParens(tok_buf: *const TokenBuffer, first_tok: TokenIndex, last_tok: TokenIndex) bool {
    var depth: u32 = 0;
    var tok_i: u32 = first_tok.asInt();
    while (tok_i <= last_tok.asInt()) : (tok_i += 1) {
        const kind = tok_buf.getToken(TokenIndex.fromInt(tok_i)).kind;
        switch (kind) {
            .lparen, .lbracket, .lbrace => depth += 1,
            .rparen, .rbracket, .rbrace => depth -|= 1,
            else => {
                if (depth == 0) {
                    switch (kind) {
                        .kw_orelse,
                        .kw_catch,
                        .pipe_gt,
                        .kw_or,
                        .pipepipe,
                        .kw_and,
                        .eqeq,
                        .bang_eq,
                        .lt,
                        .le,
                        .gt,
                        .ge,
                        .kw_is,
                        .dotdot,
                        .dotdoteq,
                        .kw_if,
                        .kw_match,
                        => return true,
                        else => {},
                    }
                }
            },
        }
    }
    return false;
}

/// Collects `UR-21-01` (`if let`) and `UR-21-02` (`while let`) rewrites across `.if_cond` / `.while_header` CST nodes.
fn collectIfWhileLetFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    is_ur21_01: bool,
    is_ur21_02: bool,
    is_ur22_01: bool,
    collector: *FixCollector,
) !void {
    if (!is_ur21_01 and !is_ur21_02) return;
    const node_count = cst_arena.countNodes();

    var idx: usize = 0;
    while (idx < node_count) : (idx += 1) {
        const cst_id = CstNodeIndex.fromInt(@intCast(idx));
        const rec = cst_arena.getNode(cst_id);
        const is_if = rec.kind == .if_cond and is_ur21_01;
        const is_while = rec.kind == .while_header and is_ur21_02;
        if (!is_if and !is_while) continue;

        const cond_span = extractCstTokenSpan(cst_arena, tok_buf, cst_id) orelse continue;
        var tok_i: u32 = cond_span.first_tok.asInt();
        var depth: u32 = 0;

        while (tok_i <= cond_span.last_tok.asInt()) : (tok_i += 1) {
            const cur_tok = TokenIndex.fromInt(tok_i);
            const cur_rec = tok_buf.getToken(cur_tok);
            switch (cur_rec.kind) {
                .lparen, .lbracket, .lbrace => depth += 1,
                .rparen, .rbracket, .rbrace => depth -|= 1,
                .kw_let => {
                    if (depth != 0) continue;
                    // Locate matching top-level `=` separating `$pat` and `$scrut`:
                    var scan_i: u32 = tok_i + 1;
                    var pat_depth: u32 = 0;
                    var eq_tok: TokenIndex = .none;
                    while (scan_i <= cond_span.last_tok.asInt()) : (scan_i += 1) {
                        const scan_k = tok_buf.getToken(TokenIndex.fromInt(scan_i)).kind;
                        switch (scan_k) {
                            .lparen, .lbracket, .lbrace => pat_depth += 1,
                            .rparen, .rbracket, .rbrace => pat_depth -|= 1,
                            .eq => {
                                if (pat_depth == 0) {
                                    eq_tok = TokenIndex.fromInt(scan_i);
                                    break;
                                }
                            },
                            else => {},
                        }
                    }
                    if (eq_tok.isNone() or eq_tok.asInt() <= tok_i + 1 or eq_tok.asInt() >= cond_span.last_tok.asInt()) {
                        continue;
                    }

                    // Locate end of `$scrut` before any chained top-level `and` / `or` / `||`:
                    var scrut_end_i: u32 = cond_span.last_tok.asInt();
                    var scrut_depth: u32 = 0;
                    var rhs_i: u32 = eq_tok.asInt() + 1;
                    while (rhs_i <= cond_span.last_tok.asInt()) : (rhs_i += 1) {
                        const rhs_k = tok_buf.getToken(TokenIndex.fromInt(rhs_i)).kind;
                        switch (rhs_k) {
                            .lparen, .lbracket, .lbrace => scrut_depth += 1,
                            .rparen, .rbracket, .rbrace => scrut_depth -|= 1,
                            .kw_and, .kw_or, .pipepipe => {
                                if (scrut_depth == 0 and rhs_i > eq_tok.asInt() + 1) {
                                    scrut_end_i = rhs_i - 1;
                                    break;
                                }
                            },
                            else => {},
                        }
                    }

                    const pat_first = TokenIndex.fromInt(tok_i + 1);
                    const pat_last = TokenIndex.fromInt(eq_tok.asInt() - 1);
                    const scrut_first = TokenIndex.fromInt(eq_tok.asInt() + 1);
                    const scrut_last = TokenIndex.fromInt(scrut_end_i);
                    const pat_start_b = tok_buf.getToken(pat_first).byte_offset;
                    const pat_last_rec = tok_buf.getToken(pat_last);
                    const pat_end_b = pat_last_rec.byte_offset +| pat_last_rec.byte_len;
                    const scrut_start_b = tok_buf.getToken(scrut_first).byte_offset;
                    const scrut_last_rec = tok_buf.getToken(scrut_last);
                    const scrut_end_b = scrut_last_rec.byte_offset +| scrut_last_rec.byte_len;

                    if (hasCommentsInByteRange(source, tok_buf, cur_rec.byte_offset, pat_start_b) or
                        hasCommentsInByteRange(source, tok_buf, pat_end_b, scrut_start_b))
                    {
                        tok_i = scrut_end_i;
                        continue;
                    }

                    const formatted_pat = try formatUpgradedPatternText(
                        allocator,
                        source,
                        tok_buf,
                        pat_first,
                        pat_last,
                        is_ur22_01,
                    );
                    defer allocator.free(formatted_pat.text);

                    const scrut_raw = std.mem.trim(u8, source[scrut_start_b..scrut_end_b], " \t\r\n");
                    const is_scrut_parens = isScrutineeNeedingParensForIs(tok_buf, scrut_first, scrut_last);

                    const pat_trimmed = std.mem.trim(u8, formatted_pat.text, " \t\r\n");
                    const repl = try std.fmt.allocPrint(
                        allocator,
                        "{s}{s}{s} is {s}{s}{s}",
                        .{
                            if (is_scrut_parens) "(" else "",
                            scrut_raw,
                            if (is_scrut_parens) ")" else "",
                            if (formatted_pat.is_trailing_struct_pat) "(" else "",
                            pat_trimmed,
                            if (formatted_pat.is_trailing_struct_pat) ")" else "",
                        },
                    );
                    defer allocator.free(repl);

                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        cur_rec.byte_offset,
                        scrut_end_b,
                        repl,
                        if (is_if)
                            "UR-21-01: rewrite `if let $pat = $scrut` to `if $scrut is $pat`"
                        else
                            "UR-21-02: rewrite `while let $pat = $scrut` to `while $scrut is $pat`",
                    );
                    tok_i = scrut_end_i;
                },
                else => {},
            }
        }
    }
}

/// Collects `UR-21-03` (`let .Some($id) = $expr else { $div; };` -> `let/var $id = $expr orelse $div;`) rewrites.
fn collectLetSomeElseToOrelseFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    rewritten_stmt_nodes: *std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    const node_count = cst_arena.countNodes();
    var idx: usize = 0;
    while (idx < node_count) : (idx += 1) {
        const stmt_cst = CstNodeIndex.fromInt(@intCast(idx));
        const stmt_rec = cst_arena.getNode(stmt_cst);
        if (stmt_rec.kind != .local_decl_stmt) continue;

        const stmt_end_node = @min(idx + @max(@as(usize, stmt_rec.subtree_size), 1), node_count);
        var else_branch_cst: CstNodeIndex = .none;
        var child_cursor = idx + 1;
        while (child_cursor < stmt_end_node) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cursor));
            const child_rec = cst_arena.getNode(child_id);
            if (child_rec.kind == .let_else_branch) {
                else_branch_cst = child_id;
                break;
            }
            child_cursor += @max(@as(usize, child_rec.subtree_size), 1);
        }
        if (else_branch_cst.isNone()) continue;

        const stmt_span = extractCstTokenSpan(cst_arena, tok_buf, stmt_cst) orelse continue;
        const else_span = extractCstTokenSpan(cst_arena, tok_buf, else_branch_cst) orelse continue;
        if (else_span.first_tok.asInt() <= stmt_span.first_tok.asInt() + 3) continue;

        // Locate top-level `=` between introducer and `else`:
        var eq_tok: TokenIndex = .none;
        var depth: u32 = 0;
        var scan_i: u32 = stmt_span.first_tok.asInt();
        while (scan_i < else_span.first_tok.asInt()) : (scan_i += 1) {
            const tok_k = tok_buf.getToken(TokenIndex.fromInt(scan_i)).kind;
            switch (tok_k) {
                .lparen, .lbracket, .lbrace => depth += 1,
                .rparen, .rbracket, .rbrace => depth -|= 1,
                .colon => {
                    // Reject outer `: Type` annotation on destructuring `let .Some(x): Option[T] = …`:
                    if (depth == 0) {
                        eq_tok = .none;
                        break;
                    }
                },
                .eq => {
                    if (depth == 0) {
                        eq_tok = TokenIndex.fromInt(scan_i);
                        break;
                    }
                },
                else => {},
            }
        }
        if (eq_tok.isNone() or eq_tok.asInt() + 1 >= else_span.first_tok.asInt()) continue;

        // Match introducer (`let` / `var` + optional `mut`) and `.Some([mut|var] $id)` / `Option.Some($id)`:
        var hdr_i: u32 = stmt_span.first_tok.asInt();
        const intro_kind = tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind;
        if (intro_kind != .kw_let and intro_kind != .kw_var) continue;
        var is_mutable = intro_kind == .kw_var;
        hdr_i += 1;
        if (hdr_i < eq_tok.asInt() and tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind == .kw_mut) {
            is_mutable = true;
            hdr_i += 1;
        }

        // Match `.Some(…)`, `Some(…)`, or `[cx.option.]Option.Some(…)`:
        var is_matched_some = false;
        if (hdr_i < eq_tok.asInt() and tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind == .dot) {
            hdr_i += 1;
            if (hdr_i < eq_tok.asInt() and
                std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(hdr_i)), "Some"))
            {
                hdr_i += 1;
                is_matched_some = true;
            }
        } else if (hdr_i < eq_tok.asInt()) {
            // Walk optional `cx.option.Option.` or `Option.` prefix ending in `Some`:
            var is_path_ok = true;
            var has_seen_some = false;
            var has_only_option_prefix = true;
            while (hdr_i < eq_tok.asInt()) {
                const seg_tok = TokenIndex.fromInt(hdr_i);
                const seg_lex = symbol_resolver.extractTokenSlice(source, tok_buf, seg_tok);
                if (hdr_i + 1 < eq_tok.asInt() and tok_buf.getToken(TokenIndex.fromInt(hdr_i + 1)).kind == .dot) {
                    if (!OPTION_PREFIX_SEGMENT_SET.has(seg_lex)) {
                        has_only_option_prefix = false;
                        break;
                    }
                    hdr_i += 2;
                } else {
                    if (std.mem.eql(u8, seg_lex, "Some")) {
                        has_seen_some = true;
                        hdr_i += 1;
                    } else {
                        is_path_ok = false;
                    }
                    break;
                }
            }
            is_matched_some = is_path_ok and has_seen_some and has_only_option_prefix;
        }
        if (!is_matched_some) continue;

        // Expect `(` `[mut | var]` `<ident>` `)` reaching `eq_tok`:
        if (hdr_i >= eq_tok.asInt() or tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind != .lparen) continue;
        hdr_i += 1;
        if (hdr_i < eq_tok.asInt()) {
            const mod_kind = tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind;
            if (mod_kind == .kw_mut or mod_kind == .kw_var) {
                is_mutable = true;
                hdr_i += 1;
            }
        }
        if (hdr_i >= eq_tok.asInt() or tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind != .ident) continue;
        const bind_ident = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(hdr_i));
        hdr_i += 1;
        if (hdr_i >= eq_tok.asInt() or tok_buf.getToken(TokenIndex.fromInt(hdr_i)).kind != .rparen) continue;
        hdr_i += 1;
        if (hdr_i != eq_tok.asInt()) continue;

        // Inspect `.block` inside `.let_else_branch`:
        const else_rec = cst_arena.getNode(else_branch_cst);
        const else_end_node = @min(
            @as(usize, else_branch_cst.asInt()) + @max(@as(usize, else_rec.subtree_size), 1),
            node_count,
        );
        var block_cst: CstNodeIndex = .none;
        var else_cur: usize = else_branch_cst.asInt() + 1;
        while (else_cur < else_end_node) {
            const sub_id = CstNodeIndex.fromInt(@intCast(else_cur));
            const sub_rec = cst_arena.getNode(sub_id);
            if (sub_rec.kind == .block) {
                block_cst = sub_id;
                break;
            }
            else_cur += @max(@as(usize, sub_rec.subtree_size), 1);
        }
        if (block_cst.isNone()) continue;
        const block_span = extractCstTokenSpan(cst_arena, tok_buf, block_cst) orelse continue;

        // Enumerate direct statement children of `block_cst`:
        const block_rec = cst_arena.getNode(block_cst);
        const block_end_node = @min(
            @as(usize, block_cst.asInt()) + @max(@as(usize, block_rec.subtree_size), 1),
            node_count,
        );
        var stmt_count: usize = 0;
        var single_stmt_cst: CstNodeIndex = .none;
        var last_stmt_cst: CstNodeIndex = .none;
        var blk_cur: usize = block_cst.asInt() + 1;
        while (blk_cur < block_end_node) {
            const item_id = CstNodeIndex.fromInt(@intCast(blk_cur));
            const item_rec = cst_arena.getNode(item_id);
            const is_brace_leaf = item_rec.subtree_size <= 1 and !item_rec.token.isNone() and
                (tok_buf.getToken(item_rec.token).kind == .lbrace or tok_buf.getToken(item_rec.token).kind == .rbrace);
            if (!is_brace_leaf and item_rec.kind != .block_start) {
                stmt_count += 1;
                if (stmt_count == 1) single_stmt_cst = item_id;
                last_stmt_cst = item_id;
            }
            blk_cur += @max(@as(usize, item_rec.subtree_size), 1);
        }
        if (stmt_count == 0 or last_stmt_cst.isNone()) continue;

        const is_last_diverging = blk_div: {
            const last_sp = extractCstTokenSpan(cst_arena, tok_buf, last_stmt_cst) orelse break :blk_div false;
            const first_k = tok_buf.getToken(last_sp.first_tok).kind;
            break :blk_div first_k == .kw_return or first_k == .kw_break or
                first_k == .kw_continue or first_k == .kw_unreachable;
        };
        if (!is_last_diverging) continue;

        const expr_first = TokenIndex.fromInt(eq_tok.asInt() + 1);
        const expr_last = TokenIndex.fromInt(else_span.first_tok.asInt() - 1);
        const expr_start_b = tok_buf.getToken(expr_first).byte_offset;
        const expr_last_rec = tok_buf.getToken(expr_last);
        const expr_end_b = expr_last_rec.byte_offset +| expr_last_rec.byte_len;
        const expr_raw = std.mem.trim(u8, source[expr_start_b..expr_end_b], " \t\r\n");
        const is_expr_parens = isOrelseOperandNeedingParens(tok_buf, expr_first, expr_last);

        const has_block_comments = hasCommentsInByteRange(source, tok_buf, block_span.start_byte, block_span.end_byte);
        if (hasCommentsInByteRange(source, tok_buf, stmt_span.start_byte, expr_start_b)) continue;

        const rhs_orelse_text: []const u8 = if (stmt_count == 1 and !has_block_comments) blk_unwrap: {
            const div_sp = extractCstTokenSpan(cst_arena, tok_buf, single_stmt_cst).?;
            var div_end_b = div_sp.end_byte;
            if (tok_buf.getToken(div_sp.last_tok).kind == .semi and div_sp.last_tok.asInt() > div_sp.first_tok.asInt()) {
                const prev_rec = tok_buf.getToken(TokenIndex.fromInt(div_sp.last_tok.asInt() - 1));
                div_end_b = prev_rec.byte_offset +| prev_rec.byte_len;
            }
            break :blk_unwrap std.mem.trim(u8, source[div_sp.start_byte..div_end_b], " \t\r\n");
        } else source[block_span.start_byte..block_span.end_byte];

        const repl = try std.fmt.allocPrint(
            allocator,
            "{s} {s} = {s}{s}{s} orelse {s};",
            .{
                if (is_mutable) "var" else "let",
                bind_ident,
                if (is_expr_parens) "(" else "",
                expr_raw,
                if (is_expr_parens) ")" else "",
                rhs_orelse_text,
            },
        );
        defer allocator.free(repl);

        try rewritten_stmt_nodes.put(allocator, stmt_cst.asInt(), {});
        try collector.appendSingleEdit(
            .lint_idiom,
            stmt_span.start_byte,
            stmt_span.end_byte,
            repl,
            "UR-21-03: condense `let .Some($id) = $expr else` guard to `orelse`",
        );
    }
}

/// Collects `UR-22-01` (infix `||` -> `or`, `let mut` / `var mut` / pattern `mut $id` -> `var`) rewrites.
fn collectLogicalOrAndVarFixes(
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    rewritten_stmt_nodes: *const std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    // [1] Infix `||` -> `or` strictly on AST `.binary_expr` (zero-arg closures `|| body` are `.closure_expr`):
    const ast_count = ast_arena.countNodes();
    var ast_i: usize = 0;
    while (ast_i < ast_count) : (ast_i += 1) {
        const node = ast_arena.getNode(NodeIndex.fromInt(@intCast(ast_i)));
        if (node.tag != .binary_expr or node.main_token.isNone()) continue;
        const op_rec = tok_buf.getToken(node.main_token);
        if (op_rec.kind != .pipepipe or op_rec.flags.is_synthesized) continue;
        const start_b = op_rec.byte_offset;
        const end_b = op_rec.byte_offset +| op_rec.byte_len;
        const is_left_sp = start_b > 0 and !isAsciiWhitespace(source[start_b - 1]) and source[start_b - 1] != '(';
        const is_right_sp = @as(usize, end_b) < source.len and !isAsciiWhitespace(source[end_b]) and source[end_b] != ')';
        const or_repl: []const u8 = if (is_left_sp and is_right_sp)
            " or "
        else if (is_left_sp)
            " or"
        else if (is_right_sp)
            "or "
        else
            "or";
        try collector.appendSingleEdit(
            .syntax_canonicalization,
            start_b,
            end_b,
            or_repl,
            "UR-22-01: replace retired infix `||` operator with `or`",
        );
    }

    // [2] `let mut` / `var mut` -> `var` on `.local_decl_stmt` and pattern `mut $id` -> `var $id`:
    var emitted_mut_tokens: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer emitted_mut_tokens.deinit(collector.allocator);

    const cst_count = cst_arena.countNodes();
    var cst_i: usize = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const cst_id = CstNodeIndex.fromInt(@intCast(cst_i));
        const rec = cst_arena.getNode(cst_id);
        if (rec.kind == .local_decl_stmt) {
            if (rewritten_stmt_nodes.contains(cst_id.asInt())) {
                cst_i += @max(@as(usize, rec.subtree_size), 1) - 1;
                continue;
            }
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |sp| {
                // Skip leading attributes on `@state let mut x = …`:
                var intro_tok_i: u32 = sp.first_tok.asInt();
                while (intro_tok_i <= sp.last_tok.asInt()) : (intro_tok_i += 1) {
                    const tk = tok_buf.getToken(TokenIndex.fromInt(intro_tok_i)).kind;
                    if (tk == .kw_let or tk == .kw_var) break;
                }
                if (intro_tok_i + 1 <= sp.last_tok.asInt()) {
                    const intro_rec = tok_buf.getToken(TokenIndex.fromInt(intro_tok_i));
                    const next_tok = TokenIndex.fromInt(intro_tok_i + 1);
                    const next_rec = tok_buf.getToken(next_tok);
                    if ((intro_rec.kind == .kw_let or intro_rec.kind == .kw_var) and
                        next_rec.kind == .kw_mut and
                        !hasCommentsInByteRange(source, tok_buf, intro_rec.byte_offset, next_rec.byte_offset))
                    {
                        try emitted_mut_tokens.put(collector.allocator, next_tok.asInt(), {});
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            intro_rec.byte_offset,
                            next_rec.byte_offset +| next_rec.byte_len,
                            "var",
                            "UR-22-01: replace `let mut` / `var mut` with `var`",
                        );
                    }
                }
            }
        }

        const is_pattern_ctx = switch (rec.kind) {
            .ident_pat, .field_pat, .variant_pat, .tuple_pat, .slice_pat, .struct_pat, .for_header => true,
            else => false,
        };
        if (is_pattern_ctx) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |pat_sp| {
                var tok_i: u32 = pat_sp.first_tok.asInt();
                while (tok_i <= pat_sp.last_tok.asInt()) : (tok_i += 1) {
                    if (rec.kind == .for_header and tok_buf.getToken(TokenIndex.fromInt(tok_i)).kind == .kw_in) break;
                    if (emitted_mut_tokens.contains(tok_i)) continue;
                    const mut_rec = tok_buf.getToken(TokenIndex.fromInt(tok_i));
                    if (mut_rec.kind != .kw_mut or mut_rec.flags.is_synthesized) continue;
                    const prev_k: ?TokenKind = if (tok_i > 0)
                        tok_buf.getToken(TokenIndex.fromInt(tok_i - 1)).kind
                    else
                        null;
                    const next_k: ?TokenKind = if (tok_i + 1 < tok_buf.countTokens())
                        tok_buf.getToken(TokenIndex.fromInt(tok_i + 1)).kind
                    else
                        null;
                    if (prev_k == .amp or prev_k == .star or prev_k == .kw_let or prev_k == .kw_var) continue;
                    if (next_k == .ident) {
                        try emitted_mut_tokens.put(collector.allocator, tok_i, {});
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            mut_rec.byte_offset,
                            mut_rec.byte_offset +| mut_rec.byte_len,
                            "var",
                            "UR-22-01: replace retired `mut` pattern binding modifier with `var`",
                        );
                    }
                }
            }
        }
    }
}

/// Collects `UR-22-02` legacy parameter, receiver, standalone type, pattern/loop, and call-site mode rewrites.
fn collectParameterAndCallModeFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    var handled_tokens: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer handled_tokens.deinit(allocator);

    const cst_count = cst_arena.countNodes();
    var cst_i: usize = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const cst_id = CstNodeIndex.fromInt(@intCast(cst_i));
        const rec = cst_arena.getNode(cst_id);

        // [1] Function / method / trait / impl `.fn_param`:
        if (rec.kind == .fn_param) {
            const param_sp = extractCstTokenSpan(cst_arena, tok_buf, cst_id) orelse continue;
            // Advance past any leading `@attr` subtrees inside `.fn_param`:
            var cur_tok_i: u32 = param_sp.first_tok.asInt();
            const sub_end = @min(cst_i + @max(@as(usize, rec.subtree_size), 1), cst_count);
            var sub_cur = cst_i + 1;
            while (sub_cur < sub_end) {
                const sub_id = CstNodeIndex.fromInt(@intCast(sub_cur));
                const sub_rec = cst_arena.getNode(sub_id);
                if (sub_rec.kind == .attribute) {
                    if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |attr_sp| {
                        cur_tok_i = @max(cur_tok_i, attr_sp.last_tok.asInt() + 1);
                    }
                    sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                    continue;
                }
                break;
            }
            if (cur_tok_i > param_sp.last_tok.asInt()) continue;

            // Skip optional `comptime` modifier:
            if (tok_buf.getToken(TokenIndex.fromInt(cur_tok_i)).kind == .kw_comptime) {
                cur_tok_i += 1;
                if (cur_tok_i > param_sp.last_tok.asInt()) continue;
            }

            // Check if this `.fn_param` is a `self` receiver parameter:
            var self_tok_opt: ?u32 = null;
            var scan_self = cur_tok_i;
            while (scan_self <= param_sp.last_tok.asInt()) : (scan_self += 1) {
                const tk = tok_buf.getToken(TokenIndex.fromInt(scan_self)).kind;
                if (tk == .colon or tk == .eq) break;
                if (tk == .kw_self_val) {
                    self_tok_opt = scan_self;
                    break;
                }
            }

            if (self_tok_opt) |self_tok_i| {
                if (self_tok_i > cur_tok_i) {
                    const prefix_start_b = tok_buf.getToken(TokenIndex.fromInt(cur_tok_i)).byte_offset;
                    const self_rec = tok_buf.getToken(TokenIndex.fromInt(self_tok_i));
                    const self_end_b = self_rec.byte_offset +| self_rec.byte_len;
                    if (!hasCommentsInByteRange(source, tok_buf, prefix_start_b, self_end_b)) {
                        const first_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(cur_tok_i));
                        const second_lex = if (cur_tok_i + 1 < self_tok_i)
                            symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(cur_tok_i + 1))
                        else
                            "";

                        var mark_t = cur_tok_i;
                        while (mark_t <= self_tok_i) : (mark_t += 1) {
                            try handled_tokens.put(allocator, mark_t, {});
                        }

                        if ((std.mem.eql(u8, first_lex, "ref") and std.mem.eql(u8, second_lex, "mut")) or
                            (std.mem.eql(u8, first_lex, "&") and std.mem.eql(u8, second_lex, "inout")))
                        {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                prefix_start_b,
                                self_end_b,
                                "&mut self",
                                "UR-22-02: rewrite `ref mut self` receiver to `&mut self`",
                            );
                        } else if (std.mem.eql(u8, first_lex, "var") and std.mem.eql(u8, second_lex, "mut")) {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                prefix_start_b,
                                self_end_b,
                                "var self",
                                "UR-22-02: rewrite `var mut self` receiver to `var self`",
                            );
                        } else if (RETIRED_SELF_MODE_MAP.get(first_lex)) |canon_self| {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                prefix_start_b,
                                self_end_b,
                                canon_self,
                                "UR-22-02: canonicalize `self` receiver mode",
                            );
                        }
                    }
                }
                continue;
            }

            // Standard parameter `[mode] <name> : [ty_mode] <Type> [= default]`:
            var colon_tok_opt: ?u32 = null;
            var depth_p: u32 = 0;
            var scan_c = cur_tok_i;
            while (scan_c <= param_sp.last_tok.asInt()) : (scan_c += 1) {
                const tk = tok_buf.getToken(TokenIndex.fromInt(scan_c)).kind;
                switch (tk) {
                    .lparen, .lbracket, .lbrace => depth_p += 1,
                    .rparen, .rbracket, .rbrace => depth_p -|= 1,
                    .colon => {
                        if (depth_p == 0) {
                            colon_tok_opt = scan_c;
                            break;
                        }
                    },
                    else => {},
                }
            }
            const colon_tok_i = colon_tok_opt orelse continue;
            if (colon_tok_i == 0 or colon_tok_i <= cur_tok_i or colon_tok_i >= param_sp.last_tok.asInt()) {
                // Handle `$id: <ty_mode> $ty` when `colon_tok_i == cur_tok_i + 1`:
                if (colon_tok_i == cur_tok_i + 1 and colon_tok_i + 1 <= param_sp.last_tok.asInt()) {
                    const ty_tok_i = colon_tok_i + 1;
                    const ty_first_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ty_tok_i));
                    const ty_second_lex = if (ty_tok_i + 1 <= param_sp.last_tok.asInt())
                        symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ty_tok_i + 1))
                    else
                        "";
                    const ty_first_rec = tok_buf.getToken(TokenIndex.fromInt(ty_tok_i));
                    if (std.mem.eql(u8, ty_first_lex, "ref") and std.mem.eql(u8, ty_second_lex, "mut") and
                        ty_tok_i + 2 <= param_sp.last_tok.asInt())
                    {
                        const mut_rec = tok_buf.getToken(TokenIndex.fromInt(ty_tok_i + 1));
                        const mut_end = mut_rec.byte_offset +| mut_rec.byte_len;
                        if (!hasCommentsInByteRange(source, tok_buf, ty_first_rec.byte_offset, mut_end)) {
                            try handled_tokens.put(allocator, ty_tok_i, {});
                            try handled_tokens.put(allocator, ty_tok_i + 1, {});
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                ty_first_rec.byte_offset,
                                mut_end,
                                "&mut",
                                "UR-22-02: rewrite `: ref mut T` parameter type to `: &mut T`",
                            );
                        }
                    } else if (ty_tok_i + 1 <= param_sp.last_tok.asInt()) {
                        if (RETIRED_TYPE_MODE_MAP.get(ty_first_lex)) |canon_ty_mode| {
                            if (std.mem.eql(u8, canon_ty_mode, "&")) {
                                const after_ref = tok_buf.getToken(TokenIndex.fromInt(ty_tok_i + 1));
                                if (!hasCommentsInByteRange(source, tok_buf, ty_first_rec.byte_offset, after_ref.byte_offset)) {
                                    try handled_tokens.put(allocator, ty_tok_i, {});
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        ty_first_rec.byte_offset,
                                        after_ref.byte_offset,
                                        "&",
                                        "UR-22-02: rewrite `: ref T` parameter type to `: &T`",
                                    );
                                }
                            } else {
                                try handled_tokens.put(allocator, ty_tok_i, {});
                                try collector.appendSingleEdit(
                                    .syntax_canonicalization,
                                    ty_first_rec.byte_offset,
                                    ty_first_rec.byte_offset +| ty_first_rec.byte_len,
                                    canon_ty_mode,
                                    "UR-22-02: canonicalize retired parameter type mode",
                                );
                            }
                        }
                    }
                }
                continue;
            }

            // Parameter has `[mode_tokens…] <name> : <Type>`:
            const name_tok_i = colon_tok_i - 1;
            const name_rec = tok_buf.getToken(TokenIndex.fromInt(name_tok_i));
            if (name_rec.kind != .ident and name_rec.kind != .underscore) continue;
            if (name_tok_i <= cur_tok_i) continue;

            const mode_first_rec = tok_buf.getToken(TokenIndex.fromInt(cur_tok_i));
            if (hasCommentsInByteRange(source, tok_buf, mode_first_rec.byte_offset, name_rec.byte_offset)) {
                continue;
            }
            const mode_first_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(cur_tok_i));
            const mode_second_lex = if (cur_tok_i + 1 < name_tok_i)
                symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(cur_tok_i + 1))
            else
                "";

            const ty_start_tok_i = colon_tok_i + 1;
            const ty_start_rec = tok_buf.getToken(TokenIndex.fromInt(ty_start_tok_i));
            var mark_p = cur_tok_i;
            while (mark_p < name_tok_i) : (mark_p += 1) {
                try handled_tokens.put(allocator, mark_p, {});
            }

            var new_param_prefix: ?[]const u8 = null;
            var inserted_ty_mode: ?[]const u8 = null;

            if (std.mem.eql(u8, mode_first_lex, "ref") and std.mem.eql(u8, mode_second_lex, "mut")) {
                new_param_prefix = "";
                inserted_ty_mode = if (ty_start_rec.kind == .amp) null else "&mut ";
            } else if (PARAM_MUT_INTRO_SET.has(mode_first_lex) and PARAM_OWN_MODE_SET.has(mode_second_lex)) {
                new_param_prefix = "var ";
                inserted_ty_mode = if (ty_start_rec.kind == .kw_own) null else "own ";
            } else if (PARAM_OWN_MODE_SET.has(mode_first_lex)) {
                new_param_prefix = "";
                inserted_ty_mode = if (ty_start_rec.kind == .kw_own) null else "own ";
            } else if (RETIRED_TYPE_MODE_MAP.get(mode_first_lex)) |canon_lead| {
                new_param_prefix = "";
                if (ty_start_rec.kind != .amp) {
                    inserted_ty_mode = if (std.mem.eql(u8, canon_lead, "&"))
                        "&"
                    else if (std.mem.eql(u8, canon_lead, "&mut"))
                        "&mut "
                    else
                        "&out ";
                }
            } else if (std.mem.eql(u8, mode_first_lex, "mut") or
                (std.mem.eql(u8, mode_first_lex, "var") and std.mem.eql(u8, mode_second_lex, "mut")))
            {
                new_param_prefix = "var ";
                const ty_lead_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ty_start_tok_i));
                if (std.mem.eql(u8, ty_lead_lex, "sink")) {
                    try handled_tokens.put(allocator, ty_start_tok_i, {});
                    try collector.appendDualEdits(
                        .syntax_canonicalization,
                        mode_first_rec.byte_offset,
                        name_rec.byte_offset,
                        "var ",
                        ty_start_rec.byte_offset,
                        ty_start_rec.byte_offset +| ty_start_rec.byte_len,
                        "own",
                        "UR-22-02: rewrite `mut x: sink T` parameter to `var x: own T`",
                    );
                    continue;
                }
            }

            if (new_param_prefix) |param_pref| {
                if (inserted_ty_mode) |ty_pref| {
                    try collector.appendDualEdits(
                        .syntax_canonicalization,
                        mode_first_rec.byte_offset,
                        name_rec.byte_offset,
                        param_pref,
                        ty_start_rec.byte_offset,
                        ty_start_rec.byte_offset,
                        ty_pref,
                        "UR-22-02: canonicalize parameter passing mode",
                    );
                } else {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        mode_first_rec.byte_offset,
                        name_rec.byte_offset,
                        param_pref,
                        "UR-22-02: canonicalize parameter mutability modifier",
                    );
                }
            }
            continue;
        }

        // [2] Standalone `.ref_type` / `.mode_type` (e.g., `fn(ref T)` / `fn(inout T)` / `fn(sink T)` / `fn(set T)`):
        if (rec.kind == .ref_type or rec.kind == .mode_type) {
            const ty_sp = extractCstTokenSpan(cst_arena, tok_buf, cst_id) orelse continue;
            const first_i = ty_sp.first_tok.asInt();
            if (handled_tokens.contains(first_i)) continue;
            const first_rec = tok_buf.getToken(ty_sp.first_tok);
            const first_lex = symbol_resolver.extractTokenSlice(source, tok_buf, ty_sp.first_tok);
            const second_lex = if (first_i + 1 <= ty_sp.last_tok.asInt())
                symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(first_i + 1))
            else
                "";

            if (std.mem.eql(u8, first_lex, "ref") and std.mem.eql(u8, second_lex, "mut") and
                first_i + 2 <= ty_sp.last_tok.asInt())
            {
                const mut_rec = tok_buf.getToken(TokenIndex.fromInt(first_i + 1));
                const mut_end = mut_rec.byte_offset +| mut_rec.byte_len;
                if (!hasCommentsInByteRange(source, tok_buf, first_rec.byte_offset, mut_end)) {
                    try handled_tokens.put(allocator, first_i, {});
                    try handled_tokens.put(allocator, first_i + 1, {});
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        first_rec.byte_offset,
                        mut_end,
                        "&mut",
                        "UR-22-02: rewrite `ref mut T` type to `&mut T`",
                    );
                }
            } else if (first_i + 1 <= ty_sp.last_tok.asInt()) {
                if (RETIRED_TYPE_MODE_MAP.get(first_lex)) |canon_mode| {
                    if (std.mem.eql(u8, canon_mode, "&")) {
                        const next_rec = tok_buf.getToken(TokenIndex.fromInt(first_i + 1));
                        if (!hasCommentsInByteRange(source, tok_buf, first_rec.byte_offset, next_rec.byte_offset)) {
                            try handled_tokens.put(allocator, first_i, {});
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                first_rec.byte_offset,
                                next_rec.byte_offset,
                                "&",
                                "UR-22-02: rewrite `ref T` type to `&T`",
                            );
                        }
                    } else {
                        try handled_tokens.put(allocator, first_i, {});
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            first_rec.byte_offset,
                            first_rec.byte_offset +| first_rec.byte_len,
                            canon_mode,
                            "UR-22-02: canonicalize retired type passing mode",
                        );
                    }
                }
            }
            continue;
        }

        // [3] Pattern & `for_header` `ref mut $id` -> `&mut $id` and `ref $id` -> `&$id`:
        const is_pat_or_for = switch (rec.kind) {
            .ident_pat, .field_pat, .variant_pat, .tuple_pat, .slice_pat, .struct_pat, .for_header => true,
            else => false,
        };
        if (is_pat_or_for) {
            const pat_sp = extractCstTokenSpan(cst_arena, tok_buf, cst_id) orelse continue;
            var tok_i: u32 = pat_sp.first_tok.asInt();
            while (tok_i <= pat_sp.last_tok.asInt()) : (tok_i += 1) {
                if (rec.kind == .for_header and tok_buf.getToken(TokenIndex.fromInt(tok_i)).kind == .kw_in) break;
                if (handled_tokens.contains(tok_i)) continue;
                const t_rec = tok_buf.getToken(TokenIndex.fromInt(tok_i));
                if (t_rec.kind != .ident or !std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(tok_i)), "ref")) {
                    continue;
                }
                if (tok_i + 2 <= pat_sp.last_tok.asInt() and
                    tok_buf.getToken(TokenIndex.fromInt(tok_i + 1)).kind == .kw_mut and
                    tok_buf.getToken(TokenIndex.fromInt(tok_i + 2)).kind == .ident)
                {
                    const mut_rec = tok_buf.getToken(TokenIndex.fromInt(tok_i + 1));
                    const mut_end = mut_rec.byte_offset +| mut_rec.byte_len;
                    if (!hasCommentsInByteRange(source, tok_buf, t_rec.byte_offset, mut_end)) {
                        try handled_tokens.put(allocator, tok_i, {});
                        try handled_tokens.put(allocator, tok_i + 1, {});
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            t_rec.byte_offset,
                            mut_end,
                            "&mut",
                            "UR-22-02: rewrite `ref mut` binding to `&mut`",
                        );
                    }
                    tok_i += 1;
                } else if (tok_i + 1 <= pat_sp.last_tok.asInt() and
                    tok_buf.getToken(TokenIndex.fromInt(tok_i + 1)).kind == .ident)
                {
                    const id_rec = tok_buf.getToken(TokenIndex.fromInt(tok_i + 1));
                    if (!hasCommentsInByteRange(source, tok_buf, t_rec.byte_offset, id_rec.byte_offset)) {
                        try handled_tokens.put(allocator, tok_i, {});
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            t_rec.byte_offset,
                            id_rec.byte_offset,
                            "&",
                            "UR-22-02: rewrite `ref` binding to `&`",
                        );
                    }
                }
            }
            continue;
        }

        // [4] Call-site argument prefixes inside `.call_expr` `( … )` (including `ref (*p)` and `inout (arr[i])`!):
        if (rec.kind == .call_expr) {
            const call_end_node = @min(cst_i + @max(@as(usize, rec.subtree_size), 1), cst_count);
            // Locate the direct `.call_args_start` (`(`) leaf of THIS `.call_expr` (not nested inner calls!):
            var open_paren_tok: TokenIndex = .none;
            var close_paren_tok: TokenIndex = .none;
            var child_c = cst_i + 1;
            while (child_c < call_end_node) {
                const c_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_c)));
                if (c_rec.kind == .call_args_start and !c_rec.token.isNone()) {
                    open_paren_tok = c_rec.token;
                } else if (!open_paren_tok.isNone() and c_rec.subtree_size <= 1 and !c_rec.token.isNone() and
                    tok_buf.getToken(c_rec.token).kind == .rparen)
                {
                    close_paren_tok = c_rec.token;
                }
                child_c += @max(@as(usize, c_rec.subtree_size), 1);
            }
            if (open_paren_tok.isNone() or close_paren_tok.isNone()) continue;
            if (open_paren_tok.asInt() + 1 >= close_paren_tok.asInt()) continue;

            // Walk top-level comma-separated argument starts inside `( … )`:
            var arg_start_i: u32 = open_paren_tok.asInt() + 1;
            var paren_depth: u32 = 0;
            var scan_arg: u32 = arg_start_i;
            while (scan_arg <= close_paren_tok.asInt()) : (scan_arg += 1) {
                const scan_kind = tok_buf.getToken(TokenIndex.fromInt(scan_arg)).kind;
                const is_boundary = paren_depth == 0 and (scan_kind == .comma or scan_arg == close_paren_tok.asInt());
                if (is_boundary) {
                    if (arg_start_i < scan_arg) {
                        var mode_i = arg_start_i;
                        // Skip `label:` on named call arguments:
                        if (mode_i + 2 < scan_arg and
                            tok_buf.getToken(TokenIndex.fromInt(mode_i)).kind == .ident and
                            tok_buf.getToken(TokenIndex.fromInt(mode_i + 1)).kind == .colon)
                        {
                            mode_i += 2;
                        }
                        if (mode_i + 1 < scan_arg and !handled_tokens.contains(mode_i)) {
                            const m0_rec = tok_buf.getToken(TokenIndex.fromInt(mode_i));
                            const m0_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(mode_i));
                            const m1_rec = tok_buf.getToken(TokenIndex.fromInt(mode_i + 1));
                            const m1_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(mode_i + 1));

                            if (m0_rec.kind == .ident and std.mem.eql(u8, m0_lex, "ref") and
                                m1_rec.kind == .kw_mut and mode_i + 2 < scan_arg and
                                isCallArgExprStartToken(tok_buf.getToken(TokenIndex.fromInt(mode_i + 2)).kind))
                            {
                                const mut_end = m1_rec.byte_offset +| m1_rec.byte_len;
                                if (!hasCommentsInByteRange(source, tok_buf, m0_rec.byte_offset, mut_end)) {
                                    try handled_tokens.put(allocator, mode_i, {});
                                    try handled_tokens.put(allocator, mode_i + 1, {});
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        m0_rec.byte_offset,
                                        mut_end,
                                        "&mut",
                                        "UR-22-02: rewrite call-site `ref mut` to `&mut`",
                                    );
                                }
                            } else if (m0_rec.kind == .ident and isCallArgExprStartToken(m1_rec.kind)) {
                                if (RETIRED_TYPE_MODE_MAP.get(m0_lex)) |canon_call_mode| {
                                    if (std.mem.eql(u8, canon_call_mode, "&")) {
                                        if (!hasCommentsInByteRange(source, tok_buf, m0_rec.byte_offset, m1_rec.byte_offset)) {
                                            try handled_tokens.put(allocator, mode_i, {});
                                            try collector.appendSingleEdit(
                                                .syntax_canonicalization,
                                                m0_rec.byte_offset,
                                                m1_rec.byte_offset,
                                                "&",
                                                "UR-22-02: rewrite call-site `ref` to `&`",
                                            );
                                        }
                                    } else if (!std.mem.eql(u8, canon_call_mode, "&out") or !std.mem.eql(u8, m1_lex, "is")) {
                                        try handled_tokens.put(allocator, mode_i, {});
                                        try collector.appendSingleEdit(
                                            .syntax_canonicalization,
                                            m0_rec.byte_offset,
                                            m0_rec.byte_offset +| m0_rec.byte_len,
                                            canon_call_mode,
                                            "UR-22-02: canonicalize retired call-site passing mode",
                                        );
                                    }
                                }
                            }
                        }
                    }
                    arg_start_i = scan_arg + 1;
                    continue;
                }
                switch (scan_kind) {
                    .lparen, .lbracket, .lbrace => paren_depth += 1,
                    .rparen, .rbracket, .rbrace => paren_depth -|= 1,
                    else => {},
                }
            }
        }
    }
}

/// Returns `true` if `kind` is a `CstNodeKind` representing a `Type` expression node.
fn isTypeCstKind(kind: CstNodeKind) bool {
    return switch (kind) {
        .prim_type_node,
        .named_type,
        .ref_type,
        .ptr_type,
        .mode_type,
        .slice_or_array_type,
        .tuple_type,
        .fn_type,
        .optional_type,
        .result_type,
        .refined_type,
        .closure_type,
        .intersect_bound_type,
        .union_bound_type,
        => true,
        else => false,
    };
}

/// Returns `true` if `type_cst` is a slice/array reference `&[T]` or `&mut [T; N]` (`PrimaryType`).
fn isSliceRefCstNode(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    type_cst: CstNodeIndex,
    last_tok: TokenIndex,
) bool {
    const rec = cst_arena.getNode(type_cst);
    if (rec.kind != .ref_type or rec.subtree_size <= 1) return false;
    const cst_end = @min(@as(usize, type_cst.asInt()) + @as(usize, rec.subtree_size), cst_arena.countNodes());
    var check_c: usize = type_cst.asInt() + 1;
    while (check_c < cst_end) {
        const sub_id = CstNodeIndex.fromInt(@intCast(check_c));
        const sub_rec = cst_arena.getNode(sub_id);
        if (isTypeCstKind(sub_rec.kind)) {
            return sub_rec.kind == .slice_or_array_type and tok_buf.getToken(last_tok).kind == .rbracket;
        }
        check_c += @max(@as(usize, sub_rec.subtree_size), 1);
    }
    return false;
}

/// Returns `true` if `type_cst` ends in an unparenthesized `.fn_type`, `.closure_type`, or `any`/`dyn` bound tail.
fn hasCallableTypeTailCst(
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    type_cst: CstNodeIndex,
) bool {
    const sp = extractCstTokenSpan(cst_arena, tok_buf, type_cst) orelse return false;
    const rec = cst_arena.getNode(type_cst);
    if (rec.subtree_size <= 1) return false;
    const first_lex = symbol_resolver.extractTokenSlice(source, tok_buf, sp.first_tok);
    if (rec.kind == .fn_type or rec.kind == .closure_type or CALLABLE_BOUND_HEAD_SET.has(first_lex)) {
        return true;
    }
    return switch (rec.kind) {
        .ptr_type, .ref_type, .mode_type => blk: {
            if (isSliceRefCstNode(cst_arena, tok_buf, type_cst, sp.last_tok)) break :blk false;
            const cst_end = @min(@as(usize, type_cst.asInt()) + @as(usize, rec.subtree_size), cst_arena.countNodes());
            var last_type_child: CstNodeIndex = .none;
            var cursor: usize = @as(usize, type_cst.asInt()) + 1;
            while (cursor < cst_end) {
                const child_id = CstNodeIndex.fromInt(@intCast(cursor));
                const child_rec = cst_arena.getNode(child_id);
                if (isTypeCstKind(child_rec.kind)) last_type_child = child_id;
                cursor += @max(@as(usize, child_rec.subtree_size), 1);
            }
            if (last_type_child.isNone()) break :blk false;
            break :blk hasCallableTypeTailCst(source, cst_arena, tok_buf, last_type_child);
        },
        else => false,
    };
}

/// Recursively renders `type_cst` bottom-up for `UR-22-03`, returning rendered text, intrinsic precedence, and change flag.
fn renderUpgradedTypeCstRecursive(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    type_cst: CstNodeIndex,
    is_option_unshadowed: bool,
    is_result_unshadowed: bool,
) anyerror!struct { text: []u8, prec: TypeRewritePrec, has_callable_tail: bool, has_change: bool } {
    const sp = extractCstTokenSpan(cst_arena, tok_buf, type_cst) orelse {
        return .{
            .text = try allocator.dupe(u8, ""),
            .prec = .tier4_primary,
            .has_callable_tail = false,
            .has_change = false,
        };
    };
    const rec = cst_arena.getNode(type_cst);
    const cst_end = @min(@as(usize, type_cst.asInt()) + @max(@as(usize, rec.subtree_size), 1), cst_arena.countNodes());

    // [1] Check if `type_cst` is a generic `.named_type` instantiating `Option[T]` or `Result[Ok, Err]`:
    if (rec.kind == .named_type and !hasCommentsInByteRange(source, tok_buf, sp.start_byte, sp.end_byte)) {
        var type_args_cst: CstNodeIndex = .none;
        var child_c: usize = type_cst.asInt() + 1;
        while (child_c < cst_end) {
            const sub_id = CstNodeIndex.fromInt(@intCast(child_c));
            const sub_rec = cst_arena.getNode(sub_id);
            if (sub_rec.kind == .type_args) {
                type_args_cst = sub_id;
            }
            child_c += @max(@as(usize, sub_rec.subtree_size), 1);
        }

        if (!type_args_cst.isNone()) {
            const args_sp = extractCstTokenSpan(cst_arena, tok_buf, type_args_cst).?;
            const head_raw = std.mem.trim(u8, source[sp.start_byte..args_sp.start_byte], " \t\r\n");
            const is_opt_name = is_option_unshadowed and CANONICAL_OPTION_HEAD_SET.has(head_raw);
            const is_res_name = is_result_unshadowed and CANONICAL_RESULT_HEAD_SET.has(head_raw);

            if (is_opt_name or is_res_name) {
                var arg_types: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
                defer arg_types.deinit(allocator);
                const args_rec = cst_arena.getNode(type_args_cst);
                const args_end = @min(
                    @as(usize, type_args_cst.asInt()) + @max(@as(usize, args_rec.subtree_size), 1),
                    cst_arena.countNodes(),
                );
                var arg_cur: usize = type_args_cst.asInt() + 1;
                while (arg_cur < args_end) {
                    const arg_id = CstNodeIndex.fromInt(@intCast(arg_cur));
                    const arg_rec = cst_arena.getNode(arg_id);
                    if (isTypeCstKind(arg_rec.kind)) {
                        try arg_types.append(allocator, arg_id);
                        arg_cur += @max(@as(usize, arg_rec.subtree_size), 1);
                    } else {
                        arg_cur += 1;
                    }
                }

                if (is_opt_name and arg_types.items.len == 1) {
                    const inner = try renderUpgradedTypeCstRecursive(
                        allocator,
                        source,
                        cst_arena,
                        tok_buf,
                        arg_types.items[0],
                        is_option_unshadowed,
                        is_result_unshadowed,
                    );
                    defer allocator.free(inner.text);
                    const is_needing_parens = @backingInt(inner.prec) < @backingInt(TypeRewritePrec.tier3_postfix) or
                        inner.has_callable_tail;
                    const out_str = try std.fmt.allocPrint(
                        allocator,
                        "{s}{s}{s}?",
                        .{
                            if (is_needing_parens) "(" else "",
                            inner.text,
                            if (is_needing_parens) ")" else "",
                        },
                    );
                    return .{
                        .text = out_str,
                        .prec = .tier3_postfix,
                        .has_callable_tail = false,
                        .has_change = true,
                    };
                }

                if (is_res_name and arg_types.items.len == 2) {
                    const ok_part = try renderUpgradedTypeCstRecursive(
                        allocator,
                        source,
                        cst_arena,
                        tok_buf,
                        arg_types.items[0],
                        is_option_unshadowed,
                        is_result_unshadowed,
                    );
                    defer allocator.free(ok_part.text);
                    const err_part = try renderUpgradedTypeCstRecursive(
                        allocator,
                        source,
                        cst_arena,
                        tok_buf,
                        arg_types.items[1],
                        is_option_unshadowed,
                        is_result_unshadowed,
                    );
                    defer allocator.free(err_part.text);

                    // `T!E` is non-associative (`tier1_result`), and callable tails (`*fn() -> A`) capture `!E`:
                    const is_ok_parenthesized = @backingInt(ok_part.prec) <= @backingInt(TypeRewritePrec.tier1_result) or
                        ok_part.has_callable_tail;
                    const is_err_parenthesized = @backingInt(err_part.prec) <= @backingInt(TypeRewritePrec.tier1_result) or
                        err_part.has_callable_tail;
                    const out_str = try std.fmt.allocPrint(
                        allocator,
                        "{s}{s}{s}!{s}{s}{s}",
                        .{
                            if (is_ok_parenthesized) "(" else "",
                            ok_part.text,
                            if (is_ok_parenthesized) ")" else "",
                            if (is_err_parenthesized) "(" else "",
                            err_part.text,
                            if (is_err_parenthesized) ")" else "",
                        },
                    );
                    return .{
                        .text = out_str,
                        .prec = .tier1_result,
                        .has_callable_tail = false,
                        .has_change = true,
                    };
                }
            }
        }
    }

    // [2] Classify intrinsic precedence of `type_cst` for parenthesization when nested inside `Option`/`Result`:
    const first_tok_kind = tok_buf.getToken(sp.first_tok).kind;
    const is_slice_ref = isSliceRefCstNode(cst_arena, tok_buf, type_cst, sp.last_tok);

    const intrinsic_prec: TypeRewritePrec = switch (rec.kind) {
        .union_bound_type, .intersect_bound_type, .refined_type => .tier0_open,
        .result_type => .tier1_result,
        .ref_type => if (is_slice_ref) .tier4_primary else .tier2_prefix,
        .mode_type => if (first_tok_kind == .hash_soa) .tier4_primary else .tier2_prefix,
        .optional_type => .tier3_postfix,
        .prim_type_node, .named_type, .ptr_type, .slice_or_array_type, .tuple_type, .fn_type, .closure_type => blk_p: {
            if (first_tok_kind == .tilde) break :blk_p .tier2_prefix;
            break :blk_p .tier4_primary;
        },
        else => .tier4_primary,
    };
    const is_direct_callable_or_dyn = rec.kind == .fn_type or rec.kind == .closure_type or
        CALLABLE_BOUND_HEAD_SET.has(symbol_resolver.extractTokenSlice(source, tok_buf, sp.first_tok));
    const has_unchanged_callable_tail = is_direct_callable_or_dyn or
        hasCallableTypeTailCst(source, cst_arena, tok_buf, type_cst);

    // [3] Recursively inspect direct child type CST nodes and splice any upgraded inner types:
    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    var cursor_b: usize = sp.start_byte;
    var has_any_child_change = false;
    var has_last_child_callable_tail = false;

    var child_idx: usize = type_cst.asInt() + 1;
    while (child_idx < cst_end) {
        const sub_id = CstNodeIndex.fromInt(@intCast(child_idx));
        const sub_rec = cst_arena.getNode(sub_id);
        if (isTypeCstKind(sub_rec.kind)) {
            if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |sub_sp| {
                const sub_res = try renderUpgradedTypeCstRecursive(
                    allocator,
                    source,
                    cst_arena,
                    tok_buf,
                    sub_id,
                    is_option_unshadowed,
                    is_result_unshadowed,
                );
                defer allocator.free(sub_res.text);

                if (sub_res.has_change) {
                    has_any_child_change = true;
                    if (sub_sp.start_byte > cursor_b) {
                        try out_buf.appendSlice(allocator, source[cursor_b..sub_sp.start_byte]);
                    }
                    // Check if `type_cst` requires parens around `sub_res` (`*mut Option[u8]` -> `*mut (u8?)`,
                    // `&Option[[u8; 4]]` -> `&([u8; 4]?)`, `&Result[A, B]` -> `&(A!B)`):
                    const is_already_grouped = rec.kind == .tuple_type or rec.kind == .slice_or_array_type;
                    const required_child_min: TypeRewritePrec = switch (rec.kind) {
                        .ptr_type => .tier4_primary,
                        .ref_type => if (is_slice_ref) .tier0_open else .tier3_postfix,
                        .mode_type => if (first_tok_kind == .hash_soa) .tier4_primary else .tier3_postfix,
                        .optional_type => .tier3_postfix,
                        .result_type => .tier2_prefix,
                        else => .tier0_open,
                    };
                    const trimmed_sub = std.mem.trimStart(u8, sub_res.text, " \t\r\n");
                    const has_leading_inner_lbracket = trimmed_sub.len > 0 and trimmed_sub[0] == '[';
                    const is_wrap_child = !is_already_grouped and
                        (@backingInt(sub_res.prec) < @backingInt(required_child_min) or
                            (rec.kind == .ref_type and !is_slice_ref and has_leading_inner_lbracket) or
                            (rec.kind == .optional_type and sub_res.has_callable_tail) or
                            (rec.kind == .result_type and sub_res.has_callable_tail));
                    if (is_wrap_child) try out_buf.append(allocator, '(');
                    try out_buf.appendSlice(allocator, sub_res.text);
                    if (is_wrap_child) try out_buf.append(allocator, ')');
                    has_last_child_callable_tail = !is_wrap_child and sub_res.has_callable_tail;
                    cursor_b = sub_sp.end_byte;
                } else {
                    has_last_child_callable_tail = sub_res.has_callable_tail;
                }
            }
            child_idx += @max(@as(usize, sub_rec.subtree_size), 1);
        } else {
            child_idx += 1;
        }
    }

    if (!has_any_child_change) {
        out_buf.deinit(allocator);
        return .{
            .text = try allocator.dupe(u8, source[sp.start_byte..sp.end_byte]),
            .prec = intrinsic_prec,
            .has_callable_tail = has_unchanged_callable_tail,
            .has_change = false,
        };
    }

    if (cursor_b < sp.end_byte) {
        try out_buf.appendSlice(allocator, source[cursor_b..sp.end_byte]);
    }
    const has_final_callable_tail = is_direct_callable_or_dyn or switch (rec.kind) {
        .ptr_type, .mode_type => has_last_child_callable_tail,
        .ref_type => !is_slice_ref and has_last_child_callable_tail,
        else => false,
    };
    return .{
        .text = try out_buf.toOwnedSlice(allocator),
        .prec = intrinsic_prec,
        .has_callable_tail = has_final_callable_tail,
        .has_change = true,
    };
}

/// Collects bottom-up `UR-22-03` (`Option[$t]` -> `$t?` and `Result[$ok, $err]` -> `$ok!$err`) rewrites.
fn collectOptionAndResultTypeFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    const is_option_unshadowed = !hasLocalSymbolShadow(source, tok_buf, "Option");
    const is_result_unshadowed = !hasLocalSymbolShadow(source, tok_buf, "Result");
    if (!is_option_unshadowed and !is_result_unshadowed) return;

    const cst_count = cst_arena.countNodes();
    var idx: usize = 0;
    while (idx < cst_count) {
        const cst_id = CstNodeIndex.fromInt(@intCast(idx));
        const rec = cst_arena.getNode(cst_id);
        if (isTypeCstKind(rec.kind)) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |sp| {
                const rendered = try renderUpgradedTypeCstRecursive(
                    allocator,
                    source,
                    cst_arena,
                    tok_buf,
                    cst_id,
                    is_option_unshadowed,
                    is_result_unshadowed,
                );
                defer allocator.free(rendered.text);
                if (rendered.has_change) {
                    try collector.appendSingleEdit(
                        .type_migration,
                        sp.start_byte,
                        sp.end_byte,
                        rendered.text,
                        "UR-22-03: canonicalize `Option[T]` / `Result[Ok, Err]` to `T?` / `Ok!Err`",
                    );
                }
            }
            // Skip entire top-level type subtree since `renderUpgradedTypeCstRecursive` synthesized it bottom-up:
            idx += @max(@as(usize, rec.subtree_size), 1);
        } else {
            idx += 1;
        }
    }
}

/// Strips redundant comment-free `-> unit` from a `.fn_sig` CST node on a `fn` item declaration (`UR-22-04`).
fn tryCollectOmitFnUnitReturnFix(
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    fn_sig_cst: CstNodeIndex,
    collector: *FixCollector,
) !void {
    const sig_rec = cst_arena.getNode(fn_sig_cst);
    const sig_end = @min(@as(usize, fn_sig_cst.asInt()) + @max(@as(usize, sig_rec.subtree_size), 1), cst_arena.countNodes());
    var ret_cst: CstNodeIndex = .none;
    var cur: usize = fn_sig_cst.asInt() + 1;
    while (cur < sig_end) {
        const sub_id = CstNodeIndex.fromInt(@intCast(cur));
        const sub_rec = cst_arena.getNode(sub_id);
        if (sub_rec.kind == .return_type) {
            ret_cst = sub_id;
            break;
        }
        cur += @max(@as(usize, sub_rec.subtree_size), 1);
    }
    if (ret_cst.isNone()) return;

    const ret_sp = extractCstTokenSpan(cst_arena, tok_buf, ret_cst) orelse return;
    if (ret_sp.last_tok.asInt() != ret_sp.first_tok.asInt() + 1) return;
    if (tok_buf.getToken(ret_sp.first_tok).kind != .arrow) return;
    const unit_tok = ret_sp.last_tok;
    const is_omissible_unit = tok_buf.getToken(unit_tok).kind == .prim_type and
        (UNIT_OR_NEVER_PRIM_MAP.get(symbol_resolver.extractTokenSlice(source, tok_buf, unit_tok)) orelse false);
    if (!is_omissible_unit) {
        return;
    }

    var erase_start = ret_sp.start_byte;
    if (ret_sp.first_tok.asInt() > 0) {
        const prev_rec = tok_buf.getToken(TokenIndex.fromInt(ret_sp.first_tok.asInt() - 1));
        const prev_end = prev_rec.byte_offset +| prev_rec.byte_len;
        if (!hasCommentsInByteRange(source, tok_buf, prev_end, ret_sp.end_byte)) {
            erase_start = prev_end;
        }
    }
    if (hasCommentsInByteRange(source, tok_buf, erase_start, ret_sp.end_byte)) return;

    try collector.appendSingleEdit(
        .syntax_canonicalization,
        erase_start,
        ret_sp.end_byte,
        "",
        "UR-22-04: omit redundant `-> unit` return type on `fn` declaration",
    );
}

/// Collects `UR-22-04` (`@$attr($k = $v)` -> `@$attr($k: $v)`, `bit_field`, `enum`, `,` fields, omit `-> unit`) fixes.
fn collectAttrEnumBitfieldAndUnitFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    rewritten_test_fns: *const std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    var idx: usize = 0;
    while (idx < cst_count) : (idx += 1) {
        const cst_id = CstNodeIndex.fromInt(@intCast(idx));
        const rec = cst_arena.getNode(cst_id);
        const sub_end = @min(idx + @max(@as(usize, rec.subtree_size), 1), cst_count);

        // [1] `@$attr($k = $v)` -> `@$attr($k: $v)`:
        if (rec.kind == .attribute) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |attr_sp| {
                var paren_depth: u32 = 0;
                var tok_i: u32 = attr_sp.first_tok.asInt();
                while (tok_i <= attr_sp.last_tok.asInt()) : (tok_i += 1) {
                    const tk = tok_buf.getToken(TokenIndex.fromInt(tok_i)).kind;
                    if (tk == .lparen) {
                        paren_depth += 1;
                        continue;
                    }
                    if (tk == .rparen) {
                        paren_depth -|= 1;
                        continue;
                    }
                    if (paren_depth == 1 and tok_i >= 1 and tok_i + 1 <= attr_sp.last_tok.asInt()) {
                        const prev_k = tok_buf.getToken(TokenIndex.fromInt(tok_i - 1)).kind;
                        const cur_rec = tok_buf.getToken(TokenIndex.fromInt(tok_i));
                        const eq_rec = tok_buf.getToken(TokenIndex.fromInt(tok_i + 1));
                        if ((prev_k == .lparen or prev_k == .comma) and
                            (cur_rec.kind == .ident or cur_rec.kind.isKeyword()) and
                            eq_rec.kind == .eq and
                            !hasCommentsInByteRange(source, tok_buf, cur_rec.byte_offset, eq_rec.byte_offset))
                        {
                            const key_end = cur_rec.byte_offset +| cur_rec.byte_len;
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                key_end,
                                eq_rec.byte_offset +| eq_rec.byte_len,
                                ":",
                                "UR-22-04: replace retired `=` in attribute argument with `:`",
                            );
                        }
                    }
                }
            }
            continue;
        }

        // [2] `type $N = bit_field $U { … } [;]` -> `bit_field $N: $U { … }` (slicing CST + `TokenBuffer`!):
        if (rec.kind == .type_alias_item) {
            const alias_sp = extractCstTokenSpan(cst_arena, tok_buf, cst_id) orelse continue;
            var scan_i: u32 = alias_sp.first_tok.asInt();
            while (scan_i <= alias_sp.last_tok.asInt() and
                tok_buf.getToken(TokenIndex.fromInt(scan_i)).kind != .kw_type) : (scan_i += 1)
            {}
            if (scan_i + 4 <= alias_sp.last_tok.asInt() and
                tok_buf.getToken(TokenIndex.fromInt(scan_i)).kind == .kw_type)
            {
                const type_kw_rec = tok_buf.getToken(TokenIndex.fromInt(scan_i));
                const name_tok = TokenIndex.fromInt(scan_i + 1);
                const eq_tok = TokenIndex.fromInt(scan_i + 2);
                const bf_kw_tok = TokenIndex.fromInt(scan_i + 3);
                if (tok_buf.getToken(name_tok).kind == .type_ident and
                    tok_buf.getToken(eq_tok).kind == .eq and
                    tok_buf.getToken(bf_kw_tok).kind == .kw_bit_field)
                {
                    // Find `{` opening the `bit_field` member block (skipping `where` / `[…]` / `(…)`):
                    var lbrace_tok_opt: ?u32 = null;
                    const maybe_close_tok_i: u32 = if (tok_buf.getToken(alias_sp.last_tok).kind == .semi and
                        alias_sp.last_tok.asInt() > scan_i + 4)
                        alias_sp.last_tok.asInt() - 1
                    else
                        alias_sp.last_tok.asInt();
                    if (tok_buf.getToken(TokenIndex.fromInt(maybe_close_tok_i)).kind == .rbrace) {
                        var rev_depth: u32 = 0;
                        var rev_i: u32 = maybe_close_tok_i;
                        while (rev_i >= scan_i + 4) : (rev_i -= 1) {
                            const rk = tok_buf.getToken(TokenIndex.fromInt(rev_i)).kind;
                            if (rk == .rbrace) {
                                rev_depth += 1;
                            } else if (rk == .lbrace) {
                                rev_depth -|= 1;
                                if (rev_depth == 0) {
                                    lbrace_tok_opt = rev_i;
                                    break;
                                }
                            }
                            if (rev_i == 0) break;
                        }
                    } else {
                        var probe_b: u32 = scan_i + 4;
                        var hdr_brace: u32 = 0;
                        var hdr_bracket: u32 = 0;
                        var hdr_paren: u32 = 0;
                        var is_in_where = false;
                        while (probe_b <= alias_sp.last_tok.asInt()) : (probe_b += 1) {
                            const pk = tok_buf.getToken(TokenIndex.fromInt(probe_b)).kind;
                            if (pk == .kw_where and hdr_brace == 0 and hdr_bracket == 0 and hdr_paren == 0) {
                                is_in_where = true;
                                continue;
                            }
                            if (pk == .lbracket) {
                                hdr_bracket += 1;
                            } else if (pk == .rbracket) {
                                hdr_bracket -|= 1;
                            } else if (pk == .lparen) {
                                hdr_paren += 1;
                            } else if (pk == .rparen) {
                                hdr_paren -|= 1;
                            } else if (pk == .lbrace) {
                                if (!is_in_where and hdr_brace == 0 and hdr_bracket == 0 and hdr_paren == 0) {
                                    lbrace_tok_opt = probe_b;
                                    break;
                                }
                                hdr_brace += 1;
                            } else if (pk == .rbrace) {
                                hdr_brace -|= 1;
                                if (is_in_where and hdr_brace == 0 and hdr_bracket == 0 and hdr_paren == 0) {
                                    is_in_where = false;
                                }
                            }
                        }
                    }
                    if (lbrace_tok_opt) |lbrace_i| {
                        if (lbrace_i > scan_i + 4) {
                            const back_first = tok_buf.getToken(TokenIndex.fromInt(scan_i + 4));
                            const back_last = tok_buf.getToken(TokenIndex.fromInt(lbrace_i - 1));
                            const back_end = back_last.byte_offset +| back_last.byte_len;
                            if (!hasCommentsInByteRange(source, tok_buf, type_kw_rec.byte_offset, back_first.byte_offset)) {
                                const backing_str = std.mem.trim(u8, source[back_first.byte_offset..back_end], " \t\r\n");
                                const name_str = symbol_resolver.extractTokenSlice(source, tok_buf, name_tok);
                                const hdr_repl = try std.fmt.allocPrint(
                                    allocator,
                                    "bit_field {s}: {s}",
                                    .{ name_str, backing_str },
                                );
                                defer allocator.free(hdr_repl);

                                if (tok_buf.getToken(alias_sp.last_tok).kind == .semi) {
                                    const semi_rec = tok_buf.getToken(alias_sp.last_tok);
                                    try collector.appendDualEdits(
                                        .syntax_canonicalization,
                                        type_kw_rec.byte_offset,
                                        back_end,
                                        hdr_repl,
                                        semi_rec.byte_offset,
                                        semi_rec.byte_offset +| semi_rec.byte_len,
                                        "",
                                        "UR-22-04: rewrite `type N = bit_field U { … };` to `bit_field N: U { … }`",
                                    );
                                } else {
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        type_kw_rec.byte_offset,
                                        back_end,
                                        hdr_repl,
                                        "UR-22-04: rewrite `type N = bit_field U { … }` to `bit_field N: U { … }`",
                                    );
                                }

                                // Convert top-level `;` -> `,` member separators inside `{ … }` (preserving `[T; N]`):
                                var brace_depth: u32 = 0;
                                var bracket_depth: u32 = 0;
                                var paren_depth: u32 = 0;
                                var has_seen_body_open = false;
                                var mem_i: u32 = lbrace_i;
                                while (mem_i <= alias_sp.last_tok.asInt()) : (mem_i += 1) {
                                    const m_rec = tok_buf.getToken(TokenIndex.fromInt(mem_i));
                                    switch (m_rec.kind) {
                                        .lbrace => {
                                            brace_depth += 1;
                                            has_seen_body_open = true;
                                        },
                                        .rbrace => {
                                            brace_depth -|= 1;
                                            if (has_seen_body_open and brace_depth == 0) break;
                                        },
                                        .lbracket => bracket_depth += 1,
                                        .rbracket => bracket_depth -|= 1,
                                        .lparen => paren_depth += 1,
                                        .rparen => paren_depth -|= 1,
                                        .semi => {
                                            if (has_seen_body_open and brace_depth == 1 and
                                                bracket_depth == 0 and paren_depth == 0)
                                            {
                                                try collector.appendSingleEdit(
                                                    .syntax_canonicalization,
                                                    m_rec.byte_offset,
                                                    m_rec.byte_offset +| m_rec.byte_len,
                                                    ",",
                                                    "UR-22-04: replace `;` bit_field member separator with `,`",
                                                );
                                            }
                                        },
                                        else => {},
                                    }
                                }
                            }
                        }
                    }
                }
            }
            continue;
        }

        // [3] `bit_field $N($U) { … }` -> `bit_field $N: $U { … }`:
        if (rec.kind == .bit_field_item or rec.kind == .struct_item) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |bf_sp| {
                var scan_bf: u32 = bf_sp.first_tok.asInt();
                while (scan_bf <= bf_sp.last_tok.asInt()) : (scan_bf += 1) {
                    const bf_tk = tok_buf.getToken(TokenIndex.fromInt(scan_bf)).kind;
                    if (bf_tk == .kw_bit_field or bf_tk == .lbrace) break;
                }
                if (scan_bf + 4 <= bf_sp.last_tok.asInt() and
                    tok_buf.getToken(TokenIndex.fromInt(scan_bf)).kind == .kw_bit_field and
                    tok_buf.getToken(TokenIndex.fromInt(scan_bf + 1)).kind == .type_ident and
                    tok_buf.getToken(TokenIndex.fromInt(scan_bf + 2)).kind == .lparen)
                {
                    var rparen_opt: ?u32 = null;
                    var p_i: u32 = scan_bf + 3;
                    while (p_i <= bf_sp.last_tok.asInt()) : (p_i += 1) {
                        if (tok_buf.getToken(TokenIndex.fromInt(p_i)).kind == .rparen) {
                            rparen_opt = p_i;
                            break;
                        }
                    }
                    if (rparen_opt) |rparen_i| {
                        if (rparen_i > scan_bf + 3) {
                            const lp_rec = tok_buf.getToken(TokenIndex.fromInt(scan_bf + 2));
                            const rp_rec = tok_buf.getToken(TokenIndex.fromInt(rparen_i));
                            const inner_start = tok_buf.getToken(TokenIndex.fromInt(scan_bf + 3)).byte_offset;
                            const inner_last_rec = tok_buf.getToken(TokenIndex.fromInt(rparen_i - 1));
                            const inner_end = inner_last_rec.byte_offset +| inner_last_rec.byte_len;
                            const rp_end = rp_rec.byte_offset +| rp_rec.byte_len;
                            if (!hasCommentsInByteRange(source, tok_buf, lp_rec.byte_offset, inner_start) and
                                !hasCommentsInByteRange(source, tok_buf, inner_end, rp_end))
                            {
                                const inner_str = std.mem.trim(u8, source[inner_start..inner_end], " \t\r\n");
                                const colon_repl = try std.fmt.allocPrint(allocator, ": {s}", .{inner_str});
                                defer allocator.free(colon_repl);
                                try collector.appendSingleEdit(
                                    .syntax_canonicalization,
                                    lp_rec.byte_offset,
                                    rp_end,
                                    colon_repl,
                                    "UR-22-04: rewrite `bit_field N(U)` backing syntax to `bit_field N: U`",
                                );
                            }
                        }
                    }
                }
            }
        }

        // [4] `@repr(<IntPrim>) enum $N` -> `enum $N: <IntPrim>` (preserving `@repr(C)` on `@repr(C, u8)`):
        if (rec.kind == .enum_item) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |enum_sp| {
                // Find `enum Name [TypeParams]` and check that `: Backing` is not already present before `where` / `{`:
                var enum_kw_i: u32 = enum_sp.first_tok.asInt();
                while (enum_kw_i <= enum_sp.last_tok.asInt() and
                    tok_buf.getToken(TokenIndex.fromInt(enum_kw_i)).kind != .kw_enum) : (enum_kw_i += 1)
                {}
                if (enum_kw_i + 1 <= enum_sp.last_tok.asInt() and
                    tok_buf.getToken(TokenIndex.fromInt(enum_kw_i + 1)).kind == .type_ident)
                {
                    var insert_after_tok: u32 = enum_kw_i + 1;
                    if (insert_after_tok + 1 <= enum_sp.last_tok.asInt() and
                        tok_buf.getToken(TokenIndex.fromInt(insert_after_tok + 1)).kind == .lbracket)
                    {
                        var br_depth: u32 = 0;
                        var b_i = insert_after_tok + 1;
                        while (b_i <= enum_sp.last_tok.asInt()) : (b_i += 1) {
                            const bk = tok_buf.getToken(TokenIndex.fromInt(b_i)).kind;
                            if (bk == .lbracket) br_depth += 1 else if (bk == .rbracket) {
                                br_depth -|= 1;
                                if (br_depth == 0) {
                                    insert_after_tok = b_i;
                                    break;
                                }
                            }
                        }
                    }
                    const has_existing_backing = insert_after_tok + 1 <= enum_sp.last_tok.asInt() and
                        tok_buf.getToken(TokenIndex.fromInt(insert_after_tok + 1)).kind == .colon;

                    if (!has_existing_backing) {
                        // Scan `.attribute` children inside `enum_item`:
                        var attr_c = idx + 1;
                        while (attr_c < sub_end) {
                            const a_id = CstNodeIndex.fromInt(@intCast(attr_c));
                            const a_rec = cst_arena.getNode(a_id);
                            if (a_rec.kind == .attribute) {
                                if (extractCstTokenSpan(cst_arena, tok_buf, a_id)) |a_sp| {
                                    if (a_sp.first_tok.asInt() + 4 <= a_sp.last_tok.asInt() and
                                        tok_buf.getToken(a_sp.first_tok).kind == .at and
                                        std.mem.eql(
                                            u8,
                                            symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(a_sp.first_tok.asInt() + 1)),
                                            "repr",
                                        ) and
                                        tok_buf.getToken(TokenIndex.fromInt(a_sp.first_tok.asInt() + 2)).kind == .lparen and
                                        tok_buf.getToken(a_sp.last_tok).kind == .rparen)
                                    {
                                        const arg_first = a_sp.first_tok.asInt() + 3;
                                        const arg_last = a_sp.last_tok.asInt() - 1;
                                        const ins_rec = tok_buf.getToken(TokenIndex.fromInt(insert_after_tok));
                                        const ins_byte = ins_rec.byte_offset +| ins_rec.byte_len;

                                        if (arg_first == arg_last) {
                                            const sole_arg = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(arg_first));
                                            if (INT_PRIM_REPR_SET.has(sole_arg)) {
                                                var attr_erase_end: usize = a_sp.end_byte;
                                                while (attr_erase_end < source.len and
                                                    (source[attr_erase_end] == ' ' or source[attr_erase_end] == '\t')) : (attr_erase_end += 1)
                                                {}
                                                if (attr_erase_end < source.len and source[attr_erase_end] == '\r') attr_erase_end += 1;
                                                if (attr_erase_end < source.len and source[attr_erase_end] == '\n') {
                                                    attr_erase_end += 1;
                                                    while (attr_erase_end < source.len and
                                                        (source[attr_erase_end] == ' ' or source[attr_erase_end] == '\t') and
                                                        attr_erase_end < ins_byte) : (attr_erase_end += 1)
                                                    {}
                                                }
                                                const clamped_erase_end: u32 = @intCast(@min(attr_erase_end, ins_byte));
                                                if (!hasCommentsInByteRange(source, tok_buf, a_sp.start_byte, clamped_erase_end)) {
                                                    const backing_ins = try std.fmt.allocPrint(allocator, ": {s}", .{sole_arg});
                                                    defer allocator.free(backing_ins);
                                                    try collector.appendDualEdits(
                                                        .syntax_canonicalization,
                                                        a_sp.start_byte,
                                                        clamped_erase_end,
                                                        "",
                                                        ins_byte,
                                                        ins_byte,
                                                        backing_ins,
                                                        "UR-22-04: migrate `@repr(<IntPrim>) enum` to `enum Name: <IntPrim>`",
                                                    );
                                                    break;
                                                }
                                            }
                                        } else if (arg_first + 2 == arg_last and
                                            tok_buf.getToken(TokenIndex.fromInt(arg_first + 1)).kind == .comma)
                                        {
                                            const a0 = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(arg_first));
                                            const a1 = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(arg_last));
                                            const is_a0_c = C_REPR_ARG_SET.has(a0);
                                            const is_a1_c = C_REPR_ARG_SET.has(a1);
                                            const int_prim_opt: ?[]const u8 = if (is_a0_c and INT_PRIM_REPR_SET.has(a1))
                                                a1
                                            else if (is_a1_c and INT_PRIM_REPR_SET.has(a0))
                                                a0
                                            else
                                                null;
                                            if (int_prim_opt) |int_prim| {
                                                if (!hasCommentsInByteRange(source, tok_buf, a_sp.start_byte, a_sp.end_byte)) {
                                                    const backing_ins = try std.fmt.allocPrint(allocator, ": {s}", .{int_prim});
                                                    defer allocator.free(backing_ins);
                                                    try collector.appendDualEdits(
                                                        .syntax_canonicalization,
                                                        a_sp.start_byte,
                                                        a_sp.end_byte,
                                                        "@repr(C)",
                                                        ins_byte,
                                                        ins_byte,
                                                        backing_ins,
                                                        "UR-22-04: split `@repr(C, <IntPrim>)` onto `@repr(C)` + `enum Name: <IntPrim>`",
                                                    );
                                                    break;
                                                }
                                            }
                                        }
                                    }
                                }
                                attr_c += @max(@as(usize, a_rec.subtree_size), 1);
                            } else {
                                break;
                            }
                        }
                    }
                }
            }
        }

        // [5] `;` -> `,` on `.struct_item`, `.union_item`, `.enum_item`, and `.bit_field_item` members:
        if (rec.kind == .struct_item or rec.kind == .union_item or
            rec.kind == .enum_item or rec.kind == .bit_field_item)
        {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |nom_sp| {
                // Skip header CST subtrees (`.attribute`, `.type_params`, backing `Type`, `.where_clause`) before `{`:
                var start_scan_tok_i: u32 = nom_sp.first_tok.asInt();
                var hdr_c = idx + 1;
                while (hdr_c < sub_end) {
                    const hdr_id = CstNodeIndex.fromInt(@intCast(hdr_c));
                    const hdr_rec = cst_arena.getNode(hdr_id);
                    if (hdr_rec.kind == .attribute or hdr_rec.kind == .visibility_modifier or
                        hdr_rec.kind == .type_params or hdr_rec.kind == .where_clause or
                        isTypeCstKind(hdr_rec.kind))
                    {
                        if (extractCstTokenSpan(cst_arena, tok_buf, hdr_id)) |hdr_sp| {
                            start_scan_tok_i = @max(start_scan_tok_i, hdr_sp.last_tok.asInt() + 1);
                        }
                        hdr_c += @max(@as(usize, hdr_rec.subtree_size), 1);
                        continue;
                    }
                    if (hdr_rec.subtree_size <= 1 and !hdr_rec.token.isNone() and
                        tok_buf.getToken(hdr_rec.token).kind == .lbrace)
                    {
                        start_scan_tok_i = @max(start_scan_tok_i, hdr_rec.token.asInt());
                        break;
                    }
                    if (hdr_rec.kind == .struct_field or hdr_rec.kind == .enum_variant) break;
                    hdr_c += @max(@as(usize, hdr_rec.subtree_size), 1);
                }

                var brace_depth: u32 = 0;
                var bracket_depth: u32 = 0;
                var paren_depth: u32 = 0;
                var where_brace_depth: u32 = 0;
                var is_in_where_clause = false;
                var has_seen_body_open = false;
                var m_tok_i: u32 = start_scan_tok_i;
                while (m_tok_i <= nom_sp.last_tok.asInt()) : (m_tok_i += 1) {
                    const m_rec = tok_buf.getToken(TokenIndex.fromInt(m_tok_i));
                    if (!has_seen_body_open and m_rec.kind == .kw_where and
                        brace_depth == 0 and bracket_depth == 0 and paren_depth == 0)
                    {
                        is_in_where_clause = true;
                        where_brace_depth = 0;
                        continue;
                    }
                    switch (m_rec.kind) {
                        .lbracket => bracket_depth += 1,
                        .rbracket => bracket_depth -|= 1,
                        .lparen => paren_depth += 1,
                        .rparen => paren_depth -|= 1,
                        .lbrace => {
                            if (is_in_where_clause) {
                                if (where_brace_depth == 0 and bracket_depth == 0 and paren_depth == 0) {
                                    // Verify whether this `{` is the final body block ending at `nom_sp.last_tok`:
                                    var look_depth: u32 = 1;
                                    var look_i: u32 = m_tok_i + 1;
                                    while (look_i <= nom_sp.last_tok.asInt() and look_depth > 0) : (look_i += 1) {
                                        const lk = tok_buf.getToken(TokenIndex.fromInt(look_i)).kind;
                                        if (lk == .lbrace) look_depth += 1 else if (lk == .rbrace) look_depth -|= 1;
                                    }
                                    if (look_depth == 0 and look_i > nom_sp.last_tok.asInt()) {
                                        is_in_where_clause = false;
                                        brace_depth = 1;
                                        has_seen_body_open = true;
                                        continue;
                                    }
                                }
                                where_brace_depth += 1;
                            } else {
                                brace_depth += 1;
                                if (bracket_depth == 0 and paren_depth == 0) {
                                    has_seen_body_open = true;
                                }
                            }
                        },
                        .rbrace => {
                            if (is_in_where_clause) {
                                where_brace_depth -|= 1;
                            } else {
                                brace_depth -|= 1;
                                if (has_seen_body_open and brace_depth == 0) break;
                            }
                        },
                        .semi => {
                            if (has_seen_body_open and brace_depth == 1 and
                                bracket_depth == 0 and paren_depth == 0)
                            {
                                try collector.appendSingleEdit(
                                    .syntax_canonicalization,
                                    m_rec.byte_offset,
                                    m_rec.byte_offset +| m_rec.byte_len,
                                    ",",
                                    "UR-22-04: replace retired `;` nominal member separator with `,`",
                                );
                            }
                        },
                        else => {},
                    }
                }
            }
        }

        // [6] Omit comment-free `-> unit` ONLY on `fn` item declarations (NEVER `.fn_type` or `subscript`):
        if ((rec.kind == .fn_item or rec.kind == .trait_member or rec.kind == .impl_member) and
            !rewritten_test_fns.contains(cst_id.asInt()))
        {
            var fn_cur = idx + 1;
            var is_subscript_member = false;
            while (fn_cur < sub_end) {
                const sub_id = CstNodeIndex.fromInt(@intCast(fn_cur));
                const sub_rec = cst_arena.getNode(sub_id);
                if (sub_rec.kind == .subscript_item or sub_rec.kind == .subscript_introducer) {
                    is_subscript_member = true;
                    break;
                }
                if (sub_rec.kind == .fn_sig and !is_subscript_member) {
                    try tryCollectOmitFnUnitReturnFix(source, cst_arena, tok_buf, sub_id, collector);
                    break;
                }
                if (sub_rec.kind == .fn_item) break;
                fn_cur += @max(@as(usize, sub_rec.subtree_size), 1);
            }
        }
    }
}

/// Converts a function identifier (`"test_foo_bar"` or `"foo_bar"`) into a prose `test "foo bar"` title (`UR-22-05`).
fn toProseTestTitle(allocator: std.mem.Allocator, raw_fn_name: []const u8) ![]u8 {
    const stripped = if (raw_fn_name.len > 5 and std.mem.startsWith(u8, raw_fn_name, "test_"))
        raw_fn_name[5..]
    else
        raw_fn_name;
    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);
    for (stripped) |ch_byte| {
        if (ch_byte == '_') {
            if (out.items.len > 0 and out.items[out.items.len - 1] != ' ') {
                try out.append(allocator, ' ');
            }
        } else {
            try out.append(allocator, ch_byte);
        }
    }
    if (out.items.len == 0) {
        try out.appendSlice(allocator, raw_fn_name);
    }
    return out.toOwnedSlice(allocator);
}

/// Collects `UR-22-05` (`*const $ty` -> `*$ty`, `c_void` -> `opaque` + `use` pruning, `extern "c"` -> `"C"`, `@test fn`).
fn collectFfiPointersAndProseTestsFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    rewritten_test_fns: *std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    const is_c_void_unshadowed = !hasLocalSymbolShadow(source, tok_buf, "c_void");
    const cst_count = cst_arena.countNodes();
    const tok_count = tok_buf.countTokens();

    // [1] `extern "c"` -> `extern "C"` and `*const $ty` -> `*$ty`:
    var tok_i: usize = 0;
    while (tok_i < tok_count) : (tok_i += 1) {
        const t_idx = TokenIndex.fromInt(@intCast(tok_i));
        const t_rec = tok_buf.getToken(t_idx);
        if (t_rec.flags.is_synthesized) continue;

        if (t_rec.kind == .kw_extern and tok_i + 1 < tok_count) {
            const abi_tok = TokenIndex.fromInt(@intCast(tok_i + 1));
            const abi_rec = tok_buf.getToken(abi_tok);
            if (abi_rec.kind == .string_lit and std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, abi_tok), "\"c\"")) {
                try collector.appendSingleEdit(
                    .syntax_canonicalization,
                    abi_rec.byte_offset,
                    abi_rec.byte_offset +| abi_rec.byte_len,
                    "\"C\"",
                    "UR-22-05: normalize `extern \"c\"` ABI string to `extern \"C\"`",
                );
            }
        }

        if (t_rec.kind == .star and tok_i + 2 < tok_count) {
            const const_tok = TokenIndex.fromInt(@intCast(tok_i + 1));
            const const_rec = tok_buf.getToken(const_tok);
            const target_rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_i + 2)));
            if (const_rec.kind == .kw_const and
                !hasCommentsInByteRange(source, tok_buf, t_rec.byte_offset, target_rec.byte_offset))
            {
                try collector.appendSingleEdit(
                    .syntax_canonicalization,
                    t_rec.byte_offset,
                    target_rec.byte_offset,
                    "*",
                    "UR-22-05: rewrite `*const T` raw pointer type to `*T`",
                );
            }
        }
    }

    // [2] `c_void` (and `[cx|core|std.]ffi.c_void`) -> `opaque` in type positions + prune unused `use …c_void`:
    if (is_c_void_unshadowed) {
        var use_token_ranges: std.ArrayListUnmanaged(struct { first: u32, last: u32 }) = .empty;
        defer use_token_ranges.deinit(allocator);

        var c_idx: usize = 0;
        while (c_idx < cst_count) : (c_idx += 1) {
            const c_id = CstNodeIndex.fromInt(@intCast(c_idx));
            const c_rec = cst_arena.getNode(c_id);
            if (c_rec.kind != .use_item) continue;
            if (extractCstTokenSpan(cst_arena, tok_buf, c_id)) |u_sp| {
                try use_token_ranges.append(allocator, .{
                    .first = u_sp.first_tok.asInt(),
                    .last = u_sp.last_tok.asInt(),
                });

                // Check if this `.use_item` imports `c_void` (`use cx.ffi.c_void;` or `use cx.ffi.{c_void, c_int};`):
                var has_c_void_in_use = false;
                var has_brace_group = false;
                var lbrace_u: u32 = 0;
                var rbrace_u: u32 = 0;
                var c_void_tok_u: u32 = 0;
                var has_as_alias = false;

                var u_t: u32 = u_sp.first_tok.asInt();
                while (u_t <= u_sp.last_tok.asInt()) : (u_t += 1) {
                    const uk = tok_buf.getToken(TokenIndex.fromInt(u_t)).kind;
                    const u_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(u_t));
                    if (uk == .lbrace) {
                        has_brace_group = true;
                        lbrace_u = u_t;
                    } else if (uk == .rbrace) {
                        rbrace_u = u_t;
                    } else if (std.mem.eql(u8, u_lex, "c_void")) {
                        has_c_void_in_use = true;
                        c_void_tok_u = u_t;
                        if (u_t + 1 <= u_sp.last_tok.asInt() and
                            tok_buf.getToken(TokenIndex.fromInt(u_t + 1)).kind == .kw_as)
                        {
                            has_as_alias = true;
                        }
                    }
                }

                if (has_c_void_in_use and !has_as_alias) {
                    if (!has_brace_group) {
                        var del_end: usize = u_sp.end_byte;
                        while (del_end < source.len and (source[del_end] == ' ' or source[del_end] == '\t')) : (del_end += 1) {}
                        if (del_end < source.len and source[del_end] == '\r') del_end += 1;
                        if (del_end < source.len and source[del_end] == '\n') del_end += 1;
                        if (!hasCommentsInByteRange(source, tok_buf, u_sp.start_byte, @intCast(del_end))) {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                u_sp.start_byte,
                                @intCast(del_end),
                                "",
                                "UR-22-05: prune retired `use …c_void;` import",
                            );
                        }
                    } else if (lbrace_u < c_void_tok_u and c_void_tok_u < rbrace_u) {
                        // Count top-level items inside `{ … }`:
                        var item_count: usize = 1;
                        var b_scan = lbrace_u + 1;
                        while (b_scan < rbrace_u) : (b_scan += 1) {
                            if (tok_buf.getToken(TokenIndex.fromInt(b_scan)).kind == .comma and
                                b_scan + 1 < rbrace_u)
                            {
                                item_count += 1;
                            }
                        }
                        if (item_count <= 1) {
                            var del_end: usize = u_sp.end_byte;
                            while (del_end < source.len and (source[del_end] == ' ' or source[del_end] == '\t')) : (del_end += 1) {}
                            if (del_end < source.len and source[del_end] == '\r') del_end += 1;
                            if (del_end < source.len and source[del_end] == '\n') del_end += 1;
                            if (!hasCommentsInByteRange(source, tok_buf, u_sp.start_byte, @intCast(del_end))) {
                                try collector.appendSingleEdit(
                                    .syntax_canonicalization,
                                    u_sp.start_byte,
                                    @intCast(del_end),
                                    "",
                                    "UR-22-05: prune retired `use …{c_void};` import",
                                );
                            }
                        } else {
                            const cv_rec = tok_buf.getToken(TokenIndex.fromInt(c_void_tok_u));
                            if (c_void_tok_u + 1 < rbrace_u and
                                tok_buf.getToken(TokenIndex.fromInt(c_void_tok_u + 1)).kind == .comma)
                            {
                                const next_item_rec = tok_buf.getToken(TokenIndex.fromInt(c_void_tok_u + 2));
                                if (!hasCommentsInByteRange(source, tok_buf, cv_rec.byte_offset, next_item_rec.byte_offset)) {
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        cv_rec.byte_offset,
                                        next_item_rec.byte_offset,
                                        "",
                                        "UR-22-05: remove retired `c_void` from `use` group",
                                    );
                                }
                            } else if (c_void_tok_u > lbrace_u + 1 and
                                tok_buf.getToken(TokenIndex.fromInt(c_void_tok_u - 1)).kind == .comma)
                            {
                                const prev_comma_rec = tok_buf.getToken(TokenIndex.fromInt(c_void_tok_u - 1));
                                const cv_end = cv_rec.byte_offset +| cv_rec.byte_len;
                                if (!hasCommentsInByteRange(source, tok_buf, prev_comma_rec.byte_offset, cv_end)) {
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        prev_comma_rec.byte_offset,
                                        cv_end,
                                        "",
                                        "UR-22-05: remove retired `c_void` from `use` group",
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }

        // Replace `[cx.|core.|std.][ffi.]c_void` outside `.use_item` in pointer/type positions with `opaque`:
        var scan_cv: u32 = 0;
        while (scan_cv < tok_count) : (scan_cv += 1) {
            const cv_idx = TokenIndex.fromInt(scan_cv);
            const cv_rec = tok_buf.getToken(cv_idx);
            if (cv_rec.kind != .ident or !std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, cv_idx), "c_void")) continue;

            var is_in_use = false;
            for (use_token_ranges.items) |ur| {
                if (scan_cv >= ur.first and scan_cv <= ur.last) {
                    is_in_use = true;
                    break;
                }
            }
            if (is_in_use) continue;

            // Walk backward across `[cx|core|std.]ffi.` path prefix if present:
            var start_tok_i: u32 = scan_cv;
            if (start_tok_i >= 2 and tok_buf.getToken(TokenIndex.fromInt(start_tok_i - 1)).kind == .dot) {
                const prev_seg = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(start_tok_i - 2));
                if (std.mem.eql(u8, prev_seg, "ffi")) {
                    start_tok_i -= 2;
                    if (start_tok_i >= 2 and tok_buf.getToken(TokenIndex.fromInt(start_tok_i - 1)).kind == .dot) {
                        const root_seg = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(start_tok_i - 2));
                        if (STDLIB_ROOT_SEG_SET.has(root_seg)) {
                            start_tok_i -= 2;
                        }
                    }
                }
            }

            // Ensure `c_void` sits in a type or pointer position (`*c_void`, `*mut c_void`, `*const c_void`,
            // `: c_void`, `[c_void]`, `-> c_void`, or `= c_void` on `type`):
            const before_kind: ?TokenKind = if (start_tok_i > 0)
                tok_buf.getToken(TokenIndex.fromInt(start_tok_i - 1)).kind
            else
                null;
            const is_type_pos = if (before_kind) |bk| switch (bk) {
                .star, .kw_mut, .kw_const, .colon, .arrow, .lbracket, .comma, .kw_as, .eq => true,
                else => false,
            } else false;
            if (is_type_pos) {
                const start_rec = tok_buf.getToken(TokenIndex.fromInt(start_tok_i));
                const cv_end = cv_rec.byte_offset +| cv_rec.byte_len;
                if (!hasCommentsInByteRange(source, tok_buf, start_rec.byte_offset, cv_end)) {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        start_rec.byte_offset,
                        cv_end,
                        "opaque",
                        "UR-22-05: replace retired `c_void` target with `opaque`",
                    );
                }
            }
        }
    }

    // [3] Parameterless `@test [async] [pub] fn test_foo_bar() [-> unit] { … }` -> `[async] test "foo bar" { … }`:
    var fn_idx: usize = 0;
    while (fn_idx < cst_count) : (fn_idx += 1) {
        const fn_cst = CstNodeIndex.fromInt(@intCast(fn_idx));
        const fn_rec = cst_arena.getNode(fn_cst);
        if (fn_rec.kind != .fn_item) continue;
        const fn_end_node = @min(fn_idx + @max(@as(usize, fn_rec.subtree_size), 1), cst_count);

        var test_attr_cst: CstNodeIndex = .none;
        var has_sibling_after_test_attr = false;
        var fn_sig_cst: CstNodeIndex = .none;
        var body_block_cst: CstNodeIndex = .none;
        var has_forbidden_fn_mod = false;
        var is_async_fn = false;

        var sub_i = fn_idx + 1;
        while (sub_i < fn_end_node) {
            const sub_id = CstNodeIndex.fromInt(@intCast(sub_i));
            const sub_rec = cst_arena.getNode(sub_id);
            if (sub_rec.kind == .attribute) {
                if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |a_sp| {
                    if (a_sp.last_tok.asInt() == a_sp.first_tok.asInt() + 1 and
                        tok_buf.getToken(a_sp.first_tok).kind == .at and
                        std.mem.eql(
                            u8,
                            symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(a_sp.first_tok.asInt() + 1)),
                            "test",
                        ))
                    {
                        test_attr_cst = sub_id;
                    } else if (!test_attr_cst.isNone()) {
                        has_sibling_after_test_attr = true;
                    }
                }
                sub_i += @max(@as(usize, sub_rec.subtree_size), 1);
                continue;
            }
            if (sub_rec.kind == .fn_sig) {
                fn_sig_cst = sub_id;
                sub_i += @max(@as(usize, sub_rec.subtree_size), 1);
                continue;
            }
            if (sub_rec.kind == .block) {
                body_block_cst = sub_id;
                break;
            }
            if (sub_rec.subtree_size <= 1 and !sub_rec.token.isNone()) {
                const tk = tok_buf.getToken(sub_rec.token).kind;
                if (tk == .kw_async) is_async_fn = true;
                if (tk == .kw_unsafe or tk == .kw_extern or tk == .kw_comptime) has_forbidden_fn_mod = true;
            }
            sub_i += @max(@as(usize, sub_rec.subtree_size), 1);
        }

        if (test_attr_cst.isNone() or fn_sig_cst.isNone() or body_block_cst.isNone() or has_forbidden_fn_mod) {
            continue;
        }

        // Verify `fn_sig` has zero generic params, zero `fn_param`s, zero `where_clause`, and extract `fn_name`:
        const sig_rec = cst_arena.getNode(fn_sig_cst);
        const sig_end = @min(@as(usize, fn_sig_cst.asInt()) + @max(@as(usize, sig_rec.subtree_size), 1), cst_count);
        var has_type_params_or_where = false;
        var has_any_param = false;
        var ret_cst: CstNodeIndex = .none;
        var sig_c: usize = fn_sig_cst.asInt() + 1;
        while (sig_c < sig_end) {
            const sc_id = CstNodeIndex.fromInt(@intCast(sig_c));
            const sc_rec = cst_arena.getNode(sc_id);
            if (sc_rec.kind == .type_params or sc_rec.kind == .where_clause) {
                has_type_params_or_where = true;
                break;
            }
            if (sc_rec.kind == .param_list) {
                const pl_end = @min(sig_c + @max(@as(usize, sc_rec.subtree_size), 1), sig_end);
                var pl_c = sig_c + 1;
                while (pl_c < pl_end) : (pl_c += 1) {
                    const pk = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(pl_c))).kind;
                    if (pk == .fn_param or pk == .variadic_param) {
                        has_any_param = true;
                        break;
                    }
                }
            } else if (sc_rec.kind == .return_type) {
                ret_cst = sc_id;
            }
            sig_c += @max(@as(usize, sc_rec.subtree_size), 1);
        }
        if (has_type_params_or_where or has_any_param) continue;

        const sig_sp = extractCstTokenSpan(cst_arena, tok_buf, fn_sig_cst) orelse continue;
        const body_sp = extractCstTokenSpan(cst_arena, tok_buf, body_block_cst) orelse continue;
        const test_attr_sp = extractCstTokenSpan(cst_arena, tok_buf, test_attr_cst) orelse continue;
        const fn_name = symbol_resolver.extractTokenSlice(source, tok_buf, sig_sp.first_tok);
        if (fn_name.len == 0 or tok_buf.getToken(sig_sp.first_tok).kind != .ident) continue;

        // Locate start of `[pub…] [async] fn` modifiers after all attributes on `fn_item`:
        const fn_sp = extractCstTokenSpan(cst_arena, tok_buf, fn_cst) orelse continue;
        var mod_start_tok_i: u32 = fn_sp.first_tok.asInt();
        var attr_walk = fn_idx + 1;
        while (attr_walk < fn_end_node) {
            const aw_id = CstNodeIndex.fromInt(@intCast(attr_walk));
            const aw_rec = cst_arena.getNode(aw_id);
            if (aw_rec.kind == .attribute) {
                if (extractCstTokenSpan(cst_arena, tok_buf, aw_id)) |aw_sp| {
                    mod_start_tok_i = @max(mod_start_tok_i, aw_sp.last_tok.asInt() + 1);
                }
                attr_walk += @max(@as(usize, aw_rec.subtree_size), 1);
            } else {
                break;
            }
        }
        if (mod_start_tok_i > sig_sp.last_tok.asInt()) continue;
        const mod_start_byte = tok_buf.getToken(TokenIndex.fromInt(mod_start_tok_i)).byte_offset;

        // Preserve non-`unit` return type (`-> unit!IoError`) if present; strip `-> unit`:
        var kept_ret_slice: []const u8 = "";
        if (!ret_cst.isNone()) {
            if (extractCstTokenSpan(cst_arena, tok_buf, ret_cst)) |r_sp| {
                const is_unit_ret = r_sp.last_tok.asInt() == r_sp.first_tok.asInt() + 1 and
                    tok_buf.getToken(r_sp.last_tok).kind == .prim_type and
                    (UNIT_OR_NEVER_PRIM_MAP.get(
                        symbol_resolver.extractTokenSlice(source, tok_buf, r_sp.last_tok),
                    ) orelse false);
                if (!is_unit_ret) {
                    kept_ret_slice = std.mem.trim(u8, source[r_sp.start_byte..r_sp.end_byte], " \t\r\n");
                }
            }
        }

        const prose_title = try toProseTestTitle(allocator, fn_name);
        defer allocator.free(prose_title);
        var header_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer header_buf.deinit(allocator);
        if (is_async_fn) try header_buf.appendSlice(allocator, "async ");
        try header_buf.appendSlice(allocator, "test ");
        try pkg_manifest.appendEscapedTomlBasicString(&header_buf, allocator, prose_title);
        if (kept_ret_slice.len > 0) {
            try header_buf.append(allocator, ' ');
            try header_buf.appendSlice(allocator, kept_ret_slice);
        }
        try header_buf.append(allocator, ' ');

        if (!has_sibling_after_test_attr and
            !hasCommentsInByteRange(source, tok_buf, test_attr_sp.start_byte, body_sp.start_byte))
        {
            try rewritten_test_fns.put(allocator, fn_cst.asInt(), {});
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                test_attr_sp.start_byte,
                body_sp.start_byte,
                header_buf.items,
                "UR-22-05: rewrite parameterless `@test fn` to `test \"…\"` declaration",
            );
        } else if (!hasCommentsInByteRange(source, tok_buf, mod_start_byte, body_sp.start_byte)) {
            var attr_del_end: usize = test_attr_sp.end_byte;
            while (attr_del_end < mod_start_byte and
                (source[attr_del_end] == ' ' or source[attr_del_end] == '\t')) : (attr_del_end += 1)
            {}
            if (attr_del_end < mod_start_byte and source[attr_del_end] == '\r') attr_del_end += 1;
            if (attr_del_end < mod_start_byte and source[attr_del_end] == '\n') attr_del_end += 1;
            const clamped_attr_del_end: u32 = @intCast(@min(attr_del_end, mod_start_byte));
            if (!hasCommentsInByteRange(source, tok_buf, test_attr_sp.start_byte, clamped_attr_del_end)) {
                try rewritten_test_fns.put(allocator, fn_cst.asInt(), {});
                try collector.appendDualEdits(
                    .syntax_canonicalization,
                    test_attr_sp.start_byte,
                    clamped_attr_del_end,
                    "",
                    mod_start_byte,
                    body_sp.start_byte,
                    header_buf.items,
                    "UR-22-05: rewrite parameterless `@test fn` to `test \"…\"` preserving sibling attributes",
                );
            }
        }
    }
}

/// Collects all enabled Sub-stage B Tier 2 lossless CST/AST structural rewrites into `collector`.
fn collectSubstageBTier2Fixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    options: UpgradeOptions,
    collector: *FixCollector,
) !void {
    const is_ur21_01 = isRuleEnabled(options.rule_mask, .ur_21_01_if_let_to_is_condition);
    const is_ur21_02 = isRuleEnabled(options.rule_mask, .ur_21_02_while_let_to_is_condition);
    const is_ur21_03 = isRuleEnabled(options.rule_mask, .ur_21_03_let_some_else_to_orelse);
    const is_ur22_01 = isRuleEnabled(options.rule_mask, .ur_22_01_logical_or_and_var_bindings);
    const is_ur22_02 = isRuleEnabled(options.rule_mask, .ur_22_02_parameter_and_ownership_modes);
    const is_ur22_03 = isRuleEnabled(options.rule_mask, .ur_22_03_postfix_option_and_infix_result);
    const is_ur22_04 = isRuleEnabled(options.rule_mask, .ur_22_04_attributes_enums_and_bitfields);
    const is_ur22_05 = isRuleEnabled(options.rule_mask, .ur_22_05_ffi_pointers_and_prose_tests);

    if (!is_ur21_01 and !is_ur21_02 and !is_ur21_03 and !is_ur22_01 and
        !is_ur22_02 and !is_ur22_03 and !is_ur22_04 and !is_ur22_05)
    {
        return;
    }

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var parse_sink = DiagnosticSink.init(allocator);
    defer parse_sink.deinit();

    _ = try parser.parseSource(source, file_id, &tok_buf, &cst_arena, &ast_arena, &parse_sink, collector.interner);

    var rewritten_stmt_nodes: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer rewritten_stmt_nodes.deinit(allocator);
    var rewritten_test_fns: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer rewritten_test_fns.deinit(allocator);

    if (is_ur21_01 or is_ur21_02) {
        try collectIfWhileLetFixes(
            allocator,
            source,
            &cst_arena,
            &tok_buf,
            is_ur21_01,
            is_ur21_02,
            is_ur22_01,
            collector,
        );
    }
    if (is_ur21_03) {
        try collectLetSomeElseToOrelseFixes(
            allocator,
            source,
            &cst_arena,
            &tok_buf,
            &rewritten_stmt_nodes,
            collector,
        );
    }
    if (is_ur22_01) {
        try collectLogicalOrAndVarFixes(
            source,
            &cst_arena,
            &ast_arena,
            &tok_buf,
            &rewritten_stmt_nodes,
            collector,
        );
    }
    if (is_ur22_02) {
        try collectParameterAndCallModeFixes(allocator, source, &cst_arena, &tok_buf, collector);
    }
    if (is_ur22_03) {
        try collectOptionAndResultTypeFixes(allocator, source, &cst_arena, &tok_buf, collector);
    }
    if (is_ur22_05) {
        try collectFfiPointersAndProseTestsFixes(
            allocator,
            source,
            &cst_arena,
            &tok_buf,
            &rewritten_test_fns,
            collector,
        );
    }
    if (is_ur22_04) {
        try collectAttrEnumBitfieldAndUnitFixes(
            allocator,
            source,
            &cst_arena,
            &tok_buf,
            &rewritten_test_fns,
            collector,
        );
    }
}

// ---------------- Tier 3 Semantic Modernizers -----------------

/// Builds a dense `NodeIndex -> parent NodeIndex` table across `ast_arena` in $O(N)$ time.
fn computeAstParentMap(allocator: std.mem.Allocator, ast_arena: *const AstArena) ![]NodeIndex {
    const node_count = ast_arena.countNodes();
    const parents = try allocator.alloc(NodeIndex, node_count);
    errdefer allocator.free(parents);
    @memset(parents, .none);
    if (node_count == 0) return parents;

    const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
    defer allocator.free(extra_ends);

    var i: usize = 0;
    while (i < node_count) : (i += 1) {
        const parent_id = NodeIndex.fromInt(@intCast(i));
        const node = ast_arena.getNode(parent_id);

        if (node.lhs.tag == .node) {
            const child_idx = node.lhs.payload;
            if (child_idx < node_count and child_idx != i) {
                parents[child_idx] = parent_id;
            }
        }
        if (node.rhs.tag == .node) {
            const child_idx = node.rhs.payload;
            if (child_idx < node_count and child_idx != i) {
                parents[child_idx] = parent_id;
            }
        }

        // Walk `extra_data` child node lists on calls, blocks, tuples, arrays, and control flow:
        const has_extra_children = switch (node.tag) {
            .root,
            .block,
            .call_expr,
            .generic_call,
            .method_call,
            .index_expr,
            .tuple_lit,
            .array_lit,
            .struct_lit,
            .if_expr,
            .match_expr,
            .for_stmt,
            .while_stmt,
            .local_var_decl,
            .walrus_expr,
            .with_expr,
            => true,
            else => false,
        };
        if (has_extra_children and (node.lhs.tag == .extra or node.rhs.tag == .extra)) {
            const start_e: usize = if (node.lhs.tag == .extra) node.lhs.payload else node.rhs.payload;
            const end_e: usize = @min(@as(usize, extra_ends[i]), ast_arena.extra_data.items.len);
            var cur_e = start_e;
            if (node.tag == .method_call and cur_e < end_e) {
                // Slot 0 of `.method_call` is `member_tok` (`TokenIndex`), NOT an AST `NodeIndex`:
                cur_e += 1;
            }
            while (cur_e < end_e) : (cur_e += 1) {
                const raw_word = ast_arena.extra_data.items[cur_e];
                if (raw_word > 0 and raw_word < node_count and raw_word != i) {
                    if (parents[raw_word].isNone()) {
                        parents[raw_word] = parent_id;
                    }
                }
            }
        }
    }
    return parents;
}

/// Unwraps `.ref_ty` and `.mut_ref_ty` layers on `raw_ty` in `type_pool`.
fn unwrapAutoDerefType(type_pool: *const InternPool, raw_ty: TypeId) TypeId {
    var current = raw_ty;
    var depth: u8 = 0;
    while (!current.isNone() and !current.isError() and depth < 16) : (depth += 1) {
        const node = type_pool.getNode(current);
        if (node.tag == .ref_ty or node.tag == .mut_ref_ty) {
            current = TypeId.fromInt(node.lhs);
        } else {
            break;
        }
    }
    return current;
}

/// Looks up the resolved `TypeId` of `ast_node` across file-level and per-`DefId` `BodySemanticSideTables`.
fn lookupSemanticNodeType(
    db: *CompilerDb,
    file_id: FileId,
    item_tree: *const ItemTree,
    ast_node: NodeIndex,
) !TypeId {
    if (ast_node.isNone()) return .err_ty;
    if (db.getFileSideTables(file_id)) |file_st| {
        const file_ty = file_st.getNodeType(ast_node);
        if (!file_ty.isError()) return file_ty;
    }
    for (item_tree.entries) |entry| {
        if (try db.getDefSideTables(entry.def_id)) |def_st| {
            if (ast_node.asInt() >= def_st.ast_start and ast_node.asInt() < def_st.ast_end) {
                const def_ty = def_st.getNodeType(ast_node);
                if (!def_ty.isError()) return def_ty;
            }
        }
    }
    return .err_ty;
}

/// Looks up the resolved `SymbolIndex` of `ast_node` across file-level and per-`DefId` `BodySemanticSideTables`.
fn lookupSemanticNodeSymbol(
    db: *CompilerDb,
    file_id: FileId,
    item_tree: *const ItemTree,
    ast_node: NodeIndex,
) !SymbolIndex {
    if (ast_node.isNone()) return .none;
    if (db.getFileSideTables(file_id)) |file_st| {
        if (ast_node.asInt() >= file_st.ast_start and ast_node.asInt() < file_st.ast_end) {
            const rel = ast_node.asInt() - file_st.ast_start;
            if (rel < file_st.node_symbols.len and !file_st.node_symbols[rel].isNone()) {
                return file_st.node_symbols[rel];
            }
        }
    }
    for (item_tree.entries) |entry| {
        if (try db.getDefSideTables(entry.def_id)) |def_st| {
            if (ast_node.asInt() >= def_st.ast_start and ast_node.asInt() < def_st.ast_end) {
                const rel = ast_node.asInt() - def_st.ast_start;
                if (rel < def_st.node_symbols.len and !def_st.node_symbols[rel].isNone()) {
                    return def_st.node_symbols[rel];
                }
            }
        }
    }
    return .none;
}

/// Looks up the verified `@fix_inline` rewrite of `ast_node` across file-level and per-`DefId` `BodySemanticSideTables`.
fn lookupFixInlineRewrite(
    db: *CompilerDb,
    file_id: FileId,
    item_tree: *const ItemTree,
    ast_node: NodeIndex,
) !?type_system.FixInlineNodeRewrite {
    if (ast_node.isNone()) return null;
    if (db.getFileSideTables(file_id)) |file_st| {
        if (file_st.getFixInlineRewrite(ast_node)) |rw| return rw;
    }
    for (item_tree.entries) |entry| {
        if (try db.getDefSideTables(entry.def_id)) |def_st| {
            if (def_st.getFixInlineRewrite(ast_node)) |rw| return rw;
        }
    }
    return null;
}

/// Looks up the `CallArgMapping` of `call_node` across file-level and per-`DefId` `BodySemanticSideTables`.
fn lookupCallArgMapping(
    db: *CompilerDb,
    file_id: FileId,
    item_tree: *const ItemTree,
    call_node: NodeIndex,
) !?type_system.CallArgMapping {
    if (call_node.isNone()) return null;
    if (db.getFileSideTables(file_id)) |file_st| {
        if (file_st.getCallArgMapping(call_node)) |mapping| return mapping;
    }
    for (item_tree.entries) |entry| {
        if (try db.getDefSideTables(entry.def_id)) |def_st| {
            if (def_st.getCallArgMapping(call_node)) |mapping| return mapping;
        }
    }
    return null;
}

/// Follows `.use_alias_sym` indirections in `sym_table` to reach the underlying target `SymbolIndex`.
fn chaseUseAliasSymbol(sym_table: *const symbol_resolver.SymbolTable, start_sym: SymbolIndex) SymbolIndex {
    var cur = start_sym;
    var hops: u8 = 0;
    while (!cur.isNone() and cur.asInt() < sym_table.countSymbols() and hops < 16) : (hops += 1) {
        const rec = sym_table.getSymbol(cur).*;
        if (rec.kind == .use_alias_sym and !rec.target_symbol.isNone()) {
            cur = rec.target_symbol;
        } else {
            break;
        }
    }
    return cur;
}

/// Returns `true` if `expr_node` is a side-effect-free pure place (`ident_expr`, `self_val`, or `.field_access` chain).
fn isPurePlaceAstExpr(ast_arena: *const AstArena, expr_node: NodeIndex) bool {
    var cur = expr_node;
    var depth: u8 = 0;
    while (!cur.isNone() and cur.asInt() < ast_arena.countNodes() and depth < 32) : (depth += 1) {
        const node = ast_arena.getNode(cur);
        switch (node.tag) {
            .ident_expr, .self_val, .path_expr => return true,
            .field_access => {
                if (node.lhs.tag != .node) return false;
                cur = NodeIndex.fromInt(node.lhs.payload);
            },
            else => return false,
        }
    }
    return false;
}

/// Returns `true` if `first_sp` and `second_sp` span identical non-synthesized token lexeme sequences.
fn hasIdenticalTokenLexemes(
    source: []const u8,
    tok_buf: *const TokenBuffer,
    first_sp: CstTokenSpan,
    second_sp: CstTokenSpan,
) bool {
    const count_a = first_sp.last_tok.asInt() - first_sp.first_tok.asInt() + 1;
    const count_b = second_sp.last_tok.asInt() - second_sp.first_tok.asInt() + 1;
    if (count_a != count_b) return false;
    var offset: u32 = 0;
    while (offset < count_a) : (offset += 1) {
        const tok_a = TokenIndex.fromInt(first_sp.first_tok.asInt() + offset);
        const tok_b = TokenIndex.fromInt(second_sp.first_tok.asInt() + offset);
        if (tok_buf.getToken(tok_a).kind != tok_buf.getToken(tok_b).kind) return false;
        if (!std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, tok_a), symbol_resolver.extractTokenSlice(source, tok_buf, tok_b))) {
            return false;
        }
    }
    return true;
}

/// Checks whether the CST subtree of `closure_body_cst` contains any non-nested `return` token (`UR-21-06` guard).
fn hasNonNestedReturnInClosureBody(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    closure_body_cst: CstNodeIndex,
) bool {
    if (closure_body_cst.isNone() or closure_body_cst.asInt() >= cst_arena.countNodes()) return false;
    const start_idx: usize = closure_body_cst.asInt();
    const rec = cst_arena.getNode(closure_body_cst);
    const end_idx: usize = @min(start_idx + @max(@as(usize, rec.subtree_size), 1), cst_arena.countNodes());

    var cur = start_idx;
    while (cur < end_idx) {
        const node_id = CstNodeIndex.fromInt(@intCast(cur));
        const node_rec = cst_arena.getNode(node_id);
        // Do not descend into nested closures or nested `fn` items that own their own return frame:
        if (cur != start_idx and (node_rec.kind == .closure_expr or node_rec.kind == .fn_item)) {
            cur += @max(@as(usize, node_rec.subtree_size), 1);
            continue;
        }
        if (node_rec.kind == .return_stmt or node_rec.kind == .return_introducer) return true;
        if (node_rec.subtree_size <= 1 and !node_rec.token.isNone() and
            tok_buf.getToken(node_rec.token).kind == .kw_return)
        {
            return true;
        }
        cur += 1;
    }
    return false;
}

/// Checks whether a `.ptr` field access on a mutable slice/array is coerced to or consumed as `*mut T` (`UR-22-06`).
fn isPtrAccessCoercedToMutRawPtr(
    db: *CompilerDb,
    file_id: FileId,
    item_tree: *const ItemTree,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    ast_parents: []const NodeIndex,
    extra_ends: []const u32,
    expr_id: NodeIndex,
) !bool {
    if (expr_id.isNone() or expr_id.asInt() >= ast_parents.len) return false;
    const parent_id = ast_parents[expr_id.asInt()];
    if (parent_id.isNone() or parent_id.asInt() >= ast_arena.countNodes()) return false;
    const parent_node = ast_arena.getNode(parent_id);

    switch (parent_node.tag) {
        .local_var_decl => {
            // Inspect `let/var p: *mut T = buf.ptr;` explicit `: *mut` annotation in CST:
            if (extractCstTokenSpan(cst_arena, tok_buf, ast_arena.getCstOrigin(parent_id))) |decl_sp| {
                var scan_t: u32 = decl_sp.first_tok.asInt();
                while (scan_t + 1 <= decl_sp.last_tok.asInt()) : (scan_t += 1) {
                    const tk = tok_buf.getToken(TokenIndex.fromInt(scan_t)).kind;
                    if (tk == .eq) break;
                    if (tk == .star and tok_buf.getToken(TokenIndex.fromInt(scan_t + 1)).kind == .kw_mut) {
                        return true;
                    }
                }
            }
            return false;
        },
        .cast_expr => {
            if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, parent_id)) |cast_sp| {
                return std.mem.indexOf(u8, source[cast_sp.start_byte..cast_sp.end_byte], "*mut") != null;
            }
            return false;
        },
        .assign_stmt => {
            if (parent_node.lhs.tag == .node) {
                const lhs_ty = try lookupSemanticNodeType(
                    db,
                    file_id,
                    item_tree,
                    NodeIndex.fromInt(parent_node.lhs.payload),
                );
                const lhs_type_node = db.type_pool.getNode(lhs_ty);
                if (lhs_type_node.tag == .raw_ptr_ty and lhs_type_node.rhs != 0) return true;
            }
            return false;
        },
        .deref_expr, .unary_expr => {
            // Mutated directly through `(buf.ptr).* = …` or `*buf.ptr = …`:
            const grand_id = ast_parents[parent_id.asInt()];
            if (!grand_id.isNone() and ast_arena.getNode(grand_id).tag == .assign_stmt) {
                const assign_n = ast_arena.getNode(grand_id);
                if (assign_n.lhs.tag == .node and assign_n.lhs.payload == parent_id.asInt()) return true;
            }
            return false;
        },
        .return_stmt => {
            // Check enclosing `DefId` signature return type for `*mut T`:
            for (item_tree.entries) |entry| {
                if (try db.getDefSideTables(entry.def_id)) |def_st| {
                    if (expr_id.asInt() >= def_st.ast_start and expr_id.asInt() < def_st.ast_end) {
                        if (db.symbol_table.def_to_symbol.get(entry.def_id.asInt())) |fn_sym_idx| {
                            const fn_ty = db.symbol_table.getSymbol(fn_sym_idx).type_id;
                            if (db.type_pool.getFnSignatureView(fn_ty)) |sig_v| {
                                const ret_node = db.type_pool.getNode(sig_v.ret_ty);
                                if (ret_node.tag == .raw_ptr_ty and ret_node.rhs != 0) return true;
                            }
                        }
                        break;
                    }
                }
            }
            return false;
        },
        .named_arg, .call_expr, .generic_call, .method_call => {
            var call_id = parent_id;
            var call_node = parent_node;
            var arg_carrier_id = expr_id;
            if (call_node.tag == .named_arg) {
                if (call_id.asInt() >= ast_parents.len) return false;
                arg_carrier_id = call_id;
                call_id = ast_parents[call_id.asInt()];
                if (call_id.isNone() or call_id.asInt() >= ast_arena.countNodes()) return false;
                call_node = ast_arena.getNode(call_id);
                if (call_node.tag != .call_expr and
                    call_node.tag != .generic_call and
                    call_node.tag != .method_call)
                {
                    return false;
                }
            }

            const maybe_mapping = try lookupCallArgMapping(db, file_id, item_tree, call_id);
            const raw_callee_sym = if (maybe_mapping) |mapping|
                (if (!mapping.callee_sym.isNone())
                    mapping.callee_sym
                else
                    try lookupSemanticNodeSymbol(db, file_id, item_tree, call_id))
            else
                try lookupSemanticNodeSymbol(db, file_id, item_tree, call_id);
            const callee_sym = chaseUseAliasSymbol(&db.symbol_table, raw_callee_sym);

            if (!callee_sym.isNone() and callee_sym.asInt() < db.symbol_table.countSymbols()) {
                const fn_ty = db.symbol_table.getSymbol(callee_sym).type_id;
                if (db.type_pool.getFnSignatureView(fn_ty)) |sig_v| {
                    if (maybe_mapping) |mapping| {
                        const self_offset: usize = if (sig_v.paramCount() > mapping.total_params)
                            sig_v.paramCount() - @as(usize, mapping.total_params)
                        else
                            0;
                        for (mapping.provided_slots) |slot| {
                            if (slot.arg_ast_node == expr_id) {
                                const param_idx = self_offset + @as(usize, slot.param_index);
                                if (param_idx < sig_v.paramCount()) {
                                    const p_node = db.type_pool.getNode(sig_v.getParamType(param_idx));
                                    return p_node.tag == .raw_ptr_ty and p_node.rhs != 0;
                                }
                                return false;
                            }
                        }
                        return false;
                    }

                    if ((call_node.tag == .call_expr or call_node.tag == .method_call) and
                        call_node.rhs.tag == .extra and call_id.asInt() < extra_ends.len)
                    {
                        const e_start: usize = call_node.rhs.payload;
                        const e_end: usize = @min(@as(usize, extra_ends[call_id.asInt()]), ast_arena.extra_data.items.len);
                        const args_base: usize = if (call_node.tag == .method_call) e_start + 1 else e_start;
                        if (args_base <= e_end) {
                            const arg_words = ast_arena.extra_data.items[args_base..e_end];
                            const self_offset: usize = if (call_node.tag == .method_call and
                                sig_v.paramCount() > arg_words.len)
                                1
                            else
                                0;
                            for (arg_words, 0..) |raw_arg_node, arg_i| {
                                if (raw_arg_node == arg_carrier_id.asInt() or raw_arg_node == expr_id.asInt()) {
                                    const param_idx = self_offset + arg_i;
                                    if (param_idx < sig_v.paramCount()) {
                                        const p_node = db.type_pool.getNode(sig_v.getParamType(param_idx));
                                        return p_node.tag == .raw_ptr_ty and p_node.rhs != 0;
                                    }
                                    return false;
                                }
                            }
                            return false;
                        }
                    }

                    var p_idx: usize = 0;
                    while (p_idx < sig_v.paramCount()) : (p_idx += 1) {
                        const p_node = db.type_pool.getNode(sig_v.getParamType(p_idx));
                        if (p_node.tag == .raw_ptr_ty and p_node.rhs != 0) return true;
                    }
                }
            }
            return false;
        },
        else => return false,
    }
}

/// Returns `true` if `expr_id` is a retired prefix `*ptr` AST node (`CstNodeKind.prefix_expr` + `*`).
fn isRetiredPrefixDerefAst(
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    expr_id: NodeIndex,
) bool {
    if (expr_id.isNone() or expr_id.asInt() >= ast_arena.countNodes()) return false;
    const node = ast_arena.getNode(expr_id);
    if ((node.tag != .deref_expr and node.tag != .unary_expr) or
        node.main_token.isNone() or node.lhs.tag != .node)
    {
        return false;
    }
    const tok_rec = tok_buf.getToken(node.main_token);
    if (tok_rec.kind != .star or tok_rec.flags.is_synthesized) return false;
    const orig_cst = ast_arena.getCstOrigin(expr_id);
    return !orig_cst.isNone() and orig_cst.asInt() < cst_arena.countNodes() and
        cst_arena.getNode(orig_cst).kind == .prefix_expr;
}

/// Recursively renders an expression subtree for `UR-22-06` prefix deref (`*$p` -> `$p.*`, `**p` -> `p.*.*`).
fn renderPrefixDerefExprRecursive(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    expr_id: NodeIndex,
) anyerror![]u8 {
    if (expr_id.isNone() or expr_id.asInt() >= ast_arena.countNodes()) return allocator.dupe(u8, "");
    const node = ast_arena.getNode(expr_id);
    if (isRetiredPrefixDerefAst(cst_arena, ast_arena, tok_buf, expr_id)) {
        var deref_layers: usize = 1;
        var inner_id = NodeIndex.fromInt(node.lhs.payload);
        while (isRetiredPrefixDerefAst(cst_arena, ast_arena, tok_buf, inner_id)) {
            deref_layers += 1;
            inner_id = NodeIndex.fromInt(ast_arena.getNode(inner_id).lhs.payload);
        }

        const inner_rendered = try renderPrefixDerefExprRecursive(
            allocator,
            source,
            cst_arena,
            ast_arena,
            tok_buf,
            inner_id,
        );
        defer allocator.free(inner_rendered);

        const inner_tag = ast_arena.getNode(inner_id).tag;
        const inner_sp_opt = extractAstByteSpan(cst_arena, ast_arena, tok_buf, inner_id);
        const is_already_paren = if (inner_sp_opt) |isp|
            tok_buf.getToken(isp.first_tok).kind == .lparen and tok_buf.getToken(isp.last_tok).kind == .rparen
        else
            false;
        const is_postfix_or_primary = is_already_paren or switch (inner_tag) {
            .ident_expr,
            .self_val,
            .path_expr,
            .field_access,
            .method_call,
            .call_expr,
            .generic_call,
            .index_expr,
            .deref_expr,
            .try_expr,
            .await_expr,
            => true,
            else => false,
        };

        var buf: std.ArrayList(u8) = .empty;
        errdefer buf.deinit(allocator);
        if (!is_postfix_or_primary) try buf.append(allocator, '(');
        try buf.appendSlice(allocator, std.mem.trim(u8, inner_rendered, " \t\r\n"));
        if (!is_postfix_or_primary) try buf.append(allocator, ')');
        var d_i: usize = 0;
        while (d_i < deref_layers) : (d_i += 1) {
            try buf.appendSlice(allocator, ".*");
        }
        return buf.toOwnedSlice(allocator);
    }

    const sp = extractAstByteSpan(cst_arena, ast_arena, tok_buf, expr_id) orelse return allocator.dupe(u8, "");
    return allocator.dupe(u8, source[sp.start_byte..sp.end_byte]);
}

/// Harvests `E0424` mutability hints, `E0421` `~Copy` parameter completions, and allowlisted compiler fixes from `sink_ptr`.
fn scanSinkForTier3(
    alloc: std.mem.Allocator,
    db_ptr: *CompilerDb,
    fid: FileId,
    src_bytes: []const u8,
    cst: *const LosslessCstArena,
    tb: *const TokenBuffer,
    sink_ptr: *const DiagnosticSink,
    is_enable_ur22_02: bool,
    is_enable_general: bool,
    is_internal_core_mode: bool,
    mut_map: *std.AutoHashMapUnmanaged(u32, bool),
    col: *FixCollector,
) !void {
    for (sink_ptr.diagnostics.items) |diag_item| {
        if (diag_item.primary_span.file_id != fid and !diag_item.primary_span.file_id.isNone()) continue;

        if (diag_item.code == .e0424_retired_slice_field_access and diag_item.suggestions.len > 0) {
            const fix0 = diag_item.suggestions[0];
            if (fix0.edits.len == 1) {
                const repl_str = db_ptr.interner.get(fix0.edits[0].replacement_id);
                try mut_map.put(
                    alloc,
                    diag_item.primary_span.start_byte,
                    std.mem.eql(u8, repl_str, "as_mut_ptr()"),
                );
            }
        }

        // `UR-22-02` Tier-3 `~Copy` completion; `var $id: $ty` hitting `E0421` -> `var $id: own $ty`:
        if (is_enable_ur22_02 and diag_item.code == .e0421_non_copy_value_parameter) {
            const p_start = diag_item.primary_span.start_byte;
            const cst_len = cst.countNodes();
            var ci: usize = 0;
            while (ci < cst_len) : (ci += 1) {
                const cid = CstNodeIndex.fromInt(@intCast(ci));
                if (cst.getNode(cid).kind != .fn_param) continue;
                const p_sp = extractCstTokenSpan(cst, tb, cid) orelse continue;
                if (p_start < p_sp.start_byte or p_start > p_sp.end_byte) continue;
                var has_var_kw = false;
                var colon_opt: ?u32 = null;
                var ti: u32 = p_sp.first_tok.asInt();
                while (ti <= p_sp.last_tok.asInt()) : (ti += 1) {
                    const tk = tb.getToken(TokenIndex.fromInt(ti)).kind;
                    if (tk == .kw_var) has_var_kw = true;
                    if (tk == .colon) {
                        colon_opt = ti;
                        break;
                    }
                }
                if (has_var_kw and colon_opt != null and colon_opt.? + 1 <= p_sp.last_tok.asInt()) {
                    const ty_tok = TokenIndex.fromInt(colon_opt.? + 1);
                    const ty_rec = tb.getToken(ty_tok);
                    if (ty_rec.kind != .kw_own and ty_rec.kind != .amp and ty_rec.kind != .star) {
                        _ = src_bytes;
                        try col.appendSingleEdit(
                            .type_migration,
                            ty_rec.byte_offset,
                            ty_rec.byte_offset,
                            "own ",
                            "UR-22-02: insert `own` on `~Copy` `var` value parameter (`E0421`)",
                        );
                    }
                }
                break;
            }
        }

        // When `!has_explicit_rule_filter`, harvest `W0403` (`@deprecated`) and allowlisted compiler fixes:
        if (is_enable_general) {
            const is_allowed_code = switch (diag_item.code) {
                .w0403_deprecated_symbol => true,
                .e0218_direct_core_import_forbidden => !is_internal_core_mode,
                .e0418_irrefutable_is_binding => true,
                .e0420_missing_call_site_own => true,
                else => false,
            };
            if (is_allowed_code) {
                for (diag_item.suggestions) |sug| {
                    try col.appendClonedFix(&db_ptr.interner, sug);
                }
            }
        }
    }
}

/// Collects Sub-stage C Tier 3 `CompilerDb` semantic modernizer fixes for `file_id` into `collector`.
fn collectSubstageCTier3FixesForFile(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    options: UpgradeOptions,
    collector: *FixCollector,
) !void {
    const is_ur21_04 = isRuleEnabled(options.rule_mask, .ur_21_04_type_level_generic_args);
    const is_ur21_05 = isRuleEnabled(options.rule_mask, .ur_21_05_option_unwrap_to_orelse);
    const is_ur21_06 = isRuleEnabled(options.rule_mask, .ur_21_06_with_arena_to_with_context);
    const is_ur21_07 = isRuleEnabled(options.rule_mask, .ur_21_07_end_relative_dollar_slices);
    const is_ur22_02 = isRuleEnabled(options.rule_mask, .ur_22_02_parameter_and_ownership_modes);
    const is_ur22_06 = isRuleEnabled(options.rule_mask, .ur_22_06_semantic_unary_deref_and_slice_methods);
    const is_harvesting_general = !options.has_explicit_rule_filter;

    if (!is_ur21_04 and !is_ur21_05 and !is_ur21_06 and !is_ur21_07 and
        !is_ur22_02 and !is_ur22_06 and !is_harvesting_general)
    {
        return;
    }

    const source = try db.getSourceText(file_id);
    const parsed = try db.parseCst(file_id);
    _ = try db.resolveSignatures(file_id);
    const item_tree = try db.extractItemTree(file_id);
    for (item_tree.entries) |entry| {
        _ = try db.getDefSideTables(entry.def_id);
    }

    const tok_buf = &parsed.token_buffer;
    const cst_arena = &parsed.cst_arena;
    const ast_arena = &parsed.ast_arena;
    const ast_count = ast_arena.countNodes();

    const ast_parents = try computeAstParentMap(allocator, ast_arena);
    defer allocator.free(ast_parents);
    const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
    defer allocator.free(extra_ends);

    // Build $O(1)$ map of `E0424` (`member_start_byte -> is_mut_suggested`) from signature & body diagnostics:
    var e0424_mut_map: std.AutoHashMapUnmanaged(u32, bool) = .empty;
    defer e0424_mut_map.deinit(allocator);

    try scanSinkForTier3(
        allocator,
        db,
        file_id,
        source,
        cst_arena,
        tok_buf,
        &parsed.diagnostics,
        is_ur22_02,
        is_harvesting_general,
        options.is_internal_core,
        &e0424_mut_map,
        collector,
    );
    if (db.getSignatureDiagnostics(file_id)) |sig_sink| {
        try scanSinkForTier3(
            allocator,
            db,
            file_id,
            source,
            cst_arena,
            tok_buf,
            sig_sink,
            is_ur22_02,
            is_harvesting_general,
            options.is_internal_core,
            &e0424_mut_map,
            collector,
        );
    }
    for (item_tree.entries) |entry| {
        if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
            try scanSinkForTier3(
                allocator,
                db,
                file_id,
                source,
                cst_arena,
                tok_buf,
                body_sink,
                is_ur22_02,
                is_harvesting_general,
                options.is_internal_core,
                &e0424_mut_map,
                collector,
            );
        }
    }

    // Walk AST nodes for `@fix_inline`, `UR-21-04`, `UR-21-05`, `UR-21-06`, `UR-21-07`, and `UR-22-06`:
    var ast_idx: usize = 0;
    while (ast_idx < ast_count) : (ast_idx += 1) {
        const node_id = NodeIndex.fromInt(@intCast(ast_idx));
        const node = ast_arena.getNode(node_id);

        // [0] Standalone `@fix_inline("…")` (`DR-14` §2.2 – silent during `corex check`, active in `corex upgrade`):
        if (is_harvesting_general) {
            if (try lookupFixInlineRewrite(db, file_id, item_tree, node_id)) |fix_rw| {
                const repl_text = db.interner.get(fix_rw.replacement_id);
                if (fix_rw.is_rhs_token_only and node.rhs.tag == .token) {
                    const rhs_sp = tok_buf.getTokenSpan(file_id, TokenIndex.fromInt(node.rhs.payload));
                    if (rhs_sp.end_byte > rhs_sp.start_byte) {
                        try collector.appendSingleEdit(
                            .type_migration,
                            rhs_sp.start_byte,
                            rhs_sp.end_byte,
                            repl_text,
                            "DR-14: expand `@fix_inline` migration template",
                        );
                    }
                } else if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, node_id)) |rw_sp| {
                    if (rw_sp.end_byte > rw_sp.start_byte) {
                        try collector.appendSingleEdit(
                            .type_migration,
                            rw_sp.start_byte,
                            rw_sp.end_byte,
                            repl_text,
                            "DR-14: expand `@fix_inline` migration template",
                        );
                    }
                }
            }
        }

        // [1] `UR-21-04`; `Type.assoc_fn[Args](…)` -> `Type[Args].assoc_fn(…)`:
        if (is_ur21_04 and node.tag == .method_call and node.lhs.tag == .node and node.rhs.tag == .extra) {
            const recv_node = NodeIndex.fromInt(node.lhs.payload);
            const recv_tag = ast_arena.getNode(recv_node).tag;
            if (recv_tag == .ident_expr or recv_tag == .path_expr) {
                const call_cst = ast_arena.getCstOrigin(node_id);
                if (!call_cst.isNone()) {
                    const call_rec = cst_arena.getNode(call_cst);
                    const call_end = @min(
                        @as(usize, call_cst.asInt()) + @max(@as(usize, call_rec.subtree_size), 1),
                        cst_arena.countNodes(),
                    );
                    var type_args_cst: CstNodeIndex = .none;
                    var cc: usize = call_cst.asInt() + 1;
                    while (cc < call_end) {
                        const sub_id = CstNodeIndex.fromInt(@intCast(cc));
                        const sub_rec = cst_arena.getNode(sub_id);
                        if (sub_rec.kind == .type_args) {
                            type_args_cst = sub_id;
                            break;
                        }
                        if (sub_rec.kind == .call_args_start) break;
                        cc += @max(@as(usize, sub_rec.subtree_size), 1);
                    }

                    if (!type_args_cst.isNone()) {
                        const recv_sym = chaseUseAliasSymbol(
                            &db.symbol_table,
                            try lookupSemanticNodeSymbol(db, file_id, item_tree, recv_node),
                        );
                        if (!recv_sym.isNone() and recv_sym.asInt() < db.symbol_table.countSymbols()) {
                            const sym_rec = db.symbol_table.getSymbol(recv_sym).*;
                            const is_nominal = sym_rec.kind == .struct_sym or sym_rec.kind == .enum_sym or
                                sym_rec.kind == .union_sym or sym_rec.kind == .type_alias_sym;
                            const nom_gen_params = db.symbol_table.getGenericParamSpecs(recv_sym);
                            if (is_nominal and nom_gen_params.len > 0) {
                                const call_sym = chaseUseAliasSymbol(
                                    &db.symbol_table,
                                    try lookupSemanticNodeSymbol(db, file_id, item_tree, node_id),
                                );
                                const fn_own_generics: usize = if (!call_sym.isNone() and
                                    call_sym.asInt() < db.symbol_table.countSymbols())
                                    db.symbol_table.getGenericParamSpecs(call_sym).len
                                else
                                    0;
                                if (fn_own_generics == 0) {
                                    if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, recv_node)) |recv_sp| {
                                        if (extractCstTokenSpan(cst_arena, tok_buf, type_args_cst)) |ta_sp| {
                                            if (recv_sp.end_byte < ta_sp.start_byte) {
                                                const ta_text = source[ta_sp.start_byte..ta_sp.end_byte];
                                                try collector.appendDualEdits(
                                                    .type_migration,
                                                    recv_sp.end_byte,
                                                    recv_sp.end_byte,
                                                    ta_text,
                                                    ta_sp.start_byte,
                                                    ta_sp.end_byte,
                                                    "",
                                                    "UR-21-04: lift generic arguments onto nominal type `Type[Args].assoc_fn(…)`",
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // [2] `UR-21-05`; `$opt.unwrap_or($def)` -> `$opt orelse $def`, `$opt.unwrap()` -> `$opt orelse unreachable`:
        if (is_ur21_05 and node.tag == .method_call and node.lhs.tag == .node and node.rhs.tag == .extra) {
            const extra_start: usize = node.rhs.payload;
            const extra_end: usize = @min(@as(usize, extra_ends[ast_idx]), ast_arena.extra_data.items.len);
            if (extra_start < extra_end) {
                const member_tok = TokenIndex.fromInt(ast_arena.extra_data.items[extra_start]);
                const member_lex = symbol_resolver.extractTokenSlice(source, tok_buf, member_tok);
                const call_arg_slice = ast_arena.extra_data.items[extra_start + 1 .. extra_end];
                const is_unwrap = std.mem.eql(u8, member_lex, "unwrap") and call_arg_slice.len == 0;
                const is_unwrap_or = std.mem.eql(u8, member_lex, "unwrap_or") and call_arg_slice.len == 1;

                if (is_unwrap or is_unwrap_or) {
                    const recv_node = NodeIndex.fromInt(node.lhs.payload);
                    const raw_recv_ty = try lookupSemanticNodeType(db, file_id, item_tree, recv_node);
                    const deref_ty = unwrapAutoDerefType(&db.type_pool, raw_recv_ty);
                    if (!deref_ty.isError() and db.type_pool.getTag(deref_ty) == .optional_ty) {
                        if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, node_id)) |full_sp| {
                            if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, recv_node)) |recv_sp| {
                                const recv_raw = std.mem.trim(u8, source[recv_sp.start_byte..recv_sp.end_byte], " \t\r\n");
                                const is_recv_parens = isOrelseOperandNeedingParens(
                                    tok_buf,
                                    recv_sp.first_tok,
                                    recv_sp.last_tok,
                                );

                                const parent_id = ast_parents[ast_idx];
                                const is_outer_parens = if (!parent_id.isNone() and
                                    parent_id.asInt() < ast_count)
                                    switch (ast_arena.getNode(parent_id).tag) {
                                        .field_access,
                                        .method_call,
                                        .index_expr,
                                        .try_expr,
                                        .await_expr,
                                        .deref_expr,
                                        .call_expr,
                                        .generic_call,
                                        .unary_expr,
                                        .cast_expr,
                                        .range_expr,
                                        .binary_expr,
                                        .pipe_expr,
                                        .is_expr,
                                        => true,
                                        else => false,
                                    }
                                else
                                    false;

                                if (is_unwrap) {
                                    if (!hasCommentsInByteRange(source, tok_buf, recv_sp.end_byte, full_sp.end_byte)) {
                                        const repl = try std.fmt.allocPrint(
                                            allocator,
                                            "{s}{s}{s}{s} orelse unreachable{s}",
                                            .{
                                                if (is_outer_parens) "(" else "",
                                                if (is_recv_parens) "(" else "",
                                                recv_raw,
                                                if (is_recv_parens) ")" else "",
                                                if (is_outer_parens) ")" else "",
                                            },
                                        );
                                        defer allocator.free(repl);
                                        try collector.appendSingleEdit(
                                            .lint_idiom,
                                            full_sp.start_byte,
                                            full_sp.end_byte,
                                            repl,
                                            "UR-21-05: modernize `$opt.unwrap()` to `$opt orelse unreachable`",
                                        );
                                    }
                                } else {
                                    if (extractAstByteSpan(
                                        cst_arena,
                                        ast_arena,
                                        tok_buf,
                                        NodeIndex.fromInt(call_arg_slice[0]),
                                    )) |def_sp| {
                                        if (!hasCommentsInByteRange(source, tok_buf, recv_sp.end_byte, def_sp.start_byte) and
                                            !hasCommentsInByteRange(source, tok_buf, def_sp.end_byte, full_sp.end_byte))
                                        {
                                            const def_raw = std.mem.trim(
                                                u8,
                                                source[def_sp.start_byte..def_sp.end_byte],
                                                " \t\r\n",
                                            );
                                            const is_def_parens = isOrelseOperandNeedingParens(
                                                tok_buf,
                                                def_sp.first_tok,
                                                def_sp.last_tok,
                                            );
                                            const repl = try std.fmt.allocPrint(
                                                allocator,
                                                "{s}{s}{s}{s} orelse {s}{s}{s}{s}",
                                                .{
                                                    if (is_outer_parens) "(" else "",
                                                    if (is_recv_parens) "(" else "",
                                                    recv_raw,
                                                    if (is_recv_parens) ")" else "",
                                                    if (is_def_parens) "(" else "",
                                                    def_raw,
                                                    if (is_def_parens) ")" else "",
                                                    if (is_outer_parens) ")" else "",
                                                },
                                            );
                                            defer allocator.free(repl);
                                            try collector.appendSingleEdit(
                                                .lint_idiom,
                                                full_sp.start_byte,
                                                full_sp.end_byte,
                                                repl,
                                                "UR-21-05: modernize `$opt.unwrap_or($def)` to `$opt orelse $def`",
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // [3] `UR-21-06`; `cx.mem.with_arena($arena, || $blk)` -> `with context.allocator = $arena $blk`:
        if (is_ur21_06 and (node.tag == .call_expr or node.tag == .method_call)) {
            const parent_id = ast_parents[ast_idx];
            const is_stmt_position = !parent_id.isNone() and ast_arena.getNode(parent_id).tag == .block;
            if (is_stmt_position) {
                var is_with_arena_callee = false;
                var arg_words: []const u32 = &.{};

                if (node.tag == .call_expr and node.lhs.tag == .node and node.rhs.tag == .extra) {
                    const callee_node = NodeIndex.fromInt(node.lhs.payload);
                    const e_start: usize = node.rhs.payload;
                    const e_end: usize = @min(@as(usize, extra_ends[ast_idx]), ast_arena.extra_data.items.len);
                    if (e_start < e_end) arg_words = ast_arena.extra_data.items[e_start..e_end];
                    if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, callee_node)) |cal_sp| {
                        const cal_str = std.mem.trim(u8, source[cal_sp.start_byte..cal_sp.end_byte], " \t\r\n");
                        if (WITH_ARENA_CALLEE_SET.has(cal_str)) {
                            is_with_arena_callee = true;
                        } else if (std.mem.eql(u8, cal_str, "with_arena")) {
                            const cal_sym = chaseUseAliasSymbol(
                                &db.symbol_table,
                                try lookupSemanticNodeSymbol(db, file_id, item_tree, callee_node),
                            );
                            if (!cal_sym.isNone() and cal_sym.asInt() < db.symbol_table.countSymbols()) {
                                const sym_r = db.symbol_table.getSymbol(cal_sym).*;
                                if (std.mem.eql(u8, sym_r.name_text, "with_arena")) is_with_arena_callee = true;
                            }
                        }
                    }
                } else if (node.tag == .method_call and node.lhs.tag == .node and node.rhs.tag == .extra) {
                    const e_start: usize = node.rhs.payload;
                    const e_end: usize = @min(@as(usize, extra_ends[ast_idx]), ast_arena.extra_data.items.len);
                    if (e_start < e_end) {
                        const mem_tok = TokenIndex.fromInt(ast_arena.extra_data.items[e_start]);
                        if (std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, mem_tok), "with_arena")) {
                            arg_words = ast_arena.extra_data.items[e_start + 1 .. e_end];
                            if (extractAstByteSpan(
                                cst_arena,
                                ast_arena,
                                tok_buf,
                                NodeIndex.fromInt(node.lhs.payload),
                            )) |r_sp| {
                                const r_str = std.mem.trim(u8, source[r_sp.start_byte..r_sp.end_byte], " \t\r\n");
                                if (MEM_MODULE_RECEIVER_SET.has(r_str)) {
                                    is_with_arena_callee = true;
                                }
                            }
                        }
                    }
                }

                if (is_with_arena_callee and arg_words.len == 2) {
                    const arena_arg = NodeIndex.fromInt(arg_words[0]);
                    const closure_arg = NodeIndex.fromInt(arg_words[1]);
                    if (!closure_arg.isNone() and closure_arg.asInt() < ast_count and
                        ast_arena.getNode(closure_arg).tag == .closure_expr)
                    {
                        const clos_cst = ast_arena.getCstOrigin(closure_arg);
                        if (extractCstTokenSpan(cst_arena, tok_buf, clos_cst)) |clos_sp| {
                            // Verify zero-parameter `||` closure and extract `$blk`:
                            if (tok_buf.getToken(clos_sp.first_tok).kind == .pipepipe and
                                !hasNonNestedReturnInClosureBody(cst_arena, tok_buf, clos_cst))
                            {
                                if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, arena_arg)) |arena_sp| {
                                    if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, node_id)) |call_sp| {
                                        // Include trailing `;` of the expression statement if present:
                                        var stmt_end_byte = call_sp.end_byte;
                                        if (call_sp.last_tok.asInt() + 1 < tok_buf.countTokens()) {
                                            const after_call = tok_buf.getToken(
                                                TokenIndex.fromInt(call_sp.last_tok.asInt() + 1),
                                            );
                                            if (after_call.kind == .semi) {
                                                stmt_end_byte = after_call.byte_offset +| after_call.byte_len;
                                            }
                                        }

                                        // Extract body after `||` (and optional `-> unit`):
                                        var body_tok_i: u32 = clos_sp.first_tok.asInt() + 1;
                                        if (body_tok_i + 1 <= clos_sp.last_tok.asInt() and
                                            tok_buf.getToken(TokenIndex.fromInt(body_tok_i)).kind == .arrow)
                                        {
                                            body_tok_i += 2;
                                        }
                                        if (body_tok_i <= clos_sp.last_tok.asInt()) {
                                            const body_first_rec = tok_buf.getToken(TokenIndex.fromInt(body_tok_i));
                                            if (!hasCommentsInByteRange(source, tok_buf, call_sp.start_byte, arena_sp.start_byte) and
                                                !hasCommentsInByteRange(source, tok_buf, arena_sp.end_byte, body_first_rec.byte_offset) and
                                                !hasCommentsInByteRange(source, tok_buf, clos_sp.end_byte, stmt_end_byte))
                                            {
                                                const body_raw = std.mem.trim(
                                                    u8,
                                                    source[body_first_rec.byte_offset..clos_sp.end_byte],
                                                    " \t\r\n",
                                                );
                                                const arena_raw = std.mem.trim(
                                                    u8,
                                                    source[arena_sp.start_byte..arena_sp.end_byte],
                                                    " \t\r\n",
                                                );
                                                const is_block_body = body_first_rec.kind == .lbrace;
                                                const repl = if (is_block_body)
                                                    try std.fmt.allocPrint(
                                                        allocator,
                                                        "with context.allocator = {s} {s}",
                                                        .{ arena_raw, body_raw },
                                                    )
                                                else
                                                    try std.fmt.allocPrint(
                                                        allocator,
                                                        "with context.allocator = {s} {{ {s}; }}",
                                                        .{ arena_raw, body_raw },
                                                    );
                                                defer allocator.free(repl);

                                                try collector.appendSingleEdit(
                                                    .lint_idiom,
                                                    call_sp.start_byte,
                                                    stmt_end_byte,
                                                    repl,
                                                    "UR-21-06: rewrite `with_arena` closure call to `with context.allocator`",
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // [4] `UR-21-07`; `$s[$lo .. $s.len() - $k]` -> `$s[$lo..$-$k]` (omitting literal `0` `$lo`):
        if (is_ur21_07 and node.tag == .index_expr and node.lhs.tag == .node and node.rhs.tag == .node) {
            const recv_s = NodeIndex.fromInt(node.lhs.payload);
            const idx_arg = NodeIndex.fromInt(node.rhs.payload);
            if (isPurePlaceAstExpr(ast_arena, recv_s) and !idx_arg.isNone() and idx_arg.asInt() < ast_count) {
                const range_node = ast_arena.getNode(idx_arg);
                if (range_node.tag == .range_expr and range_node.rhs.tag == .node) {
                    const end_node_id = NodeIndex.fromInt(range_node.rhs.payload);
                    const end_node = ast_arena.getNode(end_node_id);
                    if (end_node.tag == .binary_expr and !end_node.main_token.isNone() and
                        tok_buf.getToken(end_node.main_token).kind == .minus and
                        end_node.lhs.tag == .node and end_node.rhs.tag == .node)
                    {
                        const sub_lhs_id = NodeIndex.fromInt(end_node.lhs.payload);
                        const sub_rhs_id = NodeIndex.fromInt(end_node.rhs.payload);
                        const sub_lhs = ast_arena.getNode(sub_lhs_id);

                        var len_recv_opt: ?NodeIndex = null;
                        if (sub_lhs.tag == .method_call and sub_lhs.lhs.tag == .node and sub_lhs.rhs.tag == .extra) {
                            const m_start: usize = sub_lhs.rhs.payload;
                            const m_end: usize = @min(
                                @as(usize, extra_ends[sub_lhs_id.asInt()]),
                                ast_arena.extra_data.items.len,
                            );
                            if (m_start + 1 == m_end) {
                                const m_tok = TokenIndex.fromInt(ast_arena.extra_data.items[m_start]);
                                if (std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, m_tok), "len")) {
                                    len_recv_opt = NodeIndex.fromInt(sub_lhs.lhs.payload);
                                }
                            }
                        } else if (sub_lhs.tag == .field_access and sub_lhs.lhs.tag == .node and
                            sub_lhs.rhs.tag == .token)
                        {
                            const f_tok = TokenIndex.fromInt(sub_lhs.rhs.payload);
                            if (std.mem.eql(u8, symbol_resolver.extractTokenSlice(source, tok_buf, f_tok), "len")) {
                                len_recv_opt = NodeIndex.fromInt(sub_lhs.lhs.payload);
                            }
                        }

                        if (len_recv_opt) |len_recv| {
                            const s_ty = unwrapAutoDerefType(
                                &db.type_pool,
                                try lookupSemanticNodeType(db, file_id, item_tree, recv_s),
                            );
                            const s_tag = db.type_pool.getTag(s_ty);
                            const is_slice_like = s_ty == .str_ty or s_tag == .slice_ty or
                                s_tag == .array_ty or s_tag == .soa_slice_ty or s_tag == .soa_array_ty;
                            if (is_slice_like) {
                                if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, recv_s)) |s_sp| {
                                    if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, len_recv)) |lr_sp| {
                                        if (hasIdenticalTokenLexemes(source, tok_buf, s_sp, lr_sp)) {
                                            if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, idx_arg)) |rng_sp| {
                                                if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, sub_rhs_id)) |k_sp| {
                                                    const range_op = if (!range_node.main_token.isNone() and
                                                        tok_buf.getToken(range_node.main_token).kind == .dotdoteq)
                                                        "..="
                                                    else
                                                        "..";
                                                    var lo_str: []const u8 = "";
                                                    var lo_kept_sp: ?CstTokenSpan = null;
                                                    if (range_node.lhs.tag == .node) {
                                                        if (extractAstByteSpan(
                                                            cst_arena,
                                                            ast_arena,
                                                            tok_buf,
                                                            NodeIndex.fromInt(range_node.lhs.payload),
                                                        )) |lo_sp| {
                                                            const raw_lo = std.mem.trim(
                                                                u8,
                                                                source[lo_sp.start_byte..lo_sp.end_byte],
                                                                " \t\r\n",
                                                            );
                                                            if (!std.mem.eql(u8, raw_lo, "0")) {
                                                                lo_str = raw_lo;
                                                                lo_kept_sp = lo_sp;
                                                            }
                                                        }
                                                    }
                                                    const has_unpreserved_range_comment = if (lo_kept_sp) |lo_sp|
                                                        hasCommentsInByteRange(source, tok_buf, rng_sp.start_byte, lo_sp.start_byte) or
                                                            hasCommentsInByteRange(source, tok_buf, lo_sp.end_byte, k_sp.start_byte) or
                                                            hasCommentsInByteRange(source, tok_buf, k_sp.end_byte, rng_sp.end_byte)
                                                    else
                                                        hasCommentsInByteRange(source, tok_buf, rng_sp.start_byte, k_sp.start_byte) or
                                                            hasCommentsInByteRange(source, tok_buf, k_sp.end_byte, rng_sp.end_byte);
                                                    if (!has_unpreserved_range_comment) {
                                                        const k_tag = ast_arena.getNode(sub_rhs_id).tag;
                                                        const k_raw = std.mem.trim(
                                                            u8,
                                                            source[k_sp.start_byte..k_sp.end_byte],
                                                            " \t\r\n",
                                                        );
                                                        const is_k_parenthesized = k_tag == .binary_expr or
                                                            k_tag == .range_expr or
                                                            k_tag == .cast_expr or k_tag == .if_expr;
                                                        const rhs_dollar = if (k_tag == .int_lit)
                                                            try std.fmt.allocPrint(allocator, "$-{s}", .{k_raw})
                                                        else if (is_k_parenthesized)
                                                            try std.fmt.allocPrint(allocator, "$ - ({s})", .{k_raw})
                                                        else
                                                            try std.fmt.allocPrint(allocator, "$ - {s}", .{k_raw});
                                                        defer allocator.free(rhs_dollar);

                                                        const repl = try std.fmt.allocPrint(
                                                            allocator,
                                                            "{s}{s}{s}",
                                                            .{ lo_str, range_op, rhs_dollar },
                                                        );
                                                        defer allocator.free(repl);

                                                        try collector.appendSingleEdit(
                                                            .lint_idiom,
                                                            rng_sp.start_byte,
                                                            rng_sp.end_byte,
                                                            repl,
                                                            "UR-21-07: modernize `$s[$lo .. $s.len() - $k]` to `$s[$lo..$-$k]`",
                                                        );
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // [5] `UR-22-06`; `!$e` -> `not $e` / `~$e`, prefix `*$p` -> `$p.*`, `.len`/`.ptr` -> `.len()`/`.as_ptr()`:
        if (is_ur22_06) {
            // [5a] Retired `!$e`:
            if (node.tag == .unary_expr and !node.main_token.isNone()) {
                const u_rec = tok_buf.getToken(node.main_token);
                if (u_rec.kind == .bang and !u_rec.flags.is_synthesized) {
                    const bang_span = Span.init(file_id, u_rec.byte_offset, u_rec.byte_offset +| u_rec.byte_len);
                    if (try db.resolveBangFixSuggestion(file_id, bang_span)) |bang_fix| {
                        try collector.appendClonedFix(&db.interner, bang_fix);
                    } else if (node.lhs.tag == .node) {
                        const op_node = NodeIndex.fromInt(node.lhs.payload);
                        const op_ty = unwrapAutoDerefType(
                            &db.type_pool,
                            try lookupSemanticNodeType(db, file_id, item_tree, op_node),
                        );
                        if (op_ty == .bool_ty) {
                            const has_ws = @as(usize, bang_span.end_byte) < source.len and
                                isAsciiWhitespace(source[bang_span.end_byte]);
                            try collector.appendSingleEdit(
                                .type_migration,
                                bang_span.start_byte,
                                bang_span.end_byte,
                                if (has_ws) "not" else "not ",
                                "UR-22-06: replace retired `!` on `bool` with `not`",
                            );
                        } else if (op_ty.isIntegerPrimitive() or op_ty == .untyped_int_ty or
                            db.type_pool.getTag(op_ty) == .bit_field_ty)
                        {
                            try collector.appendSingleEdit(
                                .type_migration,
                                bang_span.start_byte,
                                bang_span.end_byte,
                                "~",
                                "UR-22-06: replace retired `!` on integer/bit_field with `~`",
                            );
                        }
                    }
                }
            }

            // [5b] Retired prefix `*$p` -> `$p.*` (handled once on outermost `*` of nested `**p` chains):
            if (isRetiredPrefixDerefAst(cst_arena, ast_arena, tok_buf, node_id)) {
                const parent_id = ast_parents[ast_idx];
                const is_nested_under_prefix_star = isRetiredPrefixDerefAst(cst_arena, ast_arena, tok_buf, parent_id);
                if (!is_nested_under_prefix_star) {
                    if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, node_id)) |deref_sp| {
                        if (!hasCommentsInByteRange(source, tok_buf, deref_sp.start_byte, deref_sp.end_byte)) {
                            const postfix_str = try renderPrefixDerefExprRecursive(
                                allocator,
                                source,
                                cst_arena,
                                ast_arena,
                                tok_buf,
                                node_id,
                            );
                            defer allocator.free(postfix_str);
                            if (postfix_str.len > 0) {
                                try collector.appendSingleEdit(
                                    .type_migration,
                                    deref_sp.start_byte,
                                    deref_sp.end_byte,
                                    postfix_str,
                                    "UR-22-06: rewrite retired prefix `*ptr` dereference to `ptr.*`",
                                );
                            }
                        }
                    }
                }
            }

            // [5c] Slice/array/`str` `.len` -> `.len()`, `.is_empty` -> `.is_empty()`, & `.ptr` -> `.as_mut_ptr()` / `.as_ptr()`:
            if (node.tag == .field_access and node.lhs.tag == .node and node.rhs.tag == .token) {
                const mem_tok = TokenIndex.fromInt(node.rhs.payload);
                const mem_rec = tok_buf.getToken(mem_tok);
                const mem_lex = symbol_resolver.extractTokenSlice(source, tok_buf, mem_tok);
                if (!mem_rec.flags.is_synthesized) {
                    if (SLICE_PROP_MEMBER_MAP.get(mem_lex)) |prop_kind| {
                        const recv_node = NodeIndex.fromInt(node.lhs.payload);
                        const raw_recv_ty = try lookupSemanticNodeType(db, file_id, item_tree, recv_node);
                        const deref_ty = unwrapAutoDerefType(&db.type_pool, raw_recv_ty);
                        const deref_tag = db.type_pool.getTag(deref_ty);
                        const is_verified_slice_or_e0424 = e0424_mut_map.contains(mem_rec.byte_offset) or
                            deref_ty == .str_ty or deref_tag == .slice_ty or deref_tag == .array_ty or
                            deref_tag == .soa_slice_ty or deref_tag == .soa_array_ty;

                        if (is_verified_slice_or_e0424) {
                            switch (prop_kind) {
                                .len => try collector.appendSingleEdit(
                                    .type_migration,
                                    mem_rec.byte_offset,
                                    mem_rec.byte_offset +| mem_rec.byte_len,
                                    "len()",
                                    "UR-22-06: replace retired `.len` property with `.len()`",
                                ),
                                .is_empty => try collector.appendSingleEdit(
                                    .type_migration,
                                    mem_rec.byte_offset,
                                    mem_rec.byte_offset +| mem_rec.byte_len,
                                    "is_empty()",
                                    "UR-22-06: replace retired `.is_empty` property with `.is_empty()`",
                                ),
                                .ptr => {
                                    const is_mut_place = (e0424_mut_map.get(mem_rec.byte_offset) orelse
                                        (db.type_pool.getTag(raw_recv_ty) == .mut_ref_ty)) and deref_ty != .str_ty;
                                    const is_using_mut_ptr = is_mut_place and try isPtrAccessCoercedToMutRawPtr(
                                        db,
                                        file_id,
                                        item_tree,
                                        source,
                                        cst_arena,
                                        ast_arena,
                                        tok_buf,
                                        ast_parents,
                                        extra_ends,
                                        node_id,
                                    );
                                    try collector.appendSingleEdit(
                                        .type_migration,
                                        mem_rec.byte_offset,
                                        mem_rec.byte_offset +| mem_rec.byte_len,
                                        if (is_using_mut_ptr) "as_mut_ptr()" else "as_ptr()",
                                        "UR-22-06: replace retired `.ptr` property with pointer method",
                                    );
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

// ---------------- Manifest & Lockfile Helpers -----------------

/// Unquotes a single-line `"…"` or `'…'` TOML scalar slice for fast key/value inspection.
fn unquoteSimpleTomlString(raw_tok_slice: []const u8) ?[]const u8 {
    if (raw_tok_slice.len >= 2 and
        ((raw_tok_slice[0] == '"' and raw_tok_slice[raw_tok_slice.len - 1] == '"') or
            (raw_tok_slice[0] == '\'' and raw_tok_slice[raw_tok_slice.len - 1] == '\'')))
    {
        return raw_tok_slice[1 .. raw_tok_slice.len - 1];
    }
    return raw_tok_slice;
}

/// Extracts the `[header.path]` section prefix string of a TOML `.table_header` CST node into `section_buf`.
fn extractTomlTableHeaderPath(
    doc: *const pkg_manifest.TomlDocumentView,
    header_node: pkg_manifest.TomlCstNode,
    section_buf: *[128]u8,
) []const u8 {
    var out_len: usize = 0;
    var tok_i: u32 = header_node.first_token;
    while (tok_i <= header_node.last_token and tok_i < doc.tokens.tokens.len) : (tok_i += 1) {
        const tok = doc.tokens.tokens.get(tok_i);
        if (tok.kind == .lbracket or tok.kind == .rbracket or
            tok.kind == .double_lbracket or tok.kind == .double_rbracket)
        {
            continue;
        }
        if (tok.kind == .dot) {
            if (out_len < section_buf.len) {
                section_buf[out_len] = '.';
                out_len += 1;
            }
            continue;
        }
        const raw_seg = doc.toml_slice[tok.byte_offset .. tok.byte_offset + tok.byte_len];
        const clean_seg = unquoteSimpleTomlString(raw_seg) orelse raw_seg;
        if (out_len + clean_seg.len <= section_buf.len) {
            @memcpy(section_buf[out_len .. out_len + clean_seg.len], clean_seg);
            out_len += clean_seg.len;
        }
    }
    return section_buf[0..out_len];
}

/// Collects retired `[package]` / `[workspace.package]` `edition = "2024"` / `"2025"` -> `"2026"` fixes on `doc`.
fn collectRetiredEditionTomlFixes(
    arena: *BumpArena,
    interner: *StringInterner,
    doc: *const pkg_manifest.TomlDocumentView,
    fixes_out: *std.ArrayListUnmanaged(SuggestedFix),
) !void {
    const cst_len = doc.cst.nodes.len;
    var section_buf: [128]u8 = undefined;
    var active_section: []const u8 = "";

    var idx: usize = 0;
    while (idx < cst_len) : (idx += 1) {
        const cst_node = doc.cst.nodes.get(idx);
        if (cst_node.kind == .table_header or cst_node.kind == .array_table_header) {
            active_section = extractTomlTableHeaderPath(doc, cst_node, &section_buf);
            continue;
        }
        if (cst_node.kind != .key_value) continue;
        if (cst_node.first_token + 2 > cst_node.last_token or cst_node.last_token >= doc.tokens.tokens.len) continue;

        // Check `edition = "<retired>"` inside `[package]`, `[workspace.package]`, or dotted `package.edition`:
        const first_tok = doc.tokens.tokens.get(cst_node.first_token);
        const last_tok = doc.tokens.tokens.get(cst_node.last_token);
        if (last_tok.kind != .basic_string and last_tok.kind != .literal_string) continue;
        const val_raw = doc.toml_slice[last_tok.byte_offset .. last_tok.byte_offset + last_tok.byte_len];
        const val_unquoted = unquoteSimpleTomlString(val_raw) orelse continue;
        if (!RETIRED_EDITION_SET.has(val_unquoted)) continue;

        const key_raw = doc.toml_slice[first_tok.byte_offset .. first_tok.byte_offset + first_tok.byte_len];
        const key_clean = unquoteSimpleTomlString(key_raw) orelse key_raw;

        var is_edition_target = false;
        if (MANIFEST_EDITION_SECTION_SET.has(active_section) and
            std.mem.eql(u8, key_clean, "edition") and
            doc.tokens.tokens.get(cst_node.first_token + 1).kind == .eq)
        {
            is_edition_target = true;
        } else if (active_section.len == 0 and std.mem.eql(u8, key_clean, "package") and
            cst_node.first_token + 4 <= cst_node.last_token)
        {
            const k2_tok = doc.tokens.tokens.get(cst_node.first_token + 2);
            const k2_raw = doc.toml_slice[k2_tok.byte_offset .. k2_tok.byte_offset + k2_tok.byte_len];
            if (doc.tokens.tokens.get(cst_node.first_token + 1).kind == .dot and
                std.mem.eql(u8, unquoteSimpleTomlString(k2_raw) orelse k2_raw, "edition"))
            {
                is_edition_target = true;
            }
        }

        if (is_edition_target) {
            const abs_lo = doc.base_byte_offset +| last_tok.byte_offset;
            const abs_hi = abs_lo +| @as(u32, last_tok.byte_len);
            const edits = try arena.asAllocator().alloc(TextEdit, 1);
            edits[0] = .{
                .file_id = doc.file_id,
                .start_byte = abs_lo,
                .end_byte = abs_hi,
                .replacement_id = try interner.intern(
                    if (val_raw.len >= 2 and val_raw[0] == '\'') "'2026'" else "\"2026\"",
                ),
            };
            try fixes_out.append(arena.backing_allocator, .{
                .message = "upgrade retired `edition` to `\"2026\"`",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = edits,
            });
        }
    }
}

/// Collects `TextEdit`s appending missing accepted capabilities into explicit `allow_caps = […]` arrays in `doc`.
fn collectManifestAllowCapsAppendFixes(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    doc: *const pkg_manifest.TomlDocumentView,
    accepted_by_pkg: *const std.StringHashMapUnmanaged(u16),
    fixes_out: *std.ArrayListUnmanaged(SuggestedFix),
) !void {
    if (accepted_by_pkg.count() == 0) return;
    const cst_len = doc.cst.nodes.len;
    var section_buf: [128]u8 = undefined;
    var active_section: []const u8 = "";
    var current_inline_dep: []const u8 = "";
    var inline_dep_end_idx: usize = 0;

    var idx: usize = 0;
    while (idx < cst_len) : (idx += 1) {
        if (idx >= inline_dep_end_idx) current_inline_dep = "";
        const cst_node = doc.cst.nodes.get(idx);
        if (cst_node.kind == .table_header or cst_node.kind == .array_table_header) {
            active_section = extractTomlTableHeaderPath(doc, cst_node, &section_buf);
            continue;
        }
        if (cst_node.kind != .key_value) continue;
        if (cst_node.first_token >= doc.tokens.tokens.len or cst_node.last_token >= doc.tokens.tokens.len) continue;

        const key_tok = doc.tokens.tokens.get(cst_node.first_token);
        const key_raw = doc.toml_slice[key_tok.byte_offset .. key_tok.byte_offset + key_tok.byte_len];
        const key_clean = unquoteSimpleTomlString(key_raw) orelse key_raw;

        // Track `<dep_name> = { … allow_caps = […] … }` inside `[dependencies]` / `[dev-dependencies]`:
        if (MANIFEST_DEP_SECTION_SET.has(active_section) and !cst_node.flags.is_inline_table_entry) {
            current_inline_dep = key_clean;
            inline_dep_end_idx = idx + @max(@as(usize, cst_node.subtree_size), 1);
            continue;
        }

        // Determine if this `key_value` is `allow_caps = […]` or `default_allow_caps = […]` for a target package:
        var extra_bits: u16 = 0;
        if (std.mem.eql(u8, key_clean, "allow_caps")) {
            if (current_inline_dep.len > 0) {
                extra_bits = accepted_by_pkg.get(current_inline_dep) orelse 0;
            } else if (std.mem.startsWith(u8, active_section, "dependencies.")) {
                extra_bits = accepted_by_pkg.get(active_section["dependencies.".len..]) orelse 0;
            } else if (std.mem.startsWith(u8, active_section, "dev-dependencies.")) {
                extra_bits = accepted_by_pkg.get(active_section["dev-dependencies.".len..]) orelse 0;
            } else if (std.mem.startsWith(u8, active_section, "security.package.")) {
                extra_bits = accepted_by_pkg.get(active_section["security.package.".len..]) orelse 0;
            }
        } else if (std.mem.eql(u8, key_clean, "default_allow_caps") and std.mem.eql(u8, active_section, "security")) {
            extra_bits = accepted_by_pkg.get("*") orelse 0;
        }
        if (extra_bits == 0) continue;

        // Locate the `.array` child `[` … `]` of `allow_caps`:
        const kv_end = @min(idx + @max(@as(usize, cst_node.subtree_size), 1), cst_len);
        var arr_idx = idx + 1;
        while (arr_idx < kv_end) : (arr_idx += 1) {
            const arr_node = doc.cst.nodes.get(arr_idx);
            if (arr_node.kind != .array) continue;
            if (arr_node.last_token >= doc.tokens.tokens.len) break;
            const rbracket_tok = doc.tokens.tokens.get(arr_node.last_token);
            if (rbracket_tok.kind != .rbracket) break;

            // Scan existing capability strings inside `[` … `]`:
            var present_bits: u16 = 0;
            var elem_count: usize = 0;
            var t_i = arr_node.first_token + 1;
            while (t_i < arr_node.last_token) : (t_i += 1) {
                const elem_tok = doc.tokens.tokens.get(t_i);
                if (elem_tok.kind == .basic_string or elem_tok.kind == .literal_string) {
                    elem_count += 1;
                    const s_raw = doc.toml_slice[elem_tok.byte_offset .. elem_tok.byte_offset + elem_tok.byte_len];
                    if (unquoteSimpleTomlString(s_raw)) |cap_name| {
                        if (pkg_manifest.MANIFEST_CAPABILITY_MAP.get(cap_name)) |cap_b| {
                            present_bits |= cap_b;
                        }
                    }
                }
            }

            const missing_bits = extra_bits & ~present_bits;
            if (missing_bits != 0) {
                var append_buf: std.ArrayListUnmanaged(u8) = .empty;
                defer append_buf.deinit(allocator);
                const is_needing_leading_comma = elem_count > 0 and !arr_node.flags.has_trailing_comma;
                var is_first_added = true;
                for (CANONICAL_LOCKFILE_CAP_TABLE) |cap_entry| {
                    if ((missing_bits & cap_entry.bit) != 0) {
                        if (is_first_added) {
                            if (is_needing_leading_comma) {
                                try append_buf.appendSlice(allocator, ", ");
                            } else if (elem_count > 0) {
                                try append_buf.append(allocator, ' ');
                            }
                            is_first_added = false;
                        } else {
                            try append_buf.appendSlice(allocator, ", ");
                        }
                        try pkg_manifest.appendEscapedTomlBasicString(&append_buf, allocator, cap_entry.name);
                    }
                }
                const ins_pos = doc.base_byte_offset +| rbracket_tok.byte_offset;
                const edits = try arena.asAllocator().alloc(TextEdit, 1);
                edits[0] = .{
                    .file_id = doc.file_id,
                    .start_byte = ins_pos,
                    .end_byte = ins_pos,
                    .replacement_id = try interner.intern(append_buf.items),
                };
                try fixes_out.append(arena.backing_allocator, .{
                    .message = "append accepted capabilities to `allow_caps`",
                    .applicability = .machine_applicable,
                    .priority = .memory_safety,
                    .edits = edits,
                });
            }
            break;
        }
    }
}

/// Canonicalizes a `.cx` script `---` frontmatter TOML prefix (`[0 .. prefix_end_byte)`).
fn canonicalizeScriptFrontmatterPrefix(
    allocator: std.mem.Allocator,
    file_id: FileId,
    raw_source: []const u8,
    prefix_end_byte: usize,
    cfg_env: *const pkg_manifest.CfgEnv,
) ![]u8 {
    var current = try allocator.dupe(u8, raw_source[0..prefix_end_byte]);
    errdefer allocator.free(current);

    var pass: u8 = 0;
    while (pass < MAX_SYNERGY_PASSES) : (pass += 1) {
        var arena = BumpArena.init(allocator);
        defer arena.deinit();
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        const extracted = (try pkg_manifest.extractScriptFrontmatter(&arena, file_id, current, null)) orelse break;
        var parsed_fm = try pkg_manifest.parseScriptFrontmatterManifest(
            allocator,
            &arena,
            &interner,
            file_id,
            current,
            extracted,
            cfg_env,
            &sink,
        );
        defer parsed_fm.doc.deinit(allocator);

        var candidate_fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
        defer candidate_fixes.deinit(allocator);
        for (sink.diagnostics.items) |d_item| {
            for (d_item.suggestions) |sug| {
                if (sug.applicability == .machine_applicable) {
                    try candidate_fixes.append(allocator, sug);
                }
            }
        }
        try collectRetiredEditionTomlFixes(&arena, &interner, &parsed_fm.doc, &candidate_fixes);
        if (candidate_fixes.items.len == 0) break;

        const patched = pkg_manifest.applyManifestFixesTransactionally(
            allocator,
            &parsed_fm.doc,
            candidate_fixes.items,
            &interner,
        ) catch break;
        if (std.mem.eql(u8, current, patched)) {
            allocator.free(patched);
            break;
        }
        allocator.free(current);
        current = patched;
    }
    return current;
}

/// Formats and registers an owned card explanation line into `owned` and `lines`.
fn appendFmtLine(
    alloc: std.mem.Allocator,
    owned: *std.ArrayListUnmanaged([]u8),
    lines: *std.ArrayListUnmanaged([]const u8),
    comptime fmt_str: []const u8,
    args: anytype,
) !void {
    const formatted = try std.fmt.allocPrint(alloc, fmt_str, args);
    errdefer alloc.free(formatted);
    try owned.append(alloc, formatted);
    try lines.append(alloc, formatted);
}

// --------- Multi-Module, Stdlib & Dependency Binding ----------

/// Normalizes path separators to `/` and strips leading `./` prefixes for deterministic `FileId` matching.
fn normalizeModLookupPathAlloc(allocator: std.mem.Allocator, raw_path: []const u8) ![]u8 {
    var trimmed = raw_path;
    while (trimmed.len >= 2 and trimmed[0] == '.' and (trimmed[1] == '/' or trimmed[1] == '\\')) {
        trimmed = trimmed[2..];
    }
    const out = try allocator.alloc(u8, trimmed.len);
    for (trimmed, 0..) |ch_byte, i| {
        out[i] = if (ch_byte == '\\') '/' else ch_byte;
    }
    return out;
}

/// Formats a relative or directory-qualified candidate module path (`<mod>.cx` when `dir_path` is `"."` or `""`).
fn formatSubmoduleCandidateAlloc(
    allocator: std.mem.Allocator,
    dir_path: []const u8,
    stem_opt: ?[]const u8,
    mod_name: []const u8,
    is_mod_cx: bool,
) ![]u8 {
    const has_dir = dir_path.len > 0 and !std.mem.eql(u8, dir_path, ".");
    const suffix = if (is_mod_cx) "/mod.cx" else ".cx";
    if (stem_opt) |stem_str| {
        if (has_dir) {
            return std.fmt.allocPrint(allocator, "{s}/{s}/{s}{s}", .{ dir_path, stem_str, mod_name, suffix });
        }
        return std.fmt.allocPrint(allocator, "{s}/{s}{s}", .{ stem_str, mod_name, suffix });
    }
    if (has_dir) {
        return std.fmt.allocPrint(allocator, "{s}/{s}{s}", .{ dir_path, mod_name, suffix });
    }
    return std.fmt.allocPrint(allocator, "{s}{s}", .{ mod_name, suffix });
}

/// Recursively discovers and binds external `mod <name>;` `.cx` files on disk into `source_map` and `db`.
fn discoverExternalSubmodulesInDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs_sourcemap.VfsSourceMap,
    db: *CompilerDb,
    parent_fid: FileId,
    parent_path: []const u8,
    durability: query_db.Durability,
    pkg_id: vfs_sourcemap.PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    has_core_mention_out: *bool,
    depth: u32,
) !void {
    if (depth >= MAX_UPGRADE_MOD_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return;
    try visited_fids.put(allocator, parent_fid.asInt(), {});

    if (!db.source_inputs.contains(parent_fid.asInt())) {
        _ = source_map.getLineIndex(parent_fid) catch {};
        const disk_src = source_map.getFileSource(parent_fid) orelse "";
        _ = try db.setInput(parent_fid, disk_src, durability);
    }
    const parent_src = try db.getSourceText(parent_fid);
    if (!has_core_mention_out.* and
        (std.mem.indexOf(u8, parent_src, "cx") != null or
            std.mem.indexOf(u8, parent_src, "core") != null or
            std.mem.indexOf(u8, parent_src, "std") != null))
    {
        has_core_mention_out.* = true;
    }
    try db.setFilePath(parent_fid, parent_path);
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
            for (cand_paths) |maybe_path| {
                if (maybe_path) |owned_path| allocator.free(owned_path);
            }
        }
        var cand_len: usize = 0;
        if (!is_hub_file) {
            cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(
                allocator,
                parent_dir,
                parent_stem,
                mod_name,
                false,
            );
            cand_len += 1;
            cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(
                allocator,
                parent_dir,
                parent_stem,
                mod_name,
                true,
            );
            cand_len += 1;
        }
        cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(allocator, parent_dir, null, mod_name, false);
        cand_len += 1;
        cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(allocator, parent_dir, null, mod_name, true);
        cand_len += 1;

        var idx: usize = 0;
        while (idx < cand_len) : (idx += 1) {
            const cand_str = cand_paths[idx].?;
            if (source_map.resolveOrCreatePath(io, cand_str, pkg_id)) |child_fid| {
                if (child_fid == parent_fid) continue;
                try db.bindExternalModule(parent_fid, mod_name, child_fid);
                try discoverExternalSubmodulesInDb(
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

/// Recursively discovers and binds `mod <name>;` submodules inside a mounted virtual `/cx/<pkg>@<ver>/…` `.cxtree`.
fn discoverVirtualCxTreeSubmodulesInDb(
    allocator: std.mem.Allocator,
    source_map: *vfs_sourcemap.VfsSourceMap,
    db: *CompilerDb,
    parent_fid: FileId,
    parent_vpath: []const u8,
    pkg_id: vfs_sourcemap.PackageId,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    has_core_mention_out: *bool,
    depth: u32,
) !void {
    if (depth >= MAX_UPGRADE_MOD_DISCOVERY_DEPTH or visited_fids.contains(parent_fid.asInt())) return;
    try visited_fids.put(allocator, parent_fid.asInt(), {});

    const parent_src = source_map.faultCxTreeFile(parent_fid) catch return;
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
            for (cand_paths) |maybe_path| {
                if (maybe_path) |owned_path| allocator.free(owned_path);
            }
        }
        var cand_len: usize = 0;
        if (!is_hub_file) {
            cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(
                allocator,
                parent_dir,
                parent_stem,
                mod_name,
                false,
            );
            cand_len += 1;
            cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(
                allocator,
                parent_dir,
                parent_stem,
                mod_name,
                true,
            );
            cand_len += 1;
        }
        cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(allocator, parent_dir, null, mod_name, false);
        cand_len += 1;
        cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(allocator, parent_dir, null, mod_name, true);
        cand_len += 1;

        var idx: usize = 0;
        while (idx < cand_len) : (idx += 1) {
            const cand_vpath = cand_paths[idx].?;
            const vpath_id = source_map.interner.lookup(cand_vpath) orelse continue;
            const child_fid = source_map.path_to_file_id.get(vpath_id) orelse continue;
            try db.bindExternalModule(parent_fid, mod_name, child_fid);
            try discoverVirtualCxTreeSubmodulesInDb(
                allocator,
                source_map,
                db,
                child_fid,
                cand_vpath,
                pkg_id,
                visited_fids,
                has_core_mention_out,
                depth + 1,
            );
            break;
        }
    }
}

/// Registers `core/root.cx` (and its `core/` submodule tree) on `db` as `"core"` and `"cx"` when present on disk.
fn registerCoreStdlibInDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs_sourcemap.VfsSourceMap,
    db: *CompilerDb,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    const core_root_path = "core/root.cx";
    const core_fid = source_map.resolveOrCreatePath(io, core_root_path, .std_core) catch return;
    var has_dummy_core_mention = true;
    try discoverExternalSubmodulesInDb(
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

/// Re-binds external `mod <name>;` edges across all `.root` files in `db` after Tier 1/2 syntax healing.
fn rebindWorkspaceSubmodulesInDb(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    options: UpgradeOptions,
) !void {
    if (db.file_paths.count() == 0) return;

    const RootPathEntry = struct {
        fid: FileId,
        norm_path: []u8,
    };

    var root_entries: std.ArrayListUnmanaged(RootPathEntry) = .empty;
    defer {
        for (root_entries.items) |entry| allocator.free(entry.norm_path);
        root_entries.deinit(allocator);
    }
    var norm_to_fid: std.StringHashMapUnmanaged(FileId) = .empty;
    defer norm_to_fid.deinit(allocator);

    var has_core_mention = false;
    var fp_it = db.file_paths.iterator();
    while (fp_it.next()) |fp_kv| {
        const fid = FileId.fromInt(fp_kv.key_ptr.*);
        if (fid.isNone() or fid.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) continue;
        if (db.getFilePackageId(fid) != .root or db.isStdlibFile(fid)) continue;
        if (!db.source_inputs.contains(fid.asInt())) continue;

        const norm_p = try normalizeModLookupPathAlloc(allocator, fp_kv.value_ptr.*);
        errdefer allocator.free(norm_p);
        try root_entries.append(allocator, .{ .fid = fid, .norm_path = norm_p });
        try norm_to_fid.put(allocator, norm_p, fid);

        if (!has_core_mention) {
            const src_text = try db.getSourceText(fid);
            if (std.mem.indexOf(u8, src_text, "cx") != null or std.mem.indexOf(u8, src_text, "core") != null) {
                has_core_mention = true;
            }
        }
    }

    if (has_core_mention) {
        if (options.io) |io_val| {
            if (options.vfs) |vfs_ptr| {
                const cx_sym = try db.interner.intern("cx");
                if (!db.root_module_files.contains(cx_sym.asInt())) {
                    var core_visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
                    defer core_visited.deinit(allocator);
                    try registerCoreStdlibInDb(allocator, io_val, vfs_ptr, db, &core_visited);
                }
            }
        }
    }

    var on_disk_visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer on_disk_visited.deinit(allocator);

    for (root_entries.items) |root_item| {
        const parent_fid = root_item.fid;
        const parent_path = root_item.norm_path;

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
        if (ext_mod_names.items.len == 0) continue;

        const parent_dir = std.fs.path.dirname(parent_path) orelse ".";
        const parent_base = std.fs.path.basename(parent_path);
        const parent_stem = std.fs.path.stem(parent_path);
        const is_hub_file = HUB_MODULE_BASENAME_SET.has(parent_base);

        for (ext_mod_names.items) |mod_name| {
            var cand_paths: [4]?[]u8 = @splat(null);
            defer {
                for (cand_paths) |maybe_path| {
                    if (maybe_path) |owned_path| allocator.free(owned_path);
                }
            }
            var cand_len: usize = 0;
            if (!is_hub_file) {
                cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(
                    allocator,
                    parent_dir,
                    parent_stem,
                    mod_name,
                    false,
                );
                cand_len += 1;
                cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(
                    allocator,
                    parent_dir,
                    parent_stem,
                    mod_name,
                    true,
                );
                cand_len += 1;
            }
            cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(allocator, parent_dir, null, mod_name, false);
            cand_len += 1;
            cand_paths[cand_len] = try formatSubmoduleCandidateAlloc(allocator, parent_dir, null, mod_name, true);
            cand_len += 1;

            var idx: usize = 0;
            while (idx < cand_len) : (idx += 1) {
                const cand_norm = cand_paths[idx].?;
                if (norm_to_fid.get(cand_norm)) |known_child_fid| {
                    if (known_child_fid != parent_fid) {
                        try db.bindExternalModule(parent_fid, mod_name, known_child_fid);
                        break;
                    }
                } else if (options.io != null and options.vfs != null) {
                    const io_val = options.io.?;
                    const vfs_ptr = options.vfs.?;
                    if (vfs_ptr.resolveOrCreatePath(io_val, cand_norm, .root)) |disk_child_fid| {
                        if (disk_child_fid != parent_fid) {
                            try db.bindExternalModule(parent_fid, mod_name, disk_child_fid);
                            var has_sub_core = false;
                            try discoverExternalSubmodulesInDb(
                                allocator,
                                io_val,
                                vfs_ptr,
                                db,
                                disk_child_fid,
                                cand_norm,
                                .low,
                                .root,
                                &on_disk_visited,
                                &has_sub_core,
                                1,
                            );
                            if (has_sub_core) {
                                const cx_sym = try db.interner.intern("cx");
                                if (!db.root_module_files.contains(cx_sym.asInt())) {
                                    try registerCoreStdlibInDb(allocator, io_val, vfs_ptr, db, &on_disk_visited);
                                }
                            }
                            break;
                        }
                    } else |_| {}
                }
            }
        }
    }
}

/// Best-effort mounts offline cached `.cxtree`, local `path`, and `workspace_member` dependencies from `toml_path`.
fn mountOfflineManifestDepsInDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs_sourcemap.VfsSourceMap,
    db: *CompilerDb,
    toml_path: []const u8,
    options: UpgradeOptions,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
    has_core_mention_out: *bool,
) !void {
    const active_target = options.target_spec orelse codegen_abi.TargetSpec.host();
    const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(active_target, true);

    var local_sink = DiagnosticSink.init(allocator);
    defer local_sink.deinit();

    const toml_fid = source_map.resolveOrCreatePath(io, toml_path, .root) catch return;
    var bundle = loadUpgradedWorkspaceManifestBundle(
        io,
        allocator,
        source_map.interner,
        toml_path,
        toml_fid,
        &cfg_env,
        null,
    ) catch return;
    defer bundle.deinit();

    const ws_dir = std.fs.path.dirname(toml_path) orelse ".";
    const lock_path = try std.fs.path.join(allocator, &.{ ws_dir, "corex.lock" });
    defer allocator.free(lock_path);

    var lock_arena = BumpArena.init(allocator);
    defer lock_arena.deinit();
    var parsed_lock_opt: ?pkg_manifest.Lockfile = null;
    if (std.Io.Dir.cwd().readFileAlloc(io, lock_path, allocator, .limited(pkg_manifest.MAX_TOML_BYTES))) |lock_bytes| {
        defer allocator.free(lock_bytes);
        const lock_fid = source_map.setOverlay(lock_path, lock_bytes, .root) catch FileId.fromInt(2);
        parsed_lock_opt = pkg_manifest.parseLockfile(
            allocator,
            &lock_arena,
            source_map.interner,
            lock_fid,
            lock_bytes,
            null,
            null,
        ) catch null;
    } else |_| {}

    var resolved = (pkg_resolver.resolveProjectGraph(
        allocator,
        source_map.interner,
        source_map,
        &bundle,
        if (parsed_lock_opt) |*parsed_lock| parsed_lock else null,
        .{
            .io = io,
            .target_spec = active_target,
            .is_including_tests = true,
            .is_offline = true,
            .corex_home_dir = options.corex_home_dir orelse "",
            .environ_map = options.environ_map,
        },
        &local_sink,
    ) catch return) orelse return;
    defer resolved.deinit(allocator);

    if (resolved.packages.len <= 1) return;

    var cache_opt: ?pkg_cache.PkgCache = if (options.corex_home_dir) |home_dir|
        pkg_cache.PkgCache.init(
            allocator,
            home_dir,
            pkg_cache.DEFAULT_MAX_LRU_ENTRIES,
            pkg_cache.DEFAULT_MAX_LRU_BYTES,
        ) catch null
    else
        null;
    defer if (cache_opt) |*cache_inst| cache_inst.deinit();

    const blobs_dir_opt: ?[]u8 = if (cache_opt) |cache_inst|
        try std.fmt.allocPrint(allocator, "{s}/blobs", .{cache_inst.cas_root})
    else
        null;
    defer if (blobs_dir_opt) |blobs_buf| allocator.free(blobs_buf);

    var pkg_root_fids: std.AutoHashMapUnmanaged(vfs_sourcemap.PackageId, FileId) = .empty;
    defer pkg_root_fids.deinit(allocator);

    for (resolved.packages) |pkg_node| {
        if (pkg_node.pkg_id == .root or pkg_node.pkg_id == .std_core) continue;

        const ver_str = try pkg_node.version.formatAlloc(allocator, source_map.interner);
        defer allocator.free(ver_str);

        if (pkg_node.source_kind != .workspace_member and pkg_node.source_kind != .local_path) {
            const cache_ptr = if (cache_opt) |*c_ref| c_ref else continue;
            const blobs_dir = blobs_dir_opt orelse continue;
            const cxtree_hash = pkg_node.cxtree_blake3 orelse continue;
            const cxtree_bytes = cache_ptr.readVerifiedCxTreeAlloc(
                io,
                cxtree_hash,
                &local_sink,
                pkg_node.manifest_span,
            ) catch continue;
            defer allocator.free(cxtree_bytes);

            const mounted_ids = source_map.mountCxTreePackage(
                io,
                pkg_node.pkg_id,
                pkg_node.canonical_name,
                ver_str,
                cxtree_bytes,
                blobs_dir,
            ) catch continue;
            allocator.free(mounted_ids);

            const entry_rel = pkg_node.lib_root_rel_path orelse pkg_node.bin_root_rel_path orelse "src/root.cx";
            const entry_vpath = try std.fmt.allocPrint(
                allocator,
                "/cx/{s}@{s}/{s}",
                .{ pkg_node.canonical_name, ver_str, entry_rel },
            );
            defer allocator.free(entry_vpath);
            const vpath_id = source_map.interner.lookup(entry_vpath) orelse continue;
            const dep_root_fid = source_map.path_to_file_id.get(vpath_id) orelse continue;
            try discoverVirtualCxTreeSubmodulesInDb(
                allocator,
                source_map,
                db,
                dep_root_fid,
                entry_vpath,
                pkg_node.pkg_id,
                visited_fids,
                has_core_mention_out,
                0,
            );
            try pkg_root_fids.put(allocator, pkg_node.pkg_id, dep_root_fid);
        } else {
            if (pkg_node.package_root_path.len == 0) continue;
            const entry_rel = pkg_node.lib_root_rel_path orelse pkg_node.bin_root_rel_path orelse "src/root.cx";
            const entry_path = try std.fs.path.join(allocator, &.{ pkg_node.package_root_path, entry_rel });
            defer allocator.free(entry_path);
            const dep_root_fid = source_map.resolveOrCreatePath(io, entry_path, pkg_node.pkg_id) catch continue;
            try discoverExternalSubmodulesInDb(
                allocator,
                io,
                source_map,
                db,
                dep_root_fid,
                entry_path,
                .medium,
                pkg_node.pkg_id,
                visited_fids,
                has_core_mention_out,
                0,
            );
            try pkg_root_fids.put(allocator, pkg_node.pkg_id, dep_root_fid);
        }
        try db.symbol_table.markPackageDepsConfigured(pkg_node.pkg_id);
    }

    if (pkg_root_fids.count() == 0) return;

    for (resolved.packages) |pkg_node| {
        for (pkg_node.dependencies) |dep_bind| {
            const target_fid = pkg_root_fids.get(dep_bind.target_pkg_id) orelse continue;
            try db.bindPackageDepFile(pkg_node.pkg_id, try db.interner.intern(dep_bind.alias_text), target_fid);
        }
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

// --------------- Rule Discovery & CLI Rendering ---------------

/// Returns the single-bit mask (`1 << @intFromEnum(rule_id)`) for `rule_id`.
pub inline fn toRuleBit(rule_id: UpgradeRuleId) u16 {
    return @as(u16, 1) << @intCast(rule_id.asInt());
}

/// Returns `true` if `rule_id` is enabled in `rule_mask`.
pub inline fn isRuleEnabled(rule_mask: u16, rule_id: UpgradeRuleId) bool {
    return (rule_mask & toRuleBit(rule_id)) != 0;
}

/// Parses a comma-separated `--rule=UR-21-00,UR-22-06` specification into a `rule_mask` (`null` on unknown rule).
pub fn parseRuleFilterMask(raw_csv: []const u8) ?u16 {
    const trimmed = std.mem.trim(u8, raw_csv, " \t");
    if (trimmed.len == 0) return null;
    var mask: u16 = 0;
    var iter = std.mem.splitScalar(u8, trimmed, ',');
    while (iter.next()) |part| {
        const code = std.mem.trim(u8, part, " \t");
        if (code.len == 0) return null;
        const rule_id = upgrade_rules.lookupUpgradeRule(code) orelse return null;
        mask |= toRuleBit(rule_id);
    }
    return mask;
}

/// Parses `--accept-caps` (`null` -> `LOCKFILE_CAP_BITS`) or `--accept-caps=net,unsafe_op` (`null` on invalid cap).
pub fn parseAcceptCapsFilter(raw_value: ?[]const u8) ?u16 {
    const csv = raw_value orelse return EffectCapabilityMask.LOCKFILE_CAP_BITS;
    const trimmed = std.mem.trim(u8, csv, " \t");
    if (trimmed.len == 0) return null;
    var bits: u16 = 0;
    var iter = std.mem.splitScalar(u8, trimmed, ',');
    while (iter.next()) |part| {
        const cap_name = std.mem.trim(u8, part, " \t");
        if (cap_name.len == 0) return null;
        const canonical_name = RETIRED_CAP_ALIAS_MAP.get(cap_name) orelse cap_name;
        const cap_bit = pkg_manifest.MANIFEST_CAPABILITY_MAP.get(canonical_name) orelse return null;
        if ((cap_bit & EffectCapabilityMask.LOCKFILE_CAP_BITS) == 0) return null;
        bits |= cap_bit;
    }
    return bits;
}

/// Formats `cap_bits` as a comma-separated canonical capability list (`"fs, net, unsafe_op"`).
pub fn formatCapabilityMaskList(allocator: std.mem.Allocator, cap_bits: u16) ![]u8 {
    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);
    var is_first = true;
    for (CANONICAL_LOCKFILE_CAP_TABLE) |entry| {
        if ((cap_bits & entry.bit) != 0) {
            if (!is_first) try out.appendSlice(allocator, ", ");
            is_first = false;
            try out.appendSlice(allocator, entry.name);
        }
    }
    return out.toOwnedSlice(allocator);
}

/// Inspects leading comments (`<= 4096` bytes) and returns `true` if `@generated` or `DO NOT EDIT` is present.
pub const isGeneratedSourceHeader = check_audit.isGeneratedSourceHeader;

/// Renders the monochrome Unicode box-drawing table of all 15 canonical `UPGRADE_RULE_CATALOG` rules (`--list`).
pub fn renderUpgradeRuleList(
    allocator: std.mem.Allocator,
    writer: *std.Io.Writer,
    style_config: StyleConfig,
) !void {
    const columns = [_]TableColumn{
        .{ .header = "Rule", .alignment = .left },
        .{ .header = "Tier", .alignment = .left },
        .{ .header = "Wave", .alignment = .left },
        .{ .header = "Mandatory", .alignment = .left },
        .{ .header = "Summary", .alignment = .left },
    };

    var cell_matrix: [upgrade_rules.UPGRADE_RULE_COUNT][5][]const u8 = undefined;
    const row_slices = try allocator.alloc([]const []const u8, upgrade_rules.UPGRADE_RULE_CATALOG.len);
    defer allocator.free(row_slices);

    for (upgrade_rules.UPGRADE_RULE_CATALOG, 0..) |entry, i| {
        cell_matrix[i] = .{
            entry.rule_code,
            entry.tier.asLabel(),
            entry.wave.asSpecCode(),
            if (entry.is_mandatory_syntax) "yes" else "no",
            entry.summary,
        };
        row_slices[i] = &cell_matrix[i];
    }

    try TableRenderer.init(style_config).renderTable(writer, &columns, row_slices);
    try style_config.writeStyled(writer, .success, Glyphs.SUCCESS);
    try writer.print(" {d} canonical Zero-Legacy upgrade rules registered\n", .{
        upgrade_rules.UPGRADE_RULE_CATALOG.len,
    });
}

/// Renders a structured monochrome card explaining `rule_id` with canonical `Before:` / `After:` `.cx` blocks.
pub fn renderUpgradeRuleExplanation(
    allocator: std.mem.Allocator,
    writer: *std.Io.Writer,
    style_config: StyleConfig,
    rule_id: UpgradeRuleId,
) !void {
    const descriptor = rule_id.asDescriptor();
    const example = UPGRADE_RULE_EXAMPLES[rule_id.asInt()];

    const title_line = try std.fmt.allocPrint(
        allocator,
        "{s} {s} {s} ({s})",
        .{ descriptor.rule_code, Glyphs.BULLET, descriptor.tier.asLabel(), descriptor.wave.asSpecCode() },
    );
    defer allocator.free(title_line);

    var owned_lines: std.ArrayListUnmanaged([]u8) = .empty;
    defer {
        for (owned_lines.items) |buf| allocator.free(buf);
        owned_lines.deinit(allocator);
    }
    var card_lines: std.ArrayListUnmanaged([]const u8) = .empty;
    defer card_lines.deinit(allocator);

    try appendFmtLine(allocator, &owned_lines, &card_lines, "Rule:        {s}", .{descriptor.rule_code});
    try appendFmtLine(allocator, &owned_lines, &card_lines, "Tier:        {s}", .{descriptor.tier.asLabel()});
    try appendFmtLine(allocator, &owned_lines, &card_lines, "Wave:        {s}", .{descriptor.wave.asSpecCode()});
    try appendFmtLine(
        allocator,
        &owned_lines,
        &card_lines,
        "Mandatory:   {s}",
        .{if (descriptor.is_mandatory_syntax) "yes (retired syntax)" else "no (idiom modernizer)"},
    );
    if (descriptor.related_diagnostic) |diag_code| {
        const diag_desc = diag_code.asDescriptor();
        try appendFmtLine(
            allocator,
            &owned_lines,
            &card_lines,
            "Diagnostic:  {s} ({s})",
            .{ diag_desc.code_str, diag_desc.title },
        );
    } else {
        try card_lines.append(allocator, "Diagnostic:  none (semantic idiom modernizer)");
    }
    try appendFmtLine(allocator, &owned_lines, &card_lines, "Summary:     {s}", .{descriptor.summary});
    try appendFmtLine(allocator, &owned_lines, &card_lines, "Explanation: {s}", .{example.explanation});
    try card_lines.append(allocator, "");
    try card_lines.append(allocator, "Before:");
    var before_it = std.mem.splitScalar(u8, example.before_cx, '\n');
    while (before_it.next()) |b_line| {
        try appendFmtLine(allocator, &owned_lines, &card_lines, "  {s}", .{b_line});
    }
    try card_lines.append(allocator, "");
    try card_lines.append(allocator, "After:");
    var after_it = std.mem.splitScalar(u8, example.after_cx, '\n');
    while (after_it.next()) |a_line| {
        try appendFmtLine(allocator, &owned_lines, &card_lines, "  {s}", .{a_line});
    }

    try CardRenderer.init(style_config).renderCard(writer, title_line, card_lines.items);
}

// ---------------- Source & Workspace Upgraders ----------------

/// Upgrades all registered workspace `.cx` `file_ids` in `db` across `0..MAX_SYNERGY_PASSES` with cross-file Tier 3 resolution.
pub fn upgradeWorkspaceFilesInDb(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_ids: []const FileId,
    options: UpgradeOptions,
) ![]FileUpgradeResult {
    const results = try allocator.alloc(FileUpgradeResult, file_ids.len);
    var initialized_count: usize = 0;
    errdefer {
        var i: usize = 0;
        while (i < initialized_count) : (i += 1) results[i].deinit(allocator);
        allocator.free(results);
    }

    if (file_ids.len == 0) return results;

    try db.setInternalCore(options.is_internal_core);
    db.setIncludeTests(true);
    db.setComptimeStepLimit(options.comptime_step_limit);
    if (options.target_spec) |explicit_target| {
        db.setTargetSpec(explicit_target);
    }
    const cfg_env = pkg_manifest.CfgEnv.fromTargetSpec(db.target_spec, true);

    var states = try allocator.alloc(PerFileState, file_ids.len);
    var states_init: usize = 0;
    defer {
        var s_i: usize = 0;
        while (s_i < states_init) : (s_i += 1) {
            allocator.free(states[s_i].original_full);
            if (states[s_i].canonical_fm_prefix) |fm_p| allocator.free(fm_p);
            allocator.free(states[s_i].working_masked_cx);
        }
        allocator.free(states);
    }

    // [1] Initialize per-file baseline buffers, generated-file guards, and script frontmatter masks:
    for (file_ids, 0..) |fid, i| {
        const raw_src = try db.getSourceText(fid);
        const orig_copy = try allocator.dupe(u8, raw_src);
        errdefer allocator.free(orig_copy);

        const is_gen = isGeneratedSourceHeader(orig_copy);
        var fm_arena = BumpArena.init(allocator);
        defer fm_arena.deinit();
        const fm_opt = if (!is_gen)
            try pkg_manifest.extractScriptFrontmatter(&fm_arena, fid, orig_copy, null)
        else
            null;

        var fm_prefix_len: usize = 0;
        var canon_fm: ?[]u8 = null;
        errdefer if (canon_fm) |fm_buf| allocator.free(fm_buf);
        if (fm_opt) |extracted| {
            fm_prefix_len = extracted.prefix_end_byte;
            if (!options.has_explicit_rule_filter) {
                canon_fm = try canonicalizeScriptFrontmatterPrefix(
                    allocator,
                    fid,
                    orig_copy,
                    fm_prefix_len,
                    &cfg_env,
                );
            } else {
                canon_fm = try allocator.dupe(u8, orig_copy[0..fm_prefix_len]);
            }
        }

        const masked_copy = try allocator.dupe(u8, orig_copy);
        errdefer allocator.free(masked_copy);
        if (fm_prefix_len > 0) {
            maskFrontmatterBytesInPlace(masked_copy, fm_prefix_len);
        }
        const base_errs = if (is_gen) 0 else try countSyntaxErrors(allocator, fid, masked_copy);

        states[i] = .{
            .original_full = orig_copy,
            .canonical_fm_prefix = canon_fm,
            .fm_prefix_len = fm_prefix_len,
            .working_masked_cx = masked_copy,
            .baseline_syntax_errors = base_errs,
            .is_generated = is_gen,
        };
        states_init += 1;
    }

    // [2] Bounded multi-pass synergy loop (`0 .. MAX_SYNERGY_PASSES = 4`):
    var pass: u8 = 0;
    while (pass < MAX_SYNERGY_PASSES) : (pass += 1) {
        var has_changed_in_pass = false;

        // Sub-stage A (Tier 1 Pre-CST Lexeme Shims – immediate in-memory heal):
        for (file_ids, 0..) |fid, i| {
            if (states[i].is_generated) continue;
            var patch_interner = try StringInterner.init(allocator);
            defer patch_interner.deinit();
            var collector = FixCollector.init(allocator, &patch_interner, fid);
            defer collector.deinit();

            try collectSubstageATier1Fixes(allocator, states[i].working_masked_cx, fid, options, &collector);
            const applied_a = try applyCollectedFixesInMemory(allocator, &states[i].working_masked_cx, &collector);
            if (applied_a > 0) {
                states[i].edits_applied += applied_a;
                has_changed_in_pass = true;
            }
        }

        // Sub-stage B (Tier 2 Lossless CST/AST Structural Rewrites – immediate in-memory heal):
        for (file_ids, 0..) |fid, i| {
            if (states[i].is_generated) continue;
            var patch_interner = try StringInterner.init(allocator);
            defer patch_interner.deinit();
            var collector = FixCollector.init(allocator, &patch_interner, fid);
            defer collector.deinit();

            try collectSubstageBTier2Fixes(allocator, states[i].working_masked_cx, fid, options, &collector);
            const applied_b = try applyCollectedFixesInMemory(allocator, &states[i].working_masked_cx, &collector);
            if (applied_b > 0) {
                states[i].edits_applied += applied_b;
                has_changed_in_pass = true;
            }
        }

        // Sync healed buffers into `CompilerDb` and re-bind `mod <name>;` edges before Sub-stage C:
        for (file_ids, 0..) |fid, i| {
            if (states[i].is_generated) continue;
            _ = try db.setInput(fid, states[i].working_masked_cx, .low);
        }
        try rebindWorkspaceSubmodulesInDb(allocator, db, options);

        // Sub-stage C (Tier 3 Type-Directed Semantic Modernizers across `CompilerDb`):
        for (file_ids, 0..) |fid, i| {
            if (states[i].is_generated) continue;
            var patch_interner = try StringInterner.init(allocator);
            defer patch_interner.deinit();
            var collector = FixCollector.init(allocator, &patch_interner, fid);
            defer collector.deinit();

            try collectSubstageCTier3FixesForFile(allocator, db, fid, options, &collector);
            const applied_c = try applyCollectedFixesInMemory(allocator, &states[i].working_masked_cx, &collector);
            if (applied_c > 0) {
                states[i].edits_applied += applied_c;
                has_changed_in_pass = true;
            }
        }

        for (0..file_ids.len) |i| {
            if (!states[i].is_generated) states[i].passes_run = pass + 1;
        }
        if (!has_changed_in_pass) break;
    }

    // [3] Re-attach canonicalized frontmatter, run `fmt_engine.formatSource` when appropriate, and enforce rollback guard:
    const is_running_full_fmt = !options.has_explicit_rule_filter or options.rule_mask == ALL_UPGRADE_RULES_MASK;
    for (file_ids, 0..) |fid, i| {
        const st = &states[i];
        if (st.is_generated) {
            results[i] = .{
                .upgraded_source = try allocator.dupe(u8, st.original_full),
                .is_changed = false,
                .is_skipped_generated = true,
                .passes_executed = 0,
                .applied_edit_count = 0,
                .is_rolled_back = false,
            };
            initialized_count += 1;
            continue;
        }

        const has_fm_changed = if (st.canonical_fm_prefix) |canon_fm|
            !std.mem.eql(u8, canon_fm, st.original_full[0..st.fm_prefix_len])
        else
            false;

        if (st.edits_applied == 0 and !has_fm_changed) {
            _ = try db.setInput(fid, st.original_full, .low);
            results[i] = .{
                .upgraded_source = try allocator.dupe(u8, st.original_full),
                .is_changed = false,
                .is_skipped_generated = false,
                .passes_executed = st.passes_run,
                .applied_edit_count = 0,
                .is_rolled_back = false,
            };
            initialized_count += 1;
            continue;
        }

        // Splice canonicalized script frontmatter prefix back onto the upgraded `.cx` body:
        var candidate_full = if (st.canonical_fm_prefix) |canon_fm| blk_splice: {
            const body_slice = if (st.fm_prefix_len <= st.working_masked_cx.len)
                st.working_masked_cx[st.fm_prefix_len..]
            else
                "";
            const joined = try allocator.alloc(u8, canon_fm.len + body_slice.len);
            @memcpy(joined[0..canon_fm.len], canon_fm);
            @memcpy(joined[canon_fm.len..], body_slice);
            break :blk_splice joined;
        } else try allocator.dupe(u8, st.working_masked_cx);
        errdefer allocator.free(candidate_full);

        // Run `fmt_engine.formatSource` on modified `.cx` buffers (skipped during partial `--rule` surgical runs):
        if (st.edits_applied > 0 and is_running_full_fmt) {
            var fmt_res = try fmt_engine.formatSource(allocator, candidate_full, fid);
            if (!fmt_res.has_syntax_errors) {
                allocator.free(candidate_full);
                candidate_full = fmt_res.formatted_text;
            } else {
                fmt_res.deinit(allocator);
            }
        }

        // Atomic soundness rollback guard; roll back if syntax error count increased vs baseline:
        const final_syntax_errors = try countSyntaxErrors(allocator, fid, candidate_full);
        if (final_syntax_errors > st.baseline_syntax_errors) {
            allocator.free(candidate_full);
            _ = try db.setInput(fid, st.original_full, .low);
            results[i] = .{
                .upgraded_source = try allocator.dupe(u8, st.original_full),
                .is_changed = false,
                .is_skipped_generated = false,
                .passes_executed = st.passes_run,
                .applied_edit_count = 0,
                .is_rolled_back = true,
            };
            initialized_count += 1;
            continue;
        }

        _ = try db.setInput(fid, candidate_full, .low);
        const is_diff = !std.mem.eql(u8, candidate_full, st.original_full);
        results[i] = .{
            .upgraded_source = candidate_full,
            .is_changed = is_diff,
            .is_skipped_generated = false,
            .passes_executed = st.passes_run,
            .applied_edit_count = st.edits_applied,
            .is_rolled_back = false,
        };
        initialized_count += 1;
    }

    return results;
}

/// Upgrades a standalone `.cx` source buffer using a fresh `CompilerDb` instance.
pub fn upgradeSource(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    options: UpgradeOptions,
) !FileUpgradeResult {
    if (isGeneratedSourceHeader(source)) {
        return .{
            .upgraded_source = try allocator.dupe(u8, source),
            .is_changed = false,
            .is_skipped_generated = true,
            .passes_executed = 0,
            .applied_edit_count = 0,
            .is_rolled_back = false,
        };
    }

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    _ = try db.setInput(file_id, source, .low);

    const batch = try upgradeWorkspaceFilesInDb(allocator, &db, &.{file_id}, options);
    defer allocator.free(batch);
    return batch[0];
}

// ---------------- Manifest & Capability Policy ----------------

/// Canonicalizes a `corex.toml` buffer (`kebab-case` names, `"unsafe_op"`, `@cfg` targets, `edition = "2026"`).
pub fn upgradeManifestToml(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    file_id: FileId,
    cfg_env: *const pkg_manifest.CfgEnv,
    options: UpgradeOptions,
) !ManifestUpgradeResult {
    if (options.has_explicit_rule_filter) {
        var arena = BumpArena.init(allocator);
        defer arena.deinit();
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var parsed = try pkg_manifest.parseManifest(
            allocator,
            &arena,
            &interner,
            file_id,
            source_bytes,
            cfg_env,
            null,
        );
        defer parsed.doc.deinit(allocator);
        return .{
            .upgraded_toml = try allocator.dupe(u8, source_bytes),
            .is_changed = false,
            .applied_edit_count = 0,
            .root_manifest_blake3 = parsed.manifest.root_manifest_blake3,
        };
    }

    var current = try allocator.dupe(u8, source_bytes);
    errdefer allocator.free(current);
    var total_applied: u32 = 0;

    var pass: u8 = 0;
    while (pass < MAX_SYNERGY_PASSES) : (pass += 1) {
        var arena = BumpArena.init(allocator);
        defer arena.deinit();
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var sink = DiagnosticSink.init(allocator);
        defer sink.deinit();

        var parsed = try pkg_manifest.parseManifest(
            allocator,
            &arena,
            &interner,
            file_id,
            current,
            cfg_env,
            &sink,
        );
        defer parsed.doc.deinit(allocator);

        var fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
        defer fixes.deinit(allocator);
        for (sink.diagnostics.items) |diag_item| {
            for (diag_item.suggestions) |sug| {
                if (sug.applicability == .machine_applicable) {
                    try fixes.append(allocator, sug);
                }
            }
        }
        try collectRetiredEditionTomlFixes(&arena, &interner, &parsed.doc, &fixes);
        if (fixes.items.len == 0) break;

        const patched = pkg_manifest.applyManifestFixesTransactionally(
            allocator,
            &parsed.doc,
            fixes.items,
            &interner,
        ) catch break;
        if (std.mem.eql(u8, current, patched)) {
            allocator.free(patched);
            break;
        }
        total_applied += @intCast(fixes.items.len);
        allocator.free(current);
        current = patched;
    }

    // Recompute normalized `root_manifest_blake3` on the final canonicalized `corex.toml`:
    var final_arena = BumpArena.init(allocator);
    defer final_arena.deinit();
    var final_interner = try StringInterner.init(allocator);
    defer final_interner.deinit();
    var final_parsed = try pkg_manifest.parseManifest(
        allocator,
        &final_arena,
        &final_interner,
        file_id,
        current,
        cfg_env,
        null,
    );
    defer final_parsed.doc.deinit(allocator);

    return .{
        .upgraded_toml = current,
        .is_changed = !std.mem.eql(u8, current, source_bytes),
        .applied_edit_count = total_applied,
        .root_manifest_blake3 = final_parsed.manifest.root_manifest_blake3,
    };
}

/// Loads a `WorkspaceManifestBundle` after healing any legacy `edition` / `"unsafe"` tokens in `root_manifest_path` in memory.
pub fn loadUpgradedWorkspaceManifestBundle(
    io: std.Io,
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    root_manifest_path: []const u8,
    root_file_id: FileId,
    cfg_env: *const pkg_manifest.CfgEnv,
    sink: ?*DiagnosticSink,
) !pkg_manifest.WorkspaceManifestBundle {
    const raw_toml = try std.Io.Dir.cwd().readFileAlloc(
        io,
        root_manifest_path,
        allocator,
        .limited(pkg_manifest.MAX_TOML_BYTES),
    );
    defer allocator.free(raw_toml);

    var upg_toml = try upgradeManifestToml(allocator, raw_toml, root_file_id, cfg_env, .{});
    defer upg_toml.deinit(allocator);

    if (!upg_toml.is_changed) {
        return pkg_manifest.loadWorkspaceManifestBundle(
            io,
            allocator,
            interner,
            root_manifest_path,
            root_file_id,
            cfg_env,
            sink,
        );
    }

    var single_arena = BumpArena.init(allocator);
    var should_free_single_arena = true;
    defer if (should_free_single_arena) single_arena.deinit();

    var parsed_upg = try pkg_manifest.parseManifest(
        allocator,
        &single_arena,
        interner,
        root_file_id,
        upg_toml.upgraded_toml,
        cfg_env,
        sink,
    );
    defer parsed_upg.doc.deinit(allocator);

    if (parsed_upg.manifest.workspace == null) {
        const root_dir_raw = std.fs.path.dirname(root_manifest_path) orelse ".";
        const owned_root = try single_arena.dupe(u8, root_dir_raw);
        const owned_path = try single_arena.dupe(u8, root_manifest_path);
        const members = try single_arena.allocSlice(pkg_manifest.WorkspaceMember, 1);
        members[0] = .{
            .rel_dir = ".",
            .abs_dir = owned_root,
            .manifest_path = owned_path,
            .manifest = parsed_upg.manifest,
            .is_default_member = true,
        };
        should_free_single_arena = false;
        return .{
            .arena = single_arena,
            .workspace_root_dir = owned_root,
            .root_manifest_path = owned_path,
            .root_manifest = parsed_upg.manifest,
            .members = members,
            .primary_member_index = 0,
            .is_script = false,
            .root_manifest_blake3 = parsed_upg.manifest.root_manifest_blake3,
        };
    }

    var ws_bundle = try pkg_manifest.loadWorkspaceManifestBundle(
        io,
        allocator,
        interner,
        root_manifest_path,
        root_file_id,
        cfg_env,
        null,
    );
    errdefer ws_bundle.deinit();

    var ws_parsed = try pkg_manifest.parseManifest(
        allocator,
        &ws_bundle.arena,
        interner,
        root_file_id,
        upg_toml.upgraded_toml,
        cfg_env,
        sink,
    );
    defer ws_parsed.doc.deinit(allocator);

    ws_bundle.root_manifest = ws_parsed.manifest;
    ws_bundle.root_manifest_blake3 = ws_parsed.manifest.root_manifest_blake3;
    if (ws_bundle.members.len > 0 and std.mem.eql(u8, ws_bundle.members[0].rel_dir, ".")) {
        const mut_members = try ws_bundle.arena.dupe(pkg_manifest.WorkspaceMember, ws_bundle.members);
        mut_members[0].manifest = ws_parsed.manifest;
        ws_bundle.members = mut_members;
    }
    return ws_bundle;
}

/// Evaluates `--accept-caps` against `corex.toml`, optional `corex.lock`, and `observed_caps` (`deny_caps` never overridden!).
pub fn evaluateAndApplyAcceptCaps(
    allocator: std.mem.Allocator,
    toml_file_id: FileId,
    toml_bytes: []const u8,
    lock_file_id: FileId,
    lock_bytes_opt: ?[]const u8,
    observed_caps: []const PackageObservedCaps,
    cfg_env: *const pkg_manifest.CfgEnv,
    accept_caps_filter_bits: u16,
) !AcceptCapsOutcome {
    var arena = BumpArena.init(allocator);
    defer arena.deinit();
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    var parsed_manifest = try pkg_manifest.parseManifest(
        allocator,
        &arena,
        &interner,
        toml_file_id,
        toml_bytes,
        cfg_env,
        null,
    );
    defer parsed_manifest.doc.deinit(allocator);
    const manifest = &parsed_manifest.manifest;

    var parsed_lock_opt: ?pkg_manifest.Lockfile = if (lock_bytes_opt) |lb|
        try pkg_manifest.parseLockfile(allocator, &arena, &interner, lock_file_id, lb, null, null)
    else
        null;
    var mutable_lock_pkgs: ?[]pkg_manifest.LockPackage = null;
    if (parsed_lock_opt) |*lock_init| {
        const dup_pkgs = try arena.dupe(pkg_manifest.LockPackage, lock_init.packages);
        lock_init.packages = dup_pkgs;
        mutable_lock_pkgs = dup_pkgs;
    }

    var accepted_by_pkg: std.StringHashMapUnmanaged(u16) = .empty;
    defer accepted_by_pkg.deinit(allocator);

    // [1] Verify `deny_caps` bans FIRST (`E0324` from `deny_caps` is NEVER overridden by `--accept-caps`!):
    for (observed_caps) |obs| {
        const actual_bits = obs.actual_surface_caps.asBits() & EffectCapabilityMask.LOCKFILE_CAP_BITS;
        var explicit_deny_bits: u16 = manifest.security.deny_caps.asBits();
        var explicit_allow_opt: ?u16 = if (manifest.security.default_allow_caps) |def_allow|
            def_allow.asBits()
        else
            null;
        var is_using_global_default_allow = explicit_allow_opt != null;

        for (manifest.dependencies) |dep| {
            if (std.mem.eql(u8, interner.get(dep.package_kebab), obs.package_kebab) or
                std.mem.eql(u8, interner.get(dep.alias_kebab), obs.package_kebab))
            {
                explicit_deny_bits |= dep.deny_caps.asBits();
                if (dep.allow_caps) |dep_allow| {
                    explicit_allow_opt = dep_allow.asBits();
                    is_using_global_default_allow = false;
                }
            }
        }
        for (manifest.security.package_overrides) |pkg_ov| {
            if (std.mem.eql(u8, interner.get(pkg_ov.package_kebab), obs.package_kebab)) {
                explicit_deny_bits |= pkg_ov.deny_caps.asBits();
                if (pkg_ov.allow_caps) |ov_allow| {
                    explicit_allow_opt = ov_allow.asBits();
                    is_using_global_default_allow = false;
                }
            }
        }

        if ((actual_bits & explicit_deny_bits) != 0) {
            return .{
                .updated_toml = try allocator.dupe(u8, toml_bytes),
                .updated_lock = if (lock_bytes_opt) |lb| try allocator.dupe(u8, lb) else null,
                .has_denied_cap_violation = true,
                .offending_package = try allocator.dupe(u8, obs.package_kebab),
            };
        }

        // [2] Compute capability escalation `actual_surface_caps \ locked_or_allowed_caps`:
        var locked_bits: u16 = EffectCapabilityMask.LOCKFILE_CAP_BITS;
        if (parsed_lock_opt) |lock_view| {
            for (lock_view.packages) |lpkg| {
                if (std.mem.eql(u8, interner.get(lpkg.name), obs.package_kebab)) {
                    locked_bits = lpkg.max_caps.asBits();
                    break;
                }
            }
        }
        const allowed_ceiling = (explicit_allow_opt orelse EffectCapabilityMask.LOCKFILE_CAP_BITS) & locked_bits;
        const escalated_bits = actual_bits & ~allowed_ceiling;
        if (escalated_bits == 0) continue;

        const unaccepted_bits = escalated_bits & ~accept_caps_filter_bits;
        if (unaccepted_bits != 0) {
            return .{
                .updated_toml = try allocator.dupe(u8, toml_bytes),
                .updated_lock = if (lock_bytes_opt) |lb| try allocator.dupe(u8, lb) else null,
                .unaccepted_escalation_bits = unaccepted_bits,
                .offending_package = try allocator.dupe(u8, obs.package_kebab),
            };
        }

        // Record accepted capability bits for `allow_caps` TOML update and `LockPackage.max_caps`:
        if (explicit_allow_opt) |cur_allow| {
            if ((actual_bits & ~cur_allow) != 0) {
                const map_key = if (is_using_global_default_allow) "*" else obs.package_kebab;
                const gop = try accepted_by_pkg.getOrPut(allocator, map_key);
                gop.value_ptr.* = (if (gop.found_existing) gop.value_ptr.* else 0) | (actual_bits & ~cur_allow);
            }
        }
        if (mutable_lock_pkgs) |pkgs_mut| {
            for (pkgs_mut) |*lpkg_ptr| {
                if (std.mem.eql(u8, interner.get(lpkg_ptr.name), obs.package_kebab)) {
                    lpkg_ptr.max_caps = lpkg_ptr.max_caps.unionWith(EffectCapabilityMask.fromBits(escalated_bits));
                }
            }
        }
    }

    // [3] Apply any `allow_caps = […]` additions to `corex.toml` and recompute `root_manifest_blake3`:
    var updated_toml = try allocator.dupe(u8, toml_bytes);
    errdefer allocator.free(updated_toml);
    if (accepted_by_pkg.count() > 0) {
        var cap_fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
        defer cap_fixes.deinit(allocator);
        try collectManifestAllowCapsAppendFixes(
            allocator,
            &arena,
            &interner,
            &parsed_manifest.doc,
            &accepted_by_pkg,
            &cap_fixes,
        );
        if (cap_fixes.items.len > 0) {
            const patched_toml = try pkg_manifest.applyManifestFixesTransactionally(
                allocator,
                &parsed_manifest.doc,
                cap_fixes.items,
                &interner,
            );
            allocator.free(updated_toml);
            updated_toml = patched_toml;
        }
    }

    var updated_blake3 = manifest.root_manifest_blake3;
    if (!std.mem.eql(u8, updated_toml, toml_bytes)) {
        var re_arena = BumpArena.init(allocator);
        defer re_arena.deinit();
        var re_interner = try StringInterner.init(allocator);
        defer re_interner.deinit();
        var re_parsed = try pkg_manifest.parseManifest(
            allocator,
            &re_arena,
            &re_interner,
            toml_file_id,
            updated_toml,
            cfg_env,
            null,
        );
        defer re_parsed.doc.deinit(allocator);
        updated_blake3 = re_parsed.manifest.root_manifest_blake3;
    }

    // [4] Re-serialize `corex.lock` with updated `LockPackage.max_caps` and synchronized `root_manifest_blake3`:
    var updated_lock_opt: ?[]u8 = null;
    errdefer if (updated_lock_opt) |lb| allocator.free(lb);
    var is_lock_diff = false;
    if (parsed_lock_opt) |*lock_mut| {
        lock_mut.root_manifest_blake3 = updated_blake3;
        const serialized_lock = try pkg_manifest.serializeLockfile(allocator, lock_mut, &interner);
        is_lock_diff = if (lock_bytes_opt) |orig_lb| !std.mem.eql(u8, orig_lb, serialized_lock) else true;
        updated_lock_opt = serialized_lock;
    }

    return .{
        .updated_toml = updated_toml,
        .updated_lock = updated_lock_opt,
        .is_toml_changed = !std.mem.eql(u8, updated_toml, toml_bytes),
        .is_lock_changed = is_lock_diff,
    };
}

/// Renders the `--check` dry-run report and returns the CLI exit code (`0` when clean, `1` when pending migrations exist).
pub fn renderUpgradeCheckReport(
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
    stdout_style: StyleConfig,
    stderr_style: StyleConfig,
    pending_items: []const PendingUpgradeItem,
) !u8 {
    if (pending_items.len == 0) {
        try stdout_style.writeStatusHeader(
            stdout_writer,
            .success,
            Glyphs.SUCCESS,
            "upgrade --check",
            "all files conform to canonical CoreX 2026",
        );
        try stdout_writer.writeByte('\n');
        return 0;
    }

    for (pending_items) |item| {
        try stderr_style.writeStyled(stderr_writer, .err, Glyphs.FAILURE);
        try stderr_writer.writeByte(' ');
        try stderr_style.writeStyled(stderr_writer, .bold, "upgrade --check");
        try stderr_writer.print(": pending {s} migration in {s}\n", .{ item.kind.asLabel(), item.path });
    }
    return 1;
}

/// Renders an unaccepted or `deny_caps`-blocked capability escalation failure to `stderr_writer` (returns exit `1`).
pub fn renderCapabilityEscalationError(
    allocator: std.mem.Allocator,
    stderr_writer: *std.Io.Writer,
    stderr_style: StyleConfig,
    outcome: *const AcceptCapsOutcome,
) !u8 {
    if (outcome.has_denied_cap_violation) {
        try stderr_style.writeStyled(stderr_writer, .err, Glyphs.FAILURE);
        try stderr_writer.print(
            " error[E0324]: package `{s}` violates explicit `deny_caps` policy (`--accept-caps` never overrides `deny_caps`)\n",
            .{outcome.offending_package},
        );
        return 1;
    }
    const caps_str = try formatCapabilityMaskList(allocator, outcome.unaccepted_escalation_bits);
    defer allocator.free(caps_str);
    try stderr_style.writeStyled(stderr_writer, .err, Glyphs.FAILURE);
    try stderr_writer.print(
        " error[E0324]: unaccepted capability escalation in `{s}`: [{s}] (pass `--accept-caps={s}` to authorize)\n",
        .{ outcome.offending_package, caps_str, caps_str },
    );
    return 1;
}

/// Executes `corex upgrade` across disk `.cx` and `corex.toml` paths, honoring `--check` without writing to disk.
pub fn executeUpgradePaths(
    allocator: std.mem.Allocator,
    io: std.Io,
    cx_paths: []const []const u8,
    manifest_path_opt: ?[]const u8,
    options: UpgradeOptions,
    stdout_style: StyleConfig,
    stderr_style: StyleConfig,
    stdout_writer: *std.Io.Writer,
    stderr_writer: *std.Io.Writer,
) !u8 {
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var source_map = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
    defer source_map.deinit(io);
    source_map.setIo(io);

    var db = try CompilerDb.init(allocator);
    defer db.deinit();
    db.setVfsSourceMap(&source_map);
    db.setEmbedIo(io);
    if (options.is_internal_core) {
        try db.setInternalCore(true);
    }

    var pending_list: std.ArrayListUnmanaged(PendingUpgradeItem) = .empty;
    defer pending_list.deinit(allocator);
    var upgraded_cx_count: usize = 0;
    var upgraded_manifest_count: usize = 0;

    // [1] Load `.cx` workspace/file targets, bind `mod <name>;` submodules, stdlib `cx`, and offline dependencies:
    var loaded_fids: std.ArrayListUnmanaged(FileId) = .empty;
    defer loaded_fids.deinit(allocator);
    var loaded_paths: std.ArrayListUnmanaged([]const u8) = .empty;
    defer loaded_paths.deinit(allocator);

    var has_core_mention = false;
    for (cx_paths) |cx_path| {
        const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(io, cx_path, allocator, .limited(64 * 1024 * 1024));
        defer allocator.free(raw_bytes);
        if (!has_core_mention and
            (std.mem.indexOf(u8, raw_bytes, "cx") != null or
                std.mem.indexOf(u8, raw_bytes, "core") != null or
                std.mem.indexOf(u8, raw_bytes, "std") != null))
        {
            has_core_mention = true;
        }
        const fid = try source_map.setOverlay(cx_path, raw_bytes, .root);
        _ = try db.setInput(fid, raw_bytes, .low);
        try db.setFilePath(fid, cx_path);
        try loaded_fids.append(allocator, fid);
        try loaded_paths.append(allocator, cx_path);
    }

    if (loaded_fids.items.len > 0) {
        var visited_fids: std.AutoHashMapUnmanaged(u32, void) = .empty;
        defer visited_fids.deinit(allocator);

        if (manifest_path_opt) |toml_path| {
            try mountOfflineManifestDepsInDb(
                allocator,
                io,
                &source_map,
                &db,
                toml_path,
                options,
                &visited_fids,
                &has_core_mention,
            );
        }
        if (has_core_mention) {
            try registerCoreStdlibInDb(allocator, io, &source_map, &db, &visited_fids);
        }

        var ws_options = options;
        ws_options.io = io;
        ws_options.vfs = &source_map;
        try rebindWorkspaceSubmodulesInDb(allocator, &db, ws_options);

        const cx_results = try upgradeWorkspaceFilesInDb(allocator, &db, loaded_fids.items, ws_options);
        defer {
            for (cx_results) |*res| res.deinit(allocator);
            allocator.free(cx_results);
        }

        for (cx_results, loaded_paths.items) |res, path_str| {
            if (!res.is_changed) continue;
            if (options.is_check_only) {
                try pending_list.append(allocator, .{ .kind = .cx_source, .path = path_str });
            } else {
                try codegen_abi.writeArtifactAtomic(io, allocator, path_str, res.upgraded_source);
                upgraded_cx_count += 1;
            }
        }
    }

    // [2] Canonicalize `corex.toml` (and synchronize sibling `corex.lock` `root_manifest_blake3`) when present:
    if (manifest_path_opt) |toml_path| {
        if (!options.has_explicit_rule_filter) {
            const raw_toml = try std.Io.Dir.cwd().readFileAlloc(io, toml_path, allocator, .limited(16 * 1024 * 1024));
            defer allocator.free(raw_toml);
            const toml_fid = try source_map.setOverlay(toml_path, raw_toml, .root);
            const cfg_env = pkg_manifest.CfgEnv.fromTargetSpec(
                options.target_spec orelse codegen_abi.TargetSpec.host(),
                true,
            );
            var manifest_res = try upgradeManifestToml(allocator, raw_toml, toml_fid, &cfg_env, options);
            defer manifest_res.deinit(allocator);

            if (manifest_res.is_changed) {
                if (options.is_check_only) {
                    try pending_list.append(allocator, .{ .kind = .manifest_toml, .path = toml_path });
                } else {
                    try codegen_abi.writeArtifactAtomic(io, allocator, toml_path, manifest_res.upgraded_toml);
                    upgraded_manifest_count += 1;

                    const ws_dir = std.fs.path.dirname(toml_path) orelse ".";
                    const lock_path = try std.fs.path.join(allocator, &.{ ws_dir, "corex.lock" });
                    defer allocator.free(lock_path);
                    if (std.Io.Dir.cwd().readFileAlloc(
                        io,
                        lock_path,
                        allocator,
                        .limited(pkg_manifest.MAX_TOML_BYTES),
                    )) |lock_bytes| {
                        defer allocator.free(lock_bytes);
                        var lock_arena = BumpArena.init(allocator);
                        defer lock_arena.deinit();
                        var lock_interner = try StringInterner.init(allocator);
                        defer lock_interner.deinit();
                        var lock_sink = DiagnosticSink.init(allocator);
                        defer lock_sink.deinit();

                        if (pkg_manifest.parseLockfile(
                            allocator,
                            &lock_arena,
                            &lock_interner,
                            FileId.fromInt(2),
                            lock_bytes,
                            null,
                            &lock_sink,
                        )) |parsed_lock_opt| {
                            if (!lock_sink.hasErrors()) {
                                if (parsed_lock_opt) |lock_val| {
                                    var updated_lock = lock_val;
                                    updated_lock.root_manifest_blake3 = manifest_res.root_manifest_blake3;
                                    const new_lock_bytes = try pkg_manifest.serializeLockfile(
                                        allocator,
                                        &updated_lock,
                                        &lock_interner,
                                    );
                                    defer allocator.free(new_lock_bytes);
                                    if (!std.mem.eql(u8, lock_bytes, new_lock_bytes)) {
                                        try codegen_abi.writeArtifactAtomic(io, allocator, lock_path, new_lock_bytes);
                                    }
                                }
                            }
                        } else |_| {}
                    } else |_| {}
                }
            }
        }
    }

    if (options.is_check_only) {
        for (options.extra_pending_items) |extra_item| {
            var is_duplicate = false;
            for (pending_list.items) |existing_item| {
                if (existing_item.kind == extra_item.kind and std.mem.eql(u8, existing_item.path, extra_item.path)) {
                    is_duplicate = true;
                    break;
                }
            }
            if (!is_duplicate) {
                try pending_list.append(allocator, extra_item);
            }
        }
        return renderUpgradeCheckReport(
            stdout_writer,
            stderr_writer,
            stdout_style,
            stderr_style,
            pending_list.items,
        );
    }

    var summary_buf: [160]u8 = undefined;
    const summary_msg = std.fmt.bufPrint(
        &summary_buf,
        "upgraded {d} source file(s) and {d} manifest(s) to canonical CoreX 2026",
        .{ upgraded_cx_count, upgraded_manifest_count },
    ) catch "upgraded workspace to canonical CoreX 2026";
    try stdout_style.writeStatusHeader(stdout_writer, .success, Glyphs.SUCCESS, "upgrade", summary_msg);
    try stdout_writer.writeByte('\n');
    return 0;
}

// ---------------------------------------- MAIN -----------------------------------------

// ------------------------- Unit Tests -------------------------

test "test_is_generated_source_header_bounds_and_markers" {
    try std.testing.expect(isGeneratedSourceHeader("// Code @generated by prost. DO NOT EDIT.\npub struct Msg {}\n"));
    try std.testing.expect(isGeneratedSourceHeader("//! File DO NOT EDIT manually\nmod bindings;\n"));
    try std.testing.expect(isGeneratedSourceHeader("/* header\n * @generated\n */\npub fn init() {}\n"));
    try std.testing.expect(isGeneratedSourceHeader("#!/usr/bin/env corex\n// @generated\nfn main() {}\n"));
    try std.testing.expect(!isGeneratedSourceHeader("// Normal hand-authored module\npub fn check() {\n    // @generated inside body\n}\n"));

    // Verify marker past the 4096-byte header scan cap is ignored:
    var padded = try std.testing.allocator.alloc(u8, GENERATED_HEADER_SCAN_LIMIT + 128);
    defer std.testing.allocator.free(padded);
    @memset(padded, ' ');
    padded[0] = '/';
    padded[1] = '/';
    padded[GENERATED_HEADER_SCAN_LIMIT - 2] = '\n';
    const tail = "// @generated\nfn after_limit() {}\n";
    @memcpy(padded[GENERATED_HEADER_SCAN_LIMIT + 8 .. GENERATED_HEADER_SCAN_LIMIT + 8 + tail.len], tail);
    try std.testing.expect(!isGeneratedSourceHeader(padded));

    // Verify `upgradeSource` skips generated files with zero edits:
    const gen_legacy = "// @generated\nuse std::io;\nfn legacy() -> unit {}\n";
    var skipped_res = try upgradeSource(std.testing.allocator, gen_legacy, FileId.fromInt(1), .{});
    defer skipped_res.deinit(std.testing.allocator);
    try std.testing.expect(skipped_res.is_skipped_generated);
    try std.testing.expect(!skipped_res.is_changed);
    try std.testing.expectEqual(@as(u32, 0), skipped_res.applied_edit_count);
    try std.testing.expectEqualStrings(gen_legacy, skipped_res.upgraded_source);
}

test "test_render_upgrade_rule_list_and_all_15_explanations_zero_drift" {
    var list_buf: [16384]u8 = undefined;
    var list_writer = std.Io.Writer.fixed(&list_buf);
    try renderUpgradeRuleList(std.testing.allocator, &list_writer, StyleConfig.MONOCHROME);
    const list_text = list_writer.buffered();

    try std.testing.expect(!style.hasBannedEmoji(list_text));
    try std.testing.expect(std.mem.indexOf(u8, list_text, Glyphs.TOP_LEFT) != null);
    try std.testing.expect(std.mem.indexOf(u8, list_text, Glyphs.BOTTOM_RIGHT) != null);
    try std.testing.expect(
        std.mem.endsWith(u8, list_text, "✓ 15 canonical Zero-Legacy upgrade rules registered\n"),
    );

    for (upgrade_rules.UPGRADE_RULE_CATALOG) |entry| {
        try std.testing.expect(std.mem.indexOf(u8, list_text, entry.rule_code) != null);

        var card_buf: [8192]u8 = undefined;
        var card_writer = std.Io.Writer.fixed(&card_buf);
        try renderUpgradeRuleExplanation(std.testing.allocator, &card_writer, StyleConfig.MONOCHROME, entry.id);
        const card_text = card_writer.buffered();
        try std.testing.expect(!style.hasBannedEmoji(card_text));
        try std.testing.expect(std.mem.indexOf(u8, card_text, entry.rule_code) != null);
        try std.testing.expect(std.mem.indexOf(u8, card_text, "Before:") != null);
        try std.testing.expect(std.mem.indexOf(u8, card_text, "After:") != null);
    }
}

test "test_tier1_and_tier2_synergy_ur21_and_ur22_rewrites" {
    const legacy_cx =
        \\use std::io;
        \\use cx.ffi.c_void;
        \\
        \\extern "c" fn free_raw(ptr: *const c_void) -> unit;
        \\
        \\@repr(u8)
        \\pub enum Mode {
        \\    Read = 0;
        \\    Write = 1;
        \\}
        \\
        \\type RegFlags = bit_field u8 {
        \\    ready: bool | 1;
        \\    mode: u8 | 7;
        \\};
        \\
        \\pub struct Point {
        \\    pub x: i32;
        \\    pub y: i32;
        \\}
        \\
        \\@noalloc
        \\@align(bytes = 16)
        \\pub fn process[T: Numeric](
        \\    ref item: T,
        \\    inout count: i32,
        \\    set done: bool,
        \\    opt_ref: Option[&u8],
        \\    nested_res: Result[Result[u32, i32], i32],
        \\) -> unit {
        \\    let mut acc = count;
        \\    let escaped = "\{ok\} and \\{acc}";
        \\    let raw_lit = r"\{untouched\}";
        \\    if acc > 0 && (acc == 1 || acc == 2) {
        \\        let zero_clos = || acc;
        \\        let _ = zero_clos();
        \\    }
        \\    let maybe_pt: Point? = .None;
        \\    if let Point { x, y } = maybe_pt {
        \\        acc = x + y;
        \\    }
        \\    let maybe_v: i32? = .Some(4);
        \\    let .Some(mut unwrapped) = maybe_v else {
        \\        done = false;
        \\        return;
        \\    };
        \\    unwrapped += 1;
        \\    done = unwrapped > 0;
        \\}
        \\
        \\@test
        \\pub fn test_bitfield_and_modes() -> unit {
        \\    var val: i32 = 1;
        \\    var flag: bool = false;
        \\}
    ;

    var res = try upgradeSource(std.testing.allocator, legacy_cx, FileId.fromInt(10), .{});
    defer res.deinit(std.testing.allocator);

    try std.testing.expect(res.is_changed);
    try std.testing.expect(!res.is_rolled_back);
    const out = res.upgraded_source;

    // `UR-21-00` & `UR-22-05`:
    try std.testing.expect(std.mem.indexOf(u8, out, "use cx.io;") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "c_void") == null);
    try std.testing.expect(std.mem.indexOf(u8, out, "extern \"C\" fn free_raw(ptr: *opaque);") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "test \"bitfield and modes\" {") != null);

    // `UR-22-04` (`enum`, `bit_field` member preservation, `@attr(k: v)`, `,` fields, omit `-> unit`):
    try std.testing.expect(std.mem.indexOf(u8, out, "pub enum Mode: u8 {") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "bit_field RegFlags: u8 {") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "ready: bool | 1,") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "mode: u8 | 7,") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "@align(bytes: 16)") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "@no_alloc") != null);

    // `UR-22-00`, `UR-22-01`, `UR-22-02`, `UR-22-03`, `UR-21-01`, `UR-21-03`:
    try std.testing.expect(std.mem.indexOf(u8, out, "[T: Number]") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "item: &T") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "count: &mut i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "done: &out bool") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "opt_ref: (&u8)?") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "nested_res: (u32!i32)!i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "var acc = count;") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "\"{{ok}} and \\\\{acc}\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "r\"\\{untouched\\}\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "if acc > 0 and (acc == 1 or acc == 2)") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "let zero_clos = || acc;") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "if maybe_pt is (Point { x, y })") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "var unwrapped = maybe_v orelse {") != null);
}

test "test_tier3_semantic_modernizers_and_surgical_rule_filter" {
    const tier3_cx =
        \\pub struct Boxed[T] {
        \\    pub val: T,
        \\}
        \\
        \\impl[T] Boxed[T] {
        \\    pub fn wrap(val: T) -> Boxed[T] {
        \\        return Boxed[T] { val: val };
        \\    }
        \\}
        \\
        \\pub struct CustomLen {
        \\    pub len: usize,
        \\}
        \\
        \\pub struct OwnedHandle {
        \\    pub fd: i32,
        \\}
        \\
        \\impl Drop for OwnedHandle {
        \\    pub fn drop(&mut self) {}
        \\}
        \\
        \\pub fn consume_handle(mut handle: OwnedHandle) -> i32 {
        \\    return handle.fd;
        \\}
        \\
        \\pub fn modernize(
        \\    opt_a: i32?,
        \\    res_b: i32!i32,
        \\    data: &[u8],
        \\    mut_data: &mut [u8],
        \\    pp: **i32,
        \\    custom: CustomLen,
        \\    flag: bool,
        \\    mask: u32,
        \\) -> usize {
        \\    let boxed = Boxed.wrap[i32](7);
        \\    let a1 = opt_a.unwrap_or(0) + boxed.val;
        \\    let a2 = opt_a.unwrap();
        \\    let tail = data[0 .. data.len - 2];
        \\    let rw_p: *mut u8 = mut_data.ptr;
        \\    let ro_p: *u8 = data.ptr;
        \\    let _ = rw_p;
        \\    let _ = ro_p;
        \\    let deref_v = unsafe { **pp };
        \\    if !flag {
        \\        let inv = !mask;
        \\        return custom.len + (inv as usize) + (a1 as usize) + (a2 as usize) + (deref_v as usize) + (res_b catch 0 as usize);
        \\    }
        \\    return tail.len;
        \\}
    ;

    var res = try upgradeSource(std.testing.allocator, tier3_cx, FileId.fromInt(20), .{});
    defer res.deinit(std.testing.allocator);
    try std.testing.expect(res.is_changed);
    try std.testing.expect(!res.is_rolled_back);
    const out = res.upgraded_source;

    // `UR-22-02` Tier-3 `~Copy` completion (`mut handle: OwnedHandle` -> `var handle: own OwnedHandle`):
    try std.testing.expect(std.mem.indexOf(u8, out, "var handle: own OwnedHandle") != null);
    // `UR-21-04` (`Boxed.wrap[i32](7)` -> `Boxed[i32].wrap(7)`):
    try std.testing.expect(std.mem.indexOf(u8, out, "Boxed[i32].wrap(7)") != null);
    // `UR-21-05` (`(opt_a orelse 0) + boxed.val` and `opt_a orelse unreachable`):
    try std.testing.expect(std.mem.indexOf(u8, out, "(opt_a orelse 0) + boxed.val") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "opt_a orelse unreachable") != null);
    // `UR-21-07` (`data[0 .. data.len - 2]` -> `data[..$-2]` across multi-pass synergy with `UR-22-06`):
    try std.testing.expect(std.mem.indexOf(u8, out, "data[..$-2]") != null);
    // `UR-22-06` (`!flag` -> `not flag`, `!mask` -> `~mask`, `**pp` -> `pp.*.*`, `.ptr` & `.len`, `custom.len` preserved!):
    try std.testing.expect(std.mem.indexOf(u8, out, "mut_data.as_mut_ptr()") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "data.as_ptr()") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "pp.*.*") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "if not flag") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "~mask") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "custom.len") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "tail.len()") != null);

    // `UR-21-06` (`with_arena` without `return` upgrades; `with_arena` containing `return` is skipped) + `W0403`:
    const arena_and_dep_in =
        \\@deprecated(upgrade: "modern_inc($0)")
        \\pub fn legacy_inc(val: i32) -> i32 {
        \\    return modern_inc(val);
        \\}
        \\pub fn modern_inc(val: i32) -> i32 {
        \\    return val + 1;
        \\}
        \\pub fn run_arena(scratch: &mut i32) -> i32 {
        \\    cx.mem.with_arena(scratch, || {
        \\        let _ = 1;
        \\    });
        \\    cx.mem.with_arena(scratch, || {
        \\        return;
        \\    });
        \\    return legacy_inc(4);
        \\}
    ;
    var arena_dep_res = try upgradeSource(std.testing.allocator, arena_and_dep_in, FileId.fromInt(22), .{});
    defer arena_dep_res.deinit(std.testing.allocator);
    try std.testing.expect(
        std.mem.indexOf(u8, arena_dep_res.upgraded_source, "with context.allocator = scratch {") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, arena_dep_res.upgraded_source, "cx.mem.with_arena(") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, arena_dep_res.upgraded_source, "|| {\n            return;\n        }") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, arena_dep_res.upgraded_source, "return modern_inc(4);") != null,
    );

    // Script `---` TOML frontmatter canonicalization + `.cx` body upgrade:
    const script_in =
        \\---
        \\[dependencies]
        \\http_helper = "1.0.0"
        \\---
        \\use std::io;
        \\pub fn main() {}
    ++ "\n";
    var script_res = try upgradeSource(std.testing.allocator, script_in, FileId.fromInt(23), .{});
    defer script_res.deinit(std.testing.allocator);
    try std.testing.expect(std.mem.indexOf(u8, script_res.upgraded_source, "http-helper = \"1.0.0\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, script_res.upgraded_source, "use cx.io;") != null);

    // Surgical `--rule=UR-21-00` filter must NOT rewrite `Option[i32]` or `-> unit`:
    const surgical_in = "use std::io;\npub fn keep(x: Option[i32]) -> unit {}\n";
    const mask_only_21_00 = parseRuleFilterMask("UR-21-00").?;
    var surgical_res = try upgradeSource(std.testing.allocator, surgical_in, FileId.fromInt(21), .{
        .rule_mask = mask_only_21_00,
        .has_explicit_rule_filter = true,
    });
    defer surgical_res.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings("use cx.io;\npub fn keep(x: Option[i32]) -> unit {}\n", surgical_res.upgraded_source);
}

test "test_manifest_canonicalization_edition_2026_accept_caps_and_check_mode" {
    const raw_toml =
        \\[package]
        \\name = "my_legacy_app"
        \\version = "0.1.0"
        \\edition = "2024"
        \\corex = ">=0.1.0"
        \\
        \\[dependencies]
        \\net_client = { version = "1.2.0", target = "cfg(unix)", allow_caps = ["unsafe"] }
        \\
        \\[security]
        \\deny_caps = ["process"]
    ++ "\n";

    const cfg_env = pkg_manifest.CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.host(), true);
    var upg_toml = try upgradeManifestToml(
        std.testing.allocator,
        raw_toml,
        FileId.fromInt(30),
        &cfg_env,
        .{},
    );
    defer upg_toml.deinit(std.testing.allocator);

    try std.testing.expect(upg_toml.is_changed);
    try std.testing.expect(std.mem.indexOf(u8, upg_toml.upgraded_toml, "name = \"my-legacy-app\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, upg_toml.upgraded_toml, "edition = \"2026\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, upg_toml.upgraded_toml, "corex = \">=0.1.0\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, upg_toml.upgraded_toml, "net-client") != null);
    try std.testing.expect(std.mem.indexOf(u8, upg_toml.upgraded_toml, "target = \"target.os is (.Linux | .Macos)\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, upg_toml.upgraded_toml, "allow_caps = [\"unsafe_op\"]") != null);

    // Build an initial `corex.lock` locking `net-client` to `["unsafe_op"]`:
    var lock_interner = try StringInterner.init(std.testing.allocator);
    defer lock_interner.deinit();
    const pkg_sem = (try pkg_manifest.SemVer.parse(&lock_interner, "1.2.0")).?;
    const lock_pkgs = [_]pkg_manifest.LockPackage{.{
        .name = try lock_interner.intern("net-client"),
        .version = pkg_sem,
        .source = try lock_interner.intern("registry+https://pkg.corex.dev"),
        .tree_hash = @splat(0x11),
        .max_caps = .{ .unsafe_op = true },
        .cxi_blake3 = @splat(0x22),
    }};
    const init_lock = pkg_manifest.Lockfile{
        .root_manifest_blake3 = upg_toml.root_manifest_blake3,
        .packages = &lock_pkgs,
    };
    const lock_bytes = try pkg_manifest.serializeLockfile(std.testing.allocator, &init_lock, &lock_interner);
    defer std.testing.allocator.free(lock_bytes);

    // [1] Unaccepted escalation (`net` not in `--accept-caps=fs`):
    const obs_net = [_]PackageObservedCaps{.{
        .package_kebab = "net-client",
        .actual_surface_caps = .{ .unsafe_op = true, .net = true },
    }};
    var unaccepted = try evaluateAndApplyAcceptCaps(
        std.testing.allocator,
        FileId.fromInt(31),
        upg_toml.upgraded_toml,
        FileId.fromInt(32),
        lock_bytes,
        &obs_net,
        &cfg_env,
        parseAcceptCapsFilter("fs").?,
    );
    defer unaccepted.deinit(std.testing.allocator);
    try std.testing.expect(unaccepted.unaccepted_escalation_bits != 0);
    try std.testing.expect(!unaccepted.is_toml_changed);
    try std.testing.expect(!unaccepted.is_lock_changed);

    // [2] Accepted escalation (`--accept-caps=net` updates both `allow_caps` and `corex.lock` `max_caps`):
    var accepted = try evaluateAndApplyAcceptCaps(
        std.testing.allocator,
        FileId.fromInt(31),
        upg_toml.upgraded_toml,
        FileId.fromInt(32),
        lock_bytes,
        &obs_net,
        &cfg_env,
        parseAcceptCapsFilter("net").?,
    );
    defer accepted.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(u16, 0), accepted.unaccepted_escalation_bits);
    try std.testing.expect(!accepted.has_denied_cap_violation);
    try std.testing.expect(accepted.is_toml_changed);
    try std.testing.expect(accepted.is_lock_changed);
    try std.testing.expect(
        std.mem.indexOf(u8, accepted.updated_toml, "allow_caps = [\"unsafe_op\", \"net\"]") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, accepted.updated_lock.?, "max_caps = [\"net\", \"unsafe_op\"]") != null,
    );

    // [3] Explicit `deny_caps = ["process"]` is NEVER overridden even with bare `--accept-caps`:
    const obs_denied = [_]PackageObservedCaps{.{
        .package_kebab = "net-client",
        .actual_surface_caps = .{ .unsafe_op = true, .process = true },
    }};
    var denied = try evaluateAndApplyAcceptCaps(
        std.testing.allocator,
        FileId.fromInt(31),
        upg_toml.upgraded_toml,
        FileId.fromInt(32),
        lock_bytes,
        &obs_denied,
        &cfg_env,
        parseAcceptCapsFilter(null).?,
    );
    defer denied.deinit(std.testing.allocator);
    try std.testing.expect(denied.has_denied_cap_violation);

    // [4] `--check` dry-run report verification:
    var out_buf: [512]u8 = undefined;
    var err_buf: [512]u8 = undefined;
    var out_w = std.Io.Writer.fixed(&out_buf);
    var err_w = std.Io.Writer.fixed(&err_buf);
    const clean_code = try renderUpgradeCheckReport(
        &out_w,
        &err_w,
        StyleConfig.MONOCHROME,
        StyleConfig.MONOCHROME,
        &.{},
    );
    try std.testing.expectEqual(@as(u8, 0), clean_code);
    try std.testing.expectEqualStrings(
        "✓ upgrade --check: all files conform to canonical CoreX 2026\n",
        out_w.buffered(),
    );
}

test "test_precedence_rewrites_ur21_05_pipe_and_ur22_03_slice_array_fn_ptr" {
    const legacy_src =
        \\pub struct MyErr {}
        \\
        \\pub fn inc(val: i32) -> i32 {
        \\    return val +% 1;
        \\}
        \\
        \\pub fn probe_pipe(opt: i32?) -> i32 {
        \\    return opt.unwrap_or(10) |> inc();
        \\}
        \\
        \\pub fn probe_types(
        \\    arr_opt: &Option[[u8; 4]],
        \\    fn_opt: Option[*fn() -> i32],
        \\    fn_res: Result[*fn() -> i32, MyErr],
        \\) -> i32 {
        \\    let _ = arr_opt;
        \\    let _ = fn_opt;
        \\    let _ = fn_res;
        \\    return 0;
        \\}
    ++ "\n";

    var res = try upgradeSource(std.testing.allocator, legacy_src, FileId.fromInt(40), .{});
    defer res.deinit(std.testing.allocator);
    try std.testing.expect(res.is_changed);
    try std.testing.expect(!res.is_rolled_back);

    const out = res.upgraded_source;
    try std.testing.expect(std.mem.indexOf(u8, out, "(opt orelse 10) |> inc()") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "&([u8; 4]?)") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "(*fn() -> i32)?") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "(*fn() -> i32)!MyErr") != null);
    try std.testing.expectEqual(@as(u32, 0), try countSyntaxErrors(std.testing.allocator, FileId.fromInt(41), out));
}

test "test_deprecated_variadic_and_comment_guards_plus_standalone_fix_inline" {
    const dep_src =
        \\@deprecated("use c_printf_v2", upgrade: "c_printf_v2($0)")
        \\extern "C" fn c_printf(fmt_ptr: *u8, ...) -> i32;
        \\
        \\extern "C" fn c_printf_v2(fmt_ptr: *u8, ...) -> i32;
        \\
        \\pub fn modern_add(lhs: i32, rhs: i32) -> i32 {
        \\    return lhs +% rhs;
        \\}
        \\
        \\@deprecated("use modern_add", upgrade: "modern_add($0, $1)")
        \\pub fn legacy_add(lhs: i32, rhs: i32) -> i32 {
        \\    return modern_add(lhs, rhs);
        \\}
        \\
        \\@fix_inline("modern_add($0, 1)")
        \\pub fn bump_one(val: i32) -> i32 {
        \\    return modern_add(val, 1);
        \\}
        \\
        \\pub fn caller(fmt_ptr: *u8, num: i32) -> i32 {
        \\    let var_keep = unsafe { c_printf(fmt_ptr, num, 99) };
        \\    let cmt_keep = legacy_add(/* preserve_arg_cmt */ num, 2);
        \\    let inlined = bump_one(num);
        \\    return var_keep +% cmt_keep +% inlined;
        \\}
    ++ "\n";

    // [1] Standalone `@fix_inline` must NOT emit `W0403` during `corex check` (only the two `@deprecated` calls warn):
    {
        var db = try CompilerDb.init(std.testing.allocator);
        defer db.deinit();
        const check_fid = FileId.fromInt(42);
        _ = try db.setInput(check_fid, dep_src, .low);
        _ = try db.parseCst(check_fid);
        _ = try db.resolveSignatures(check_fid);
        var w0403_count: usize = 0;
        for ((try db.extractItemTree(check_fid)).entries) |entry| {
            _ = try db.typecheckBody(entry.def_id);
            if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                for (body_sink.diagnostics.items) |diag_item| {
                    if (diag_item.code == .w0403_deprecated_symbol) {
                        w0403_count += 1;
                    }
                }
            }
        }
        try std.testing.expectEqual(@as(usize, 2), w0403_count);
    }

    // [2] `upgradeSource` expands `@fix_inline`, preserves C-variadic extra args, and preserves commented `@deprecated` calls:
    var upg_res = try upgradeSource(std.testing.allocator, dep_src, FileId.fromInt(43), .{});
    defer upg_res.deinit(std.testing.allocator);
    try std.testing.expect(upg_res.is_changed);
    try std.testing.expect(!upg_res.is_rolled_back);

    const upgraded = upg_res.upgraded_source;
    try std.testing.expect(std.mem.indexOf(u8, upgraded, "c_printf(fmt_ptr, num, 99)") != null);
    try std.testing.expect(std.mem.indexOf(u8, upgraded, "/* preserve_arg_cmt */") != null);
    try std.testing.expect(std.mem.indexOf(u8, upgraded, "let inlined = modern_add(num, 1);") != null);
}

test "test_generated_script_frontmatter_guard_ref_self_type_and_cst_comment_guards" {
    // [1] `#!` + `---` script with `# @generated` in TOML frontmatter or `// DO NOT EDIT` after `---` skips upgrade:
    const gen_toml_script =
        "#!/usr/bin/env corex\n" ++
        "---\n" ++
        "# @generated by codegen\n" ++
        "[dependencies]\n" ++
        "---\n" ++
        "use std::io;\n" ++
        "pub fn main() -> unit {}\n";
    try std.testing.expect(isGeneratedSourceHeader(gen_toml_script));
    var skip_toml = try upgradeSource(std.testing.allocator, gen_toml_script, FileId.fromInt(44), .{});
    defer skip_toml.deinit(std.testing.allocator);
    try std.testing.expect(skip_toml.is_skipped_generated);
    try std.testing.expect(!skip_toml.is_changed);

    const gen_after_fm_script =
        "#!/usr/bin/env corex\n" ++
        "---\n" ++
        "[dependencies]\n" ++
        "---\n" ++
        "// DO NOT EDIT: synthesized fixture\n" ++
        "use std::io;\n" ++
        "pub fn main() -> unit {}\n";
    try std.testing.expect(isGeneratedSourceHeader(gen_after_fm_script));
    var skip_after = try upgradeSource(std.testing.allocator, gen_after_fm_script, FileId.fromInt(45), .{});
    defer skip_after.deinit(std.testing.allocator);
    try std.testing.expect(skip_after.is_skipped_generated);
    try std.testing.expect(!skip_after.is_changed);

    // String value containing `# @generated` inside TOML frontmatter is NOT a generated marker comment:
    const non_gen_script =
        "---\n" ++
        "[package]\n" ++
        "name = \"demo-script\"\n" ++
        "version = \"0.1.0\"\n" ++
        "description = \"literal # @generated text\"\n" ++
        "---\n" ++
        "use std::io;\n" ++
        "pub fn main() {}\n";
    try std.testing.expect(!isGeneratedSourceHeader(non_gen_script));

    // [2] `UR-22-02` preserves explicit `: Self` receiver annotations (`ref self: Self` -> `&self: Self`):
    const self_modes_src =
        \\pub struct Counter {
        \\    pub val: i32,
        \\}
        \\
        \\impl Counter {
        \\    pub fn read_val(ref self: Self) -> i32 {
        \\        return self.val;
        \\    }
        \\
        \\    pub fn bump_val(ref mut self: Self) {
        \\        self.val = self.val +% 1;
        \\    }
        \\
        \\    pub fn take_val(sink self: Self) -> i32 {
        \\        return self.val;
        \\    }
        \\}
    ++ "\n";
    var self_res = try upgradeSource(std.testing.allocator, self_modes_src, FileId.fromInt(46), .{});
    defer self_res.deinit(std.testing.allocator);
    try std.testing.expect(self_res.is_changed);
    try std.testing.expect(!self_res.is_rolled_back);
    try std.testing.expect(std.mem.indexOf(u8, self_res.upgraded_source, "(&self: Self)") != null);
    try std.testing.expect(std.mem.indexOf(u8, self_res.upgraded_source, "(&mut self: Self)") != null);
    try std.testing.expect(std.mem.indexOf(u8, self_res.upgraded_source, "(own self: Self)") != null);
    try std.testing.expectEqual(
        @as(u32, 0),
        try countSyntaxErrors(std.testing.allocator, FileId.fromInt(47), self_res.upgraded_source),
    );

    // [3] CST/AST comment guards prevent silent comment deletion across `UR-21-01`/`02`/`06`/`07` & `UR-22-02`/`03`/`04`/`05`:
    const commented_src =
        \\use /* c_use */ cx.ffi.c_void;
        \\
        \\bit_field Flags(/* c_bf */ u8) {
        \\    ready: bool | 1,
        \\}
        \\
        \\pub fn keep_comments(
        \\    ref /* c_param */ arg: i32,
        \\    opt: Option[/* c_opt */ i32],
        \\    slice_in: &[u8],
        \\    scratch: &mut i32,
        \\) -> usize {
        \\    if /* c_if */ let .Some(val) = opt {
        \\        let _ = val;
        \\    }
        \\    while /* c_while */ let .Some(w_val) = opt {
        \\        let _ = w_val;
        \\        break;
        \\    }
        \\    cx.mem.with_arena(/* c_arena */ scratch, || {
        \\        let _ = arg;
        \\    });
        \\    let sub = slice_in[0 /* c_rng */ .. slice_in.len() - 1];
        \\    return sub.len();
        \\}
    ++ "\n";
    var cmt_res = try upgradeSource(std.testing.allocator, commented_src, FileId.fromInt(48), .{});
    defer cmt_res.deinit(std.testing.allocator);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_use */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_bf */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_param */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_opt */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_if */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_while */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_arena */") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "/* c_rng */") != null);
}

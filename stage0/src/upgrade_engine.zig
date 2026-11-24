//! Zero-Legacy Automated Source & Manifest Upgrade Engine (`DR-14`, `DR-17`, `DR-21`, `DR-22`, `DR-23`, & `DR-24`)
//!
//! Implements the bounded 4-pass multi-stage rewrite pipeline (`corex upgrade` / `corex fix`) covering
//! Tier 1 pre-CST lexical shims (`UR-21-00`, `UR-22-00`, `UR-23-00`, `UR-23-02`, `UR-24-00`–`UR-24-02`), Tier 2
//! lossless CST/AST structural rewrites (`UR-21-01`–`UR-21-03`, `UR-22-01`–`UR-22-05`, `UR-23-01`, `UR-23-03`,
//! `UR-23-06`, `UR-24-03`, `UR-24-04`), Tier 3 `CompilerDb` `TypeId`-aware semantic modernizers (`UR-21-04`–`UR-21-07`,
//! `UR-22-06`, `UR-23-04`, `UR-23-05`, `UR-24-05`, `UR-24-06`, `@deprecated` `W0403`), and `corex.toml` / `--accept-caps`.
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
    rule_mask: u32 = ALL_UPGRADE_RULES_MASK,
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
    /// `true` when upgrading a synthetic single-expression wrapper (`{expr}` hole) that must skip `formatSource`.
    skip_post_format: bool = false,
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

/// Single byte-span edit specification passed to `FixCollector.appendMultiEdits`.
const PendingByteEdit = struct {
    /// Inclusive starting byte offset in source.
    start_byte: u32,
    /// Exclusive ending byte offset in source.
    end_byte: u32,
    /// Replacement UTF-8 slice interned into `FixCollector.interner`.
    replacement: []const u8,
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

    /// Appends an atomic multi-edit `.machine_applicable` `SuggestedFix` bundle.
    fn appendMultiEdits(
        self: *FixCollector,
        priority: EditPriority,
        pending_edits: []const PendingByteEdit,
        message: []const u8,
    ) !void {
        if (pending_edits.len == 0) return;
        const edits = try self.arena.asAllocator().alloc(TextEdit, pending_edits.len);
        for (pending_edits, 0..) |spec, i| {
            edits[i] = .{
                .file_id = self.file_id,
                .start_byte = spec.start_byte,
                .end_byte = spec.end_byte,
                .replacement_id = try self.interner.intern(spec.replacement),
            };
        }
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

/// Bitmask enabling all 29 canonical Zero-Legacy upgrade rules (`0x1FFF_FFFF`).
pub const ALL_UPGRADE_RULES_MASK: u32 = (@as(u32, 1) << @intCast(upgrade_rules.UPGRADE_RULE_COUNT)) - 1;

/// Maximum multi-pass fixed-point synergy iterations per file (`DR-14` §2.3 & `DR-21` §3.3).
pub const MAX_SYNERGY_PASSES: u8 = upgrade_rules.MAX_SYNERGY_PASSES;

/// Maximum leading byte prefix inspected for `@generated` or `DO NOT EDIT` header comments.
pub const GENERATED_HEADER_SCAN_LIMIT: usize = check_audit.GENERATED_HEADER_SCAN_BYTES;

/// Canonical 29-entry explanation and before/after showcase table indexed by `@backingInt(UpgradeRuleId)`.
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
    .{
        .id = .ur_23_00_block_doc_comments_to_line_docs,
        .explanation = "CoreX rejects C/Javadoc '/** … */' and '/*! … */' block doc comments so glob patterns " ++
            "like 'src/*' inside Markdown backticks never open nested comments.",
        .before_cx =
        \\/**
        \\ * Computes CRC-32 over `packets/*`.
        \\ */
        \\pub fn crc32(data: &[u8]) -> u32 { return 0; }
        ,
        .after_cx =
        \\/| Computes CRC-32 over `packets/*`.
        \\pub fn crc32(data: &[u8]) -> u32 { return 0; }
        ,
    },
    .{
        .id = .ur_23_01_doc_comment_placement_and_attachment,
        .explanation = "Module '/#' doc comments are valid exclusively at file top; inline 'mod' blocks " ++
            "use outer '/|' docs, and '/|' must immediately precede a documentable declaration.",
        .before_cx =
        \\pub mod codec {
        \\    /# Wire framing helpers.
        \\    /| Decodes frame header.
        \\
        \\    pub fn decode() {}
        \\}
        ,
        .after_cx =
        \\/| Wire framing helpers.
        \\pub mod codec {
        \\    /| Decodes frame header.
        \\    pub fn decode() {}
        \\}
        ,
    },
    .{
        .id = .ur_23_02_elif_to_else_if,
        .explanation = "Curly-brace blocks self-delimit every branch without extra indentation, so chained " ++
            "conditionals compose full English 'else if' rather than contracted 'elif'/'elsif'/'elseif'.",
        .before_cx =
        \\if code == 200 {
        \\    handle_ok();
        \\} elif code == 404 {
        \\    handle_not_found();
        \\}
        ,
        .after_cx =
        \\if code == 200 {
        \\    handle_ok();
        \\} else if code == 404 {
        \\    handle_not_found();
        \\}
        ,
    },
    .{
        .id = .ur_23_03_impl_visibility_and_inline_type_methods,
        .explanation = "Type declarations define pure data layouts while behavior lives in visibility-free " ++
            "'impl' blocks whose individual methods declare 'pub', 'pub(pkg)', or 'pub(super)'.",
        .before_cx =
        \\pub struct Counter {
        \\    pub val: u32,
        \\    pub fn read(&self) -> u32 { return self.val; }
        \\}
        \\pub impl Clone for Counter {}
        ,
        .after_cx =
        \\pub struct Counter {
        \\    pub val: u32,
        \\}
        \\
        \\impl Counter {
        \\    pub fn read(&self) -> u32 { return self.val; }
        \\}
        \\impl Clone for Counter {}
        ,
    },
    .{
        .id = .ur_23_04_canonical_wildcard_discard_stmt,
        .explanation = "'let' and 'var' always introduce at least one named binding; immediate discards use " ++
            "'_ = expr;', while 'unit' calls drop '_ =', 'unit!E' uses 'catch {}', and 'T!E' uses '.ok()'.",
        .before_cx =
        \\let _ = compute_checksum(buf);
        \\let _ = stream.flush();
        \\(_, _) = next_pair();
        ,
        .after_cx =
        \\_ = compute_checksum(buf);
        \\stream.flush() catch {};
        \\_ = next_pair();
        ,
    },
    .{
        .id = .ur_23_05_foreign_scalar_type_names,
        .explanation = "All 20 built-in CoreX machine scalars use concise lowercase keywords ('u32', 'bool', " ++
            "'str', 'unit', 'opaque'), separating registers from PascalCase nominal types and Type Groups.",
        .before_cx =
        \\pub fn reset_slot(idx: USize, count: UInt32, active: Bool, raw: *Void) -> Void {}
        ,
        .after_cx =
        \\pub fn reset_slot(idx: usize, count: u32, active: bool, raw: *opaque) {}
        ,
    },
    .{
        .id = .ur_23_06_missing_colon_before_type,
        .explanation = "Postfix ':' separates identifiers from type annotations across parameters, struct " ++
            "fields, closures, and bindings, avoiding Go-style juxtaposition ambiguities.",
        .before_cx =
        \\pub fn add_pair(lhs u32, rhs u32) -> u32 {
        \\    let sum u32 = lhs + rhs;
        \\    return sum;
        \\}
        ,
        .after_cx =
        \\pub fn add_pair(lhs: u32, rhs: u32) -> u32 {
        \\    let sum: u32 = lhs + rhs;
        \\    return sum;
        \\}
        ,
    },
    .{
        .id = .ur_24_00_doc_prefixes_block_comments_and_tabs,
        .explanation = "CoreX unifies comments onto <=2-character line prefixes ('//' comment, '/|' item doc, " ++
            "'/#' module doc), retiring '/* … */', '///', '//!', and hard '\\t' tab indentation.",
        .before_cx =
        \\//! Ring buffer primitives.
        \\
        \\/// Capacity in elements.
        \\pub const RING_CAP: usize = /* power of two */ 64;
        ,
        .after_cx =
        \\/# Ring buffer primitives.
        \\
        \\/| Capacity in elements.
        \\// power of two
        \\pub const RING_CAP: usize = 64;
        ,
    },
    .{
        .id = .ur_24_01_f_strings_and_multiline_dedent,
        .explanation = "Explicit 'f\"…\"' / 'f#\"…\"#' marks string interpolation at byte 0 while retiring fat " ++
            "'\"\"\"' fences in favor of dedented '\"<newline> … \"' multiline literals.",
        .before_cx =
        \\pub fn banner(port: u16) -> String {
        \\    return """
        \\        listening on 0.0.0.0:{port}
        \\        """;
        \\}
        ,
        .after_cx =
        \\pub fn banner(port: u16) -> String {
        \\    return f"
        \\        listening on 0.0.0.0:{port}
        \\        ";
        \\}
        ,
    },
    .{
        .id = .ur_24_02_plain_string_brace_unescape,
        .explanation = "Plain '\"…\"' strings are 100% literal UTF-8 'str' slices where '{' and '}' require " ++
            "zero '{{' / '}}' escaping across JSON, SQL, regex, and C codegen snippets.",
        .before_cx =
        \\const SELECT_SQL: str = "SELECT id FROM sessions WHERE meta != '{{}}'";
        ,
        .after_cx =
        \\const SELECT_SQL: str = "SELECT id FROM sessions WHERE meta != '{}'";
        ,
    },
    .{
        .id = .ur_24_03_consolidated_repr_and_link_attrs,
        .explanation = "Memory layout and symbol linkage modifiers consolidate into '@repr(…)' and '@link(…)' " ++
            "so 'corex fmt' packs attributes horizontally within <=100 columns.",
        .before_cx =
        \\@repr_c
        \\@cache_aligned
        \\@zero_pad
        \\pub struct SlabHeader { pub addr: u64 }
        ,
        .after_cx =
        \\@repr(C, align: .CacheLine, zero_pad: true)
        \\pub struct SlabHeader {
        \\    pub addr: u64,
        \\}
        ,
    },
    .{
        .id = .ur_24_04_unwrap_grouped_attribute_lists,
        .explanation = "CoreX uses bracket-free '@attr' annotations packed horizontally by 'corex fmt' rather " ++
            "than Rust/Odin-style '@[…]' or '@(…)' outer list wrappers.",
        .before_cx =
        \\@[must_use, no_alloc, no_panic]
        \\pub fn is_valid(tag: u8) -> bool = tag != 0_u8;
        ,
        .after_cx =
        \\@no_alloc @no_panic @must_use
        \\pub fn is_valid(tag: u8) -> bool = tag != 0_u8;
        ,
    },
    .{
        .id = .ur_24_05_strip_redundant_private_contracts,
        .explanation = "Interprocedural SAST and MIR inlining infer effects and inline intra-package/generic/'= expr;' " ++
            "helpers automatically, reserving '@no_alloc'/'@no_panic'/'@inline' for 'pub' SemVer boundaries.",
        .before_cx =
        \\@inline
        \\@no_alloc
        \\@no_panic
        \\fn step_gen(cur: u16) -> u16 {
        \\    return cur +% 1_u16;
        \\}
        ,
        .after_cx =
        \\fn step_gen(cur: u16) -> u16 {
        \\    return cur +% 1_u16;
        \\}
        ,
    },
    .{
        .id = .ur_24_06_inline_fat_arrow_if_expr,
        .explanation = "Pure single-expression conditional values use 'if cond => a else b', reserving braced " ++
            "'if cond { … }' strictly for conditional statements and multi-statement blocks.",
        .before_cx =
        \\pub fn flag_bits(urgent: bool) -> u16 {
        \\    return if urgent { 1_u16 } else { 0_u16 };
        \\}
        ,
        .after_cx =
        \\pub fn flag_bits(urgent: bool) -> u16 {
        \\    return if urgent => 1_u16 else 0_u16;
        \\}
        ,
    },
};

/// $O(1)$ set of foreign contracted conditional keywords rewritten to `"else if"` (`UR-23-02`).
const FOREIGN_ELIF_KEYWORD_SET = std.StaticStringMap(void).initComptime(.{
    .{ "elif", {} },
    .{ "elseif", {} },
    .{ "elsif", {} },
});

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

/// $O(1)$ set of layout and linkage attribute names coalesced by `UR-24-03` (`@repr(…)` / `@link(…)`).
const DR24_COALESCED_ATTR_SET = std.StaticStringMap(void).initComptime(.{
    .{ "align", {} },
    .{ "cache_aligned", {} },
    .{ "link", {} },
    .{ "link_name", {} },
    .{ "link_section", {} },
    .{ "packed", {} },
    .{ "repr", {} },
    .{ "repr_c", {} },
    .{ "zero_pad", {} },
});

/// $O(1)$ set of ABI/entry-point attributes exempting functions from `UR-24-05` (`W0333`) stripping.
const DR24_ABI_BOUNDARY_ATTR_SET = std.StaticStringMap(void).initComptime(.{
    .{ "export", {} },
    .{ "gpu_kernel", {} },
    .{ "ifunc", {} },
    .{ "link_name", {} },
    .{ "link_section", {} },
    .{ "std_cap_boundary", {} },
    .{ "wasm_export", {} },
});

/// $O(1)$ set of effect-contract attributes stripped on private internal helpers by `UR-24-05`.
const DR24_PRIVATE_CONTRACT_ATTR_SET = std.StaticStringMap(void).initComptime(.{
    .{ "no_alloc", {} },
    .{ "no_block", {} },
    .{ "no_panic", {} },
});

/// $O(1)$ set of scoped `@allow(…)` identifiers that suppress `W0333` / `UR-24-05`.
const DR24_ALLOW_W0333_SET = std.StaticStringMap(void).initComptime(.{
    .{ "W0333", {} },
    .{ "redundant_private_contract", {} },
});

/// $O(1)$ set of `@align` / `@repr` cache-line alignment aliases canonicalized to `.CacheLine` (`ADR-24C`).
const CACHE_LINE_ALIAS_SET = std.StaticStringMap(void).initComptime(.{
    .{ ".CacheLine", {} },
    .{ ".cache_line", {} },
    .{ "cache_aligned", {} },
    .{ "cache_line", {} },
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

/// Scans inter-token trivia gaps in `source` and emits `UR-23-00` (`/** … */`, `/*! … */`) line-doc rewrites.
fn collectBlockDocCommentTier1Fixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    base_offset: u32,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    const tok_count = tok_buf.countTokens();
    if (tok_count == 0) return;

    var prev_real_end: ?usize = null;
    var tok_idx: usize = 0;
    while (tok_idx < tok_count) : (tok_idx += 1) {
        const rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_idx)));
        if (rec.flags.is_synthesized) continue;
        const gap_end: usize = @min(@as(usize, rec.byte_offset), source.len);
        const raw_gap_start: usize = prev_real_end orelse 0;
        const is_first_gap = prev_real_end == null and base_offset == 0;
        prev_real_end = @min(@as(usize, rec.byte_offset) + @as(usize, rec.byte_len), source.len);
        if (raw_gap_start >= gap_end) continue;

        var cursor: usize = raw_gap_start;
        if (is_first_gap) {
            if (gap_end >= 3 and source[0] == 0xEF and source[1] == 0xBB and source[2] == 0xBF) cursor = 3;
            if (cursor + 1 < gap_end and source[cursor] == '#' and source[cursor + 1] == '!') {
                while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                if (cursor < gap_end and source[cursor] == '\n') cursor += 1;
            }
        }

        var has_seen_non_mod_comment = false;
        while (cursor < gap_end) {
            const byte_val = source[cursor];
            if (byte_val == '/' and cursor + 1 < gap_end and source[cursor + 1] == '/') {
                const cmt_start = cursor;
                while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                const raw_cmt = std.mem.trimEnd(u8, source[cmt_start..cursor], "\r\n");
                if (!std.mem.startsWith(u8, raw_cmt, "//!")) {
                    has_seen_non_mod_comment = true;
                }
            } else if (byte_val == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                const cmt_start = cursor;
                cursor += 2;
                var blk_depth: u32 = 1;
                while (cursor < gap_end and blk_depth > 0) {
                    if (source[cursor] == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                        blk_depth += 1;
                        cursor += 2;
                    } else if (source[cursor] == '*' and cursor + 1 < gap_end and source[cursor + 1] == '/') {
                        blk_depth -= 1;
                        cursor += 2;
                    } else {
                        cursor += 1;
                    }
                }
                const cmt_end = cursor;
                const cmt_len = cmt_end - cmt_start;
                const is_star_doc = blk_depth == 0 and cmt_len >= 5 and
                    source[cmt_start + 2] == '*' and source[cmt_start + 3] != '*' and source[cmt_start + 3] != '/';
                const is_bang_doc = blk_depth == 0 and cmt_len >= 5 and source[cmt_start + 2] == '!';

                if (is_star_doc or is_bang_doc) {
                    var line_bol = cmt_start;
                    while (line_bol > 0 and source[line_bol - 1] != '\n') : (line_bol -= 1) {}
                    var indent_end = line_bol;
                    while (indent_end < cmt_start and (source[indent_end] == ' ' or source[indent_end] == '\t')) {
                        indent_end += 1;
                    }
                    const indent_slice = source[line_bol..indent_end];
                    const has_code_before = indent_end < cmt_start;

                    var after_newlines: u32 = 0;
                    var has_comment_after = false;
                    var probe = cmt_end;
                    while (probe < gap_end) : (probe += 1) {
                        if (source[probe] == '\n') after_newlines += 1;
                        if (source[probe] == '/' and probe + 1 < gap_end and
                            (source[probe + 1] == '/' or source[probe + 1] == '*'))
                        {
                            has_comment_after = true;
                            break;
                        }
                    }
                    const is_file_top_mod_doc = is_first_gap and !has_seen_non_mod_comment and !has_code_before and
                        (is_bang_doc or rec.kind == .eof or rec.kind == .kw_use or after_newlines >= 2 or has_comment_after);
                    const target_prefix: []const u8 = if (is_file_top_mod_doc)
                        "/#"
                    else if (is_bang_doc)
                        "//"
                    else
                        "/|";

                    const repl_lines = try fmt_engine.renderBlockDocAsLineComments(
                        allocator,
                        source[cmt_start + 3 .. cmt_end - 2],
                        target_prefix,
                        indent_slice,
                        has_code_before,
                    );
                    defer allocator.free(repl_lines);

                    const abs_start = base_offset +| @as(u32, @intCast(cmt_start));
                    if (cmt_end < gap_end and !has_code_before) {
                        var same_ln = cmt_end;
                        while (same_ln < gap_end and (source[same_ln] == ' ' or source[same_ln] == '\t')) : (same_ln += 1) {}
                        if (same_ln == gap_end and rec.kind != .eof) {
                            const with_nl = try std.fmt.allocPrint(allocator, "{s}\n{s}", .{ repl_lines, indent_slice });
                            defer allocator.free(with_nl);
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                abs_start,
                                base_offset +| @as(u32, @intCast(same_ln)),
                                with_nl,
                                "UR-23-00: rewrite block doc comment to `/#` or `/|` line doc comments (`E0118`)",
                            );
                        } else {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                abs_start,
                                base_offset +| @as(u32, @intCast(cmt_end)),
                                repl_lines,
                                "UR-23-00: rewrite block doc comment to `/#` or `/|` line doc comments (`E0118`)",
                            );
                        }
                    } else {
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            abs_start,
                            base_offset +| @as(u32, @intCast(cmt_end)),
                            repl_lines,
                            "UR-23-00: rewrite block doc comment to `/#` or `/|` line doc comments (`E0118`)",
                        );
                    }
                    if (!is_file_top_mod_doc) has_seen_non_mod_comment = true;
                } else {
                    has_seen_non_mod_comment = true;
                }
            } else {
                cursor += 1;
            }
        }
    }
}

/// Checks whether an `elif` / `elsif` / `elseif` token at `tok_idx` introduces a conditional branch (`UR-23-02`).
fn isForeignElifBranchToken(tok_buf: *const TokenBuffer, tok_idx: usize) bool {
    const tok_count = tok_buf.countTokens();
    if (tok_idx + 1 >= tok_count) return false;
    const prev_kind: ?TokenKind = if (tok_idx > 0)
        tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_idx - 1))).kind
    else
        null;
    if (prev_kind) |pk| {
        if (pk != .rbrace and pk != .semi and pk != .lbrace) return false;
    }

    const next_kind = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_idx + 1))).kind;
    if (next_kind == .kw_let) return true;
    if (!isCallArgExprStartToken(next_kind)) return false;

    var depth: u32 = 0;
    var scan_i: usize = tok_idx + 1;
    const scan_limit = @min(tok_count, tok_idx + 66);
    while (scan_i < scan_limit) : (scan_i += 1) {
        const tk = tok_buf.getToken(TokenIndex.fromInt(@intCast(scan_i))).kind;
        if (tk == .eof) return false;
        if (depth == 0) {
            if (tk == .lbrace) return scan_i > tok_idx + 1;
            if (tk == .semi or tk == .rbrace or tk == .comma or
                tk == .eq or tk == .plus_eq or tk == .minus_eq or tk == .star_eq or
                tk == .slash_eq or tk == .percent_eq or tk == .amp_eq or tk == .pipe_eq or
                tk == .caret_eq or tk == .shl_eq or tk == .shr_eq)
            {
                return false;
            }
        }
        switch (tk) {
            .lparen, .lbracket => depth += 1,
            .rparen, .rbracket => {
                if (depth == 0) return false;
                depth -= 1;
            },
            else => {},
        }
    }
    return false;
}

/// Wrapper prefix used when recursively upgrading `{Expr}` hole expressions inside strings (`UR-24-01`).
const HOLE_UPGRADE_WRAP_PREFIX = "pub fn __cx_up_hole__() {\n    __cx_up_sink__(";
/// Wrapper suffix used when recursively upgrading `{Expr}` hole expressions inside strings (`UR-24-01`).
const HOLE_UPGRADE_WRAP_SUFFIX = ");\n}\n";

/// Computes the minimum `#` guard count (`>= min_hashes`) so `"` followed by `h` `#`s never occurs in `body`.
fn computeRequiredQuoteGuardHashes(body: []const u8, min_hashes: usize) usize {
    var needed: usize = min_hashes;
    var idx: usize = 0;
    while (idx < body.len) {
        if (body[idx] == '"') {
            var hash_run: usize = 0;
            var h_pos = idx + 1;
            while (h_pos < body.len and body[h_pos] == '#') : (h_pos += 1) {
                hash_run += 1;
            }
            if (hash_run + 1 > needed) {
                needed = hash_run + 1;
            }
            idx = h_pos;
        } else {
            idx += 1;
        }
    }
    return @min(needed, 15);
}

/// Normalizes leading `\t` tabs on multiline string lines to 4 spaces and optionally escapes content `\t` to `\t`.
fn appendNormalizedStringSegment(
    allocator: std.mem.Allocator,
    out: *std.ArrayList(u8),
    segment: []const u8,
    is_at_line_start_io: *bool,
    is_multiline: bool,
    should_escape_inner_tabs: bool,
    should_escape_unescaped_quotes: bool,
) !void {
    var idx: usize = 0;
    while (idx < segment.len) {
        const ch = segment[idx];
        if (ch == '\n') {
            try out.append(allocator, '\n');
            is_at_line_start_io.* = true;
            idx += 1;
            continue;
        }
        if (ch == '\r') {
            try out.append(allocator, '\r');
            idx += 1;
            continue;
        }
        if (is_multiline and is_at_line_start_io.* and (ch == ' ' or ch == '\t')) {
            if (ch == '\t') {
                try out.appendSlice(allocator, "    ");
            } else {
                try out.append(allocator, ' ');
            }
            idx += 1;
            continue;
        }
        is_at_line_start_io.* = false;

        if (ch == '\\') {
            var bs_run: usize = 0;
            while (idx + bs_run < segment.len and segment[idx + bs_run] == '\\') : (bs_run += 1) {}
            try out.appendNTimes(allocator, '\\', bs_run);
            idx += bs_run;
            if ((bs_run % 2) == 1 and idx < segment.len) {
                try out.append(allocator, segment[idx]);
                idx += 1;
            }
            continue;
        }
        if (ch == '\t' and should_escape_inner_tabs) {
            try out.appendSlice(allocator, "\\t");
            idx += 1;
            continue;
        }
        if (ch == '"' and should_escape_unescaped_quotes) {
            try out.appendSlice(allocator, "\\\"");
            idx += 1;
            continue;
        }
        try out.append(allocator, ch);
        idx += 1;
    }
}

/// Ensures a migrated multiline `"""…"""` body ends with `\n[ ]*` at `<= min_content_indent` (`E0115`, `E0116`).
fn ensureValidMultilineClosingIndentAlloc(
    allocator: std.mem.Allocator,
    raw_body_after_open: []const u8,
    is_raw: bool,
    is_fmt: bool,
) ![]u8 {
    var open_nl_end: usize = 0;
    if (raw_body_after_open.len > 0 and raw_body_after_open[0] == '\n') {
        open_nl_end = 1;
    } else if (raw_body_after_open.len >= 2 and raw_body_after_open[0] == '\r' and raw_body_after_open[1] == '\n') {
        open_nl_end = 2;
    }
    if (open_nl_end == 0) return allocator.dupe(u8, raw_body_after_open);

    const after_nl = raw_body_after_open[open_nl_end..];
    var last_lf: ?usize = null;
    var min_content_spaces: usize = std.math.maxInt(usize);
    var line_start: usize = 0;
    var cur: usize = 0;

    while (cur < after_nl.len) {
        if (!is_raw and after_nl[cur] == '\\' and cur + 1 < after_nl.len) {
            cur += 2;
            continue;
        }
        if (is_fmt and !is_raw and after_nl[cur] == '{') {
            if (cur + 1 < after_nl.len and after_nl[cur + 1] == '{') {
                cur += 2;
                continue;
            }
            cur = scanHoleEndWithoutEdits(after_nl, cur + 1, after_nl.len);
            continue;
        }
        if (after_nl[cur] == '\n') {
            const clean_end = if (cur > line_start and after_nl[cur - 1] == '\r') cur - 1 else cur;
            const ln = after_nl[line_start..clean_end];
            if (ln.len > 0) {
                var sp_cols: usize = 0;
                var has_non_ws = false;
                for (ln) |b_val| {
                    if (b_val == ' ') {
                        sp_cols += 1;
                    } else if (b_val == '\t') {
                        sp_cols += 4;
                    } else {
                        has_non_ws = true;
                        break;
                    }
                }
                if (has_non_ws) {
                    min_content_spaces = @min(min_content_spaces, sp_cols);
                }
            }
            last_lf = cur;
            line_start = cur + 1;
        }
        cur += 1;
    }

    const tail = if (last_lf) |lf_i| after_nl[lf_i + 1 ..] else after_nl;
    var tail_only_ws = true;
    var tail_spaces: usize = 0;
    for (tail) |b_val| {
        if (b_val == ' ') {
            tail_spaces += 1;
        } else if (b_val == '\t') {
            tail_spaces += 4;
        } else {
            tail_only_ws = false;
            break;
        }
    }

    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);
    try out.append(allocator, '\n');

    if (!tail_only_ws) {
        var sp_cols: usize = 0;
        for (tail) |b_val| {
            if (b_val == ' ') sp_cols += 1 else if (b_val == '\t') sp_cols += 4 else break;
        }
        min_content_spaces = @min(min_content_spaces, sp_cols);
        const close_indent = if (min_content_spaces == std.math.maxInt(usize)) 0 else min_content_spaces;
        var at_bol = true;
        try appendNormalizedStringSegment(allocator, &out, after_nl, &at_bol, true, false, false);
        try out.append(allocator, '\n');
        try out.appendNTimes(allocator, ' ', close_indent);
        return out.toOwnedSlice(allocator);
    }

    const content_prefix = if (last_lf) |lf_i| after_nl[0 .. lf_i + 1] else "";
    const clamped_close = if (min_content_spaces == std.math.maxInt(usize))
        tail_spaces
    else
        @min(tail_spaces, min_content_spaces);
    var at_bol = true;
    try appendNormalizedStringSegment(allocator, &out, content_prefix, &at_bol, true, false, false);
    try out.appendNTimes(allocator, ' ', clamped_close);
    return out.toOwnedSlice(allocator);
}

/// Splits `{Expr[=][:Spec]}` inside an upgrade hole scan into `(expr_slice, spec_with_colon, has_debug_eq)`.
fn splitUpgradeHoleParts(raw_hole: []const u8) struct {
    expr_slice: []const u8,
    spec_with_colon: []const u8,
    has_debug_eq: bool,
} {
    var spec_colon_idx: ?usize = null;
    var nesting_depth: u32 = 0;
    var pos: usize = 0;
    while (pos < raw_hole.len) {
        const ch = raw_hole[pos];
        if (ch == '(' or ch == '[' or ch == '{') {
            nesting_depth += 1;
            pos += 1;
        } else if (ch == ')' or ch == ']' or ch == '}') {
            nesting_depth -|= 1;
            pos += 1;
        } else if ((ch == 'r' or ch == 'b' or ch == 'f') and pos + 1 < raw_hole.len and
            !(pos > 0 and isIdentContinueByte(raw_hole[pos - 1])))
        {
            var probe = pos + 1;
            if (ch == 'b' and probe < raw_hole.len and raw_hole[probe] == 'r') probe += 1;
            var hashes: usize = 0;
            while (probe < raw_hole.len and raw_hole[probe] == '#') : (probe += 1) hashes += 1;
            if (probe < raw_hole.len and (raw_hole[probe] == '"' or (ch == 'b' and raw_hole[probe] == '\''))) {
                const delim = raw_hole[probe];
                const is_triple = delim == '"' and probe + 2 < raw_hole.len and
                    raw_hole[probe + 1] == '"' and raw_hole[probe + 2] == '"';
                const is_raw_inner = ch == 'r' or (pos + 1 < raw_hole.len and raw_hole[pos + 1] == 'r');
                pos = probe + (if (is_triple) @as(usize, 3) else 1);
                while (pos < raw_hole.len) {
                    if (!is_raw_inner and raw_hole[pos] == '\\' and pos + 1 < raw_hole.len) {
                        pos += 2;
                        continue;
                    }
                    if (is_triple) {
                        if (pos + 2 + hashes < raw_hole.len and raw_hole[pos] == '"' and
                            raw_hole[pos + 1] == '"' and raw_hole[pos + 2] == '"')
                        {
                            var h_ok = true;
                            for (0..hashes) |hi| {
                                if (raw_hole[pos + 3 + hi] != '#') h_ok = false;
                            }
                            if (h_ok) {
                                pos += 3 + hashes;
                                break;
                            }
                        }
                    } else if (raw_hole[pos] == delim and pos + hashes < raw_hole.len) {
                        var h_ok = true;
                        for (0..hashes) |hi| {
                            if (raw_hole[pos + 1 + hi] != '#') h_ok = false;
                        }
                        if (h_ok) {
                            pos += 1 + hashes;
                            break;
                        }
                    }
                    pos += 1;
                }
                continue;
            }
            pos += 1;
        } else if (ch == '"' or ch == '\'') {
            const delim = ch;
            const is_triple = delim == '"' and pos + 2 < raw_hole.len and
                raw_hole[pos + 1] == '"' and raw_hole[pos + 2] == '"';
            pos += if (is_triple) 3 else 1;
            while (pos < raw_hole.len) {
                if (raw_hole[pos] == '\\' and pos + 1 < raw_hole.len) {
                    pos += 2;
                    continue;
                }
                if (is_triple) {
                    if (pos + 2 < raw_hole.len and raw_hole[pos] == '"' and
                        raw_hole[pos + 1] == '"' and raw_hole[pos + 2] == '"')
                    {
                        pos += 3;
                        break;
                    }
                } else if (raw_hole[pos] == delim) {
                    pos += 1;
                    break;
                }
                pos += 1;
            }
        } else if (nesting_depth == 0 and ch == ':' and pos > 0 and
            !(pos + 1 < raw_hole.len and raw_hole[pos + 1] == ':'))
        {
            if (lexer.parseFormatSpec(raw_hole[pos + 1 ..], false)) |_| {
                spec_colon_idx = pos;
                break;
            } else |_| {
                pos += 1;
            }
        } else if (nesting_depth == 0 and ch == ':' and pos > 0 and
            pos + 2 < raw_hole.len and raw_hole[pos + 1] == ':' and
            (raw_hole[pos + 2] == '<' or raw_hole[pos + 2] == '^' or raw_hole[pos + 2] == '>'))
        {
            if (lexer.parseFormatSpec(raw_hole[pos + 1 ..], false)) |_| {
                spec_colon_idx = pos;
                break;
            } else |_| {
                pos += 1;
            }
        } else {
            pos += 1;
        }
    }

    const before_spec = if (spec_colon_idx) |c_idx| raw_hole[0..c_idx] else raw_hole;
    const spec_with_colon = if (spec_colon_idx) |c_idx| raw_hole[c_idx..] else "";
    const trimmed_before = std.mem.trim(u8, before_spec, " \t");
    if (trimmed_before.len >= 2 and trimmed_before[trimmed_before.len - 1] == '=') {
        const prev_b = trimmed_before[trimmed_before.len - 2];
        if (prev_b != '=' and prev_b != '!' and prev_b != '<' and prev_b != '>' and prev_b != ':') {
            return .{
                .expr_slice = std.mem.trimEnd(u8, trimmed_before[0 .. trimmed_before.len - 1], " \t"),
                .spec_with_colon = spec_with_colon,
                .has_debug_eq = true,
            };
        }
    }
    return .{
        .expr_slice = before_spec,
        .spec_with_colon = spec_with_colon,
        .has_debug_eq = false,
    };
}

/// Recursively upgrades an inner `{Expr}` hole expression via `upgradeSource` without full-file formatting.
fn upgradeInnerHoleExprAlloc(
    allocator: std.mem.Allocator,
    expr_slice: []const u8,
    file_id: FileId,
    options: UpgradeOptions,
    depth: u8,
) anyerror![]u8 {
    if (depth >= 4 or std.mem.trim(u8, expr_slice, " \t\r\n").len == 0) {
        return allocator.dupe(u8, expr_slice);
    }
    const wrapped = try std.fmt.allocPrint(
        allocator,
        "{s}{s}{s}",
        .{ HOLE_UPGRADE_WRAP_PREFIX, expr_slice, HOLE_UPGRADE_WRAP_SUFFIX },
    );
    defer allocator.free(wrapped);

    var inner_opts = options;
    inner_opts.has_explicit_rule_filter = true;
    inner_opts.skip_post_format = true;
    var sub_res = try upgradeSource(allocator, wrapped, file_id, inner_opts);
    defer sub_res.deinit(allocator);

    if (!sub_res.is_rolled_back and
        std.mem.startsWith(u8, sub_res.upgraded_source, HOLE_UPGRADE_WRAP_PREFIX) and
        std.mem.endsWith(u8, sub_res.upgraded_source, HOLE_UPGRADE_WRAP_SUFFIX))
    {
        const start_i = HOLE_UPGRADE_WRAP_PREFIX.len;
        const end_i = sub_res.upgraded_source.len - HOLE_UPGRADE_WRAP_SUFFIX.len;
        if (end_i >= start_i) {
            return allocator.dupe(u8, sub_res.upgraded_source[start_i..end_i]);
        }
    }
    return allocator.dupe(u8, expr_slice);
}

/// Emits `UR-24-00` fixes across inter-token trivia gaps: `//!`->`/#`, `///`->`/|`, `/* … */`->`// …`, and `\t`->4 spaces.
fn collectDr24TriviaAndTabTier1Fixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    base_offset: u32,
    tok_buf: *const TokenBuffer,
    is_ur23_00_enabled: bool,
    is_ur23_01_enabled: bool,
    collector: *FixCollector,
) !void {
    const tok_count = tok_buf.countTokens();
    if (tok_count == 0) return;

    var prev_real_end: ?usize = null;
    var prev_sig_kind_1: TokenKind = .eof;
    var prev_sig_kind_2: TokenKind = .eof;
    var prev_sig_kind_3: TokenKind = .eof;
    var is_still_in_file_top_mod_doc = (base_offset == 0);

    var tok_idx: usize = 0;
    while (tok_idx < tok_count) : (tok_idx += 1) {
        const rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_idx)));
        if (rec.flags.is_synthesized) continue;
        const gap_end: usize = @min(@as(usize, rec.byte_offset), source.len);
        const raw_gap_start: usize = prev_real_end orelse 0;
        const is_first_gap = prev_real_end == null and base_offset == 0;
        const is_after_inline_mod_open = prev_sig_kind_1 == .lbrace and
            prev_sig_kind_2 == .ident and
            prev_sig_kind_3 == .kw_mod;
        prev_real_end = @min(@as(usize, rec.byte_offset) + @as(usize, rec.byte_len), source.len);

        if (raw_gap_start < gap_end) {
            var cursor: usize = raw_gap_start;
            if (is_first_gap) {
                if (gap_end >= 3 and source[0] == 0xEF and source[1] == 0xBB and source[2] == 0xBF) cursor = 3;
                if (cursor + 1 < gap_end and source[cursor] == '#' and source[cursor + 1] == '!') {
                    while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                    if (cursor < gap_end and source[cursor] == '\n') cursor += 1;
                }
            }

            var consecutive_nl: u32 = 0;
            var active_hoist_bol: ?usize = null;
            var hoist_header_buf: std.ArrayList(u8) = .empty;
            defer hoist_header_buf.deinit(allocator);
            var hoist_edits: std.ArrayList(PendingByteEdit) = .empty;
            defer hoist_edits.deinit(allocator);

            while (cursor < gap_end) {
                const ch = source[cursor];
                if (ch == '\t') {
                    const tab_start = cursor;
                    while (cursor < gap_end and source[cursor] == '\t') : (cursor += 1) {}
                    const tab_count = cursor - tab_start;
                    const space_repl = try allocator.alloc(u8, tab_count * 4);
                    defer allocator.free(space_repl);
                    @memset(space_repl, ' ');
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        base_offset +| @as(u32, @intCast(tab_start)),
                        base_offset +| @as(u32, @intCast(cursor)),
                        space_repl,
                        "UR-24-00: replace hard `\\t` tab indentation with 4 spaces (`E0116`)",
                    );
                    continue;
                }
                if (ch == '\n') {
                    consecutive_nl += 1;
                    if (consecutive_nl >= 2 and !is_first_gap) {
                        is_still_in_file_top_mod_doc = false;
                    }
                    cursor += 1;
                    continue;
                }
                if (ch == ' ' or ch == '\r') {
                    cursor += 1;
                    continue;
                }

                if (ch == '/' and cursor + 1 < gap_end and
                    (source[cursor + 1] == '/' or source[cursor + 1] == '|' or source[cursor + 1] == '#'))
                {
                    const cmt_start = cursor;
                    while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                    const raw_line = std.mem.trimEnd(u8, source[cmt_start..cursor], "\r\n");

                    if (std.mem.startsWith(u8, raw_line, "//!")) {
                        if (consecutive_nl >= 2) {
                            // Still allow if no other comment kind preceded at file top, else `UR-23-01` handles it.
                        }
                        const repl_prefix: []const u8 = if (is_still_in_file_top_mod_doc or
                            (is_after_inline_mod_open and is_ur23_01_enabled))
                            "/#"
                        else
                            "//";
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            base_offset +| @as(u32, @intCast(cmt_start)),
                            base_offset +| @as(u32, @intCast(cmt_start + 3)),
                            repl_prefix,
                            "UR-24-00: migrate retired `//!` prefix (`E0118`)",
                        );
                    } else if (std.mem.startsWith(u8, raw_line, "///") and
                        (raw_line.len == 3 or
                            (raw_line[3] != '/' and raw_line[3] != '|' and raw_line[3] != '#')))
                    {
                        is_still_in_file_top_mod_doc = false;
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            base_offset +| @as(u32, @intCast(cmt_start)),
                            base_offset +| @as(u32, @intCast(cmt_start + 3)),
                            "/|",
                            "UR-24-00: migrate retired `///` doc prefix to `/|` (`E0118`)",
                        );
                    } else if (!std.mem.startsWith(u8, raw_line, "/#")) {
                        is_still_in_file_top_mod_doc = false;
                    }

                    // Expand any literal `\t` tabs inside the comment body to 4 spaces:
                    var body_i: usize = cmt_start + 2;
                    while (body_i < cursor) {
                        if (source[body_i] == '\t') {
                            const t_s = body_i;
                            while (body_i < cursor and source[body_i] == '\t') : (body_i += 1) {}
                            const sp_buf = try allocator.alloc(u8, (body_i - t_s) * 4);
                            defer allocator.free(sp_buf);
                            @memset(sp_buf, ' ');
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                base_offset +| @as(u32, @intCast(t_s)),
                                base_offset +| @as(u32, @intCast(body_i)),
                                sp_buf,
                                "UR-24-00: replace hard `\\t` tab in comment with spaces (`E0116`)",
                            );
                        } else {
                            body_i += 1;
                        }
                    }
                    consecutive_nl = 0;
                    continue;
                }

                if (ch == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                    const cmt_start = cursor;
                    cursor += 2;
                    var blk_depth: u32 = 1;
                    while (cursor < gap_end and blk_depth > 0) {
                        if (source[cursor] == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                            blk_depth += 1;
                            cursor += 2;
                        } else if (source[cursor] == '*' and cursor + 1 < gap_end and source[cursor + 1] == '/') {
                            blk_depth -= 1;
                            cursor += 2;
                        } else {
                            cursor += 1;
                        }
                    }
                    const cmt_end = cursor;
                    const cmt_len = cmt_end - cmt_start;
                    const is_star_doc = blk_depth == 0 and cmt_len >= 5 and
                        source[cmt_start + 2] == '*' and source[cmt_start + 3] != '*' and source[cmt_start + 3] != '/';
                    const is_bang_doc = blk_depth == 0 and cmt_len >= 5 and source[cmt_start + 2] == '!';
                    if (is_ur23_00_enabled and (is_star_doc or is_bang_doc)) {
                        consecutive_nl = 0;
                        continue;
                    }
                    is_still_in_file_top_mod_doc = false;
                    if (blk_depth != 0 or cmt_len < 4) continue;

                    var line_bol = cmt_start;
                    while (line_bol > 0 and source[line_bol - 1] != '\n') : (line_bol -= 1) {}
                    var indent_end = line_bol;
                    var indent_cols: usize = 0;
                    while (indent_end < cmt_start and (source[indent_end] == ' ' or source[indent_end] == '\t')) : (indent_end += 1) {
                        indent_cols += if (source[indent_end] == '\t') 4 else 1;
                    }
                    const indent_spaces = try allocator.alloc(u8, indent_cols);
                    defer allocator.free(indent_spaces);
                    @memset(indent_spaces, ' ');

                    const has_code_before = indent_end < cmt_start;
                    var after_ws = cmt_end;
                    while (after_ws < source.len and (source[after_ws] == ' ' or source[after_ws] == '\t')) : (after_ws += 1) {}
                    const has_eol_immediately = after_ws >= source.len or
                        source[after_ws] == '\n' or source[after_ws] == '\r' or
                        (after_ws + 1 < source.len and source[after_ws] == '/' and source[after_ws + 1] == '/');
                    const has_code_after = !has_eol_immediately;

                    const raw_inner = source[cmt_start + 2 .. cmt_end - 2];
                    if (has_code_before and has_code_after) {
                        // Mid-line `/* cmt */`: hoist `// cmt` above `line_bol`!
                        if (active_hoist_bol != null and active_hoist_bol.? != line_bol and hoist_edits.items.len > 0) {
                            hoist_edits.items[0].replacement = hoist_header_buf.items;
                            try collector.appendMultiEdits(
                                .syntax_canonicalization,
                                hoist_edits.items,
                                "UR-24-00: hoist mid-line `/* … */` block comment to leading `//` comment (`E0118`)",
                            );
                            hoist_header_buf.clearRetainingCapacity();
                            hoist_edits.clearRetainingCapacity();
                            active_hoist_bol = null;
                        }
                        if (active_hoist_bol == null) {
                            active_hoist_bol = line_bol;
                            try hoist_edits.append(allocator, .{
                                .start_byte = base_offset +| @as(u32, @intCast(line_bol)),
                                .end_byte = base_offset +| @as(u32, @intCast(line_bol)),
                                .replacement = "",
                            });
                        }
                        const rendered_cmt = try fmt_engine.renderBlockDocAsLineComments(
                            allocator,
                            raw_inner,
                            "//",
                            indent_spaces,
                            false,
                        );
                        defer allocator.free(rendered_cmt);
                        try hoist_header_buf.appendSlice(allocator, indent_spaces);
                        try hoist_header_buf.appendSlice(allocator, rendered_cmt);
                        try hoist_header_buf.append(allocator, '\n');

                        const del_end = @min(after_ws, gap_end);
                        const needs_sep_space = cmt_start > 0 and del_end < source.len and
                            !isAsciiWhitespace(source[cmt_start - 1]) and
                            source[cmt_start - 1] != '(' and source[cmt_start - 1] != '[' and
                            !isAsciiWhitespace(source[del_end]) and
                            source[del_end] != ')' and source[del_end] != ']' and
                            source[del_end] != ',' and source[del_end] != ';';
                        try hoist_edits.append(allocator, .{
                            .start_byte = base_offset +| @as(u32, @intCast(cmt_start)),
                            .end_byte = base_offset +| @as(u32, @intCast(del_end)),
                            .replacement = if (needs_sep_space) " " else "",
                        });
                        cursor = del_end;
                    } else if (has_code_before) {
                        // Trailing end-of-line `/* cmt */` -> `// cmt`:
                        const rendered_cmt = try fmt_engine.renderBlockDocAsLineComments(
                            allocator,
                            raw_inner,
                            "//",
                            indent_spaces,
                            false,
                        );
                        defer allocator.free(rendered_cmt);
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            base_offset +| @as(u32, @intCast(cmt_start)),
                            base_offset +| @as(u32, @intCast(cmt_end)),
                            rendered_cmt,
                            "UR-24-00: rewrite trailing `/* … */` block comment to `//` (`E0118`)",
                        );
                    } else {
                        // Standalone / leading `/* cmt */` -> `// cmt`:
                        const rendered_cmt = try fmt_engine.renderBlockDocAsLineComments(
                            allocator,
                            raw_inner,
                            "//",
                            indent_spaces,
                            false,
                        );
                        defer allocator.free(rendered_cmt);
                        if (has_code_after and after_ws <= gap_end) {
                            const with_nl = try std.fmt.allocPrint(allocator, "{s}\n{s}", .{ rendered_cmt, indent_spaces });
                            defer allocator.free(with_nl);
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                base_offset +| @as(u32, @intCast(cmt_start)),
                                base_offset +| @as(u32, @intCast(after_ws)),
                                with_nl,
                                "UR-24-00: rewrite leading `/* … */` block comment to `//` (`E0118`)",
                            );
                            cursor = after_ws;
                        } else {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                base_offset +| @as(u32, @intCast(cmt_start)),
                                base_offset +| @as(u32, @intCast(cmt_end)),
                                rendered_cmt,
                                "UR-24-00: rewrite `/* … */` block comment to `//` (`E0118`)",
                            );
                        }
                    }
                    consecutive_nl = 0;
                    continue;
                }
                cursor += 1;
            }

            if (active_hoist_bol != null and hoist_edits.items.len > 0) {
                hoist_edits.items[0].replacement = hoist_header_buf.items;
                try collector.appendMultiEdits(
                    .syntax_canonicalization,
                    hoist_edits.items,
                    "UR-24-00: hoist mid-line `/* … */` block comment to leading `//` comment (`E0118`)",
                );
            }
        }

        if (rec.kind != .eof) {
            is_still_in_file_top_mod_doc = false;
            prev_sig_kind_3 = prev_sig_kind_2;
            prev_sig_kind_2 = prev_sig_kind_1;
            prev_sig_kind_1 = rec.kind;
        }
    }
}

/// Emits Tier 1 `UR-24-01` & `UR-24-02` Branch A fixes (retired `"""`, `{{`/`}}`/`\{`/`\}`, and `\t` in literals).
fn collectDr24Tier1StringLiteralFix(
    allocator: std.mem.Allocator,
    tok_kind: TokenKind,
    lexeme: []const u8,
    start_byte: u32,
    end_byte: u32,
    file_id: FileId,
    options: UpgradeOptions,
    depth: u8,
    collector: *FixCollector,
) anyerror!void {
    const is_ur24_00 = isRuleEnabled(options.rule_mask, .ur_24_00_doc_prefixes_block_comments_and_tabs);
    const is_ur24_01 = isRuleEnabled(options.rule_mask, .ur_24_01_f_strings_and_multiline_dedent);
    const is_ur24_02 = isRuleEnabled(options.rule_mask, .ur_24_02_plain_string_brace_unescape);

    if (tok_kind == .char_lit or tok_kind == .byte_lit) {
        if (is_ur24_00 and std.mem.indexOfScalar(u8, lexeme, '\t') != null) {
            var char_out: std.ArrayList(u8) = .empty;
            defer char_out.deinit(allocator);
            for (lexeme) |b_val| {
                if (b_val == '\t') {
                    try char_out.appendSlice(allocator, "\\t");
                } else {
                    try char_out.append(allocator, b_val);
                }
            }
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                char_out.items,
                "UR-24-00: escape literal `\\t` tab inside character/byte literal (`E0116`)",
            );
        }
        return;
    }

    const info = lexer.extractStringBodyInfo(tok_kind, lexeme);
    const quote_len: usize = if (info.is_retired_triple) 3 else 1;
    const close_suffix_len: usize = quote_len + @as(usize, info.hash_count);
    const open_delim_end: usize = @as(usize, info.prefix_len) + @as(usize, info.hash_count) + quote_len;
    if (lexeme.len < open_delim_end + close_suffix_len) return;
    const close_quote_pos: usize = lexeme.len - close_suffix_len;
    if (lexeme[close_quote_pos] != '"') return;
    const raw_body = lexeme[open_delim_end..close_quote_pos];

    // [1] Raw or byte string literals (`r"…"`, `r#"…"#`, `b"…"`, `br"…"`, `r"""…"""`, `b"""…"""`, `br"""…"""`):
    if (info.is_raw or info.is_bytes) {
        if (info.is_retired_triple and is_ur24_01) {
            const norm_body = if (info.is_multiline)
                try ensureValidMultilineClosingIndentAlloc(allocator, raw_body, info.is_raw, false)
            else
                try allocator.dupe(u8, raw_body);
            defer allocator.free(norm_body);

            var out: std.ArrayList(u8) = .empty;
            defer out.deinit(allocator);
            if (info.is_raw) {
                const needed_hashes = computeRequiredQuoteGuardHashes(norm_body, info.hash_count);
                if (info.is_bytes) try out.appendSlice(allocator, "br") else try out.append(allocator, 'r');
                try out.appendNTimes(allocator, '#', needed_hashes);
                try out.append(allocator, '"');
                try out.appendSlice(allocator, norm_body);
                try out.append(allocator, '"');
                try out.appendNTimes(allocator, '#', needed_hashes);
            } else {
                try out.appendSlice(allocator, "b\"");
                var at_bol = info.is_multiline;
                try appendNormalizedStringSegment(
                    allocator,
                    &out,
                    norm_body,
                    &at_bol,
                    info.is_multiline,
                    is_ur24_00,
                    true,
                );
                try out.append(allocator, '"');
            }
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                out.items,
                "UR-24-01: migrate retired `\"\"\"` string delimiter to dedented `\"` literal (`E0115`)",
            );
            return;
        }
        if (!info.is_raw and is_ur24_00 and std.mem.indexOfScalar(u8, raw_body, '\t') != null) {
            var out: std.ArrayList(u8) = .empty;
            defer out.deinit(allocator);
            try out.appendSlice(allocator, lexeme[0..open_delim_end]);
            var at_bol = info.is_multiline;
            try appendNormalizedStringSegment(allocator, &out, raw_body, &at_bol, info.is_multiline, true, false);
            try out.appendSlice(allocator, lexeme[close_quote_pos..]);
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                out.items,
                "UR-24-00: normalize hard `\\t` tab inside byte string literal (`E0116`)",
            );
        }
        return;
    }

    // [2] Already `f`-prefixed `.fmt_string_lit`: only migrate `f"""…"""` or stray `\t`:
    if (info.is_fmt) {
        if (info.is_retired_triple and is_ur24_01) {
            const norm_body = if (info.is_multiline)
                try ensureValidMultilineClosingIndentAlloc(allocator, raw_body, false, true)
            else
                try allocator.dupe(u8, raw_body);
            defer allocator.free(norm_body);
            const needed_hashes = computeRequiredQuoteGuardHashes(norm_body, info.hash_count);
            var out: std.ArrayList(u8) = .empty;
            defer out.deinit(allocator);
            try out.append(allocator, 'f');
            try out.appendNTimes(allocator, '#', needed_hashes);
            try out.append(allocator, '"');
            try out.appendSlice(allocator, norm_body);
            try out.append(allocator, '"');
            try out.appendNTimes(allocator, '#', needed_hashes);
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                out.items,
                "UR-24-01: migrate retired `f\"\"\"` delimiter to `f\"` (`E0115`)",
            );
            return;
        }
        if (is_ur24_00 and std.mem.indexOfScalar(u8, raw_body, '\t') != null) {
            var out: std.ArrayList(u8) = .empty;
            defer out.deinit(allocator);
            try out.appendSlice(allocator, lexeme[0..open_delim_end]);
            var at_bol = info.is_multiline;
            try appendNormalizedStringSegment(allocator, &out, raw_body, &at_bol, info.is_multiline, true, false);
            try out.appendSlice(allocator, lexeme[close_quote_pos..]);
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                out.items,
                "UR-24-00: normalize hard `\\t` tab inside `f\"…\"` literal (`E0116`)",
            );
        }
        return;
    }

    // [3] Unprefixed `"…"` or `"""…"""`: scan with exact backslash parity (`Critic Amendment #6`):
    var has_legacy_marker = info.is_retired_triple;
    var has_cooked_escape = false;
    var hole_ranges: std.ArrayList(ByteInterval) = .empty;
    defer hole_ranges.deinit(allocator);

    var pos: usize = 0;
    while (pos < raw_body.len) {
        if (raw_body[pos] == '\\') {
            var bs_run: usize = 0;
            while (pos + bs_run < raw_body.len and raw_body[pos + bs_run] == '\\') : (bs_run += 1) {}
            if (bs_run >= 2) has_cooked_escape = true;
            pos += bs_run;
            if ((bs_run % 2) == 1) {
                if (pos < raw_body.len) {
                    const esc_ch = raw_body[pos];
                    if (esc_ch == '{' or esc_ch == '}') {
                        has_legacy_marker = true;
                        pos += 1;
                        continue;
                    }
                    if (esc_ch != '"') {
                        has_cooked_escape = true;
                    }
                    if (esc_ch == 'u' and pos + 1 < raw_body.len and raw_body[pos + 1] == '{') {
                        pos += 2;
                        while (pos < raw_body.len and raw_body[pos] != '}') : (pos += 1) {}
                        if (pos < raw_body.len) pos += 1;
                        continue;
                    }
                    pos += 1;
                }
                continue;
            }
            if (pos >= raw_body.len) break;
        }

        if (raw_body[pos] == '{') {
            if (pos + 1 < raw_body.len and raw_body[pos + 1] == '{') {
                has_legacy_marker = true;
                pos += 2;
                continue;
            }
            const hole_end = scanHoleEndWithoutEdits(raw_body, pos + 1, raw_body.len);
            if (hole_end > pos + 1 and hole_end <= raw_body.len and raw_body[hole_end - 1] == '}') {
                try hole_ranges.append(allocator, .{ .start = pos, .end = hole_end });
                pos = hole_end;
                continue;
            }
        } else if (raw_body[pos] == '}' and pos + 1 < raw_body.len and raw_body[pos + 1] == '}') {
            has_legacy_marker = true;
            pos += 2;
            continue;
        }
        pos += 1;
    }

    if (!has_legacy_marker) {
        if (is_ur24_00 and std.mem.indexOfScalar(u8, raw_body, '\t') != null) {
            var out: std.ArrayList(u8) = .empty;
            defer out.deinit(allocator);
            try out.append(allocator, '"');
            var at_bol = info.is_multiline;
            try appendNormalizedStringSegment(allocator, &out, raw_body, &at_bol, info.is_multiline, true, false);
            try out.append(allocator, '"');
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                out.items,
                "UR-24-00: normalize hard `\\t` tab inside string literal (`E0116`)",
            );
        }
        return;
    }

    // Branch A1: `has_legacy_marker` AND `>= 1` unescaped `{…}` hole -> `f"…"` / `f#"…"#` (`UR-24-01`):
    if (hole_ranges.items.len > 0) {
        if (!is_ur24_01) return;
        var rebuilt_body: std.ArrayList(u8) = .empty;
        defer rebuilt_body.deinit(allocator);
        var max_lit_quote_hashes: usize = 0;

        var seg_cursor: usize = 0;
        for (hole_ranges.items) |hr| {
            const lit_seg = raw_body[seg_cursor..hr.start];
            // Scan `lit_seg` for unescaped `"` (only possible in `"""…"""`) and rewrite `\{`/`\}` -> `{{`/`}}`:
            var l_i: usize = 0;
            while (l_i < lit_seg.len) {
                if (lit_seg[l_i] == '\\') {
                    var bs_run: usize = 0;
                    while (l_i + bs_run < lit_seg.len and lit_seg[l_i + bs_run] == '\\') : (bs_run += 1) {}
                    if ((bs_run % 2) == 1 and l_i + bs_run < lit_seg.len and
                        (lit_seg[l_i + bs_run] == '{' or lit_seg[l_i + bs_run] == '}'))
                    {
                        try rebuilt_body.appendNTimes(allocator, '\\', bs_run - 1);
                        const br_ch = lit_seg[l_i + bs_run];
                        try rebuilt_body.appendNTimes(allocator, br_ch, 2);
                        l_i += bs_run + 1;
                        continue;
                    }
                    try rebuilt_body.appendNTimes(allocator, '\\', bs_run);
                    l_i += bs_run;
                    if ((bs_run % 2) == 1 and l_i < lit_seg.len) {
                        try rebuilt_body.append(allocator, lit_seg[l_i]);
                        l_i += 1;
                    }
                    continue;
                }
                if (lit_seg[l_i] == '"') {
                    max_lit_quote_hashes = @max(
                        max_lit_quote_hashes,
                        computeRequiredQuoteGuardHashes(lit_seg[l_i..], 1),
                    );
                }
                try rebuilt_body.append(allocator, lit_seg[l_i]);
                l_i += 1;
            }

            const hole_inner = raw_body[hr.start + 1 .. hr.end - 1];
            const split = splitUpgradeHoleParts(hole_inner);
            const upg_expr = try upgradeInnerHoleExprAlloc(allocator, split.expr_slice, file_id, options, depth + 1);
            defer allocator.free(upg_expr);

            try rebuilt_body.append(allocator, '{');
            try rebuilt_body.appendSlice(allocator, upg_expr);
            if (split.has_debug_eq) try rebuilt_body.append(allocator, '=');
            try rebuilt_body.appendSlice(allocator, split.spec_with_colon);
            try rebuilt_body.append(allocator, '}');
            seg_cursor = hr.end;
        }

        // Trailing literal text segment after the last `{…}` hole:
        const tail_seg = raw_body[seg_cursor..];
        var t_i: usize = 0;
        while (t_i < tail_seg.len) {
            if (tail_seg[t_i] == '\\') {
                var bs_run: usize = 0;
                while (t_i + bs_run < tail_seg.len and tail_seg[t_i + bs_run] == '\\') : (bs_run += 1) {}
                if ((bs_run % 2) == 1 and t_i + bs_run < tail_seg.len and
                    (tail_seg[t_i + bs_run] == '{' or tail_seg[t_i + bs_run] == '}'))
                {
                    try rebuilt_body.appendNTimes(allocator, '\\', bs_run - 1);
                    const br_ch = tail_seg[t_i + bs_run];
                    try rebuilt_body.appendNTimes(allocator, br_ch, 2);
                    t_i += bs_run + 1;
                    continue;
                }
                try rebuilt_body.appendNTimes(allocator, '\\', bs_run);
                t_i += bs_run;
                if ((bs_run % 2) == 1 and t_i < tail_seg.len) {
                    try rebuilt_body.append(allocator, tail_seg[t_i]);
                    t_i += 1;
                }
                continue;
            }
            if (tail_seg[t_i] == '"') {
                max_lit_quote_hashes = @max(
                    max_lit_quote_hashes,
                    computeRequiredQuoteGuardHashes(tail_seg[t_i..], 1),
                );
            }
            try rebuilt_body.append(allocator, tail_seg[t_i]);
            t_i += 1;
        }

        const norm_f_body = if (info.is_multiline)
            try ensureValidMultilineClosingIndentAlloc(allocator, rebuilt_body.items, false, true)
        else
            try allocator.dupe(u8, rebuilt_body.items);
        defer allocator.free(norm_f_body);

        const final_hashes = if (max_lit_quote_hashes > 0)
            computeRequiredQuoteGuardHashes(norm_f_body, max_lit_quote_hashes)
        else
            0;

        var final_out: std.ArrayList(u8) = .empty;
        defer final_out.deinit(allocator);
        try final_out.append(allocator, 'f');
        try final_out.appendNTimes(allocator, '#', final_hashes);
        try final_out.append(allocator, '"');
        var at_bol = info.is_multiline;
        try appendNormalizedStringSegment(
            allocator,
            &final_out,
            norm_f_body,
            &at_bol,
            info.is_multiline,
            is_ur24_00,
            false,
        );
        try final_out.append(allocator, '"');
        try final_out.appendNTimes(allocator, '#', final_hashes);

        try collector.appendSingleEdit(
            .syntax_canonicalization,
            start_byte,
            end_byte,
            final_out.items,
            "UR-24-01: upgrade interpolated string literal to `f\"…\"` (`ADR-24B`)",
        );
        return;
    }

    // Branch A2: `has_legacy_marker` AND `0` holes -> plain `"…"` or `r#"…"#` (`UR-24-02` / `UR-24-01`):
    if (!is_ur24_02 and !(info.is_retired_triple and is_ur24_01)) return;
    var unescaped_body: std.ArrayList(u8) = .empty;
    defer unescaped_body.deinit(allocator);
    var has_unescaped_quote = false;

    var p_i: usize = 0;
    while (p_i < raw_body.len) {
        if (raw_body[p_i] == '\\') {
            var bs_run: usize = 0;
            while (p_i + bs_run < raw_body.len and raw_body[p_i + bs_run] == '\\') : (bs_run += 1) {}
            if (is_ur24_02 and (bs_run % 2) == 1 and p_i + bs_run < raw_body.len and
                (raw_body[p_i + bs_run] == '{' or raw_body[p_i + bs_run] == '}'))
            {
                try unescaped_body.appendNTimes(allocator, '\\', bs_run - 1);
                try unescaped_body.append(allocator, raw_body[p_i + bs_run]);
                p_i += bs_run + 1;
                continue;
            }
            try unescaped_body.appendNTimes(allocator, '\\', bs_run);
            p_i += bs_run;
            if ((bs_run % 2) == 1 and p_i < raw_body.len) {
                try unescaped_body.append(allocator, raw_body[p_i]);
                p_i += 1;
            }
            continue;
        }
        if (is_ur24_02 and raw_body[p_i] == '{' and p_i + 1 < raw_body.len and raw_body[p_i + 1] == '{') {
            try unescaped_body.append(allocator, '{');
            p_i += 2;
            continue;
        }
        if (is_ur24_02 and raw_body[p_i] == '}' and p_i + 1 < raw_body.len and raw_body[p_i + 1] == '}') {
            try unescaped_body.append(allocator, '}');
            p_i += 2;
            continue;
        }
        if (raw_body[p_i] == '"') {
            has_unescaped_quote = true;
        }
        try unescaped_body.append(allocator, raw_body[p_i]);
        p_i += 1;
    }

    const norm_plain_body = if (info.is_multiline)
        try ensureValidMultilineClosingIndentAlloc(allocator, unescaped_body.items, false, false)
    else
        try allocator.dupe(u8, unescaped_body.items);
    defer allocator.free(norm_plain_body);

    var plain_out: std.ArrayList(u8) = .empty;
    defer plain_out.deinit(allocator);
    if (has_unescaped_quote and !has_cooked_escape) {
        const raw_hashes = computeRequiredQuoteGuardHashes(norm_plain_body, 1);
        try plain_out.append(allocator, 'r');
        try plain_out.appendNTimes(allocator, '#', raw_hashes);
        try plain_out.append(allocator, '"');
        try plain_out.appendSlice(allocator, norm_plain_body);
        try plain_out.append(allocator, '"');
        try plain_out.appendNTimes(allocator, '#', raw_hashes);
    } else {
        try plain_out.append(allocator, '"');
        var at_bol = info.is_multiline;
        try appendNormalizedStringSegment(
            allocator,
            &plain_out,
            norm_plain_body,
            &at_bol,
            info.is_multiline,
            is_ur24_00,
            has_unescaped_quote,
        );
        try plain_out.append(allocator, '"');
    }

    if (!std.mem.eql(u8, plain_out.items, lexeme)) {
        try collector.appendSingleEdit(
            .syntax_canonicalization,
            start_byte,
            end_byte,
            plain_out.items,
            "UR-24-02: unescape literal braces and canonicalize 0-hole string literal (`ADR-24B`)",
        );
    }
}

/// Tokenizes `source` (rebased at `base_offset`) and emits Tier 1 `UR-21-00`, `UR-22-00`, `UR-23-00`, `UR-23-02`, & `UR-24-00`–`02` fixes.
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
    const is_ur23_00 = isRuleEnabled(options.rule_mask, .ur_23_00_block_doc_comments_to_line_docs);
    const is_ur23_01 = isRuleEnabled(options.rule_mask, .ur_23_01_doc_comment_placement_and_attachment);
    const is_ur23_02 = isRuleEnabled(options.rule_mask, .ur_23_02_elif_to_else_if);
    const is_ur24_00 = isRuleEnabled(options.rule_mask, .ur_24_00_doc_prefixes_block_comments_and_tabs);
    const is_ur24_01 = isRuleEnabled(options.rule_mask, .ur_24_01_f_strings_and_multiline_dedent);
    const is_ur24_02 = isRuleEnabled(options.rule_mask, .ur_24_02_plain_string_brace_unescape);
    if (!is_ur21_00 and !is_ur22_00 and !is_ur23_00 and !is_ur23_02 and
        !is_ur24_00 and !is_ur24_01 and !is_ur24_02)
    {
        return;
    }

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var lex_sink = DiagnosticSink.init(allocator);
    defer lex_sink.deinit();

    var lex_inst = lexer.Lexer.init(source, file_id, &tok_buf, &lex_sink, collector.interner);
    _ = try lex_inst.tokenize();
    const tok_count = tok_buf.countTokens();

    if (is_ur23_00) {
        try collectBlockDocCommentTier1Fixes(allocator, source, base_offset, &tok_buf, collector);
    }
    if (is_ur24_00) {
        try collectDr24TriviaAndTabTier1Fixes(
            allocator,
            source,
            base_offset,
            &tok_buf,
            is_ur23_00,
            is_ur23_01,
            collector,
        );
    }

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

        // [2] `UR-22-00`; `&&` -> `and`, `@noalloc` -> `@no_alloc`, `Numeric` -> `Number`:
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

        if (is_ur23_02 and rec.kind == .ident and FOREIGN_ELIF_KEYWORD_SET.has(lexeme) and
            isForeignElifBranchToken(&tok_buf, i))
        {
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                start_byte,
                end_byte,
                "else if",
                "UR-23-02: replace foreign `elif` keyword with `else if`",
            );
            continue;
        }

        if (rec.kind == .string_lit or rec.kind == .byte_string_lit or rec.kind == .fmt_string_lit or
            rec.kind == .char_lit or rec.kind == .byte_lit)
        {
            if (is_ur24_00 or is_ur24_01 or is_ur24_02) {
                try collectDr24Tier1StringLiteralFix(
                    allocator,
                    rec.kind,
                    lexeme,
                    start_byte,
                    end_byte,
                    file_id,
                    options,
                    depth,
                    collector,
                );
            } else if (rec.kind == .string_lit and lexeme.len >= 2 and lexeme[0] != 'r' and lexeme[0] != 'b') {
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
}

/// Collects Sub-stage A Tier 1 pre-CST lexical rewrites (`UR-21-00`, `UR-22-00`, `UR-23-00`, `UR-23-02`, `UR-24-00`–`02`).
fn collectSubstageATier1Fixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    options: UpgradeOptions,
    collector: *FixCollector,
) !void {
    const is_ur21_00 = isRuleEnabled(options.rule_mask, .ur_21_00_path_coloncolon_and_std_root);
    const is_ur22_00 = isRuleEnabled(options.rule_mask, .ur_22_00_lexical_token_canonicalization);
    const is_ur23_00 = isRuleEnabled(options.rule_mask, .ur_23_00_block_doc_comments_to_line_docs);
    const is_ur23_02 = isRuleEnabled(options.rule_mask, .ur_23_02_elif_to_else_if);
    const is_ur24_00 = isRuleEnabled(options.rule_mask, .ur_24_00_doc_prefixes_block_comments_and_tabs);
    const is_ur24_01 = isRuleEnabled(options.rule_mask, .ur_24_01_f_strings_and_multiline_dedent);
    const is_ur24_02 = isRuleEnabled(options.rule_mask, .ur_24_02_plain_string_brace_unescape);
    if (!is_ur21_00 and !is_ur22_00 and !is_ur23_00 and !is_ur23_02 and
        !is_ur24_00 and !is_ur24_01 and !is_ur24_02)
    {
        return;
    }

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
        .fmt_string_lit,
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
    is_ur24_03_enabled: bool,
    rewritten_enum_items: *std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    var idx: usize = 0;
    while (idx < cst_count) : (idx += 1) {
        const cst_id = CstNodeIndex.fromInt(@intCast(idx));
        const rec = cst_arena.getNode(cst_id);
        const sub_end = @min(idx + @max(@as(usize, rec.subtree_size), 1), cst_count);

        // [1] `@$attr($k = $v)` -> `@$attr($k: $v)` (deferring layout/link attrs to `UR-24-03` when active):
        if (rec.kind == .attribute) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |attr_sp| {
                if (is_ur24_03_enabled and attr_sp.first_tok.asInt() + 1 <= attr_sp.last_tok.asInt() and
                    tok_buf.getToken(attr_sp.first_tok).kind == .at)
                {
                    const attr_name_lex = symbol_resolver.extractTokenSlice(
                        source,
                        tok_buf,
                        TokenIndex.fromInt(attr_sp.first_tok.asInt() + 1),
                    );
                    if (DR24_COALESCED_ATTR_SET.has(attr_name_lex)) continue;
                }
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
                                                    try rewritten_enum_items.put(allocator, cst_id.asInt(), {});
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
                                                    try rewritten_enum_items.put(allocator, cst_id.asInt(), {});
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

/// Returns `true` when `sub_id` is an `.invalid_parse_subtree` wrapping an inline `fn` or `subscript` (`E0232`).
fn isInlineMethodRecoverySubtree(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    sub_id: CstNodeIndex,
) bool {
    if (sub_id.isNone() or sub_id.asInt() >= cst_arena.countNodes()) return false;
    if (cst_arena.getNode(sub_id).kind != .invalid_parse_subtree) return false;
    const span = extractCstTokenSpan(cst_arena, tok_buf, sub_id) orelse return false;
    const tok_count = tok_buf.countTokens();
    var cursor_tok: u32 = span.first_tok.asInt();
    const last_tok: u32 = @min(span.last_tok.asInt(), tok_count -| 1);

    while (cursor_tok <= last_tok) {
        const tok_rec = tok_buf.getToken(TokenIndex.fromInt(cursor_tok));
        if (tok_rec.flags.is_synthesized) {
            cursor_tok += 1;
            continue;
        }
        switch (tok_rec.kind) {
            .at => {
                cursor_tok += 1;
                if (cursor_tok <= last_tok) cursor_tok += 1;
                if (cursor_tok <= last_tok) {
                    const delim_kind = tok_buf.getToken(TokenIndex.fromInt(cursor_tok)).kind;
                    if (delim_kind == .lparen or delim_kind == .lbracket) {
                        const close_kind: TokenKind = if (delim_kind == .lparen) .rparen else .rbracket;
                        var depth: u32 = 1;
                        cursor_tok += 1;
                        while (cursor_tok <= last_tok and depth > 0) : (cursor_tok += 1) {
                            const inner_kind = tok_buf.getToken(TokenIndex.fromInt(cursor_tok)).kind;
                            if (inner_kind == delim_kind) {
                                depth += 1;
                            } else if (inner_kind == close_kind) {
                                depth -= 1;
                            }
                        }
                    }
                }
            },
            .kw_pub => {
                cursor_tok += 1;
                if (cursor_tok <= last_tok and tok_buf.getToken(TokenIndex.fromInt(cursor_tok)).kind == .lparen) {
                    var depth: u32 = 1;
                    cursor_tok += 1;
                    while (cursor_tok <= last_tok and depth > 0) : (cursor_tok += 1) {
                        const inner_kind = tok_buf.getToken(TokenIndex.fromInt(cursor_tok)).kind;
                        if (inner_kind == .lparen) {
                            depth += 1;
                        } else if (inner_kind == .rparen) {
                            depth -= 1;
                        }
                    }
                }
            },
            .kw_async, .kw_unsafe, .kw_comptime => cursor_tok += 1,
            .kw_extern => {
                cursor_tok += 1;
                if (cursor_tok <= last_tok and
                    tok_buf.getToken(TokenIndex.fromInt(cursor_tok)).kind == .string_lit)
                {
                    cursor_tok += 1;
                }
            },
            .kw_fn, .kw_subscript => return true,
            else => return false,
        }
    }
    return false;
}

/// Byte span of an inline `mod foo { //! … }` inner module doc block hoisted by `UR-23-01`.
const ByteInterval = struct {
    /// Inclusive starting byte offset.
    start: usize,
    /// Exclusive ending byte offset.
    end: usize,
};

/// Single outer doc-comment line prefix span tracked by `UR-23-01`.
const OuterDocPrefixSpan = struct {
    /// Byte offset of `/` starting `/|` or `///`.
    offset: u32,
    /// Prefix byte width (`2` for `/|`, `3` for `///`).
    prefix_len: u8,
};

/// Collects `UR-23-01` fixes: hoists inline `mod { /# … }`, downgrades mid-file `/#`, and heals `E0230` `/|`.
fn collectDocCommentPlacementFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    const tok_count = tok_buf.countTokens();
    if (tok_count == 0) return;

    var hoisted_ranges: std.ArrayList(ByteInterval) = .empty;
    defer hoisted_ranges.deinit(allocator);

    // [1] Hoist `mod foo { /# … }` (or `//! …`) inner module doc comments above `[Vis] mod foo {` as outer `/| …`:
    var cst_i: usize = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const mod_cst = CstNodeIndex.fromInt(@intCast(cst_i));
        const mod_rec = cst_arena.getNode(mod_cst);
        if (mod_rec.kind != .mod_item) continue;
        const mod_sp = extractCstTokenSpan(cst_arena, tok_buf, mod_cst) orelse continue;
        const mod_end_node = @min(cst_i + @max(@as(usize, mod_rec.subtree_size), 1), cst_count);

        var lbrace_end_opt: ?usize = null;
        var sub_cur = cst_i + 1;
        while (sub_cur < mod_end_node) : (sub_cur += 1) {
            const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_cur)));
            if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
                !leaf.token.isNone() and leaf.token.asInt() < tok_count)
            {
                const tr = tok_buf.getToken(leaf.token);
                if (!tr.flags.is_synthesized and tr.kind == .lbrace) {
                    lbrace_end_opt = @min(@as(usize, tr.byte_offset) + @as(usize, tr.byte_len), source.len);
                    break;
                }
            }
        }
        const lbrace_end = lbrace_end_opt orelse continue;
        var scan_pos = lbrace_end;
        while (scan_pos < source.len and (source[scan_pos] == ' ' or source[scan_pos] == '\t' or source[scan_pos] == '\r')) {
            scan_pos += 1;
        }
        if (scan_pos >= source.len or source[scan_pos] != '\n') continue;
        scan_pos += 1;
        const inner_del_start = scan_pos;

        var mod_bol: usize = mod_sp.start_byte;
        while (mod_bol > 0 and source[mod_bol - 1] != '\n') : (mod_bol -= 1) {}
        var mod_indent_end = mod_bol;
        while (mod_indent_end < mod_sp.start_byte and
            (source[mod_indent_end] == ' ' or source[mod_indent_end] == '\t')) : (mod_indent_end += 1)
        {}
        const mod_indent = source[mod_bol..mod_indent_end];

        var outer_buf: std.ArrayList(u8) = .empty;
        defer outer_buf.deinit(allocator);
        var inner_line_count: usize = 0;
        var inner_del_end = inner_del_start;

        while (scan_pos < source.len) {
            var line_end = scan_pos;
            while (line_end < source.len and source[line_end] != '\n') : (line_end += 1) {}
            const raw_line = std.mem.trimEnd(u8, source[scan_pos..line_end], "\r");
            const trimmed_start = std.mem.trimStart(u8, raw_line, " \t");
            const mod_prefix_len: usize = if (std.mem.startsWith(u8, trimmed_start, "/#"))
                2
            else if (std.mem.startsWith(u8, trimmed_start, "//!"))
                3
            else
                break;

            const payload = std.mem.trimEnd(u8, trimmed_start[mod_prefix_len..], " \t");
            try outer_buf.appendSlice(allocator, mod_indent);
            try outer_buf.appendSlice(allocator, "/|");
            if (payload.len > 0) {
                if (payload[0] != ' ' and payload[0] != '\t') try outer_buf.append(allocator, ' ');
                try outer_buf.appendSlice(allocator, payload);
            }
            try outer_buf.append(allocator, '\n');
            inner_line_count += 1;
            scan_pos = if (line_end < source.len) line_end + 1 else source.len;
            inner_del_end = scan_pos;
        }

        if (inner_line_count > 0) {
            // Also strip a single trailing blank line right after the hoisted inner `/#` / `//!` block:
            var blank_probe = inner_del_end;
            while (blank_probe < source.len and
                (source[blank_probe] == ' ' or source[blank_probe] == '\t' or source[blank_probe] == '\r'))
            {
                blank_probe += 1;
            }
            if (blank_probe < source.len and source[blank_probe] == '\n') {
                inner_del_end = blank_probe + 1;
            }

            try hoisted_ranges.append(allocator, .{ .start = inner_del_start, .end = inner_del_end });
            try collector.appendDualEdits(
                .syntax_canonicalization,
                @intCast(mod_bol),
                @intCast(mod_bol),
                outer_buf.items,
                @intCast(inner_del_start),
                @intCast(inner_del_end),
                "",
                "UR-23-01: hoist inline `mod` `/#` module doc comments to outer `/|`",
            );
        }
    }

    // Build $O(1)$ tables of documentable CST head tokens and post-`@attribute` declaration tokens:
    const is_doc_target = try allocator.alloc(bool, tok_count);
    defer allocator.free(is_doc_target);
    @memset(is_doc_target, false);
    const attr_head_for_decl_tok = try allocator.alloc(TokenIndex, tok_count);
    defer allocator.free(attr_head_for_decl_tok);
    @memset(attr_head_for_decl_tok, .none);

    cst_i = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const cid = CstNodeIndex.fromInt(@intCast(cst_i));
        const cid_rec = cst_arena.getNode(cid);
        if (cid_rec.kind.isDocumentable() or isInlineMethodRecoverySubtree(cst_arena, tok_buf, cid)) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cid)) |sp| {
                if (sp.first_tok.asInt() < tok_count) {
                    is_doc_target[sp.first_tok.asInt()] = true;
                }
                if (cid_rec.kind.isDocumentable()) {
                    const sub_end = @min(cst_i + @max(@as(usize, cid_rec.subtree_size), 1), cst_count);
                    var attr_cur = cst_i + 1;
                    var has_leading_attr = false;
                    while (attr_cur < sub_end) {
                        const sub_id = CstNodeIndex.fromInt(@intCast(attr_cur));
                        const sub_r = cst_arena.getNode(sub_id);
                        if (sub_r.kind == .attribute) {
                            has_leading_attr = true;
                            attr_cur += @max(@as(usize, sub_r.subtree_size), 1);
                            continue;
                        }
                        if (has_leading_attr) {
                            if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |post_sp| {
                                if (post_sp.first_tok.asInt() < tok_count and post_sp.first_tok != sp.first_tok) {
                                    attr_head_for_decl_tok[post_sp.first_tok.asInt()] = sp.first_tok;
                                }
                            }
                        }
                        break;
                    }
                }
            }
        }
    }

    // [2] Scan inter-token trivia gaps for mid-file `/#`/`//!` (`E0229`) and unattached/blank-separated `/|`/`///` (`E0230`):
    var prev_real_end: ?usize = null;
    var tok_idx: usize = 0;
    while (tok_idx < tok_count) : (tok_idx += 1) {
        const rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_idx)));
        if (rec.flags.is_synthesized) continue;
        const gap_end: usize = @min(@as(usize, rec.byte_offset), source.len);
        const raw_gap_start: usize = prev_real_end orelse 0;
        const is_first_gap = prev_real_end == null;
        prev_real_end = @min(@as(usize, rec.byte_offset) + @as(usize, rec.byte_len), source.len);
        if (raw_gap_start >= gap_end) continue;

        var cursor: usize = raw_gap_start;
        if (is_first_gap) {
            if (gap_end >= 3 and source[0] == 0xEF and source[1] == 0xBB and source[2] == 0xBF) cursor = 3;
            if (cursor + 1 < gap_end and source[cursor] == '#' and source[cursor + 1] == '!') {
                while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                if (cursor < gap_end and source[cursor] == '\n') cursor += 1;
            }
            // Advance past masked `---` script frontmatter whitespace lines before legal top-of-file `/#`:
            while (cursor < gap_end) {
                var ws_pos = cursor;
                while (ws_pos < gap_end and (source[ws_pos] == ' ' or source[ws_pos] == '\t' or source[ws_pos] == '\r')) {
                    ws_pos += 1;
                }
                if (ws_pos < gap_end and source[ws_pos] == '\n') {
                    cursor = ws_pos + 1;
                    continue;
                }
                break;
            }
        } else {
            // Skip any same-line trailing comment on `prev_real_tok`'s closing line:
            while (cursor < gap_end) {
                if (source[cursor] == '\n') {
                    cursor += 1;
                    break;
                }
                if (source[cursor] == '/' and cursor + 1 < gap_end and
                    (source[cursor + 1] == '/' or source[cursor + 1] == '|' or source[cursor + 1] == '#'))
                {
                    while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                    if (cursor < gap_end and source[cursor] == '\n') cursor += 1;
                    break;
                }
                if (source[cursor] == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                    cursor += 2;
                    var block_depth: u32 = 1;
                    while (cursor < gap_end and block_depth > 0) {
                        if (source[cursor] == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                            block_depth += 1;
                            cursor += 2;
                        } else if (source[cursor] == '*' and cursor + 1 < gap_end and source[cursor + 1] == '/') {
                            block_depth -= 1;
                            cursor += 2;
                        } else {
                            cursor += 1;
                        }
                    }
                    continue;
                }
                cursor += 1;
            }
        }

        var is_in_legal_top_mod_doc = is_first_gap;
        var active_outer_doc_offsets: std.ArrayList(OuterDocPrefixSpan) = .empty;
        defer active_outer_doc_offsets.deinit(allocator);
        var last_outer_doc_lf: ?usize = null;
        var consecutive_newlines: u32 = 0;

        while (cursor < gap_end) {
            const byte_val = source[cursor];
            if (byte_val == ' ' or byte_val == '\t' or byte_val == '\r') {
                cursor += 1;
            } else if (byte_val == '\n') {
                consecutive_newlines += 1;
                if (consecutive_newlines >= 2) {
                    is_in_legal_top_mod_doc = false;
                }
                cursor += 1;
            } else if (byte_val == '/' and cursor + 1 < gap_end and
                (source[cursor + 1] == '/' or source[cursor + 1] == '|' or source[cursor + 1] == '#'))
            {
                const cmt_start = cursor;
                while (cursor < gap_end and source[cursor] != '\n') : (cursor += 1) {}
                const raw_cmt = std.mem.trimEnd(u8, source[cmt_start..cursor], "\r\n");
                const mod_doc_len: u8 = if (std.mem.startsWith(u8, raw_cmt, "/#"))
                    2
                else if (std.mem.startsWith(u8, raw_cmt, "//!"))
                    3
                else
                    0;
                const outer_doc_len: u8 = if (std.mem.startsWith(u8, raw_cmt, "/|"))
                    2
                else if (std.mem.startsWith(u8, raw_cmt, "///") and
                    !std.mem.startsWith(u8, raw_cmt, "////") and
                    !std.mem.startsWith(u8, raw_cmt, "///|") and
                    !std.mem.startsWith(u8, raw_cmt, "///#"))
                    3
                else
                    0;

                if (outer_doc_len > 0) {
                    is_in_legal_top_mod_doc = false;
                    if (consecutive_newlines >= 2 and active_outer_doc_offsets.items.len > 0) {
                        // Previous `/|` / `///` block was orphaned before another doc block; downgrade it to `//`:
                        for (active_outer_doc_offsets.items) |doc_entry| {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                doc_entry.offset,
                                doc_entry.offset + doc_entry.prefix_len,
                                "//",
                                "UR-23-01: downgrade unattached `/|` doc comment to `//` (`E0230`)",
                            );
                        }
                        active_outer_doc_offsets.clearRetainingCapacity();
                    }
                    try active_outer_doc_offsets.append(allocator, .{
                        .offset = @intCast(cmt_start),
                        .prefix_len = outer_doc_len,
                    });
                    last_outer_doc_lf = if (cursor < gap_end and source[cursor] == '\n') cursor else null;
                    consecutive_newlines = 0;
                } else {
                    if (active_outer_doc_offsets.items.len > 0) {
                        for (active_outer_doc_offsets.items) |doc_entry| {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                doc_entry.offset,
                                doc_entry.offset + doc_entry.prefix_len,
                                "//",
                                "UR-23-01: downgrade unattached `/|` doc comment to `//` (`E0230`)",
                            );
                        }
                        active_outer_doc_offsets.clearRetainingCapacity();
                        last_outer_doc_lf = null;
                    }
                    if (mod_doc_len > 0) {
                        if (!is_in_legal_top_mod_doc) {
                            var is_already_hoisted = false;
                            for (hoisted_ranges.items) |hr| {
                                if (cmt_start >= hr.start and cmt_start < hr.end) {
                                    is_already_hoisted = true;
                                    break;
                                }
                            }
                            if (!is_already_hoisted) {
                                try collector.appendSingleEdit(
                                    .syntax_canonicalization,
                                    @intCast(cmt_start),
                                    @intCast(cmt_start + mod_doc_len),
                                    "//",
                                    "UR-23-01: downgrade misplaced mid-file `/#` comment to `//` (`E0229`)",
                                );
                            }
                        }
                    } else {
                        is_in_legal_top_mod_doc = false;
                    }
                    consecutive_newlines = 0;
                }
            } else if (byte_val == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                is_in_legal_top_mod_doc = false;
                if (active_outer_doc_offsets.items.len > 0) {
                    for (active_outer_doc_offsets.items) |doc_entry| {
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            doc_entry.offset,
                            doc_entry.offset + doc_entry.prefix_len,
                            "//",
                            "UR-23-01: downgrade unattached `/|` doc comment to `//` (`E0230`)",
                        );
                    }
                    active_outer_doc_offsets.clearRetainingCapacity();
                    last_outer_doc_lf = null;
                }
                cursor += 2;
                var block_depth: u32 = 1;
                while (cursor < gap_end and block_depth > 0) {
                    if (source[cursor] == '/' and cursor + 1 < gap_end and source[cursor + 1] == '*') {
                        block_depth += 1;
                        cursor += 2;
                    } else if (source[cursor] == '*' and cursor + 1 < gap_end and source[cursor + 1] == '/') {
                        block_depth -= 1;
                        cursor += 2;
                    } else {
                        cursor += 1;
                    }
                }
                consecutive_newlines = 0;
            } else {
                cursor += 1;
            }
        }

        if (active_outer_doc_offsets.items.len > 0) {
            if (is_doc_target[tok_idx]) {
                if (consecutive_newlines >= 2) {
                    if (last_outer_doc_lf) |doc_lf| {
                        var tok_bol = gap_end;
                        while (tok_bol > doc_lf + 1 and (source[tok_bol - 1] == ' ' or source[tok_bol - 1] == '\t')) {
                            tok_bol -= 1;
                        }
                        if (tok_bol > doc_lf + 1) {
                            try collector.appendSingleEdit(
                                .syntax_canonicalization,
                                @intCast(doc_lf + 1),
                                @intCast(tok_bol),
                                "",
                                "UR-23-01: remove blank line separating `/|` doc comment from declaration (`E0230`)",
                            );
                        }
                    }
                }
            } else if (!attr_head_for_decl_tok[tok_idx].isNone() and consecutive_newlines <= 1) {
                const attr_first_tok = attr_head_for_decl_tok[tok_idx];
                const attr_start_b: usize = tok_buf.getToken(attr_first_tok).byte_offset;
                var attr_bol: usize = @min(attr_start_b, source.len);
                while (attr_bol > 0 and source[attr_bol - 1] != '\n') : (attr_bol -= 1) {}
                var attr_indent_end = attr_bol;
                while (attr_indent_end < attr_start_b and
                    (source[attr_indent_end] == ' ' or source[attr_indent_end] == '\t')) : (attr_indent_end += 1)
                {}
                const attr_indent = source[attr_bol..attr_indent_end];

                var first_doc_bol: usize = active_outer_doc_offsets.items[0].offset;
                while (first_doc_bol > raw_gap_start and source[first_doc_bol - 1] != '\n') : (first_doc_bol -= 1) {}
                const last_doc_off: usize = active_outer_doc_offsets.items[active_outer_doc_offsets.items.len - 1].offset;
                var del_end: usize = last_doc_off;
                while (del_end < gap_end and source[del_end] != '\n') : (del_end += 1) {}
                if (del_end < gap_end and source[del_end] == '\n') del_end += 1;

                if (attr_bol <= first_doc_bol) {
                    var hoisted_doc_buf: std.ArrayList(u8) = .empty;
                    defer hoisted_doc_buf.deinit(allocator);
                    for (active_outer_doc_offsets.items) |doc_entry| {
                        var ln_end: usize = doc_entry.offset;
                        while (ln_end < gap_end and source[ln_end] != '\n' and source[ln_end] != '\r') : (ln_end += 1) {}
                        try hoisted_doc_buf.appendSlice(allocator, attr_indent);
                        if (doc_entry.prefix_len == 3) {
                            try hoisted_doc_buf.appendSlice(allocator, "/|");
                            try hoisted_doc_buf.appendSlice(allocator, source[doc_entry.offset + 3 .. ln_end]);
                        } else {
                            try hoisted_doc_buf.appendSlice(allocator, source[doc_entry.offset..ln_end]);
                        }
                        try hoisted_doc_buf.append(allocator, '\n');
                    }
                    try collector.appendDualEdits(
                        .syntax_canonicalization,
                        @intCast(attr_bol),
                        @intCast(attr_bol),
                        hoisted_doc_buf.items,
                        @intCast(first_doc_bol),
                        @intCast(del_end),
                        "",
                        "UR-23-01: hoist `/|` doc comments above `@attribute` annotations (`E0230`)",
                    );
                } else {
                    for (active_outer_doc_offsets.items) |doc_entry| {
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            doc_entry.offset,
                            doc_entry.offset + doc_entry.prefix_len,
                            "//",
                            "UR-23-01: downgrade unattached `/|` doc comment to `//` (`E0230`)",
                        );
                    }
                }
            } else {
                for (active_outer_doc_offsets.items) |doc_entry| {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        doc_entry.offset,
                        doc_entry.offset + doc_entry.prefix_len,
                        "//",
                        "UR-23-01: downgrade unattached `/|` doc comment to `//` (`E0230`)",
                    );
                }
            }
        }
    }
}

/// Builds `[Params]` (stripping `= Default`) and `[Args]` (`[T, N]`) from a `.type_params` CST node (`UR-23-03`).
fn renderImplGenericHeaderPair(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    type_params_cst: CstNodeIndex,
    params_out: *std.ArrayList(u8),
    args_out: *std.ArrayList(u8),
) !void {
    if (type_params_cst.isNone()) return;
    const tp_rec = cst_arena.getNode(type_params_cst);
    const tp_end = @min(@as(usize, type_params_cst.asInt()) + @max(@as(usize, tp_rec.subtree_size), 1), cst_arena.countNodes());

    try params_out.append(allocator, '[');
    try args_out.append(allocator, '[');
    var param_count: usize = 0;

    var cur = @as(usize, type_params_cst.asInt()) + 1;
    while (cur < tp_end) {
        const sub_id = CstNodeIndex.fromInt(@intCast(cur));
        const sub_rec = cst_arena.getNode(sub_id);
        if (sub_rec.kind == .type_param) {
            if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |p_sp| {
                // Find parameter identifier (skipping leading `@attribute` annotations) and optional `= Default`:
                var name_slice: []const u8 = "";
                var eq_start_opt: ?u32 = null;
                var depth: u32 = 0;
                var ti: u32 = p_sp.first_tok.asInt();
                while (ti <= p_sp.last_tok.asInt()) {
                    const tr = tok_buf.getToken(TokenIndex.fromInt(ti));
                    if (depth == 0 and name_slice.len == 0 and tr.kind == .at) {
                        ti += 1;
                        if (ti <= p_sp.last_tok.asInt()) ti += 1;
                        if (ti <= p_sp.last_tok.asInt()) {
                            const adk = tok_buf.getToken(TokenIndex.fromInt(ti)).kind;
                            if (adk == .lparen or adk == .lbracket) {
                                const aclose: TokenKind = if (adk == .lparen) .rparen else .rbracket;
                                var adepth: u32 = 1;
                                ti += 1;
                                while (ti <= p_sp.last_tok.asInt() and adepth > 0) : (ti += 1) {
                                    const aik = tok_buf.getToken(TokenIndex.fromInt(ti)).kind;
                                    if (aik == adk) adepth += 1 else if (aik == aclose) adepth -= 1;
                                }
                            }
                        }
                        continue;
                    }
                    if (depth == 0 and name_slice.len == 0 and
                        (tr.kind == .type_ident or tr.kind == .ident or tr.kind == .const_ident))
                    {
                        name_slice = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ti));
                    }
                    if (depth == 0 and tr.kind == .eq) {
                        eq_start_opt = tr.byte_offset;
                        break;
                    }
                    switch (tr.kind) {
                        .lparen, .lbracket, .lbrace => depth += 1,
                        .rparen, .rbracket, .rbrace => depth -|= 1,
                        else => {},
                    }
                    ti += 1;
                }
                if (name_slice.len > 0) {
                    if (param_count > 0) {
                        try params_out.appendSlice(allocator, ", ");
                        try args_out.appendSlice(allocator, ", ");
                    }
                    const param_end_b = eq_start_opt orelse p_sp.end_byte;
                    try params_out.appendSlice(
                        allocator,
                        std.mem.trim(u8, source[p_sp.start_byte..param_end_b], " \t\r\n"),
                    );
                    try args_out.appendSlice(allocator, name_slice);
                    param_count += 1;
                }
            }
            cur += @max(@as(usize, sub_rec.subtree_size), 1);
            continue;
        }
        cur += @max(@as(usize, sub_rec.subtree_size), 1);
    }

    if (param_count == 0) {
        params_out.clearRetainingCapacity();
        args_out.clearRetainingCapacity();
        return;
    }
    try params_out.append(allocator, ']');
    try args_out.append(allocator, ']');
}

/// Collects `UR-23-03` fixes: strips `[Vis]` on `impl` (`E0231`) and extracts inline type methods (`E0232`).
fn collectImplVisAndInlineTypeMethodFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    const tok_count = tok_buf.countTokens();
    if (tok_count == 0) return;

    var cst_i: usize = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const node_id = CstNodeIndex.fromInt(@intCast(cst_i));
        const rec = cst_arena.getNode(node_id);

        // [1] `E0231`; strip `[Vis]` on `[Vis] impl …` (`pub impl`, `pub(pkg) impl`, `pub(super) impl`):
        if (rec.kind == .impl_item) {
            const impl_sp = extractCstTokenSpan(cst_arena, tok_buf, node_id) orelse continue;
            var impl_kw_tok: TokenIndex = .none;
            var ti: u32 = impl_sp.first_tok.asInt();
            while (ti <= impl_sp.last_tok.asInt()) : (ti += 1) {
                if (tok_buf.getToken(TokenIndex.fromInt(ti)).kind == .kw_impl) {
                    impl_kw_tok = TokenIndex.fromInt(ti);
                    break;
                }
            }
            if (!impl_kw_tok.isNone()) {
                const impl_kw_rec = tok_buf.getToken(impl_kw_tok);
                var vis_start_opt: ?u32 = null;

                // [1a] `[Vis]` was parsed inside `.impl_item` before `kw_impl`:
                const sub_end = @min(cst_i + @max(@as(usize, rec.subtree_size), 1), cst_count);
                var sub_cur = cst_i + 1;
                while (sub_cur < sub_end) {
                    const sub_id = CstNodeIndex.fromInt(@intCast(sub_cur));
                    const sub_rec = cst_arena.getNode(sub_id);
                    if (sub_rec.kind == .visibility_modifier) {
                        if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |vis_sp| {
                            if (vis_sp.end_byte <= impl_kw_rec.byte_offset) {
                                vis_start_opt = vis_sp.start_byte;
                            }
                        }
                        break;
                    }
                    if (sub_rec.subtree_size <= 1 and !sub_rec.token.isNone() and
                        sub_rec.token.asInt() < impl_kw_tok.asInt() and
                        tok_buf.getToken(sub_rec.token).kind == .kw_pub)
                    {
                        vis_start_opt = tok_buf.getToken(sub_rec.token).byte_offset;
                        break;
                    }
                    sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                }

                // [1b] `[Vis]` was emitted immediately preceding `kw_impl` outside `.impl_item`:
                if (vis_start_opt == null and impl_kw_tok.asInt() > 0) {
                    const prev1 = tok_buf.getToken(TokenIndex.fromInt(impl_kw_tok.asInt() - 1));
                    if (prev1.kind == .kw_pub and !prev1.flags.is_synthesized) {
                        vis_start_opt = prev1.byte_offset;
                    } else if (prev1.kind == .rparen and impl_kw_tok.asInt() >= 4) {
                        const prev4 = tok_buf.getToken(TokenIndex.fromInt(impl_kw_tok.asInt() - 4));
                        const prev3 = tok_buf.getToken(TokenIndex.fromInt(impl_kw_tok.asInt() - 3));
                        if (prev4.kind == .kw_pub and prev3.kind == .lparen and !prev4.flags.is_synthesized) {
                            vis_start_opt = prev4.byte_offset;
                        }
                    }
                }

                if (vis_start_opt) |vis_start| {
                    if (!hasCommentsInByteRange(source, tok_buf, vis_start, impl_kw_rec.byte_offset)) {
                        try collector.appendSingleEdit(
                            .syntax_canonicalization,
                            vis_start,
                            impl_kw_rec.byte_offset,
                            "",
                            "UR-23-03: remove visibility modifier from `impl` block (`E0231`)",
                        );
                    }
                }
            }
            continue;
        }

        // [2] `E0232`; extract inline `fn` / `subscript` members from `struct` / `union` / `enum` / `bit_field`:
        const is_nominal_type = switch (rec.kind) {
            .struct_item, .union_item, .enum_item, .bit_field_item => true,
            else => false,
        };
        if (!is_nominal_type) continue;

        const type_sp = extractCstTokenSpan(cst_arena, tok_buf, node_id) orelse continue;
        const type_end_node = @min(cst_i + @max(@as(usize, rec.subtree_size), 1), cst_count);

        var type_name: []const u8 = "";
        var type_params_cst: CstNodeIndex = .none;
        var where_cst: CstNodeIndex = .none;
        var open_brace_tok: TokenIndex = .none;
        var close_brace_tok: TokenIndex = .none;
        var inline_methods: std.ArrayList(CstNodeIndex) = .empty;
        defer inline_methods.deinit(allocator);

        var has_seen_type_kw = false;
        var sub_cur = cst_i + 1;
        while (sub_cur < type_end_node) {
            const sub_id = CstNodeIndex.fromInt(@intCast(sub_cur));
            const sub_rec = cst_arena.getNode(sub_id);

            if (open_brace_tok.isNone()) {
                if (sub_rec.kind == .type_params) {
                    type_params_cst = sub_id;
                    sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                    continue;
                }
                if (sub_rec.kind == .where_clause) {
                    where_cst = sub_id;
                    sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                    continue;
                }
                if (sub_rec.kind == .enum_introducer or sub_rec.kind == .struct_introducer or
                    sub_rec.kind == .union_introducer or sub_rec.kind == .bit_field_introducer)
                {
                    has_seen_type_kw = true;
                    if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |intro_sp| {
                        var ti = intro_sp.first_tok.asInt();
                        while (ti <= intro_sp.last_tok.asInt()) : (ti += 1) {
                            const tk = tok_buf.getToken(TokenIndex.fromInt(ti)).kind;
                            if (type_name.len == 0 and (tk == .type_ident or tk == .ident)) {
                                type_name = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ti));
                            }
                        }
                    }
                    sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                    continue;
                }
                if (sub_rec.subtree_size <= 1 and !sub_rec.token.isNone() and sub_rec.token.asInt() < tok_count) {
                    const tr = tok_buf.getToken(sub_rec.token);
                    if (!tr.flags.is_synthesized) {
                        if (tr.kind == .kw_struct or tr.kind == .kw_union or
                            tr.kind == .kw_enum or tr.kind == .kw_bit_field)
                        {
                            has_seen_type_kw = true;
                        } else if (has_seen_type_kw and type_name.len == 0 and
                            (tr.kind == .type_ident or tr.kind == .ident))
                        {
                            type_name = symbol_resolver.extractTokenSlice(source, tok_buf, sub_rec.token);
                        } else if (tr.kind == .lbrace) {
                            open_brace_tok = sub_rec.token;
                        }
                    }
                }
                sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
                continue;
            }

            if (sub_rec.subtree_size <= 1 and !sub_rec.token.isNone() and sub_rec.token.asInt() < tok_count) {
                const tr = tok_buf.getToken(sub_rec.token);
                if (!tr.flags.is_synthesized and tr.kind == .rbrace) {
                    close_brace_tok = sub_rec.token;
                }
                sub_cur += 1;
                continue;
            }

            if (sub_rec.kind == .fn_item or sub_rec.kind == .subscript_item or
                sub_rec.kind == .impl_member or sub_rec.kind == .trait_member or
                isInlineMethodRecoverySubtree(cst_arena, tok_buf, sub_id))
            {
                try inline_methods.append(allocator, sub_id);
            }
            sub_cur += @max(@as(usize, sub_rec.subtree_size), 1);
        }

        if (inline_methods.items.len == 0 or type_name.len == 0 or
            open_brace_tok.isNone() or close_brace_tok.isNone())
        {
            continue;
        }

        var impl_params_buf: std.ArrayList(u8) = .empty;
        defer impl_params_buf.deinit(allocator);
        var type_args_buf: std.ArrayList(u8) = .empty;
        defer type_args_buf.deinit(allocator);
        try renderImplGenericHeaderPair(
            allocator,
            source,
            cst_arena,
            tok_buf,
            type_params_cst,
            &impl_params_buf,
            &type_args_buf,
        );

        var where_slice: []const u8 = "";
        if (!where_cst.isNone()) {
            if (extractCstTokenSpan(cst_arena, tok_buf, where_cst)) |w_sp| {
                where_slice = std.mem.trim(u8, source[w_sp.start_byte..w_sp.end_byte], " \t\r\n");
            }
        }

        var type_bol: usize = type_sp.start_byte;
        while (type_bol > 0 and source[type_bol - 1] != '\n') : (type_bol -= 1) {}
        var type_indent_end = type_bol;
        while (type_indent_end < type_sp.start_byte and
            (source[type_indent_end] == ' ' or source[type_indent_end] == '\t')) : (type_indent_end += 1)
        {}
        const outer_indent = source[type_bol..type_indent_end];

        const open_brace_rec = tok_buf.getToken(open_brace_tok);
        const close_brace_rec = tok_buf.getToken(close_brace_tok);
        const body_interior_start: usize = @min(
            @as(usize, open_brace_rec.byte_offset) + @as(usize, open_brace_rec.byte_len),
            source.len,
        );
        const close_brace_end: u32 = close_brace_rec.byte_offset +| close_brace_rec.byte_len;

        var pending_edits: std.ArrayList(PendingByteEdit) = .empty;
        defer pending_edits.deinit(allocator);
        var owned_repls: std.ArrayList([]u8) = .empty;
        defer {
            for (owned_repls.items) |buf| allocator.free(buf);
            owned_repls.deinit(allocator);
        }
        var extracted_body: std.ArrayList(u8) = .empty;
        defer extracted_body.deinit(allocator);

        var valid_extraction = true;
        for (inline_methods.items, 0..) |m_cst, m_idx| {
            const m_sp = extractCstTokenSpan(cst_arena, tok_buf, m_cst) orelse {
                valid_extraction = false;
                break;
            };

            // Determine earliest byte belonging to this inline method (including attached `///` docs):
            var prev_tok_end: usize = body_interior_start;
            if (m_sp.first_tok.asInt() > open_brace_tok.asInt() + 1) {
                var back_t: u32 = m_sp.first_tok.asInt() - 1;
                while (back_t > open_brace_tok.asInt()) : (back_t -= 1) {
                    const pr = tok_buf.getToken(TokenIndex.fromInt(back_t));
                    if (!pr.flags.is_synthesized) {
                        prev_tok_end = @max(prev_tok_end, @as(usize, pr.byte_offset) + @as(usize, pr.byte_len));
                        break;
                    }
                }
            }
            // Advance past `prev_tok_end`'s closing line:
            while (prev_tok_end < m_sp.start_byte and source[prev_tok_end] != '\n') : (prev_tok_end += 1) {}
            if (prev_tok_end < m_sp.start_byte and source[prev_tok_end] == '\n') prev_tok_end += 1;

            var m_bol: usize = m_sp.start_byte;
            while (m_bol > prev_tok_end and source[m_bol - 1] != '\n') : (m_bol -= 1) {}

            // Walk upward across contiguous `/|` or `///` lines immediately above `m_bol`:
            var extract_start = m_bol;
            while (extract_start > prev_tok_end) {
                const prev_ln_end = extract_start - 1;
                var prev_ln_start = prev_ln_end;
                while (prev_ln_start > prev_tok_end and source[prev_ln_start - 1] != '\n') : (prev_ln_start -= 1) {}
                const ln_trimmed = std.mem.trimStart(
                    u8,
                    std.mem.trimEnd(u8, source[prev_ln_start..prev_ln_end], "\r"),
                    " \t",
                );
                const is_doc_ln = std.mem.startsWith(u8, ln_trimmed, "/|") or
                    (std.mem.startsWith(u8, ln_trimmed, "///") and
                        !std.mem.startsWith(u8, ln_trimmed, "////") and
                        !std.mem.startsWith(u8, ln_trimmed, "///|") and
                        !std.mem.startsWith(u8, ln_trimmed, "///#"));
                if (is_doc_ln) {
                    extract_start = prev_ln_start;
                } else {
                    break;
                }
            }

            // Include optional trailing `,` and trailing newline on `m_cst`:
            var m_copy_end: usize = m_sp.end_byte;
            var del_end: usize = m_sp.end_byte;
            if (m_sp.last_tok.asInt() + 1 < close_brace_tok.asInt()) {
                const after_rec = tok_buf.getToken(TokenIndex.fromInt(m_sp.last_tok.asInt() + 1));
                if (!after_rec.flags.is_synthesized and after_rec.kind == .comma) {
                    del_end = @as(usize, after_rec.byte_offset) + @as(usize, after_rec.byte_len);
                }
            }
            if (tok_buf.getToken(m_sp.last_tok).kind == .comma and m_sp.last_tok.asInt() > m_sp.first_tok.asInt()) {
                const before_comma = tok_buf.getToken(TokenIndex.fromInt(m_sp.last_tok.asInt() - 1));
                m_copy_end = @as(usize, before_comma.byte_offset) + @as(usize, before_comma.byte_len);
            }
            while (del_end < close_brace_rec.byte_offset and
                (source[del_end] == ' ' or source[del_end] == '\t')) : (del_end += 1)
            {}
            if (del_end < close_brace_rec.byte_offset and source[del_end] == '\r') del_end += 1;
            if (del_end < close_brace_rec.byte_offset and source[del_end] == '\n') del_end += 1;

            if (m_idx > 0) try extracted_body.appendSlice(allocator, "\n\n");
            const method_slice = std.mem.trimEnd(u8, source[extract_start..m_copy_end], " \t\r\n");
            if (extract_start == m_bol and m_bol == m_sp.start_byte) {
                try extracted_body.appendSlice(allocator, outer_indent);
                try extracted_body.appendSlice(allocator, "    ");
            }
            try extracted_body.appendSlice(allocator, method_slice);

            try pending_edits.append(allocator, .{
                .start_byte = @intCast(extract_start),
                .end_byte = @intCast(del_end),
                .replacement = "",
            });
        }
        if (!valid_extraction) continue;

        const impl_block = try std.fmt.allocPrint(
            allocator,
            "\n\n{s}impl{s} {s}{s}{s}{s} {{\n{s}\n{s}}}",
            .{
                outer_indent,
                impl_params_buf.items,
                type_name,
                type_args_buf.items,
                if (where_slice.len > 0) " " else "",
                where_slice,
                extracted_body.items,
                outer_indent,
            },
        );
        try owned_repls.append(allocator, impl_block);
        try pending_edits.append(allocator, .{
            .start_byte = close_brace_end,
            .end_byte = close_brace_end,
            .replacement = impl_block,
        });

        try collector.appendMultiEdits(
            .syntax_canonicalization,
            pending_edits.items,
            "UR-23-03: extract inline method from nominal type into adjacent `impl` block (`E0232`)",
        );
    }
}

/// Collects `UR-23-04` Sub-stage B fixes rewriting untyped `let _ = $e;` (`E0234`) and `(_, _) = $e;` (`E0235`) to `_ = $e;`.
/// Collects `UR-23-04` Sub-stage B `.machine_applicable` fixes emitted for `E0234` and `E0235` onto `collector`.
fn collectWildcardDiscardTier2Fixes(
    allocator: std.mem.Allocator,
    parse_sink: *const DiagnosticSink,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    rewritten_stmt_nodes: *std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    for (parse_sink.diagnostics.items) |diag_item| {
        if (diag_item.code != .e0234_non_binding_wildcard_let_var and
            diag_item.code != .e0235_all_wildcard_destructuring_assign)
        {
            continue;
        }
        var has_cloned_fix = false;
        for (diag_item.suggestions) |sug| {
            if (sug.applicability == .machine_applicable and sug.edits.len > 0) {
                try collector.appendClonedFix(collector.interner, sug);
                has_cloned_fix = true;
            }
        }
        if (!has_cloned_fix) continue;

        const diag_start = diag_item.primary_span.start_byte;
        var cst_i: usize = 0;
        while (cst_i < cst_count) : (cst_i += 1) {
            const cst_id = CstNodeIndex.fromInt(@intCast(cst_i));
            const rec = cst_arena.getNode(cst_id);
            if (rec.kind != .local_decl_stmt and rec.kind != .assign_stmt) continue;
            if (extractCstTokenSpan(cst_arena, tok_buf, cst_id)) |sp| {
                if (sp.start_byte <= diag_start and diag_start <= sp.end_byte) {
                    try rewritten_stmt_nodes.put(allocator, cst_id.asInt(), {});
                }
            }
        }
    }
}

/// Collects `UR-23-06` `.machine_applicable` `":"` insertion fixes emitted for `E0236` (`left_val u32` -> `left_val: u32`).
fn collectMissingColonBeforeTypeFixes(
    parse_sink: *const DiagnosticSink,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    var has_cloned_any = false;
    for (parse_sink.diagnostics.items) |diag_item| {
        if (diag_item.code != .e0236_missing_colon_before_type) continue;
        var has_fix = false;
        for (diag_item.suggestions) |sug| {
            if (sug.applicability == .machine_applicable and sug.edits.len > 0) {
                try collector.appendClonedFix(collector.interner, sug);
                has_fix = true;
                has_cloned_any = true;
            }
        }
        if (!has_fix and !diag_item.primary_span.file_id.isNone()) {
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                diag_item.primary_span.end_byte,
                diag_item.primary_span.end_byte,
                ":",
                "UR-23-06: insert missing `:` before type annotation (`E0236`)",
            );
            has_cloned_any = true;
        }
    }
    if (has_cloned_any) return;

    // Fallback; inspect synthesized `.colon` recovery tokens if `parse_sink` omitted suggestions:
    const tok_count = tok_buf.countTokens();
    var i: usize = 0;
    while (i < tok_count) : (i += 1) {
        const rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(i)));
        if (rec.flags.is_synthesized and rec.kind == .colon) {
            try collector.appendSingleEdit(
                .syntax_canonicalization,
                rec.byte_offset,
                rec.byte_offset,
                ":",
                "UR-23-06: insert missing `:` before type annotation (`E0236`)",
            );
        }
    }
}

/// Computes a comment-preserving deletion range `[start_byte .. end_byte)` for a removed `@attribute` span.
fn computeSafeAttrRemovalRange(
    source: []const u8,
    file_id: FileId,
    tok_buf: *const TokenBuffer,
    attr_span: Span,
    min_start_byte: u32,
) ByteInterval {
    const raw_rem = symbol_resolver.computeAttributeRemovalSpan(source, file_id, attr_span);
    const clamped_start: u32 = @max(raw_rem.start_byte, min_start_byte);
    const clamped_end: u32 = @max(raw_rem.end_byte, clamped_start);
    if (!hasCommentsInByteRange(source, tok_buf, clamped_start, clamped_end)) {
        return .{ .start = clamped_start, .end = clamped_end };
    }
    var tight_end: usize = @min(@as(usize, attr_span.end_byte), source.len);
    while (tight_end < source.len and (source[tight_end] == ' ' or source[tight_end] == '\t')) : (tight_end += 1) {}
    if (!hasCommentsInByteRange(source, tok_buf, attr_span.start_byte, @intCast(tight_end))) {
        return .{ .start = @max(attr_span.start_byte, min_start_byte), .end = @max(@as(u32, @intCast(tight_end)), min_start_byte) };
    }
    return .{ .start = @max(attr_span.start_byte, min_start_byte), .end = @max(attr_span.end_byte, min_start_byte) };
}

/// Splits top-level comma-separated argument slices inside `inner_args` while respecting nested delimiters and strings.
fn splitTopLevelAttrCommaArgsAlloc(
    allocator: std.mem.Allocator,
    inner_args: []const u8,
) !std.ArrayListUnmanaged([]const u8) {
    var parts: std.ArrayListUnmanaged([]const u8) = .empty;
    errdefer parts.deinit(allocator);
    if (inner_args.len == 0) return parts;

    var depth_paren: u32 = 0;
    var depth_bracket: u32 = 0;
    var depth_brace: u32 = 0;
    var seg_start: usize = 0;
    var cursor: usize = 0;
    while (cursor < inner_args.len) {
        const ch = inner_args[cursor];
        if (ch == '"' or ch == '\'') {
            const quote_ch = ch;
            cursor += 1;
            while (cursor < inner_args.len) {
                if (inner_args[cursor] == '\\' and cursor + 1 < inner_args.len) {
                    cursor += 2;
                    continue;
                }
                if (inner_args[cursor] == quote_ch) {
                    cursor += 1;
                    break;
                }
                cursor += 1;
            }
            continue;
        }
        if ((ch == 'r' or ch == 'b' or ch == 'f') and cursor + 1 < inner_args.len) {
            var hash_probe = cursor + 1;
            if (ch == 'b' and hash_probe < inner_args.len and inner_args[hash_probe] == 'r') {
                hash_probe += 1;
            }
            const hash_start = hash_probe;
            while (hash_probe < inner_args.len and inner_args[hash_probe] == '#') : (hash_probe += 1) {}
            const hash_n = hash_probe - hash_start;
            if (hash_probe < inner_args.len and inner_args[hash_probe] == '"' and (hash_n > 0 or inner_args[cursor] != 'b')) {
                cursor = hash_probe + 1;
                while (cursor < inner_args.len) : (cursor += 1) {
                    if (inner_args[cursor] == '"' and cursor + 1 + hash_n <= inner_args.len) {
                        var is_closed = true;
                        var hi: usize = 0;
                        while (hi < hash_n) : (hi += 1) {
                            if (inner_args[cursor + 1 + hi] != '#') {
                                is_closed = false;
                                break;
                            }
                        }
                        if (is_closed) {
                            cursor += 1 + hash_n;
                            break;
                        }
                    }
                }
                continue;
            }
        }
        switch (ch) {
            '(' => depth_paren += 1,
            ')' => depth_paren -|= 1,
            '[' => depth_bracket += 1,
            ']' => depth_bracket -|= 1,
            '{' => depth_brace += 1,
            '}' => depth_brace -|= 1,
            ',' => {
                if (depth_paren == 0 and depth_bracket == 0 and depth_brace == 0) {
                    const trimmed_seg = std.mem.trim(u8, inner_args[seg_start..cursor], " \t\r\n");
                    if (trimmed_seg.len > 0) try parts.append(allocator, trimmed_seg);
                    seg_start = cursor + 1;
                }
            },
            else => {},
        }
        cursor += 1;
    }
    const tail_seg = std.mem.trim(u8, inner_args[seg_start..], " \t\r\n");
    if (tail_seg.len > 0) try parts.append(allocator, tail_seg);
    return parts;
}

/// Strips an optional `key:` or `key =` prefix from an attribute argument and trims whitespace.
fn stripOptionalAttrKeyPrefix(raw_arg: []const u8, allowed_keys: []const []const u8) []const u8 {
    const trimmed = std.mem.trim(u8, raw_arg, " \t\r\n");
    for (allowed_keys) |key_name| {
        if (trimmed.len > key_name.len and std.mem.startsWith(u8, trimmed, key_name)) {
            const after_key = std.mem.trimStart(u8, trimmed[key_name.len..], " \t");
            if (after_key.len > 0 and (after_key[0] == ':' or after_key[0] == '=')) {
                return std.mem.trim(u8, after_key[1..], " \t\r\n");
            }
        }
    }
    return trimmed;
}

/// Normalizes an `@align(…)` / `@repr(align: …)` value (`cache_line` -> `.CacheLine`).
fn normalizeReprAlignValue(raw_arg: []const u8) []const u8 {
    const clean = stripOptionalAttrKeyPrefix(raw_arg, &.{ "bytes", "align" });
    if (CACHE_LINE_ALIAS_SET.has(clean)) {
        return ".CacheLine";
    }
    return clean;
}

/// Normalizes a `@packed` / `@packed(k)` / `@repr(packed: …)` value.
fn normalizeReprPackedValue(raw_arg: []const u8) []const u8 {
    const clean = stripOptionalAttrKeyPrefix(raw_arg, &.{ "packed", "align", "bytes" });
    return if (clean.len > 0) clean else "true";
}

/// Participating CST attribute entry for `UR-24-03` `@repr(…)` / `@link(…)` coalescing.
const CoalescedAttrCstEntry = struct {
    /// Attribute identifier (`"repr"`, `"repr_c"`, `"align"`, `"link_name"`, etc.).
    name: []const u8,
    /// Full `@attr(…)` source byte span.
    span: Span,
    /// Trimmed interior of `( … )`, or `""` when parameterless.
    inner_args: []const u8,
    /// `true` when `name` is a retired standalone attribute rather than `@repr` / `@link`.
    is_retired: bool,
};

/// Collects `UR-24-03` fixes coalescing retired layout/link attributes into canonical `@repr(…)` and `@link(…)`.
fn collectConsolidatedReprAndLinkFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    rewritten_enum_items: *const std.AutoHashMapUnmanaged(u32, void),
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    if (cst_count == 0) return;

    const visited_attr_cst = try allocator.alloc(bool, cst_count);
    defer allocator.free(visited_attr_cst);
    @memset(visited_attr_cst, false);

    var idx: usize = 0;
    while (idx < cst_count) : (idx += 1) {
        const item_cst = CstNodeIndex.fromInt(@intCast(idx));
        const item_rec = cst_arena.getNode(item_cst);
        if (item_rec.kind == .attribute or item_rec.subtree_size <= 1) continue;
        const sub_end = @min(idx + @max(@as(usize, item_rec.subtree_size), 1), cst_count);

        var layout_entries: std.ArrayListUnmanaged(CoalescedAttrCstEntry) = .empty;
        defer layout_entries.deinit(allocator);
        var link_entries: std.ArrayListUnmanaged(CoalescedAttrCstEntry) = .empty;
        defer link_entries.deinit(allocator);

        var child_cur = idx + 1;
        while (child_cur < sub_end) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cur));
            const child_rec = cst_arena.getNode(child_id);
            if (child_rec.kind == .attribute and !visited_attr_cst[child_cur]) {
                visited_attr_cst[child_cur] = true;
                if (extractCstTokenSpan(cst_arena, tok_buf, child_id)) |attr_sp| {
                    if (!hasCommentsInByteRange(source, tok_buf, attr_sp.start_byte, attr_sp.end_byte) and
                        attr_sp.first_tok.asInt() + 1 <= attr_sp.last_tok.asInt() and
                        tok_buf.getToken(attr_sp.first_tok).kind == .at)
                    {
                        const name_tok = TokenIndex.fromInt(attr_sp.first_tok.asInt() + 1);
                        const attr_name = symbol_resolver.extractTokenSlice(source, tok_buf, name_tok);
                        if (DR24_COALESCED_ATTR_SET.has(attr_name)) {
                            var inner_args: []const u8 = "";
                            var is_well_formed = true;
                            if (attr_sp.first_tok.asInt() + 2 <= attr_sp.last_tok.asInt()) {
                                const open_tok = TokenIndex.fromInt(attr_sp.first_tok.asInt() + 2);
                                const close_tok = attr_sp.last_tok;
                                if (tok_buf.getToken(open_tok).kind == .lparen and
                                    tok_buf.getToken(close_tok).kind == .rparen)
                                {
                                    const open_rec = tok_buf.getToken(open_tok);
                                    const close_rec = tok_buf.getToken(close_tok);
                                    const body_lo: usize = @min(
                                        @as(usize, open_rec.byte_offset) + @as(usize, open_rec.byte_len),
                                        source.len,
                                    );
                                    const body_hi: usize = @min(@as(usize, close_rec.byte_offset), source.len);
                                    if (body_lo <= body_hi) {
                                        inner_args = std.mem.trim(u8, source[body_lo..body_hi], " \t\r\n");
                                    }
                                } else {
                                    is_well_formed = false;
                                }
                            }
                            if (is_well_formed) {
                                const attr_span = Span.init(file_id, attr_sp.start_byte, attr_sp.end_byte);
                                if (std.mem.startsWith(u8, attr_name, "link")) {
                                    try link_entries.append(allocator, .{
                                        .name = attr_name,
                                        .span = attr_span,
                                        .inner_args = inner_args,
                                        .is_retired = !std.mem.eql(u8, attr_name, "link"),
                                    });
                                } else {
                                    try layout_entries.append(allocator, .{
                                        .name = attr_name,
                                        .span = attr_span,
                                        .inner_args = inner_args,
                                        .is_retired = !std.mem.eql(u8, attr_name, "repr"),
                                    });
                                }
                            }
                        }
                    }
                }
            }
            child_cur += @max(@as(usize, child_rec.subtree_size), 1);
        }

        // [1] Coalesce layout group (`@repr`, `@repr_c`, `@packed`, `@align`, `@cache_aligned`, `@zero_pad`):
        if (layout_entries.items.len > 0 and !rewritten_enum_items.contains(item_cst.asInt())) {
            var base_mode: ?[]const u8 = null;
            var packed_val: ?[]const u8 = null;
            var align_val: ?[]const u8 = null;
            var zero_pad_val: ?[]const u8 = null;
            var has_retired_or_multi = layout_entries.items.len > 1;
            var is_layout_valid = true;

            for (layout_entries.items) |entry| {
                if (entry.is_retired) has_retired_or_multi = true;
                if (std.mem.eql(u8, entry.name, "repr_c")) {
                    if (entry.inner_args.len > 0) {
                        is_layout_valid = false;
                        break;
                    }
                    base_mode = "C";
                } else if (std.mem.eql(u8, entry.name, "packed")) {
                    packed_val = normalizeReprPackedValue(entry.inner_args);
                    if (base_mode == null) base_mode = "C";
                } else if (std.mem.eql(u8, entry.name, "align")) {
                    const norm_align = normalizeReprAlignValue(entry.inner_args);
                    if (norm_align.len == 0) {
                        is_layout_valid = false;
                        break;
                    }
                    align_val = norm_align;
                } else if (std.mem.eql(u8, entry.name, "cache_aligned")) {
                    if (entry.inner_args.len > 0) {
                        is_layout_valid = false;
                        break;
                    }
                    align_val = ".CacheLine";
                } else if (std.mem.eql(u8, entry.name, "zero_pad")) {
                    const clean_zp = stripOptionalAttrKeyPrefix(entry.inner_args, &.{"zero_pad"});
                    zero_pad_val = if (clean_zp.len > 0) clean_zp else "true";
                } else if (std.mem.eql(u8, entry.name, "repr")) {
                    var sub_parts = try splitTopLevelAttrCommaArgsAlloc(allocator, entry.inner_args);
                    defer sub_parts.deinit(allocator);
                    if (sub_parts.items.len == 0) {
                        is_layout_valid = false;
                        break;
                    }
                    for (sub_parts.items) |part| {
                        if (std.mem.eql(u8, part, "C") or std.mem.eql(u8, part, "c")) {
                            base_mode = "C";
                        } else if (std.mem.eql(u8, part, "transparent")) {
                            base_mode = "transparent";
                        } else if (std.mem.eql(u8, part, "packed")) {
                            packed_val = "true";
                            if (base_mode == null) base_mode = "C";
                        } else if (std.mem.startsWith(u8, part, "packed") and
                            part.len > 6 and
                            (part[6] == ':' or part[6] == '=' or part[6] == ' ' or part[6] == '\t' or part[6] == '('))
                        {
                            if (part[6] == '(' and part[part.len - 1] == ')') {
                                packed_val = normalizeReprPackedValue(part[7 .. part.len - 1]);
                            } else {
                                packed_val = normalizeReprPackedValue(part);
                            }
                            if (base_mode == null) base_mode = "C";
                        } else if (CACHE_LINE_ALIAS_SET.has(part)) {
                            align_val = ".CacheLine";
                        } else if (std.mem.startsWith(u8, part, "align") and
                            part.len > 5 and
                            (part[5] == ':' or part[5] == '=' or part[5] == ' ' or part[5] == '\t' or part[5] == '('))
                        {
                            const norm_align = if (part[5] == '(' and part[part.len - 1] == ')')
                                normalizeReprAlignValue(part[6 .. part.len - 1])
                            else
                                normalizeReprAlignValue(part);
                            if (norm_align.len == 0) {
                                is_layout_valid = false;
                                break;
                            }
                            align_val = norm_align;
                        } else if (std.mem.eql(u8, part, "zero_pad")) {
                            zero_pad_val = "true";
                        } else if (std.mem.startsWith(u8, part, "zero_pad") and
                            part.len > 8 and
                            (part[8] == ':' or part[8] == '=' or part[8] == ' ' or part[8] == '\t'))
                        {
                            const clean_zp = stripOptionalAttrKeyPrefix(part, &.{"zero_pad"});
                            zero_pad_val = if (clean_zp.len > 0) clean_zp else "true";
                        } else {
                            // Unrecognized `@repr(…)` argument (e.g., enum integer backing before `UR-22-04`); skip:
                            is_layout_valid = false;
                            break;
                        }
                    }
                    if (!is_layout_valid) break;
                }
            }

            if (is_layout_valid and (base_mode != null or packed_val != null or align_val != null or zero_pad_val != null)) {
                var repr_buf: std.ArrayList(u8) = .empty;
                defer repr_buf.deinit(allocator);
                try repr_buf.appendSlice(allocator, "@repr(");
                var has_emitted_arg = false;
                if (base_mode) |base_str| {
                    try repr_buf.appendSlice(allocator, base_str);
                    has_emitted_arg = true;
                }
                if (packed_val) |pk_str| {
                    if (has_emitted_arg) try repr_buf.appendSlice(allocator, ", ");
                    try repr_buf.appendSlice(allocator, "packed: ");
                    try repr_buf.appendSlice(allocator, pk_str);
                    has_emitted_arg = true;
                }
                if (align_val) |al_str| {
                    if (has_emitted_arg) try repr_buf.appendSlice(allocator, ", ");
                    try repr_buf.appendSlice(allocator, "align: ");
                    try repr_buf.appendSlice(allocator, al_str);
                    has_emitted_arg = true;
                }
                if (zero_pad_val) |zp_str| {
                    if (has_emitted_arg) try repr_buf.appendSlice(allocator, ", ");
                    try repr_buf.appendSlice(allocator, "zero_pad: ");
                    try repr_buf.appendSlice(allocator, zp_str);
                }
                try repr_buf.append(allocator, ')');

                const first_sp = layout_entries.items[0].span;
                const first_raw = source[first_sp.start_byte..first_sp.end_byte];
                if (has_retired_or_multi or !std.mem.eql(u8, first_raw, repr_buf.items)) {
                    var edits: std.ArrayList(PendingByteEdit) = .empty;
                    defer edits.deinit(allocator);
                    try edits.append(allocator, .{
                        .start_byte = first_sp.start_byte,
                        .end_byte = first_sp.end_byte,
                        .replacement = repr_buf.items,
                    });
                    var min_erase_start: u32 = first_sp.end_byte;
                    for (layout_entries.items[1..]) |tail_entry| {
                        const rem = computeSafeAttrRemovalRange(
                            source,
                            file_id,
                            tok_buf,
                            tail_entry.span,
                            min_erase_start,
                        );
                        try edits.append(allocator, .{
                            .start_byte = @intCast(rem.start),
                            .end_byte = @intCast(rem.end),
                            .replacement = "",
                        });
                        min_erase_start = @intCast(rem.end);
                    }
                    try collector.appendMultiEdits(
                        .syntax_canonicalization,
                        edits.items,
                        "UR-24-03: coalesce layout attributes into canonical `@repr(…)` (`E0239`)",
                    );
                }
            }
        }

        // [2] Coalesce linkage group (`@link`, `@link_name`, `@link_section`):
        if (link_entries.items.len > 0) {
            var link_name_val: ?[]const u8 = null;
            var link_section_val: ?[]const u8 = null;
            var has_retired_or_multi_link = link_entries.items.len > 1;
            var is_link_valid = true;

            for (link_entries.items) |entry| {
                if (entry.is_retired) has_retired_or_multi_link = true;
                if (std.mem.eql(u8, entry.name, "link_name")) {
                    const clean_nm = stripOptionalAttrKeyPrefix(entry.inner_args, &.{"name"});
                    if (clean_nm.len == 0) {
                        is_link_valid = false;
                        break;
                    }
                    link_name_val = clean_nm;
                } else if (std.mem.eql(u8, entry.name, "link_section")) {
                    const clean_sec = stripOptionalAttrKeyPrefix(entry.inner_args, &.{"section"});
                    if (clean_sec.len == 0) {
                        is_link_valid = false;
                        break;
                    }
                    link_section_val = clean_sec;
                } else if (std.mem.eql(u8, entry.name, "link")) {
                    var sub_parts = try splitTopLevelAttrCommaArgsAlloc(allocator, entry.inner_args);
                    defer sub_parts.deinit(allocator);
                    if (sub_parts.items.len == 0) {
                        is_link_valid = false;
                        break;
                    }
                    for (sub_parts.items) |part| {
                        if (std.mem.startsWith(u8, part, "name")) {
                            const clean_nm = stripOptionalAttrKeyPrefix(part, &.{"name"});
                            if (clean_nm.len == 0 or std.mem.eql(u8, clean_nm, part)) {
                                is_link_valid = false;
                                break;
                            }
                            link_name_val = clean_nm;
                        } else if (std.mem.startsWith(u8, part, "section")) {
                            const clean_sec = stripOptionalAttrKeyPrefix(part, &.{"section"});
                            if (clean_sec.len == 0 or std.mem.eql(u8, clean_sec, part)) {
                                is_link_valid = false;
                                break;
                            }
                            link_section_val = clean_sec;
                        } else {
                            is_link_valid = false;
                            break;
                        }
                    }
                    if (!is_link_valid) break;
                }
            }

            if (is_link_valid and (link_name_val != null or link_section_val != null)) {
                var link_buf: std.ArrayList(u8) = .empty;
                defer link_buf.deinit(allocator);
                try link_buf.appendSlice(allocator, "@link(");
                if (link_name_val) |nm_str| {
                    try link_buf.appendSlice(allocator, "name: ");
                    try link_buf.appendSlice(allocator, nm_str);
                }
                if (link_section_val) |sec_str| {
                    if (link_name_val != null) try link_buf.appendSlice(allocator, ", ");
                    try link_buf.appendSlice(allocator, "section: ");
                    try link_buf.appendSlice(allocator, sec_str);
                }
                try link_buf.append(allocator, ')');

                const first_sp = link_entries.items[0].span;
                const first_raw = source[first_sp.start_byte..first_sp.end_byte];
                if (has_retired_or_multi_link or !std.mem.eql(u8, first_raw, link_buf.items)) {
                    var edits: std.ArrayList(PendingByteEdit) = .empty;
                    defer edits.deinit(allocator);
                    try edits.append(allocator, .{
                        .start_byte = first_sp.start_byte,
                        .end_byte = first_sp.end_byte,
                        .replacement = link_buf.items,
                    });
                    var min_erase_start: u32 = first_sp.end_byte;
                    for (link_entries.items[1..]) |tail_entry| {
                        const rem = computeSafeAttrRemovalRange(
                            source,
                            file_id,
                            tok_buf,
                            tail_entry.span,
                            min_erase_start,
                        );
                        try edits.append(allocator, .{
                            .start_byte = @intCast(rem.start),
                            .end_byte = @intCast(rem.end),
                            .replacement = "",
                        });
                        min_erase_start = @intCast(rem.end);
                    }
                    try collector.appendMultiEdits(
                        .syntax_canonicalization,
                        edits.items,
                        "UR-24-03: coalesce linkage attributes into canonical `@link(…)` (`E0239`)",
                    );
                }
            }
        }
    }
}

/// Collects `UR-24-04` fixes unwrapping `@[a, b]` and `@(a, b)` grouped attribute lists into `@a @b`.
fn collectUnwrapGroupedAttrListFixes(
    allocator: std.mem.Allocator,
    source: []const u8,
    tok_buf: *const TokenBuffer,
    collector: *FixCollector,
) !void {
    const tok_count = tok_buf.countTokens();
    var tok_i: usize = 0;
    while (tok_i + 2 < tok_count) : (tok_i += 1) {
        const at_rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_i)));
        if (at_rec.flags.is_synthesized or at_rec.kind != .at) continue;
        const open_rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_i + 1)));
        if (open_rec.flags.is_synthesized or (open_rec.kind != .lbracket and open_rec.kind != .lparen)) continue;
        const close_kind: TokenKind = if (open_rec.kind == .lbracket) .rbracket else .rparen;

        var depth: u32 = 1;
        var close_opt: ?usize = null;
        var scan_i: usize = tok_i + 2;
        while (scan_i < tok_count) : (scan_i += 1) {
            const scan_rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(scan_i)));
            if (scan_rec.flags.is_synthesized) continue;
            if (scan_rec.kind == open_rec.kind) {
                depth += 1;
            } else if (scan_rec.kind == close_kind) {
                depth -= 1;
                if (depth == 0) {
                    close_opt = scan_i;
                    break;
                }
            }
        }
        const close_idx = close_opt orelse continue;
        const close_rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(close_idx)));
        const full_end: u32 = close_rec.byte_offset +| close_rec.byte_len;
        if (hasCommentsInByteRange(source, tok_buf, at_rec.byte_offset, full_end)) continue;

        const inner_lo: usize = @min(@as(usize, open_rec.byte_offset) + @as(usize, open_rec.byte_len), source.len);
        const inner_hi: usize = @min(@as(usize, close_rec.byte_offset), source.len);
        if (inner_lo >= inner_hi) continue;
        var elems = try splitTopLevelAttrCommaArgsAlloc(allocator, source[inner_lo..inner_hi]);
        defer elems.deinit(allocator);
        if (elems.items.len == 0) continue;

        var out_buf: std.ArrayList(u8) = .empty;
        defer out_buf.deinit(allocator);
        for (elems.items, 0..) |raw_elem, elem_i| {
            if (elem_i > 0) try out_buf.append(allocator, ' ');
            const clean_elem = if (std.mem.startsWith(u8, raw_elem, "@"))
                std.mem.trimStart(u8, raw_elem[1..], " \t")
            else
                raw_elem;
            try out_buf.append(allocator, '@');
            try out_buf.appendSlice(allocator, clean_elem);
        }
        try collector.appendSingleEdit(
            .syntax_canonicalization,
            at_rec.byte_offset,
            full_end,
            out_buf.items,
            "UR-24-04: unwrap grouped `@[…]` / `@(…)` attribute list into `@attr` sequence (`E0239`)",
        );
        tok_i = close_idx;
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
    const is_ur23_01 = isRuleEnabled(options.rule_mask, .ur_23_01_doc_comment_placement_and_attachment);
    const is_ur23_03 = isRuleEnabled(options.rule_mask, .ur_23_03_impl_visibility_and_inline_type_methods);
    const is_ur23_04 = isRuleEnabled(options.rule_mask, .ur_23_04_canonical_wildcard_discard_stmt);
    const is_ur23_06 = isRuleEnabled(options.rule_mask, .ur_23_06_missing_colon_before_type);
    const is_ur24_03 = isRuleEnabled(options.rule_mask, .ur_24_03_consolidated_repr_and_link_attrs);
    const is_ur24_04 = isRuleEnabled(options.rule_mask, .ur_24_04_unwrap_grouped_attribute_lists);

    if (!is_ur21_01 and !is_ur21_02 and !is_ur21_03 and !is_ur22_01 and
        !is_ur22_02 and !is_ur22_03 and !is_ur22_04 and !is_ur22_05 and
        !is_ur23_01 and !is_ur23_03 and !is_ur23_04 and !is_ur23_06 and
        !is_ur24_03 and !is_ur24_04)
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
    var rewritten_enum_items: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer rewritten_enum_items.deinit(allocator);

    if (is_ur23_01) {
        try collectDocCommentPlacementFixes(allocator, source, &cst_arena, &tok_buf, collector);
    }
    if (is_ur23_06) {
        try collectMissingColonBeforeTypeFixes(&parse_sink, &tok_buf, collector);
    }
    if (is_ur23_03) {
        try collectImplVisAndInlineTypeMethodFixes(allocator, source, &cst_arena, &tok_buf, collector);
    }
    if (is_ur23_04) {
        try collectWildcardDiscardTier2Fixes(
            allocator,
            &parse_sink,
            &cst_arena,
            &tok_buf,
            &rewritten_stmt_nodes,
            collector,
        );
    }
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
            is_ur24_03,
            &rewritten_enum_items,
            collector,
        );
    }
    if (is_ur24_04) {
        try collectUnwrapGroupedAttrListFixes(allocator, source, &tok_buf, collector);
    }
    if (is_ur24_03) {
        try collectConsolidatedReprAndLinkFixes(
            allocator,
            source,
            file_id,
            &cst_arena,
            &tok_buf,
            &rewritten_enum_items,
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

/// Returns `true` if `kind` owns executable expressions or bodies carrying `BodySemanticSideTables`.
inline fn hasBodySideTablesItemKind(kind: query_db.ItemKind) bool {
    return switch (kind) {
        .fn_decl,
        .impl_decl,
        .const_decl,
        .extern_block,
        .subscript_decl,
        .test_decl,
        .bench_decl,
        => true,
        .mod_decl,
        .use_decl,
        .struct_decl,
        .enum_decl,
        .union_decl,
        .trait_decl,
        .type_alias_decl,
        .ffi_extern_block,
        .extern_static,
        => false,
    };
}

/// Fetches `BodySemanticSideTables` for `def_id`, propagating `OutOfMemory` while ignoring non-fatal query errors.
inline fn getDefSideTablesBestEffort(
    db: *CompilerDb,
    def_id: DefId,
) error{OutOfMemory}!?*const type_system.BodySemanticSideTables {
    return db.getDefSideTables(def_id) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => null,
    };
}

/// Looks up the cached `BodySemanticSideTables` for `def_id` in $O(1)$, computing it lazily only on cache miss.
inline fn getCachedOrComputeDefSideTables(
    db: *CompilerDb,
    def_id: DefId,
) error{OutOfMemory}!?*const type_system.BodySemanticSideTables {
    if (def_id.isNone()) return null;
    if (db.parsed_artifacts.getPtr(def_id.fileId().asInt())) |parsed_ptr| {
        if (db.def_side_tables.getPtr(def_id.asInt())) |cached_st| {
            if (!query_db.Fingerprint128.eql(cached_st.ast_fingerprint, query_db.Fingerprint128.ZERO) and
                query_db.Fingerprint128.eql(cached_st.ast_fingerprint, parsed_ptr.ast_fingerprint))
            {
                return cached_st;
            }
        }
    }
    return getDefSideTablesBestEffort(db, def_id);
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
        if (!hasBodySideTablesItemKind(entry.kind)) continue;
        if (try getCachedOrComputeDefSideTables(db, entry.def_id)) |def_st| {
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
        if (!hasBodySideTablesItemKind(entry.kind)) continue;
        if (try getCachedOrComputeDefSideTables(db, entry.def_id)) |def_st| {
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
        if (!hasBodySideTablesItemKind(entry.kind)) continue;
        if (try getCachedOrComputeDefSideTables(db, entry.def_id)) |def_st| {
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
        if (!hasBodySideTablesItemKind(entry.kind)) continue;
        if (try getCachedOrComputeDefSideTables(db, entry.def_id)) |def_st| {
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
                if (!hasBodySideTablesItemKind(entry.kind)) continue;
                if (try getCachedOrComputeDefSideTables(db, entry.def_id)) |def_st| {
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

/// Open CST subtree frame used while building `computeCstParentMap`.
const CstParentFrame = struct {
    /// Enclosing CST node index.
    node_id: CstNodeIndex,
    /// Exclusive ending CST node index (`node_id + subtree_size`).
    end_idx: usize,
};

/// Builds a dense `CstNodeIndex -> parent CstNodeIndex` table across `cst_arena` in $O(N)$ time.
fn computeCstParentMap(allocator: std.mem.Allocator, cst_arena: *const LosslessCstArena) ![]CstNodeIndex {
    const cst_count = cst_arena.countNodes();
    const parents = try allocator.alloc(CstNodeIndex, cst_count);
    errdefer allocator.free(parents);
    @memset(parents, .none);
    if (cst_count == 0) return parents;

    var stack: std.ArrayList(CstParentFrame) = .empty;
    defer stack.deinit(allocator);

    var idx: usize = 0;
    while (idx < cst_count) : (idx += 1) {
        while (stack.items.len > 0 and idx >= stack.items[stack.items.len - 1].end_idx) {
            _ = stack.pop();
        }
        if (stack.items.len > 0) {
            parents[idx] = stack.items[stack.items.len - 1].node_id;
        }
        const rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(idx)));
        if (rec.subtree_size > 1) {
            try stack.append(allocator, .{
                .node_id = CstNodeIndex.fromInt(@intCast(idx)),
                .end_idx = @min(idx + @as(usize, rec.subtree_size), cst_count),
            });
        }
    }
    return parents;
}

/// Locates the innermost `.named_type` CST node whose sole identifier span equals `[start_byte .. end_byte)`.
fn findEnclosingSimpleNamedTypeCst(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    start_byte: u32,
    end_byte: u32,
) CstNodeIndex {
    const cst_count = cst_arena.countNodes();
    var best_cst: CstNodeIndex = .none;
    var cst_i: usize = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const cid = CstNodeIndex.fromInt(@intCast(cst_i));
        const rec = cst_arena.getNode(cid);
        if (rec.kind != .named_type) continue;
        const sp = extractCstTokenSpan(cst_arena, tok_buf, cid) orelse continue;
        if (sp.start_byte == start_byte and sp.end_byte == end_byte and sp.first_tok == sp.last_tok) {
            best_cst = cid;
        }
    }
    return best_cst;
}

/// Harvests `E0424` mutability hints, `E0421` `~Copy` completions, `UR-23-05` foreign scalars, and allowlisted fixes.
fn scanSinkForTier3(
    alloc: std.mem.Allocator,
    db_ptr: *CompilerDb,
    fid: FileId,
    src_bytes: []const u8,
    cst: *const LosslessCstArena,
    cst_parents: []const CstNodeIndex,
    tb: *const TokenBuffer,
    sink_ptr: *const DiagnosticSink,
    is_enable_ur22_02: bool,
    is_enable_ur23_05: bool,
    is_enable_general: bool,
    is_internal_core_mode: bool,
    mut_map: *std.AutoHashMapUnmanaged(u32, bool),
    ur23_05_seen: *std.AutoHashMapUnmanaged(u32, void),
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

        // `UR-23-05`; rewrite unresolved `PascalCase` foreign scalar inside `.named_type` (`E0403`):
        if (is_enable_ur23_05 and diag_item.code == .e0403_unresolved_symbol) {
            const start_b = diag_item.primary_span.start_byte;
            const end_b = diag_item.primary_span.end_byte;
            if (start_b < end_b and @as(usize, end_b) <= src_bytes.len and !ur23_05_seen.contains(start_b)) {
                const named_cst = findEnclosingSimpleNamedTypeCst(cst, tb, start_b, end_b);
                if (!named_cst.isNone()) {
                    const lexeme = src_bytes[start_b..end_b];
                    if (symbol_resolver.lookupUnambiguousForeignScalar(lexeme)) |mapped_prim| {
                        var is_under_ptr_type = false;
                        var cur_parent = if (named_cst.asInt() < cst_parents.len)
                            cst_parents[named_cst.asInt()]
                        else
                            .none;
                        if (!cur_parent.isNone() and cur_parent.asInt() < cst.countNodes() and
                            cst.getNode(cur_parent).kind == .ptr_type)
                        {
                            is_under_ptr_type = true;
                        }
                        const final_prim: []const u8 = if (is_under_ptr_type and std.mem.eql(u8, lexeme, "Void"))
                            "opaque"
                        else
                            mapped_prim;
                        try ur23_05_seen.put(alloc, start_b, {});
                        try col.appendSingleEdit(
                            .type_migration,
                            start_b,
                            end_b,
                            final_prim,
                            "UR-23-05: rewrite foreign scalar type name to lowercase CoreX primitive (`E0403`)",
                        );
                    }
                }
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

/// Parsed probe result for a single `{Expr[=][:Spec]}` candidate inside an unmarked `"…"` literal (`UR-24-01` Branch B).
const UnmarkedHoleProbe = struct {
    /// Byte offset after opening `{` inside the literal's `body` slice.
    hole_body_start: usize,
    /// Byte offset of closing `}` inside the literal's `body` slice.
    hole_body_end: usize,
    /// Trimmed expression slice inside `{…}`.
    expr_slice: []const u8,
    /// Verbatim `:Spec` suffix (`""` when absent).
    spec_with_colon: []const u8,
    /// `true` when `{expr=}` debug shorthand is present.
    has_debug_eq: bool,
    /// `true` when the parsed expression is a bare identifier (`{ident}`) rather than a compound expression.
    is_bare_ident: bool,
};

/// Parses `expr_slice` inside `fn __p__() { let __x = <expr>; }` to verify it is a valid single expression.
fn probeSingleHoleExprSyntax(
    allocator: std.mem.Allocator,
    expr_slice: []const u8,
) !?struct { is_bare_ident: bool } {
    const trimmed = std.mem.trim(u8, expr_slice, " \t\r\n");
    if (trimmed.len == 0) return null;
    if (std.mem.indexOfScalar(u8, trimmed, ';') != null) return null;

    const probe_src = try std.fmt.allocPrint(allocator, "fn __cx_probe__() {{\n    let __cx_v = (\n{s}\n    );\n}}\n", .{trimmed});
    defer allocator.free(probe_src);

    var probe_interner = try StringInterner.init(allocator);
    defer probe_interner.deinit();
    var probe_toks = TokenBuffer.init(allocator);
    defer probe_toks.deinit();
    var probe_cst = LosslessCstArena.init(allocator);
    defer probe_cst.deinit();
    var probe_ast = AstArena.init(allocator);
    defer probe_ast.deinit();
    var probe_sink = DiagnosticSink.init(allocator);
    defer probe_sink.deinit();

    _ = try parser.parseSource(
        probe_src,
        FileId.fromInt(999_991),
        &probe_toks,
        &probe_cst,
        &probe_ast,
        &probe_sink,
        &probe_interner,
    );
    if (probe_sink.error_count > 0) return null;

    // Reject top-level comma tuples caused by our `( … )` wrapper when `trimmed` itself wasn't parenthesized:
    if (trimmed[0] != '(') {
        var depth: u32 = 0;
        var ti: usize = 0;
        while (ti < probe_toks.countTokens()) : (ti += 1) {
            const tr = probe_toks.getToken(TokenIndex.fromInt(@intCast(ti)));
            if (tr.flags.is_synthesized) continue;
            if (tr.byte_offset < 33 or tr.byte_offset >= 33 + trimmed.len) continue;
            if (depth == 0 and tr.kind == .comma) return null;
            switch (tr.kind) {
                .lparen, .lbracket, .lbrace => depth += 1,
                .rparen, .rbracket, .rbrace => depth -|= 1,
                else => {},
            }
        }
    }

    // Count real tokens inside `trimmed` to classify bare identifier `{ident}` vs compound expression:
    var inner_tok_count: usize = 0;
    var sole_tok_kind: TokenKind = .eof;
    var scan_i: usize = 0;
    while (scan_i < probe_toks.countTokens()) : (scan_i += 1) {
        const tr = probe_toks.getToken(TokenIndex.fromInt(@intCast(scan_i)));
        if (tr.flags.is_synthesized or tr.kind == .eof) continue;
        if (tr.byte_offset < 33 or tr.byte_offset >= 33 + trimmed.len) continue;
        inner_tok_count += 1;
        sole_tok_kind = tr.kind;
    }
    if (inner_tok_count == 0) return null;
    const is_bare_id = inner_tok_count == 1 and
        (sole_tok_kind == .ident or sole_tok_kind == .const_ident or sole_tok_kind == .type_ident);
    return .{ .is_bare_ident = is_bare_id };
}

/// Returns `true` if `cst_kind` forms a lexical binding boundary for local variables (`UR-24-01` Branch B).
inline fn isLexicalScopeCstKind(cst_kind: CstNodeKind) bool {
    return switch (cst_kind) {
        .block,
        .for_stmt,
        .while_stmt,
        .loop_expr,
        .match_arm,
        .closure_expr,
        .fn_item,
        .impl_member,
        .trait_member,
        .subscript_item,
        .test_item,
        .bench_item,
        => true,
        else => false,
    };
}

/// Checks whether a bare `{ident}` inside an unmarked string at `str_tok_idx` resolves in `db` or CST `param_list`.
fn isBareIdentResolvedAtStringSite(
    db: *CompilerDb,
    file_id: FileId,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    cst_parents: []const CstNodeIndex,
    tok_buf: *const TokenBuffer,
    item_tree: *const query_db.ItemTree,
    leaf_cst_for_tok: CstNodeIndex,
    str_start_byte: u32,
    ident_name: []const u8,
) bool {
    const cst_count = cst_arena.countNodes();

    // [1] Check enclosing CST `.fn_item` / `.impl_member` / `.closure_expr` / `.for_expr` parameter & loop bindings:
    var cur_cst = leaf_cst_for_tok;
    var walk_steps: usize = 0;
    while (!cur_cst.isNone() and cur_cst.asInt() < cst_count and walk_steps < 256) : (walk_steps += 1) {
        const cur_rec = cst_arena.getNode(cur_cst);
        if (cur_rec.kind == .fn_item or cur_rec.kind == .impl_member or
            cur_rec.kind == .trait_member or cur_rec.kind == .subscript_item)
        {
            const fn_end = @min(@as(usize, cur_cst.asInt()) + @max(@as(usize, cur_rec.subtree_size), 1), cst_count);
            var sub_i: usize = cur_cst.asInt() + 1;
            while (sub_i < fn_end) : (sub_i += 1) {
                const sub_id = CstNodeIndex.fromInt(@intCast(sub_i));
                const sub_rec = cst_arena.getNode(sub_id);
                if (sub_rec.kind == .block) break;
                if (sub_rec.kind == .fn_param) {
                    if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |p_sp| {
                        var pt: u32 = p_sp.first_tok.asInt();
                        while (pt <= p_sp.last_tok.asInt()) : (pt += 1) {
                            const pk = tok_buf.getToken(TokenIndex.fromInt(pt)).kind;
                            if (pk == .colon or pk == .eq) break;
                            if (pk == .ident or pk == .kw_self_val) {
                                const p_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(pt));
                                if (std.mem.eql(u8, p_lex, ident_name)) return true;
                            }
                        }
                    }
                }
            }
        } else if (cur_rec.kind == .closure_expr) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cur_cst)) |cl_sp| {
                const first_k = tok_buf.getToken(cl_sp.first_tok).kind;
                if (first_k == .pipe) {
                    var ct: u32 = cl_sp.first_tok.asInt() + 1;
                    var in_type = false;
                    while (ct <= cl_sp.last_tok.asInt()) : (ct += 1) {
                        const ck = tok_buf.getToken(TokenIndex.fromInt(ct)).kind;
                        if (ck == .pipe) break;
                        if (ck == .colon) in_type = true else if (ck == .comma) in_type = false;
                        if (!in_type and ck == .ident) {
                            const c_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ct));
                            if (std.mem.eql(u8, c_lex, ident_name)) return true;
                        }
                    }
                }
            }
        }
        cur_cst = if (cur_cst.asInt() < cst_parents.len) cst_parents[cur_cst.asInt()] else .none;
    }

    // [2] Find enclosing `DefId` in `item_tree` and check `CompilerDb` local/param/const/static symbols:
    var enclosing_def: DefId = .NONE;
    for (item_tree.entries) |entry| {
        if (entry.ast_node.isNone()) continue;
        const entry_cst = db.parsed_artifacts.getPtr(file_id.asInt()).?.ast_arena.getCstOrigin(entry.ast_node);
        if (extractCstTokenSpan(cst_arena, tok_buf, entry_cst)) |e_sp| {
            if (e_sp.start_byte <= str_start_byte and str_start_byte <= e_sp.end_byte) {
                enclosing_def = entry.def_id;
            }
        }
    }

    for (db.symbol_table.symbols.items, 0..) |sym, sym_raw| {
        const unwrapped = if (sym.kind == .use_alias_sym)
            db.symbol_table.getSymbol(db.symbol_table.unwrapAliasSymbolIdx(SymbolIndex.fromInt(@intCast(sym_raw)))).*
        else
            sym;
        const is_allowed_kind = switch (unwrapped.kind) {
            .local_let_sym,
            .local_var_sym,
            .param_sym,
            .const_param_sym,
            .const_sym,
            .extern_static_sym,
            => true,
            else => false,
        };
        if (!is_allowed_kind) continue;
        if (!std.mem.eql(u8, sym.name_text, ident_name)) continue;

        if (unwrapped.kind == .local_let_sym or unwrapped.kind == .local_var_sym or unwrapped.kind == .param_sym) {
            if (sym.decl_span.file_id != file_id) continue;
            if (!enclosing_def.isNone() and sym.owner_def_id != enclosing_def and sym.def_id != enclosing_def) continue;
            if (sym.decl_span.start_byte >= str_start_byte) continue;

            // Verify that the innermost lexical CST block containing `sym.decl_span.start_byte` also encloses `str_start_byte`:
            var best_scope_cst: CstNodeIndex = .none;
            var ci: usize = 0;
            while (ci < cst_count) : (ci += 1) {
                const cid = CstNodeIndex.fromInt(@intCast(ci));
                if (!isLexicalScopeCstKind(cst_arena.getNode(cid).kind)) continue;
                if (extractCstTokenSpan(cst_arena, tok_buf, cid)) |b_sp| {
                    if (b_sp.start_byte <= sym.decl_span.start_byte and sym.decl_span.start_byte <= b_sp.end_byte) {
                        best_scope_cst = cid;
                    }
                }
            }
            if (!best_scope_cst.isNone()) {
                if (extractCstTokenSpan(cst_arena, tok_buf, best_scope_cst)) |b_sp| {
                    if (str_start_byte < b_sp.start_byte or str_start_byte > b_sp.end_byte) continue;
                }
            }
            return true;
        }

        // Module/file-visible `const_sym`, `const_param_sym`, or `extern_static_sym`:
        if (sym.decl_span.file_id == file_id or sym.flags.is_imported or sym.flags.is_builtin) {
            if (sym.decl_span.file_id == file_id and !sym.scope_id.isNone() and
                sym.scope_id.asInt() < db.symbol_table.scope_arena.countScopes())
            {
                const sc_rec = db.symbol_table.scope_arena.getScope(sym.scope_id);
                if (sc_rec.kind == .nominal_type_scope or sc_rec.kind == .trait_scope) continue;
            }
            return true;
        }
    }
    return false;
}

/// Collects Tier 3 `UR-24-01` Branch B fixes upgrading unmarked `"…{expr}…"` literals with verified semantic/AST holes.
fn collectUnmarkedFmtStringTier3Fixes(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    cst_parents: []const CstNodeIndex,
    tok_buf: *const TokenBuffer,
    item_tree: *const query_db.ItemTree,
    options: UpgradeOptions,
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    const tok_count = tok_buf.countTokens();
    if (tok_count == 0) return;

    // Build $O(1)$ map of leaf CST node per token and mark tokens inside `.attribute` / `.use_item` / `extern "ABI"`:
    const tok_leaf_cst = try allocator.alloc(CstNodeIndex, tok_count);
    defer allocator.free(tok_leaf_cst);
    @memset(tok_leaf_cst, .none);
    const is_non_expr_str_tok = try allocator.alloc(bool, tok_count);
    defer allocator.free(is_non_expr_str_tok);
    @memset(is_non_expr_str_tok, false);

    var cst_i: usize = 0;
    while (cst_i < cst_count) : (cst_i += 1) {
        const cid = CstNodeIndex.fromInt(@intCast(cst_i));
        const crec = cst_arena.getNode(cid);
        if (crec.subtree_size <= 1 and !crec.flags.is_missing_or_injected and
            !crec.token.isNone() and crec.token.asInt() < tok_count)
        {
            tok_leaf_cst[crec.token.asInt()] = cid;
        }
        if (crec.kind == .attribute or crec.kind == .use_item) {
            if (extractCstTokenSpan(cst_arena, tok_buf, cid)) |sp| {
                var ti: u32 = sp.first_tok.asInt();
                while (ti <= sp.last_tok.asInt() and ti < tok_count) : (ti += 1) {
                    is_non_expr_str_tok[ti] = true;
                }
            }
        }
    }

    var tok_i: usize = 0;
    while (tok_i < tok_count) : (tok_i += 1) {
        const rec = tok_buf.getToken(TokenIndex.fromInt(@intCast(tok_i)));
        if (rec.flags.is_synthesized or rec.kind != .string_lit or is_non_expr_str_tok[tok_i]) continue;
        if (tok_i > 0) {
            const prev_tok_id = TokenIndex.fromInt(@intCast(tok_i - 1));
            const prev_k = tok_buf.getToken(prev_tok_id).kind;
            if (prev_k == .kw_extern) continue;
            if (prev_k == .ident) {
                const prev_lex = symbol_resolver.extractTokenSlice(source, tok_buf, prev_tok_id);
                if (std.mem.eql(u8, prev_lex, "test") or std.mem.eql(u8, prev_lex, "bench")) continue;
            }
        }

        const start_b: usize = rec.byte_offset;
        const end_b: usize = @min(start_b + @as(usize, rec.byte_len), source.len);
        if (start_b >= end_b) continue;
        const raw_lit = source[start_b..end_b];
        const info = lexer.extractStringBodyInfo(.string_lit, raw_lit);
        if (info.is_raw or info.is_bytes or info.is_fmt or info.is_retired_triple) continue;

        const close_quote_pos = raw_lit.len -| (1 + @as(usize, info.hash_count));
        const open_body_pos = @as(usize, info.prefix_len) + @as(usize, info.hash_count) + 1;
        if (open_body_pos >= close_quote_pos) continue;
        const body = raw_lit[open_body_pos..close_quote_pos];
        if (std.mem.indexOfScalar(u8, body, '{') == null) continue;

        // Scan `body` with exact backslash parity; reject if any `{{`, `}}`, `\{`, `\}`, or unmatched brace exists:
        var holes: std.ArrayListUnmanaged(UnmarkedHoleProbe) = .empty;
        defer holes.deinit(allocator);
        var is_branch_b_candidate = true;
        var has_compound_or_spec = false;
        var pos: usize = 0;

        while (pos < body.len) {
            if (body[pos] == '\\') {
                var bs_run: usize = 0;
                while (pos + bs_run < body.len and body[pos + bs_run] == '\\') : (bs_run += 1) {}
                pos += bs_run;
                if ((bs_run % 2) == 1 and pos < body.len) {
                    if (body[pos] == '{' or body[pos] == '}') {
                        is_branch_b_candidate = false;
                        break;
                    }
                    pos += 1;
                }
                continue;
            }
            if (body[pos] == '}') {
                is_branch_b_candidate = false;
                break;
            }
            if (body[pos] == '{') {
                if (pos + 1 < body.len and body[pos + 1] == '{') {
                    is_branch_b_candidate = false;
                    break;
                }
                const hole_start = pos + 1;
                const after_close = scanHoleEndWithoutEdits(body, hole_start, body.len);
                if (after_close == 0 or after_close > body.len or body[after_close - 1] != '}') {
                    is_branch_b_candidate = false;
                    break;
                }
                const hole_end = after_close - 1;
                const split = splitUpgradeHoleParts(body[hole_start..hole_end]);
                if (split.spec_with_colon.len > 0) {
                    if (lexer.parseFormatSpec(split.spec_with_colon[1..], split.has_debug_eq)) |_| {} else |_| {
                        is_branch_b_candidate = false;
                        break;
                    }
                }
                const syntax_probe = (try probeSingleHoleExprSyntax(allocator, split.expr_slice)) orelse {
                    is_branch_b_candidate = false;
                    break;
                };
                if (split.has_debug_eq or split.spec_with_colon.len > 0 or !syntax_probe.is_bare_ident) {
                    has_compound_or_spec = true;
                }
                try holes.append(allocator, .{
                    .hole_body_start = hole_start,
                    .hole_body_end = hole_end,
                    .expr_slice = split.expr_slice,
                    .spec_with_colon = split.spec_with_colon,
                    .has_debug_eq = split.has_debug_eq,
                    .is_bare_ident = syntax_probe.is_bare_ident,
                });
                pos = after_close;
                continue;
            }
            pos += 1;
        }

        if (!is_branch_b_candidate or holes.items.len == 0) continue;

        if (!has_compound_or_spec) {
            var all_bare_resolved = true;
            for (holes.items) |hole_item| {
                const ident_str = std.mem.trim(u8, hole_item.expr_slice, " \t\r\n");
                if (!isBareIdentResolvedAtStringSite(
                    db,
                    file_id,
                    source,
                    cst_arena,
                    cst_parents,
                    tok_buf,
                    item_tree,
                    tok_leaf_cst[tok_i],
                    rec.byte_offset,
                    ident_str,
                )) {
                    all_bare_resolved = false;
                    break;
                }
            }
            if (!all_bare_resolved) continue;
        }

        // Reconstruct `f"…"` / `f#"…"#` while recursively upgrading each hole expression:
        var out_lit: std.ArrayList(u8) = .empty;
        defer out_lit.deinit(allocator);
        try out_lit.append(allocator, 'f');
        try out_lit.appendSlice(allocator, raw_lit[0..open_body_pos]);
        var prev_body_idx: usize = 0;
        for (holes.items) |hole_item| {
            try out_lit.appendSlice(allocator, body[prev_body_idx..hole_item.hole_body_start]);
            const upg_expr = try upgradeInnerHoleExprAlloc(allocator, hole_item.expr_slice, file_id, options, 1);
            defer allocator.free(upg_expr);
            try out_lit.appendSlice(allocator, upg_expr);
            if (hole_item.has_debug_eq) try out_lit.append(allocator, '=');
            try out_lit.appendSlice(allocator, hole_item.spec_with_colon);
            try out_lit.append(allocator, '}');
            prev_body_idx = hole_item.hole_body_end + 1;
        }
        try out_lit.appendSlice(allocator, body[prev_body_idx..]);
        try out_lit.appendSlice(allocator, raw_lit[close_quote_pos..]);

        try collector.appendSingleEdit(
            .syntax_canonicalization,
            rec.byte_offset,
            @intCast(end_b),
            out_lit.items,
            "UR-24-01: add explicit `f` prefix to interpolated string literal",
        );
    }
}

/// Returns `true` if `cst_id` or any CST ancestor carries `@allow(W0333)` / `@allow(redundant_private_contract)`.
fn hasAllowW0333InCstChain(
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    cst_parents: []const CstNodeIndex,
    tok_buf: *const TokenBuffer,
    cst_id: CstNodeIndex,
) bool {
    const cst_count = cst_arena.countNodes();
    var cur = cst_id;
    var steps: usize = 0;
    while (!cur.isNone() and cur.asInt() < cst_count and steps < 128) : (steps += 1) {
        const rec = cst_arena.getNode(cur);
        const sub_end = @min(@as(usize, cur.asInt()) + @max(@as(usize, rec.subtree_size), 1), cst_count);
        var child_cur: usize = cur.asInt() + 1;
        while (child_cur < sub_end) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cur));
            const child_rec = cst_arena.getNode(child_id);
            if (child_rec.kind == .attribute) {
                if (extractCstTokenSpan(cst_arena, tok_buf, child_id)) |a_sp| {
                    if (a_sp.first_tok.asInt() + 3 <= a_sp.last_tok.asInt() and
                        tok_buf.getToken(a_sp.first_tok).kind == .at and
                        std.mem.eql(
                            u8,
                            symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(a_sp.first_tok.asInt() + 1)),
                            "allow",
                        ))
                    {
                        var ti: u32 = a_sp.first_tok.asInt() + 2;
                        while (ti <= a_sp.last_tok.asInt()) : (ti += 1) {
                            const arg_lex = symbol_resolver.extractTokenSlice(source, tok_buf, TokenIndex.fromInt(ti));
                            if (DR24_ALLOW_W0333_SET.has(arg_lex)) return true;
                        }
                    }
                }
            }
            child_cur += @max(@as(usize, child_rec.subtree_size), 1);
        }
        cur = if (cur.asInt() < cst_parents.len) cst_parents[cur.asInt()] else .none;
    }
    return false;
}

/// Checks whether a CST item has unrestricted `pub` visibility (not `pub(pkg)` / `pub(super)` or private).
fn hasUnrestrictedPubModifierCst(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    item_cst: CstNodeIndex,
) bool {
    const cst_count = cst_arena.countNodes();
    if (item_cst.isNone() or item_cst.asInt() >= cst_count) return false;
    const item_rec = cst_arena.getNode(item_cst);
    const sub_end = @min(@as(usize, item_cst.asInt()) + @max(@as(usize, item_rec.subtree_size), 1), cst_count);
    var child_cur: usize = item_cst.asInt() + 1;
    while (child_cur < sub_end) {
        const child_id = CstNodeIndex.fromInt(@intCast(child_cur));
        const child_rec = cst_arena.getNode(child_id);
        if (child_rec.kind == .visibility_modifier) {
            if (extractCstTokenSpan(cst_arena, tok_buf, child_id)) |v_sp| {
                return v_sp.first_tok == v_sp.last_tok and
                    tok_buf.getToken(v_sp.first_tok).kind == .kw_pub;
            }
        }
        if (child_rec.kind != .attribute) break;
        child_cur += @max(@as(usize, child_rec.subtree_size), 1);
    }
    return false;
}

/// Collects `UR-24-05` fixes stripping redundant bare `@inline` and private `@no_alloc`/`@no_panic`/`@no_block` (`W0333`).
fn collectStripRedundantPrivateContractsFixes(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    cst_parents: []const CstNodeIndex,
    tok_buf: *const TokenBuffer,
    item_tree: *const query_db.ItemTree,
    collector: *FixCollector,
) !void {
    const cst_count = cst_arena.countNodes();
    if (cst_count == 0) return;

    var idx: usize = 0;
    while (idx < cst_count) : (idx += 1) {
        const fn_cst = CstNodeIndex.fromInt(@intCast(idx));
        const fn_rec = cst_arena.getNode(fn_cst);
        if (fn_rec.kind != .fn_item and fn_rec.kind != .impl_member) continue;
        const fn_sp = extractCstTokenSpan(cst_arena, tok_buf, fn_cst) orelse continue;
        const sub_end = @min(idx + @max(@as(usize, fn_rec.subtree_size), 1), cst_count);

        // Skip functions inside `.trait_item` or `.extern_block_item`, and detect enclosing `.impl_item` traits/generics:
        var is_excluded_parent = false;
        var is_in_generic_impl = false;
        var is_in_trait_impl = false;
        var is_in_private_mod = false;
        var anc_cst = if (idx < cst_parents.len) cst_parents[idx] else .none;
        var anc_steps: usize = 0;
        while (!anc_cst.isNone() and anc_cst.asInt() < cst_count and anc_steps < 128) : (anc_steps += 1) {
            const anc_rec = cst_arena.getNode(anc_cst);
            if (anc_rec.kind == .trait_item or anc_rec.kind == .trait_member or anc_rec.kind == .extern_block_item) {
                is_excluded_parent = true;
                break;
            }
            if (anc_rec.kind == .mod_item and !hasUnrestrictedPubModifierCst(cst_arena, tok_buf, anc_cst)) {
                is_in_private_mod = true;
            }
            if (anc_rec.kind == .impl_item) {
                const impl_end = @min(
                    @as(usize, anc_cst.asInt()) + @max(@as(usize, anc_rec.subtree_size), 1),
                    cst_count,
                );
                var ic: usize = anc_cst.asInt() + 1;
                while (ic < impl_end) {
                    const ic_id = CstNodeIndex.fromInt(@intCast(ic));
                    const ic_rec = cst_arena.getNode(ic_id);
                    if (ic_rec.kind == .type_params) is_in_generic_impl = true;
                    if (ic_rec.subtree_size <= 1 and !ic_rec.token.isNone() and
                        ic_rec.token.asInt() < tok_buf.countTokens())
                    {
                        const tk = tok_buf.getToken(ic_rec.token).kind;
                        if (tk == .kw_for) is_in_trait_impl = true;
                        if (tk == .lbrace) break;
                    }
                    ic += @max(@as(usize, ic_rec.subtree_size), 1);
                }
            }
            anc_cst = if (anc_cst.asInt() < cst_parents.len) cst_parents[anc_cst.asInt()] else .none;
        }
        if (is_excluded_parent) continue;
        if (hasAllowW0333InCstChain(source, cst_arena, cst_parents, tok_buf, fn_cst)) continue;

        // Inspect function header CST for `extern`, `fn main`, generics, `= expr;` body, and attributes:
        var is_extern_or_proto = false;
        var has_own_generics = false;
        var has_expr_body = false;
        var has_abi_boundary_attr = false;
        var has_contract_candidate = false;
        var fn_name_lex: []const u8 = "";
        var seen_fn_kw = false;

        const CandidateStripAttr = struct {
            name: []const u8,
            span: Span,
            is_bare_inline: bool,
        };
        var candidates: std.ArrayListUnmanaged(CandidateStripAttr) = .empty;
        defer candidates.deinit(allocator);

        var child_cur = idx + 1;
        while (child_cur < sub_end) {
            const child_id = CstNodeIndex.fromInt(@intCast(child_cur));
            const child_rec = cst_arena.getNode(child_id);
            if (child_rec.kind == .attribute) {
                if (extractCstTokenSpan(cst_arena, tok_buf, child_id)) |a_sp| {
                    if (a_sp.first_tok.asInt() + 1 <= a_sp.last_tok.asInt() and
                        tok_buf.getToken(a_sp.first_tok).kind == .at)
                    {
                        const a_name = symbol_resolver.extractTokenSlice(
                            source,
                            tok_buf,
                            TokenIndex.fromInt(a_sp.first_tok.asInt() + 1),
                        );
                        if (DR24_ABI_BOUNDARY_ATTR_SET.has(a_name)) {
                            has_abi_boundary_attr = true;
                        } else if (std.mem.eql(u8, a_name, "link")) {
                            has_abi_boundary_attr = true;
                        } else if (std.mem.eql(u8, a_name, "inline") and
                            a_sp.first_tok.asInt() + 1 == a_sp.last_tok.asInt())
                        {
                            try candidates.append(allocator, .{
                                .name = a_name,
                                .span = Span.init(file_id, a_sp.start_byte, a_sp.end_byte),
                                .is_bare_inline = true,
                            });
                        } else if (DR24_PRIVATE_CONTRACT_ATTR_SET.has(a_name) and
                            a_sp.first_tok.asInt() + 1 == a_sp.last_tok.asInt())
                        {
                            has_contract_candidate = true;
                            try candidates.append(allocator, .{
                                .name = a_name,
                                .span = Span.init(file_id, a_sp.start_byte, a_sp.end_byte),
                                .is_bare_inline = false,
                            });
                        }
                    }
                }
            } else if (child_rec.kind == .fn_sig) {
                const sig_end = @min(child_cur + @max(@as(usize, child_rec.subtree_size), 1), sub_end);
                var sc = child_cur + 1;
                while (sc < sig_end) {
                    const s_id = CstNodeIndex.fromInt(@intCast(sc));
                    const s_rec = cst_arena.getNode(s_id);
                    if (s_rec.kind == .type_params) has_own_generics = true;
                    if (s_rec.subtree_size <= 1 and !s_rec.token.isNone() and s_rec.token.asInt() < tok_buf.countTokens()) {
                        const sk = tok_buf.getToken(s_rec.token).kind;
                        if (sk == .kw_extern) is_extern_or_proto = true;
                        if (sk == .kw_fn) {
                            seen_fn_kw = true;
                        } else if (seen_fn_kw and fn_name_lex.len == 0 and symbol_resolver.isIdentifierToken(sk)) {
                            fn_name_lex = symbol_resolver.extractTokenSlice(source, tok_buf, s_rec.token);
                        }
                    }
                    sc += @max(@as(usize, s_rec.subtree_size), 1);
                }
            } else if (child_rec.kind == .type_params) {
                has_own_generics = true;
            } else if (child_rec.subtree_size <= 1 and !child_rec.token.isNone() and
                child_rec.token.asInt() < tok_buf.countTokens())
            {
                const lk = tok_buf.getToken(child_rec.token).kind;
                if (lk == .kw_extern) is_extern_or_proto = true;
                if (lk == .kw_fn) {
                    seen_fn_kw = true;
                } else if (seen_fn_kw and fn_name_lex.len == 0 and symbol_resolver.isIdentifierToken(lk)) {
                    fn_name_lex = symbol_resolver.extractTokenSlice(source, tok_buf, child_rec.token);
                } else if (lk == .eq) {
                    has_expr_body = true;
                } else if (lk == .semi and !has_expr_body) {
                    is_extern_or_proto = true;
                }
            }
            child_cur += @max(@as(usize, child_rec.subtree_size), 1);
        }

        if (candidates.items.len == 0 or is_extern_or_proto or has_abi_boundary_attr) continue;
        if (std.mem.eql(u8, fn_name_lex, "main")) continue;

        // Locate matching semantic `SymbolIndex` (if active under `@cfg`) in `db.symbol_table`:
        var matched_sym_idx: SymbolIndex = .none;
        for (db.symbol_table.symbols.items, 0..) |sym, sym_i| {
            if (sym.kind == .fn_sym and sym.decl_span.file_id == file_id and sym.cst_node == fn_cst) {
                matched_sym_idx = SymbolIndex.fromInt(@intCast(sym_i));
                break;
            }
        }

        const is_syntactic_pub = hasUnrestrictedPubModifierCst(cst_arena, tok_buf, fn_cst) and !is_in_private_mod;
        const is_effective_pub = if (!matched_sym_idx.isNone())
            db.symbol_table.isEffectivePubBoundary(matched_sym_idx)
        else
            is_syntactic_pub;

        if (!matched_sym_idx.isNone()) {
            const sym_rec = db.symbol_table.getSymbol(matched_sym_idx);
            if (db.symbol_table.getScopeAllowMask(sym_rec.scope_id).has_allow_redundant_contract_w0333) continue;
            if (db.symbol_table.getSymbolAllowMask(matched_sym_idx).has_allow_redundant_contract_w0333) continue;
        }

        const can_strip_bare_inline = !is_effective_pub or has_own_generics or is_in_generic_impl or has_expr_body;

        var can_strip_private_contracts = false;
        if (has_contract_candidate and !is_effective_pub and !is_in_trait_impl and !matched_sym_idx.isNone()) {
            const sym_rec = db.symbol_table.getSymbol(matched_sym_idx);
            if (!sym_rec.layout_inline_flags.is_fn_value_reified and
                !db.symbol_table.impl_method_trait.contains(matched_sym_idx.asInt()))
            {
                const check_def = if (!sym_rec.def_id.isNone()) sym_rec.def_id else sym_rec.owner_def_id;
                if (!check_def.isNone()) {
                    var has_any_fn_error = false;
                    if (db.typecheckBody(check_def)) |tc_res| {
                        if (tc_res.error_count > 0) has_any_fn_error = true;
                    } else |_| {
                        has_any_fn_error = true;
                    }
                    if (!has_any_fn_error) {
                        if (db.verifySastMir(check_def)) |sast_res| {
                            if (!sast_res.is_verified_sound or sast_res.error_count > 0) {
                                if (db.sast_diagnostics.getPtr(check_def.asInt())) |sast_sink| {
                                    for (sast_sink.diagnostics.items) |sd| {
                                        if (sd.severity == .err and
                                            sd.primary_span.start_byte <= fn_sp.end_byte and
                                            fn_sp.start_byte <= sd.primary_span.end_byte)
                                        {
                                            has_any_fn_error = true;
                                            break;
                                        }
                                    }
                                } else {
                                    has_any_fn_error = true;
                                }
                            }
                        } else |_| {
                            has_any_fn_error = true;
                        }
                    }
                    if (!has_any_fn_error) can_strip_private_contracts = true;
                }
            }
        }
        _ = item_tree;

        var min_del_start: u32 = 0;
        var strip_edits: std.ArrayList(PendingByteEdit) = .empty;
        defer strip_edits.deinit(allocator);
        for (candidates.items) |cand| {
            const should_strip = if (cand.is_bare_inline) can_strip_bare_inline else can_strip_private_contracts;
            if (!should_strip) continue;
            const rem = computeSafeAttrRemovalRange(source, file_id, tok_buf, cand.span, min_del_start);
            if (rem.end > rem.start) {
                try strip_edits.append(allocator, .{
                    .start_byte = @intCast(rem.start),
                    .end_byte = @intCast(rem.end),
                    .replacement = "",
                });
                min_del_start = @intCast(rem.end);
            }
        }
        if (strip_edits.items.len > 0) {
            try collector.appendMultiEdits(
                .lint_idiom,
                strip_edits.items,
                "UR-24-05: strip redundant `@inline` / private `@no_alloc` / `@no_panic` / `@no_block` (`W0333`)",
            );
        }
    }
}

/// Checks whether `expr_id` is a pure side-effect-free scrutinee expression (`ident`, `self`, field, index, deref).
fn isPureScrutineeAst(ast_arena: *const AstArena, expr_id: NodeIndex, depth: u32) bool {
    if (expr_id.isNone() or expr_id.asInt() >= ast_arena.countNodes() or depth > 16) return false;
    const node = ast_arena.getNode(expr_id);
    return switch (node.tag) {
        .ident_expr, .self_val => true,
        .field_access => node.lhs.tag == .node and
            isPureScrutineeAst(ast_arena, NodeIndex.fromInt(node.lhs.payload), depth + 1),
        .deref_expr => node.lhs.tag == .node and
            isPureScrutineeAst(ast_arena, NodeIndex.fromInt(node.lhs.payload), depth + 1),
        .index_expr => node.lhs.tag == .node and node.rhs.tag == .node and
            isPureScrutineeAst(ast_arena, NodeIndex.fromInt(node.lhs.payload), depth + 1) and
            isPureScrutineeAst(ast_arena, NodeIndex.fromInt(node.rhs.payload), depth + 1),
        else => false,
    };
}

/// Checks whether `expr_id` is a constant literal, enum variant, or `CONST_IDENT` usable as a `match` pattern.
fn isMatchPatternConstAst(
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    expr_id: NodeIndex,
) bool {
    if (expr_id.isNone() or expr_id.asInt() >= ast_arena.countNodes()) return false;
    const node = ast_arena.getNode(expr_id);
    return switch (node.tag) {
        .int_lit, .char_lit, .byte_lit, .string_lit, .byte_string_lit, .contextual_variant, .path_expr => true,
        .unary_expr => !node.main_token.isNone() and
            tok_buf.getToken(node.main_token).kind == .minus and
            node.lhs.tag == .node and
            ast_arena.getNode(NodeIndex.fromInt(node.lhs.payload)).tag == .int_lit,
        .ident_expr => !node.main_token.isNone() and
            tok_buf.getToken(node.main_token).kind == .const_ident,
        .field_access => !node.main_token.isNone() and
            node.rhs.tag == .token and
            tok_buf.getToken(TokenIndex.fromInt(node.rhs.payload)).kind == .type_ident,
        else => false,
    };
}

/// Extracts the single pure scrutinee slice tested by `cond_id` (`==` / `or` / guard-free `is`), or `null`.
fn extractSingleMatchScrutineeSlice(
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    cond_id: NodeIndex,
    depth: u32,
) ?struct { scrut_node: NodeIndex, scrut_slice: []const u8 } {
    if (cond_id.isNone() or cond_id.asInt() >= ast_arena.countNodes() or depth > 16) return null;
    const node = ast_arena.getNode(cond_id);
    if (node.tag == .is_expr and !node.main_token.isNone() and
        tok_buf.getToken(node.main_token).kind == .kw_is and node.lhs.tag == .node)
    {
        const scrut = NodeIndex.fromInt(node.lhs.payload);
        if (!isPureScrutineeAst(ast_arena, scrut, 0)) return null;
        const cst_id = ast_arena.getCstOrigin(scrut);
        const sp = extractCstTokenSpan(cst_arena, tok_buf, cst_id) orelse return null;
        return .{
            .scrut_node = scrut,
            .scrut_slice = std.mem.trim(u8, source[sp.start_byte..sp.end_byte], " \t\r\n"),
        };
    }
    if (node.tag == .binary_expr and !node.main_token.isNone() and
        node.lhs.tag == .node and node.rhs.tag == .node)
    {
        const op_kind = tok_buf.getToken(node.main_token).kind;
        const lhs_id = NodeIndex.fromInt(node.lhs.payload);
        const rhs_id = NodeIndex.fromInt(node.rhs.payload);
        if (op_kind == .kw_or) {
            const left_res = extractSingleMatchScrutineeSlice(source, cst_arena, ast_arena, tok_buf, lhs_id, depth + 1) orelse return null;
            const right_res = extractSingleMatchScrutineeSlice(source, cst_arena, ast_arena, tok_buf, rhs_id, depth + 1) orelse return null;
            if (!std.mem.eql(u8, left_res.scrut_slice, right_res.scrut_slice)) return null;
            return left_res;
        }
        if (op_kind == .eqeq) {
            if (isPureScrutineeAst(ast_arena, lhs_id, 0) and isMatchPatternConstAst(ast_arena, tok_buf, rhs_id)) {
                const sp = extractCstTokenSpan(cst_arena, tok_buf, ast_arena.getCstOrigin(lhs_id)) orelse return null;
                return .{
                    .scrut_node = lhs_id,
                    .scrut_slice = std.mem.trim(u8, source[sp.start_byte..sp.end_byte], " \t\r\n"),
                };
            }
            if (isPureScrutineeAst(ast_arena, rhs_id, 0) and isMatchPatternConstAst(ast_arena, tok_buf, lhs_id)) {
                const sp = extractCstTokenSpan(cst_arena, tok_buf, ast_arena.getCstOrigin(rhs_id)) orelse return null;
                return .{
                    .scrut_node = rhs_id,
                    .scrut_slice = std.mem.trim(u8, source[sp.start_byte..sp.end_byte], " \t\r\n"),
                };
            }
        }
    }
    return null;
}

/// Returns `true` when `cond_nodes` (`len >= 3`) is a Priority-1 single-scrutinee `W0202` `match` candidate.
fn isPriority1MatchChainCandidate(
    db: *CompilerDb,
    file_id: FileId,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
    tok_buf: *const TokenBuffer,
    item_tree: *const query_db.ItemTree,
    cond_nodes: []const NodeIndex,
) !bool {
    if (cond_nodes.len < 3) return false;
    const first = extractSingleMatchScrutineeSlice(source, cst_arena, ast_arena, tok_buf, cond_nodes[0], 0) orelse return false;
    for (cond_nodes[1..]) |cond_id| {
        const next_m = extractSingleMatchScrutineeSlice(source, cst_arena, ast_arena, tok_buf, cond_id, 0) orelse return false;
        if (!std.mem.eql(u8, first.scrut_slice, next_m.scrut_slice)) return false;
    }
    const scrut_ty = try lookupSemanticNodeType(db, file_id, item_tree, first.scrut_node);
    if (scrut_ty.isError() or scrut_ty == .bool_ty or
        scrut_ty == .f32_ty or scrut_ty == .f64_ty)
    {
        return false;
    }
    return true;
}

/// Returns `true` if `arm_tag` is a multi-branch/control-flow construct excluded from `if … => …` arms (`UR-24-06`).
inline fn isDisallowedInlineIfArmTag(arm_tag: syntax_arenas.AstTag) bool {
    return switch (arm_tag) {
        .if_expr,
        .match_expr,
        .block,
        .with_expr,
        .for_stmt,
        .while_stmt,
        .loop_expr,
        .return_stmt,
        .break_stmt,
        .continue_stmt,
        => true,
        else => false,
    };
}

/// Returns `true` if `subtree_idx` contains a braced expression or pattern requiring outer `(` … `)` in headers.
fn hasStructLitOrBlockInCstSubtree(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) bool {
    if (subtree_idx.isNone() or subtree_idx.asInt() >= cst_arena.countNodes()) return false;
    const root_node = cst_arena.getNode(subtree_idx);
    const end_idx = @min(
        @as(usize, subtree_idx.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = tok_buf.countTokens();
    var cursor: usize = subtree_idx.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .struct_lit_expr or
            node.kind == .view_block_expr or
            node.kind == .with_expr or
            node.kind == .struct_pat or
            node.kind == .block)
        {
            return true;
        }
        if (node.kind == .contextual_variant_expr or
            node.kind == .variant_pat or
            node.kind == .path_pat)
        {
            const sub_end = @min(end_idx, cursor + @max(@as(usize, node.subtree_size), 1));
            var sub_cursor: usize = cursor + 1;
            while (sub_cursor < sub_end) : (sub_cursor += 1) {
                const sub_node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_cursor)));
                if (sub_node.kind == .field_init or
                    sub_node.kind == .field_pat or
                    sub_node.kind == .struct_pat_start)
                {
                    return true;
                }
                if (sub_node.subtree_size <= 1 and !sub_node.token.isNone() and sub_node.token.asInt() < tok_count and
                    tok_buf.getToken(sub_node.token).kind == .lbrace)
                {
                    return true;
                }
            }
        }
    }
    return false;
}

/// Returns `true` when `target_cst` sits inside a control-flow header (`allow_struct_lit == false`) without outer `(...)`.
fn isCstInNoStructLitHeader(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    cst_parents: []const CstNodeIndex,
    target_cst: CstNodeIndex,
    target_start_byte: u32,
) bool {
    const cst_count = cst_arena.countNodes();
    const tok_count = tok_buf.countTokens();
    var cur_cst = target_cst;
    var depth: usize = 0;
    while (!cur_cst.isNone() and cur_cst.asInt() < cst_parents.len and depth < 256) : (depth += 1) {
        const parent_cst = cst_parents[cur_cst.asInt()];
        if (parent_cst.isNone() or parent_cst.asInt() >= cst_count) return false;
        const parent_rec = cst_arena.getNode(parent_cst);
        switch (parent_rec.kind) {
            .if_cond, .while_header, .for_header, .context_binding => return true,
            .tuple_or_paren_expr,
            .block,
            .array_expr,
            .call_arg,
            .struct_lit_expr,
            .field_init,
            .view_block_expr,
            .match_arm,
            .local_decl_stmt,
            .return_stmt,
            .assign_stmt,
            .expr_stmt,
            .const_item,
            .fn_item,
            .fn_expr_body,
            .test_item,
            .bench_item,
            .subscript_arm,
            .file_end,
            .mod_item,
            => return false,
            .match_expr, .while_stmt, .for_stmt, .with_expr => {
                const parent_start: usize = parent_cst.asInt();
                const parent_end = @min(parent_start + @max(@as(usize, parent_rec.subtree_size), 1), cst_count);
                var child_idx = parent_start + 1;
                while (child_idx < parent_end) {
                    const child_cst = CstNodeIndex.fromInt(@intCast(child_idx));
                    const child_rec = cst_arena.getNode(child_cst);
                    if (parent_rec.kind == .match_expr and child_rec.subtree_size <= 1 and
                        !child_rec.token.isNone() and child_rec.token.asInt() < tok_count and
                        tok_buf.getToken(child_rec.token).kind == .lbrace)
                    {
                        return target_start_byte < tok_buf.getToken(child_rec.token).byte_offset;
                    }
                    if (parent_rec.kind != .match_expr and child_rec.kind == .block) {
                        if (extractCstTokenSpan(cst_arena, tok_buf, child_cst)) |blk_sp| {
                            return target_start_byte < blk_sp.start_byte;
                        }
                        return false;
                    }
                    child_idx += @max(@as(usize, child_rec.subtree_size), 1);
                }
                return true;
            },
            .index_expr => {
                const parent_start: usize = parent_cst.asInt();
                const parent_end = @min(parent_start + @max(@as(usize, parent_rec.subtree_size), 1), cst_count);
                var child_idx = parent_start + 1;
                while (child_idx < parent_end) {
                    const child_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_idx)));
                    if (child_rec.subtree_size <= 1 and !child_rec.token.isNone() and
                        child_rec.token.asInt() < tok_count and
                        tok_buf.getToken(child_rec.token).kind == .lbracket)
                    {
                        if (target_start_byte > tok_buf.getToken(child_rec.token).byte_offset) return false;
                        break;
                    }
                    child_idx += @max(@as(usize, child_rec.subtree_size), 1);
                }
            },
            else => {},
        }
        cur_cst = parent_cst;
    }
    return false;
}

/// Climbs from `inner_cst` up through any enclosing single-expression `( … )` `.tuple_or_paren_expr` wrappers.
fn climbEnclosingGroupingParens(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    cst_parents: []const CstNodeIndex,
    inner_cst: CstNodeIndex,
) CstNodeIndex {
    if (inner_cst.isNone() or inner_cst.asInt() >= cst_arena.countNodes()) return inner_cst;
    const tok_count = tok_buf.countTokens();
    var cur_cst = inner_cst;
    var depth: usize = 0;
    while (!cur_cst.isNone() and cur_cst.asInt() < cst_parents.len and depth < 64) : (depth += 1) {
        const parent_cst = cst_parents[cur_cst.asInt()];
        if (parent_cst.isNone() or parent_cst.asInt() >= cst_arena.countNodes()) break;
        if (cst_arena.getNode(parent_cst).kind != .tuple_or_paren_expr) break;
        const cur_sp = extractCstTokenSpan(cst_arena, tok_buf, cur_cst) orelse break;
        const par_sp = extractCstTokenSpan(cst_arena, tok_buf, parent_cst) orelse break;
        if (par_sp.first_tok.asInt() + 1 != cur_sp.first_tok.asInt() or
            cur_sp.last_tok.asInt() + 1 != par_sp.last_tok.asInt() or
            par_sp.last_tok.asInt() >= tok_count)
        {
            break;
        }
        const open_tok = tok_buf.getToken(par_sp.first_tok);
        const close_tok = tok_buf.getToken(par_sp.last_tok);
        if (open_tok.kind != .lparen or close_tok.kind != .rparen or
            open_tok.flags.is_synthesized or close_tok.flags.is_synthesized)
        {
            break;
        }
        cur_cst = parent_cst;
    }
    return cur_cst;
}

/// Returns `true` when `cst_idx` is a fat-arrow `if cond => a else b` `.if_expr` node.
fn isFatArrowIfCstInArena(
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    cst_idx: CstNodeIndex,
) bool {
    if (cst_idx.isNone() or cst_idx.asInt() >= cst_arena.countNodes()) return false;
    const node = cst_arena.getNode(cst_idx);
    if (node.kind != .if_expr) return false;
    const end_idx = @min(
        @as(usize, cst_idx.asInt()) + @max(@as(usize, node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = tok_buf.countTokens();
    var child_idx: usize = cst_idx.asInt() + 1;
    while (child_idx < end_idx) {
        const child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_idx)));
        if (child.subtree_size <= 1 and !child.token.isNone() and child.token.asInt() < tok_count and
            tok_buf.getToken(child.token).kind == .fat_arrow)
        {
            return true;
        }
        child_idx += @max(@as(usize, child.subtree_size), 1);
    }
    return false;
}

/// Unwraps redundant outer `( … )` around an `if` header condition while preserving required grouping parens.
fn unwrapRedundantHeaderParensInArena(
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    tok_buf: *const TokenBuffer,
    outer_cst: CstNodeIndex,
    inner_base_cst: CstNodeIndex,
) CstNodeIndex {
    if (outer_cst == inner_base_cst) return outer_cst;
    if (hasStructLitOrBlockInCstSubtree(cst_arena, tok_buf, inner_base_cst) or
        isFatArrowIfCstInArena(cst_arena, tok_buf, inner_base_cst))
    {
        return outer_cst;
    }
    if (extractCstTokenSpan(cst_arena, tok_buf, outer_cst)) |out_sp| {
        if (hasCommentsInByteRange(source, tok_buf, out_sp.start_byte, out_sp.end_byte)) {
            return outer_cst;
        }
        var tok_i = out_sp.first_tok.asInt();
        while (tok_i <= out_sp.last_tok.asInt() and tok_i < tok_buf.countTokens()) : (tok_i += 1) {
            if (tok_buf.getToken(TokenIndex.fromInt(tok_i)).kind == .colon_eq) {
                return outer_cst;
            }
        }
    }
    return inner_base_cst;
}

/// Collects `UR-24-06` fixes rewriting `1 <= K <= 4` pure value `if { a } else { b }` chains to `if cond => a else b`.
fn collectInlineFatArrowIfExprFixes(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    source: []const u8,
    cst_arena: *const LosslessCstArena,
    cst_parents: []const CstNodeIndex,
    ast_arena: *const AstArena,
    ast_parents: []const NodeIndex,
    extra_ends: []const u32,
    tok_buf: *const TokenBuffer,
    item_tree: *const query_db.ItemTree,
    collector: *FixCollector,
) !void {
    const ast_count = ast_arena.countNodes();
    const cst_count = cst_arena.countNodes();

    var node_i: usize = 0;
    while (node_i < ast_count) : (node_i += 1) {
        const root_if = NodeIndex.fromInt(@intCast(node_i));
        const root_node = ast_arena.getNode(root_if);
        if (root_node.tag != .if_expr) continue;

        const parent_ast = if (node_i < ast_parents.len) ast_parents[node_i] else .none;
        if (!parent_ast.isNone() and parent_ast.asInt() < ast_count) {
            const parent_rec = ast_arena.getNode(parent_ast);
            if (parent_rec.tag == .if_expr) {
                // Skip `else if` tail links; only inspect outermost `if` roots:
                if (parent_rec.rhs.tag == .extra) {
                    const p_extra = ast_arena.getExtraSlice(ExtraIndex.fromInt(parent_rec.rhs.payload), 2);
                    if (p_extra.len == 2 and p_extra[1] == node_i) continue;
                }
            }
            // Skip statement-position `if` inside `.block` (only value tail expression `block.rhs` produces a value):
            if (parent_rec.tag == .block) {
                if (!(parent_rec.rhs.tag == .node and parent_rec.rhs.payload == node_i)) continue;
            }
        }

        const if_cst = ast_arena.getCstOrigin(root_if);
        if (if_cst.isNone() or if_cst.asInt() >= cst_count) continue;
        if (cst_arena.getNode(if_cst).flags.has_error) continue;
        const if_sp = extractCstTokenSpan(cst_arena, tok_buf, if_cst) orelse continue;
        if (hasCommentsInByteRange(source, tok_buf, if_sp.start_byte, if_sp.end_byte)) continue;

        const if_ty = try lookupSemanticNodeType(db, file_id, item_tree, root_if);
        if (if_ty.isError() or if_ty == .unit_ty or if_ty == .never_ty) continue;

        // Walk `if` / `else if` / `else` chain (`1 <= K <= 4`), requiring braced `{ expr }` blocks throughout:
        var cond_nodes: [4]NodeIndex = undefined;
        var arm_exprs: [5]NodeIndex = undefined;
        var cond_count: usize = 0;
        var cur_if = root_if;
        var is_valid_chain = true;

        while (true) {
            if (cond_count >= 4 or cur_if.isNone() or cur_if.asInt() >= ast_count) {
                is_valid_chain = false;
                break;
            }
            const cur_node = ast_arena.getNode(cur_if);
            if (cur_node.tag != .if_expr or cur_node.lhs.tag != .node or cur_node.rhs.tag != .extra) {
                is_valid_chain = false;
                break;
            }
            const branches = ast_arena.getExtraSlice(ExtraIndex.fromInt(cur_node.rhs.payload), 2);
            if (branches.len != 2) {
                is_valid_chain = false;
                break;
            }
            const cond_id = NodeIndex.fromInt(cur_node.lhs.payload);
            const then_blk_id = NodeIndex.fromInt(branches[0]);
            const else_id = NodeIndex.fromInt(branches[1]);
            if (then_blk_id.isNone() or then_blk_id.asInt() >= ast_count or
                else_id.isNone() or else_id.asInt() >= ast_count)
            {
                is_valid_chain = false;
                break;
            }
            const then_blk = ast_arena.getNode(then_blk_id);
            if (then_blk.tag != .block or then_blk.rhs.tag != .node) {
                is_valid_chain = false;
                break;
            }
            if (then_blk.lhs.tag == .extra and
                then_blk_id.asInt() < extra_ends.len and
                then_blk.lhs.payload < extra_ends[then_blk_id.asInt()])
            {
                is_valid_chain = false;
                break;
            }
            const then_tail = NodeIndex.fromInt(then_blk.rhs.payload);
            if (then_tail.isNone() or isDisallowedInlineIfArmTag(ast_arena.getNode(then_tail).tag)) {
                is_valid_chain = false;
                break;
            }

            cond_nodes[cond_count] = cond_id;
            arm_exprs[cond_count] = then_tail;
            cond_count += 1;

            const else_node = ast_arena.getNode(else_id);
            if (else_node.tag == .if_expr) {
                cur_if = else_id;
                continue;
            }
            if (else_node.tag != .block or else_node.rhs.tag != .node) {
                is_valid_chain = false;
                break;
            }
            if (else_node.lhs.tag == .extra and
                else_id.asInt() < extra_ends.len and
                else_node.lhs.payload < extra_ends[else_id.asInt()])
            {
                is_valid_chain = false;
                break;
            }
            const else_tail = NodeIndex.fromInt(else_node.rhs.payload);
            if (else_tail.isNone() or isDisallowedInlineIfArmTag(ast_arena.getNode(else_tail).tag)) {
                is_valid_chain = false;
                break;
            }
            arm_exprs[cond_count] = else_tail;
            break;
        }
        if (!is_valid_chain or cond_count == 0) continue;

        // Skip redundant `if cond { true } else { false }` (`W0202` boolean-simplification domain):
        if (cond_count == 1 and
            ast_arena.getNode(arm_exprs[0]).tag == .bool_lit and
            ast_arena.getNode(arm_exprs[1]).tag == .bool_lit)
        {
            continue;
        }

        // Skip Priority-1 `>= 3`-arm single-scrutinee `match` candidates so `UR-24-06` and `W0202` never conflict:
        if (try isPriority1MatchChainCandidate(
            db,
            file_id,
            source,
            cst_arena,
            ast_arena,
            tok_buf,
            item_tree,
            cond_nodes[0..cond_count],
        )) {
            continue;
        }

        // Extract single-line condition and arm slices:
        var cond_slices: [4][]const u8 = undefined;
        var arm_slices: [5][]const u8 = undefined;
        var all_single_line = true;
        var has_brace_ambig_subexpr = false;
        for (0..cond_count) |ci| {
            const base_cond_cst = ast_arena.getCstOrigin(cond_nodes[ci]);
            const outer_cond_cst = climbEnclosingGroupingParens(cst_arena, tok_buf, cst_parents, base_cond_cst);
            const cond_cst = unwrapRedundantHeaderParensInArena(
                source,
                cst_arena,
                tok_buf,
                outer_cond_cst,
                base_cond_cst,
            );
            if (cond_cst == base_cond_cst and
                (ast_arena.getNode(cond_nodes[ci]).tag == .struct_lit or
                    hasStructLitOrBlockInCstSubtree(cst_arena, tok_buf, cond_cst)))
            {
                has_brace_ambig_subexpr = true;
            }
            const csp = extractCstTokenSpan(cst_arena, tok_buf, cond_cst) orelse {
                all_single_line = false;
                break;
            };
            const c_str = std.mem.trim(u8, source[csp.start_byte..csp.end_byte], " \t\r\n");
            if (c_str.len == 0 or std.mem.indexOfScalar(u8, c_str, '\n') != null) {
                all_single_line = false;
                break;
            }
            cond_slices[ci] = c_str;
        }
        if (!all_single_line) continue;

        for (0..cond_count + 1) |ai| {
            const base_arm_cst = ast_arena.getCstOrigin(arm_exprs[ai]);
            const arm_cst = if (ast_arena.getNode(arm_exprs[ai]).tag == .tuple_lit)
                base_arm_cst
            else
                climbEnclosingGroupingParens(cst_arena, tok_buf, cst_parents, base_arm_cst);
            if (arm_cst == base_arm_cst and
                (ast_arena.getNode(arm_exprs[ai]).tag == .struct_lit or
                    hasStructLitOrBlockInCstSubtree(cst_arena, tok_buf, arm_cst)))
            {
                has_brace_ambig_subexpr = true;
            }
            const asp = extractCstTokenSpan(cst_arena, tok_buf, arm_cst) orelse {
                all_single_line = false;
                break;
            };
            const a_str = std.mem.trim(u8, source[asp.start_byte..asp.end_byte], " \t\r\n");
            if (a_str.len == 0 or a_str[0] == '{' or std.mem.indexOfScalar(u8, a_str, '\n') != null) {
                all_single_line = false;
                break;
            }
            arm_slices[ai] = a_str;
        }
        if (!all_single_line) continue;

        const parent_cst = if (if_cst.asInt() < cst_parents.len) cst_parents[if_cst.asInt()] else CstNodeIndex.none;
        const parent_cst_kind: ?syntax_arenas.CstNodeKind = if (!parent_cst.isNone() and parent_cst.asInt() < cst_count)
            cst_arena.getNode(parent_cst).kind
        else
            null;

        // Determine if `(if …)` parentheses are needed due to operator precedence or header `{` ambiguity:
        var needs_parens = false;
        if (!parent_ast.isNone() and parent_ast.asInt() < ast_count) {
            const p_tag = ast_arena.getNode(parent_ast).tag;
            needs_parens = switch (p_tag) {
                .field_access,
                .method_call,
                .try_expr,
                .deref_expr,
                .unary_expr,
                .binary_expr,
                .pipe_expr,
                .cast_expr,
                .range_expr,
                .is_expr,
                => true,
                .call_expr, .generic_call => parent_cst_kind != .call_arg,
                .index_expr => parent_cst_kind == .index_expr and blk_before_lbracket: {
                    const p_start: usize = parent_cst.asInt();
                    const p_end = @min(
                        p_start + @max(@as(usize, cst_arena.getNode(parent_cst).subtree_size), 1),
                        cst_count,
                    );
                    var sub_i = p_start + 1;
                    while (sub_i < p_end) {
                        const sub_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_i)));
                        if (sub_rec.subtree_size <= 1 and !sub_rec.token.isNone() and
                            sub_rec.token.asInt() < tok_buf.countTokens() and
                            tok_buf.getToken(sub_rec.token).kind == .lbracket)
                        {
                            break :blk_before_lbracket if_sp.start_byte < tok_buf.getToken(sub_rec.token).byte_offset;
                        }
                        sub_i += @max(@as(usize, sub_rec.subtree_size), 1);
                    }
                    break :blk_before_lbracket true;
                },
                else => false,
            };
        }
        if (!needs_parens and if_sp.last_tok.asInt() + 1 < tok_buf.countTokens()) {
            const next_k = tok_buf.getToken(TokenIndex.fromInt(if_sp.last_tok.asInt() + 1)).kind;
            if (next_k == .dot or next_k == .question or next_k == .lbracket or next_k == .lparen or
                next_k == .pipe_gt or next_k == .kw_orelse or next_k == .kw_catch or next_k == .kw_as)
            {
                needs_parens = true;
            }
        }
        if (!needs_parens and has_brace_ambig_subexpr and
            isCstInNoStructLitHeader(cst_arena, tok_buf, cst_parents, if_cst, if_sp.start_byte))
        {
            needs_parens = true;
        }
        // Avoid double-wrapping if already inside `( … )`:
        if (needs_parens and parent_cst_kind == .tuple_or_paren_expr) {
            needs_parens = false;
        } else if (needs_parens and if_sp.first_tok.asInt() > 0 and if_sp.last_tok.asInt() + 1 < tok_buf.countTokens()) {
            if (tok_buf.getToken(TokenIndex.fromInt(if_sp.first_tok.asInt() - 1)).kind == .lparen and
                tok_buf.getToken(TokenIndex.fromInt(if_sp.last_tok.asInt() + 1)).kind == .rparen)
            {
                needs_parens = false;
            }
        }

        const is_direct_fn_expr_body = (parent_cst_kind == .fn_expr_body);
        if (!(try fmt_engine.fitsInlineFatArrowIfLineBudget(
            allocator,
            source,
            if_sp.start_byte,
            if_sp.end_byte,
            cond_slices[0..cond_count],
            arm_slices[0 .. cond_count + 1],
            needs_parens,
            is_direct_fn_expr_body,
        ))) {
            continue;
        }

        var repl_buf: std.ArrayList(u8) = .empty;
        defer repl_buf.deinit(allocator);
        if (needs_parens) try repl_buf.append(allocator, '(');
        for (0..cond_count) |ci| {
            if (ci == 0) {
                try repl_buf.appendSlice(allocator, "if ");
            } else {
                try repl_buf.appendSlice(allocator, " else if ");
            }
            try repl_buf.appendSlice(allocator, cond_slices[ci]);
            try repl_buf.appendSlice(allocator, " => ");
            try repl_buf.appendSlice(allocator, arm_slices[ci]);
        }
        try repl_buf.appendSlice(allocator, " else ");
        try repl_buf.appendSlice(allocator, arm_slices[cond_count]);
        if (needs_parens) try repl_buf.append(allocator, ')');

        try collector.appendSingleEdit(
            .lint_idiom,
            if_sp.start_byte,
            if_sp.end_byte,
            repl_buf.items,
            "UR-24-06: rewrite pure single-expression `if { a } else { b }` to `if cond => a else b` (`W0202`)",
        );
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
    const is_ur23_04 = isRuleEnabled(options.rule_mask, .ur_23_04_canonical_wildcard_discard_stmt);
    const is_ur23_05 = isRuleEnabled(options.rule_mask, .ur_23_05_foreign_scalar_type_names);
    const is_ur24_01 = isRuleEnabled(options.rule_mask, .ur_24_01_f_strings_and_multiline_dedent);
    const is_ur24_05 = isRuleEnabled(options.rule_mask, .ur_24_05_strip_redundant_private_contracts);
    const is_ur24_06 = isRuleEnabled(options.rule_mask, .ur_24_06_inline_fat_arrow_if_expr);
    const is_harvesting_general = !options.has_explicit_rule_filter;

    if (!is_ur21_04 and !is_ur21_05 and !is_ur21_06 and !is_ur21_07 and
        !is_ur22_02 and !is_ur22_06 and !is_ur23_04 and !is_ur23_05 and
        !is_ur24_01 and !is_ur24_05 and !is_ur24_06 and !is_harvesting_general)
    {
        return;
    }

    const source = try db.getSourceText(file_id);
    const parsed = try db.parseCst(file_id);
    _ = db.resolveSignatures(file_id) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {},
    };
    const item_tree = try db.extractItemTree(file_id);
    for (item_tree.entries) |entry| {
        if (!hasBodySideTablesItemKind(entry.kind)) continue;
        _ = try getDefSideTablesBestEffort(db, entry.def_id);
    }

    const tok_buf = &parsed.token_buffer;
    const cst_arena = &parsed.cst_arena;
    const ast_arena = &parsed.ast_arena;
    const ast_count = ast_arena.countNodes();

    const ast_parents = try computeAstParentMap(allocator, ast_arena);
    defer allocator.free(ast_parents);
    const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
    defer allocator.free(extra_ends);
    const cst_parents = if (is_ur23_05 or is_ur24_01 or is_ur24_05 or is_ur24_06)
        try computeCstParentMap(allocator, cst_arena)
    else
        try allocator.alloc(CstNodeIndex, 0);
    defer allocator.free(cst_parents);

    // Build $O(1)$ map of `E0424` (`member_start_byte -> is_mut_suggested`) from signature & body diagnostics:
    var e0424_mut_map: std.AutoHashMapUnmanaged(u32, bool) = .empty;
    defer e0424_mut_map.deinit(allocator);
    var ur23_05_seen: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer ur23_05_seen.deinit(allocator);

    try scanSinkForTier3(
        allocator,
        db,
        file_id,
        source,
        cst_arena,
        cst_parents,
        tok_buf,
        &parsed.diagnostics,
        is_ur22_02,
        is_ur23_05,
        is_harvesting_general,
        options.is_internal_core,
        &e0424_mut_map,
        &ur23_05_seen,
        collector,
    );
    if (db.getSignatureDiagnostics(file_id)) |sig_sink| {
        try scanSinkForTier3(
            allocator,
            db,
            file_id,
            source,
            cst_arena,
            cst_parents,
            tok_buf,
            sig_sink,
            is_ur22_02,
            is_ur23_05,
            is_harvesting_general,
            options.is_internal_core,
            &e0424_mut_map,
            &ur23_05_seen,
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
                cst_parents,
                tok_buf,
                body_sink,
                is_ur22_02,
                is_ur23_05,
                is_harvesting_general,
                options.is_internal_core,
                &e0424_mut_map,
                &ur23_05_seen,
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
                                s_tag == .array_ty or s_tag == .soa_slice_ty or s_tag == .soa_array_ty or
                                s_tag == .soa_vec_ty;
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
                            deref_tag == .soa_slice_ty or deref_tag == .soa_array_ty or
                            deref_tag == .soa_vec_ty;

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

        // [6] `UR-23-04` Tier 3 semantic refinement on `_ = $e;` (`unit` / `unit!E` / `T!E`):
        if (is_ur23_04 and node.tag == .assign_stmt and node.lhs.tag == .node and node.rhs.tag == .node and
            !node.main_token.isNone() and tok_buf.getToken(node.main_token).kind == .eq)
        {
            const lhs_node = NodeIndex.fromInt(node.lhs.payload);
            const rhs_node = NodeIndex.fromInt(node.rhs.payload);
            if (!lhs_node.isNone() and lhs_node.asInt() < ast_count and
                ast_arena.getNode(lhs_node).tag == .wildcard_pat)
            {
                if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, node_id)) |stmt_sp| {
                    if (extractAstByteSpan(cst_arena, ast_arena, tok_buf, rhs_node)) |rhs_sp| {
                        var stmt_end_b = stmt_sp.end_byte;
                        if (tok_buf.getToken(stmt_sp.last_tok).kind != .semi and
                            stmt_sp.last_tok.asInt() + 1 < tok_buf.countTokens())
                        {
                            const after_rec = tok_buf.getToken(TokenIndex.fromInt(stmt_sp.last_tok.asInt() + 1));
                            if (after_rec.kind == .semi and !after_rec.flags.is_synthesized) {
                                stmt_end_b = after_rec.byte_offset +| after_rec.byte_len;
                            }
                        }

                        if (!hasCommentsInByteRange(source, tok_buf, stmt_sp.start_byte, rhs_sp.start_byte) and
                            !hasCommentsInByteRange(source, tok_buf, rhs_sp.end_byte, stmt_end_b))
                        {
                            const raw_rhs_ty = try lookupSemanticNodeType(db, file_id, item_tree, rhs_node);
                            const rhs_ty = db.type_pool.unwrapUnderlyingType(raw_rhs_ty);
                            const rhs_raw = std.mem.trim(u8, source[rhs_sp.start_byte..rhs_sp.end_byte], " \t\r\n");
                            if (rhs_ty == .unit_ty) {
                                const repl = try std.fmt.allocPrint(allocator, "{s};", .{rhs_raw});
                                defer allocator.free(repl);
                                try collector.appendSingleEdit(
                                    .syntax_canonicalization,
                                    stmt_sp.start_byte,
                                    stmt_end_b,
                                    repl,
                                    "UR-23-04: remove pointless `_ =` discard on `unit` expression (`E0439`)",
                                );
                            } else if (!rhs_ty.isError() and db.type_pool.getTag(rhs_ty) == .result_ty) {
                                const ok_ty = db.type_pool.unwrapUnderlyingType(
                                    TypeId.fromInt(db.type_pool.getNode(rhs_ty).lhs),
                                );
                                if (ok_ty == .unit_ty) {
                                    const rhs_tag = ast_arena.getNode(rhs_node).tag;
                                    const is_needing_catch_parens = switch (rhs_tag) {
                                        .binary_expr,
                                        .pipe_expr,
                                        .range_expr,
                                        .cast_expr,
                                        .is_expr,
                                        .closure_expr,
                                        => true,
                                        else => false,
                                    };
                                    const repl = if (is_needing_catch_parens)
                                        try std.fmt.allocPrint(allocator, "({s}) catch {{}};", .{rhs_raw})
                                    else
                                        try std.fmt.allocPrint(allocator, "{s} catch {{}};", .{rhs_raw});
                                    defer allocator.free(repl);
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        stmt_sp.start_byte,
                                        stmt_end_b,
                                        repl,
                                        "UR-23-04: rewrite `_ = unit_result;` to `… catch {};` (`E0414`)",
                                    );
                                } else {
                                    const rhs_cst = ast_arena.getCstOrigin(rhs_node);
                                    const is_paren = !rhs_cst.isNone() and rhs_cst.asInt() < cst_arena.countNodes() and
                                        cst_arena.getNode(rhs_cst).kind == .tuple_or_paren_expr and
                                        ast_arena.getNode(rhs_node).tag != .tuple_lit;
                                    const repl = if (is_paren)
                                        try std.fmt.allocPrint(allocator, "_ = {s}.ok();", .{rhs_raw})
                                    else
                                        try std.fmt.allocPrint(allocator, "_ = ({s}).ok();", .{rhs_raw});
                                    defer allocator.free(repl);
                                    try collector.appendSingleEdit(
                                        .syntax_canonicalization,
                                        stmt_sp.start_byte,
                                        stmt_end_b,
                                        repl,
                                        "UR-23-04: rewrite `_ = result_expr;` to `_ = (…).ok();` (`E0414`)",
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // [7] `UR-23-04` Tier 3 typed wildcard `let _: $T = $e;` (`AutoDrop`/`@linear` -> `_typed`, `Copy` -> `_ = $e;`):
    if (is_ur23_04) {
        const cst_count = cst_arena.countNodes();
        const cst_to_ast = try syntax_arenas.computeCstToAstMap(allocator, cst_count, ast_arena);
        defer allocator.free(cst_to_ast);

        var cst_i: usize = 0;
        while (cst_i < cst_count) : (cst_i += 1) {
            const decl_cst = CstNodeIndex.fromInt(@intCast(cst_i));
            const decl_rec = cst_arena.getNode(decl_cst);
            if (decl_rec.kind != .local_decl_stmt) continue;

            const sp = extractCstTokenSpan(cst_arena, tok_buf, decl_cst) orelse continue;
            const end_node = @min(cst_i + @max(@as(usize, decl_rec.subtree_size), 1), cst_count);
            var has_let_else = false;
            var sc = cst_i + 1;
            while (sc < end_node) : (sc += 1) {
                if (cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sc))).kind == .let_else_branch) {
                    has_let_else = true;
                    break;
                }
            }
            if (has_let_else) continue;

            var intro_i: u32 = sp.first_tok.asInt();
            var attr_cur = cst_i + 1;
            while (attr_cur < end_node) {
                const sub_id = CstNodeIndex.fromInt(@intCast(attr_cur));
                const sub_r = cst_arena.getNode(sub_id);
                if (sub_r.kind == .attribute) {
                    if (extractCstTokenSpan(cst_arena, tok_buf, sub_id)) |a_sp| {
                        intro_i = @max(intro_i, a_sp.last_tok.asInt() + 1);
                    }
                    attr_cur += @max(@as(usize, sub_r.subtree_size), 1);
                    continue;
                }
                break;
            }
            if (intro_i + 3 > sp.last_tok.asInt()) continue;
            const intro_rec = tok_buf.getToken(TokenIndex.fromInt(intro_i));
            if (intro_rec.kind != .kw_let and intro_rec.kind != .kw_var) continue;

            var wild_tok_i = intro_i + 1;
            if (wild_tok_i <= sp.last_tok.asInt() and tok_buf.getToken(TokenIndex.fromInt(wild_tok_i)).kind == .kw_mut) {
                wild_tok_i += 1;
            }
            if (wild_tok_i + 2 > sp.last_tok.asInt()) continue;
            const wild_rec = tok_buf.getToken(TokenIndex.fromInt(wild_tok_i));
            const colon_rec = tok_buf.getToken(TokenIndex.fromInt(wild_tok_i + 1));
            if (wild_rec.kind != .underscore or colon_rec.kind != .colon) continue;

            var depth: u32 = 0;
            var eq_tok_opt: ?u32 = null;
            var ti = wild_tok_i + 2;
            while (ti <= sp.last_tok.asInt()) : (ti += 1) {
                const tk = tok_buf.getToken(TokenIndex.fromInt(ti)).kind;
                if (depth == 0 and tk == .eq) {
                    eq_tok_opt = ti;
                    break;
                }
                switch (tk) {
                    .lparen, .lbracket, .lbrace => depth += 1,
                    .rparen, .rbracket, .rbrace => depth -|= 1,
                    else => {},
                }
            }
            const eq_i = eq_tok_opt orelse continue;
            const eq_rec = tok_buf.getToken(TokenIndex.fromInt(eq_i));

            // Resolve semantic `TypeId` of `$T` (falling back to `.local_var_decl` or `$e` in `cst_to_ast`):
            var resolved_ty: TypeId = .err_ty;
            var sub_scan = cst_i;
            while (sub_scan < end_node and resolved_ty.isError()) : (sub_scan += 1) {
                const mapped_ast = cst_to_ast[sub_scan];
                if (mapped_ast.isNone() or mapped_ast.asInt() >= ast_count) continue;
                const sub_sp = extractCstTokenSpan(
                    cst_arena,
                    tok_buf,
                    CstNodeIndex.fromInt(@intCast(sub_scan)),
                ) orelse continue;
                if (sub_sp.start_byte >= colon_rec.byte_offset and sub_sp.end_byte <= eq_rec.byte_offset) {
                    resolved_ty = try lookupSemanticNodeType(db, file_id, item_tree, mapped_ast);
                }
            }
            if (resolved_ty.isError()) {
                const decl_ast = cst_to_ast[cst_i];
                if (!decl_ast.isNone()) {
                    resolved_ty = try lookupSemanticNodeType(db, file_id, item_tree, decl_ast);
                }
            }
            if (resolved_ty.isError()) {
                sub_scan = cst_i + 1;
                while (sub_scan < end_node and resolved_ty.isError()) : (sub_scan += 1) {
                    const mapped_ast = cst_to_ast[sub_scan];
                    if (mapped_ast.isNone() or mapped_ast.asInt() >= ast_count) continue;
                    const sub_sp = extractCstTokenSpan(
                        cst_arena,
                        tok_buf,
                        CstNodeIndex.fromInt(@intCast(sub_scan)),
                    ) orelse continue;
                    if (sub_sp.start_byte > eq_rec.byte_offset) {
                        resolved_ty = try lookupSemanticNodeType(db, file_id, item_tree, mapped_ast);
                    }
                }
            }

            if (!resolved_ty.isError()) {
                const tier = type_system.classifyOwnershipTier(&db.type_pool, &db.symbol_table, resolved_ty);
                if (tier == .auto_drop_tier or tier == .linear_tier) {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        wild_rec.byte_offset,
                        wild_rec.byte_offset +| wild_rec.byte_len,
                        "_typed",
                        "UR-23-04: preserve scope-exit `AutoDrop` guard via `_typed` binding (`E0234`)",
                    );
                } else if (!hasCommentsInByteRange(source, tok_buf, intro_rec.byte_offset, eq_rec.byte_offset)) {
                    try collector.appendSingleEdit(
                        .syntax_canonicalization,
                        intro_rec.byte_offset,
                        eq_rec.byte_offset,
                        "_ ",
                        "UR-23-04: rewrite typed `Copy` wildcard declaration to `_ = …;` (`E0234`)",
                    );
                }
            }
        }
    }

    // [8] `UR-24-01` Branch B; upgrade unmarked `"…{expr}…"` strings with verified semantic/compound holes:
    if (is_ur24_01) {
        try collectUnmarkedFmtStringTier3Fixes(
            allocator,
            db,
            file_id,
            source,
            cst_arena,
            cst_parents,
            tok_buf,
            item_tree,
            options,
            collector,
        );
    }

    // [9] `UR-24-05`; strip redundant bare `@inline` and private `@no_alloc` / `@no_panic` / `@no_block` (`W0333`):
    if (is_ur24_05) {
        try collectStripRedundantPrivateContractsFixes(
            allocator,
            db,
            file_id,
            source,
            cst_arena,
            cst_parents,
            tok_buf,
            item_tree,
            collector,
        );
    }

    // [10] `UR-24-06`; rewrite `1 <= K <= 4` pure value `if { a } else { b }` chains to `if cond => a else b`:
    if (is_ur24_06) {
        try collectInlineFatArrowIfExprFixes(
            allocator,
            db,
            file_id,
            source,
            cst_arena,
            cst_parents,
            ast_arena,
            ast_parents,
            extra_ends,
            tok_buf,
            item_tree,
            collector,
        );
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

    const was_already_loaded = db.source_inputs.contains(parent_fid.asInt());
    if (!was_already_loaded) {
        _ = source_map.getLineIndex(parent_fid) catch {};
        const disk_src = source_map.getFileSource(parent_fid) orelse "";
        _ = try db.setInput(parent_fid, disk_src, durability);
        try db.setFilePath(parent_fid, parent_path);
        if (pkg_id != .root) {
            try db.setFilePackageId(parent_fid, pkg_id);
        }
    }
    const parent_src = try db.getSourceText(parent_fid);
    if (!has_core_mention_out.* and
        (std.mem.indexOf(u8, parent_src, "cx") != null or
            std.mem.indexOf(u8, parent_src, "core") != null or
            std.mem.indexOf(u8, parent_src, "std") != null))
    {
        has_core_mention_out.* = true;
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

/// Registers `core/root.cx` and optional `stdlib/cx/mod.cx` on `db` as `"core"` and `"cx"` when present on disk.
fn registerCoreStdlibInDb(
    allocator: std.mem.Allocator,
    io: std.Io,
    source_map: *vfs_sourcemap.VfsSourceMap,
    db: *CompilerDb,
    visited_fids: *std.AutoHashMapUnmanaged(u32, void),
) !void {
    var prefix_opt: ?[]u8 = null;
    defer if (prefix_opt) |owned_p| allocator.free(owned_p);
    var core_path_opt: ?[]u8 = null;
    defer if (core_path_opt) |owned_c| allocator.free(owned_c);

    var core_fid: FileId = .none;
    if (source_map.resolveOrCreatePath(io, "core/root.cx", .std_core)) |fid| {
        prefix_opt = try allocator.dupe(u8, "");
        core_path_opt = try allocator.dupe(u8, "core/root.cx");
        core_fid = fid;
    } else |_| {}

    if (core_fid.isNone()) {
        if (std.process.executableDirPathAlloc(io, allocator)) |exe_dir| {
            defer allocator.free(exe_dir);
            const rel_parents = [_][]const u8{ "..", "../..", "../../.." };
            for (rel_parents) |rel_up| {
                const cand_prefix = try std.fmt.allocPrint(allocator, "{s}/{s}/", .{ exe_dir, rel_up });
                const cand_core = try std.fmt.allocPrint(allocator, "{s}core/root.cx", .{cand_prefix});
                if (source_map.resolveOrCreatePath(io, cand_core, .std_core)) |fid| {
                    prefix_opt = cand_prefix;
                    core_path_opt = cand_core;
                    core_fid = fid;
                    break;
                } else |_| {
                    allocator.free(cand_core);
                    allocator.free(cand_prefix);
                }
            }
        } else |_| {}
    }

    if (core_fid.isNone()) return;
    const active_prefix = prefix_opt.?;
    const core_root_path = core_path_opt.?;

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

    const cx_mod_path = try std.fmt.allocPrint(allocator, "{s}stdlib/cx/mod.cx", .{active_prefix});
    defer allocator.free(cx_mod_path);
    if (source_map.resolveOrCreatePath(io, cx_mod_path, .std_core)) |cx_fid| {
        var has_dummy_cx_mention = true;
        try discoverExternalSubmodulesInDb(
            allocator,
            io,
            source_map,
            db,
            cx_fid,
            cx_mod_path,
            .high,
            .std_core,
            visited_fids,
            &has_dummy_cx_mention,
            0,
        );
        try db.registerCxStdlibPreludeRoot(cx_fid);
    } else |_| {
        try db.registerRootModule("cx", core_fid);
    }
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
pub inline fn toRuleBit(rule_id: UpgradeRuleId) u32 {
    return @as(u32, 1) << @intCast(rule_id.asInt());
}

/// Returns `true` if `rule_id` is enabled in `rule_mask`.
pub inline fn isRuleEnabled(rule_mask: u32, rule_id: UpgradeRuleId) bool {
    return (rule_mask & toRuleBit(rule_id)) != 0;
}

/// Parses a comma-separated `--rule=UR-21-00,UR-23-06` specification into a `rule_mask` (`null` on unknown rule).
pub fn parseRuleFilterMask(raw_csv: []const u8) ?u32 {
    const trimmed = std.mem.trim(u8, raw_csv, " \t");
    if (trimmed.len == 0) return null;
    var mask: u32 = 0;
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

/// Renders the monochrome Unicode box-drawing table of all 22 canonical `UPGRADE_RULE_CATALOG` rules (`--list`).
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

        // Pre-warm signatures and body side-tables across all workspace files so cross-file `is_fn_value_reified`
        // flags (`UR-24-05` / `W0333`) are populated before per-file Tier 3 stripping runs:
        if (isRuleEnabled(options.rule_mask, .ur_24_05_strip_redundant_private_contracts) and file_ids.len > 1) {
            for (file_ids, 0..) |fid, i| {
                if (states[i].is_generated) continue;
                _ = try db.parseCst(fid);
                _ = db.resolveSignatures(fid) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => {},
                };
            }
            for (file_ids, 0..) |fid, i| {
                if (states[i].is_generated) continue;
                for ((try db.extractItemTree(fid)).entries) |entry| {
                    if (!hasBodySideTablesItemKind(entry.kind)) continue;
                    _ = try getDefSideTablesBestEffort(db, entry.def_id);
                }
            }
        }

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
    const is_running_full_fmt = !options.skip_post_format and
        (!options.has_explicit_rule_filter or options.rule_mask == ALL_UPGRADE_RULES_MASK);
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
    var pending_list: std.ArrayListUnmanaged(PendingUpgradeItem) = .empty;
    defer pending_list.deinit(allocator);
    var upgraded_cx_count: usize = 0;
    var upgraded_manifest_count: usize = 0;

    // [1] Load `.cx` workspace/file targets, bind `mod <name>;` submodules, stdlib `cx`, and offline dependencies:
    if (cx_paths.len > 0) {
        const cx_results = blk_upgrade_cx: {
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

            var loaded_fids: std.ArrayListUnmanaged(FileId) = .empty;
            defer loaded_fids.deinit(allocator);
            var has_core_mention = false;
            for (cx_paths) |cx_path| {
                const raw_bytes = try std.Io.Dir.cwd().readFileAlloc(
                    io,
                    cx_path,
                    allocator,
                    .limited(64 * 1024 * 1024),
                );
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
            }

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

            break :blk_upgrade_cx try upgradeWorkspaceFilesInDb(allocator, &db, loaded_fids.items, ws_options);
        };
        defer {
            for (cx_results) |*res| res.deinit(allocator);
            allocator.free(cx_results);
        }

        // `source_map` and `db` are now deinitialized so Windows `SEC_COMMIT` `mmap` handles never block writes:
        for (cx_results, cx_paths) |res, path_str| {
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
            const toml_fid = FileId.fromInt(1);
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

test "test_render_upgrade_rule_list_and_all_explanations_zero_drift" {
    var list_buf: [32768]u8 = undefined;
    var list_writer = std.Io.Writer.fixed(&list_buf);
    try renderUpgradeRuleList(std.testing.allocator, &list_writer, StyleConfig.MONOCHROME);
    const list_text = list_writer.buffered();

    try std.testing.expect(!style.hasBannedEmoji(list_text));
    try std.testing.expect(std.mem.indexOf(u8, list_text, Glyphs.TOP_LEFT) != null);
    try std.testing.expect(std.mem.indexOf(u8, list_text, Glyphs.BOTTOM_RIGHT) != null);
    try std.testing.expect(
        std.mem.endsWith(u8, list_text, "✓ 29 canonical Zero-Legacy upgrade rules registered\n"),
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

    // `UR-22-04` & `UR-24-03` (`enum`, `bit_field` member preservation, `@repr(align: 16)`, `,` fields, omit `-> unit`):
    try std.testing.expect(std.mem.indexOf(u8, out, "pub enum Mode: u8 {") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "bit_field RegFlags: u8 {") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "ready: bool | 1,") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "mode: u8 | 7,") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "@repr(align: 16)") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "@no_alloc") != null);

    // `UR-22-00`, `UR-22-01`, `UR-22-02`, `UR-22-03`, `UR-21-01`, `UR-21-03`, `UR-24-01`:
    try std.testing.expect(std.mem.indexOf(u8, out, "[T: Number]") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "item: &T") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "count: &mut i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "done: &out bool") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "opt_ref: (&u8)?") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "nested_res: (u32!i32)!i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "var acc = count;") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "f\"{{ok}} and \\\\{acc}\"") != null);
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
        \\    _ = rw_p;
        \\    _ = ro_p;
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
        \\        _ = 1;
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
        \\    _ = arr_opt;
        \\    _ = fn_opt;
        \\    _ = fn_res;
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
        \\    let cmt_keep = legacy_add(
        \\        // preserve_arg_cmt
        \\        num,
        \\        2,
        \\    );
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
    try std.testing.expect(std.mem.indexOf(u8, upgraded, "// preserve_arg_cmt") != null);
    try std.testing.expect(std.mem.indexOf(u8, upgraded, "legacy_add(") != null);
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

    // [3] Block-comment hoisting (`UR-24-00`) & CST/AST `//` comment guards prevent silent comment deletion:
    const commented_src =
        \\use /* c_use */ cx.ffi.c_void;
        \\
        \\bit_field Flags(
        \\    // c_bf
        \\    u8
        \\) {
        \\    ready: bool | 1,
        \\}
        \\
        \\pub fn keep_comments(
        \\    ref /* c_param */ arg: i32,
        \\    opt: Option[
        \\        // c_opt
        \\        i32
        \\    ],
        \\    slice_in: &[u8],
        \\    scratch: &mut i32,
        \\) -> usize {
        \\    if
        \\        // c_if
        \\        let .Some(val) = opt
        \\    {
        \\        _ = val;
        \\    }
        \\    while
        \\        // c_while
        \\        let .Some(w_val) = opt
        \\    {
        \\        _ = w_val;
        \\        break;
        \\    }
        \\    cx.mem.with_arena(
        \\        // c_arena
        \\        scratch,
        \\        || {
        \\            _ = arg;
        \\        },
        \\    );
        \\    let sub = slice_in[0
        \\        // c_rng
        \\        .. slice_in.len() - 1];
        \\    return sub.len();
        \\}
    ++ "\n";
    var cmt_res = try upgradeSource(std.testing.allocator, commented_src, FileId.fromInt(48), .{});
    defer cmt_res.deinit(std.testing.allocator);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_use") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_bf") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_param") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_opt") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_if") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_while") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_arena") != null);
    try std.testing.expect(std.mem.indexOf(u8, cmt_res.upgraded_source, "// c_rng") != null);
}

test "test_dr23_ur23_00_through_ur23_06_multi_stage_synergy" {
    const dr23_legacy_cx =
        \\/**
        \\ * Ring Slab Header (`ring_slab`).
        \\ */
        \\
        \\pub mod helpers {
        \\    //! Inline module doc hoisted to outer `/|`.
        \\    /// Detached helper doc.
        \\
        \\    pub fn ping() {}
        \\}
        \\
        \\pub struct IoErr {}
        \\
        \\pub struct Guard {
        \\    pub fd: i32,
        \\}
        \\
        \\pub impl Drop for Guard {
        \\    pub fn drop(&mut self) {}
        \\}
        \\
        \\pub struct Counter[T: Number] {
        \\    pub val: T,
        \\
        \\    /// Reads current value.
        \\    pub fn get(&self) -> T {
        \\        return self.val;
        \\    }
        \\}
        \\
        \\pub fn flush_io() -> Void!IoErr {
        \\    return .Ok({});
        \\}
        \\
        \\pub fn fetch_code() -> UInt32!IoErr {
        \\    return .Ok(7_u32);
        \\}
        \\
        \\pub fn touch_unit() {}
        \\
        \\pub fn run_all(lhs U32, rhs UInt32, active Bool, raw *Void, pair: (u32, u32)) -> u32 {
        \\    //! Misplaced inner comment downgraded to `//`.
        \\    let _: Guard = Guard { fd: 1 };
        \\    let _: u32 = lhs;
        \\    let _ = touch_unit();
        \\    let _ = flush_io();
        \\    let _ = fetch_code();
        \\    (_, _) = pair;
        \\    _ = raw;
        \\    if active {
        \\        return lhs;
        \\    } elif rhs > 0 {
        \\        return rhs;
        \\    } else {
        \\        return 0;
        \\    }
        \\}
    ++ "\n";

    var res = try upgradeSource(std.testing.allocator, dr23_legacy_cx, FileId.fromInt(60), .{});
    defer res.deinit(std.testing.allocator);
    try std.testing.expect(res.is_changed);
    try std.testing.expect(!res.is_rolled_back);

    const out = res.upgraded_source;
    // `UR-23-00`, `UR-23-01`, & `UR-24-00`:
    try std.testing.expect(std.mem.startsWith(u8, out, "/# Ring Slab Header (`ring_slab`).\n\n"));
    try std.testing.expect(std.mem.indexOf(u8, out, "/| Inline module doc hoisted to outer `/|`.\npub mod helpers {") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "/| Detached helper doc.\n    pub fn ping()") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "// Misplaced inner comment downgraded to `//`.") != null);
    // `UR-23-02`:
    try std.testing.expect(std.mem.indexOf(u8, out, "} else if rhs > 0 {") != null);
    // `UR-23-03`:
    try std.testing.expect(std.mem.indexOf(u8, out, "pub impl") == null);
    try std.testing.expect(std.mem.indexOf(u8, out, "impl Drop for Guard") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "impl[T: Number] Counter[T] {") != null);
    // `UR-23-04`:
    try std.testing.expect(std.mem.indexOf(u8, out, "let _typed: Guard = Guard { fd: 1 };") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "_ = lhs;") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "touch_unit();") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "_ = touch_unit()") == null);
    try std.testing.expect(std.mem.indexOf(u8, out, "flush_io() catch {};") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "_ = (fetch_code()).ok();") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "_ = pair;") != null);
    // `UR-23-05` & `UR-23-06`:
    try std.testing.expect(std.mem.indexOf(u8, out, "lhs: u32, rhs: u32, active: bool, raw: *opaque") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "-> unit!IoErr") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "-> u32!IoErr") != null);

    // Adversarial edge-case regression guards (`elif` identifier/call/index, qualified destructuring,
    // nested dual-`.extra` tuple patterns, bare `\r` in block docs, `@attribute` generic & doc hoisting):
    const adversarial_src =
        "/** header\rinjected_guard */\n\n" ++
        "pub struct State {\n    pub counter: u32,\n}\n\n" ++
        "pub struct Box[T: Copy = u32, const CAP: usize = 8] {\n" ++
        "    pub item: T,\n" ++
        "    pub fn peek(&self) -> T { return self.item; }\n" ++
        "}\n\n" ++
        "@inline\n" ++
        "/// Hoisted above `@inline`.\n" ++
        "pub fn elif(seed: u32) -> u32 { return seed; }\n\n" ++
        "pub fn preserve_valid_ident_and_places(state: &mut State, pair: (u32, u32)) -> u32 {\n" ++
        "    var arr: [u32; 2] = [0_u32, 0_u32];\n" ++
        "    let ((_, _), (nested_ok, _)) = ((1_u32, 2_u32), pair);\n" ++
        "    (state.counter, _) = pair;\n" ++
        "    if nested_ok > 0_u32 {\n" ++
        "        arr[0] = 1_u32;\n" ++
        "    }\n" ++
        "    let call_val = elif(nested_ok);\n" ++
        "    return call_val + arr[0];\n" ++
        "}\n";
    var adv_res = try upgradeSource(std.testing.allocator, adversarial_src, FileId.fromInt(61), .{});
    defer adv_res.deinit(std.testing.allocator);
    try std.testing.expect(adv_res.is_changed);
    try std.testing.expect(!adv_res.is_rolled_back);
    const adv_out = adv_res.upgraded_source;
    try std.testing.expect(std.mem.indexOf(u8, adv_out, "/# header\n/# injected_guard\n") != null);
    try std.testing.expect(std.mem.indexOf(u8, adv_out, "impl[T: Copy, const CAP: usize] Box[T, CAP] {") != null);
    try std.testing.expect(std.mem.indexOf(u8, adv_out, "/| Hoisted above `@inline`.\n@inline\npub fn elif") != null);
    try std.testing.expect(std.mem.indexOf(u8, adv_out, "let ((_, _), (nested_ok, _)) = ((1_u32, 2_u32), pair);") != null);
    try std.testing.expect(std.mem.indexOf(u8, adv_out, "(state.counter, _) = pair;") != null);
    try std.testing.expect(std.mem.indexOf(u8, adv_out, "elif(nested_ok)") != null);
    try std.testing.expectEqual(@as(u32, 0), try countSyntaxErrors(std.testing.allocator, FileId.fromInt(62), adv_out));
}

test "test_dr24_ur24_00_through_ur24_06_showcases_and_idempotency" {
    const dr24_legacy_cx =
        \\//! Ring slab module docs.
        \\
        \\//// Decorative banner preserved verbatim ////
        \\
        \\pub mod tag_mod {
        \\    pub fn pick(label: str) -> str = label;
        \\}
        \\
        \\/// Cache-line aligned wire header (`Span16`-style non-adjacent layout attrs).
        \\@repr_c
        \\@derive(Copy, Clone, Equatable)
        \\@cache_aligned
        \\@zero_pad
        \\pub struct Span16 {
        \\    pub lo: u64,
        \\    pub hi: u64,
        \\}
        \\
        \\@packed(2)
        \\pub struct WireHdr {
        \\    pub tag: u16,
        \\}
        \\
        \\@link_name("__cx_ring_sym")
        \\@link_section(".text.hot")
        \\pub fn exported_hook() {}
        \\
        \\@[must_use, no_alloc, no_panic]
        \\pub fn id(code: u32) -> u32 = code;
        \\
        \\@inline
        \\@no_alloc
        \\@no_panic
        \\fn step_private(cur: u16) -> u16 {
        \\    return cur +% 1_u16;
        \\}
        \\
        \\@no_alloc
        \\fn reified_cb(cur: u32) -> u32 {
        \\    return cur;
        \\}
        \\
        \\pub fn use_reified() -> u32 {
        \\    let fn_ptr: @no_alloc fn(u32) -> u32 = reified_cb;
        \\    return fn_ptr(7_u32);
        \\}
        \\
        \\pub fn classify_and_format(port: u16, delta: i32, code: u32) -> usize {
        \\    //! Mid-file module doc downgraded to `//`.
        \\    let inline_cmt = /* mid-line comment */ step_private(port);
        \\    _ = inline_cmt;
        \\    let empty_json = "{{}}";
        \\    let keep_route = "/users/{id}";
        \\    let keep_pct = "{p}%";
        \\    let live_port = "0.0.0.0:{port}";
        \\    let live_sum = "{delta + 1}";
        \\    let multi_msg = """
        \\        bound={tag_mod::pick(r"""ok""")}
        \\        """;
        \\    _ = empty_json;
        \\    _ = keep_route;
        \\    _ = keep_pct;
        \\    _ = live_port;
        \\    _ = live_sum;
        \\    _ = multi_msg;
        \\    let sign_val = if delta < 0 { -1_i32 } else if delta > 0 { 1_i32 } else { 0_i32 };
        \\    _ = sign_val;
        \\    let match_stay = if code == 1_u32 { 10_usize } else if code == 2_u32 { 20_usize } else if code == 3_u32 { 30_usize } else { 0_usize };
        \\    let picked_len = if port > 0_u16 { "live" } else { "idle" }.len();
        \\    return match_stay +% picked_len;
        \\}
    ++ "\n";

    var pass1 = try upgradeSource(std.testing.allocator, dr24_legacy_cx, FileId.fromInt(70), .{});
    defer pass1.deinit(std.testing.allocator);
    try std.testing.expect(pass1.is_changed);
    try std.testing.expect(!pass1.is_rolled_back);

    const out = pass1.upgraded_source;
    // `UR-24-00`:
    try std.testing.expect(std.mem.startsWith(u8, out, "/# Ring slab module docs.\n\n"));
    try std.testing.expect(std.mem.indexOf(u8, out, "//// Decorative banner preserved verbatim ////") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "/| Cache-line aligned wire header") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "// Mid-file module doc downgraded to `//`.") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "// mid-line comment\n    let inline_cmt = step_private(port);") != null);

    // `UR-24-03` & `UR-24-04` + horizontal `fmt_engine` attribute packing (`<= 100` cols, `.CacheLine`):
    try std.testing.expect(
        std.mem.indexOf(u8, out, "@repr(C, align: .CacheLine, zero_pad: true) @derive(Copy, Clone, Equatable)\npub struct Span16") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, out, "@repr(C, packed: 2)\npub struct WireHdr") != null);
    try std.testing.expect(
        std.mem.indexOf(u8, out, "@link(name: \"__cx_ring_sym\", section: \".text.hot\")\npub fn exported_hook()") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, out, "@no_alloc @no_panic @must_use\npub fn id(") != null);

    // `UR-24-05` (`step_private` stripped completely; `reified_cb` keeps `@no_alloc` due to fn-pointer reification!):
    try std.testing.expect(std.mem.indexOf(u8, out, "\nfn step_private(cur: u16) -> u16") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "@no_alloc\nfn reified_cb(cur: u32) -> u32") != null);

    // `UR-24-01` & `UR-24-02` (Branch A + Branch B + nested `::` & `r"""…"""` + idempotent plain literals):
    try std.testing.expect(std.mem.indexOf(u8, out, "let empty_json = \"{}\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "let keep_route = \"/users/{id}\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "let keep_pct = \"{p}%\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "let live_port = f\"0.0.0.0:{port}\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "let live_sum = f\"{delta + 1}\";") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "tag_mod.pick(r\"ok\")") != null);

    // `UR-24-06` (`sign_val` & parenthesized `(if …).len()` upgrade; 3-arm single-scrutinee `match_stay` stays braced):
    try std.testing.expect(std.mem.indexOf(u8, out, "if delta < 0 => -1_i32") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "(if port > 0_u16 => \"live\" else \"idle\").len()") != null);
    try std.testing.expect(std.mem.indexOf(u8, out, "if code == 1_u32 {") != null);
    try std.testing.expectEqual(@as(u32, 0), try countSyntaxErrors(std.testing.allocator, FileId.fromInt(71), out));

    // Strict idempotency check (`upgrade(upgrade(x)) == upgrade(x)` with 0 edits):
    var pass2 = try upgradeSource(std.testing.allocator, out, FileId.fromInt(72), .{});
    defer pass2.deinit(std.testing.allocator);
    try std.testing.expect(!pass2.is_changed);
    try std.testing.expectEqual(@as(u32, 0), pass2.applied_edit_count);
    try std.testing.expectEqualStrings(out, pass2.upgraded_source);
}

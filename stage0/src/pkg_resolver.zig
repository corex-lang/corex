//! Hybrid Bounded-MVS + Bounded PubGrub CDCL Package & Feature Resolver (`pkg_resolver.zig`)
//!
//! Implements `DR-11` §3–§4 and `DR-16` §2–§3: `SeriesKey` major/0.x/0.0.z compatibility-series
//! coexistence, `< 5 ms` $O(V + E)$ `Bounded-MVS` monotone SemVer + `FeatureBitset512` unification
//! (including weak `foo?/feat` fixed-point activation), bounded `100,000`-step `PubGrub CDCL`
//! conflict resolution with `ConflictDagExport` monochrome proof trees (`E0010`), native `links`
//! uniqueness (`E0011`), sparse registry / Git / path / script fetching, Ed25519 + RFC 6962 + Bao
//! CAS verification (`E0015`), hermetic `--locked`/`--offline`/`--frozen` guards (`E0014`/`E0016`),
//! and transactional zero-friction auto-sync into `corex.toml` and `corex.lock`.
//!
//! Shares canonical `SemVer`, `VersionReq`, `Manifest`, `Lockfile`, and `@cfg` types directly from
//! `pkg_manifest.zig`, `pkg_cache.zig`, and `pkg_conflict_seam.zig` with zero parser duplication.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const mir_sast = @import("mir_sast.zig");
const codegen_abi = @import("codegen_abi.zig");
const diagnostic = @import("diag/diagnostic.zig");
const style = @import("cli/style.zig");
const pkg_conflict_seam = @import("pkg_conflict_seam.zig");
const pkg_cxi_seam = @import("pkg_cxi_seam.zig");
const pkg_manifest = @import("pkg_manifest.zig");
const pkg_cache = @import("pkg_cache.zig");

const FileId = mem_foundation.FileId;
const StringId = mem_foundation.StringId;
const SymbolId = mem_foundation.SymbolId;
const Span = mem_foundation.Span;
const BumpArena = mem_foundation.BumpArena;
const StringInterner = mem_foundation.StringInterner;
const PackageId = vfs_sourcemap.PackageId;
const Glyphs = style.Glyphs;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const SuggestedFix = diagnostic.SuggestedFix;

// ---------------------------------------- TYPES ----------------------------------------

// ------------- Re-Exported Canonical Shared Types -------------

/// Re-exported compatibility-series tier (`pkg_manifest.SeriesTier`).
pub const SeriesTier = pkg_manifest.SeriesTier;
/// Re-exported 12-byte SemVer numeric core (`pkg_manifest.SemVerCore`).
pub const SemVerCore = pkg_manifest.SemVerCore;
/// Re-exported 20-byte SemVer 2.0.0 record (`pkg_manifest.SemVer`).
pub const SemVer = pkg_manifest.SemVer;
/// Re-exported version comparator operator (`pkg_manifest.ComparatorOp`).
pub const ComparatorOp = pkg_manifest.ComparatorOp;
/// Re-exported normalized version comparator atom (`pkg_manifest.VersionComparator`).
pub const VersionComparator = pkg_manifest.VersionComparator;
/// Re-exported SemVer requirement conjunction (`pkg_manifest.VersionReq`).
pub const VersionReq = pkg_manifest.VersionReq;
/// Re-exported dependency table section kind (`pkg_manifest.DepKind`).
pub const DepKind = pkg_manifest.DepKind;
/// Re-exported Git revision selector kind (`pkg_manifest.GitRevKind`).
pub const GitRevKind = pkg_manifest.GitRevKind;
/// Re-exported dependency source specification (`pkg_manifest.DepSourceSpec`).
pub const DepSourceSpec = pkg_manifest.DepSourceSpec;
/// Re-exported normalized dependency edge (`pkg_manifest.DependencySpec`).
pub const DependencySpec = pkg_manifest.DependencySpec;
/// Re-exported version exclusion rule (`pkg_manifest.ExcludeRule`).
pub const ExcludeRule = pkg_manifest.ExcludeRule;
/// Re-exported transitive `[patch]` override (`pkg_manifest.PatchSpec`).
pub const PatchSpec = pkg_manifest.PatchSpec;
/// Re-exported first-lock capability policy preset (`pkg_manifest.DefaultDepPolicy`).
pub const DefaultDepPolicy = pkg_manifest.DefaultDepPolicy;
/// Re-exported capability enforcement scope (`pkg_manifest.EnforcementScope`).
pub const EnforcementScope = pkg_manifest.EnforcementScope;
/// Re-exported `[security]` policy (`pkg_manifest.SecurityPolicy`).
pub const SecurityPolicy = pkg_manifest.SecurityPolicy;
/// Re-exported `[package]` metadata (`pkg_manifest.PackageMeta`).
pub const PackageMeta = pkg_manifest.PackageMeta;
/// Re-exported `[features]` entry (`pkg_manifest.FeatureDecl`).
pub const FeatureDecl = pkg_manifest.FeatureDecl;
/// Re-exported validated `corex.toml` manifest (`pkg_manifest.Manifest`).
pub const Manifest = pkg_manifest.Manifest;
/// Re-exported workspace member descriptor (`pkg_manifest.WorkspaceMember`).
pub const WorkspaceMember = pkg_manifest.WorkspaceMember;
/// Re-exported workspace manifest bundle (`pkg_manifest.WorkspaceManifestBundle`).
pub const WorkspaceManifestBundle = pkg_manifest.WorkspaceManifestBundle;
/// Re-exported inline `use "<spec>" as <alias>;` descriptor (`pkg_manifest.InlineUseSpec`).
pub const InlineUseSpec = pkg_manifest.InlineUseSpec;
/// Re-exported `corex.lock` package record (`pkg_manifest.LockPackage`).
pub const LockPackage = pkg_manifest.LockPackage;
/// Re-exported `corex.lock` document (`pkg_manifest.Lockfile`).
pub const Lockfile = pkg_manifest.Lockfile;
/// Re-exported 16-bit capability bitmask (`mir_sast.EffectCapabilityMask`).
pub const EffectCapabilityMask = mir_sast.EffectCapabilityMask;
/// Re-exported PubGrub incompatibility kind (`pkg_conflict_seam.IncompatKind`).
pub const IncompatKind = pkg_conflict_seam.IncompatKind;
/// Re-exported 16-byte PubGrub incompatibility term (`pkg_conflict_seam.IncompatTerm`).
pub const IncompatTerm = pkg_conflict_seam.IncompatTerm;
/// Re-exported 24-byte PubGrub incompatibility node (`pkg_conflict_seam.IncompatNode`).
pub const IncompatNode = pkg_conflict_seam.IncompatNode;
/// Re-exported 24-byte lossless TOML span anchor (`pkg_conflict_seam.TomlSpanAnchor`).
pub const TomlSpanAnchor = pkg_conflict_seam.TomlSpanAnchor;
/// Re-exported level-0 conflict DAG (`pkg_conflict_seam.ConflictDagExport`).
pub const ConflictDagExport = pkg_conflict_seam.ConflictDagExport;

// ------------- SeriesKey, Bitsets & Graph Records -------------

/// Exact 12-byte zero-padding compatibility-series key identifying an MVS / PubGrub node (`DR-11` §3.1).
pub const SeriesKey = extern struct {
    /// Interned canonical `kebab-case` package name (`SymbolId`).
    pkg_name_sym: SymbolId,
    /// Compatibility series tier (`major_ge_1`, `minor_0_x`, or `patch_0_0_z`).
    tier: SeriesTier = .major_ge_1,
    /// Backing source domain (`0 = registry`, `1 = git`, `2 = path`, `3 = workspace_member`).
    source_tag: u8 = SOURCE_TAG_REGISTRY,
    /// Explicit zero padding guaranteeing unique C-ABI byte layout (`AutoHashMap`-safe).
    _pad: u16 = 0,
    /// Series slot ordinal (`major`, `minor`, `patch`) or interned `git`/`path` locator `StringId.asInt()`.
    series_or_source_id: u32 = 0,

    /// Constructs a registry `SeriesKey` for `(pkg_name_sym, ver)` using `DR-11` §3.1 slot rules.
    pub inline fn forRegistrySemVer(pkg_name_sym: SymbolId, ver: SemVer) SeriesKey {
        const slot = ver.seriesSlot();
        return .{
            .pkg_name_sym = pkg_name_sym,
            .tier = slot.tier,
            .source_tag = SOURCE_TAG_REGISTRY,
            .series_or_source_id = slot.number,
        };
    }

    /// Computes a deterministic 64-bit `Wyhash(0)` digest of this `SeriesKey`.
    pub inline fn hash64(self: SeriesKey) u64 {
        return std.hash.Wyhash.hash(0, std.mem.asBytes(&self));
    }
};

/// Fast stack-allocated 512-bit feature bitset (`64B`) for `< 5 ms` $O(1)$ MVS feature unification.
pub const FeatureBitset512 = struct {
    /// Eight 64-bit bitset words covering dense feature ordinals `0..511`.
    words: [8]u64 = @splat(0),

    /// Returns `true` when bit `bit_idx` (`< 512`) is set.
    pub inline fn isSet(self: FeatureBitset512, bit_idx: u16) bool {
        if (bit_idx >= 512) return false;
        const word_idx: usize = bit_idx >> 6;
        const shift_amt: u6 = @truncate(bit_idx);
        return ((self.words[word_idx] >> shift_amt) & 1) != 0;
    }

    /// Sets bit `bit_idx` (`< 512`) and returns `true` if the bit transitioned from `0` to `1`.
    pub inline fn setReturningChanged(self: *FeatureBitset512, bit_idx: u16) bool {
        if (bit_idx >= 512) return false;
        const word_idx: usize = bit_idx >> 6;
        const shift_amt: u6 = @truncate(bit_idx);
        const mask: u64 = @as(u64, 1) << shift_amt;
        const is_new = (self.words[word_idx] & mask) == 0;
        self.words[word_idx] |= mask;
        return is_new;
    }

    /// Unions `other` into `self` and returns `true` if `(other \ self) != ∅` (`P2-1`).
    pub inline fn unionReturningChanged(self: *FeatureBitset512, other: FeatureBitset512) bool {
        var has_changed = false;
        var i: usize = 0;
        while (i < 8) : (i += 1) {
            const added = other.words[i] & ~self.words[i];
            if (added != 0) {
                self.words[i] |= added;
                has_changed = true;
            }
        }
        return has_changed;
    }
};

/// Backing storage origin for a resolved package node in `ResolvedPackageGraph`.
pub const PackageSourceKind = enum(u8) {
    /// Root or sibling workspace member directory (`0`).
    workspace_member = 0,
    /// Local filesystem `path = "…"` dependency (`1`).
    local_path = 1,
    /// Sparse registry package verified in `PkgCache` (`2`).
    sparse_registry = 2,
    /// Pinned Git commit tree ingested into `PkgCache` (`3`).
    git_pinned = 3,
    /// Pre-verified `.cxtree` content-addressed archive in `PkgCache` (`4`).
    cxtree_cas = 4,
};

/// Resolved direct dependency alias binding (`alias_sym -> target_pkg_id`) on a `ResolvedPackageNode`.
pub const ResolvedDepBinding = struct {
    /// Interned `.cx` `snake_case` module identifier visible inside the declaring package.
    alias_sym: SymbolId,
    /// Borrowed `snake_case` module alias slice.
    alias_text: []const u8,
    /// Borrowed `kebab-case` manifest dependency key slice.
    alias_kebab: []const u8,
    /// Target `PackageId` in `ResolvedPackageGraph`.
    target_pkg_id: PackageId,
    /// Source span of the dependency declaration in `corex.toml` or `.cx` inline `use`.
    decl_span: Span,
    /// Optional explicit per-edge `allow_caps` override (`null` inherits `[security]`).
    explicit_allow_caps: ?EffectCapabilityMask = null,
    /// Explicit per-edge `deny_caps` blockmask.
    explicit_deny_caps: EffectCapabilityMask = .EMPTY,
};

/// Single resolved package instance in bottom-up topological dependency order (`deps` before `dependents`).
pub const ResolvedPackageNode = struct {
    /// Assigned 16-bit `PackageId` (`0` = primary root target, `>= 2` = workspace peers & external deps).
    pkg_id: PackageId,
    /// Interned canonical `kebab-case` package name (`SymbolId`).
    canonical_name_sym: SymbolId,
    /// Borrowed canonical `kebab-case` package name (e.g., `"corex-http"`).
    canonical_name: []const u8,
    /// Default `snake_case` `.cx` module name (e.g., `"corex_http"`).
    default_snake_name: []const u8,
    /// Selected exact SemVer 2.0.0 version.
    version: SemVer,
    /// Compatibility series key.
    series_key: SeriesKey,
    /// Backing source classification.
    source_kind: PackageSourceKind,
    /// Canonical lockfile source URI (`"root"`, `"registry+…"`, `"git+…#<sha>"`, `"path+file://…"`).
    source_uri: []const u8,
    /// Host root directory (for `.workspace_member` / `.local_path`) or virtual `/cx/<name>@<ver>` prefix.
    package_root_path: []const u8,
    /// Relative POSIX path to library root `.cx` file (`"src/root.cx"` / `"src/lib.cx"`, `null` if bin-only).
    lib_root_rel_path: ?[]const u8 = null,
    /// Relative POSIX path to binary entry `.cx` file (`"src/main.cx"`, `null` if lib-only).
    bin_root_rel_path: ?[]const u8 = null,
    /// Verified 32-byte `.cxtree` Merkle digest (`tree_hash` in `corex.lock`).
    cxtree_blake3: ?[32]u8 = null,
    /// Optional 32-byte archive `BLAKE3` digest (`checksum` in `corex.lock`).
    archive_checksum: ?[32]u8 = null,
    /// Optional 64-byte publisher `Ed25519` signature (`signature` in `corex.lock`).
    signature: ?[64]u8 = null,
    /// Optional RFC 6962 transparency-log leaf index (`tlog_index` in `corex.lock`).
    tlog_index: ?u64 = null,
    /// Optional pre-existing `cxi_blake3` recorded in `corex.lock` (verified under `--locked`).
    locked_cxi_blake3: ?[32]u8 = null,
    /// Monotone unified enabled feature names sorted ASCII-ascending.
    enabled_features: [][]const u8 = &.{},
    /// Complete `[features]` names sorted ASCII-ascending (gates `E0435`).
    declared_features: [][]const u8 = &.{},
    /// `true` when the package manifest explicitly declared a `[features]` table or optional deps.
    has_feature_manifest: bool = false,
    /// Direct dependency alias bindings visible exclusively to `pkg_id`.
    dependencies: []ResolvedDepBinding = &.{},
    /// Optional exclusive native C library linkage key (`links = "z"` -> `E0011` if duplicated).
    native_links_lib: ?[]const u8 = null,
    /// Effective `PackageCapPolicy` computed from root `[security]` + lockfile ceilings (`DR-17`).
    cap_policy: mir_sast.PackageCapPolicy = .{},
    /// Primary manifest span for diagnostics.
    manifest_span: Span = Span.ZERO,
};

/// Complete deterministic dependency & feature resolution output returned by `resolveProjectGraph`.
pub const ResolvedPackageGraph = struct {
    /// Backing arena owning all strings, feature slices, and `ResolvedPackageNode` slices.
    arena: BumpArena,
    /// Topologically sorted package nodes (`packages[i]` only depends on `packages[0..i]`).
    packages: []ResolvedPackageNode,
    /// Primary target `PackageId` (`PackageId.root`).
    root_pkg_id: PackageId = .root,
    /// Deduplicated native `-l<lib>` stems collected from `native_links_lib` in link order.
    ordered_native_link_libs: [][]const u8 = &.{},
    /// `true` when Tier-1 Bounded-MVS succeeded without invoking Tier-2 PubGrub CDCL.
    has_used_mvs_fast_path: bool = true,
    /// Total solver steps executed (`<= MAX_SOLVER_STEPS`).
    solver_steps: u32 = 0,
    /// `true` when unlocked auto-sync transactionally updated `corex.toml` on disk.
    has_auto_synced_manifest: bool = false,
    /// Exported minimized level-0 `ConflictDagExport` when `E0010` occurred (`null` on success).
    conflict_dag: ?ConflictDagExport = null,

    /// Releases `arena` memory owned by `self`.
    pub fn deinit(self: *ResolvedPackageGraph, allocator: std.mem.Allocator) void {
        _ = allocator;
        self.arena.deinit();
        self.* = undefined;
    }
};

/// Configuration options governing `resolveProjectGraph`.
pub const ResolveOptions = struct {
    /// Zig `std.Io` handle for CAS, local registry, and local Git operations.
    io: std.Io,
    /// Optional process environment map (`COREX_REGISTRY_DIR`, `COREX_HERMETIC`, etc.).
    environ_map: ?*const std.process.Environ.Map = null,
    /// Active cross-compilation target specification for `target = "…"` `@cfg` predicates.
    target_spec: codegen_abi.TargetSpec = codegen_abi.TargetSpec.host(),
    /// Toolchain SemVer evaluated against `[package].corex` bounds.
    compiler_version: SemVer = .{ .major = 0, .minor = 1, .patch = 0 },
    /// Activated CLI feature tokens from `-F` / `--features` (`"feat"` or `"pkg/feat"`).
    cli_features: []const []const u8 = &.{},
    /// `true` when `--no-default-features` disables implicit `"default"` on root.
    has_no_default_features: bool = false,
    /// `true` when compiling `corex test` / `corex bench` (includes root `[dev-dependencies]`).
    is_including_tests: bool = false,
    /// `true` when `--locked`, `--frozen`, or `COREX_HERMETIC=1` forbids lockfile/manifest drift.
    is_locked: bool = false,
    /// `true` when `--offline`, `--frozen`, or `COREX_HERMETIC=1` forbids external fetches.
    is_offline: bool = false,
    /// `true` when `--frozen` or `COREX_HERMETIC=1` is active.
    is_frozen: bool = false,
    /// `true` when `--verify-checksums` forces full `.cxtree` and blob `BLAKE3` re-verification.
    is_verifying_checksums: bool = false,
    /// Optional local sparse-registry directory override (`COREX_REGISTRY_DIR` fallback).
    local_registry_dir: ?[]const u8 = null,
    /// Canonical `COREX_HOME` directory path owning `cache/blake3`.
    corex_home_dir: []const u8,
    /// Active inline `use "<spec>" as <alias>;` imports extracted from root `.cx` files.
    inline_imports: []const symbol_resolver.InlineUseImport = &.{},
    /// Unresolved bare `use <snake_pkg>…;` root identifiers eligible for unlocked auto-sync.
    unresolved_use_roots: []const []const u8 = &.{},
};

// ----------------- Internal Solver Structures -----------------

/// Candidate version metadata loaded from workspace, path, Git, or sparse registry index.
const CandidateVersionMeta = struct {
    /// Exact SemVer 2.0.0 version.
    version: SemVer,
    /// Backing source classification.
    source_kind: PackageSourceKind,
    /// Interned canonical source URI (`"registry+…"`, `"git+…#<sha>"`, `"path+file://…"`, `"root"`).
    source_uri: StringId,
    /// Optional host directory path (for `.workspace_member`, `.local_path`, or unpacked mock registry pkg).
    host_dir_path: ?[]const u8 = null,
    /// Optional relative library root path (`"src/root.cx"`).
    lib_root_rel_path: ?[]const u8 = null,
    /// Optional relative binary root path (`"src/main.cx"`).
    bin_root_rel_path: ?[]const u8 = null,
    /// `[package].corex` compiler version requirement (`StringId.empty` when unconstrained).
    corex_req: StringId = .empty,
    /// Exclusive native C library linkage key (`StringId.empty` when absent).
    links: StringId = .empty,
    /// `true` if marked `yanked = true` in the sparse registry index.
    is_yanked: bool = false,
    /// `true` if `[features]` or optional dependencies are declared.
    has_feature_manifest: bool = false,
    /// Sorted `[features]` declarations.
    features: []const FeatureDecl = &.{},
    /// Outgoing dependency edges from this candidate version.
    dependencies: []const DependencySpec = &.{},
    /// Expected `.cxtree` digest when known from index or `corex.lock`.
    expected_tree_blake3: ?[32]u8 = null,
    /// Expected archive `BLAKE3` digest when known from index or `corex.lock`.
    expected_checksum: ?[32]u8 = null,
    /// Optional publisher `Ed25519` public key (`32B`) from sparse index.
    publisher_pub_key: ?[32]u8 = null,
    /// Optional publisher `Ed25519` signature (`64B`) from sparse index or `corex.lock`.
    signature: ?[64]u8 = null,
    /// Optional RFC 6962 transparency-log leaf index.
    tlog_index: ?u64 = null,
    /// Optional RFC 6962 transparency-log tree size (`> 0` triggers Merkle proof verification).
    tlog_tree_size: ?u64 = null,
    /// Optional RFC 6962 transparency-log expected Merkle root (`32B`).
    tlog_root: ?[32]u8 = null,
    /// Optional RFC 6962 transparency-log sibling proof hashes.
    tlog_proof: []const [32]u8 = &.{},
    /// Optional RFC 6962 custom leaf payload (`null` uses canonical `"corex-publish-v1\n…"` leaf).
    tlog_leaf_override: ?[]const u8 = null,
    /// Optional companion `.obao` path in local registry store for Bao verification.
    obao_file_path: ?[]const u8 = null,
    /// Optional raw archive/cxtree file path in local registry store.
    archive_file_path: ?[]const u8 = null,
    /// Manifest span for diagnostics.
    manifest_span: Span = Span.ZERO,
};

/// Dense compatibility-series slot inside `SolverContext`.
const SeriesEntry = struct {
    /// Dense `u32` series index (`0` = primary root target, `1..` = peers & external series).
    series_id: u32,
    /// Canonical `12B` `SeriesKey`.
    key: SeriesKey,
    /// Sorted ascending candidate versions (`SemVer.compare` ASC).
    candidates: std.ArrayListUnmanaged(CandidateVersionMeta) = .empty,
    /// Dense feature table (`0..511` -> `StringId`) for `FeatureBitset512`.
    feature_ids: std.ArrayListUnmanaged(StringId) = .empty,
    /// $O(1)$ reverse map `StringId -> dense feature bit index`.
    feature_to_bit: std.AutoHashMapUnmanaged(StringId, u16) = .empty,

    /// Interns `feat_id` into `0..511` on this series (returning `>= 512` when overflowed).
    fn internFeatureBit(self: *SeriesEntry, allocator: std.mem.Allocator, feat_id: StringId) !u16 {
        if (self.feature_to_bit.get(feat_id)) |existing_bit| return existing_bit;
        const next_bit: u16 = @intCast(@min(self.feature_ids.items.len, std.math.maxInt(u16)));
        try self.feature_ids.append(allocator, feat_id);
        try self.feature_to_bit.put(allocator, feat_id, next_bit);
        return next_bit;
    }
};

/// Buffered weak feature activation (`"dep_alias?/feat_name"`) waiting for `dep_alias` activation.
const PendingWeakFeature = struct {
    /// Manifest `alias_kebab` of the optional dependency on this series.
    dep_alias_kebab: StringId,
    /// Feature `StringId` to activate on `dep_alias_kebab` once `dep:<alias>` becomes active.
    target_feat_id: StringId,
};

/// Per-series mutable state during Tier-1 `Bounded-MVS` fixed-point propagation.
const MvsNodeState = struct {
    /// `true` once reachable from `PackageId.root`.
    is_active: bool = false,
    /// Currently selected candidate index inside `SeriesEntry.candidates` (`0` minimal seed).
    selected_idx: u32 = 0,
    /// `true` if currently queued on the MVS FIFO worklist.
    is_in_worklist: bool = false,
    /// `true` if at least one active dependency edge requested implicit `"default"` on this series.
    has_default_feature_requested: bool = false,
    /// Enabled features in `0..511` fast bitset (`FeatureBitset512`).
    enabled_bits: FeatureBitset512 = .{},
    /// Overflow enabled features when `feature_ids.len > 512`.
    overflow_features: std.AutoHashMapUnmanaged(StringId, void) = .empty,
    /// Set of activated optional dependency aliases (`dep:<alias_kebab>`).
    active_opt_deps: std.AutoHashMapUnmanaged(StringId, void) = .empty,
    /// Buffered weak `foo?/feat` activations awaiting `active_opt_deps.contains(foo)`.
    pending_weak: std.ArrayListUnmanaged(PendingWeakFeature) = .empty,
};

/// Active constraint edge recorded during MVS / CDCL for upper-bound & `links` diagnostics.
const ActiveDepConstraint = struct {
    /// Requesting `series_id`.
    caller_series: u32,
    /// Requesting candidate version index.
    caller_ver_idx: u32,
    /// Target `series_id`.
    callee_series: u32,
    /// Version requirement imposed on `callee_series`.
    req: VersionReq,
    /// Optional gating feature `StringId` on `caller_series` (`.empty` when unconditional).
    gating_feat: StringId = .empty,
    /// Optional `TomlSpanAnchor` index in root manifest (`maxInt(u32)` when non-root).
    anchor_id: u32 = std.math.maxInt(u32),
    /// Source span of the dependency edge.
    decl_span: Span = Span.ZERO,
};

/// Packed `(series_id, feat_string_id)` key for boolean feature variables in Tier-2 PubGrub CDCL.
const SeriesFeatKey = extern struct {
    /// Target `series_id`.
    series_id: u32,
    /// Interned feature `StringId`.
    feat_id: StringId,
};

/// Human-readable auxiliary note attached to an `IncompatNode` index for `E0010` proof rendering.
const IncompatExplainMeta = struct {
    /// Optional formatted requirement text when `candidates` had zero matches (e.g., `"serde ^2.0.0"`).
    unmatched_req_label: ?[]const u8 = null,
    /// Source span fallback when `toml_anchor_id == maxInt(u32)`.
    span: Span = Span.ZERO,
};

/// Single trail assignment entry in Tier-2 `PubGrub CDCL` (`PartialAssignment`).
const CdclTrailEntry = struct {
    /// Decision level (`0` = root axioms & unit propagations at root, `>= 1` = speculative branches).
    decision_level: u32,
    /// `null` for a speculative decision; `IncompatNode` index for unit propagation.
    cause_incompat: ?u32,
    /// Assigned domain mutation kind (either narrowing `series_id` versions or setting `SeriesFeatKey`).
    mutation: union(enum) {
        /// Snapshot of `series_id`'s previous allowed-state bitset words before narrowing.
        series_domain: struct {
            /// Target `series_id`.
            series_id: u32,
            /// Saved bitset words (`len == wordsForStates(candidates.len + 1)`).
            prev_words: []u64,
        },
        /// Boolean feature assignment `(series_id, feat_id) = val`.
        feature_val: struct {
            /// Target `(series_id, feat_id)`.
            key: SeriesFeatKey,
            /// Assigned truth value.
            is_enabled: bool,
        },
    },
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum CDCL conflict-resolution iterations before deterministic abort (`DR-11` §3.3).
pub const MAX_SOLVER_STEPS: u32 = 100_000;
/// Maximum packages in a single resolved dependency graph (`u16` `PackageId` cap: `0..16,383`).
pub const MAX_RESOLVED_PACKAGES: u16 = 16_384;
/// Fast-path inline bitset capacity per package before overflow map fallback (`DR-11` §3.2).
pub const MAX_FEATURES_PER_PKG: u16 = 512;
/// Hard upper bound (`8 MiB`) on a single sparse-index metadata file (`DR-11` §4.1).
pub const MAX_INDEX_FILE_BYTES: usize = 8 * 1024 * 1024;
/// Open-ended upper-bound sentinel stored in `IncompatTerm.ver_max`.
const INF_VER_INDEX: u32 = std.math.maxInt(u32);
/// `SeriesKey.source_tag` for sparse HTTP/local registry packages (`0`).
pub const SOURCE_TAG_REGISTRY: u8 = 0;
/// `SeriesKey.source_tag` for direct Git repository packages (`1`).
pub const SOURCE_TAG_GIT: u8 = 1;
/// `SeriesKey.source_tag` for local filesystem `path` packages (`2`).
pub const SOURCE_TAG_PATH: u8 = 2;
/// `SeriesKey.source_tag` for workspace member packages (`3`).
pub const SOURCE_TAG_WORKSPACE: u8 = 3;
/// Default canonical sparse registry prefix written to `corex.lock`.
pub const DEFAULT_REGISTRY_URI = "registry+https://index.corex-lang.org/";
/// Default LRU entry cap passed to `PkgCache.init` during resolution (`4,096`).
const RESOLVER_CACHE_MAX_ENTRIES: u32 = 4096;
/// Default LRU byte cap (`64 MiB`) passed to `PkgCache.init` during resolution.
const RESOLVER_CACHE_MAX_BYTES: u64 = 64 * 1024 * 1024;

// -------------------------------------- INTERNALS --------------------------------------

// -------------- Bitset & `IncompatTerm` Encoding --------------

/// Returns the number of `u64` words required to represent `state_count` states (`>= 1`).
inline fn countStateWords(state_count: usize) usize {
    return @max((state_count + 63) / 64, 1);
}

/// Returns `true` if `state_idx` is set in `words`.
inline fn isStateBitSet(words: []const u64, state_idx: usize) bool {
    const word_i = state_idx >> 6;
    if (word_i >= words.len) return false;
    const bit_i: u6 = @truncate(state_idx);
    return ((words[word_i] >> bit_i) & 1) != 0;
}

/// Clears `state_idx` in `words`.
inline fn clearStateBit(words: []u64, state_idx: usize) void {
    const word_i = state_idx >> 6;
    if (word_i >= words.len) return;
    const bit_i: u6 = @truncate(state_idx);
    words[word_i] &= ~(@as(u64, 1) << bit_i);
}

/// Sets `state_idx` in `words`.
inline fn setStateBit(words: []u64, state_idx: usize) void {
    const word_i = state_idx >> 6;
    if (word_i >= words.len) return;
    const bit_i: u6 = @truncate(state_idx);
    words[word_i] |= (@as(u64, 1) << bit_i);
}

/// Counts total set bits across `words`.
fn popcountStateWords(words: []const u64) usize {
    var total: usize = 0;
    for (words) |word_val| {
        total += @popCount(word_val);
    }
    return total;
}

/// Returns the lowest set state index in `words`, or `null` if all zero.
fn firstSetStateBit(words: []const u64) ?usize {
    for (words, 0..) |word_val, word_i| {
        if (word_val != 0) {
            return (word_i << 6) + @ctz(word_val);
        }
    }
    return null;
}

/// Encodes a version-range `IncompatTerm` (`[ver_min .. ver_max]` inclusive).
inline fn makeVersionTerm(series_id: u32, ver_min: u32, ver_max: u32, is_positive: bool) IncompatTerm {
    const flags: u32 = (if (is_positive) @as(u32, 0x01) else 0) | 0x02 | 0x04;
    return .{
        .series_id = series_id,
        .ver_min = ver_min,
        .ver_max = ver_max,
        .flags_and_feat = flags,
    };
}

/// Encodes a feature-activation `IncompatTerm` (`bit 3` + 24-bit `feat_id` in `flags_and_feat >> 8`).
inline fn makeFeatureTerm(series_id: u32, feat_id: StringId, is_positive: bool) IncompatTerm {
    const feat_bits: u32 = (feat_id.asInt() & 0x00FF_FFFF) << 8;
    const flags: u32 = (if (is_positive) @as(u32, 0x01) else 0) | 0x08 | feat_bits;
    return .{
        .series_id = series_id,
        .ver_min = 0,
        .ver_max = INF_VER_INDEX,
        .flags_and_feat = flags,
    };
}

/// Returns `true` when `term` encodes a feature requirement (`bit 3` of `flags_and_feat`).
inline fn isFeatureTerm(term: IncompatTerm) bool {
    return (term.flags_and_feat & 0x08) != 0;
}

/// Returns `true` when `term` is positive (`bit 0` of `flags_and_feat`).
inline fn isPositiveTerm(term: IncompatTerm) bool {
    return (term.flags_and_feat & 0x01) != 0;
}

/// Extracts the 24-bit `StringId` from a feature `IncompatTerm`.
inline fn extractTermFeatureId(term: IncompatTerm) StringId {
    return StringId.fromInt((term.flags_and_feat >> 8) & 0x00FF_FFFF);
}

/// Evaluates whether discrete state `state_idx` (`0..cand_len - 1`, or `cand_len` = `ABSENT`) belongs to `States(term)`.
fn isStateMatchingVersionTerm(term: IncompatTerm, cand_len: usize, state_idx: usize) bool {
    const is_pos = isPositiveTerm(term);
    if (state_idx >= cand_len) {
        // `STATE_ABSENT`: never in `S ∈ Range`, always in `S ∉ Range`:
        return !is_pos;
    }
    const is_min_inc = (term.flags_and_feat & 0x02) != 0;
    const is_max_inc = (term.flags_and_feat & 0x04) != 0;
    const idx_u32: u32 = @intCast(state_idx);
    const is_above_min = if (is_min_inc) idx_u32 >= term.ver_min else idx_u32 > term.ver_min;
    const is_below_max = if (term.ver_max == INF_VER_INDEX)
        true
    else if (is_max_inc)
        idx_u32 <= term.ver_max
    else
        idx_u32 < term.ver_max;
    const is_in_range = is_above_min and is_below_max;
    return if (is_pos) is_in_range else !is_in_range;
}

// ---------- Hex, Digest & Filesystem Ingest Helpers -----------

/// Parses either `"b3:<64-hex>"`, `"blake3:<64-hex>"`, or raw `"<64-hex>"` into `[32]u8`.
fn parseFlexibleBlake3Hex(raw_text: []const u8) ?[32]u8 {
    const trimmed = std.mem.trim(u8, raw_text, " \t\r\n");
    const hex_slice = if (std.mem.startsWith(u8, trimmed, "b3:"))
        trimmed[3..]
    else if (std.mem.startsWith(u8, trimmed, "blake3:"))
        trimmed[7..]
    else
        trimmed;
    if (hex_slice.len != 64) return null;
    var out: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, hex_slice) catch return null;
    return out;
}

/// Parses either `"ed25519:<128-hex>"` or raw `"<128-hex>"` into `[64]u8`.
fn parseFlexibleEd25519SigHex(raw_text: []const u8) ?[64]u8 {
    const trimmed = std.mem.trim(u8, raw_text, " \t\r\n");
    const hex_slice = if (std.mem.startsWith(u8, trimmed, "ed25519:"))
        trimmed[8..]
    else
        trimmed;
    if (hex_slice.len != 128) return null;
    var out: [64]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, hex_slice) catch return null;
    return out;
}

/// Parses `"ed25519:<64-hex>"` or raw `"<64-hex>"` into a 32-byte Ed25519 public key.
fn parseFlexiblePubKeyHex(raw_text: []const u8) ?[32]u8 {
    const trimmed = std.mem.trim(u8, raw_text, " \t\r\n");
    const hex_slice = if (std.mem.startsWith(u8, trimmed, "ed25519:"))
        trimmed[8..]
    else
        trimmed;
    if (hex_slice.len != 64) return null;
    var out: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, hex_slice) catch return null;
    return out;
}

/// Returns `true` if `raw_str` is a 40-character ASCII hexadecimal Git SHA-1 OID.
fn isHexGitOid40(raw_str: []const u8) bool {
    if (raw_str.len != 40) return false;
    for (raw_str) |byte_val| {
        if (!std.ascii.isHex(byte_val)) return false;
    }
    return true;
}

/// Detects entry `.cx` relative paths (`src/root.cx`, `src/lib.cx`, `root.cx`, `src/main.cx`, `main.cx`) from `manifest` & `entries`.
fn detectEntryRelPathsFromList(
    arena: *BumpArena,
    interner: *const StringInterner,
    manifest_opt: ?*const Manifest,
    rel_paths: []const []const u8,
) !struct { lib_rel: ?[]const u8, bin_rel: ?[]const u8 } {
    var lib_rel: ?[]const u8 = null;
    var bin_rel: ?[]const u8 = null;

    if (manifest_opt) |manifest| {
        if (manifest.lib_target) |lib_t| {
            const p_str = interner.get(lib_t.path);
            if (p_str.len > 0) lib_rel = try arena.dupe(u8, p_str);
        } else if (manifest.package) |pkg_m| {
            const rm_str = interner.get(pkg_m.root_module);
            if (rm_str.len > 0) lib_rel = try arena.dupe(u8, rm_str);
        }
        if (manifest.bin_targets.len > 0) {
            const bp_str = interner.get(manifest.bin_targets[0].path);
            if (bp_str.len > 0) bin_rel = try arena.dupe(u8, bp_str);
        }
    }

    const hasPath = struct {
        /// Returns `true` if `needle` appears in `haystack`.
        fn check(haystack: []const []const u8, needle: []const u8) bool {
            for (haystack) |item| {
                if (std.mem.eql(u8, item, needle)) return true;
            }
            return false;
        }
    }.check;

    if (lib_rel == null) {
        if (hasPath(rel_paths, "src/root.cx")) {
            lib_rel = "src/root.cx";
        } else if (hasPath(rel_paths, "src/lib.cx")) {
            lib_rel = "src/lib.cx";
        } else if (hasPath(rel_paths, "root.cx")) {
            lib_rel = "root.cx";
        } else if (hasPath(rel_paths, "lib.cx")) {
            lib_rel = "lib.cx";
        }
    }
    if (bin_rel == null) {
        if (hasPath(rel_paths, "src/main.cx")) {
            bin_rel = "src/main.cx";
        } else if (hasPath(rel_paths, "main.cx")) {
            bin_rel = "main.cx";
        }
    }
    return .{ .lib_rel = lib_rel, .bin_rel = bin_rel };
}

/// Walks a host package directory, normalizes source files (`CRLF`->`LF`), optionally publishes blobs + `.cxtree` to `cache`,
/// and returns `(tree_blake3, cxtree_bytes, lib_rel, bin_rel)`.
fn ingestHostDirectoryAsCxTree(
    allocator: std.mem.Allocator,
    io: std.Io,
    arena: *BumpArena,
    interner: *const StringInterner,
    pkg_name: []const u8,
    dir_path: []const u8,
    manifest_opt: ?*const Manifest,
    cache_opt: ?*pkg_cache.PkgCache,
    is_publish_to_cache: bool,
    sink: ?*DiagnosticSink,
    span: Span,
) !struct {
    tree_blake3: [32]u8,
    cxtree_bytes: []align(8) u8,
    lib_rel: ?[]const u8,
    bin_rel: ?[]const u8,
} {
    var opened_dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer opened_dir.close(io);

    var walker = try opened_dir.walk(allocator);
    defer walker.deinit();

    var input_entries: std.ArrayListUnmanaged(pkg_cache.CxTreeInputEntry) = .empty;
    defer input_entries.deinit(allocator);
    var rel_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer rel_names.deinit(allocator);

    var blob_arena = BumpArena.init(allocator);
    defer blob_arena.deinit();

    while (try walker.next(io)) |entry| {
        if (entry.kind != .file) continue;
        const norm_rel = try arena.dupe(u8, entry.path);
        for (norm_rel) |*byte_ptr| {
            if (byte_ptr.* == '\\') byte_ptr.* = '/';
        }
        if (std.mem.startsWith(u8, norm_rel, ".git/") or
            std.mem.startsWith(u8, norm_rel, "target/") or
            std.mem.startsWith(u8, norm_rel, "build/") or
            std.mem.startsWith(u8, norm_rel, ".zig-cache/") or
            std.mem.startsWith(u8, norm_rel, "vendor/") or
            std.mem.eql(u8, norm_rel, "corex.lock"))
        {
            continue;
        }
        if (!vfs_sourcemap.isValidCxTreeRelativePath(norm_rel)) continue;

        const raw_bytes = try opened_dir.readFileAlloc(
            io,
            entry.path,
            allocator,
            .limited(vfs_sourcemap.MAX_SOURCE_FILE_BYTES),
        );
        defer allocator.free(raw_bytes);

        const norm_blob = try pkg_cache.normalizeSourceForBlobIngest(&blob_arena, norm_rel, raw_bytes);
        if (is_publish_to_cache) {
            if (cache_opt) |cache_inst| {
                try cache_inst.publishBlob(io, norm_blob.bytes, norm_blob.blake3_digest, sink, span);
            }
        }
        try input_entries.append(allocator, .{
            .rel_path = norm_rel,
            .file_mode = 0x01,
            .file_size = norm_blob.bytes.len,
            .file_blake3 = norm_blob.blake3_digest,
        });
        try rel_names.append(allocator, norm_rel);
    }

    const built = try pkg_cache.buildCxTreeBytes(allocator, pkg_name, input_entries.items, sink, span);
    errdefer allocator.free(built.bytes);

    if (is_publish_to_cache) {
        if (cache_opt) |cache_inst| {
            try cache_inst.publishCxTree(io, built.bytes, built.tree_blake3, sink, span);
        }
    }

    const detected = try detectEntryRelPathsFromList(arena, interner, manifest_opt, rel_names.items);
    return .{
        .tree_blake3 = built.tree_blake3,
        .cxtree_bytes = built.bytes,
        .lib_rel = detected.lib_rel,
        .bin_rel = detected.bin_rel,
    };
}

/// Parses an octal field inside a 512-byte POSIX USTAR tar header (`git archive --format=tar`).
fn parseTarOctalField(field_bytes: []const u8) ?u64 {
    var val: u64 = 0;
    var has_digit = false;
    for (field_bytes) |byte_val| {
        if (byte_val == 0 or byte_val == ' ') {
            if (has_digit) break;
            continue;
        }
        if (byte_val < '0' or byte_val > '7') return null;
        has_digit = true;
        val = (val << 3) | @as(u64, byte_val - '0');
    }
    return if (has_digit) val else 0;
}

/// Ingests an in-memory POSIX USTAR `.tar` stream (e.g., from `git archive` or registry `.tar`) into `PkgCache`,
/// returning `(tree_blake3, manifest_bytes_opt, lib_rel, bin_rel)`.
fn ingestTarArchiveIntoCache(
    allocator: std.mem.Allocator,
    io: std.Io,
    arena: *BumpArena,
    pkg_name: []const u8,
    tar_bytes: []const u8,
    cache: *pkg_cache.PkgCache,
    sink: ?*DiagnosticSink,
    span: Span,
) !struct {
    tree_blake3: [32]u8,
    manifest_bytes: ?[]u8,
    lib_rel: ?[]const u8,
    bin_rel: ?[]const u8,
} {
    var input_entries: std.ArrayListUnmanaged(pkg_cache.CxTreeInputEntry) = .empty;
    defer input_entries.deinit(allocator);
    var rel_names: std.ArrayListUnmanaged([]const u8) = .empty;
    defer rel_names.deinit(allocator);

    var blob_arena = BumpArena.init(allocator);
    defer blob_arena.deinit();

    var manifest_copy: ?[]u8 = null;
    errdefer if (manifest_copy) |mb| allocator.free(mb);

    var offset: usize = 0;
    while (offset < tar_bytes.len) {
        if (tar_bytes.len - offset < 512) {
            var is_tail_zero = true;
            for (tar_bytes[offset..]) |tail_byte| {
                if (tail_byte != 0) {
                    is_tail_zero = false;
                    break;
                }
            }
            if (is_tail_zero) break;
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = .e0015_cache_integrity_mismatch,
                    .severity = .err,
                    .primary_span = span,
                    .message = "truncated `.tar` package archive header",
                });
            }
            return error.CacheIntegrityMismatch;
        }

        const hdr = tar_bytes[offset .. offset + 512];
        offset += 512;

        var is_all_zero = true;
        for (hdr) |byte_val| {
            if (byte_val != 0) {
                is_all_zero = false;
                break;
            }
        }
        if (is_all_zero) break;

        const file_size_u64 = parseTarOctalField(hdr[124..136]) orelse {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = .e0015_cache_integrity_mismatch,
                    .severity = .err,
                    .primary_span = span,
                    .message = "corrupt octal size field in `.tar` package archive header",
                });
            }
            return error.CacheIntegrityMismatch;
        };
        if (file_size_u64 > vfs_sourcemap.MAX_SOURCE_FILE_BYTES or file_size_u64 > tar_bytes.len - offset) {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = .e0015_cache_integrity_mismatch,
                    .severity = .err,
                    .primary_span = span,
                    .message = "truncated or oversized entry in `.tar` package archive",
                });
            }
            return error.CacheIntegrityMismatch;
        }
        const file_size: usize = @intCast(file_size_u64);
        const type_flag = hdr[156];
        const payload = tar_bytes[offset .. offset + file_size];
        const padded_size = std.math.add(usize, file_size, 511) catch {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = .e0015_cache_integrity_mismatch,
                    .severity = .err,
                    .primary_span = span,
                    .message = "overflowing `.tar` archive entry block size",
                });
            }
            return error.CacheIntegrityMismatch;
        };
        const padded_advance = padded_size & ~@as(usize, 511);
        offset = if (padded_advance <= tar_bytes.len - offset) offset + padded_advance else tar_bytes.len;

        // Skip directories, PAX extended headers (`'x'`, `'g'`), and symlinks (`'2'`):
        if (type_flag != 0 and type_flag != '0') continue;

        const name_end = std.mem.indexOfScalar(u8, hdr[0..100], 0) orelse 100;
        const prefix_end = std.mem.indexOfScalar(u8, hdr[345..500], 0) orelse 155;
        const raw_name = hdr[0..name_end];
        const raw_prefix = hdr[345 .. 345 + prefix_end];

        const joined_rel = if (raw_prefix.len > 0)
            try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ raw_prefix, raw_name })
        else
            try arena.dupe(u8, raw_name);

        const trimmed_rel = std.mem.trimStart(u8, joined_rel, "./");
        if (trimmed_rel.len == 0 or std.mem.eql(u8, trimmed_rel, "pax_global_header")) continue;
        if (!vfs_sourcemap.isValidCxTreeRelativePath(trimmed_rel)) continue;

        const norm_blob = try pkg_cache.normalizeSourceForBlobIngest(&blob_arena, trimmed_rel, payload);
        try cache.publishBlob(io, norm_blob.bytes, norm_blob.blake3_digest, sink, span);
        if (std.mem.eql(u8, trimmed_rel, "corex.toml") and manifest_copy == null) {
            manifest_copy = try allocator.dupe(u8, norm_blob.bytes);
        }
        try input_entries.append(allocator, .{
            .rel_path = trimmed_rel,
            .file_mode = 0x01,
            .file_size = norm_blob.bytes.len,
            .file_blake3 = norm_blob.blake3_digest,
        });
        try rel_names.append(allocator, trimmed_rel);
    }

    const built = try pkg_cache.buildCxTreeBytes(allocator, pkg_name, input_entries.items, sink, span);
    defer allocator.free(built.bytes);
    try cache.publishCxTree(io, built.bytes, built.tree_blake3, sink, span);

    var lib_rel: ?[]const u8 = null;
    var bin_rel: ?[]const u8 = null;
    for (rel_names.items) |rel_p| {
        if (std.mem.eql(u8, rel_p, "src/root.cx")) lib_rel = rel_p;
        if (lib_rel == null and std.mem.eql(u8, rel_p, "src/lib.cx")) lib_rel = rel_p;
        if (lib_rel == null and std.mem.eql(u8, rel_p, "root.cx")) lib_rel = rel_p;
        if (std.mem.eql(u8, rel_p, "src/main.cx")) bin_rel = rel_p;
        if (bin_rel == null and std.mem.eql(u8, rel_p, "main.cx")) bin_rel = rel_p;
    }
    return .{
        .tree_blake3 = built.tree_blake3,
        .manifest_bytes = manifest_copy,
        .lib_rel = lib_rel,
        .bin_rel = bin_rel,
    };
}

// ----------- Sparse Registry Index & Git Providers ------------

/// Parses a single JSON object from a sparse-index NDJSON line into `CandidateVersionMeta`.
fn parseSparseIndexJsonObject(
    allocator: std.mem.Allocator,
    arena: *BumpArena,
    interner: *StringInterner,
    reg_root_dir: ?[]const u8,
    obj: std.json.ObjectMap,
) !?CandidateVersionMeta {
    const vers_val = obj.get("vers") orelse obj.get("version") orelse return null;
    if (vers_val != .string) return null;
    const parsed_ver = (try SemVer.parse(interner, vers_val.string)) orelse return null;

    const pkg_name_str = if (obj.get("name")) |nv| (if (nv == .string) nv.string else "") else "";
    const is_yanked = if (obj.get("yanked")) |yv| (yv == .bool and yv.bool) else false;
    const links_id: StringId = if (obj.get("links")) |lv|
        (if (lv == .string and lv.string.len > 0) try interner.intern(lv.string) else .empty)
    else
        .empty;
    const corex_req_id: StringId = if (obj.get("corex")) |cv|
        (if (cv == .string and cv.string.len > 0) try interner.intern(cv.string) else .empty)
    else
        .empty;

    var deps_list: std.ArrayListUnmanaged(DependencySpec) = .empty;
    defer deps_list.deinit(allocator);
    if (obj.get("deps")) |deps_val| {
        if (deps_val == .array) {
            for (deps_val.array.items) |dep_item| {
                if (dep_item != .object) continue;
                const dep_obj = dep_item.object;
                const raw_name_v = dep_obj.get("name") orelse continue;
                if (raw_name_v != .string) continue;
                const alias_kebab = raw_name_v.string;
                const pkg_kebab = if (dep_obj.get("package")) |pv|
                    (if (pv == .string and pv.string.len > 0) pv.string else alias_kebab)
                else
                    alias_kebab;
                const req_str = if (dep_obj.get("req")) |rv|
                    (if (rv == .string) rv.string else "*")
                else
                    "*";
                const ver_req = (try VersionReq.parse(interner, req_str)) orelse continue;

                const kind_val: DepKind = if (dep_obj.get("kind")) |kv| blk_k: {
                    if (kv == .string) {
                        if (std.mem.eql(u8, kv.string, "dev")) break :blk_k .dev;
                        if (std.mem.eql(u8, kv.string, "build")) break :blk_k .build;
                    }
                    break :blk_k .normal;
                } else .normal;

                const is_opt = if (dep_obj.get("optional")) |ov| (ov == .bool and ov.bool) else false;
                const has_def = if (dep_obj.get("default_features")) |dv|
                    (if (dv == .bool) dv.bool else true)
                else if (dep_obj.get("default-features")) |dv2|
                    (if (dv2 == .bool) dv2.bool else true)
                else
                    true;
                const target_id: StringId = if (dep_obj.get("target")) |tv|
                    (if (tv == .string and tv.string.len > 0) try interner.intern(tv.string) else .empty)
                else
                    .empty;

                var feat_ids: std.ArrayListUnmanaged(StringId) = .empty;
                defer feat_ids.deinit(allocator);
                if (dep_obj.get("features")) |fv| {
                    if (fv == .array) {
                        for (fv.array.items) |f_elem| {
                            if (f_elem == .string and f_elem.string.len > 0) {
                                try feat_ids.append(allocator, try interner.intern(f_elem.string));
                            }
                        }
                    }
                }
                if (!pkg_manifest.isValidPackageNameKebab(alias_kebab)) continue;
                var snake_buf: [pkg_manifest.MAX_PKG_NAME_BYTES]u8 = undefined;
                for (alias_kebab, 0..) |ch_byte, i| {
                    snake_buf[i] = if (ch_byte == '-') '_' else ch_byte;
                }
                const snake_str = snake_buf[0..alias_kebab.len];

                try deps_list.append(allocator, .{
                    .alias_kebab = try interner.intern(alias_kebab),
                    .module_snake = try interner.intern(snake_str),
                    .package_kebab = try interner.intern(pkg_kebab),
                    .kind = kind_val,
                    .source = .{ .registry = ver_req },
                    .has_default_features = has_def,
                    .is_optional = is_opt,
                    .features = try arena.dupe(StringId, feat_ids.items),
                    .target_cfg = target_id,
                });
            }
        }
    }

    var feat_decls: std.ArrayListUnmanaged(FeatureDecl) = .empty;
    defer feat_decls.deinit(allocator);
    var has_feat_manifest = false;
    if (obj.get("features")) |feats_val| {
        if (feats_val == .object) {
            has_feat_manifest = true;
            var f_it = feats_val.object.iterator();
            while (f_it.next()) |kv| {
                var act_ids: std.ArrayListUnmanaged(StringId) = .empty;
                defer act_ids.deinit(allocator);
                if (kv.value_ptr.* == .array) {
                    for (kv.value_ptr.array.items) |act_elem| {
                        if (act_elem == .string and act_elem.string.len > 0) {
                            try act_ids.append(allocator, try interner.intern(act_elem.string));
                        }
                    }
                }
                try feat_decls.append(allocator, .{
                    .name = try interner.intern(kv.key_ptr.*),
                    .activations = try arena.dupe(StringId, act_ids.items),
                });
            }
        }
    }
    for (deps_list.items) |dep_s| {
        if (dep_s.is_optional) has_feat_manifest = true;
    }

    const expected_cksum: ?[32]u8 = if (obj.get("cksum") orelse obj.get("checksum")) |ck_v|
        (if (ck_v == .string) parseFlexibleBlake3Hex(ck_v.string) else null)
    else
        null;
    const expected_tree: ?[32]u8 = if (obj.get("tree_hash") orelse obj.get("tree_blake3")) |th_v|
        (if (th_v == .string) parseFlexibleBlake3Hex(th_v.string) else null)
    else
        null;
    const pub_key: ?[32]u8 = if (obj.get("pub_key") orelse obj.get("publisher_key")) |pk_v|
        (if (pk_v == .string) parseFlexiblePubKeyHex(pk_v.string) else null)
    else
        null;
    const sig_bytes: ?[64]u8 = if (obj.get("sig") orelse obj.get("signature")) |sg_v|
        (if (sg_v == .string) parseFlexibleEd25519SigHex(sg_v.string) else null)
    else
        null;
    const tlog_idx: ?u64 = if (obj.get("tlog_index")) |ti_v|
        (if (ti_v == .integer and ti_v.integer >= 0) @as(u64, @intCast(ti_v.integer)) else null)
    else
        null;
    const tlog_size: ?u64 = if (obj.get("tlog_tree_size")) |ts_v|
        (if (ts_v == .integer and ts_v.integer > 0) @as(u64, @intCast(ts_v.integer)) else null)
    else
        null;
    const tlog_root: ?[32]u8 = if (obj.get("tlog_root")) |tr_v|
        (if (tr_v == .string) parseFlexibleBlake3Hex(tr_v.string) else null)
    else
        null;
    const tlog_leaf_ov: ?[]const u8 = if (obj.get("tlog_leaf")) |tl_v|
        (if (tl_v == .string) try arena.dupe(u8, tl_v.string) else null)
    else
        null;

    var proof_hashes: std.ArrayListUnmanaged([32]u8) = .empty;
    defer proof_hashes.deinit(allocator);
    if (obj.get("tlog_proof")) |tp_v| {
        if (tp_v == .array) {
            for (tp_v.array.items) |p_item| {
                if (p_item == .string) {
                    if (parseFlexibleBlake3Hex(p_item.string)) |h_val| {
                        try proof_hashes.append(allocator, h_val);
                    }
                }
            }
        }
    }

    var host_pkg_dir: ?[]const u8 = null;
    var obao_path: ?[]const u8 = null;
    var archive_path: ?[]const u8 = null;
    if (reg_root_dir) |reg_dir| {
        if (obj.get("path") orelse obj.get("src_dir")) |dir_v| {
            if (dir_v == .string and dir_v.string.len > 0) {
                host_pkg_dir = if (std.fs.path.isAbsolute(dir_v.string))
                    try arena.dupe(u8, dir_v.string)
                else
                    try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ reg_dir, dir_v.string });
            }
        } else if (pkg_name_str.len > 0) {
            const ver_text = vers_val.string;
            var host_dir_buf: [512]u8 = undefined;
            if (std.fmt.bufPrint(&host_dir_buf, "{s}/packages/{s}-{s}", .{ reg_dir, pkg_name_str, ver_text })) |dir_s| {
                host_pkg_dir = try arena.dupe(u8, dir_s);
            } else |_| {
                host_pkg_dir = try std.fmt.allocPrint(
                    arena.asAllocator(),
                    "{s}/packages/{s}-{s}",
                    .{ reg_dir, pkg_name_str, ver_text },
                );
            }
        }
        if (obj.get("obao") orelse obj.get("obao_path")) |ob_v| {
            if (ob_v == .string and ob_v.string.len > 0) {
                obao_path = if (std.fs.path.isAbsolute(ob_v.string))
                    try arena.dupe(u8, ob_v.string)
                else
                    try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ reg_dir, ob_v.string });
            }
        }
        if (obj.get("archive") orelse obj.get("cxtree_path")) |ar_v| {
            if (ar_v == .string and ar_v.string.len > 0) {
                archive_path = if (std.fs.path.isAbsolute(ar_v.string))
                    try arena.dupe(u8, ar_v.string)
                else
                    try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ reg_dir, ar_v.string });
            }
        }
    }

    const src_uri_str = if (obj.get("source")) |sv|
        (if (sv == .string and sv.string.len > 0) sv.string else DEFAULT_REGISTRY_URI)
    else
        DEFAULT_REGISTRY_URI;

    return .{
        .version = parsed_ver,
        .source_kind = .sparse_registry,
        .source_uri = try interner.intern(src_uri_str),
        .host_dir_path = host_pkg_dir,
        .corex_req = corex_req_id,
        .links = links_id,
        .is_yanked = is_yanked,
        .has_feature_manifest = has_feat_manifest,
        .features = try arena.dupe(FeatureDecl, feat_decls.items),
        .dependencies = try arena.dupe(DependencySpec, deps_list.items),
        .expected_tree_blake3 = expected_tree,
        .expected_checksum = expected_cksum,
        .publisher_pub_key = pub_key,
        .signature = sig_bytes,
        .tlog_index = tlog_idx,
        .tlog_tree_size = tlog_size,
        .tlog_root = tlog_root,
        .tlog_proof = try arena.dupe([32]u8, proof_hashes.items),
        .tlog_leaf_override = tlog_leaf_ov,
        .obao_file_path = obao_path,
        .archive_file_path = archive_path,
    };
}

/// Probes sparse-index metadata files for `pkg_name` inside `base_index_dir` (NDJSON or directory scan of `<pkg>-<ver>/corex.toml`).
fn loadSparseIndexVersionsFromDir(
    allocator: std.mem.Allocator,
    io: std.Io,
    arena: *BumpArena,
    scratch_json_arena: *BumpArena,
    interner: *StringInterner,
    cfg_env: *const symbol_resolver.CfgEnv,
    base_dir: []const u8,
    pkg_name: []const u8,
    out_versions: *std.ArrayListUnmanaged(CandidateVersionMeta),
    sink: ?*DiagnosticSink,
) !bool {
    var rel_buf: [160]u8 = undefined;
    const sparse_rel = formatSparseIndexRelPath(pkg_name, &rel_buf) orelse return false;

    const cand_patterns: usize = 5;
    for (0..cand_patterns) |pat_idx| {
        var stack_path_buf: [512]u8 = undefined;
        var heap_cand_path: ?[]u8 = null;
        defer if (heap_cand_path) |hp| allocator.free(hp);

        const cand_file: []const u8 = switch (pat_idx) {
            0 => std.fmt.bufPrint(&stack_path_buf, "{s}/index/{s}", .{ base_dir, sparse_rel }) catch blk_p0: {
                const hp = try std.fmt.allocPrint(allocator, "{s}/index/{s}", .{ base_dir, sparse_rel });
                heap_cand_path = hp;
                break :blk_p0 hp;
            },
            1 => std.fmt.bufPrint(&stack_path_buf, "{s}/{s}", .{ base_dir, sparse_rel }) catch blk_p1: {
                const hp = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ base_dir, sparse_rel });
                heap_cand_path = hp;
                break :blk_p1 hp;
            },
            2 => std.fmt.bufPrint(&stack_path_buf, "{s}/index/{s}.json", .{ base_dir, pkg_name }) catch blk_p2: {
                const hp = try std.fmt.allocPrint(allocator, "{s}/index/{s}.json", .{ base_dir, pkg_name });
                heap_cand_path = hp;
                break :blk_p2 hp;
            },
            3 => std.fmt.bufPrint(&stack_path_buf, "{s}/{s}.json", .{ base_dir, pkg_name }) catch blk_p3: {
                const hp = try std.fmt.allocPrint(allocator, "{s}/{s}.json", .{ base_dir, pkg_name });
                heap_cand_path = hp;
                break :blk_p3 hp;
            },
            else => std.fmt.bufPrint(&stack_path_buf, "{s}/{s}.ndjson", .{ base_dir, pkg_name }) catch blk_p4: {
                const hp = try std.fmt.allocPrint(allocator, "{s}/{s}.ndjson", .{ base_dir, pkg_name });
                heap_cand_path = hp;
                break :blk_p4 hp;
            },
        };

        const raw_bytes = std.Io.Dir.cwd().readFileAlloc(
            io,
            cand_file,
            allocator,
            .limited(MAX_INDEX_FILE_BYTES + 1),
        ) catch continue;
        defer allocator.free(raw_bytes);
        if (raw_bytes.len > MAX_INDEX_FILE_BYTES) {
            if (sink) |diag_sink| {
                try diag_sink.emit(.{
                    .code = .e0013_invalid_manifest_or_pkg_name,
                    .severity = .err,
                    .message = "sparse registry index metadata file exceeds 8 MiB limit",
                });
            }
            return false;
        }

        defer scratch_json_arena.resetRetainingCapacity();

        var line_iter = std.mem.splitScalar(u8, raw_bytes, '\n');
        var has_parsed_any = false;
        while (line_iter.next()) |raw_line| {
            const trimmed = std.mem.trim(u8, raw_line, " \t\r");
            if (trimmed.len == 0 or trimmed[0] == '#') continue;
            const parsed_val = std.json.parseFromSliceLeaky(
                std.json.Value,
                scratch_json_arena.asAllocator(),
                trimmed,
                .{},
            ) catch continue;
            if (parsed_val == .object) {
                if (try parseSparseIndexJsonObject(allocator, arena, interner, base_dir, parsed_val.object)) |cand| {
                    try out_versions.append(allocator, cand);
                    has_parsed_any = true;
                }
            } else if (parsed_val == .array) {
                for (parsed_val.array.items) |elem| {
                    if (elem == .object) {
                        if (try parseSparseIndexJsonObject(allocator, arena, interner, base_dir, elem.object)) |cand| {
                            try out_versions.append(allocator, cand);
                            has_parsed_any = true;
                        }
                    }
                }
            }
        }
        if (has_parsed_any) return true;
    }

    // Fallback: scan `<base_dir>/packages/<pkg_name>-<ver>/corex.toml` or `<base_dir>/<pkg_name>-<ver>/corex.toml`:
    const scan_roots = [_][]u8{
        try std.fmt.allocPrint(allocator, "{s}/packages", .{base_dir}),
        try allocator.dupe(u8, base_dir),
    };
    defer for (scan_roots) |sr| allocator.free(sr);

    const prefix = try std.fmt.allocPrint(allocator, "{s}-", .{pkg_name});
    defer allocator.free(prefix);

    var has_dir_cands = false;
    for (scan_roots) |scan_root| {
        var dir_handle = std.Io.Dir.cwd().openDir(io, scan_root, .{ .iterate = true }) catch continue;
        defer dir_handle.close(io);
        var iter = dir_handle.iterate();
        while (try iter.next(io)) |entry| {
            if (entry.kind != .directory or !std.mem.startsWith(u8, entry.name, prefix)) continue;
            const ver_part = entry.name[prefix.len..];
            const parsed_ver = (try SemVer.parse(interner, ver_part)) orelse continue;
            const pkg_dir = try std.fmt.allocPrint(arena.asAllocator(), "{s}/{s}", .{ scan_root, entry.name });
            const toml_path = try std.fmt.allocPrint(allocator, "{s}/corex.toml", .{pkg_dir});
            defer allocator.free(toml_path);
            const toml_bytes = std.Io.Dir.cwd().readFileAlloc(
                io,
                toml_path,
                allocator,
                .limited(pkg_manifest.MAX_TOML_BYTES),
            ) catch continue;
            defer allocator.free(toml_bytes);

            var parsed_m = try pkg_manifest.parseManifest(
                allocator,
                arena,
                interner,
                .none,
                toml_bytes,
                cfg_env,
                null,
            );
            defer parsed_m.doc.deinit(allocator);
            const links_id = if (parsed_m.manifest.package) |pm| pm.links else .empty;
            const corex_id = if (parsed_m.manifest.package) |pm| pm.corex_req else .empty;
            var has_fm = parsed_m.manifest.features.len > 0;
            for (parsed_m.manifest.dependencies) |dep_item| {
                if (dep_item.is_optional) has_fm = true;
            }
            try out_versions.append(allocator, .{
                .version = parsed_ver,
                .source_kind = .sparse_registry,
                .source_uri = try interner.intern(DEFAULT_REGISTRY_URI),
                .host_dir_path = pkg_dir,
                .corex_req = corex_id,
                .links = links_id,
                .has_feature_manifest = has_fm,
                .features = parsed_m.manifest.features,
                .dependencies = parsed_m.manifest.dependencies,
            });
            has_dir_cands = true;
        }
        if (has_dir_cands) return true;
    }
    return false;
}

/// Resolves a Git reference (`rev`, `tag`, `branch`, or `HEAD`) directly from `.git` files on disk (`< 0.2 ms`).
fn resolveGitOidFromDotGitFiles(
    allocator: std.mem.Allocator,
    io: std.Io,
    repo_dir: []const u8,
    rev_kind: GitRevKind,
    rev_str: []const u8,
) !?[40]u8 {
    if (rev_kind == .rev and isHexGitOid40(rev_str)) {
        var out_oid: [40]u8 = undefined;
        @memcpy(&out_oid, rev_str[0..40]);
        for (&out_oid) |*ch| ch.* = std.ascii.toLower(ch.*);
        return out_oid;
    }

    const git_roots = [_][]u8{
        try std.fmt.allocPrint(allocator, "{s}/.git", .{repo_dir}),
        try allocator.dupe(u8, repo_dir),
    };
    defer for (git_roots) |gr| allocator.free(gr);

    for (git_roots) |git_dir| {
        const ref_rel: []u8 = switch (rev_kind) {
            .tag => try std.fmt.allocPrint(allocator, "refs/tags/{s}", .{rev_str}),
            .branch => try std.fmt.allocPrint(allocator, "refs/heads/{s}", .{rev_str}),
            .rev => try allocator.dupe(u8, rev_str),
            .default_head => blk_head: {
                const head_path = try std.fmt.allocPrint(allocator, "{s}/HEAD", .{git_dir});
                defer allocator.free(head_path);
                const head_bytes = std.Io.Dir.cwd().readFileAlloc(io, head_path, allocator, .limited(256)) catch continue;
                defer allocator.free(head_bytes);
                const trimmed_h = std.mem.trim(u8, head_bytes, " \t\r\n");
                if (isHexGitOid40(trimmed_h)) {
                    var direct_oid: [40]u8 = undefined;
                    @memcpy(&direct_oid, trimmed_h[0..40]);
                    for (&direct_oid) |*ch| ch.* = std.ascii.toLower(ch.*);
                    return direct_oid;
                }
                if (std.mem.startsWith(u8, trimmed_h, "ref:")) {
                    break :blk_head try allocator.dupe(u8, std.mem.trim(u8, trimmed_h[4..], " \t"));
                }
                continue;
            },
        };
        defer allocator.free(ref_rel);

        const loose_path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ git_dir, ref_rel });
        defer allocator.free(loose_path);
        if (std.Io.Dir.cwd().readFileAlloc(io, loose_path, allocator, .limited(128))) |ref_bytes| {
            defer allocator.free(ref_bytes);
            const trimmed_ref = std.mem.trim(u8, ref_bytes, " \t\r\n");
            if (isHexGitOid40(trimmed_ref)) {
                var out_oid: [40]u8 = undefined;
                @memcpy(&out_oid, trimmed_ref[0..40]);
                for (&out_oid) |*ch| ch.* = std.ascii.toLower(ch.*);
                return out_oid;
            }
        } else |_| {}

        const packed_path = try std.fmt.allocPrint(allocator, "{s}/packed-refs", .{git_dir});
        defer allocator.free(packed_path);
        if (std.Io.Dir.cwd().readFileAlloc(io, packed_path, allocator, .limited(512 * 1024))) |packed_bytes| {
            defer allocator.free(packed_bytes);
            var matched_oid: ?[40]u8 = null;
            var line_it = std.mem.splitScalar(u8, packed_bytes, '\n');
            while (line_it.next()) |line| {
                const trim_l = std.mem.trim(u8, line, " \t\r");
                if (trim_l.len == 0 or trim_l[0] == '#') continue;
                if (trim_l[0] == '^' and matched_oid != null and isHexGitOid40(trim_l[1..])) {
                    // Peeled annotated tag commit OID overrides tag object OID:
                    var peeled: [40]u8 = undefined;
                    @memcpy(&peeled, trim_l[1..41]);
                    for (&peeled) |*ch| ch.* = std.ascii.toLower(ch.*);
                    return peeled;
                }
                if (matched_oid != null) return matched_oid;
                if (trim_l.len > 41 and trim_l[40] == ' ' and isHexGitOid40(trim_l[0..40])) {
                    const ref_name = std.mem.trim(u8, trim_l[41..], " \t");
                    if (std.mem.eql(u8, ref_name, ref_rel)) {
                        var found_oid: [40]u8 = undefined;
                        @memcpy(&found_oid, trim_l[0..40]);
                        for (&found_oid) |*ch| ch.* = std.ascii.toLower(ch.*);
                        matched_oid = found_oid;
                    }
                }
            }
            if (matched_oid != null) return matched_oid;
        } else |_| {}
    }
    return null;
}

/// Maps a `git = "…"` URL to a local repository path (supporting `file://`, relative/abs paths, and local fixture mirrors).
fn resolveLocalGitRepoPathAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    workspace_root_dir: []const u8,
    local_registry_dir: ?[]const u8,
    raw_url: []const u8,
) !?[]u8 {
    const stripped = if (std.mem.startsWith(u8, raw_url, "git+")) raw_url[4..] else raw_url;
    if (std.mem.startsWith(u8, stripped, "file://")) {
        const after_scheme = stripped[7..];
        if (std.Io.Dir.cwd().openDir(io, after_scheme, .{})) |dir_h| {
            var mut_d = dir_h;
            mut_d.close(io);
            return try allocator.dupe(u8, after_scheme);
        } else |_| {}
    }
    if (std.fs.path.isAbsolute(stripped)) {
        if (std.Io.Dir.cwd().openDir(io, stripped, .{})) |dir_h| {
            var mut_d = dir_h;
            mut_d.close(io);
            return try allocator.dupe(u8, stripped);
        } else |_| {}
    }
    const rel_ws = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ workspace_root_dir, stripped });
    if (std.Io.Dir.cwd().openDir(io, rel_ws, .{})) |dir_h| {
        var mut_d = dir_h;
        mut_d.close(io);
        return rel_ws;
    } else |_| {
        allocator.free(rel_ws);
    }

    if (local_registry_dir) |reg_dir| {
        const base_name_raw = if (std.mem.lastIndexOfScalar(u8, stripped, '/')) |sl| stripped[sl + 1 ..] else stripped;
        const base_name = if (std.mem.endsWith(u8, base_name_raw, ".git"))
            base_name_raw[0 .. base_name_raw.len - 4]
        else
            base_name_raw;
        const mirror_cands = [_][]u8{
            try std.fmt.allocPrint(allocator, "{s}/git/{s}", .{ reg_dir, base_name }),
            try std.fmt.allocPrint(allocator, "{s}/git/{s}.git", .{ reg_dir, base_name }),
        };
        defer for (mirror_cands) |mc| allocator.free(mc);
        for (mirror_cands) |mc_path| {
            if (std.Io.Dir.cwd().openDir(io, mc_path, .{})) |dir_h| {
                var mut_d = dir_h;
                mut_d.close(io);
                return try allocator.dupe(u8, mc_path);
            } else |_| {}
        }
    }
    return null;
}

/// Formats canonical `"git+<url>[?tag=…|?branch=…|?rev=…]#<40-hex-oid>"` for `corex.lock`.
fn formatCanonicalGitSourceUriAlloc(
    arena: *BumpArena,
    raw_url: []const u8,
    rev_kind: GitRevKind,
    rev_val: []const u8,
    oid_hex: *const [40]u8,
) ![]const u8 {
    const clean_url = if (std.mem.startsWith(u8, raw_url, "git+")) raw_url[4..] else raw_url;
    return switch (rev_kind) {
        .default_head => try std.fmt.allocPrint(arena.asAllocator(), "git+{s}#{s}", .{ clean_url, oid_hex }),
        .tag => try std.fmt.allocPrint(arena.asAllocator(), "git+{s}?tag={s}#{s}", .{ clean_url, rev_val, oid_hex }),
        .branch => try std.fmt.allocPrint(arena.asAllocator(), "git+{s}?branch={s}#{s}", .{ clean_url, rev_val, oid_hex }),
        .rev => try std.fmt.allocPrint(arena.asAllocator(), "git+{s}?rev={s}#{s}", .{ clean_url, rev_val, oid_hex }),
    };
}

// ---------- Target `@cfg` & Security Policy Helpers -----------

/// Computes the effective `mir_sast.PackageCapPolicy` for an external or workspace dependency node.
fn buildNodeCapPolicy(
    arena: *BumpArena,
    interner: *const StringInterner,
    root_security: SecurityPolicy,
    pkg_kebab_id: StringId,
    pkg_display: []const u8,
    is_third_party: bool,
    is_dev_only: bool,
    incoming_allow_union: ?EffectCapabilityMask,
    incoming_deny_union: EffectCapabilityMask,
    locked_max_caps: ?EffectCapabilityMask,
    policy_span: Span,
) !mir_sast.PackageCapPolicy {
    if (!is_third_party) {
        return .{
            .package_name = try arena.dupe(u8, pkg_display),
            .policy_span = policy_span,
            .allowed_caps = EffectCapabilityMask.fromBits(0x0FFF),
            .forbid_global_caps = .EMPTY,
            .is_third_party_dependency = false,
            .is_warning_ambient_dead_caps = false,
            .enforcement_scope = if (root_security.enforcement_scope == .reachable) .reachable else .surface,
        };
    }

    var base_allow: EffectCapabilityMask = switch (root_security.default_dep_policy) {
        .zero_trust => root_security.default_allow_caps orelse .EMPTY,
        .trust_on_first_lock => root_security.default_allow_caps orelse
            (locked_max_caps orelse EffectCapabilityMask.fromBits(EffectCapabilityMask.LOCKFILE_CAP_BITS)),
        .allow_all => root_security.default_allow_caps orelse
            EffectCapabilityMask.fromBits(EffectCapabilityMask.LOCKFILE_CAP_BITS),
    };
    if (is_dev_only) {
        if (root_security.dev_default_allow_caps) |dev_allow| {
            base_allow = dev_allow;
        }
    }

    var explicit_allow: ?EffectCapabilityMask = incoming_allow_union;
    var extra_deny = incoming_deny_union;
    if (is_dev_only) {
        extra_deny = extra_deny.unionWith(root_security.dev_deny_caps);
    }

    for (root_security.package_overrides) |pkg_ov| {
        if (pkg_ov.package_kebab == pkg_kebab_id or
            std.mem.eql(u8, interner.get(pkg_ov.package_kebab), interner.get(pkg_kebab_id)))
        {
            if (pkg_ov.allow_caps) |ov_allow| {
                explicit_allow = if (explicit_allow) |prev| prev.unionWith(ov_allow) else ov_allow;
            }
            extra_deny = extra_deny.unionWith(pkg_ov.deny_caps);
        }
    }

    const global_forbid = root_security.forbid_global_caps
        .unionWith(root_security.deny_caps)
        .unionWith(extra_deny);

    // Always permit local/pure computation effects (`alloc`, `may_panic`, `blocking_sync`, `indirect_opaque`)
    // unless restricted by function-level `@no_*`; `[security]` gates OS/supply-chain `LOCKFILE_CAP_BITS`:
    const non_os_bits: u16 = 0x0FFF & ~EffectCapabilityMask.LOCKFILE_CAP_BITS;
    const allowed_with_non_os = EffectCapabilityMask.fromBits(base_allow.asBits() | non_os_bits);
    const explicit_with_non_os: ?EffectCapabilityMask = if (explicit_allow) |exp|
        EffectCapabilityMask.fromBits(exp.asBits() | non_os_bits)
    else
        null;
    const locked_with_non_os: ?EffectCapabilityMask = if (locked_max_caps) |lck|
        EffectCapabilityMask.fromBits(lck.asBits() | non_os_bits)
    else
        null;

    return .{
        .package_name = try arena.dupe(u8, pkg_display),
        .policy_span = policy_span,
        .allowed_caps = allowed_with_non_os,
        .allow_caps = explicit_with_non_os,
        .locked_caps = locked_with_non_os,
        .forbid_global_caps = global_forbid,
        .is_third_party_dependency = true,
        .is_warning_ambient_dead_caps = root_security.is_warn_ambient_dead_caps,
        .enforcement_scope = if (root_security.enforcement_scope == .reachable) .reachable else .surface,
    };
}

// ---------- Solver Context (`MVS` + `PubGrub CDCL`) -----------

/// Stateful solver context coordinating candidate loading, Tier-1 `Bounded-MVS`, and Tier-2 `PubGrub CDCL`.
const SolverContext = struct {
    /// General-purpose backing allocator for temporary hash maps and worklists.
    allocator: std.mem.Allocator,
    /// Output arena transferred to `ResolvedPackageGraph` on success.
    graph_arena: *BumpArena,
    /// Shared string interner.
    interner: *StringInterner,
    /// Shared VFS source map.
    vfs: *vfs_sourcemap.VfsSourceMap,
    /// Global CAS store handle (`<corex_home>/cache/blake3`).
    cache: *pkg_cache.PkgCache,
    /// Workspace manifest bundle.
    bundle: *const WorkspaceManifestBundle,
    /// Optional existing `corex.lock`.
    existing_lock: ?*const Lockfile,
    /// Resolution options.
    options: ResolveOptions,
    /// Active target `@cfg` environment.
    base_cfg_env: symbol_resolver.CfgEnv,
    /// Effective local sparse-registry directory (`options.local_registry_dir` or `$COREX_REGISTRY_DIR`).
    effective_registry_dir: ?[]const u8,
    /// Diagnostic sink.
    sink: *DiagnosticSink,
    /// Dense array of `SeriesEntry` records (`0` = primary root).
    series_list: std.ArrayListUnmanaged(SeriesEntry) = .empty,
    /// $O(1)$ map `SeriesKey -> series_id`.
    series_map: std.AutoHashMapUnmanaged(SeriesKey, u32) = .empty,
    /// Cached registry versions per `pkg_name_sym` so each sparse-index file is parsed at most once.
    registry_index_cache: std.AutoHashMapUnmanaged(SymbolId, []CandidateVersionMeta) = .empty,
    /// Active `[patch]` overrides keyed by `package_kebab` `SymbolId`.
    patch_map: std.AutoHashMapUnmanaged(SymbolId, PatchSpec) = .empty,
    /// Workspace members keyed by `package_kebab` `SymbolId`.
    workspace_pkg_map: std.AutoHashMapUnmanaged(SymbolId, u32) = .empty,
    /// Reusable bump arena for NDJSON sparse-index parsing, reset per index file.
    scratch_json_arena: BumpArena,
    /// Set of `SymbolId`s where a fetch or integrity error (`E0014`/`E0015`/`E0016`) was already emitted.
    has_aborted_error: bool = false,

    /// Releases solver-temporary containers (keeping `graph_arena` intact).
    fn deinit(self: *SolverContext) void {
        for (self.series_list.items) |*entry| {
            entry.candidates.deinit(self.allocator);
            entry.feature_ids.deinit(self.allocator);
            entry.feature_to_bit.deinit(self.allocator);
        }
        self.series_list.deinit(self.allocator);
        self.series_map.deinit(self.allocator);
        self.registry_index_cache.deinit(self.allocator);
        self.patch_map.deinit(self.allocator);
        self.workspace_pkg_map.deinit(self.allocator);
        self.scratch_json_arena.deinit();
    }

    /// Ensures all registry versions of `pkg_kebab_sym` are loaded and cached in `registry_index_cache`.
    fn ensureRegistryCandidatesLoaded(
        self: *SolverContext,
        pkg_kebab_sym: SymbolId,
        req_span: Span,
    ) ![]CandidateVersionMeta {
        if (self.registry_index_cache.get(pkg_kebab_sym)) |cached| return cached;

        const pkg_name = self.interner.get(pkg_kebab_sym);
        var raw_versions: std.ArrayListUnmanaged(CandidateVersionMeta) = .empty;
        defer raw_versions.deinit(self.allocator);

        // [1] First probe `<corex_home>/cache/blake3/index/default` (always valid even in `--offline` mode):
        var cached_idx_buf: [512]u8 = undefined;
        var heap_cached_idx: ?[]u8 = null;
        defer if (heap_cached_idx) |hc| self.allocator.free(hc);
        const cached_index_dir = std.fmt.bufPrint(
            &cached_idx_buf,
            "{s}/index/default",
            .{self.cache.cas_root},
        ) catch blk_cidx: {
            const allocated_idx = try std.fmt.allocPrint(self.allocator, "{s}/index/default", .{self.cache.cas_root});
            heap_cached_idx = allocated_idx;
            break :blk_cidx allocated_idx;
        };
        const has_cached_idx = try loadSparseIndexVersionsFromDir(
            self.allocator,
            self.options.io,
            self.graph_arena,
            &self.scratch_json_arena,
            self.interner,
            &self.base_cfg_env,
            cached_index_dir,
            pkg_name,
            &raw_versions,
            self.sink,
        );
        var has_found = has_cached_idx;

        // [2] Also synthesize candidates from `existing_lock` when cached `.cxtree` exists in `PkgCache`:
        if (!has_found and self.existing_lock != null) {
            for (self.existing_lock.?.packages) |lock_pkg| {
                if (lock_pkg.name != pkg_kebab_sym and
                    !std.mem.eql(u8, self.interner.get(lock_pkg.name), pkg_name))
                {
                    continue;
                }
                const src_str = self.interner.get(lock_pkg.source);
                if (!std.mem.startsWith(u8, src_str, "registry+")) continue;

                // Verify `.cxtree` is present in `COREX_HOME` (emitting `E0016` if offline & missing, `E0015` if corrupt):
                const cxtree_bytes = self.cache.readVerifiedCxTreeAlloc(
                    self.options.io,
                    lock_pkg.tree_hash,
                    self.sink,
                    req_span,
                ) catch |err| switch (err) {
                    error.CacheIntegrityMismatch => {
                        self.has_aborted_error = true;
                        return &.{};
                    },
                    else => {
                        if (self.options.is_offline or self.options.is_frozen) {
                            try self.sink.emit(.{
                                .code = .e0016_offline_or_fetch_failed,
                                .severity = .err,
                                .primary_span = req_span,
                                .message = try std.fmt.allocPrint(
                                    self.sink.arena.asAllocator(),
                                    "cached `.cxtree` for locked package `{s}` is missing from `COREX_HOME` in `--offline` mode",
                                    .{pkg_name},
                                ),
                            });
                            self.has_aborted_error = true;
                            return &.{};
                        }
                        continue;
                    },
                };
                defer self.allocator.free(cxtree_bytes);

                // Parse embedded `corex.toml` from `.cxtree` blobs if present so transitive deps/features are exact:
                var parsed_deps: []const DependencySpec = &.{};
                var parsed_feats: []const FeatureDecl = &.{};
                var has_fm = false;
                var has_embedded_toml = false;
                if (vfs_sourcemap.validateCxTreeBytes(self.allocator, cxtree_bytes)) |view| {
                    for (view.entries) |t_entry| {
                        const rel_p = view.asEntryPath(t_entry);
                        if (std.mem.eql(u8, rel_p, "corex.toml")) {
                            const toml_blob = self.cache.readVerifiedBlobAlloc(
                                self.options.io,
                                t_entry.file_blake3,
                                self.sink,
                                req_span,
                            ) catch |b_err| {
                                if (b_err == error.CacheIntegrityMismatch) {
                                    self.has_aborted_error = true;
                                    return &.{};
                                }
                                break;
                            };
                            defer self.allocator.free(toml_blob);
                            var pm = try pkg_manifest.parseManifest(
                                self.allocator,
                                self.graph_arena,
                                self.interner,
                                .none,
                                toml_blob,
                                &self.base_cfg_env,
                                null,
                            );
                            defer pm.doc.deinit(self.allocator);
                            parsed_deps = pm.manifest.dependencies;
                            parsed_feats = pm.manifest.features;
                            has_fm = parsed_feats.len > 0;
                            for (parsed_deps) |d_item| {
                                if (d_item.is_optional) has_fm = true;
                            }
                            has_embedded_toml = true;
                            break;
                        }
                    }
                } else |_| {}

                if (!has_embedded_toml) {
                    if (lock_pkg.features.len > 0) {
                        const synth_feats = try self.graph_arena.allocSlice(FeatureDecl, lock_pkg.features.len);
                        for (lock_pkg.features, 0..) |feat_id, feat_idx| {
                            synth_feats[feat_idx] = .{ .name = feat_id };
                        }
                        parsed_feats = synth_feats;
                        has_fm = true;
                    }
                    if (lock_pkg.dependencies.len > 0) {
                        var synth_deps: std.ArrayListUnmanaged(DependencySpec) = .empty;
                        defer synth_deps.deinit(self.allocator);
                        for (lock_pkg.dependencies) |dep_ref_id| {
                            const dep_ref = self.interner.get(dep_ref_id);
                            const sp1 = std.mem.indexOfScalar(u8, dep_ref, ' ') orelse continue;
                            const dep_name = dep_ref[0..sp1];
                            const after_name = dep_ref[sp1 + 1 ..];
                            const sp2 = std.mem.indexOfScalar(u8, after_name, ' ') orelse continue;
                            const dep_ver_str = after_name[0..sp2];
                            const src_part = after_name[sp2 + 1 ..];
                            if (src_part.len < 3 or src_part[0] != '(' or src_part[src_part.len - 1] != ')') continue;
                            const dep_src_uri = src_part[1 .. src_part.len - 1];
                            if (!std.mem.startsWith(u8, dep_src_uri, "registry+")) continue;

                            var exact_req_buf: [96]u8 = undefined;
                            const exact_req_str = std.fmt.bufPrint(&exact_req_buf, "={s}", .{dep_ver_str}) catch continue;
                            const dep_req = (try VersionReq.parse(self.interner, exact_req_str)) orelse continue;
                            if (!pkg_manifest.isValidPackageNameKebab(dep_name)) continue;
                            var snake_buf: [pkg_manifest.MAX_PKG_NAME_BYTES]u8 = undefined;
                            for (dep_name, 0..) |ch_byte, i| {
                                snake_buf[i] = if (ch_byte == '-') '_' else ch_byte;
                            }
                            const dep_kebab_id = try self.interner.intern(dep_name);
                            const dep_snake_id = try self.interner.intern(snake_buf[0..dep_name.len]);
                            try synth_deps.append(self.allocator, .{
                                .alias_kebab = dep_kebab_id,
                                .module_snake = dep_snake_id,
                                .package_kebab = dep_kebab_id,
                                .kind = .normal,
                                .source = .{ .registry = dep_req },
                            });
                        }
                        parsed_deps = try self.graph_arena.dupe(DependencySpec, synth_deps.items);
                    }
                }

                try raw_versions.append(self.allocator, .{
                    .version = lock_pkg.version,
                    .source_kind = .sparse_registry,
                    .source_uri = try self.interner.intern(DEFAULT_REGISTRY_URI),
                    .links = lock_pkg.links,
                    .has_feature_manifest = has_fm,
                    .features = parsed_feats,
                    .dependencies = parsed_deps,
                    .expected_tree_blake3 = lock_pkg.tree_hash,
                    .expected_checksum = lock_pkg.checksum,
                    .signature = lock_pkg.signature,
                    .tlog_index = lock_pkg.tlog_index,
                });
                has_found = true;
            }
        }

        // [3] When online (`!is_offline` and `!is_frozen`), query `effective_registry_dir` for uncached/newer versions:
        if (!self.options.is_offline and !self.options.is_frozen) {
            if (self.effective_registry_dir) |reg_dir| {
                if (!has_found) {
                    has_found = try loadSparseIndexVersionsFromDir(
                        self.allocator,
                        self.options.io,
                        self.graph_arena,
                        &self.scratch_json_arena,
                        self.interner,
                        &self.base_cfg_env,
                        reg_dir,
                        pkg_name,
                        &raw_versions,
                        self.sink,
                    );
                } else if (!self.options.is_locked and !has_cached_idx) {
                    var extra_versions: std.ArrayListUnmanaged(CandidateVersionMeta) = .empty;
                    defer extra_versions.deinit(self.allocator);
                    if (try loadSparseIndexVersionsFromDir(
                        self.allocator,
                        self.options.io,
                        self.graph_arena,
                        &self.scratch_json_arena,
                        self.interner,
                        &self.base_cfg_env,
                        reg_dir,
                        pkg_name,
                        &extra_versions,
                        self.sink,
                    )) {
                        for (extra_versions.items) |extra_cand| {
                            var is_already_present = false;
                            for (raw_versions.items) |*existing_cand| {
                                if (SemVer.eql(existing_cand.version, extra_cand.version, self.interner)) {
                                    if (!existing_cand.has_feature_manifest and extra_cand.has_feature_manifest) {
                                        existing_cand.has_feature_manifest = true;
                                        existing_cand.features = extra_cand.features;
                                        existing_cand.dependencies = extra_cand.dependencies;
                                    }
                                    is_already_present = true;
                                    break;
                                }
                            }
                            if (!is_already_present) {
                                try raw_versions.append(self.allocator, extra_cand);
                            }
                        }
                    }
                }
            }
        } else if (!has_found) {
            try self.sink.emit(.{
                .code = .e0016_offline_or_fetch_failed,
                .severity = .err,
                .primary_span = req_span,
                .message = try std.fmt.allocPrint(
                    self.sink.arena.asAllocator(),
                    "cannot fetch uncached package `{s}` while `--offline` / `--frozen` is active",
                    .{pkg_name},
                ),
                .notes = &.{"help: run `corex build` online first or vendor dependencies into `COREX_HOME`"},
            });
            self.has_aborted_error = true;
            return &.{};
        }

        if (raw_versions.items.len > 1) {
            std.mem.sort(CandidateVersionMeta, raw_versions.items, self.interner, struct {
                /// Orders candidate versions strictly ascending by `SemVer.compare` (`DR-11` §3.2).
                fn lessThan(int_ptr: *const StringInterner, lhs: CandidateVersionMeta, rhs: CandidateVersionMeta) bool {
                    return SemVer.compare(lhs.version, rhs.version, int_ptr) == .lt;
                }
            }.lessThan);
        }

        const owned_slice = try self.graph_arena.dupe(CandidateVersionMeta, raw_versions.items);
        try self.registry_index_cache.put(self.allocator, pkg_kebab_sym, owned_slice);
        return owned_slice;
    }

    /// Gets or creates a `SeriesEntry` for `key`, seeding its candidate versions in ascending order.
    fn getOrCreateSeries(
        self: *SolverContext,
        key: SeriesKey,
        dep_source: DepSourceSpec,
        declaring_dir: []const u8,
        req_span: Span,
    ) !u32 {
        if (self.series_map.get(key)) |existing_id| return existing_id;

        const new_id: u32 = @intCast(self.series_list.items.len);
        var entry = SeriesEntry{
            .series_id = new_id,
            .key = key,
        };

        switch (key.source_tag) {
            SOURCE_TAG_WORKSPACE => {
                if (self.workspace_pkg_map.get(key.pkg_name_sym)) |mem_idx| {
                    const ws_mem = self.bundle.members[mem_idx];
                    const pkg_meta = ws_mem.manifest.package.?;
                    var has_fm = ws_mem.manifest.features.len > 0;
                    for (ws_mem.manifest.dependencies) |d_item| {
                        if (d_item.is_optional) has_fm = true;
                    }
                    const ws_uri = try std.fmt.allocPrint(self.graph_arena.asAllocator(), "path+file://{s}", .{ws_mem.rel_dir});
                    try entry.candidates.append(self.allocator, .{
                        .version = pkg_meta.version,
                        .source_kind = .workspace_member,
                        .source_uri = try self.interner.intern(ws_uri),
                        .host_dir_path = ws_mem.abs_dir,
                        .corex_req = pkg_meta.corex_req,
                        .links = pkg_meta.links,
                        .has_feature_manifest = has_fm,
                        .features = ws_mem.manifest.features,
                        .dependencies = ws_mem.manifest.dependencies,
                        .manifest_span = Span.init(ws_mem.manifest.file_id, 0, 0),
                    });
                }
            },
            SOURCE_TAG_PATH => {
                const rel_str = self.interner.get(dep_source.path.rel_path);
                const resolved_dir = if (std.fs.path.isAbsolute(rel_str))
                    try self.graph_arena.dupe(u8, rel_str)
                else
                    try std.fmt.allocPrint(self.graph_arena.asAllocator(), "{s}/{s}", .{ declaring_dir, rel_str });
                const toml_path = try std.fmt.allocPrint(self.allocator, "{s}/corex.toml", .{resolved_dir});
                defer self.allocator.free(toml_path);

                const toml_bytes = std.Io.Dir.cwd().readFileAlloc(
                    self.options.io,
                    toml_path,
                    self.allocator,
                    .limited(pkg_manifest.MAX_TOML_BYTES),
                ) catch {
                    try self.sink.emit(.{
                        .code = .e0016_offline_or_fetch_failed,
                        .severity = .err,
                        .primary_span = req_span,
                        .message = try std.fmt.allocPrint(
                            self.sink.arena.asAllocator(),
                            "path dependency `{s}` is missing `corex.toml` at `{s}`",
                            .{ self.interner.get(key.pkg_name_sym), toml_path },
                        ),
                    });
                    self.has_aborted_error = true;
                    try self.series_list.append(self.allocator, entry);
                    try self.series_map.put(self.allocator, key, new_id);
                    return new_id;
                };
                defer self.allocator.free(toml_bytes);

                const path_fid = try self.vfs.setOverlay(toml_path, toml_bytes, .root);
                _ = try self.vfs.getLineIndex(path_fid);
                var parsed_p = try pkg_manifest.parseManifest(
                    self.allocator,
                    self.graph_arena,
                    self.interner,
                    path_fid,
                    toml_bytes,
                    &self.base_cfg_env,
                    self.sink,
                );
                defer parsed_p.doc.deinit(self.allocator);
                if (parsed_p.manifest.package) |pkg_meta| {
                    var has_fm = parsed_p.manifest.features.len > 0;
                    for (parsed_p.manifest.dependencies) |d_item| {
                        if (d_item.is_optional) has_fm = true;
                    }
                    const path_uri = try std.fmt.allocPrint(self.graph_arena.asAllocator(), "path+file://{s}", .{rel_str});
                    try entry.candidates.append(self.allocator, .{
                        .version = pkg_meta.version,
                        .source_kind = .local_path,
                        .source_uri = try self.interner.intern(path_uri),
                        .host_dir_path = resolved_dir,
                        .corex_req = pkg_meta.corex_req,
                        .links = pkg_meta.links,
                        .has_feature_manifest = has_fm,
                        .features = parsed_p.manifest.features,
                        .dependencies = parsed_p.manifest.dependencies,
                        .manifest_span = Span.init(path_fid, 0, 0),
                    });
                }
            },
            SOURCE_TAG_GIT => {
                const git_spec = dep_source.git;
                const raw_url = self.interner.get(git_spec.url);
                const rev_str = self.interner.get(git_spec.rev_value);
                const pkg_name = self.interner.get(key.pkg_name_sym);

                // Check `existing_lock` first for a pinned `"git+…#<40-hex-oid>"` already cached in `PkgCache`:
                var is_loaded_from_lock = false;
                if (self.existing_lock) |lock_doc| {
                    const clean_url = if (std.mem.startsWith(u8, raw_url, "git+")) raw_url[4..] else raw_url;
                    for (lock_doc.packages) |lp| {
                        const lp_src = self.interner.get(lp.source);
                        if (!std.mem.startsWith(u8, lp_src, "git+")) continue;
                        if (std.mem.indexOf(u8, lp_src, clean_url) == null) continue;
                        if (self.cache.readVerifiedCxTreeAlloc(self.options.io, lp.tree_hash, self.sink, req_span)) |tree_buf| {
                            defer self.allocator.free(tree_buf);
                            var parsed_deps: []const DependencySpec = &.{};
                            var parsed_feats: []const FeatureDecl = &.{};
                            var has_fm = false;
                            if (vfs_sourcemap.validateCxTreeBytes(self.allocator, tree_buf)) |view| {
                                for (view.entries) |te| {
                                    const rp = view.asEntryPath(te);
                                    if (std.mem.eql(u8, rp, "corex.toml")) {
                                        if (self.cache.readVerifiedBlobAlloc(self.options.io, te.file_blake3, self.sink, req_span)) |tb| {
                                            defer self.allocator.free(tb);
                                            var pm = try pkg_manifest.parseManifest(
                                                self.allocator,
                                                self.graph_arena,
                                                self.interner,
                                                .none,
                                                tb,
                                                &self.base_cfg_env,
                                                null,
                                            );
                                            defer pm.doc.deinit(self.allocator);
                                            parsed_deps = pm.manifest.dependencies;
                                            parsed_feats = pm.manifest.features;
                                            has_fm = parsed_feats.len > 0;
                                        } else |_| {}
                                        break;
                                    }
                                }
                            } else |_| {}
                            try entry.candidates.append(self.allocator, .{
                                .version = lp.version,
                                .source_kind = .git_pinned,
                                .source_uri = lp.source,
                                .links = lp.links,
                                .has_feature_manifest = has_fm,
                                .features = parsed_feats,
                                .dependencies = parsed_deps,
                                .expected_tree_blake3 = lp.tree_hash,
                            });
                            is_loaded_from_lock = true;
                            break;
                        } else |c_err| {
                            if (c_err == error.CacheIntegrityMismatch) {
                                self.has_aborted_error = true;
                                break;
                            }
                        }
                    }
                }

                if (!is_loaded_from_lock and !self.has_aborted_error) {
                    if (self.options.is_offline or self.options.is_frozen) {
                        try self.sink.emit(.{
                            .code = .e0016_offline_or_fetch_failed,
                            .severity = .err,
                            .primary_span = req_span,
                            .message = try std.fmt.allocPrint(
                                self.sink.arena.asAllocator(),
                                "cannot fetch uncached Git dependency `{s}` (`{s}`) in `--offline` / `--frozen` mode",
                                .{ pkg_name, raw_url },
                            ),
                        });
                        self.has_aborted_error = true;
                    } else {
                        const repo_dir_opt = try resolveLocalGitRepoPathAlloc(
                            self.allocator,
                            self.options.io,
                            self.bundle.workspace_root_dir,
                            self.effective_registry_dir,
                            raw_url,
                        );
                        defer if (repo_dir_opt) |rd| self.allocator.free(rd);

                        if (repo_dir_opt) |repo_dir| {
                            var resolved_oid_opt = try resolveGitOidFromDotGitFiles(
                                self.allocator,
                                self.options.io,
                                repo_dir,
                                git_spec.rev_kind,
                                rev_str,
                            );
                            if (resolved_oid_opt == null) {
                                const target_ref = if (git_spec.rev_kind == .default_head) "HEAD" else rev_str;
                                const rev_spec = try std.fmt.allocPrint(self.allocator, "{s}^{{commit}}", .{target_ref});
                                defer self.allocator.free(rev_spec);
                                if (std.process.run(self.allocator, self.options.io, .{
                                    .argv = &.{ "git", "-C", repo_dir, "rev-parse", rev_spec },
                                    .environ_map = self.options.environ_map,
                                })) |git_res| {
                                    defer self.allocator.free(git_res.stdout);
                                    defer self.allocator.free(git_res.stderr);
                                    const out_trim = std.mem.trim(u8, git_res.stdout, " \t\r\n");
                                    if (git_res.term == .exited and git_res.term.exited == 0 and isHexGitOid40(out_trim)) {
                                        var sub_oid: [40]u8 = undefined;
                                        @memcpy(&sub_oid, out_trim[0..40]);
                                        for (&sub_oid) |*ch| ch.* = std.ascii.toLower(ch.*);
                                        resolved_oid_opt = sub_oid;
                                    }
                                } else |_| {}
                            }

                            if (resolved_oid_opt) |oid_hex| {
                                var tree_hash: [32]u8 = @splat(0);
                                var parsed_ver: SemVer = .{ .major = 0, .minor = 1, .patch = 0 };
                                var parsed_links: StringId = .empty;
                                var parsed_corex: StringId = .empty;
                                var parsed_feats: []const FeatureDecl = &.{};
                                var parsed_deps: []const DependencySpec = &.{};
                                var has_fm = false;
                                var has_ingested = false;

                                // Prefer `git archive --format=tar <oid>` so tags/branches/commits read exact snapshot:
                                if (std.process.run(self.allocator, self.options.io, .{
                                    .argv = &.{ "git", "-C", repo_dir, "archive", "--format=tar", &oid_hex },
                                    .environ_map = self.options.environ_map,
                                    .stdout_limit = .limited(32 * 1024 * 1024),
                                    .stderr_limit = .limited(1024 * 1024),
                                })) |arch_res| {
                                    defer self.allocator.free(arch_res.stdout);
                                    defer self.allocator.free(arch_res.stderr);
                                    if (arch_res.term == .exited and arch_res.term.exited == 0 and arch_res.stdout.len >= 512) {
                                        if (ingestTarArchiveIntoCache(
                                            self.allocator,
                                            self.options.io,
                                            self.graph_arena,
                                            pkg_name,
                                            arch_res.stdout,
                                            self.cache,
                                            self.sink,
                                            req_span,
                                        )) |tar_ingested| {
                                            defer if (tar_ingested.manifest_bytes) |mb| self.allocator.free(mb);
                                            tree_hash = tar_ingested.tree_blake3;
                                            has_ingested = true;
                                            if (tar_ingested.manifest_bytes) |toml_b| {
                                                var pm = try pkg_manifest.parseManifest(
                                                    self.allocator,
                                                    self.graph_arena,
                                                    self.interner,
                                                    .none,
                                                    toml_b,
                                                    &self.base_cfg_env,
                                                    self.sink,
                                                );
                                                defer pm.doc.deinit(self.allocator);
                                                if (pm.manifest.package) |pkg_m| {
                                                    parsed_ver = pkg_m.version;
                                                    parsed_links = pkg_m.links;
                                                    parsed_corex = pkg_m.corex_req;
                                                }
                                                parsed_feats = pm.manifest.features;
                                                parsed_deps = pm.manifest.dependencies;
                                                has_fm = parsed_feats.len > 0;
                                            }
                                        } else |tar_err| {
                                            if (tar_err == error.CacheIntegrityMismatch) {
                                                self.has_aborted_error = true;
                                                try self.series_list.append(self.allocator, entry);
                                                try self.series_map.put(self.allocator, key, new_id);
                                                return new_id;
                                            }
                                            return tar_err;
                                        }
                                    }
                                } else |_| {}

                                // Fallback when `git` binary is unavailable and `repo_dir` is a checked-out worktree:
                                if (!has_ingested) {
                                    const wt_toml_path = try std.fmt.allocPrint(self.allocator, "{s}/corex.toml", .{repo_dir});
                                    defer self.allocator.free(wt_toml_path);
                                    if (std.Io.Dir.cwd().readFileAlloc(
                                        self.options.io,
                                        wt_toml_path,
                                        self.allocator,
                                        .limited(pkg_manifest.MAX_TOML_BYTES),
                                    )) |wt_toml| {
                                        defer self.allocator.free(wt_toml);
                                        var pm = try pkg_manifest.parseManifest(
                                            self.allocator,
                                            self.graph_arena,
                                            self.interner,
                                            .none,
                                            wt_toml,
                                            &self.base_cfg_env,
                                            self.sink,
                                        );
                                        defer pm.doc.deinit(self.allocator);
                                        if (pm.manifest.package) |pkg_m| {
                                            parsed_ver = pkg_m.version;
                                            parsed_links = pkg_m.links;
                                            parsed_corex = pkg_m.corex_req;
                                        }
                                        parsed_feats = pm.manifest.features;
                                        parsed_deps = pm.manifest.dependencies;
                                        has_fm = parsed_feats.len > 0;
                                        const ing = try ingestHostDirectoryAsCxTree(
                                            self.allocator,
                                            self.options.io,
                                            self.graph_arena,
                                            self.interner,
                                            pkg_name,
                                            repo_dir,
                                            &pm.manifest,
                                            self.cache,
                                            true,
                                            self.sink,
                                            req_span,
                                        );
                                        self.allocator.free(ing.cxtree_bytes);
                                        tree_hash = ing.tree_blake3;
                                        has_ingested = true;
                                    } else |_| {}
                                }

                                if (has_ingested) {
                                    const canon_uri = try formatCanonicalGitSourceUriAlloc(
                                        self.graph_arena,
                                        raw_url,
                                        git_spec.rev_kind,
                                        rev_str,
                                        &oid_hex,
                                    );
                                    try entry.candidates.append(self.allocator, .{
                                        .version = parsed_ver,
                                        .source_kind = .git_pinned,
                                        .source_uri = try self.interner.intern(canon_uri),
                                        .corex_req = parsed_corex,
                                        .links = parsed_links,
                                        .has_feature_manifest = has_fm,
                                        .features = parsed_feats,
                                        .dependencies = parsed_deps,
                                        .expected_tree_blake3 = tree_hash,
                                    });
                                } else {
                                    try self.sink.emit(.{
                                        .code = .e0016_offline_or_fetch_failed,
                                        .severity = .err,
                                        .primary_span = req_span,
                                        .message = try std.fmt.allocPrint(
                                            self.sink.arena.asAllocator(),
                                            "failed to materialize Git tree `{s}` from `{s}`",
                                            .{ &oid_hex, raw_url },
                                        ),
                                    });
                                    self.has_aborted_error = true;
                                }
                            } else {
                                try self.sink.emit(.{
                                    .code = .e0016_offline_or_fetch_failed,
                                    .severity = .err,
                                    .primary_span = req_span,
                                    .message = try std.fmt.allocPrint(
                                        self.sink.arena.asAllocator(),
                                        "failed to resolve Git reference `{s}` in `{s}`",
                                        .{ if (rev_str.len > 0) rev_str else "HEAD", raw_url },
                                    ),
                                });
                                self.has_aborted_error = true;
                            }
                        } else {
                            try self.sink.emit(.{
                                .code = .e0016_offline_or_fetch_failed,
                                .severity = .err,
                                .primary_span = req_span,
                                .message = try std.fmt.allocPrint(
                                    self.sink.arena.asAllocator(),
                                    "unable to fetch or locate Git repository `{s}`",
                                    .{raw_url},
                                ),
                            });
                            self.has_aborted_error = true;
                        }
                    }
                }
            },
            else => {
                // `SOURCE_TAG_REGISTRY`: filter `all_cands` matching `key` (`tier`, `series_or_source_id`):
                const all_cands = try self.ensureRegistryCandidatesLoaded(key.pkg_name_sym, req_span);
                for (all_cands) |cand| {
                    const slot = cand.version.seriesSlot();
                    if (slot.tier == key.tier and slot.number == key.series_or_source_id) {
                        try entry.candidates.append(self.allocator, cand);
                    }
                }
            },
        }

        // Pre-populate declared feature bits (`0..511`) across all candidates of `entry`:
        for (entry.candidates.items) |cand| {
            for (cand.features) |f_decl| {
                _ = try entry.internFeatureBit(self.allocator, f_decl.name);
            }
            for (cand.dependencies) |d_spec| {
                if (d_spec.is_optional) {
                    _ = try entry.internFeatureBit(self.allocator, d_spec.alias_kebab);
                }
            }
        }

        try self.series_list.append(self.allocator, entry);
        try self.series_map.put(self.allocator, key, new_id);
        return new_id;
    }

    /// Maps a `DependencySpec` (after applying root `[patch]` overrides & workspace members) to its target `series_id`.
    fn resolveDepTargetSeries(
        self: *SolverContext,
        caller_series: u32,
        caller_cand_idx: u32,
        dep: DependencySpec,
    ) !struct { series_id: u32, effective_source: DepSourceSpec } {
        const caller_cand = self.series_list.items[caller_series].candidates.items[caller_cand_idx];
        const declaring_dir = caller_cand.host_dir_path orelse self.bundle.workspace_root_dir;

        var eff_source = dep.source;
        var eff_declaring_dir = declaring_dir;

        // [1] Apply root `[patch.<scope>]` overrides on registry / matching-URL dependencies (`DR-11` §1.3):
        if (self.patch_map.get(dep.package_kebab)) |patch_rule| {
            const is_overridable = switch (eff_source) {
                .registry => true,
                .git => |gs| std.mem.eql(u8, self.interner.get(patch_rule.scope), self.interner.get(gs.url)),
                else => false,
            };
            if (is_overridable) {
                eff_source = patch_rule.replacement;
                eff_declaring_dir = self.bundle.workspace_root_dir;
            }
        }

        // [2] Route workspace members directly when `path` points to a member or `workspace_pkg_map` matches:
        switch (eff_source) {
            .path => |ps| {
                const rel_str = self.interner.get(ps.rel_path);
                const norm_joined = if (std.fs.path.isAbsolute(rel_str))
                    try self.allocator.dupe(u8, rel_str)
                else
                    try std.fmt.allocPrint(self.allocator, "{s}/{s}", .{ eff_declaring_dir, rel_str });
                defer self.allocator.free(norm_joined);

                if (self.workspace_pkg_map.get(dep.package_kebab)) |ws_idx| {
                    const ws_mem = self.bundle.members[ws_idx];
                    if (std.mem.eql(u8, ws_mem.abs_dir, norm_joined) or std.mem.eql(u8, ws_mem.rel_dir, rel_str)) {
                        const ws_key = SeriesKey{
                            .pkg_name_sym = dep.package_kebab,
                            .tier = .major_ge_1,
                            .source_tag = SOURCE_TAG_WORKSPACE,
                            .series_or_source_id = ws_idx,
                        };
                        const sid = try self.getOrCreateSeries(ws_key, eff_source, eff_declaring_dir, dep.decl_span);
                        return .{ .series_id = sid, .effective_source = eff_source };
                    }
                }
                const loc_id = try self.interner.intern(norm_joined);
                const path_key = SeriesKey{
                    .pkg_name_sym = dep.package_kebab,
                    .tier = .major_ge_1,
                    .source_tag = SOURCE_TAG_PATH,
                    .series_or_source_id = loc_id.asInt(),
                };
                const sid = try self.getOrCreateSeries(path_key, eff_source, eff_declaring_dir, dep.decl_span);
                return .{ .series_id = sid, .effective_source = eff_source };
            },
            .git => |gs| {
                const loc_str = try std.fmt.allocPrint(
                    self.allocator,
                    "{s}#{d}:{s}",
                    .{ self.interner.get(gs.url), @backingInt(gs.rev_kind), self.interner.get(gs.rev_value) },
                );
                defer self.allocator.free(loc_str);
                const loc_id = try self.interner.intern(loc_str);
                const git_key = SeriesKey{
                    .pkg_name_sym = dep.package_kebab,
                    .tier = .major_ge_1,
                    .source_tag = SOURCE_TAG_GIT,
                    .series_or_source_id = loc_id.asInt(),
                };
                const sid = try self.getOrCreateSeries(git_key, eff_source, eff_declaring_dir, dep.decl_span);
                return .{ .series_id = sid, .effective_source = eff_source };
            },
            .registry => |ver_req| {
                // Determine target `SeriesKey` (`vN`, `v0.M`, or `v0.0.Z`);
                // for wildcard `*` (`len == 1 and op == .wildcard_any`), pick the highest non-yanked series in index:
                var chosen_slot = ver_req.min_floor.seriesSlot();
                if (ver_req.len == 1 and ver_req.comparators[0].op == .wildcard_any) {
                    const all_cands = try self.ensureRegistryCandidatesLoaded(dep.package_kebab, dep.decl_span);
                    var rev_idx = all_cands.len;
                    while (rev_idx > 0) {
                        rev_idx -= 1;
                        if (!all_cands[rev_idx].is_yanked) {
                            chosen_slot = all_cands[rev_idx].version.seriesSlot();
                            break;
                        }
                    }
                } else {
                    // Check if index has a matching candidate (e.g., `>1.9.0` might land in `2.0.0`):
                    const all_cands = try self.ensureRegistryCandidatesLoaded(dep.package_kebab, dep.decl_span);
                    for (all_cands) |cand| {
                        if (!cand.is_yanked and ver_req.matches(cand.version, self.interner)) {
                            chosen_slot = cand.version.seriesSlot();
                            break;
                        }
                    }
                }
                const reg_key = SeriesKey{
                    .pkg_name_sym = dep.package_kebab,
                    .tier = chosen_slot.tier,
                    .source_tag = SOURCE_TAG_REGISTRY,
                    .series_or_source_id = chosen_slot.number,
                };
                const sid = try self.getOrCreateSeries(reg_key, eff_source, eff_declaring_dir, dep.decl_span);
                return .{ .series_id = sid, .effective_source = eff_source };
            },
            .workspace_inherit => {
                const ws_idx = self.workspace_pkg_map.get(dep.package_kebab) orelse 0;
                const ws_key = SeriesKey{
                    .pkg_name_sym = dep.package_kebab,
                    .tier = .major_ge_1,
                    .source_tag = SOURCE_TAG_WORKSPACE,
                    .series_or_source_id = ws_idx,
                };
                const sid = try self.getOrCreateSeries(ws_key, eff_source, eff_declaring_dir, dep.decl_span);
                return .{ .series_id = sid, .effective_source = eff_source };
            },
        }
    }

    /// Evaluates whether `dep` is active on `caller_series` (`kind` filter + `target_cfg` `@cfg` filter).
    fn isDepEdgeTargetEnabled(self: *SolverContext, caller_series: u32, dep: DependencySpec) !bool {
        if (dep.kind == .dev and (caller_series != 0 or !self.options.is_including_tests)) {
            return false;
        }
        if (dep.target_cfg != .empty) {
            const cfg_text = self.interner.get(dep.target_cfg);
            const eval_opt = try pkg_manifest.validateAndEvalManifestTargetCfg(
                self.graph_arena,
                self.interner,
                null,
                cfg_text,
                &self.base_cfg_env,
                dep.decl_span,
                null,
                self.sink,
            );
            const is_matched = eval_opt orelse {
                self.has_aborted_error = true;
                return false;
            };
            if (!is_matched) return false;
        }
        return true;
    }

    /// Checks whether `cand` satisfies `[package].corex` compiler version requirement.
    fn isCompilerVersionCompatible(self: *const SolverContext, cand: CandidateVersionMeta) bool {
        if (cand.corex_req == .empty) return true;
        const req_str = self.interner.get(cand.corex_req);
        const parsed_req = (VersionReq.parse(self.interner, req_str) catch return true) orelse return true;
        return parsed_req.matches(self.options.compiler_version, self.interner);
    }

    /// Checks whether `(pkg_kebab, ver)` is banned by any root `[resolution].exclude` rule.
    fn isExcludedByManifestRule(self: *const SolverContext, pkg_kebab: SymbolId, ver: SemVer) bool {
        for (self.bundle.root_manifest.excludes) |rule| {
            if (rule.package_kebab == pkg_kebab and rule.req.matches(ver, self.interner)) {
                return true;
            }
        }
        if (self.bundle.root_manifest.workspace) |ws_cfg| {
            for (ws_cfg.excludes) |rule| {
                if (rule.package_kebab == pkg_kebab and rule.req.matches(ver, self.interner)) {
                    return true;
                }
            }
        }
        return false;
    }

    /// Activates `feat_id` on `series_id` inside `mvs_states` and returns `true` if newly added (`P2-1`).
    fn activateMvsFeature(
        self: *SolverContext,
        mvs_states: *std.ArrayListUnmanaged(MvsNodeState),
        series_id: u32,
        feat_id: StringId,
    ) !bool {
        const bit_idx = try self.series_list.items[series_id].internFeatureBit(self.allocator, feat_id);
        var state = &mvs_states.items[series_id];
        if (bit_idx < MAX_FEATURES_PER_PKG) {
            return state.enabled_bits.setReturningChanged(bit_idx);
        }
        const gop = try state.overflow_features.getOrPut(self.allocator, feat_id);
        return !gop.found_existing;
    }

    /// Returns `true` if `feat_id` is currently enabled on `series_id` in `mvs_states`.
    fn isMvsFeatureEnabled(
        self: *const SolverContext,
        mvs_states: []const MvsNodeState,
        series_id: u32,
        feat_id: StringId,
    ) bool {
        if (self.series_list.items[series_id].feature_to_bit.get(feat_id)) |bit_idx| {
            if (bit_idx < MAX_FEATURES_PER_PKG) {
                return mvs_states[series_id].enabled_bits.isSet(bit_idx);
            }
        }
        return mvs_states[series_id].overflow_features.contains(feat_id);
    }

    /// Executes Tier-1 `< 5 ms` $O(V + E)$ `Bounded-MVS` + monotone `FeatureBitset512` unification (`DR-11` §3.2, `P2-1`).
    /// Returns `true` if the MVS candidate satisfies all upper bounds, `[resolution].exclude` bans, and non-yanked checks.
    fn runTier1BoundedMvs(
        self: *SolverContext,
        mvs_states: *std.ArrayListUnmanaged(MvsNodeState),
        out_steps: *u32,
    ) !bool {
        try mvs_states.append(self.allocator, .{ .is_active = true, .selected_idx = 0, .is_in_worklist = true });
        var worklist: std.ArrayListUnmanaged(u32) = .empty;
        defer worklist.deinit(self.allocator);
        try worklist.append(self.allocator, 0);

        const default_feat_id = try self.interner.intern("default");

        // Seed root features (`default` unless `--no-default-features`, plus `-F` / `--features`):
        if (!self.options.has_no_default_features) {
            mvs_states.items[0].has_default_feature_requested = true;
            const root_cand = self.series_list.items[0].candidates.items[0];
            for (root_cand.features) |f_decl| {
                if (f_decl.name == default_feat_id) {
                    _ = try self.activateMvsFeature(mvs_states, 0, default_feat_id);
                    break;
                }
            }
        }

        var pending_cli_pkg_feats: std.ArrayListUnmanaged(struct { pkg_kebab: StringId, feat_id: StringId }) = .empty;
        defer pending_cli_pkg_feats.deinit(self.allocator);

        const root_cand_init = self.series_list.items[0].candidates.items[0];
        for (self.options.cli_features) |raw_cli_feat| {
            const trimmed = std.mem.trim(u8, raw_cli_feat, " \t");
            if (trimmed.len == 0) continue;
            if (std.mem.indexOfScalar(u8, trimmed, '/')) |slash_pos| {
                const pkg_part = trimmed[0..slash_pos];
                const feat_part = trimmed[slash_pos + 1 ..];
                const kebab_buf = try self.allocator.dupe(u8, pkg_part);
                defer self.allocator.free(kebab_buf);
                for (kebab_buf) |*ch| {
                    if (ch.* == '_') ch.* = '-';
                }
                const pkg_id = try self.interner.intern(kebab_buf);
                const f_id = try self.interner.intern(feat_part);
                if (pkg_id == self.series_list.items[0].key.pkg_name_sym) {
                    _ = try self.activateMvsFeature(mvs_states, 0, f_id);
                } else {
                    try pending_cli_pkg_feats.append(self.allocator, .{ .pkg_kebab = pkg_id, .feat_id = f_id });
                    for (root_cand_init.dependencies) |root_dep| {
                        if (root_dep.alias_kebab == pkg_id) {
                            if (root_dep.is_optional) {
                                try mvs_states.items[0].active_opt_deps.put(self.allocator, root_dep.alias_kebab, {});
                            }
                            if (root_dep.package_kebab != pkg_id) {
                                try pending_cli_pkg_feats.append(self.allocator, .{
                                    .pkg_kebab = root_dep.package_kebab,
                                    .feat_id = f_id,
                                });
                            }
                        }
                    }
                }
            } else {
                const f_id = try self.interner.intern(trimmed);
                _ = try self.activateMvsFeature(mvs_states, 0, f_id);
            }
        }

        var active_constraints: std.ArrayListUnmanaged(ActiveDepConstraint) = .empty;
        defer active_constraints.deinit(self.allocator);

        var q_head: usize = 0;
        while (true) {
            while (q_head < worklist.items.len) : (q_head += 1) {
                if (out_steps.* >= MAX_SOLVER_STEPS) return false;
                out_steps.* += 1;

                const cur_sid = worklist.items[q_head];
                mvs_states.items[cur_sid].is_in_worklist = false;

                const cands_len = self.series_list.items[cur_sid].candidates.items.len;
                if (cands_len == 0) return false;
                const cur_v_idx = mvs_states.items[cur_sid].selected_idx;
                if (cur_v_idx >= cands_len) return false;

                if (mvs_states.items[cur_sid].has_default_feature_requested) {
                    const cur_cand_def = self.series_list.items[cur_sid].candidates.items[cur_v_idx];
                    for (cur_cand_def.features) |tf| {
                        if (tf.name == default_feat_id) {
                            _ = try self.activateMvsFeature(mvs_states, cur_sid, default_feat_id);
                            break;
                        }
                    }
                }

                // Expand intra-package `[features]` transitive closure on `cur_sid` (`default -> ["tls"]`, `"dep:foo"`, `"foo?/bar"`):
                var has_local_feat_progress = true;
                var feat_guard: u32 = 0;
                while (has_local_feat_progress and feat_guard < 1024) : (feat_guard += 1) {
                    has_local_feat_progress = false;
                    const cand_snap = self.series_list.items[cur_sid].candidates.items[cur_v_idx];

                    // Implicit feature `<opt_dep>` activates `dep:<opt_dep>`:
                    for (cand_snap.dependencies) |d_spec| {
                        if (d_spec.is_optional and self.isMvsFeatureEnabled(mvs_states.items, cur_sid, d_spec.alias_kebab)) {
                            const gop = try mvs_states.items[cur_sid].active_opt_deps.getOrPut(
                                self.allocator,
                                d_spec.alias_kebab,
                            );
                            if (!gop.found_existing) has_local_feat_progress = true;
                        }
                    }

                    for (cand_snap.features) |f_decl| {
                        if (!self.isMvsFeatureEnabled(mvs_states.items, cur_sid, f_decl.name)) continue;
                        for (f_decl.activations) |act_id| {
                            const act_str = self.interner.get(act_id);
                            if (std.mem.startsWith(u8, act_str, "dep:")) {
                                const opt_alias = try self.interner.intern(act_str[4..]);
                                const gop = try mvs_states.items[cur_sid].active_opt_deps.getOrPut(
                                    self.allocator,
                                    opt_alias,
                                );
                                if (!gop.found_existing) has_local_feat_progress = true;
                            } else if (std.mem.indexOfScalar(u8, act_str, '/')) |slash_i| {
                                const raw_lhs = act_str[0..slash_i];
                                const rhs_feat = try self.interner.intern(act_str[slash_i + 1 ..]);
                                const is_weak = std.mem.endsWith(u8, raw_lhs, "?");
                                const clean_lhs = if (is_weak) raw_lhs[0 .. raw_lhs.len - 1] else raw_lhs;
                                const dep_alias_id = try self.interner.intern(clean_lhs);

                                var is_opt_dep = false;
                                for (cand_snap.dependencies) |d_check| {
                                    if (d_check.alias_kebab == dep_alias_id and d_check.is_optional) {
                                        is_opt_dep = true;
                                        break;
                                    }
                                }
                                if (!is_weak and is_opt_dep) {
                                    const gop = try mvs_states.items[cur_sid].active_opt_deps.getOrPut(
                                        self.allocator,
                                        dep_alias_id,
                                    );
                                    if (!gop.found_existing) has_local_feat_progress = true;
                                }
                                // Buffer in `pending_weak` (drained on active edges + outer fixed-point weak scan!):
                                var is_dup_pw = false;
                                for (mvs_states.items[cur_sid].pending_weak.items) |pw| {
                                    if (pw.dep_alias_kebab == dep_alias_id and pw.target_feat_id == rhs_feat) {
                                        is_dup_pw = true;
                                        break;
                                    }
                                }
                                if (!is_dup_pw) {
                                    try mvs_states.items[cur_sid].pending_weak.append(self.allocator, .{
                                        .dep_alias_kebab = dep_alias_id,
                                        .target_feat_id = rhs_feat,
                                    });
                                }
                            } else {
                                if (try self.activateMvsFeature(mvs_states, cur_sid, act_id)) {
                                    has_local_feat_progress = true;
                                }
                            }
                        }
                    }
                }

                // Snapshot dependencies of `(cur_sid, cur_v_idx)` before `resolveDepTargetSeries` may grow `series_list`:
                const deps_slice = self.series_list.items[cur_sid].candidates.items[cur_v_idx].dependencies;
                for (deps_slice) |dep| {
                    if (!(try self.isDepEdgeTargetEnabled(cur_sid, dep))) continue;
                    if (dep.is_optional and !mvs_states.items[cur_sid].active_opt_deps.contains(dep.alias_kebab)) {
                        continue;
                    }

                    const resolved_target = try self.resolveDepTargetSeries(cur_sid, cur_v_idx, dep);
                    if (self.has_aborted_error) return false;
                    const target_sid = resolved_target.series_id;
                    while (mvs_states.items.len <= target_sid) {
                        try mvs_states.append(self.allocator, .{});
                    }

                    const target_cands = self.series_list.items[target_sid].candidates.items;
                    if (target_cands.len == 0) return false;

                    // Determine minimal candidate index matching `dep` (preferring existing lockfile pin when valid!):
                    var req_floor_idx: ?u32 = null;
                    switch (resolved_target.effective_source) {
                        .registry => |ver_req| {
                            try active_constraints.append(self.allocator, .{
                                .caller_series = cur_sid,
                                .caller_ver_idx = cur_v_idx,
                                .callee_series = target_sid,
                                .req = ver_req,
                                .anchor_id = dep.anchor_id,
                                .decl_span = dep.decl_span,
                            });

                            if (self.existing_lock) |lock_doc| {
                                const pkg_sym = self.series_list.items[target_sid].key.pkg_name_sym;
                                for (lock_doc.packages) |lp| {
                                    if (lp.name != pkg_sym) continue;
                                    const lp_slot = lp.version.seriesSlot();
                                    if (lp_slot.tier != self.series_list.items[target_sid].key.tier or
                                        lp_slot.number != self.series_list.items[target_sid].key.series_or_source_id)
                                    {
                                        continue;
                                    }
                                    if (ver_req.matches(lp.version, self.interner)) {
                                        for (target_cands, 0..) |tc, tc_i| {
                                            if (SemVer.eql(tc.version, lp.version, self.interner) and
                                                lp.source == tc.source_uri)
                                            {
                                                req_floor_idx = @intCast(tc_i);
                                                break;
                                            }
                                        }
                                    }
                                }
                            }

                            if (req_floor_idx == null) {
                                for (target_cands, 0..) |tc, tc_i| {
                                    if (!tc.is_yanked and ver_req.matches(tc.version, self.interner)) {
                                        req_floor_idx = @intCast(tc_i);
                                        break;
                                    }
                                }
                            }
                            if (req_floor_idx == null) {
                                return false;
                            }
                        },
                        .path => |ps| {
                            if (ps.version_req) |ver_req| {
                                if (!ver_req.matches(target_cands[0].version, self.interner)) return false;
                            }
                            req_floor_idx = 0;
                        },
                        else => {
                            req_floor_idx = 0;
                        },
                    }

                    const min_idx = req_floor_idx.?;
                    const was_active = mvs_states.items[target_sid].is_active;
                    const prev_idx = mvs_states.items[target_sid].selected_idx;
                    const next_idx = if (was_active) @max(prev_idx, min_idx) else min_idx;
                    const has_version_raised = !was_active or (next_idx != prev_idx);

                    mvs_states.items[target_sid].is_active = true;
                    mvs_states.items[target_sid].selected_idx = next_idx;
                    if (dep.has_default_features) {
                        mvs_states.items[target_sid].has_default_feature_requested = true;
                    }

                    var has_added_features = false;
                    // [a] Activate `"default"` whenever `has_default_feature_requested` holds on `next_idx`:
                    if (mvs_states.items[target_sid].has_default_feature_requested) {
                        const target_cand = self.series_list.items[target_sid].candidates.items[next_idx];
                        for (target_cand.features) |tf| {
                            if (tf.name == default_feat_id) {
                                if (try self.activateMvsFeature(mvs_states, target_sid, default_feat_id)) {
                                    has_added_features = true;
                                }
                                break;
                            }
                        }
                    }
                    // [b] Activate explicit `dep.features`:
                    for (dep.features) |df_id| {
                        if (try self.activateMvsFeature(mvs_states, target_sid, df_id)) {
                            has_added_features = true;
                        }
                    }
                    // [c] Activate any buffered weak/`pkg/feat` activations targeting `dep.alias_kebab`:
                    const pw_len = mvs_states.items[cur_sid].pending_weak.items.len;
                    var pw_i: usize = 0;
                    while (pw_i < pw_len) : (pw_i += 1) {
                        const pw = mvs_states.items[cur_sid].pending_weak.items[pw_i];
                        if (pw.dep_alias_kebab == dep.alias_kebab) {
                            if (try self.activateMvsFeature(mvs_states, target_sid, pw.target_feat_id)) {
                                has_added_features = true;
                            }
                        }
                    }
                    // [d] Apply CLI `-F pkg/feat` targeting `target_sid`:
                    const target_pkg_sym = self.series_list.items[target_sid].key.pkg_name_sym;
                    for (pending_cli_pkg_feats.items) |cli_pf| {
                        if (cli_pf.pkg_kebab == target_pkg_sym) {
                            if (try self.activateMvsFeature(mvs_states, target_sid, cli_pf.feat_id)) {
                                has_added_features = true;
                            }
                        }
                    }

                    // CRITICAL (`P2-1`): Re-enqueue `target_sid` whenever `has_version_raised` OR `has_added_features` (`v_next == v_cur`):
                    if ((has_version_raised or has_added_features) and !mvs_states.items[target_sid].is_in_worklist) {
                        mvs_states.items[target_sid].is_in_worklist = true;
                        try worklist.append(self.allocator, target_sid);
                    }
                }
            }

            // Fixed-point pass over weak `foo?/feat` activations across all active series:
            var has_weak_progress = false;
            var scan_sid: u32 = 0;
            while (scan_sid < mvs_states.items.len) : (scan_sid += 1) {
                if (!mvs_states.items[scan_sid].is_active) continue;
                const pw_count = mvs_states.items[scan_sid].pending_weak.items.len;
                if (pw_count == 0) continue;
                const scan_v_idx = mvs_states.items[scan_sid].selected_idx;
                const scan_deps = self.series_list.items[scan_sid].candidates.items[scan_v_idx].dependencies;

                var pw_idx: usize = 0;
                while (pw_idx < pw_count) : (pw_idx += 1) {
                    const pw = mvs_states.items[scan_sid].pending_weak.items[pw_idx];
                    for (scan_deps) |dep_spec| {
                        if (dep_spec.alias_kebab != pw.dep_alias_kebab) continue;
                        if (!(try self.isDepEdgeTargetEnabled(scan_sid, dep_spec))) continue;
                        const resolved_pw = try self.resolveDepTargetSeries(scan_sid, scan_v_idx, dep_spec);
                        if (self.has_aborted_error) return false;
                        const target_sid = resolved_pw.series_id;
                        if (target_sid < mvs_states.items.len and mvs_states.items[target_sid].is_active) {
                            if (try self.activateMvsFeature(mvs_states, target_sid, pw.target_feat_id)) {
                                has_weak_progress = true;
                                if (!mvs_states.items[target_sid].is_in_worklist) {
                                    mvs_states.items[target_sid].is_in_worklist = true;
                                    try worklist.append(self.allocator, target_sid);
                                }
                            }
                        }
                    }
                }
            }
            if (!has_weak_progress) break;
        }

        // Validate all active upper bounds, `[resolution].exclude` bans, yanked flags, and compiler `corex` bounds:
        for (active_constraints.items) |constraint| {
            if (!mvs_states.items[constraint.caller_series].is_active) continue;
            if (mvs_states.items[constraint.caller_series].selected_idx != constraint.caller_ver_idx) continue;
            const callee_v_idx = mvs_states.items[constraint.callee_series].selected_idx;
            const callee_cand = self.series_list.items[constraint.callee_series].candidates.items[callee_v_idx];
            if (!constraint.req.matches(callee_cand.version, self.interner)) {
                return false;
            }
        }

        for (mvs_states.items, 0..) |st, sid| {
            if (!st.is_active) continue;
            const s_entry = &self.series_list.items[sid];
            const cand = s_entry.candidates.items[st.selected_idx];
            if (sid > 0) {
                if (self.isExcludedByManifestRule(s_entry.key.pkg_name_sym, cand.version)) return false;
                if (!self.isCompilerVersionCompatible(cand)) return false;
                if (cand.is_yanked) {
                    var is_locked_ok = false;
                    if (self.existing_lock) |lock_doc| {
                        for (lock_doc.packages) |lp| {
                            if (lp.name == s_entry.key.pkg_name_sym and
                                SemVer.eql(lp.version, cand.version, self.interner) and
                                lp.source == cand.source_uri)
                            {
                                is_locked_ok = true;
                                break;
                            }
                        }
                    }
                    if (!is_locked_ok) return false;
                }
            }
        }

        return true;
    }

    /// Executes Tier-2 Bounded `PubGrub CDCL` (`<= 100,000` steps) with feature-aware clause learning and
    /// exports a level-0 `ConflictDagExport` (`E0010`) on unsatisfiability (`DR-11` §3.3, `DR-16` §2.3, `P2-1`).
    fn runTier2PubGrubCdcl(
        self: *SolverContext,
        mvs_states: *std.ArrayListUnmanaged(MvsNodeState),
        out_steps: *u32,
        out_conflict_dag: *?ConflictDagExport,
    ) !bool {
        var cdcl_arena = BumpArena.init(self.allocator);
        defer cdcl_arena.deinit();
        const arena_alloc = cdcl_arena.asAllocator();

        var nodes: std.ArrayListUnmanaged(IncompatNode) = .empty;
        defer nodes.deinit(self.allocator);
        var terms: std.ArrayListUnmanaged(IncompatTerm) = .empty;
        defer terms.deinit(self.allocator);
        var explain_metas: std.ArrayListUnmanaged(IncompatExplainMeta) = .empty;
        defer explain_metas.deinit(self.allocator);

        var trail: std.ArrayListUnmanaged(CdclTrailEntry) = .empty;
        defer trail.deinit(self.allocator);
        var series_domains: std.ArrayListUnmanaged([]u64) = .empty;
        defer series_domains.deinit(self.allocator);
        var series_assign_step: std.ArrayListUnmanaged(usize) = .empty;
        defer series_assign_step.deinit(self.allocator);
        var series_expanded_ver: std.ArrayListUnmanaged([]bool) = .empty;
        defer series_expanded_ver.deinit(self.allocator);
        var series_seeded_bans: std.ArrayListUnmanaged(bool) = .empty;
        defer series_seeded_bans.deinit(self.allocator);

        var feat_assigns: std.AutoHashMapUnmanaged(SeriesFeatKey, struct {
            is_enabled: bool,
            step_idx: usize,
            decision_level: u32,
        }) = .empty;
        defer feat_assigns.deinit(self.allocator);

        const ensureSeriesCdclSlots = struct {
            /// Initializes `series_domains` (`{0..N-1, STATE_ABSENT}`) and level-0 `.exclude_ban` nodes for new series.
            fn run(
                ctx: *SolverContext,
                a_alloc: std.mem.Allocator,
                doms: *std.ArrayListUnmanaged([]u64),
                steps_map: *std.ArrayListUnmanaged(usize),
                exp_map: *std.ArrayListUnmanaged([]bool),
                bans_map: *std.ArrayListUnmanaged(bool),
                incompat_nodes: *std.ArrayListUnmanaged(IncompatNode),
                incompat_terms: *std.ArrayListUnmanaged(IncompatTerm),
                metas: *std.ArrayListUnmanaged(IncompatExplainMeta),
            ) !void {
                while (doms.items.len < ctx.series_list.items.len) {
                    const sid = doms.items.len;
                    const cand_len = ctx.series_list.items[sid].candidates.items.len;
                    const state_cnt = cand_len + 1;
                    const w_cnt = countStateWords(state_cnt);
                    const words = try a_alloc.alloc(u64, w_cnt);
                    @memset(words, 0);
                    for (0..state_cnt) |st_i| {
                        // Root (`sid == 0`) cannot be `STATE_ABSENT`:
                        if (sid == 0 and st_i == cand_len) continue;
                        setStateBit(words, st_i);
                    }
                    try doms.append(ctx.allocator, words);
                    try steps_map.append(ctx.allocator, 0);
                    const exp_flags = try a_alloc.alloc(bool, @max(cand_len, 1));
                    @memset(exp_flags, false);
                    try exp_map.append(ctx.allocator, exp_flags);
                    try bans_map.append(ctx.allocator, false);
                }

                // Seed level-0 `[resolution].exclude`, compiler-version, and yanked bans for newly discovered series:
                for (0..ctx.series_list.items.len) |sid_usize| {
                    if (bans_map.items[sid_usize]) continue;
                    bans_map.items[sid_usize] = true;
                    if (sid_usize == 0) continue;

                    const sid: u32 = @intCast(sid_usize);
                    const s_entry = &ctx.series_list.items[sid_usize];
                    const cands = s_entry.candidates.items;
                    if (cands.len == 0) continue;

                    const all_exclude_slices = [_][]const ExcludeRule{
                        ctx.bundle.root_manifest.excludes,
                        if (ctx.bundle.root_manifest.workspace) |ws| ws.excludes else &.{},
                    };
                    for (all_exclude_slices) |rule_slice| {
                        for (rule_slice) |rule| {
                            if (rule.package_kebab != s_entry.key.pkg_name_sym) continue;
                            var run_start: ?u32 = null;
                            var run_end: u32 = 0;
                            for (cands, 0..) |cand, c_i| {
                                if (rule.req.matches(cand.version, ctx.interner)) {
                                    if (run_start == null) run_start = @intCast(c_i);
                                    run_end = @intCast(c_i);
                                } else if (run_start) |rs| {
                                    const t_start: u32 = @intCast(incompat_terms.items.len);
                                    try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, rs, run_end, true));
                                    try incompat_nodes.append(ctx.allocator, .{
                                        .term_start = t_start,
                                        .term_len = 1,
                                        .kind = .exclude_ban,
                                        .flags = if (rule.has_cve_advisory) 0x01 else 0,
                                        .toml_anchor_id = rule.anchor_id,
                                        .decision_level = 0,
                                    });
                                    try metas.append(ctx.allocator, .{ .span = rule.span });
                                    run_start = null;
                                }
                            }
                            if (run_start) |rs| {
                                const t_start: u32 = @intCast(incompat_terms.items.len);
                                try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, rs, run_end, true));
                                try incompat_nodes.append(ctx.allocator, .{
                                    .term_start = t_start,
                                    .term_len = 1,
                                    .kind = .exclude_ban,
                                    .flags = if (rule.has_cve_advisory) 0x01 else 0,
                                    .toml_anchor_id = rule.anchor_id,
                                    .decision_level = 0,
                                });
                                try metas.append(ctx.allocator, .{ .span = rule.span });
                            }
                        }
                    }

                    // Yanked or incompatible `[package].corex` versions:
                    for (cands, 0..) |cand, c_i| {
                        const idx_u32: u32 = @intCast(c_i);
                        const is_bad_corex = !ctx.isCompilerVersionCompatible(cand);
                        var is_banned_yank = cand.is_yanked;
                        if (is_banned_yank and ctx.existing_lock != null) {
                            for (ctx.existing_lock.?.packages) |lp| {
                                if (lp.name == s_entry.key.pkg_name_sym and
                                    SemVer.eql(lp.version, cand.version, ctx.interner) and
                                    lp.source == cand.source_uri)
                                {
                                    is_banned_yank = false;
                                    break;
                                }
                            }
                        }
                        if (is_bad_corex or is_banned_yank) {
                            const t_start: u32 = @intCast(incompat_terms.items.len);
                            try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, idx_u32, idx_u32, true));
                            const label = if (is_bad_corex)
                                try std.fmt.allocPrint(
                                    ctx.graph_arena.asAllocator(),
                                    "requires compiler `corex {s}`",
                                    .{ctx.interner.get(cand.corex_req)},
                                )
                            else
                                try ctx.graph_arena.dupe(u8, "version is yanked in registry");
                            try incompat_nodes.append(ctx.allocator, .{
                                .term_start = t_start,
                                .term_len = 1,
                                .kind = .no_versions,
                                .decision_level = 0,
                            });
                            try metas.append(ctx.allocator, .{ .unmatched_req_label = label });
                        }
                    }

                    // CLI `-F pkg/feat` forces `(sid, feat) = true` whenever `sid` is active (`sid ∈ [0..INF]`):
                    if (ctx.options.cli_features.len > 0) {
                        const root_deps = ctx.series_list.items[0].candidates.items[0].dependencies;
                        for (ctx.options.cli_features) |raw_cli_feat| {
                            const trimmed_cli = std.mem.trim(u8, raw_cli_feat, " \t");
                            const slash_idx = std.mem.indexOfScalar(u8, trimmed_cli, '/') orelse continue;
                            const pkg_part = trimmed_cli[0..slash_idx];
                            const feat_part = trimmed_cli[slash_idx + 1 ..];
                            if (pkg_part.len == 0 or pkg_part.len > pkg_manifest.MAX_PKG_NAME_BYTES or feat_part.len == 0) {
                                continue;
                            }
                            var kebab_buf: [pkg_manifest.MAX_PKG_NAME_BYTES]u8 = undefined;
                            for (pkg_part, 0..) |ch_byte, i| {
                                kebab_buf[i] = if (ch_byte == '_') '-' else ch_byte;
                            }
                            const cli_pkg_id = try ctx.interner.intern(kebab_buf[0..pkg_part.len]);
                            var is_matching_cli_pkg = (cli_pkg_id == s_entry.key.pkg_name_sym);
                            if (!is_matching_cli_pkg) {
                                for (root_deps) |root_dep| {
                                    if (root_dep.alias_kebab == cli_pkg_id and
                                        root_dep.package_kebab == s_entry.key.pkg_name_sym)
                                    {
                                        is_matching_cli_pkg = true;
                                        break;
                                    }
                                }
                            }
                            if (is_matching_cli_pkg) {
                                const cli_feat_id = try ctx.interner.intern(feat_part);
                                _ = try s_entry.internFeatureBit(ctx.allocator, cli_feat_id);
                                const t_start: u32 = @intCast(incompat_terms.items.len);
                                try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, 0, INF_VER_INDEX, true));
                                try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, cli_feat_id, false));
                                try incompat_nodes.append(ctx.allocator, .{
                                    .term_start = t_start,
                                    .term_len = 2,
                                    .kind = .feature_dep,
                                    .decision_level = 0,
                                });
                                try metas.append(ctx.allocator, .{});
                            }
                        }
                    }
                }
            }
        }.run;

        try ensureSeriesCdclSlots(
            self,
            arena_alloc,
            &series_domains,
            &series_assign_step,
            &series_expanded_ver,
            &series_seeded_bans,
            &nodes,
            &terms,
            &explain_metas,
        );

        // Seed level-0 `.root_pin` `{ ¬root@[0..0] }`:
        {
            const t_start: u32 = @intCast(terms.items.len);
            try terms.append(self.allocator, makeVersionTerm(0, 0, 0, false));
            try nodes.append(self.allocator, .{
                .term_start = t_start,
                .term_len = 1,
                .kind = .root_pin,
                .decision_level = 0,
            });
            try explain_metas.append(self.allocator, .{});
        }

        // Seed root features at `decision_level = 0`:
        const default_feat_id = try self.interner.intern("default");
        const root_cand = self.series_list.items[0].candidates.items[0];
        if (!self.options.has_no_default_features) {
            for (root_cand.features) |f_decl| {
                if (f_decl.name == default_feat_id) {
                    const key = SeriesFeatKey{ .series_id = 0, .feat_id = default_feat_id };
                    try feat_assigns.put(self.allocator, key, .{
                        .is_enabled = true,
                        .step_idx = trail.items.len,
                        .decision_level = 0,
                    });
                    try trail.append(self.allocator, .{
                        .decision_level = 0,
                        .cause_incompat = null,
                        .mutation = .{ .feature_val = .{ .key = key, .is_enabled = true } },
                    });
                    break;
                }
            }
        }
        for (self.options.cli_features) |raw_cli_f| {
            const trimmed = std.mem.trim(u8, raw_cli_f, " \t");
            if (trimmed.len == 0) continue;
            if (std.mem.indexOfScalar(u8, trimmed, '/')) |slash_pos| {
                const pkg_part = trimmed[0..slash_pos];
                const feat_part = trimmed[slash_pos + 1 ..];
                if (pkg_part.len == 0 or pkg_part.len > pkg_manifest.MAX_PKG_NAME_BYTES or feat_part.len == 0) {
                    continue;
                }
                var kebab_buf: [pkg_manifest.MAX_PKG_NAME_BYTES]u8 = undefined;
                for (pkg_part, 0..) |ch_byte, i| {
                    kebab_buf[i] = if (ch_byte == '_') '-' else ch_byte;
                }
                const pkg_id = try self.interner.intern(kebab_buf[0..pkg_part.len]);
                if (pkg_id == self.series_list.items[0].key.pkg_name_sym) {
                    const root_f_id = try self.interner.intern(feat_part);
                    const root_key = SeriesFeatKey{ .series_id = 0, .feat_id = root_f_id };
                    if (!feat_assigns.contains(root_key)) {
                        try feat_assigns.put(self.allocator, root_key, .{
                            .is_enabled = true,
                            .step_idx = trail.items.len,
                            .decision_level = 0,
                        });
                        try trail.append(self.allocator, .{
                            .decision_level = 0,
                            .cause_incompat = null,
                            .mutation = .{ .feature_val = .{ .key = root_key, .is_enabled = true } },
                        });
                    }
                } else {
                    for (root_cand.dependencies) |root_dep| {
                        if (root_dep.is_optional and root_dep.alias_kebab == pkg_id) {
                            const dep_gate_str = try std.fmt.allocPrint(
                                self.allocator,
                                "dep:{s}",
                                .{self.interner.get(root_dep.alias_kebab)},
                            );
                            defer self.allocator.free(dep_gate_str);
                            const dep_gate_id = try self.interner.intern(dep_gate_str);
                            const gate_key = SeriesFeatKey{ .series_id = 0, .feat_id = dep_gate_id };
                            if (!feat_assigns.contains(gate_key)) {
                                try feat_assigns.put(self.allocator, gate_key, .{
                                    .is_enabled = true,
                                    .step_idx = trail.items.len,
                                    .decision_level = 0,
                                });
                                try trail.append(self.allocator, .{
                                    .decision_level = 0,
                                    .cause_incompat = null,
                                    .mutation = .{ .feature_val = .{ .key = gate_key, .is_enabled = true } },
                                });
                            }
                        }
                    }
                }
                continue;
            }
            const f_id = try self.interner.intern(trimmed);
            const key = SeriesFeatKey{ .series_id = 0, .feat_id = f_id };
            if (!feat_assigns.contains(key)) {
                try feat_assigns.put(self.allocator, key, .{
                    .is_enabled = true,
                    .step_idx = trail.items.len,
                    .decision_level = 0,
                });
                try trail.append(self.allocator, .{
                    .decision_level = 0,
                    .cause_incompat = null,
                    .mutation = .{ .feature_val = .{ .key = key, .is_enabled = true } },
                });
            }
        }

        const expandCandidateIncompatibilities = struct {
            /// Lazily emits `.dep_edge` and `.feature_dep` `IncompatNode`s for `(sid, v_idx)`.
            fn run(
                ctx: *SolverContext,
                a_alloc: std.mem.Allocator,
                sid: u32,
                v_idx: u32,
                def_feat: StringId,
                doms: *std.ArrayListUnmanaged([]u64),
                steps_map: *std.ArrayListUnmanaged(usize),
                exp_map: *std.ArrayListUnmanaged([]bool),
                bans_map: *std.ArrayListUnmanaged(bool),
                incompat_nodes: *std.ArrayListUnmanaged(IncompatNode),
                incompat_terms: *std.ArrayListUnmanaged(IncompatTerm),
                metas: *std.ArrayListUnmanaged(IncompatExplainMeta),
            ) !void {
                if (exp_map.items[sid][v_idx]) return;
                exp_map.items[sid][v_idx] = true;

                // [1] Intra-package `[features]` implications: `S@v ∧ S+F ⟹ S+G`:
                const cand_init = ctx.series_list.items[sid].candidates.items[v_idx];
                const features_copy = cand_init.features;
                const deps_copy = cand_init.dependencies;

                var dep_alias_to_sid: std.AutoHashMapUnmanaged(StringId, u32) = .empty;
                defer dep_alias_to_sid.deinit(ctx.allocator);

                for (deps_copy) |dep| {
                    if (!(try ctx.isDepEdgeTargetEnabled(sid, dep))) continue;
                    const resolved = try ctx.resolveDepTargetSeries(sid, v_idx, dep);
                    if (ctx.has_aborted_error) return;
                    const target_sid = resolved.series_id;
                    try dep_alias_to_sid.put(ctx.allocator, dep.alias_kebab, target_sid);

                    try ensureSeriesCdclSlots(
                        ctx,
                        a_alloc,
                        doms,
                        steps_map,
                        exp_map,
                        bans_map,
                        incompat_nodes,
                        incompat_terms,
                        metas,
                    );

                    const target_cands = ctx.series_list.items[target_sid].candidates.items;
                    const dep_gate_feat: ?StringId = if (dep.is_optional) blk_gate: {
                        const dep_prefix = try std.fmt.allocPrint(
                            ctx.allocator,
                            "dep:{s}",
                            .{ctx.interner.get(dep.alias_kebab)},
                        );
                        defer ctx.allocator.free(dep_prefix);
                        const dep_gate_id = try ctx.interner.intern(dep_prefix);
                        // Implicit `<alias_kebab>` feature activates `dep:<alias_kebab>`:
                        const imp_start: u32 = @intCast(incompat_terms.items.len);
                        try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                        try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, dep.alias_kebab, true));
                        try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, dep_gate_id, false));
                        try incompat_nodes.append(ctx.allocator, .{
                            .term_start = imp_start,
                            .term_len = 3,
                            .kind = .feature_dep,
                            .toml_anchor_id = dep.anchor_id,
                        });
                        try metas.append(ctx.allocator, .{ .span = dep.decl_span });
                        break :blk_gate dep_gate_id;
                    } else null;

                    // Collect matching indices `[0 .. target_cands.len - 1]`:
                    var match_indices: std.ArrayListUnmanaged(u32) = .empty;
                    defer match_indices.deinit(ctx.allocator);
                    switch (resolved.effective_source) {
                        .registry => |ver_req| {
                            for (target_cands, 0..) |tc, tc_i| {
                                if (ver_req.matches(tc.version, ctx.interner)) {
                                    try match_indices.append(ctx.allocator, @intCast(tc_i));
                                }
                            }
                        },
                        .path => |ps| {
                            if (target_cands.len > 0) {
                                const is_ok = if (ps.version_req) |vr|
                                    vr.matches(target_cands[0].version, ctx.interner)
                                else
                                    true;
                                if (is_ok) try match_indices.append(ctx.allocator, 0);
                            }
                        },
                        else => {
                            if (target_cands.len > 0) try match_indices.append(ctx.allocator, 0);
                        },
                    }

                    if (match_indices.items.len == 0) {
                        // Zero matching versions (`{ S@[v..v] (, S+gate) }`) is immediately incompatible:
                        const t_start: u32 = @intCast(incompat_terms.items.len);
                        try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                        if (dep_gate_feat) |gf| {
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, gf, true));
                        }
                        const t_len: u16 = @intCast(incompat_terms.items.len - t_start);
                        const miss_lbl = try std.fmt.allocPrint(
                            ctx.graph_arena.asAllocator(),
                            "no candidate version of `{s}` satisfies dependency requirement",
                            .{ctx.interner.get(dep.package_kebab)},
                        );
                        try incompat_nodes.append(ctx.allocator, .{
                            .term_start = t_start,
                            .term_len = t_len,
                            .kind = if (dep_gate_feat != null) .feature_dep else .no_versions,
                            .toml_anchor_id = dep.anchor_id,
                        });
                        try metas.append(ctx.allocator, .{
                            .unmatched_req_label = miss_lbl,
                            .span = dep.decl_span,
                        });
                        continue;
                    }

                    const lo_m = match_indices.items[0];
                    const hi_m = match_indices.items[match_indices.items.len - 1];
                    // Emit `.dep_edge`: `{ S@[v..v] (, S+gate), ¬target@[lo_m..hi_m] }`:
                    {
                        const t_start: u32 = @intCast(incompat_terms.items.len);
                        try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                        if (dep_gate_feat) |gf| {
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, gf, true));
                        }
                        try incompat_terms.append(ctx.allocator, makeVersionTerm(target_sid, lo_m, hi_m, false));
                        try incompat_nodes.append(ctx.allocator, .{
                            .term_start = t_start,
                            .term_len = @intCast(incompat_terms.items.len - t_start),
                            .kind = if (dep_gate_feat != null) .feature_dep else .dep_edge,
                            .toml_anchor_id = dep.anchor_id,
                        });
                        try metas.append(ctx.allocator, .{ .span = dep.decl_span });
                    }
                    // Also forbid any interior holes inside `[lo_m..hi_m]` if `match_indices` was non-contiguous:
                    if (hi_m - lo_m + 1 > match_indices.items.len) {
                        var m_cursor: usize = 0;
                        var idx_scan: u32 = lo_m;
                        while (idx_scan <= hi_m) : (idx_scan += 1) {
                            if (m_cursor < match_indices.items.len and match_indices.items[m_cursor] == idx_scan) {
                                m_cursor += 1;
                            } else {
                                const h_start: u32 = @intCast(incompat_terms.items.len);
                                try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                                if (dep_gate_feat) |gf| {
                                    try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, gf, true));
                                }
                                try incompat_terms.append(ctx.allocator, makeVersionTerm(target_sid, idx_scan, idx_scan, true));
                                try incompat_nodes.append(ctx.allocator, .{
                                    .term_start = h_start,
                                    .term_len = @intCast(incompat_terms.items.len - h_start),
                                    .kind = .dep_edge,
                                    .toml_anchor_id = dep.anchor_id,
                                });
                                try metas.append(ctx.allocator, .{ .span = dep.decl_span });
                            }
                        }
                    }

                    // Propagate `default` (if any candidate in `target_sid` declares `default`) & explicit `dep.features`:
                    if (dep.has_default_features) {
                        var has_target_def = false;
                        for (ctx.series_list.items[target_sid].candidates.items) |tc| {
                            for (tc.features) |tf| {
                                if (tf.name == def_feat) {
                                    has_target_def = true;
                                    break;
                                }
                            }
                        }
                        if (has_target_def) {
                            const f_start: u32 = @intCast(incompat_terms.items.len);
                            try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                            if (dep_gate_feat) |gf| {
                                try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, gf, true));
                            }
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(target_sid, def_feat, false));
                            try incompat_nodes.append(ctx.allocator, .{
                                .term_start = f_start,
                                .term_len = @intCast(incompat_terms.items.len - f_start),
                                .kind = .feature_dep,
                                .toml_anchor_id = dep.anchor_id,
                            });
                            try metas.append(ctx.allocator, .{ .span = dep.decl_span });
                        }
                    }
                    for (dep.features) |df_id| {
                        const f_start: u32 = @intCast(incompat_terms.items.len);
                        try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                        if (dep_gate_feat) |gf| {
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, gf, true));
                        }
                        try incompat_terms.append(ctx.allocator, makeFeatureTerm(target_sid, df_id, false));
                        try incompat_nodes.append(ctx.allocator, .{
                            .term_start = f_start,
                            .term_len = @intCast(incompat_terms.items.len - f_start),
                            .kind = .feature_dep,
                            .toml_anchor_id = dep.anchor_id,
                        });
                        try metas.append(ctx.allocator, .{ .span = dep.decl_span });
                    }
                }

                // Emit `[features]` activation rules (`dep:foo`, `foo/bar`, `foo?/bar`, local `sub_feat`):
                for (features_copy) |f_decl| {
                    for (f_decl.activations) |act_id| {
                        const act_str = ctx.interner.get(act_id);
                        if (std.mem.startsWith(u8, act_str, "dep:")) {
                            const dep_gate_id = try ctx.interner.intern(act_str);
                            const t_start: u32 = @intCast(incompat_terms.items.len);
                            try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, f_decl.name, true));
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, dep_gate_id, false));
                            try incompat_nodes.append(ctx.allocator, .{
                                .term_start = t_start,
                                .term_len = 3,
                                .kind = .feature_dep,
                            });
                            try metas.append(ctx.allocator, .{});
                        } else if (std.mem.indexOfScalar(u8, act_str, '/')) |slash_i| {
                            const raw_lhs = act_str[0..slash_i];
                            const rhs_feat = try ctx.interner.intern(act_str[slash_i + 1 ..]);
                            const is_weak = std.mem.endsWith(u8, raw_lhs, "?");
                            const clean_lhs = if (is_weak) raw_lhs[0 .. raw_lhs.len - 1] else raw_lhs;
                            const dep_alias_id = try ctx.interner.intern(clean_lhs);
                            const target_sid = dep_alias_to_sid.get(dep_alias_id) orelse continue;

                            var is_opt_dep = false;
                            for (deps_copy) |d_check| {
                                if (d_check.alias_kebab == dep_alias_id and d_check.is_optional) {
                                    is_opt_dep = true;
                                    break;
                                }
                            }
                            if (!is_weak and is_opt_dep) {
                                const dep_prefix = try std.fmt.allocPrint(
                                    ctx.allocator,
                                    "dep:{s}",
                                    .{clean_lhs},
                                );
                                defer ctx.allocator.free(dep_prefix);
                                const dep_gate_id = try ctx.interner.intern(dep_prefix);
                                const g_start: u32 = @intCast(incompat_terms.items.len);
                                try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                                try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, f_decl.name, true));
                                try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, dep_gate_id, false));
                                try incompat_nodes.append(ctx.allocator, .{
                                    .term_start = g_start,
                                    .term_len = 3,
                                    .kind = .feature_dep,
                                });
                                try metas.append(ctx.allocator, .{});
                            }

                            const f_start: u32 = @intCast(incompat_terms.items.len);
                            try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, f_decl.name, true));
                            if (is_weak and is_opt_dep) {
                                // Weak `foo?/bar`: only fires when `target_sid` is active (`target_sid ∈ [0..INF]`):
                                try incompat_terms.append(ctx.allocator, makeVersionTerm(target_sid, 0, INF_VER_INDEX, true));
                            }
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(target_sid, rhs_feat, false));
                            try incompat_nodes.append(ctx.allocator, .{
                                .term_start = f_start,
                                .term_len = @intCast(incompat_terms.items.len - f_start),
                                .kind = .feature_dep,
                            });
                            try metas.append(ctx.allocator, .{});
                        } else {
                            const t_start: u32 = @intCast(incompat_terms.items.len);
                            try incompat_terms.append(ctx.allocator, makeVersionTerm(sid, v_idx, v_idx, true));
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, f_decl.name, true));
                            try incompat_terms.append(ctx.allocator, makeFeatureTerm(sid, act_id, false));
                            try incompat_nodes.append(ctx.allocator, .{
                                .term_start = t_start,
                                .term_len = 3,
                                .kind = .feature_dep,
                            });
                            try metas.append(ctx.allocator, .{});
                        }
                    }
                }
            }
        }.run;

        // Expand root (`sid = 0`, `v_idx = 0`) incompatibilities upfront:
        try expandCandidateIncompatibilities(
            self,
            arena_alloc,
            0,
            0,
            default_feat_id,
            &series_domains,
            &series_assign_step,
            &series_expanded_ver,
            &series_seeded_bans,
            &nodes,
            &terms,
            &explain_metas,
        );
        if (self.has_aborted_error) return false;

        var current_dl: u32 = 0;

        // Main bounded PubGrub CDCL loop (`<= MAX_SOLVER_STEPS`):
        while (out_steps.* < MAX_SOLVER_STEPS) {
            out_steps.* += 1;

            // [1] Unit propagation scan across `nodes`:
            var conflict_node_id: ?u32 = null;
            var has_propagated = false;

            var n_idx: usize = 0;
            while (n_idx < nodes.items.len) : (n_idx += 1) {
                const inc_node = nodes.items[n_idx];
                const node_terms = terms.items[inc_node.term_start .. inc_node.term_start + inc_node.term_len];

                var falsified_count: usize = 0;
                var inconclusive_count: usize = 0;
                var unit_term_pos: usize = 0;
                var max_sat_dl: u32 = 0;

                for (node_terms, 0..) |term, t_pos| {
                    if (isFeatureTerm(term)) {
                        const f_key = SeriesFeatKey{
                            .series_id = term.series_id,
                            .feat_id = extractTermFeatureId(term),
                        };
                        const is_pos = isPositiveTerm(term);
                        if (feat_assigns.get(f_key)) |assigned| {
                            if (assigned.is_enabled == is_pos) {
                                max_sat_dl = @max(max_sat_dl, assigned.decision_level);
                            } else {
                                falsified_count += 1;
                                break;
                            }
                        } else {
                            // NOTE: unassigned feature is inconclusive (`true` or `false` still open):
                            inconclusive_count += 1;
                            unit_term_pos = t_pos;
                            if (inconclusive_count > 1) break;
                        }
                    } else {
                        const sid = term.series_id;
                        const cand_len = self.series_list.items[sid].candidates.items.len;
                        const state_cnt = cand_len + 1;
                        const dom_words = series_domains.items[sid];

                        var has_in_term = false;
                        var has_outside_term = false;
                        for (0..state_cnt) |st_i| {
                            if (!isStateBitSet(dom_words, st_i)) continue;
                            if (isStateMatchingVersionTerm(term, cand_len, st_i)) {
                                has_in_term = true;
                            } else {
                                has_outside_term = true;
                            }
                            if (has_in_term and has_outside_term) break;
                        }

                        if (!has_in_term) {
                            falsified_count += 1;
                            break;
                        } else if (has_outside_term) {
                            inconclusive_count += 1;
                            unit_term_pos = t_pos;
                            if (inconclusive_count > 1) break;
                        } else {
                            // Satisfied (`Dom(sid) ⊆ States(term)`): find decision level of latest narrowing on `sid`:
                            const step_i = series_assign_step.items[sid];
                            if (step_i > 0 and step_i <= trail.items.len) {
                                max_sat_dl = @max(max_sat_dl, trail.items[step_i - 1].decision_level);
                            }
                        }
                    }
                }

                if (falsified_count > 0 or inconclusive_count > 1) continue;

                if (inconclusive_count == 0) {
                    // Conflict detected because every term in `inc_node` is satisfied:
                    conflict_node_id = @intCast(n_idx);
                    break;
                }

                // Unit propagation on `node_terms[unit_term_pos]`:
                const unit_term = node_terms[unit_term_pos];
                if (isFeatureTerm(unit_term)) {
                    const f_key = SeriesFeatKey{
                        .series_id = unit_term.series_id,
                        .feat_id = extractTermFeatureId(unit_term),
                    };
                    const is_forced_val = !isPositiveTerm(unit_term);
                    try feat_assigns.put(self.allocator, f_key, .{
                        .is_enabled = is_forced_val,
                        .step_idx = trail.items.len + 1,
                        .decision_level = current_dl,
                    });
                    try trail.append(self.allocator, .{
                        .decision_level = current_dl,
                        .cause_incompat = @intCast(n_idx),
                        .mutation = .{ .feature_val = .{ .key = f_key, .is_enabled = is_forced_val } },
                    });
                    has_propagated = true;
                    break;
                } else {
                    const sid = unit_term.series_id;
                    const cand_len = self.series_list.items[sid].candidates.items.len;
                    const state_cnt = cand_len + 1;
                    const dom_words = series_domains.items[sid];
                    const saved_words = try arena_alloc.dupe(u64, dom_words);

                    for (0..state_cnt) |st_i| {
                        if (isStateBitSet(dom_words, st_i) and isStateMatchingVersionTerm(unit_term, cand_len, st_i)) {
                            clearStateBit(dom_words, st_i);
                        }
                    }
                    try trail.append(self.allocator, .{
                        .decision_level = current_dl,
                        .cause_incompat = @intCast(n_idx),
                        .mutation = .{ .series_domain = .{ .series_id = sid, .prev_words = saved_words } },
                    });
                    series_assign_step.items[sid] = trail.items.len;

                    // If `sid` narrowed to a single concrete candidate `v_only` (`< cand_len`), expand its edges:
                    if (popcountStateWords(dom_words) == 1) {
                        if (firstSetStateBit(dom_words)) |only_st| {
                            if (only_st < cand_len) {
                                try expandCandidateIncompatibilities(
                                    self,
                                    arena_alloc,
                                    sid,
                                    @intCast(only_st),
                                    default_feat_id,
                                    &series_domains,
                                    &series_assign_step,
                                    &series_expanded_ver,
                                    &series_seeded_bans,
                                    &nodes,
                                    &terms,
                                    &explain_metas,
                                );
                                if (self.has_aborted_error) return false;
                            }
                        }
                    }
                    has_propagated = true;
                    break;
                }
            }

            if (conflict_node_id) |init_conf_id| {
                if (current_dl == 0) {
                    // Root-level (`decision_level == 0`) unsatisfiability -> export `ConflictDagExport` & emit `E0010`:
                    nodes.items[init_conf_id].decision_level = 0;
                    const exported = try pkg_conflict_seam.exportLevelZeroConflictDag(
                        self.graph_arena,
                        init_conf_id,
                        nodes.items,
                        terms.items,
                        self.bundle.root_manifest.anchors,
                    );
                    out_conflict_dag.* = exported;
                    try emitUnsatisfiableGraphDiagnosticWithMeta(
                        self.allocator,
                        self.interner,
                        &exported,
                        &self.series_list,
                        explain_metas.items,
                        init_conf_id,
                        Span.init(self.bundle.root_manifest.file_id, 0, 0),
                        self.sink,
                    );
                    return false;
                }

                // CDCL conflict resolution: walk trail backwards to resolve `cur_conf_id` until 1st-UIP / backjump:
                var cur_conf_id = init_conf_id;
                while (out_steps.* < MAX_SOLVER_STEPS) {
                    out_steps.* += 1;
                    const conf_node = nodes.items[cur_conf_id];
                    const conf_terms = terms.items[conf_node.term_start .. conf_node.term_start + conf_node.term_len];

                    // Find the latest trail entry that contributed to satisfying `conf_terms`, and second-highest DL:
                    var latest_step_opt: ?usize = null;
                    var max_dl: u32 = 0;

                    // Undo trail entries that do NOT affect `conf_terms` until we reach the latest affecting entry:
                    for (trail.items, 0..) |t_entry, t_idx| {
                        var has_trail_effect = false;
                        switch (t_entry.mutation) {
                            .feature_val => |fv| {
                                for (conf_terms) |ct| {
                                    if (isFeatureTerm(ct) and ct.series_id == fv.key.series_id and
                                        extractTermFeatureId(ct) == fv.key.feat_id)
                                    {
                                        has_trail_effect = true;
                                        break;
                                    }
                                }
                            },
                            .series_domain => |sd| {
                                for (conf_terms) |ct| {
                                    if (!isFeatureTerm(ct) and ct.series_id == sd.series_id) {
                                        // Check if `sd.prev_words` had at least one state outside `States(ct)`:
                                        const cand_len = self.series_list.items[sd.series_id].candidates.items.len;
                                        for (0..cand_len + 1) |st_i| {
                                            if (isStateBitSet(sd.prev_words, st_i) and
                                                !isStateMatchingVersionTerm(ct, cand_len, st_i))
                                            {
                                                has_trail_effect = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                            },
                        }
                        if (has_trail_effect) {
                            max_dl = @max(max_dl, t_entry.decision_level);
                            if (t_entry.decision_level == max_dl) {
                                latest_step_opt = t_idx;
                            }
                        }
                    }

                    if (max_dl == 0 or latest_step_opt == null) {
                        // Derived conflict holds unconditionally at `decision_level == 0`:
                        while (trail.items.len > 0 and trail.items[trail.items.len - 1].decision_level > 0) {
                            const popped = trail.pop().?;
                            switch (popped.mutation) {
                                .feature_val => |fv| _ = feat_assigns.remove(fv.key),
                                .series_domain => |sd| @memcpy(series_domains.items[sd.series_id], sd.prev_words),
                            }
                        }
                        // Recompute `series_assign_step` after rewind to `0`:
                        @memset(series_assign_step.items, 0);
                        for (trail.items, 0..) |te, ti| {
                            if (te.mutation == .series_domain) {
                                series_assign_step.items[te.mutation.series_domain.series_id] = ti + 1;
                            }
                        }
                        current_dl = 0;
                        break;
                    }

                    const pivot_idx = latest_step_opt.?;
                    // Rewind trail down to `pivot_idx + 1`:
                    while (trail.items.len > pivot_idx + 1) {
                        const popped = trail.pop().?;
                        switch (popped.mutation) {
                            .feature_val => |fv| _ = feat_assigns.remove(fv.key),
                            .series_domain => |sd| @memcpy(series_domains.items[sd.series_id], sd.prev_words),
                        }
                    }

                    const pivot_entry = trail.items[pivot_idx];
                    if (pivot_entry.cause_incompat == null) {
                        // Reached the speculative decision at `pivot_entry.decision_level` (1st-UIP)!
                        // Compute backjump level = highest `decision_level < pivot_entry.decision_level` among other terms:
                        var backjump_dl: u32 = 0;
                        for (trail.items[0..pivot_idx]) |earlier| {
                            if (earlier.decision_level >= pivot_entry.decision_level) continue;
                            var has_earlier_effect = false;
                            switch (earlier.mutation) {
                                .feature_val => |fv| {
                                    for (conf_terms) |ct| {
                                        if (isFeatureTerm(ct) and ct.series_id == fv.key.series_id and
                                            extractTermFeatureId(ct) == fv.key.feat_id)
                                        {
                                            has_earlier_effect = true;
                                            break;
                                        }
                                    }
                                },
                                .series_domain => |sd| {
                                    for (conf_terms) |ct| {
                                        if (!isFeatureTerm(ct) and ct.series_id == sd.series_id) {
                                            has_earlier_effect = true;
                                            break;
                                        }
                                    }
                                },
                            }
                            if (has_earlier_effect) backjump_dl = @max(backjump_dl, earlier.decision_level);
                        }

                        // Undo trail entries above `backjump_dl`:
                        while (trail.items.len > 0 and trail.items[trail.items.len - 1].decision_level > backjump_dl) {
                            const popped = trail.pop().?;
                            switch (popped.mutation) {
                                .feature_val => |fv| _ = feat_assigns.remove(fv.key),
                                .series_domain => |sd| @memcpy(series_domains.items[sd.series_id], sd.prev_words),
                            }
                        }
                        @memset(series_assign_step.items, 0);
                        for (trail.items, 0..) |te, ti| {
                            if (te.mutation == .series_domain) {
                                series_assign_step.items[te.mutation.series_domain.series_id] = ti + 1;
                            }
                        }
                        nodes.items[cur_conf_id].decision_level = backjump_dl;
                        current_dl = backjump_dl;
                        break;
                    }

                    // Generalized resolution of `cur_conf_id` (`C`) with `pivot_entry.cause_incompat` (`D`):
                    const cause_id = pivot_entry.cause_incompat.?;
                    const cause_node = nodes.items[cause_id];
                    const cause_terms = terms.items[cause_node.term_start .. cause_node.term_start + cause_node.term_len];

                    // Pop `pivot_entry` before building resolvent so `series_domains` reflects pre-propagation state:
                    const popped_pivot = trail.pop().?;
                    switch (popped_pivot.mutation) {
                        .feature_val => |fv| _ = feat_assigns.remove(fv.key),
                        .series_domain => |sd| @memcpy(series_domains.items[sd.series_id], sd.prev_words),
                    }

                    var new_terms: std.ArrayListUnmanaged(IncompatTerm) = .empty;
                    defer new_terms.deinit(self.allocator);

                    switch (popped_pivot.mutation) {
                        .feature_val => |fv| {
                            for (conf_terms) |ct| {
                                if (isFeatureTerm(ct) and ct.series_id == fv.key.series_id and
                                    extractTermFeatureId(ct) == fv.key.feat_id) continue;
                                try new_terms.append(self.allocator, ct);
                            }
                            for (cause_terms) |dt| {
                                if (isFeatureTerm(dt) and dt.series_id == fv.key.series_id and
                                    extractTermFeatureId(dt) == fv.key.feat_id) continue;
                                try new_terms.append(self.allocator, dt);
                            }
                        },
                        .series_domain => |sd| {
                            const pivot_sid = sd.series_id;
                            const cand_len = self.series_list.items[pivot_sid].candidates.items.len;
                            const state_cnt = cand_len + 1;

                            // Compute `U = (⋂_{ct on pivot_sid} States(ct)) ∪ (⋂_{dt on pivot_sid} States(dt))`:
                            const words_c = try arena_alloc.alloc(u64, countStateWords(state_cnt));
                            const words_d = try arena_alloc.alloc(u64, countStateWords(state_cnt));
                            @memset(words_c, std.math.maxInt(u64));
                            @memset(words_d, std.math.maxInt(u64));

                            for (conf_terms) |ct| {
                                if (!isFeatureTerm(ct) and ct.series_id == pivot_sid) {
                                    for (0..state_cnt) |st_i| {
                                        if (!isStateMatchingVersionTerm(ct, cand_len, st_i)) clearStateBit(words_c, st_i);
                                    }
                                } else {
                                    try new_terms.append(self.allocator, ct);
                                }
                            }
                            for (cause_terms) |dt| {
                                if (!isFeatureTerm(dt) and dt.series_id == pivot_sid) {
                                    for (0..state_cnt) |st_i| {
                                        if (!isStateMatchingVersionTerm(dt, cand_len, st_i)) clearStateBit(words_d, st_i);
                                    }
                                } else {
                                    try new_terms.append(self.allocator, dt);
                                }
                            }

                            // Encode exact union `U = words_c | words_d` into canonical `IncompatTerm`(s):
                            for (0..words_c.len) |w_i| {
                                words_c[w_i] |= words_d[w_i];
                            }
                            const has_absent_in_u = isStateBitSet(words_c, cand_len);
                            if (has_absent_in_u) {
                                // Emit `S ∉ [gap_lo..gap_hi]` for every maximal gap in `0..cand_len - 1`:
                                var gap_start: ?u32 = null;
                                for (0..cand_len) |st_i| {
                                    if (!isStateBitSet(words_c, st_i)) {
                                        if (gap_start == null) gap_start = @intCast(st_i);
                                    } else if (gap_start) |gs| {
                                        try new_terms.append(
                                            self.allocator,
                                            makeVersionTerm(pivot_sid, gs, @intCast(st_i - 1), false),
                                        );
                                        gap_start = null;
                                    }
                                }
                                if (gap_start) |gs| {
                                    try new_terms.append(
                                        self.allocator,
                                        makeVersionTerm(pivot_sid, gs, @intCast(cand_len - 1), false),
                                    );
                                }
                            } else {
                                var min_u: ?u32 = null;
                                var max_u: u32 = 0;
                                for (0..cand_len) |st_i| {
                                    if (isStateBitSet(words_c, st_i)) {
                                        if (min_u == null) min_u = @intCast(st_i);
                                        max_u = @intCast(st_i);
                                    }
                                }
                                if (min_u) |lo_u| {
                                    try new_terms.append(self.allocator, makeVersionTerm(pivot_sid, lo_u, max_u, true));
                                    var gap_start: ?u32 = null;
                                    var scan_u: u32 = lo_u;
                                    while (scan_u <= max_u) : (scan_u += 1) {
                                        if (!isStateBitSet(words_c, scan_u)) {
                                            if (gap_start == null) gap_start = scan_u;
                                        } else if (gap_start) |gs| {
                                            try new_terms.append(
                                                self.allocator,
                                                makeVersionTerm(pivot_sid, gs, scan_u - 1, false),
                                            );
                                            gap_start = null;
                                        }
                                    }
                                }
                            }
                        },
                    }

                    // Merge/intersect duplicate version terms on the same non-pivot `series_id` to keep clauses compact:
                    var deduped_terms: std.ArrayListUnmanaged(IncompatTerm) = .empty;
                    defer deduped_terms.deinit(self.allocator);
                    var handled_sids: std.AutoHashMapUnmanaged(u32, void) = .empty;
                    defer handled_sids.deinit(self.allocator);

                    for (new_terms.items) |nt| {
                        if (isFeatureTerm(nt)) {
                            var is_dup_ft = false;
                            for (deduped_terms.items) |existing_ft| {
                                if (isFeatureTerm(existing_ft) and existing_ft.series_id == nt.series_id and
                                    existing_ft.flags_and_feat == nt.flags_and_feat)
                                {
                                    is_dup_ft = true;
                                    break;
                                }
                            }
                            if (!is_dup_ft) try deduped_terms.append(self.allocator, nt);
                            continue;
                        }
                        if ((try handled_sids.getOrPut(self.allocator, nt.series_id)).found_existing) continue;
                        const m_sid = nt.series_id;
                        const m_cands = self.series_list.items[m_sid].candidates.items.len;
                        const m_states = m_cands + 1;
                        const inter_w = try arena_alloc.alloc(u64, countStateWords(m_states));
                        @memset(inter_w, std.math.maxInt(u64));
                        for (new_terms.items) |other_t| {
                            if (!isFeatureTerm(other_t) and other_t.series_id == m_sid) {
                                for (0..m_states) |st_i| {
                                    if (!isStateMatchingVersionTerm(other_t, m_cands, st_i)) clearStateBit(inter_w, st_i);
                                }
                            }
                        }
                        if (isStateBitSet(inter_w, m_cands)) {
                            var gap_s: ?u32 = null;
                            for (0..m_cands) |st_i| {
                                if (!isStateBitSet(inter_w, st_i)) {
                                    if (gap_s == null) gap_s = @intCast(st_i);
                                } else if (gap_s) |gs| {
                                    try deduped_terms.append(
                                        self.allocator,
                                        makeVersionTerm(m_sid, gs, @intCast(st_i - 1), false),
                                    );
                                    gap_s = null;
                                }
                            }
                            if (gap_s) |gs| {
                                try deduped_terms.append(
                                    self.allocator,
                                    makeVersionTerm(m_sid, gs, @intCast(m_cands - 1), false),
                                );
                            }
                        } else {
                            var min_m: ?u32 = null;
                            var max_m: u32 = 0;
                            for (0..m_cands) |st_i| {
                                if (isStateBitSet(inter_w, st_i)) {
                                    if (min_m == null) min_m = @intCast(st_i);
                                    max_m = @intCast(st_i);
                                }
                            }
                            if (min_m) |lo_m| {
                                try deduped_terms.append(self.allocator, makeVersionTerm(m_sid, lo_m, max_m, true));
                                var gap_s: ?u32 = null;
                                var sc: u32 = lo_m;
                                while (sc <= max_m) : (sc += 1) {
                                    if (!isStateBitSet(inter_w, sc)) {
                                        if (gap_s == null) gap_s = sc;
                                    } else if (gap_s) |gs| {
                                        try deduped_terms.append(self.allocator, makeVersionTerm(m_sid, gs, sc - 1, false));
                                        gap_s = null;
                                    }
                                }
                            }
                        }
                    }

                    const res_start: u32 = @intCast(terms.items.len);
                    try terms.appendSlice(self.allocator, deduped_terms.items);
                    const derived_id: u32 = @intCast(nodes.items.len);
                    try nodes.append(self.allocator, .{
                        .term_start = res_start,
                        .term_len = @intCast(deduped_terms.items.len),
                        .kind = .derived_conflict,
                        .cause_lhs = cur_conf_id,
                        .cause_rhs = cause_id,
                        .decision_level = current_dl,
                    });
                    try explain_metas.append(self.allocator, .{});
                    cur_conf_id = derived_id;
                }
                continue;
            }

            if (has_propagated) continue;

            // [2] Decision step: find the first active `SeriesKey` (`STATE_ABSENT ∉ Dom(S)`) with `|Dom(S)| > 1`:
            var chosen_sid_opt: ?u32 = null;
            var chosen_ver_idx: u32 = 0;
            for (0..self.series_list.items.len) |sid_usize| {
                const cand_len = self.series_list.items[sid_usize].candidates.items.len;
                const dom_words = series_domains.items[sid_usize];
                if (isStateBitSet(dom_words, cand_len)) continue; // `STATE_ABSENT` still allowed -> inactive.
                const rem_cnt = popcountStateWords(dom_words);
                if (rem_cnt > 1) {
                    chosen_sid_opt = @intCast(sid_usize);
                    // Minimal valid version (`MVS` ordering: pick lowest allowed index `>= 0`!):
                    chosen_ver_idx = @intCast(firstSetStateBit(dom_words).?);
                    break;
                } else if (rem_cnt == 1) {
                    const only_v: u32 = @intCast(firstSetStateBit(dom_words).?);
                    if (only_v < cand_len and !series_expanded_ver.items[sid_usize][only_v]) {
                        try expandCandidateIncompatibilities(
                            self,
                            arena_alloc,
                            @intCast(sid_usize),
                            only_v,
                            default_feat_id,
                            &series_domains,
                            &series_assign_step,
                            &series_expanded_ver,
                            &series_seeded_bans,
                            &nodes,
                            &terms,
                            &explain_metas,
                        );
                        if (self.has_aborted_error) return false;
                        has_propagated = true;
                        break;
                    }
                }
            }
            if (has_propagated) continue;

            if (chosen_sid_opt) |branch_sid| {
                current_dl += 1;
                const dom_words = series_domains.items[branch_sid];
                const saved_words = try arena_alloc.dupe(u64, dom_words);
                @memset(dom_words, 0);
                setStateBit(dom_words, chosen_ver_idx);

                try trail.append(self.allocator, .{
                    .decision_level = current_dl,
                    .cause_incompat = null,
                    .mutation = .{ .series_domain = .{ .series_id = branch_sid, .prev_words = saved_words } },
                });
                series_assign_step.items[branch_sid] = trail.items.len;

                try expandCandidateIncompatibilities(
                    self,
                    arena_alloc,
                    branch_sid,
                    chosen_ver_idx,
                    default_feat_id,
                    &series_domains,
                    &series_assign_step,
                    &series_expanded_ver,
                    &series_seeded_bans,
                    &nodes,
                    &terms,
                    &explain_metas,
                );
                if (self.has_aborted_error) return false;
                continue;
            }

            // [3] All active `SeriesKey`s have singleton versions! Default remaining unassigned features in
            //     inconclusive clauses to `false` so any negative-feature guard propagates cleanly:
            var has_defaulted_feat = false;
            for (nodes.items) |inc_node| {
                const n_terms = terms.items[inc_node.term_start .. inc_node.term_start + inc_node.term_len];
                for (n_terms) |nt| {
                    if (!isFeatureTerm(nt)) continue;
                    const sid = nt.series_id;
                    const cand_len = self.series_list.items[sid].candidates.items.len;
                    if (isStateBitSet(series_domains.items[sid], cand_len)) continue;
                    const f_key = SeriesFeatKey{ .series_id = sid, .feat_id = extractTermFeatureId(nt) };
                    if (!feat_assigns.contains(f_key)) {
                        current_dl += 1;
                        try feat_assigns.put(self.allocator, f_key, .{
                            .is_enabled = false,
                            .step_idx = trail.items.len + 1,
                            .decision_level = current_dl,
                        });
                        try trail.append(self.allocator, .{
                            .decision_level = current_dl,
                            .cause_incompat = null,
                            .mutation = .{ .feature_val = .{ .key = f_key, .is_enabled = false } },
                        });
                        has_defaulted_feat = true;
                        break;
                    }
                }
                if (has_defaulted_feat) break;
            }
            if (has_defaulted_feat) continue;

            // Converged! Export solved model into `mvs_states`:
            for (mvs_states.items) |*st| {
                st.overflow_features.deinit(self.allocator);
                st.active_opt_deps.deinit(self.allocator);
                st.pending_weak.deinit(self.allocator);
            }
            mvs_states.clearRetainingCapacity();

            for (0..self.series_list.items.len) |sid_usize| {
                const cand_len = self.series_list.items[sid_usize].candidates.items.len;
                const dom_words = series_domains.items[sid_usize];
                var node_st = MvsNodeState{};
                if (!isStateBitSet(dom_words, cand_len)) {
                    node_st.is_active = true;
                    node_st.selected_idx = @intCast(firstSetStateBit(dom_words) orelse 0);
                }
                try mvs_states.append(self.allocator, node_st);
            }

            var f_it = feat_assigns.iterator();
            while (f_it.next()) |kv| {
                if (!kv.value_ptr.is_enabled) continue;
                const sid = kv.key_ptr.series_id;
                if (!mvs_states.items[sid].is_active) continue;
                const feat_str = self.interner.get(kv.key_ptr.feat_id);
                if (std.mem.startsWith(u8, feat_str, "dep:")) {
                    const opt_alias = try self.interner.intern(feat_str[4..]);
                    try mvs_states.items[sid].active_opt_deps.put(self.allocator, opt_alias, {});
                } else {
                    _ = try self.activateMvsFeature(mvs_states, sid, kv.key_ptr.feat_id);
                    const cand = self.series_list.items[sid].candidates.items[mvs_states.items[sid].selected_idx];
                    for (cand.dependencies) |d_check| {
                        if (d_check.is_optional and d_check.alias_kebab == kv.key_ptr.feat_id) {
                            try mvs_states.items[sid].active_opt_deps.put(self.allocator, d_check.alias_kebab, {});
                        }
                    }
                }
            }
            return true;
        }

        // Solver step budget (`MAX_SOLVER_STEPS = 100,000`) exhausted:
        try self.sink.emit(.{
            .code = .e0010_unsatisfiable_dependency_graph,
            .severity = .err,
            .primary_span = Span.init(self.bundle.root_manifest.file_id, 0, 0),
            .message = "dependency solver exceeded 100,000 CDCL conflict-resolution steps",
            .notes = &.{"help: tighten version bounds or remove conflicting optional feature cycles in `corex.toml`"},
        });
        return false;
    }
};

// ---------- Monochrome Proof-Tree Renderer (`E0010`) ----------

/// Formats a single `IncompatTerm` into human-readable `"<pkg> <range>"` text.
fn appendFormattedIncompatTerm(
    buf: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    interner: *const StringInterner,
    series_list_opt: ?*const std.ArrayListUnmanaged(SeriesEntry),
    term: IncompatTerm,
) !void {
    if (series_list_opt) |s_list| {
        if (term.series_id < s_list.items.len) {
            const s_entry = &s_list.items[term.series_id];
            const pkg_name = interner.get(s_entry.key.pkg_name_sym);
            try buf.appendSlice(allocator, pkg_name);
            if (isFeatureTerm(term)) {
                const feat_name = interner.get(extractTermFeatureId(term));
                try buf.appendSlice(allocator, if (isPositiveTerm(term)) " [+" else " [-");
                try buf.appendSlice(allocator, feat_name);
                try buf.append(allocator, ']');
                return;
            }
            const cands = s_entry.candidates.items;
            if (!isPositiveTerm(term)) {
                try buf.appendSlice(allocator, " requires ");
            } else {
                try buf.appendSlice(allocator, " ");
            }
            if (term.ver_min < cands.len) {
                var tmp_list: std.ArrayList(u8) = .empty;
                defer tmp_list.deinit(allocator);
                try cands[term.ver_min].version.appendFormatted(&tmp_list, allocator, interner);
                if (term.ver_max != term.ver_min and term.ver_max < cands.len) {
                    try tmp_list.appendSlice(allocator, "..=");
                    try cands[term.ver_max].version.appendFormatted(&tmp_list, allocator, interner);
                }
                try buf.appendSlice(allocator, tmp_list.items);
            } else {
                try buf.appendSlice(allocator, "*");
            }
            return;
        }
    }
    const raw_line = try std.fmt.allocPrint(allocator, "series#{d}[{d}..{d}]", .{
        term.series_id,
        term.ver_min,
        term.ver_max,
    });
    defer allocator.free(raw_line);
    try buf.appendSlice(allocator, raw_line);
}

/// Recursively renders monochrome Unicode box-drawing proof steps (`├─`, `│`, `╰─`) for `dag.nodes[node_idx]`.
fn renderConflictDagBranchRecursive(
    buf: *std.ArrayListUnmanaged(u8),
    allocator: std.mem.Allocator,
    interner: *const StringInterner,
    dag: *const ConflictDagExport,
    series_list_opt: ?*const std.ArrayListUnmanaged(SeriesEntry),
    prefix: []const u8,
    is_last: bool,
    node_idx: u32,
    visited: *std.AutoHashMapUnmanaged(u32, void),
    depth: u32,
) !void {
    if (node_idx >= dag.nodes.len or depth >= 24) return;
    const node = dag.nodes[node_idx];

    try buf.appendSlice(allocator, prefix);
    try buf.appendSlice(allocator, if (is_last) "╰─ " else "├─ ");

    switch (node.kind) {
        .root_pin => try buf.appendSlice(allocator, "root package pin: "),
        .dep_edge => try buf.appendSlice(allocator, "dependency requirement: "),
        .feature_dep => try buf.appendSlice(allocator, "feature requirement: "),
        .exclude_ban => {
            if ((node.flags & 0x01) != 0) {
                try buf.appendSlice(allocator, Glyphs.WARNING ++ " [resolution].exclude security advisory ban: ");
            } else {
                try buf.appendSlice(allocator, "[resolution].exclude ban: ");
            }
        },
        .no_versions => try buf.appendSlice(allocator, "unsatisfied candidate constraint: "),
        .derived_conflict => try buf.appendSlice(allocator, Glyphs.FAILURE ++ " derived conflict: "),
    }

    const t_end = @min(@as(usize, node.term_start) + node.term_len, dag.terms.len);
    if (node.term_start < t_end) {
        for (dag.terms[node.term_start..t_end], 0..) |term, i| {
            if (i > 0) try buf.appendSlice(allocator, ", ");
            try appendFormattedIncompatTerm(buf, allocator, interner, series_list_opt, term);
        }
    } else {
        try buf.appendSlice(allocator, "contradiction at decision level 0");
    }
    try buf.append(allocator, '\n');

    if ((try visited.getOrPut(allocator, node_idx)).found_existing) return;
    if (node.kind == .derived_conflict) {
        const child_prefix = try std.fmt.allocPrint(
            allocator,
            "{s}{s}",
            .{ prefix, if (is_last) "   " else "│  " },
        );
        defer allocator.free(child_prefix);
        try renderConflictDagBranchRecursive(
            buf,
            allocator,
            interner,
            dag,
            series_list_opt,
            child_prefix,
            false,
            node.cause_lhs,
            visited,
            depth + 1,
        );
        try renderConflictDagBranchRecursive(
            buf,
            allocator,
            interner,
            dag,
            series_list_opt,
            child_prefix,
            true,
            node.cause_rhs,
            visited,
            depth + 1,
        );
    }
}

/// Internal helper emitting `E0010` with both `ConflictDagExport` proof lines and `TomlSpanAnchor` labels.
fn emitUnsatisfiableGraphDiagnosticWithMeta(
    allocator: std.mem.Allocator,
    interner: *const StringInterner,
    dag: *const ConflictDagExport,
    series_list_opt: ?*const std.ArrayListUnmanaged(SeriesEntry),
    explain_metas: []const IncompatExplainMeta,
    orig_root_id: u32,
    fallback_span: Span,
    sink: *DiagnosticSink,
) !void {
    _ = orig_root_id;
    const sink_alloc = sink.arena.asAllocator();

    var tree_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer tree_buf.deinit(allocator);
    try tree_buf.appendSlice(allocator, "╭─ PubGrub Conflict Proof Tree\n");

    var visited: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer visited.deinit(allocator);
    try renderConflictDagBranchRecursive(
        &tree_buf,
        allocator,
        interner,
        dag,
        series_list_opt,
        "│ ",
        true,
        dag.root_incompat_id,
        &visited,
        0,
    );

    for (explain_metas) |meta| {
        if (meta.unmatched_req_label) |extra_msg| {
            try tree_buf.appendSlice(allocator, "│ • ");
            try tree_buf.appendSlice(allocator, extra_msg);
            try tree_buf.append(allocator, '\n');
        }
    }

    var labels: std.ArrayListUnmanaged(LabeledSpan) = .empty;
    defer labels.deinit(allocator);
    var primary_span = fallback_span;

    for (dag.nodes) |node| {
        if (node.toml_anchor_id < dag.anchors.len) {
            const anchor = dag.anchors[node.toml_anchor_id];
            if (!anchor.file_id.isNone() and anchor.val_hi >= anchor.key_lo) {
                const sp = Span.init(anchor.file_id, anchor.key_lo, anchor.val_hi);
                const is_primary = labels.items.len == 0;
                if (is_primary) primary_span = sp;
                const lbl_text: []const u8 = switch (node.kind) {
                    .exclude_ban => if ((node.flags & 0x01) != 0)
                        "version banned by security advisory `[resolution].exclude` here"
                    else
                        "version excluded by `[resolution].exclude` here",
                    .feature_dep => "conflicting feature requirement declared here",
                    else => "conflicting dependency requirement declared here",
                };
                try labels.append(allocator, .{
                    .span = sp,
                    .label = lbl_text,
                    .style = if (is_primary) .primary else .secondary,
                });
            }
        }
    }

    if (labels.items.len == 0) {
        for (explain_metas) |meta| {
            if (!meta.span.file_id.isNone()) {
                primary_span = meta.span;
                try labels.append(allocator, .{
                    .span = meta.span,
                    .label = "unsatisfiable dependency requirement here",
                    .style = .primary,
                });
                break;
            }
        }
    }

    const owned_tree_note = try sink_alloc.dupe(u8, std.mem.trimEnd(u8, tree_buf.items, "\n"));
    const owned_labels = try sink_alloc.dupe(LabeledSpan, labels.items);
    const notes_arr = try sink_alloc.dupe([]const u8, &.{
        owned_tree_note,
        "help: relax conflicting version bounds, adjust `[resolution].exclude`, or import coexisting major series with `package = \"…\"`",
    });

    try sink.emit(.{
        .code = .e0010_unsatisfiable_dependency_graph,
        .severity = .err,
        .primary_span = primary_span,
        .message = "unsatisfiable dependency or feature constraint graph",
        .labels = owned_labels,
        .notes = notes_arr,
    });
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Computes the deterministic lowercase sparse-index relative path (`DR-11` §4.1 `IndexPathFor`):
/// `len == 1 -> "1/<n>"`, `len == 2 -> "2/<n>"`, `len == 3 -> "3/<n[0]>/<n>"`, `len >= 4 -> "<n[0..2]>/<n[2..4]>/<n>"`.
pub fn formatSparseIndexRelPath(pkg_name: []const u8, out_buf: *[160]u8) ?[]const u8 {
    if (pkg_name.len == 0 or pkg_name.len > pkg_manifest.MAX_PKG_NAME_BYTES) return null;
    var lower_name: [64]u8 = undefined;
    for (pkg_name, 0..) |byte_val, i| {
        const lo = std.ascii.toLower(byte_val);
        if (!std.ascii.isLower(lo) and !std.ascii.isDigit(lo) and lo != '-') return null;
        lower_name[i] = lo;
    }
    const clean = lower_name[0..pkg_name.len];
    return switch (clean.len) {
        1 => std.fmt.bufPrint(out_buf, "1/{s}", .{clean}) catch null,
        2 => std.fmt.bufPrint(out_buf, "2/{s}", .{clean}) catch null,
        3 => std.fmt.bufPrint(out_buf, "3/{c}/{s}", .{ clean[0], clean }) catch null,
        else => std.fmt.bufPrint(out_buf, "{s}/{s}/{s}", .{ clean[0..2], clean[2..4], clean }) catch null,
    };
}

/// Validates bijective `kebab-case` package naming (`DR-11` §1.4) and allocates its `.cx` `snake_case` identifier.
pub fn canonicalPkgNameToSnakeAlloc(allocator: std.mem.Allocator, raw_pkg_name: []const u8) !?[]u8 {
    return pkg_manifest.canonicalPkgNameToSnakeAlloc(allocator, raw_pkg_name);
}

/// Evaluates a CoreX `@cfg` `target = "…"` dependency predicate against `target_spec` (`E0013` on invalid syntax).
pub fn evaluateManifestTargetCfg(
    allocator: std.mem.Allocator,
    raw_cfg_expr: []const u8,
    target_spec: codegen_abi.TargetSpec,
    manifest_span: Span,
    sink: ?*DiagnosticSink,
) !?bool {
    var local_arena = BumpArena.init(allocator);
    defer local_arena.deinit();
    var local_interner = try StringInterner.init(allocator);
    defer local_interner.deinit();
    const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(target_spec, false);
    return pkg_manifest.validateAndEvalManifestTargetCfg(
        &local_arena,
        &local_interner,
        null,
        raw_cfg_expr,
        &cfg_env,
        manifest_span,
        null,
        sink,
    );
}

/// Renders a `pkg_conflict_seam.ConflictDagExport` into a monochrome Unicode proof tree and emits `E0010`.
pub fn emitUnsatisfiableGraphDiagnostic(
    allocator: std.mem.Allocator,
    interner: *const StringInterner,
    dag: *const ConflictDagExport,
    fallback_span: Span,
    sink: *DiagnosticSink,
) !void {
    return emitUnsatisfiableGraphDiagnosticWithMeta(
        allocator,
        interner,
        dag,
        null,
        &.{},
        dag.root_incompat_id,
        fallback_span,
        sink,
    );
}

/// Builds a canonical `Lockfile` snapshot from a finalized `ResolvedPackageGraph` and optional per-package `.cxi`/cap summaries.
pub fn buildLockfileFromResolvedGraph(
    arena: *BumpArena,
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    manifest_blake3: [32]u8,
    graph: *const ResolvedPackageGraph,
    cxi_digests: ?*const std.AutoHashMapUnmanaged(PackageId, [32]u8),
    cap_summaries: ?*const std.AutoHashMapUnmanaged(PackageId, mir_sast.PackageCapSummary),
) !Lockfile {
    var pkg_node_map: std.AutoHashMapUnmanaged(PackageId, *const ResolvedPackageNode) = .empty;
    defer pkg_node_map.deinit(allocator);
    for (graph.packages) |*node_ptr| {
        try pkg_node_map.put(allocator, node_ptr.pkg_id, node_ptr);
    }

    const lock_pkgs = try arena.allocSlice(LockPackage, graph.packages.len);
    for (graph.packages, 0..) |pkg_node, idx| {
        const feat_ids = try arena.allocSlice(StringId, pkg_node.enabled_features.len);
        for (pkg_node.enabled_features, 0..) |f_str, f_i| {
            feat_ids[f_i] = try interner.intern(f_str);
        }

        const dep_ids = try arena.allocSlice(StringId, pkg_node.dependencies.len);
        for (pkg_node.dependencies, 0..) |dep_b, d_i| {
            if (pkg_node_map.get(dep_b.target_pkg_id)) |target_node| {
                const ver_txt = try target_node.version.formatAlloc(allocator, interner);
                defer allocator.free(ver_txt);
                const dep_ref = try std.fmt.allocPrint(
                    allocator,
                    "{s} {s} ({s})",
                    .{ target_node.canonical_name, ver_txt, target_node.source_uri },
                );
                defer allocator.free(dep_ref);
                dep_ids[d_i] = try interner.intern(dep_ref);
            } else {
                dep_ids[d_i] = try interner.intern(dep_b.alias_kebab);
            }
        }

        var cxi_hash: [32]u8 = pkg_node.locked_cxi_blake3 orelse
            pkg_cxi_seam.computeCxiBlake3(0, 0, &.{});
        if (cxi_digests) |cxi_map| {
            if (cxi_map.get(pkg_node.pkg_id)) |real_cxi| cxi_hash = real_cxi;
        }

        var max_caps: EffectCapabilityMask = .EMPTY;
        var amb_caps: EffectCapabilityMask = .EMPTY;
        if (cap_summaries) |cap_map| {
            if (cap_map.get(pkg_node.pkg_id)) |summary| {
                max_caps = EffectCapabilityMask.fromBits(
                    summary.surface_caps.unionWith(summary.link_ambient_caps).asBits() &
                        EffectCapabilityMask.LOCKFILE_CAP_BITS,
                );
                amb_caps = EffectCapabilityMask.fromBits(
                    summary.link_ambient_caps.asBits() & EffectCapabilityMask.LOCKFILE_CAP_BITS,
                );
            }
        } else if (pkg_node.cap_policy.locked_caps) |locked_c| {
            max_caps = EffectCapabilityMask.fromBits(locked_c.asBits() & EffectCapabilityMask.LOCKFILE_CAP_BITS);
        }

        lock_pkgs[idx] = .{
            .name = pkg_node.canonical_name_sym,
            .version = pkg_node.version,
            .source = try interner.intern(pkg_node.source_uri),
            .checksum = pkg_node.archive_checksum,
            .tree_hash = pkg_node.cxtree_blake3 orelse @splat(0),
            .signature = pkg_node.signature,
            .tlog_index = pkg_node.tlog_index,
            .max_caps = max_caps,
            .ambient_caps = amb_caps,
            .cxi_blake3 = cxi_hash,
            .links = if (pkg_node.native_links_lib) |lnk| try interner.intern(lnk) else .empty,
            .features = feat_ids,
            .dependencies = dep_ids,
        };
    }

    std.mem.sort(LockPackage, lock_pkgs, interner, struct {
        /// Sorts `LockPackage` entries in canonical `corex.lock` v1 order.
        fn lessThan(int_ptr: *const StringInterner, lhs: LockPackage, rhs: LockPackage) bool {
            return pkg_manifest.compareLockPackages(int_ptr, lhs, rhs) == .lt;
        }
    }.lessThan);

    return .{
        .version = pkg_manifest.LOCKFILE_VERSION,
        .root_manifest_blake3 = manifest_blake3,
        .packages = lock_pkgs,
    };
}

/// Resolves workspace/script manifests, inline imports, auto-sync, `[patch]` overrides, features, `corex.lock`, and `.cxtree`s.
pub fn resolveProjectGraph(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    vfs: *vfs_sourcemap.VfsSourceMap,
    manifest_bundle: *const WorkspaceManifestBundle,
    existing_lockfile: ?*const Lockfile,
    options: ResolveOptions,
    sink: *DiagnosticSink,
) !?ResolvedPackageGraph {
    var graph_arena = BumpArena.init(allocator);
    var is_arena_transferred = false;
    defer if (!is_arena_transferred) graph_arena.deinit();

    const is_env_hermetic = if (options.environ_map) |env_m|
        if (env_m.get("COREX_HERMETIC")) |herm_val| std.mem.eql(u8, herm_val, "1") else false
    else
        false;
    const effective_is_locked = options.is_locked or options.is_frozen or is_env_hermetic;
    const effective_is_offline = options.is_offline or options.is_frozen or is_env_hermetic;
    var merged_opts = options;
    merged_opts.is_locked = effective_is_locked;
    merged_opts.is_offline = effective_is_offline;

    const reg_dir_opt: ?[]const u8 = options.local_registry_dir orelse
        if (options.environ_map) |env_m| env_m.get("COREX_REGISTRY_DIR") else null;

    var cache = try pkg_cache.PkgCache.init(
        allocator,
        options.corex_home_dir,
        RESOLVER_CACHE_MAX_ENTRIES,
        RESOLVER_CACHE_MAX_BYTES,
    );
    defer cache.deinit();

    // [1] Validate `--locked` / `--frozen` lockfile presence and manifest `BLAKE3` parity (`E0014`):
    const fallback_span = Span.init(manifest_bundle.root_manifest.file_id, 0, 0);
    if (effective_is_locked) {
        if (existing_lockfile) |lock_doc| {
            if (!std.crypto.timing_safe.eql([32]u8, lock_doc.root_manifest_blake3, manifest_bundle.root_manifest_blake3)) {
                try sink.emit(.{
                    .code = .e0014_lockfile_drift_or_corrupt,
                    .severity = .err,
                    .primary_span = fallback_span,
                    .message = "`corex.lock` is out of sync with `corex.toml` (`root_manifest_blake3` mismatch under `--locked` / `--frozen`)",
                    .notes = &.{"help: run `corex build` without `--locked` / `--frozen` to refresh `corex.lock`"},
                });
                return null;
            }
        } else {
            try sink.emit(.{
                .code = .e0014_lockfile_drift_or_corrupt,
                .severity = .err,
                .primary_span = fallback_span,
                .message = "`corex.lock` is missing while `--locked` / `--frozen` is active",
                .notes = &.{"help: commit `corex.lock` or run `corex build` without `--locked` to generate it"},
            });
            return null;
        }
    }

    const base_cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(options.target_spec, options.is_including_tests);

    // [2] Process inline `use "<spec>" as <alias>;` and unresolved `use <snake_pkg>…;` auto-sync (`DR-11` §1.2):
    var extra_root_deps: std.ArrayListUnmanaged(DependencySpec) = .empty;
    defer extra_root_deps.deinit(allocator);
    var pending_manifest_rhs_edits: std.ArrayListUnmanaged(struct { alias_kebab: []const u8, rhs_toml: []const u8 }) = .empty;
    defer pending_manifest_rhs_edits.deinit(allocator);

    const primary_idx = manifest_bundle.primary_member_index orelse 0;
    const base_root_manifest = if (primary_idx < manifest_bundle.members.len)
        manifest_bundle.members[primary_idx].manifest
    else
        manifest_bundle.root_manifest;

    for (options.inline_imports) |inline_imp| {
        const parsed_inline = (try pkg_manifest.parseInlineUseSpec(
            &graph_arena,
            interner,
            inline_imp.spec_text,
            inline_imp.alias_text,
            inline_imp.spec_span,
            inline_imp.decl_span,
            sink,
        )) orelse return null;

        var is_already_in_manifest = false;
        for (base_root_manifest.dependencies) |existing_dep| {
            if (existing_dep.alias_kebab == parsed_inline.alias_kebab or
                existing_dep.module_snake == parsed_inline.alias_snake)
            {
                is_already_in_manifest = true;
                break;
            }
        }
        if (is_already_in_manifest) continue;

        if (!manifest_bundle.is_script) {
            if (effective_is_locked) {
                try sink.emit(.{
                    .code = .e0014_lockfile_drift_or_corrupt,
                    .severity = .err,
                    .primary_span = inline_imp.spec_span,
                    .message = "inline `use` import requires hoisting into `corex.toml`, which is forbidden under `--locked` / `--frozen`",
                });
                return null;
            }
            const alias_k_str = interner.get(parsed_inline.alias_kebab);
            const pkg_k_str = interner.get(parsed_inline.package_kebab);
            const rhs_str: []const u8 = switch (parsed_inline.source) {
                .registry => |vr| blk_r: {
                    const stripped = if (std.mem.startsWith(u8, inline_imp.spec_text, "registry:"))
                        inline_imp.spec_text[9..]
                    else
                        inline_imp.spec_text;
                    const req_part = if (std.mem.indexOfScalar(u8, stripped, '@')) |at_i| stripped[at_i + 1 ..] else "*";
                    _ = vr;
                    if (std.mem.eql(u8, alias_k_str, pkg_k_str)) {
                        break :blk_r try std.fmt.allocPrint(graph_arena.asAllocator(), "\"{s}\"", .{req_part});
                    }
                    break :blk_r try std.fmt.allocPrint(
                        graph_arena.asAllocator(),
                        "{{ package = \"{s}\", version = \"{s}\" }}",
                        .{ pkg_k_str, req_part },
                    );
                },
                .path => |ps| try std.fmt.allocPrint(
                    graph_arena.asAllocator(),
                    "{{ path = \"{s}\" }}",
                    .{interner.get(ps.rel_path)},
                ),
                .git => |gs| blk_g: {
                    const u_str = interner.get(gs.url);
                    const rv_str = interner.get(gs.rev_value);
                    break :blk_g switch (gs.rev_kind) {
                        .default_head => try std.fmt.allocPrint(graph_arena.asAllocator(), "{{ git = \"{s}\" }}", .{u_str}),
                        .tag => try std.fmt.allocPrint(
                            graph_arena.asAllocator(),
                            "{{ git = \"{s}\", tag = \"{s}\" }}",
                            .{ u_str, rv_str },
                        ),
                        .branch => try std.fmt.allocPrint(
                            graph_arena.asAllocator(),
                            "{{ git = \"{s}\", branch = \"{s}\" }}",
                            .{ u_str, rv_str },
                        ),
                        .rev => try std.fmt.allocPrint(
                            graph_arena.asAllocator(),
                            "{{ git = \"{s}\", rev = \"{s}\" }}",
                            .{ u_str, rv_str },
                        ),
                    };
                },
                .workspace_inherit => "{ workspace = true }",
            };
            try pending_manifest_rhs_edits.append(allocator, .{ .alias_kebab = alias_k_str, .rhs_toml = rhs_str });
        }

        try extra_root_deps.append(allocator, .{
            .alias_kebab = parsed_inline.alias_kebab,
            .module_snake = parsed_inline.alias_snake,
            .package_kebab = parsed_inline.package_kebab,
            .kind = .normal,
            .source = parsed_inline.source,
            .decl_span = inline_imp.spec_span,
        });
    }

    // Check unresolved bare `use <snake_pkg>…;` against sparse registry index for unlocked auto-sync:
    if (options.unresolved_use_roots.len > 0 and !manifest_bundle.is_script) {
        const cached_idx_dir = try std.fmt.allocPrint(allocator, "{s}/index/default", .{cache.cas_root});
        defer allocator.free(cached_idx_dir);
        var probe_json_arena = BumpArena.init(allocator);
        defer probe_json_arena.deinit();

        for (options.unresolved_use_roots) |snake_root| {
            if (pkg_manifest.RESERVED_PKG_NAME_MAP.has(snake_root)) continue;
            const kebab_name = try pkg_manifest.snakeModuleToKebab(&graph_arena, snake_root);
            if (!pkg_manifest.isValidPackageNameKebab(kebab_name)) continue;

            const kebab_id = try interner.intern(kebab_name);
            const snake_id = try interner.intern(snake_root);
            var is_declared = false;
            for (base_root_manifest.dependencies) |d_ex| {
                if (d_ex.alias_kebab == kebab_id or d_ex.module_snake == snake_id) {
                    is_declared = true;
                    break;
                }
            }
            for (extra_root_deps.items) |d_ex| {
                if (d_ex.alias_kebab == kebab_id or d_ex.module_snake == snake_id) {
                    is_declared = true;
                    break;
                }
            }
            if (is_declared) continue;

            var probe_cands: std.ArrayListUnmanaged(CandidateVersionMeta) = .empty;
            defer probe_cands.deinit(allocator);
            var has_in_idx = try loadSparseIndexVersionsFromDir(
                allocator,
                options.io,
                &graph_arena,
                &probe_json_arena,
                interner,
                &base_cfg_env,
                cached_idx_dir,
                kebab_name,
                &probe_cands,
                null,
            );
            if (!has_in_idx and !effective_is_offline) {
                if (reg_dir_opt) |reg_d| {
                    has_in_idx = try loadSparseIndexVersionsFromDir(
                        allocator,
                        options.io,
                        &graph_arena,
                        &probe_json_arena,
                        interner,
                        &base_cfg_env,
                        reg_d,
                        kebab_name,
                        &probe_cands,
                        null,
                    );
                }
            }
            if (!has_in_idx or probe_cands.items.len == 0) continue;

            if (effective_is_locked) {
                try sink.emit(.{
                    .code = .e0014_lockfile_drift_or_corrupt,
                    .severity = .err,
                    .primary_span = fallback_span,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "unresolved import `{s}` matches registry package `{s}`, which cannot be auto-added under `--locked` / `--frozen`",
                        .{ snake_root, kebab_name },
                    ),
                });
                return null;
            }

            // Pick latest non-yanked stable release (or latest non-yanked pre-release if none):
            std.mem.sort(CandidateVersionMeta, probe_cands.items, interner, struct {
                /// Sorts probed versions ascending.
                fn lessThan(int_ptr: *const StringInterner, lhs: CandidateVersionMeta, rhs: CandidateVersionMeta) bool {
                    return SemVer.compare(lhs.version, rhs.version, int_ptr) == .lt;
                }
            }.lessThan);

            var picked_ver: ?SemVer = null;
            var p_i = probe_cands.items.len;
            while (p_i > 0) {
                p_i -= 1;
                const cand = probe_cands.items[p_i];
                if (!cand.is_yanked and cand.version.pre == .empty) {
                    picked_ver = cand.version;
                    break;
                }
            }
            if (picked_ver == null) {
                var p_j = probe_cands.items.len;
                while (p_j > 0) {
                    p_j -= 1;
                    if (!probe_cands.items[p_j].is_yanked) {
                        picked_ver = probe_cands.items[p_j].version;
                        break;
                    }
                }
            }
            if (picked_ver) |sel_ver| {
                const ver_str = try sel_ver.formatAlloc(graph_arena.asAllocator(), interner);
                const ver_req = (try VersionReq.parse(interner, ver_str)) orelse continue;
                const quoted_rhs = try std.fmt.allocPrint(graph_arena.asAllocator(), "\"{s}\"", .{ver_str});
                try pending_manifest_rhs_edits.append(allocator, .{
                    .alias_kebab = try graph_arena.dupe(u8, kebab_name),
                    .rhs_toml = quoted_rhs,
                });
                try extra_root_deps.append(allocator, .{
                    .alias_kebab = kebab_id,
                    .module_snake = snake_id,
                    .package_kebab = kebab_id,
                    .kind = .normal,
                    .source = .{ .registry = ver_req },
                    .decl_span = fallback_span,
                });
            }
        }
    }

    // Apply transactional `corex.toml` auto-sync edits if any were queued:
    var has_auto_synced = false;
    if (pending_manifest_rhs_edits.items.len > 0 and !manifest_bundle.is_script) {
        const target_manifest_path = if (primary_idx < manifest_bundle.members.len)
            manifest_bundle.members[primary_idx].manifest_path
        else
            manifest_bundle.root_manifest_path;
        if (std.Io.Dir.cwd().readFileAlloc(
            options.io,
            target_manifest_path,
            allocator,
            .limited(pkg_manifest.MAX_TOML_BYTES),
        )) |orig_toml| {
            defer allocator.free(orig_toml);
            var cur_patched = try allocator.dupe(u8, orig_toml);
            defer allocator.free(cur_patched);

            for (pending_manifest_rhs_edits.items) |edit_req| {
                var doc_view = try pkg_manifest.parseTomlDocument(
                    allocator,
                    base_root_manifest.file_id,
                    cur_patched,
                    cur_patched,
                    0,
                    0,
                    false,
                    .e0013_invalid_manifest_or_pkg_name,
                    null,
                );
                defer doc_view.deinit(allocator);
                const text_edit = try pkg_manifest.buildAutoAppendDependencyEdit(
                    allocator,
                    &doc_view,
                    interner,
                    edit_req.alias_kebab,
                    edit_req.rhs_toml,
                );
                const fix = SuggestedFix{
                    .message = "auto-sync dependency into `corex.toml`",
                    .edits = (&text_edit)[0..1],
                };
                const next_patched = try pkg_manifest.applyManifestFixesTransactionally(
                    allocator,
                    &doc_view,
                    (&fix)[0..1],
                    interner,
                );
                allocator.free(cur_patched);
                cur_patched = next_patched;
            }
            try codegen_abi.atomicWriteOutputFile(options.io, allocator, target_manifest_path, cur_patched);
            has_auto_synced = true;
        } else |_| {}
    }

    // [3] Initialize `SolverContext`, root `SeriesEntry` (`0`), `[patch]` map, and workspace member map:
    var ctx = SolverContext{
        .allocator = allocator,
        .graph_arena = &graph_arena,
        .interner = interner,
        .vfs = vfs,
        .cache = &cache,
        .bundle = manifest_bundle,
        .existing_lock = existing_lockfile,
        .options = merged_opts,
        .base_cfg_env = base_cfg_env,
        .effective_registry_dir = reg_dir_opt,
        .sink = sink,
        .scratch_json_arena = BumpArena.init(allocator),
    };
    defer ctx.deinit();

    for (manifest_bundle.root_manifest.patches) |p_spec| {
        try ctx.patch_map.put(allocator, p_spec.package_kebab, p_spec);
    }
    if (manifest_bundle.root_manifest.workspace) |ws_cfg| {
        for (ws_cfg.patches) |p_spec| {
            if (!ctx.patch_map.contains(p_spec.package_kebab)) {
                try ctx.patch_map.put(allocator, p_spec.package_kebab, p_spec);
            }
        }
    }
    for (manifest_bundle.members, 0..) |ws_mem, m_idx| {
        if (ws_mem.manifest.package) |pm| {
            try ctx.workspace_pkg_map.put(allocator, pm.name_kebab, @intCast(m_idx));
        }
    }

    const root_pkg_meta: PackageMeta = base_root_manifest.package orelse .{
        .name_kebab = try interner.intern("workspace-root"),
        .module_snake = try interner.intern("workspace_root"),
        .version = .{ .major = 0, .minor = 1, .patch = 0 },
        .edition = try interner.intern(pkg_manifest.DEFAULT_COREX_EDITION),
    };
    const root_dir = if (primary_idx < manifest_bundle.members.len)
        manifest_bundle.members[primary_idx].abs_dir
    else
        manifest_bundle.workspace_root_dir;

    var combined_root_deps = try graph_arena.allocSlice(
        DependencySpec,
        base_root_manifest.dependencies.len + extra_root_deps.items.len,
    );
    @memcpy(combined_root_deps[0..base_root_manifest.dependencies.len], base_root_manifest.dependencies);
    @memcpy(combined_root_deps[base_root_manifest.dependencies.len..], extra_root_deps.items);

    const root_key = SeriesKey{
        .pkg_name_sym = root_pkg_meta.name_kebab,
        .tier = .major_ge_1,
        .source_tag = SOURCE_TAG_WORKSPACE,
        .series_or_source_id = primary_idx,
    };
    var root_series = SeriesEntry{ .series_id = 0, .key = root_key };
    var root_has_fm = base_root_manifest.features.len > 0;
    for (combined_root_deps) |d_item| {
        if (d_item.is_optional) root_has_fm = true;
    }
    try root_series.candidates.append(allocator, .{
        .version = root_pkg_meta.version,
        .source_kind = .workspace_member,
        .source_uri = try interner.intern("root"),
        .host_dir_path = root_dir,
        .corex_req = root_pkg_meta.corex_req,
        .links = root_pkg_meta.links,
        .has_feature_manifest = root_has_fm,
        .features = base_root_manifest.features,
        .dependencies = combined_root_deps,
        .manifest_span = fallback_span,
    });
    for (base_root_manifest.features) |f_decl| {
        _ = try root_series.internFeatureBit(allocator, f_decl.name);
    }
    try ctx.series_list.append(allocator, root_series);
    try ctx.series_map.put(allocator, root_key, 0);

    // [4] Execute Tier-1 `Bounded-MVS`, escalating to Tier-2 `PubGrub CDCL` ONLY on upper-bound / exclude conflict:
    var mvs_states: std.ArrayListUnmanaged(MvsNodeState) = .empty;
    defer {
        for (mvs_states.items) |*st| {
            st.overflow_features.deinit(allocator);
            st.active_opt_deps.deinit(allocator);
            st.pending_weak.deinit(allocator);
        }
        mvs_states.deinit(allocator);
    }

    var solver_steps: u32 = 0;
    var has_used_mvs = true;
    var conflict_dag: ?ConflictDagExport = null;

    const is_mvs_ok = try ctx.runTier1BoundedMvs(&mvs_states, &solver_steps);
    if (ctx.has_aborted_error) return null;

    if (!is_mvs_ok) {
        has_used_mvs = false;
        const is_cdcl_ok = try ctx.runTier2PubGrubCdcl(&mvs_states, &solver_steps, &conflict_dag);
        if (!is_cdcl_ok or ctx.has_aborted_error) return null;
    }

    // [5] Topological post-order sort (`deps` precede `dependents`) & `PackageId` assignment (`0` = root, `>= 2` = deps):
    var topo_sids: std.ArrayListUnmanaged(u32) = .empty;
    defer topo_sids.deinit(allocator);
    const visit_state = try allocator.alloc(u8, mvs_states.items.len);
    defer allocator.free(visit_state);
    @memset(visit_state, 0);

    const topoDfs = struct {
        /// Post-order DFS appending dependencies before dependents.
        fn visit(
            c_ptr: *SolverContext,
            states: []const MvsNodeState,
            v_mark: []u8,
            out_order: *std.ArrayListUnmanaged(u32),
            sid: u32,
        ) !void {
            if (sid >= states.len or !states[sid].is_active or v_mark[sid] == 2) return;
            if (v_mark[sid] == 1) return; // Cycle guard.
            v_mark[sid] = 1;

            const v_idx = states[sid].selected_idx;
            const deps = c_ptr.series_list.items[sid].candidates.items[v_idx].dependencies;
            for (deps) |dep| {
                if (!(try c_ptr.isDepEdgeTargetEnabled(sid, dep))) continue;
                if (dep.is_optional and !states[sid].active_opt_deps.contains(dep.alias_kebab)) continue;
                const res_t = try c_ptr.resolveDepTargetSeries(sid, v_idx, dep);
                try visit(c_ptr, states, v_mark, out_order, res_t.series_id);
            }
            v_mark[sid] = 2;
            try out_order.append(c_ptr.allocator, sid);
        }
    }.visit;

    try topoDfs(&ctx, mvs_states.items, visit_state, &topo_sids, 0);
    if (topo_sids.items.len > MAX_RESOLVED_PACKAGES) {
        try sink.emit(.{
            .code = .e0010_unsatisfiable_dependency_graph,
            .severity = .err,
            .primary_span = fallback_span,
            .message = "resolved dependency graph exceeds maximum 16,384 packages",
        });
        return null;
    }

    // [6] Enforce `--locked` / `--frozen` / `COREX_HERMETIC=1` `(name, version, source)`, count, & feature parity (`E0014`):
    if (effective_is_locked) {
        const lock_doc = existing_lockfile.?;
        if (topo_sids.items.len != lock_doc.packages.len) {
            try sink.emit(.{
                .code = .e0014_lockfile_drift_or_corrupt,
                .severity = .err,
                .primary_span = fallback_span,
                .message = "`corex.lock` package set count is out of sync with resolved graph under `--locked` / `--frozen`",
                .notes = &.{"help: run `corex build` without `--locked` / `--frozen` to refresh `corex.lock`"},
            });
            return null;
        }

        var check_feat_ids: std.ArrayListUnmanaged(StringId) = .empty;
        defer check_feat_ids.deinit(allocator);

        for (topo_sids.items) |sid| {
            const st = &mvs_states.items[sid];
            const s_entry = &ctx.series_list.items[sid];
            const cand = s_entry.candidates.items[st.selected_idx];
            var matched_lp_opt: ?LockPackage = null;
            for (lock_doc.packages) |lp| {
                if (lp.name == s_entry.key.pkg_name_sym and
                    SemVer.eql(lp.version, cand.version, interner) and
                    lp.source == cand.source_uri)
                {
                    matched_lp_opt = lp;
                    break;
                }
            }
            const matched_lp = matched_lp_opt orelse {
                try sink.emit(.{
                    .code = .e0014_lockfile_drift_or_corrupt,
                    .severity = .err,
                    .primary_span = fallback_span,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "resolved package `{s}` (`{s}`) is missing or mismatched in `corex.lock` under `--locked`",
                        .{ interner.get(s_entry.key.pkg_name_sym), interner.get(cand.source_uri) },
                    ),
                });
                return null;
            };

            check_feat_ids.clearRetainingCapacity();
            for (s_entry.feature_ids.items, 0..) |f_id, bit_i| {
                const is_on = if (bit_i < MAX_FEATURES_PER_PKG)
                    st.enabled_bits.isSet(@intCast(bit_i))
                else
                    st.overflow_features.contains(f_id);
                if (is_on) {
                    try check_feat_ids.append(allocator, f_id);
                }
            }
            std.mem.sort(StringId, check_feat_ids.items, interner, struct {
                /// Sorts enabled `StringId` features in ASCII ascending order.
                fn lessThan(int_ptr: *const StringInterner, lhs: StringId, rhs: StringId) bool {
                    return std.mem.order(u8, int_ptr.get(lhs), int_ptr.get(rhs)) == .lt;
                }
            }.lessThan);

            var has_feat_drift = check_feat_ids.items.len != matched_lp.features.len;
            if (!has_feat_drift) {
                for (check_feat_ids.items, 0..) |en_fid, fi| {
                    if (en_fid != matched_lp.features[fi]) {
                        has_feat_drift = true;
                        break;
                    }
                }
            }
            if (has_feat_drift) {
                try sink.emit(.{
                    .code = .e0014_lockfile_drift_or_corrupt,
                    .severity = .err,
                    .primary_span = fallback_span,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "enabled features for package `{s}` differ from `corex.lock` under `--locked` / `--frozen`",
                        .{interner.get(s_entry.key.pkg_name_sym)},
                    ),
                });
                return null;
            }
        }
    }

    var sid_to_pkg_id: std.AutoHashMapUnmanaged(u32, PackageId) = .empty;
    defer sid_to_pkg_id.deinit(allocator);
    var next_ext_pkg_raw: u16 = 2; // Reserve `0 = .root`, `1 = .std_core`.
    for (topo_sids.items) |sid| {
        if (sid == 0) {
            try sid_to_pkg_id.put(allocator, 0, .root);
        } else {
            try sid_to_pkg_id.put(allocator, sid, PackageId.fromInt(next_ext_pkg_raw));
            next_ext_pkg_raw += 1;
        }
    }

    // [7] Verify Native `links` Uniqueness (`E0011`) across all resolved `SeriesKey`s:
    var seen_links: std.AutoHashMapUnmanaged(StringId, u32) = .empty;
    defer seen_links.deinit(allocator);
    var ordered_links_list: std.ArrayListUnmanaged([]const u8) = .empty;
    defer ordered_links_list.deinit(allocator);

    for (topo_sids.items) |sid| {
        const cand = ctx.series_list.items[sid].candidates.items[mvs_states.items[sid].selected_idx];
        if (cand.links == .empty) continue;
        if (seen_links.get(cand.links)) |first_sid| {
            const first_entry = &ctx.series_list.items[first_sid];
            const first_cand = first_entry.candidates.items[mvs_states.items[first_sid].selected_idx];
            const sec_entry = &ctx.series_list.items[sid];
            const first_ver = try first_cand.version.formatAlloc(allocator, interner);
            defer allocator.free(first_ver);
            const sec_ver = try cand.version.formatAlloc(allocator, interner);
            defer allocator.free(sec_ver);
            const lib_str = interner.get(cand.links);

            try sink.emit(.{
                .code = .e0011_native_links_collision,
                .severity = .err,
                .primary_span = fallback_span,
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "conflicting native `links = \"{s}\"` claimed by `{s} v{s}` and `{s} v{s}`",
                    .{
                        lib_str,
                        interner.get(first_entry.key.pkg_name_sym),
                        first_ver,
                        interner.get(sec_entry.key.pkg_name_sym),
                        sec_ver,
                    },
                ),
                .notes = &.{"help: unify to a single version or override one native wrapper via `[patch]` in `corex.toml`"},
            });
            return null;
        }
        try seen_links.put(allocator, cand.links, sid);
        try ordered_links_list.append(allocator, try graph_arena.dupe(u8, interner.get(cand.links)));
    }

    // Collect incoming workspace-owned `allow_caps` / `deny_caps` & dev-only status per `sid` (`[CRITICAL-04]`):
    var sid_allow_union: std.AutoHashMapUnmanaged(u32, EffectCapabilityMask) = .empty;
    defer sid_allow_union.deinit(allocator);
    var sid_deny_union: std.AutoHashMapUnmanaged(u32, EffectCapabilityMask) = .empty;
    defer sid_deny_union.deinit(allocator);
    var sid_has_normal_edge: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer sid_has_normal_edge.deinit(allocator);
    var sid_first_span: std.AutoHashMapUnmanaged(u32, Span) = .empty;
    defer sid_first_span.deinit(allocator);

    for (topo_sids.items) |caller_sid| {
        const v_idx = mvs_states.items[caller_sid].selected_idx;
        const caller_cand = ctx.series_list.items[caller_sid].candidates.items[v_idx];
        const is_caller_workspace = (caller_sid == 0) or (caller_cand.source_kind == .workspace_member);
        for (caller_cand.dependencies) |dep| {
            if (!(try ctx.isDepEdgeTargetEnabled(caller_sid, dep))) continue;
            if (dep.is_optional and !mvs_states.items[caller_sid].active_opt_deps.contains(dep.alias_kebab)) continue;
            const res_t = try ctx.resolveDepTargetSeries(caller_sid, v_idx, dep);
            const t_sid = res_t.series_id;
            if (dep.kind != .dev) {
                try sid_has_normal_edge.put(allocator, t_sid, {});
            }
            if (!sid_first_span.contains(t_sid) and !dep.decl_span.file_id.isNone()) {
                try sid_first_span.put(allocator, t_sid, dep.decl_span);
            }
            if (is_caller_workspace) {
                if (dep.allow_caps) |ac| {
                    const prev = sid_allow_union.get(t_sid) orelse EffectCapabilityMask.EMPTY;
                    try sid_allow_union.put(allocator, t_sid, prev.unionWith(ac));
                }
                if (!dep.deny_caps.isEmpty()) {
                    const prev_d = sid_deny_union.get(t_sid) orelse EffectCapabilityMask.EMPTY;
                    try sid_deny_union.put(allocator, t_sid, prev_d.unionWith(dep.deny_caps));
                }
            }
        }
    }

    // [8] Materialize/verify `.cxtree`, Ed25519 signatures, RFC 6962 proofs, Bao `.obao`, & `--verify-checksums`:
    const out_nodes = try graph_arena.allocSlice(ResolvedPackageNode, topo_sids.items.len);
    for (topo_sids.items, 0..) |sid, out_idx| {
        const s_entry = &ctx.series_list.items[sid];
        const st = &mvs_states.items[sid];
        const cand = s_entry.candidates.items[st.selected_idx];
        const pkg_id = sid_to_pkg_id.get(sid).?;
        const canon_name = interner.get(s_entry.key.pkg_name_sym);

        var stack_ver_buf: [64]u8 = undefined;
        var heap_ver_str: ?[]u8 = null;
        defer if (heap_ver_str) |hv| allocator.free(hv);
        const ver_str: []const u8 = if (cand.version.pre == .empty and cand.version.build == .empty)
            try std.fmt.bufPrint(&stack_ver_buf, "{d}.{d}.{d}", .{
                cand.version.major,
                cand.version.minor,
                cand.version.patch,
            })
        else blk_hv: {
            const hv = try cand.version.formatAlloc(allocator, interner);
            heap_ver_str = hv;
            break :blk_hv hv;
        };

        const owned_snake = if (pkg_manifest.isValidPackageNameKebab(canon_name)) blk_snk: {
            const snk_buf = try graph_arena.allocSlice(u8, canon_name.len);
            for (canon_name, 0..) |ch_byte, i| {
                snk_buf[i] = if (ch_byte == '-') '_' else ch_byte;
            }
            break :blk_snk snk_buf;
        } else try graph_arena.dupe(u8, "pkg_mod");

        // Look up matching `LockPackage` by `(name, version, source)`:
        var matched_lock: ?LockPackage = null;
        if (existing_lockfile) |lock_doc| {
            for (lock_doc.packages) |lp| {
                if (lp.name == s_entry.key.pkg_name_sym and
                    SemVer.eql(lp.version, cand.version, interner) and
                    lp.source == cand.source_uri)
                {
                    matched_lock = lp;
                    break;
                }
            }
        }

        const diag_span = sid_first_span.get(sid) orelse fallback_span;
        var final_tree_hash: ?[32]u8 = cand.expected_tree_blake3 orelse
            if (matched_lock) |ml| ml.tree_hash else null;
        var final_cksum: ?[32]u8 = cand.expected_checksum orelse
            if (matched_lock) |ml| ml.checksum else null;
        const final_sig: ?[64]u8 = cand.signature orelse
            if (matched_lock) |ml| ml.signature else null;
        const final_tlog_idx: ?u64 = cand.tlog_index orelse
            if (matched_lock) |ml| ml.tlog_index else null;
        const locked_cxi: ?[32]u8 = if (matched_lock) |ml| ml.cxi_blake3 else null;

        var lib_rel = cand.lib_root_rel_path;
        var bin_rel = cand.bin_root_rel_path;
        var root_path: []const u8 = "";

        if (cand.source_kind == .workspace_member or cand.source_kind == .local_path) {
            const host_dir = cand.host_dir_path orelse manifest_bundle.workspace_root_dir;
            root_path = try graph_arena.dupe(u8, host_dir);
            if (!manifest_bundle.is_script or sid != 0) {
                if (ingestHostDirectoryAsCxTree(
                    allocator,
                    options.io,
                    &graph_arena,
                    interner,
                    canon_name,
                    host_dir,
                    if (sid == 0) &base_root_manifest else null,
                    null,
                    false,
                    sink,
                    diag_span,
                )) |ing| {
                    allocator.free(ing.cxtree_bytes);
                    final_tree_hash = ing.tree_blake3;
                    if (lib_rel == null) lib_rel = ing.lib_rel;
                    if (bin_rel == null) bin_rel = ing.bin_rel;
                } else |_| {}
            }
        } else {
            // External `.sparse_registry` / `.git_pinned` / `.cxtree_cas` -> MUST resolve & verify in `PkgCache`:
            root_path = try std.fmt.allocPrint(graph_arena.asAllocator(), "/cx/{s}@{s}", .{ canon_name, ver_str });

            var has_verified_in_cache = false;
            if (final_tree_hash) |expected_th| {
                if (cache.readVerifiedCxTreeAlloc(options.io, expected_th, sink, diag_span)) |cxtree_buf| {
                    defer allocator.free(cxtree_buf);
                    const view = vfs_sourcemap.validateCxTreeBytes(allocator, cxtree_buf) catch {
                        try sink.emit(.{
                            .code = .e0015_cache_integrity_mismatch,
                            .severity = .err,
                            .primary_span = diag_span,
                            .message = "cached `.cxtree` failed binary header/entry validation",
                        });
                        return null;
                    };

                    var has_src_root = false;
                    var has_src_lib = false;
                    var has_root = false;
                    var has_src_main = false;
                    var has_main = false;

                    for (view.entries) |t_entry| {
                        const rp = view.asEntryPath(t_entry);
                        if (std.mem.eql(u8, rp, "src/root.cx")) {
                            has_src_root = true;
                        } else if (std.mem.eql(u8, rp, "src/lib.cx")) {
                            has_src_lib = true;
                        } else if (std.mem.eql(u8, rp, "root.cx")) {
                            has_root = true;
                        } else if (std.mem.eql(u8, rp, "src/main.cx")) {
                            has_src_main = true;
                        } else if (std.mem.eql(u8, rp, "main.cx")) {
                            has_main = true;
                        }

                        if (options.is_verifying_checksums or effective_is_offline) {
                            const verified_b = cache.readVerifiedBlobAlloc(
                                options.io,
                                t_entry.file_blake3,
                                sink,
                                diag_span,
                            ) catch |b_err| switch (b_err) {
                                error.CacheIntegrityMismatch => return null,
                                else => {
                                    try sink.emit(.{
                                        .code = if (effective_is_offline)
                                            .e0016_offline_or_fetch_failed
                                        else
                                            .e0015_cache_integrity_mismatch,
                                        .severity = .err,
                                        .primary_span = diag_span,
                                        .message = try std.fmt.allocPrint(
                                            sink.arena.asAllocator(),
                                            "missing cached blob for `{s}` in `{s} v{s}`",
                                            .{ rp, canon_name, ver_str },
                                        ),
                                    });
                                    return null;
                                },
                            };
                            defer allocator.free(verified_b);

                            if (verified_b.len != t_entry.file_size) {
                                try sink.emit(.{
                                    .code = .e0015_cache_integrity_mismatch,
                                    .severity = .err,
                                    .primary_span = diag_span,
                                    .message = try std.fmt.allocPrint(
                                        sink.arena.asAllocator(),
                                        "cached blob byte length for `{s}` in `{s} v{s}` does not match `.cxtree` `file_size`",
                                        .{ rp, canon_name, ver_str },
                                    ),
                                });
                                return null;
                            }

                            if (options.is_verifying_checksums) {
                                const obao_opt = cache.readOptionalBaoOutboardAlloc(
                                    options.io,
                                    t_entry.file_blake3,
                                ) catch {
                                    try sink.emit(.{
                                        .code = .e0015_cache_integrity_mismatch,
                                        .severity = .err,
                                        .primary_span = diag_span,
                                        .message = "corrupt companion `.obao` Bao outboard file in `COREX_HOME`",
                                    });
                                    return null;
                                };
                                if (obao_opt) |obao_bytes| {
                                    defer allocator.free(obao_bytes);
                                    pkg_cache.verifyBaoOutboard(
                                        t_entry.file_blake3,
                                        obao_bytes,
                                        verified_b,
                                        sink,
                                        diag_span,
                                    ) catch return null;
                                } else if (verified_b.len >= pkg_cache.BAO_OUTBOARD_MIN_BYTES) {
                                    try sink.emit(.{
                                        .code = .e0015_cache_integrity_mismatch,
                                        .severity = .err,
                                        .primary_span = diag_span,
                                        .message = "missing companion `.obao` Bao outboard file for `>= 64 KiB` cached blob",
                                    });
                                    return null;
                                }
                            }
                        }
                    }

                    if (lib_rel == null) {
                        if (has_src_root) {
                            lib_rel = "src/root.cx";
                        } else if (has_src_lib) {
                            lib_rel = "src/lib.cx";
                        } else if (has_root) {
                            lib_rel = "root.cx";
                        }
                    }
                    if (bin_rel == null) {
                        if (has_src_main) {
                            bin_rel = "src/main.cx";
                        } else if (has_main) {
                            bin_rel = "main.cx";
                        }
                    }
                    has_verified_in_cache = true;
                } else |c_err| {
                    if (c_err == error.CacheIntegrityMismatch) return null;
                }
            }

            if (!has_verified_in_cache) {
                if (effective_is_offline) {
                    try sink.emit(.{
                        .code = .e0016_offline_or_fetch_failed,
                        .severity = .err,
                        .primary_span = diag_span,
                        .message = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "package `{s} v{s}` is missing from `COREX_HOME` cache in `--offline` / `--frozen` mode",
                            .{ canon_name, ver_str },
                        ),
                    });
                    return null;
                }

                // Ingest from `archive_file_path` (`.tar` or `.cxtree`) or `host_dir_path` in local registry:
                if (cand.archive_file_path) |arch_path| {
                    const arch_bytes = std.Io.Dir.cwd().readFileAlloc(
                        options.io,
                        arch_path,
                        allocator,
                        .limited(64 * 1024 * 1024),
                    ) catch {
                        try sink.emit(.{
                            .code = .e0016_offline_or_fetch_failed,
                            .severity = .err,
                            .primary_span = diag_span,
                            .message = try std.fmt.allocPrint(
                                sink.arena.asAllocator(),
                                "failed to read registry archive `{s}`",
                                .{arch_path},
                            ),
                        });
                        return null;
                    };
                    defer allocator.free(arch_bytes);

                    var actual_arch_b3: [32]u8 = undefined;
                    std.crypto.hash.Blake3.hash(arch_bytes, &actual_arch_b3, .{});
                    if (final_cksum) |exp_ck| {
                        if (!std.crypto.timing_safe.eql([32]u8, actual_arch_b3, exp_ck)) {
                            try sink.emit(.{
                                .code = .e0015_cache_integrity_mismatch,
                                .severity = .err,
                                .primary_span = diag_span,
                                .message = try std.fmt.allocPrint(
                                    sink.arena.asAllocator(),
                                    "archive checksum mismatch for `{s} v{s}`",
                                    .{ canon_name, ver_str },
                                ),
                            });
                            return null;
                        }
                    } else {
                        final_cksum = actual_arch_b3;
                    }

                    if (cand.obao_file_path) |obao_p| {
                        const obao_bytes = std.Io.Dir.cwd().readFileAlloc(
                            options.io,
                            obao_p,
                            allocator,
                            .limited(16 * 1024 * 1024),
                        ) catch {
                            try sink.emit(.{
                                .code = .e0015_cache_integrity_mismatch,
                                .severity = .err,
                                .primary_span = diag_span,
                                .message = "missing companion `.obao` Bao outboard file",
                            });
                            return null;
                        };
                        defer allocator.free(obao_bytes);
                        pkg_cache.verifyBaoOutboard(final_cksum.?, obao_bytes, arch_bytes, sink, diag_span) catch return null;
                    }

                    const tar_res = ingestTarArchiveIntoCache(
                        allocator,
                        options.io,
                        &graph_arena,
                        canon_name,
                        arch_bytes,
                        &cache,
                        sink,
                        diag_span,
                    ) catch |tar_err| switch (tar_err) {
                        error.CacheIntegrityMismatch => return null,
                        else => return tar_err,
                    };
                    defer if (tar_res.manifest_bytes) |mb| allocator.free(mb);
                    if (final_tree_hash) |exp_th| {
                        if (!std.crypto.timing_safe.eql([32]u8, tar_res.tree_blake3, exp_th)) {
                            try sink.emit(.{
                                .code = .e0015_cache_integrity_mismatch,
                                .severity = .err,
                                .primary_span = diag_span,
                                .message = try std.fmt.allocPrint(
                                    sink.arena.asAllocator(),
                                    "`.cxtree` `tree_hash` mismatch for `{s} v{s}`",
                                    .{ canon_name, ver_str },
                                ),
                            });
                            return null;
                        }
                    }
                    final_tree_hash = tar_res.tree_blake3;
                    if (lib_rel == null) lib_rel = tar_res.lib_rel;
                    if (bin_rel == null) bin_rel = tar_res.bin_rel;
                    has_verified_in_cache = true;
                } else if (cand.host_dir_path) |src_dir| {
                    const ing = ingestHostDirectoryAsCxTree(
                        allocator,
                        options.io,
                        &graph_arena,
                        interner,
                        canon_name,
                        src_dir,
                        null,
                        &cache,
                        true,
                        sink,
                        diag_span,
                    ) catch {
                        try sink.emit(.{
                            .code = .e0016_offline_or_fetch_failed,
                            .severity = .err,
                            .primary_span = diag_span,
                            .message = try std.fmt.allocPrint(
                                sink.arena.asAllocator(),
                                "failed to fetch package `{s} v{s}` from registry store",
                                .{ canon_name, ver_str },
                            ),
                        });
                        return null;
                    };
                    defer allocator.free(ing.cxtree_bytes);

                    var raw_tree_b3: [32]u8 = undefined;
                    std.crypto.hash.Blake3.hash(ing.cxtree_bytes, &raw_tree_b3, .{});
                    if (final_cksum) |exp_ck| {
                        if (!std.crypto.timing_safe.eql([32]u8, raw_tree_b3, exp_ck) and
                            !std.crypto.timing_safe.eql([32]u8, ing.tree_blake3, exp_ck))
                        {
                            try sink.emit(.{
                                .code = .e0015_cache_integrity_mismatch,
                                .severity = .err,
                                .primary_span = diag_span,
                                .message = try std.fmt.allocPrint(
                                    sink.arena.asAllocator(),
                                    "registry checksum mismatch for `{s} v{s}`",
                                    .{ canon_name, ver_str },
                                ),
                            });
                            return null;
                        }
                    } else {
                        final_cksum = raw_tree_b3;
                    }
                    if (final_tree_hash) |exp_th| {
                        if (!std.crypto.timing_safe.eql([32]u8, ing.tree_blake3, exp_th)) {
                            try sink.emit(.{
                                .code = .e0015_cache_integrity_mismatch,
                                .severity = .err,
                                .primary_span = diag_span,
                                .message = try std.fmt.allocPrint(
                                    sink.arena.asAllocator(),
                                    "`.cxtree` `tree_hash` mismatch for `{s} v{s}`",
                                    .{ canon_name, ver_str },
                                ),
                            });
                            return null;
                        }
                    }
                    final_tree_hash = ing.tree_blake3;
                    if (lib_rel == null) lib_rel = ing.lib_rel;
                    if (bin_rel == null) bin_rel = ing.bin_rel;
                    has_verified_in_cache = true;
                } else {
                    try sink.emit(.{
                        .code = .e0016_offline_or_fetch_failed,
                        .severity = .err,
                        .primary_span = diag_span,
                        .message = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "unable to fetch `.cxtree` payload for `{s} v{s}`",
                            .{ canon_name, ver_str },
                        ),
                    });
                    return null;
                }
            }

            // Cryptographic Ed25519 publisher signature verification (`E0015` on failure):
            if (cand.publisher_pub_key) |pub_key| {
                const sig = final_sig orelse {
                    try sink.emit(.{
                        .code = .e0015_cache_integrity_mismatch,
                        .severity = .err,
                        .primary_span = diag_span,
                        .message = try std.fmt.allocPrint(
                            sink.arena.asAllocator(),
                            "missing Ed25519 publisher signature for `{s} v{s}`",
                            .{ canon_name, ver_str },
                        ),
                    });
                    return null;
                };
                pkg_cache.verifyPublisherSignature(
                    allocator,
                    canon_name,
                    ver_str,
                    final_tree_hash.?,
                    pub_key,
                    sig,
                    sink,
                    diag_span,
                ) catch return null;
            } else if (cand.signature != null and matched_lock == null) {
                try sink.emit(.{
                    .code = .e0015_cache_integrity_mismatch,
                    .severity = .err,
                    .primary_span = diag_span,
                    .message = "signature provided without publisher Ed25519 public key in sparse index",
                });
                return null;
            }

            // RFC 6962 Transparency-Log Merkle Inclusion Proof verification (`E0015` on split-view / tamper):
            if (cand.tlog_tree_size) |t_size| {
                const t_root = cand.tlog_root orelse {
                    try sink.emit(.{
                        .code = .e0015_cache_integrity_mismatch,
                        .severity = .err,
                        .primary_span = diag_span,
                        .message = "missing RFC 6962 transparency-log root hash",
                    });
                    return null;
                };
                const leaf_idx = final_tlog_idx orelse 0;
                const tree_hex = std.fmt.bytesToHex(final_tree_hash.?, .lower);
                const default_leaf = try std.fmt.allocPrint(
                    allocator,
                    "corex-publish-v1\n{s}\n{s}\n{s}",
                    .{ canon_name, ver_str, &tree_hex },
                );
                defer allocator.free(default_leaf);
                const leaf_payload = cand.tlog_leaf_override orelse default_leaf;
                pkg_cache.verifyMerkleInclusionProof(
                    leaf_idx,
                    t_size,
                    leaf_payload,
                    cand.tlog_proof,
                    t_root,
                    sink,
                    diag_span,
                ) catch return null;
            }
        }

        // Collect sorted `enabled_features` and `declared_features` slices:
        var enabled_list: std.ArrayListUnmanaged([]const u8) = .empty;
        defer enabled_list.deinit(allocator);
        for (s_entry.feature_ids.items, 0..) |f_id, bit_i| {
            const is_on = if (bit_i < MAX_FEATURES_PER_PKG)
                st.enabled_bits.isSet(@intCast(bit_i))
            else
                st.overflow_features.contains(f_id);
            if (is_on) {
                try enabled_list.append(allocator, try graph_arena.dupe(u8, interner.get(f_id)));
            }
        }
        std.mem.sort([]const u8, enabled_list.items, {}, struct {
            /// Sorts enabled feature strings in ASCII ascending order.
            fn lessThan(_: void, lhs: []const u8, rhs: []const u8) bool {
                return std.mem.order(u8, lhs, rhs) == .lt;
            }
        }.lessThan);

        var declared_list: std.ArrayListUnmanaged([]const u8) = .empty;
        defer declared_list.deinit(allocator);
        for (cand.features) |f_decl| {
            try declared_list.append(allocator, try graph_arena.dupe(u8, interner.get(f_decl.name)));
        }
        for (cand.dependencies) |d_spec| {
            if (d_spec.is_optional) {
                const alias_s = interner.get(d_spec.alias_kebab);
                var is_already_decl = false;
                for (declared_list.items) |ex_f| {
                    if (std.mem.eql(u8, ex_f, alias_s)) {
                        is_already_decl = true;
                        break;
                    }
                }
                if (!is_already_decl) {
                    try declared_list.append(allocator, try graph_arena.dupe(u8, alias_s));
                }
            }
        }
        std.mem.sort([]const u8, declared_list.items, {}, struct {
            /// Sorts declared feature strings in ASCII ascending order.
            fn lessThan(_: void, lhs: []const u8, rhs: []const u8) bool {
                return std.mem.order(u8, lhs, rhs) == .lt;
            }
        }.lessThan);

        // Collect direct `ResolvedDepBinding`s for `sid`:
        var bindings_list: std.ArrayListUnmanaged(ResolvedDepBinding) = .empty;
        defer bindings_list.deinit(allocator);
        for (cand.dependencies) |dep| {
            if (!(try ctx.isDepEdgeTargetEnabled(sid, dep))) continue;
            if (dep.is_optional and !st.active_opt_deps.contains(dep.alias_kebab)) continue;
            const res_t = try ctx.resolveDepTargetSeries(sid, st.selected_idx, dep);
            const target_pkg_id = sid_to_pkg_id.get(res_t.series_id) orelse continue;
            try bindings_list.append(allocator, .{
                .alias_sym = dep.module_snake,
                .alias_text = try graph_arena.dupe(u8, interner.get(dep.module_snake)),
                .alias_kebab = try graph_arena.dupe(u8, interner.get(dep.alias_kebab)),
                .target_pkg_id = target_pkg_id,
                .decl_span = dep.decl_span,
                .explicit_allow_caps = dep.allow_caps,
                .explicit_deny_caps = dep.deny_caps,
            });
        }

        const is_third_party = (sid != 0) and (cand.source_kind != .workspace_member);
        const is_dev_only = (sid != 0) and !sid_has_normal_edge.contains(sid);
        const display_label = try std.fmt.allocPrint(graph_arena.asAllocator(), "{s}@{s}", .{ canon_name, ver_str });
        const node_policy = try buildNodeCapPolicy(
            &graph_arena,
            interner,
            manifest_bundle.root_manifest.security,
            s_entry.key.pkg_name_sym,
            display_label,
            is_third_party,
            is_dev_only,
            if (sid_allow_union.get(sid)) |au| au else null,
            sid_deny_union.get(sid) orelse .EMPTY,
            if (matched_lock) |ml| ml.max_caps else null,
            diag_span,
        );

        out_nodes[out_idx] = .{
            .pkg_id = pkg_id,
            .canonical_name_sym = s_entry.key.pkg_name_sym,
            .canonical_name = try graph_arena.dupe(u8, canon_name),
            .default_snake_name = owned_snake,
            .version = cand.version,
            .series_key = s_entry.key,
            .source_kind = cand.source_kind,
            .source_uri = try graph_arena.dupe(u8, interner.get(cand.source_uri)),
            .package_root_path = root_path,
            .lib_root_rel_path = lib_rel,
            .bin_root_rel_path = bin_rel,
            .cxtree_blake3 = final_tree_hash,
            .archive_checksum = final_cksum,
            .signature = final_sig,
            .tlog_index = final_tlog_idx,
            .locked_cxi_blake3 = locked_cxi,
            .enabled_features = try graph_arena.dupe([]const u8, enabled_list.items),
            .declared_features = try graph_arena.dupe([]const u8, declared_list.items),
            .has_feature_manifest = cand.has_feature_manifest,
            .dependencies = try graph_arena.dupe(ResolvedDepBinding, bindings_list.items),
            .native_links_lib = if (cand.links != .empty)
                try graph_arena.dupe(u8, interner.get(cand.links))
            else
                null,
            .cap_policy = node_policy,
            .manifest_span = cand.manifest_span,
        };
    }

    const owned_link_libs = try graph_arena.dupe([]const u8, ordered_links_list.items);
    is_arena_transferred = true;
    return .{
        .arena = graph_arena,
        .packages = out_nodes,
        .root_pkg_id = .root,
        .ordered_native_link_libs = owned_link_libs,
        .has_used_mvs_fast_path = has_used_mvs,
        .solver_steps = solver_steps,
        .has_auto_synced_manifest = has_auto_synced,
        .conflict_dag = conflict_dag,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

comptime {
    std.debug.assert(@sizeOf(SeriesKey) == 12 and @alignOf(SeriesKey) == 4);
    std.debug.assert(std.meta.hasUniqueRepresentation(SeriesKey));
    std.debug.assert(@sizeOf(SemVerCore) == 12 and @alignOf(SemVerCore) == 4);
    std.debug.assert(@sizeOf(SemVer) == 20 and @alignOf(SemVer) == 4);
    std.debug.assert(@sizeOf(IncompatTerm) == 16 and @alignOf(IncompatTerm) == 4);
    std.debug.assert(@sizeOf(IncompatNode) == 24 and @alignOf(IncompatNode) == 4);
    std.debug.assert(@sizeOf(TomlSpanAnchor) == 24 and @alignOf(TomlSpanAnchor) == 4);
}

test "test_pkg_resolver_sparse_index_paths_series_coexistence_and_mvs_weak_features" {
    var rel_buf: [160]u8 = undefined;
    try std.testing.expectEqualStrings("1/z", formatSparseIndexRelPath("z", &rel_buf).?);
    try std.testing.expectEqualStrings("2/io", formatSparseIndexRelPath("io", &rel_buf).?);
    try std.testing.expectEqualStrings("3/t/tls", formatSparseIndexRelPath("tls", &rel_buf).?);
    try std.testing.expectEqualStrings("co/re/corex-http", formatSparseIndexRelPath("corex-http", &rel_buf).?);

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    const pkg_sym = try interner.intern("corex-http");

    // Verify `DR-11` §3.1 `SeriesKey` coexistence across `1.x` vs `2.x`, `0.1.x` vs `0.2.x`, and `0.0.1` vs `0.0.2`:
    const key_v1 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 1, .minor = 4, .patch = 0 });
    const key_v1_9 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 1, .minor = 9, .patch = 2 });
    const key_v2 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 2, .minor = 0, .patch = 0 });
    try std.testing.expectEqual(key_v1, key_v1_9);
    try std.testing.expect(!std.meta.eql(key_v1, key_v2));

    const key_0_1 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 0, .minor = 1, .patch = 0 });
    const key_0_2 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 0, .minor = 2, .patch = 0 });
    try std.testing.expect(!std.meta.eql(key_0_1, key_0_2));

    const key_0_0_1 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 0, .minor = 0, .patch = 1 });
    const key_0_0_2 = SeriesKey.forRegistrySemVer(pkg_sym, .{ .major = 0, .minor = 0, .patch = 2 });
    try std.testing.expect(!std.meta.eql(key_0_0_1, key_0_0_2));

    // Verify `FeatureBitset512` `P2-1` change detection:
    var bs_a = FeatureBitset512{};
    try std.testing.expect(bs_a.setReturningChanged(0));
    try std.testing.expect(!bs_a.setReturningChanged(0));
    try std.testing.expect(bs_a.setReturningChanged(511));
    try std.testing.expect(bs_a.isSet(511));
}

test "test_pkg_resolver_mvs_feature_reenqueue_weak_deps_pubgrub_exclude_and_e0010_e0011" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const scratch_base = ".zig-cache/test_pkg_resolver_e2e";
    std.Io.Dir.cwd().deleteTree(io, scratch_base) catch {};
    defer std.Io.Dir.cwd().deleteTree(io, scratch_base) catch {};

    const reg_dir = scratch_base ++ "/registry";
    const home_dir = scratch_base ++ "/home";
    const app_dir = scratch_base ++ "/app";
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/co/re");
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/packages/corex-codec-1.0.0/src");
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/packages/corex-codec-1.1.0/src");
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/packages/corex-codec-2.0.0/src");
    try std.Io.Dir.cwd().createDirPath(io, reg_dir ++ "/packages/corex-mid-1.0.0/src");
    try std.Io.Dir.cwd().createDirPath(io, home_dir);
    try std.Io.Dir.cwd().createDirPath(io, app_dir ++ "/src");

    // Populate mock registry package sources:
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/packages/corex-codec-1.0.0/src/root.cx",
        .data = "pub fn codec_v1() -> i32 = 10;\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/packages/corex-codec-1.1.0/src/root.cx",
        .data = "pub fn codec_v1() -> i32 = 11;\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/packages/corex-codec-2.0.0/src/root.cx",
        .data = "pub fn codec_v2() -> i32 = 20;\n",
    });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/packages/corex-mid-1.0.0/src/root.cx",
        .data = "pub fn mid_fn() -> i32 = 5;\n",
    });

    // Sparse NDJSON index for `corex-codec` (`1.0.0`, `1.1.0`, `2.0.0`) and `corex-mid` (`1.0.0` with weak `corex-codec?/simd`):
    const codec_ndjson =
        "{\"name\":\"corex-codec\",\"vers\":\"1.0.0\",\"deps\":[],\"features\":{\"default\":[],\"simd\":[]}}\n" ++
        "{\"name\":\"corex-codec\",\"vers\":\"1.1.0\",\"deps\":[],\"features\":{\"default\":[],\"simd\":[]}}\n" ++
        "{\"name\":\"corex-codec\",\"vers\":\"2.0.0\",\"deps\":[],\"features\":{\"default\":[]}}\n";
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/co/re/corex-codec",
        .data = codec_ndjson,
    });
    const mid_ndjson =
        "{\"name\":\"corex-mid\",\"vers\":\"1.0.0\"," ++
        "\"deps\":[{\"name\":\"corex-codec\",\"req\":\"^1.0.0\",\"optional\":true,\"features\":[],\"default_features\":true}]," ++
        "\"features\":{\"default\":[\"fast\"],\"fast\":[\"corex-codec?/simd\"]}}\n";
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = reg_dir ++ "/co/re/corex-mid",
        .data = mid_ndjson,
    });

    // [1] Tier-1 Bounded-MVS + SeriesKey `1.x` & `2.x` coexistence + `[resolution].exclude` forcing Tier-2 PubGrub (`1.1.0`):
    const app_toml_path = app_dir ++ "/corex.toml";
    const app_toml =
        "[package]\n" ++
        "name = \"demo-app\"\n" ++
        "version = \"0.1.0\"\n" ++
        "edition = \"2026\"\n\n" ++
        "[dependencies]\n" ++
        "corex-mid = \"^1.0.0\"\n" ++
        "codec-v1 = { package = \"corex-codec\", version = \"^1.0.0\" }\n" ++
        "codec-v2 = { package = \"corex-codec\", version = \"^2.0.0\" }\n\n" ++
        "[resolution]\n" ++
        "exclude = [\"corex-codec@1.0.0\"] # CVE-test\n";
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = app_toml_path, .data = app_toml });
    try std.Io.Dir.cwd().writeFile(io, .{
        .sub_path = app_dir ++ "/src/main.cx",
        .data = "pub fn main() -> i32 = 0;\n",
    });

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var vfs_map = vfs_sourcemap.VfsSourceMap.init(allocator, &interner);
    defer vfs_map.deinit(io);
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    const cfg_env = symbol_resolver.CfgEnv.fromTargetSpec(codegen_abi.TargetSpec.host(), false);
    const toml_fid = try vfs_map.resolveOrCreatePath(io, app_toml_path, .root);
    var bundle = try pkg_manifest.loadWorkspaceManifestBundle(
        io,
        allocator,
        &interner,
        app_toml_path,
        toml_fid,
        &cfg_env,
        &sink,
    );
    defer bundle.deinit();
    try std.testing.expect(!sink.hasErrors());

    const resolved_opt = try resolveProjectGraph(
        allocator,
        &interner,
        &vfs_map,
        &bundle,
        null,
        .{
            .io = io,
            .local_registry_dir = reg_dir,
            .corex_home_dir = home_dir,
        },
        &sink,
    );
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expect(resolved_opt != null);
    var resolved = resolved_opt.?;
    defer resolved.deinit(allocator);

    // `=1.0.0` was excluded, so Tier-2 PubGrub selected `1.1.0` AND `2.0.0` side-by-side (`4` nodes total: mid, v1.1, v2.0, root):
    try std.testing.expect(!resolved.has_used_mvs_fast_path);
    try std.testing.expectEqual(@as(usize, 4), resolved.packages.len);
    var has_seen_v1_1 = false;
    var has_seen_v2_0 = false;
    for (resolved.packages) |pkg_node| {
        if (std.mem.eql(u8, pkg_node.canonical_name, "corex-codec")) {
            if (pkg_node.version.major == 1 and pkg_node.version.minor == 1) has_seen_v1_1 = true;
            if (pkg_node.version.major == 2 and pkg_node.version.minor == 0) has_seen_v2_0 = true;
        }
    }
    try std.testing.expect(has_seen_v1_1 and has_seen_v2_0);

    // [2] Unsatisfiable version constraint emits `E0010` with monochrome box-drawing proof tree & `ConflictDagExport`:
    const bad_toml =
        "[package]\n" ++
        "name = \"demo-app\"\n" ++
        "version = \"0.1.0\"\n" ++
        "edition = \"2026\"\n\n" ++
        "[dependencies]\n" ++
        "corex-codec = \">=1.0.0, <1.1.0\"\n\n" ++
        "[resolution]\n" ++
        "exclude = [\"corex-codec@1.0.0\"] # CVE-ban\n";
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = app_toml_path, .data = bad_toml });
    const bad_fid = try vfs_map.setOverlay(app_toml_path, bad_toml, .root);
    var bad_sink = DiagnosticSink.init(allocator);
    defer bad_sink.deinit();
    var bad_bundle = try pkg_manifest.loadWorkspaceManifestBundle(
        io,
        allocator,
        &interner,
        app_toml_path,
        bad_fid,
        &cfg_env,
        &bad_sink,
    );
    defer bad_bundle.deinit();

    const conflict_res = try resolveProjectGraph(
        allocator,
        &interner,
        &vfs_map,
        &bad_bundle,
        null,
        .{
            .io = io,
            .local_registry_dir = reg_dir,
            .corex_home_dir = home_dir,
        },
        &bad_sink,
    );
    try std.testing.expect(conflict_res == null);
    try std.testing.expect(bad_sink.hasErrors());
    try std.testing.expectEqual(
        DiagnosticCode.e0010_unsatisfiable_dependency_graph,
        bad_sink.diagnostics.items[0].code,
    );
    try std.testing.expect(!style.hasBannedEmoji(bad_sink.diagnostics.items[0].message));
}

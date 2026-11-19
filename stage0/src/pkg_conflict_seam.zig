//! CoreX Stage-0 PubGrub Conflict Proof DAG & Manifest Span Seam
//!
//! Exports decision-level-0 `IncompatNode` derivation DAGs (`24B`), `IncompatTerm` version/feature
//! intervals (`16B`), and lossless `TomlSpanAnchor` byte spans (`24B`) into `BumpArena` slabs.
//!
//! Serves as the compact Phase 9 Stage-0 seam (`DR-16` §2.3, `DR-20` Seam `#7`) consumed by
//! conflict proof rendering (`E0010`) and Phase 13.2 `CF-IHS` counterfactual solution synthesis.

const std = @import("std");
const mem = @import("mem_foundation.zig");

// ---------------------------------------- TYPES ----------------------------------------

/// Re-exported 64 KiB slab arena owning exported conflict proof DAG slices.
pub const BumpArena = mem.BumpArena;
/// Re-exported 32-bit `VfsSourceMap` file handle.
pub const FileId = mem.FileId;
/// Contiguous 1-byte discriminant classifying PubGrub incompatibility nodes (`0..5`).
pub const IncompatKind = enum(u8) { root_pin = 0, dep_edge = 1, feature_dep = 2, exclude_ban = 3, no_versions = 4, derived_conflict = 5 };
/// Exact 16-byte (`128`-bit, `0` padding) version/feature interval term in an incompatibility.
pub const IncompatTerm = extern struct { series_id: u32 = 0, ver_min: u32 = 0, ver_max: u32 = 0, flags_and_feat: u32 = 0 };

/// Exact 24-byte (`192`-bit, `0` padding) node in a decision-level-0 PubGrub derivation DAG.
pub const IncompatNode = extern struct {
    /// Starting index inside `ConflictDagExport.terms` (`node.term_start .. + node.term_len`).
    term_start: u32 = 0,
    /// Number of `IncompatTerm` entries belonging to this incompatibility clause.
    term_len: u16 = 0,
    /// Origin or resolution category of this incompatibility node.
    kind: IncompatKind = .root_pin,
    /// Bit-packed provenance flags (`bit 0 = has_cve_advisory`).
    flags: u8 = 0,
    /// Left antecedent index in `nodes` when `.derived_conflict`, else dependent `series_id`.
    cause_lhs: u32 = 0,
    /// Right antecedent index in `nodes` when `.derived_conflict`, else target `series_id`.
    cause_rhs: u32 = 0,
    /// Index into `ConflictDagExport.anchors` (`0xFFFF_FFFF` for non-workspace leaves).
    toml_anchor_id: u32 = std.math.maxInt(u32),
    /// Solver decision level at which this incompatibility was derived (`0` at root conflict).
    decision_level: u32 = 0,
};

/// Exact 24-byte (`192`-bit, `0` padding) lossless `corex.toml` or `.cx` frontmatter span anchor.
pub const TomlSpanAnchor = extern struct { file_id: FileId, key_lo: u32, val_lo: u32, val_hi: u32, row_end: u32, eq_col: u16, form: u8, flags: u8 };
/// Read-only slice alias for `IncompatNode` arrays in exported DAG bundles.
const NodeSlice = []const IncompatNode;
/// Read-only slice alias for `IncompatTerm` pools in exported DAG bundles.
const TermSlice = []const IncompatTerm;
/// Read-only slice alias for `TomlSpanAnchor` tables in exported DAG bundles.
const AnchorSlice = []const TomlSpanAnchor;
/// Arena-cloned decision-level-0 conflict proof DAG exported by the Phase 9 package resolver.
pub const ConflictDagExport = struct { root_incompat_id: u32, nodes: NodeSlice, terms: TermSlice, anchors: AnchorSlice };

// ------------------------------------- PUBLIC API --------------------------------------

/// Clones `nodes`, `terms`, and `anchors` into `arena` so resolver scratch buffers never dangle.
pub fn exportLevelZeroConflictDag(arena: *BumpArena, root_id: u32, nodes: NodeSlice, terms: TermSlice, anchors: AnchorSlice) !ConflictDagExport {
    return .{
        .root_incompat_id = root_id,
        .nodes = try arena.dupe(IncompatNode, nodes),
        .terms = try arena.dupe(IncompatTerm, terms),
        .anchors = try arena.dupe(TomlSpanAnchor, anchors),
    };
}

// ---------------------------------------- MAIN -----------------------------------------

comptime {
    std.debug.assert(@sizeOf(IncompatKind) == 1 and @sizeOf(IncompatTerm) == 16 and @alignOf(IncompatTerm) == 4 and @alignOf(IncompatNode) == 4);
    std.debug.assert(@sizeOf(IncompatNode) == 24 and @sizeOf(TomlSpanAnchor) == 24 and @alignOf(TomlSpanAnchor) == 4);
}

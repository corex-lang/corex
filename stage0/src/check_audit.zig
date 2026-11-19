//! Check Idiom Linter, Transactional Multi-Pass Fixer & Supply-Chain Capability Auditor
//!
//! Implements the unified `W0202` (`w0202_non_idiomatic_construct`) zero-false-positive style and
//! idiom linter shared across `corex check`, `corex check --fix`, and `corex lsp`, the bounded
//! multi-pass transactional fix engine (`applyCheckFixesOnDb`), and the `DR-17` §4.4 supply-chain
//! capability audit matrix (`--caps`) and shortest BFS witness explainer (`--explain-caps`).
//!
//! All lints and source patches strictly skip `.std_core`, external `.cxtree`/cached dependencies
//! (`PackageId >= 2`), virtual C import buffers, and `@generated` / `DO NOT EDIT` files, while
//! guaranteeing 100% comment preservation and syntax/error-count rollback safety.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const vfs_sourcemap = @import("vfs_sourcemap.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const symbol_resolver = @import("symbol_resolver.zig");
const type_system = @import("type_system.zig");
const fmt_engine = @import("fmt_engine.zig");
const mir = @import("mir.zig");
const mir_sast = @import("mir_sast.zig");
const pkg_manifest = @import("pkg_manifest.zig");
const pkg_resolver = @import("pkg_resolver.zig");
const codegen_abi = @import("codegen_abi.zig");
const query_db = @import("query_db.zig");
const style = @import("cli/style.zig");
const box_draw = @import("cli/box_draw.zig");
const diagnostic = @import("diag/diagnostic.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const NodeIndex = mem_foundation.NodeIndex;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const TypeId = mem_foundation.TypeId;
const StringInterner = mem_foundation.StringInterner;
const PackageId = vfs_sourcemap.PackageId;
const VfsSourceMap = vfs_sourcemap.VfsSourceMap;
const LineIndex = vfs_sourcemap.LineIndex;
const TriviaKind = syntax_arenas.TriviaKind;
const TriviaPiece = syntax_arenas.TriviaPiece;
const TokenBuffer = syntax_arenas.TokenBuffer;
const CstNodeKind = syntax_arenas.CstNodeKind;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const SymbolIndex = symbol_resolver.SymbolIndex;
const TypeChecker = type_system.TypeChecker;
const EffectCapabilityMask = mir_sast.EffectCapabilityMask;
const FnSummaryStore = mir_sast.FnSummaryStore;
const DefId = query_db.DefId;
const CompilerDb = query_db.CompilerDb;
const StyleConfig = style.StyleConfig;
const Glyphs = style.Glyphs;
const TableColumn = box_draw.TableColumn;
const TableRenderer = box_draw.TableRenderer;
const DiagnosticSink = diagnostic.DiagnosticSink;
const TextEdit = diagnostic.TextEdit;
const SuggestedFix = diagnostic.SuggestedFix;
const TransactionalPatcher = diagnostic.TransactionalPatcher;

// ---------------------------------------- TYPES ----------------------------------------

/// Built-in generic surface type candidate eligible for `W0202` `T?` / `T!E` canonicalization.
const CanonicalStdlibType = union(enum) {
    /// Unshadowed `Option[Inner]` -> `<Inner>?`.
    option: struct {
        /// Token of the `Option` identifier.
        name_tok: TokenIndex,
        /// Closing `]` token of the generic argument list.
        close_bracket_tok: TokenIndex,
        /// Single inner type CST node.
        inner_cst: CstNodeIndex,
    },
    /// Unshadowed `Result[Ok, Err]` -> `<Ok>!<Err>`.
    result: struct {
        /// Token of the `Result` identifier.
        name_tok: TokenIndex,
        /// Closing `]` token of the generic argument list.
        close_bracket_tok: TokenIndex,
        /// Payload (`Ok`) type CST node.
        ok_cst: CstNodeIndex,
        /// Error (`Err`) type CST node.
        err_cst: CstNodeIndex,
    },
};

/// Four-tier `DR-22` surface type precedence hierarchy matching `fmt_engine.zig`.
const SurfaceTypePrec = enum(u8) {
    /// Open bounds, refinements (`is` / `where`), and `distinct` types (`0`).
    tier0_open = 0,
    /// Infix payload-first result type `Ok!Err` (`1`).
    tier1_result = 1,
    /// Prefix reference `&T`, `&mut T`, `own T`, and `~T` types (`2`).
    tier2_prefix = 2,
    /// Postfix optional type `T?` (`3`).
    tier3_postfix = 3,
    /// Primary atomic, nominal, tuple, slice/array, raw pointer `*T`, and callable types (`4`).
    tier4_primary = 4,
};

/// Decoded single-statement `{ return <bool_lit>; }` block used by `W0202` Idiom 6.
const BoolReturnBranchInfo = struct {
    /// Whether the branch returns literal `true` (`false` when returning literal `false`).
    is_true_literal: bool,
};

/// Pre-fix baseline snapshot of an editable `.root` `.cx` file for transactional rollback.
const CandidateFileSnapshot = struct {
    /// Registered `FileId` inside `CompilerDb`.
    file_id: FileId,
    /// Duplicated original UTF-8 source bytes prior to Pass 0.
    original_bytes: []u8,
    /// Raw on-disk `#!` / `---` script prefix (`[0 .. prefix_end_byte)`) when backed by a host script file.
    disk_script_prefix: ?[]u8 = null,
    /// Normalized virtual or host path for VFS overlay updates and atomic disk writes.
    file_path: []u8,
    /// Whether `original_bytes` in `CompilerDb` had `disk_script_prefix` masked to spaces (`blanked_cx_source`).
    was_prefix_masked_in_db: bool = false,
    /// Whether the file was marked open in an editor inside `VfsSourceMap` before patching.
    was_open_in_editor: bool = false,
    /// Whether `file_path` had a real host-disk backing file when `write_to_disk` is active.
    has_disk_backing: bool = false,
    /// Whether this file exhibited CST parse errors in the pre-fix baseline check.
    had_baseline_syntax_errors: bool = false,
    /// Whether at least one `.machine_applicable` fix or format normalization mutated this file.
    is_modified: bool = false,
};

/// Configuration options governing `applyCheckFixesOnDb` (`corex check --fix`).
pub const CheckFixOptions = struct {
    /// Optional Zig `std.Io` handle (required when `write_to_disk == true`).
    io: ?std.Io = null,
    /// Optional `VfsSourceMap` synchronized via `setEditorOverlay` across passes and rollback.
    vfs: ?*VfsSourceMap = null,
    /// When `true`, atomically persists converged modified files to disk via `writeArtifactAtomic`.
    write_to_disk: bool = false,
    /// Optional explicit candidate `FileId` slice (`null` auto-discovers all editable `.root` files).
    candidate_files: ?[]const FileId = null,
};

/// Execution telemetry and rollback outcome returned by `applyCheckFixesOnDb`.
pub const CheckFixReport = struct {
    /// Total `.machine_applicable` `SuggestedFix` bundles applied across all passes (`0` on rollback).
    applied_fix_count: u32 = 0,
    /// Number of editable `.root` files whose final bytes differ from the pre-fix snapshot.
    modified_file_count: u32 = 0,
    /// Number of check/patch passes executed (`1 .. MAX_CHECK_FIX_PASSES`).
    pass_count: u8 = 0,
    /// `true` if the Rollback Guard reverted all edits due to new syntax errors or increased error count.
    was_rolled_back: bool = false,
};

/// Canonical capability bit metadata pairing an `EffectCapabilityMask` bit with its `DR-17` name.
const CapabilityBitSpec = struct {
    /// Single bit inside `EffectCapabilityMask`.
    bit: u16,
    /// Canonical capability identifier (`"unsafe_op"` exclusively for bit 5).
    name: []const u8,
};

/// Pre-formatted 5-column row cells passed to `TableRenderer` in `renderCapabilityAuditTable`.
const AuditRowCells = struct {
    /// Column 0: Package canonical name or standalone stem.
    pkg_cell: []u8,
    /// Column 1: SemVer string (`"0.0.0"` or `"standalone"` in standalone mode).
    ver_cell: []u8,
    /// Column 2: Reachable capabilities (`"[] (pure)"` or `"[fs, net, …]"`).
    reachable_cell: []u8,
    /// Column 3: Exported surface capabilities (`"[] (pure)"` or `"[fs, net, …]"`).
    surface_cell: []u8,
    /// Column 4: Styled policy status (`"• root package"`, `"✓ allowed"`, `"✗ escalated ([…])"`, etc.).
    status_cell: []u8,

    /// Releases all 5 heap-allocated cell slices.
    fn deinit(self: *AuditRowCells, allocator: std.mem.Allocator) void {
        allocator.free(self.pkg_cell);
        allocator.free(self.ver_cell);
        allocator.free(self.reachable_cell);
        allocator.free(self.surface_cell);
        allocator.free(self.status_cell);
    }
};

/// Configuration options governing `renderCapabilityAuditTable` (`corex check --caps`).
pub const CapabilityAuditOptions = struct {
    /// Terminal ANSI/monochrome styling policy (`--color=never` passes `StyleConfig.MONOCHROME`).
    style_config: StyleConfig = StyleConfig.MONOCHROME,
    /// Optional resolved workspace package graph (`null` selects Standalone Single/Multi-File Mode).
    resolved_graph: ?*const pkg_resolver.ResolvedPackageGraph = null,
    /// Optional mapping from `PackageId` to its mounted `FileId` slice in Workspace Mode.
    pkg_files_map: ?*const std.AutoHashMapUnmanaged(PackageId, []const FileId) = null,
    /// Directed dependency edges for workspace capability non-laundering verification.
    cap_edges: []const mir_sast.WorkspacePackageEdge = &.{},
    /// Optional precomputed `verifyWorkspaceCapabilitySandbox` reports (`null` computes internally).
    cap_reports: ?[]const mir_sast.WorkspacePackageCapReport = null,
    /// Optional `corex.lock` document used to verify `LockPackage.max_caps` ceilings.
    lockfile: ?*const pkg_manifest.Lockfile = null,
    /// Explicit `.root` `FileId`s audited in Standalone Mode (`&.{}` auto-collects `.root` files).
    standalone_files: []const FileId = &.{},
    /// Display name for the synthesized package row in Standalone Mode (`""` derives from file path).
    standalone_label: []const u8 = "",
    /// Additional flag indicating caller-observed `@no_alloc`/`@no_panic`/`@max_stack` contract errors.
    has_contract_errors: bool = false,
};

/// Summary counters and exit-code gate returned by `renderCapabilityAuditTable`.
pub const CapabilityAuditReport = struct {
    /// Number of packages (or standalone target) verified and rendered in the table.
    package_count: u32 = 0,
    /// Number of packages exhibiting policy denials or `corex.lock` `max_caps` escalations.
    escalation_count: u32 = 0,
    /// Count of verified `@no_alloc` and/or `@no_panic` functions across audited files.
    verified_contract_fn_count: u32 = 0,
    /// `true` when `escalation_count > 0` or SAST contract errors exist (`CLI` must exit `1`).
    has_escalation: bool = false,
};

/// Single rendered node in a shortest capability witness chain (`--explain-caps`).
const WitnessHopNode = struct {
    /// Source file containing this function, call site, or dormant `@cfg` item.
    file_id: FileId,
    /// Primary source byte offset for `line:col` resolution.
    byte_offset: u32,
    /// Human-readable function signature or qualified item label.
    display_label: []u8,
};

/// Configuration options governing `renderExplainCapsReport` (`corex check --explain-caps`).
pub const ExplainCapsOptions = struct {
    /// Terminal ANSI/monochrome styling policy.
    style_config: StyleConfig = StyleConfig.MONOCHROME,
    /// Optional `VfsSourceMap` for normalized file paths and cached `LineIndex` lookups.
    vfs: ?*VfsSourceMap = null,
    /// Optional resolved workspace package graph (`null` operates in Standalone Mode).
    resolved_graph: ?*const pkg_resolver.ResolvedPackageGraph = null,
    /// Optional mapping from `PackageId` to its mounted `FileId` slice in Workspace Mode.
    pkg_files_map: ?*const std.AutoHashMapUnmanaged(PackageId, []const FileId) = null,
    /// Explicit `.root` `FileId`s inspected in Standalone Mode (`&.{}` auto-collects `.root` files).
    standalone_files: []const FileId = &.{},
    /// Package display label used in Standalone Mode when `resolved_graph == null`.
    standalone_name: []const u8 = "root",
    /// Package version label used in Standalone Mode when `resolved_graph == null`.
    standalone_version: []const u8 = "0.0.0",
    /// Optional `[pkg]` CLI selector (`null` or `""` defaults to the `.root` package).
    target_pkg_arg: ?[]const u8 = null,
    /// Optional `[cap]` CLI filter (`null` or `""` explains every reachable/dormant capability).
    target_cap_arg: ?[]const u8 = null,
};

/// Execution summary returned by `renderExplainCapsReport`.
pub const ExplainCapsReport = struct {
    /// Number of capability witness trees rendered into `writer`.
    rendered_witness_count: u32 = 0,
    /// `true` if `E0001` was emitted due to an unknown `[pkg]` or `[cap]` CLI argument.
    has_cli_error: bool = false,
};

/// Deterministic comparator sorting resolved dependency rows by `(canonical_name ASC, version ASC)`.
const DependencySortCtx = struct {
    /// Resolved package graph nodes.
    pkgs: []const pkg_resolver.ResolvedPackageNode,
    /// Shared string interner for SemVer pre-release comparisons.
    interner: *const StringInterner,

    /// Orders dependency indices by `(canonical_name ASC, version ASC)`.
    fn lessThan(ctx: DependencySortCtx, lhs_idx: usize, rhs_idx: usize) bool {
        const lhs = ctx.pkgs[lhs_idx];
        const rhs = ctx.pkgs[rhs_idx];
        const name_ord = std.mem.order(u8, lhs.canonical_name, rhs.canonical_name);
        if (name_ord != .eq) return name_ord == .lt;
        return pkg_manifest.SemVer.compare(lhs.version, rhs.version, ctx.interner) == .lt;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum synergistic check-and-patch iterations executed by `applyCheckFixesOnDb` (`DR-14` §2.5).
pub const MAX_CHECK_FIX_PASSES: u8 = 4;

/// Maximum leading trivia/comment bytes scanned after frontmatter by `isGeneratedSourceHeader`.
pub const GENERATED_HEADER_SCAN_BYTES: usize = 4096;

/// Upper bound on cross-package witness recursion depth in `renderExplainCapsReport` (`AGENTS.md` §2).
pub const MAX_WITNESS_CHAIN_DEPTH: usize = 32;

/// Canonical `EffectCapabilityMask` bit-order table using `"unsafe_op"` (`DR-17` §4.2 & §4.4).
const CANONICAL_AUDIT_CAPS = [_]CapabilityBitSpec{
    .{ .bit = 1 << 0, .name = "fs" },
    .{ .bit = 1 << 1, .name = "net" },
    .{ .bit = 1 << 2, .name = "env" },
    .{ .bit = 1 << 3, .name = "process" },
    .{ .bit = 1 << 4, .name = "ffi" },
    .{ .bit = 1 << 5, .name = "unsafe_op" },
    .{ .bit = 1 << 8, .name = "clock" },
    .{ .bit = 1 << 9, .name = "entropy" },
};

/// Additional opaque-call capability bit included when formatting policy escalation masks.
const OPAQUE_ESCALATION_CAP = CapabilityBitSpec{
    .bit = EffectCapabilityMask.INDIRECT_OPAQUE_BIT,
    .name = "indirect_opaque",
};

/// Canonical 5-column layout descriptor for `corex check --caps` (`DR-17` §4.4).
const AUDIT_TABLE_COLUMNS = [5]TableColumn{
    .{ .header = "Package", .alignment = .left },
    .{ .header = "Version", .alignment = .left },
    .{ .header = "Reachable Caps", .alignment = .left },
    .{ .header = "Surface Caps", .alignment = .left },
    .{ .header = "Policy Status", .alignment = .left },
};

// -------------------------------------- INTERNALS --------------------------------------

/// Returns `true` if `comment_slice` contains `"@generated"` or `"DO NOT EDIT"` as an ASCII substring.
inline fn hasGeneratedMarkerSubstring(comment_slice: []const u8) bool {
    return std.mem.indexOf(u8, comment_slice, "@generated") != null or
        std.mem.indexOf(u8, comment_slice, "DO NOT EDIT") != null;
}

/// Returns `true` if `line_bytes` (without `\n`) equals `"---"` followed only by spaces/tabs/CR.
fn isFrontmatterFenceLine(line_bytes: []const u8) bool {
    if (!std.mem.startsWith(u8, line_bytes, "---")) return false;
    for (line_bytes[3..]) |ch_byte| {
        if (ch_byte != ' ' and ch_byte != '\t' and ch_byte != '\r') return false;
    }
    return true;
}

/// Scans a TOML slice (`[0 .. toml_slice.len)`) for unquoted `#` comments containing `@generated` or `DO NOT EDIT`.
fn hasGeneratedMarkerInTomlComments(toml_slice: []const u8) bool {
    const scan_end = @min(toml_slice.len, GENERATED_HEADER_SCAN_BYTES);
    var in_basic = false;
    var in_literal = false;
    var in_ml_basic = false;
    var in_ml_literal = false;
    var cursor: usize = 0;

    while (cursor < scan_end) {
        if (in_ml_basic) {
            if (toml_slice[cursor] == '\\' and cursor + 1 < scan_end) {
                cursor += 2;
                continue;
            }
            if (cursor + 2 < scan_end and toml_slice[cursor] == '"' and
                toml_slice[cursor + 1] == '"' and toml_slice[cursor + 2] == '"')
            {
                in_ml_basic = false;
                cursor += 3;
                continue;
            }
            cursor += 1;
            continue;
        }
        if (in_ml_literal) {
            if (cursor + 2 < scan_end and toml_slice[cursor] == '\'' and
                toml_slice[cursor + 1] == '\'' and toml_slice[cursor + 2] == '\'')
            {
                in_ml_literal = false;
                cursor += 3;
                continue;
            }
            cursor += 1;
            continue;
        }
        if (in_basic) {
            if (toml_slice[cursor] == '\\' and cursor + 1 < scan_end) {
                cursor += 2;
                continue;
            }
            if (toml_slice[cursor] == '"' or toml_slice[cursor] == '\n') {
                in_basic = false;
            }
            cursor += 1;
            continue;
        }
        if (in_literal) {
            if (toml_slice[cursor] == '\'' or toml_slice[cursor] == '\n') {
                in_literal = false;
            }
            cursor += 1;
            continue;
        }

        const ch_byte = toml_slice[cursor];
        if (ch_byte == '"') {
            if (cursor + 2 < scan_end and toml_slice[cursor + 1] == '"' and toml_slice[cursor + 2] == '"') {
                in_ml_basic = true;
                cursor += 3;
            } else {
                in_basic = true;
                cursor += 1;
            }
            continue;
        }
        if (ch_byte == '\'') {
            if (cursor + 2 < scan_end and toml_slice[cursor + 1] == '\'' and toml_slice[cursor + 2] == '\'') {
                in_ml_literal = true;
                cursor += 3;
            } else {
                in_literal = true;
                cursor += 1;
            }
            continue;
        }
        if (ch_byte == '#') {
            const rest = toml_slice[cursor..scan_end];
            const nl_rel = std.mem.indexOfScalar(u8, rest, '\n') orelse rest.len;
            if (hasGeneratedMarkerSubstring(rest[0..nl_rel])) return true;
            cursor += nl_rel + @intFromBool(cursor + nl_rel < scan_end);
            continue;
        }
        cursor += 1;
    }
    return false;
}

/// Scans an optional `--- … ---` script frontmatter block at `start_offset`, checking `#` TOML comments for markers.
fn scanOptionalScriptFrontmatter(
    source: []const u8,
    start_offset: usize,
) struct {
    /// Post-fence byte index (or `start_offset` when no complete `--- … ---` block is present).
    next_offset: usize,
    /// `true` if a `#` TOML comment inside `--- … ---` carried `@generated` or `DO NOT EDIT`.
    has_generated_marker: bool,
} {
    var cursor = start_offset;
    while (cursor < source.len and (source[cursor] == ' ' or source[cursor] == '\t' or
        source[cursor] == '\r' or source[cursor] == '\n')) : (cursor += 1)
    {}
    const first_nl_rel = std.mem.indexOfScalar(u8, source[cursor..], '\n') orelse {
        return .{ .next_offset = start_offset, .has_generated_marker = false };
    };
    if (!isFrontmatterFenceLine(source[cursor .. cursor + first_nl_rel])) {
        return .{ .next_offset = start_offset, .has_generated_marker = false };
    }

    const body_start = cursor + first_nl_rel + 1;
    var line_start = body_start;
    while (line_start < source.len) {
        const next_nl_rel = std.mem.indexOfScalar(u8, source[line_start..], '\n') orelse (source.len - line_start);
        const line_slice = source[line_start .. line_start + next_nl_rel];
        if (isFrontmatterFenceLine(line_slice)) {
            return .{
                .next_offset = @min(source.len, line_start + next_nl_rel + 1),
                .has_generated_marker = hasGeneratedMarkerInTomlComments(source[body_start..line_start]),
            };
        }
        if (line_start + next_nl_rel >= source.len) break;
        line_start += next_nl_rel + 1;
    }
    return .{ .next_offset = start_offset, .has_generated_marker = false };
}

/// Returns `true` when `checker`'s file is an editable `.root` `.cx` source eligible for `W0202` linting.
fn isEditableRootLintFile(checker: *const TypeChecker) bool {
    if (checker.is_stdlib_file) return false;
    if (checker.file_id.isNone() or checker.file_id.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) {
        return false;
    }
    if (checker.sym_table.getFilePackageId(checker.file_id) != .root) return false;
    return !isGeneratedSourceHeader(checker.source);
}

/// Reads the recorded `TypeId` of `node_id` from `checker.node_types` (`.err_ty` when out-of-bounds).
inline fn getRecordedNodeType(checker: *const TypeChecker, node_id: NodeIndex) TypeId {
    if (!node_id.isNone() and node_id.asInt() < checker.node_types.len) {
        return checker.node_types[node_id.asInt()];
    }
    return .err_ty;
}

/// Returns `true` if `W0202` (`allow_idiom_w0202`) is suppressed at `span` via `@allow(…)`.
inline fn isW0202SuppressedAtSpan(checker: *const TypeChecker, span: Span) bool {
    if (checker.active_allow_mask.allow_idiom_w0202) return true;
    if (checker.sym_table.getScopeAllowMask(checker.current_scope).allow_idiom_w0202) return true;
    return checker.getAllowedMaskAtSpan(span).allow_idiom_w0202;
}

/// Returns `true` if `kind` is a line, doc, module-doc, or block comment trivia piece.
inline fn isCommentTriviaKind(kind: TriviaKind) bool {
    return switch (kind) {
        .line_comment, .doc_comment, .module_doc_comment, .block_comment => true,
        else => false,
    };
}

/// Returns `true` if any `TriviaPiece` in `pieces` is a comment (or coalesced trivia containing `/` + `/`/`*`).
fn hasCommentInTriviaSlice(source: []const u8, pieces: []const TriviaPiece) bool {
    for (pieces) |piece| {
        if (isCommentTriviaKind(piece.kind)) return true;
        if ((piece.flags & syntax_arenas.TRIVIA_FLAG_COALESCED) != 0) {
            const start_idx: usize = @min(@as(usize, piece.byte_offset), source.len);
            const end_idx: usize = @min(start_idx + @as(usize, piece.byte_len), source.len);
            const raw_slice = source[start_idx..end_idx];
            if (std.mem.indexOf(u8, raw_slice, "//") != null or
                std.mem.indexOf(u8, raw_slice, "/*") != null)
            {
                return true;
            }
        }
    }
    return false;
}

/// Scans `[piece_start .. piece_end)` in `source` for any `//…` or `/*…*/` comment overlapping `[start_byte, end_byte)`.
fn hasCoalescedCommentOverlappingRange(
    source: []const u8,
    piece_start: u32,
    piece_end: u32,
    start_byte: u32,
    end_byte: u32,
) bool {
    const scan_lo: usize = @min(@as(usize, piece_start), source.len);
    const scan_hi: usize = @min(@as(usize, piece_end), source.len);
    var cursor: usize = scan_lo;
    while (cursor + 1 < scan_hi) {
        if (source[cursor] == '/' and source[cursor + 1] == '/') {
            const comment_lo: u32 = @intCast(cursor);
            cursor += 2;
            while (cursor < scan_hi and source[cursor] != '\n') : (cursor += 1) {}
            const comment_hi: u32 = @intCast(cursor);
            if (comment_hi > start_byte and comment_lo < end_byte) return true;
            continue;
        }
        if (source[cursor] == '/' and source[cursor + 1] == '*') {
            const comment_lo: u32 = @intCast(cursor);
            cursor += 2;
            var block_depth: usize = 1;
            while (cursor + 1 < scan_hi and block_depth > 0) {
                if (source[cursor] == '/' and source[cursor + 1] == '*') {
                    block_depth += 1;
                    cursor += 2;
                } else if (source[cursor] == '*' and source[cursor + 1] == '/') {
                    block_depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
            if (block_depth > 0) cursor = scan_hi;
            const comment_hi: u32 = @intCast(cursor);
            if (comment_hi > start_byte and comment_lo < end_byte) return true;
            continue;
        }
        cursor += 1;
    }
    return false;
}

/// Returns `true` if `slice` begins with horizontal whitespace followed immediately by `\n` or `\r\n`.
fn hasLeadingBlankLine(slice: []const u8) bool {
    var cursor: usize = 0;
    while (cursor < slice.len) : (cursor += 1) {
        const ch_byte = slice[cursor];
        if (ch_byte == '\n') return true;
        if (ch_byte == '\r') return cursor + 1 < slice.len and slice[cursor + 1] == '\n';
        if (ch_byte != ' ' and ch_byte != '\t') return false;
    }
    return false;
}

/// Replaces the leading `raw_prefix.len` bytes of `full_source` with `raw_prefix` in a fresh owned buffer.
fn spliceRawPrefixOntoSource(
    allocator: std.mem.Allocator,
    raw_prefix: []const u8,
    full_source: []const u8,
) ![]u8 {
    if (raw_prefix.len == 0 or full_source.len < raw_prefix.len) {
        return allocator.dupe(u8, full_source);
    }
    const out_buf = try allocator.alloc(u8, full_source.len);
    @memcpy(out_buf[0..raw_prefix.len], raw_prefix);
    @memcpy(out_buf[raw_prefix.len..], full_source[raw_prefix.len..]);
    return out_buf;
}

/// Returns `true` if `ch_byte` can continue an ASCII/UTF-8 identifier or keyword lexeme.
inline fn isIdentifierByte(ch_byte: u8) bool {
    return std.ascii.isAlphanumeric(ch_byte) or ch_byte == '_' or ch_byte >= 0x80;
}

/// Appends the direct child `CstNodeIndex` items of `parent_idx` into `out_children`.
fn collectDirectCstChildren(
    allocator: std.mem.Allocator,
    cst_arena: *const LosslessCstArena,
    parent_idx: CstNodeIndex,
    out_children: *std.ArrayListUnmanaged(CstNodeIndex),
) !void {
    if (parent_idx.isNone() or parent_idx.asInt() >= cst_arena.countNodes()) return;
    const parent_node = cst_arena.getNode(parent_idx);
    if (parent_node.subtree_size <= 1) return;
    const end_idx = @min(
        @as(usize, parent_idx.asInt()) + @as(usize, parent_node.subtree_size),
        cst_arena.countNodes(),
    );
    var cursor: usize = @as(usize, parent_idx.asInt()) + 1;
    while (cursor < end_idx) {
        const child_id = CstNodeIndex.fromInt(@intCast(cursor));
        const child_node = cst_arena.getNode(child_id);
        try out_children.append(allocator, child_id);
        cursor += @max(@as(usize, child_node.subtree_size), 1);
    }
}

/// Finds the first non-synthesized leaf `TokenIndex` inside `subtree_idx` (`.none` if empty).
fn findFirstRealTokenInSubtree(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) TokenIndex {
    if (subtree_idx.isNone() or subtree_idx.asInt() >= cst_arena.countNodes()) return .none;
    const root_node = cst_arena.getNode(subtree_idx);
    const end_idx = @min(
        @as(usize, subtree_idx.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var cursor: usize = subtree_idx.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
            !leaf.token.isNone() and leaf.token.asInt() < tok_count)
        {
            const tok_rec = token_buffer.getToken(leaf.token);
            if (!tok_rec.flags.is_synthesized and tok_rec.kind != .eof) {
                return leaf.token;
            }
        }
    }
    return .none;
}

/// Finds the last non-synthesized leaf `TokenIndex` inside `subtree_idx` (`.none` if empty).
fn findLastRealTokenInSubtree(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) TokenIndex {
    if (subtree_idx.isNone() or subtree_idx.asInt() >= cst_arena.countNodes()) return .none;
    const root_node = cst_arena.getNode(subtree_idx);
    const end_idx = @min(
        @as(usize, subtree_idx.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var last_tok: TokenIndex = .none;
    var cursor: usize = subtree_idx.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (leaf.subtree_size <= 1 and !leaf.flags.is_missing_or_injected and
            !leaf.token.isNone() and leaf.token.asInt() < tok_count)
        {
            const tok_rec = token_buffer.getToken(leaf.token);
            if (!tok_rec.flags.is_synthesized and tok_rec.kind != .eof) {
                last_tok = leaf.token;
            }
        }
    }
    return last_tok;
}

/// Computes the exact source `Span` from the first real token to the last real token of `subtree_idx`.
fn getCstSubtreeSpan(
    file_id: FileId,
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) ?Span {
    const first_tok = findFirstRealTokenInSubtree(cst_arena, token_buffer, subtree_idx);
    const last_tok = findLastRealTokenInSubtree(cst_arena, token_buffer, subtree_idx);
    if (first_tok.isNone() or last_tok.isNone()) return null;
    const first_rec = token_buffer.getToken(first_tok);
    const last_rec = token_buffer.getToken(last_tok);
    if (last_rec.byte_offset + @as(u32, last_rec.byte_len) < first_rec.byte_offset) return null;
    return Span.init(
        file_id,
        first_rec.byte_offset,
        last_rec.byte_offset + @as(u32, last_rec.byte_len),
    );
}

/// Returns `true` if `subtree_idx` contains any CST error flag or synthesized/lexer-error token.
fn hasSyntaxErrorInSubtree(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) bool {
    if (subtree_idx.isNone() or subtree_idx.asInt() >= cst_arena.countNodes()) return true;
    const root_node = cst_arena.getNode(subtree_idx);
    const end_idx = @min(
        @as(usize, subtree_idx.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var cursor: usize = subtree_idx.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.flags.has_error or node.flags.is_missing_or_injected or
            node.kind == .invalid_parse_leaf or node.kind == .invalid_parse_subtree)
        {
            return true;
        }
        if (node.subtree_size <= 1 and !node.token.isNone() and node.token.asInt() < tok_count) {
            const tok_rec = token_buffer.getToken(node.token);
            if (tok_rec.flags.is_synthesized or tok_rec.flags.has_lexer_error or tok_rec.kind == .invalid_token) {
                return true;
            }
        }
    }
    return false;
}

/// Returns `true` if `subtree_idx` contains a braced expression/pattern that would become ambiguous without `(…)`.
fn hasStructLitOrBlockInSubtree(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) bool {
    if (subtree_idx.isNone() or subtree_idx.asInt() >= cst_arena.countNodes()) return false;
    const root_node = cst_arena.getNode(subtree_idx);
    const end_idx = @min(
        @as(usize, subtree_idx.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
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
                    token_buffer.getToken(sub_node.token).kind == .lbrace)
                {
                    return true;
                }
            }
        }
    }
    return false;
}

/// Returns `true` if `subtree_idx` contains any walrus condition binding (`:=`, `E0215` if unparenthesized).
fn hasWalrusInSubtree(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    subtree_idx: CstNodeIndex,
) bool {
    if (subtree_idx.isNone() or subtree_idx.asInt() >= cst_arena.countNodes()) return false;
    const root_node = cst_arena.getNode(subtree_idx);
    const end_idx = @min(
        @as(usize, subtree_idx.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var cursor: usize = subtree_idx.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .walrus_cond_expr) return true;
        if (node.subtree_size <= 1 and !node.token.isNone() and node.token.asInt() < tok_count and
            token_buffer.getToken(node.token).kind == .colon_eq)
        {
            return true;
        }
    }
    return false;
}

/// Returns `true` if `pat_cst` contains a `{` token or `.struct_pat` requiring `(Pat)` in `if scrut is (Pat) { … }`.
fn hasBraceInPatternSubtree(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    pat_cst: CstNodeIndex,
) bool {
    if (pat_cst.isNone() or pat_cst.asInt() >= cst_arena.countNodes()) return false;
    const root_node = cst_arena.getNode(pat_cst);
    if (root_node.kind == .struct_pat) return true;
    const end_idx = @min(
        @as(usize, pat_cst.asInt()) + @max(@as(usize, root_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var cursor: usize = pat_cst.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const node = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (node.kind == .struct_pat or node.kind == .struct_pat_start or node.kind == .field_pat) return true;
        if (node.subtree_size <= 1 and !node.token.isNone() and node.token.asInt() < tok_count and
            token_buffer.getToken(node.token).kind == .lbrace)
        {
            return true;
        }
    }
    return false;
}

/// Returns `true` if `pat_id` binds any local pattern variable (`.bind_pat` / `.at_pat`), excluding `const_sym` constants.
fn hasBindingInPatternAst(checker: *const TypeChecker, pat_id: NodeIndex, depth: u32) bool {
    if (depth > 64 or pat_id.isNone() or pat_id.asInt() >= checker.ast_arena.countNodes()) return true;
    const pat_node = checker.ast_arena.getNode(pat_id);
    switch (pat_node.tag) {
        .at_pat => return true,
        .bind_pat => {
            if (pat_id.asInt() < checker.node_symbols.len) {
                const sym_idx = checker.node_symbols[pat_id.asInt()];
                if (!sym_idx.isNone() and sym_idx.asInt() < checker.sym_table.countSymbols() and
                    checker.sym_table.getSymbol(sym_idx).kind == .const_sym)
                {
                    return false;
                }
            }
            if (!pat_node.main_token.isNone() and pat_node.main_token.asInt() < checker.token_buffer.countTokens() and
                checker.token_buffer.getToken(pat_node.main_token).kind == .const_ident)
            {
                return false;
            }
            return true;
        },
        else => {},
    }
    if (pat_node.lhs.tag == .node and hasBindingInPatternAst(checker, NodeIndex.fromInt(pat_node.lhs.payload), depth + 1)) {
        return true;
    }
    if (pat_node.rhs.tag == .node and hasBindingInPatternAst(checker, NodeIndex.fromInt(pat_node.rhs.payload), depth + 1)) {
        return true;
    }
    if (pat_node.lhs.tag == .extra) {
        for (checker.getNodeExtraSlice(pat_id, false)) |child_raw| {
            if (hasBindingInPatternAst(checker, NodeIndex.fromInt(child_raw), depth + 1)) return true;
        }
    }
    if (pat_node.rhs.tag == .extra and pat_node.lhs.tag != .extra) {
        for (checker.getNodeExtraSlice(pat_id, true)) |child_raw| {
            if (hasBindingInPatternAst(checker, NodeIndex.fromInt(child_raw), depth + 1)) return true;
        }
    }
    return false;
}

/// Returns `true` if `expr_id` contains an `is` pattern binding (`E0214` if lifted into `return` / `not`).
fn hasIsBindingInExprAst(checker: *const TypeChecker, expr_id: NodeIndex, depth: u32) bool {
    if (depth > 64 or expr_id.isNone() or expr_id.asInt() >= checker.ast_arena.countNodes()) return true;
    const node = checker.ast_arena.getNode(expr_id);
    if (node.tag == .is_expr) {
        if (node.lhs.tag == .node and hasIsBindingInExprAst(checker, NodeIndex.fromInt(node.lhs.payload), depth + 1)) {
            return true;
        }
        if (node.rhs.tag == .node and hasBindingInPatternAst(checker, NodeIndex.fromInt(node.rhs.payload), 0)) {
            return true;
        }
        return false;
    }
    if (node.lhs.tag == .node and hasIsBindingInExprAst(checker, NodeIndex.fromInt(node.lhs.payload), depth + 1)) {
        return true;
    }
    if (node.rhs.tag == .node and hasIsBindingInExprAst(checker, NodeIndex.fromInt(node.rhs.payload), depth + 1)) {
        return true;
    }
    if (node.lhs.tag == .extra) {
        for (checker.getNodeExtraSlice(expr_id, false)) |child_raw| {
            if (hasIsBindingInExprAst(checker, NodeIndex.fromInt(child_raw), depth + 1)) return true;
        }
    }
    if (node.rhs.tag == .extra and node.lhs.tag != .extra) {
        for (checker.getNodeExtraSlice(expr_id, true)) |child_raw| {
            if (hasIsBindingInExprAst(checker, NodeIndex.fromInt(child_raw), depth + 1)) return true;
        }
    }
    return false;
}

/// Emits a `.w0202_non_idiomatic_construct` warning with an optional `.machine_applicable` `.lint_idiom` fix.
fn emitIdiomWarning(
    sink_opt: ?*DiagnosticSink,
    primary_span: Span,
    message: []const u8,
    label_text: []const u8,
    fix_message: []const u8,
    edits: []const TextEdit,
) !void {
    const sink = sink_opt orelse return;
    if (edits.len > 0) {
        try sink.emit(.{
            .code = .w0202_non_idiomatic_construct,
            .severity = .warning,
            .primary_span = primary_span,
            .message = message,
            .labels = &.{.{
                .span = primary_span,
                .label = label_text,
                .style = .primary,
            }},
            .suggestions = &.{.{
                .message = fix_message,
                .applicability = .machine_applicable,
                .priority = .lint_idiom,
                .edits = edits,
            }},
        });
    } else {
        try sink.emit(.{
            .code = .w0202_non_idiomatic_construct,
            .severity = .warning,
            .primary_span = primary_span,
            .message = message,
            .labels = &.{.{
                .span = primary_span,
                .label = label_text,
                .style = .primary,
            }},
        });
    }
}

/// Extracts `(lparen_tok, inner_cst, rparen_tok)` when `cand_cst` is a redundant `.tuple_or_paren_expr`.
fn matchRedundantOuterParenCst(
    checker: *const TypeChecker,
    cand_cst: CstNodeIndex,
) !?struct {
    /// Opening `(` token index.
    lparen_tok: TokenIndex,
    /// Unwrapped inner expression CST node index.
    inner_cst: CstNodeIndex,
    /// Closing `)` token index.
    rparen_tok: TokenIndex,
} {
    if (cand_cst.isNone() or cand_cst.asInt() >= checker.cst_arena.countNodes()) return null;
    const cand_node = checker.cst_arena.getNode(cand_cst);
    if (cand_node.kind != .tuple_or_paren_expr or cand_node.flags.has_error) return null;
    if (hasSyntaxErrorInSubtree(checker.cst_arena, checker.token_buffer, cand_cst)) return null;

    if (cand_cst.asInt() < checker.cst_to_ast.len) {
        const mapped_ast = checker.cst_to_ast[cand_cst.asInt()];
        if (!mapped_ast.isNone() and mapped_ast.asInt() < checker.ast_arena.countNodes() and
            checker.ast_arena.getNode(mapped_ast).tag == .tuple_lit)
        {
            return null;
        }
    }

    var children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, cand_cst, &children);
    if (children.items.len != 3) return null;

    const open_leaf = checker.cst_arena.getNode(children.items[0]);
    const inner_cst = children.items[1];
    const close_leaf = checker.cst_arena.getNode(children.items[2]);
    if (open_leaf.subtree_size != 1 or open_leaf.token.isNone() or
        close_leaf.subtree_size != 1 or close_leaf.token.isNone())
    {
        return null;
    }
    const open_rec = checker.token_buffer.getToken(open_leaf.token);
    const close_rec = checker.token_buffer.getToken(close_leaf.token);
    if (open_rec.kind != .lparen or close_rec.kind != .rparen or
        open_rec.flags.is_synthesized or close_rec.flags.is_synthesized)
    {
        return null;
    }
    if (hasWalrusInSubtree(checker.cst_arena, checker.token_buffer, inner_cst)) return null;
    if (hasStructLitOrBlockInSubtree(checker.cst_arena, checker.token_buffer, inner_cst)) return null;

    return .{
        .lparen_tok = open_leaf.token,
        .inner_cst = inner_cst,
        .rparen_tok = close_leaf.token,
    };
}

/// Idiom 1: Lints redundant outer parentheses in `if (cond)`, `while (cond)`, and `match (scrut)`.
fn lintRedundantHeaderParensInCst(
    checker: *TypeChecker,
    header_cst: CstNodeIndex,
    construct_name: []const u8,
    sink_opt: ?*DiagnosticSink,
) !void {
    const matched = (try matchRedundantOuterParenCst(checker, header_cst)) orelse return;
    const paren_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        header_cst,
    ) orelse return;
    if (isW0202SuppressedAtSpan(checker, paren_span)) return;

    const inner_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        matched.inner_cst,
    ) orelse return;
    const open_rec = checker.token_buffer.getToken(matched.lparen_tok);
    const close_rec = checker.token_buffer.getToken(matched.rparen_tok);

    const has_discarded_comments =
        hasCommentsInByteRange(checker.source, checker.token_buffer, open_rec.byte_offset, inner_span.start_byte) or
        hasCommentsInByteRange(
            checker.source,
            checker.token_buffer,
            inner_span.end_byte,
            close_rec.byte_offset + @as(u32, close_rec.byte_len),
        );

    var msg_buf: [128]u8 = undefined;
    const warn_msg = std.fmt.bufPrint(
        &msg_buf,
        "redundant outer parentheses around `{s}` header expression",
        .{construct_name},
    ) catch "redundant outer parentheses around control-flow header expression";

    if (has_discarded_comments) {
        try emitIdiomWarning(
            sink_opt,
            paren_span,
            warn_msg,
            "unnecessary outer `(` … `)`",
            "remove redundant outer parentheses",
            &.{},
        );
        return;
    }

    const needs_open_space = open_rec.byte_offset > 0 and
        isIdentifierByte(checker.source[open_rec.byte_offset - 1]);
    const close_end: usize = close_rec.byte_offset + @as(usize, close_rec.byte_len);
    const needs_close_space = close_end < checker.source.len and
        (isIdentifierByte(checker.source[close_end]) or checker.source[close_end] == '{');

    const edits = [2]TextEdit{
        .{
            .file_id = checker.file_id,
            .start_byte = open_rec.byte_offset,
            .end_byte = inner_span.start_byte,
            .replacement_id = try checker.interner.intern(if (needs_open_space) " " else ""),
        },
        .{
            .file_id = checker.file_id,
            .start_byte = inner_span.end_byte,
            .end_byte = close_rec.byte_offset + @as(u32, close_rec.byte_len),
            .replacement_id = try checker.interner.intern(if (needs_close_space) " " else ""),
        },
    };
    try emitIdiomWarning(
        sink_opt,
        paren_span,
        warn_msg,
        "unnecessary outer `(` … `)`",
        "remove redundant outer parentheses",
        &edits,
    );
}

/// Returns `true` when `operand_ast_id` requires `(…)` to preserve grouping under prefix `not` (`bp = 28`).
fn isNotOperandNeedingParens(checker: *const TypeChecker, operand_ast_id: NodeIndex) bool {
    if (operand_ast_id.isNone() or operand_ast_id.asInt() >= checker.ast_arena.countNodes()) return true;
    const cst_origin = checker.ast_arena.getCstOrigin(operand_ast_id);
    if (!cst_origin.isNone() and cst_origin.asInt() < checker.cst_arena.countNodes() and
        checker.cst_arena.getNode(cst_origin).kind == .tuple_or_paren_expr)
    {
        return false;
    }
    return switch (checker.ast_arena.getNode(operand_ast_id).tag) {
        .binary_expr,
        .pipe_expr,
        .cast_expr,
        .is_expr,
        .range_expr,
        .walrus_expr,
        .if_expr,
        .closure_expr,
        .unary_expr,
        .return_stmt,
        .break_stmt,
        .continue_stmt,
        => true,
        else => false,
    };
}

/// Idiom 2: Lints scalar `bool` equality/inequality with `true`/`false` (`x == true`, `x == false`, etc.).
fn lintRedundantBoolEqualityAst(
    checker: *TypeChecker,
    bin_ast_id: NodeIndex,
    sink_opt: ?*DiagnosticSink,
) !void {
    if (bin_ast_id.isNone() or bin_ast_id.asInt() >= checker.ast_arena.countNodes()) return;
    const bin_node = checker.ast_arena.getNode(bin_ast_id);
    if (bin_node.tag != .binary_expr) return;
    if (bin_node.main_token.isNone() or bin_node.main_token.asInt() >= checker.token_buffer.countTokens()) return;

    const op_tok = checker.token_buffer.getToken(bin_node.main_token);
    if (op_tok.flags.is_synthesized or (op_tok.kind != .eqeq and op_tok.kind != .bang_eq)) return;
    if (bin_node.lhs.tag != .node or bin_node.rhs.tag != .node) return;

    const lhs_id = NodeIndex.fromInt(bin_node.lhs.payload);
    const rhs_id = NodeIndex.fromInt(bin_node.rhs.payload);
    if (getRecordedNodeType(checker, bin_ast_id) != .bool_ty or
        getRecordedNodeType(checker, lhs_id) != .bool_ty or
        getRecordedNodeType(checker, rhs_id) != .bool_ty)
    {
        return;
    }

    const lhs_node = checker.ast_arena.getNode(lhs_id);
    const rhs_node = checker.ast_arena.getNode(rhs_id);
    const is_rhs_bool_lit = rhs_node.tag == .bool_lit and !rhs_node.main_token.isNone() and
        !checker.token_buffer.getToken(rhs_node.main_token).flags.is_synthesized;
    const is_lhs_bool_lit = lhs_node.tag == .bool_lit and !lhs_node.main_token.isNone() and
        !checker.token_buffer.getToken(lhs_node.main_token).flags.is_synthesized;
    if (!is_rhs_bool_lit and !is_lhs_bool_lit) return;

    const bin_cst = checker.ast_arena.getCstOrigin(bin_ast_id);
    if (hasSyntaxErrorInSubtree(checker.cst_arena, checker.token_buffer, bin_cst)) return;
    const bin_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        bin_cst,
    ) orelse checker.getAstNodeSpan(bin_ast_id);
    if (isW0202SuppressedAtSpan(checker, bin_span)) return;

    const lit_node = if (is_rhs_bool_lit) rhs_node else lhs_node;
    const expr_id = if (is_rhs_bool_lit) lhs_id else rhs_id;
    const is_lit_true = checker.token_buffer.getToken(lit_node.main_token).kind == .kw_true;
    const is_identity = (op_tok.kind == .eqeq and is_lit_true) or (op_tok.kind == .bang_eq and !is_lit_true);

    const expr_cst = checker.ast_arena.getCstOrigin(expr_id);
    const expr_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        expr_cst,
    ) orelse checker.getAstNodeSpan(expr_id);
    if (expr_span.start_byte < bin_span.start_byte or expr_span.end_byte > bin_span.end_byte) return;

    const has_lost_comments =
        hasCommentsInByteRange(checker.source, checker.token_buffer, bin_span.start_byte, expr_span.start_byte) or
        hasCommentsInByteRange(checker.source, checker.token_buffer, expr_span.end_byte, bin_span.end_byte);

    if (has_lost_comments) {
        try emitIdiomWarning(
            sink_opt,
            bin_span,
            "redundant comparison with boolean literal; use the boolean expression or `not` directly",
            "redundant boolean literal comparison",
            "simplify boolean literal comparison",
            &.{},
        );
        return;
    }

    const expr_slice = checker.source[expr_span.start_byte..expr_span.end_byte];
    var repl_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer repl_buf.deinit(checker.allocator);

    if (bin_span.start_byte > 0 and isIdentifierByte(checker.source[bin_span.start_byte - 1])) {
        try repl_buf.append(checker.allocator, ' ');
    }
    if (is_lhs_bool_lit and is_rhs_bool_lit) {
        const lhs_true = checker.token_buffer.getToken(lhs_node.main_token).kind == .kw_true;
        const folded_val = if (op_tok.kind == .eqeq) (lhs_true == is_lit_true) else (lhs_true != is_lit_true);
        try repl_buf.appendSlice(checker.allocator, if (folded_val) "true" else "false");
    } else if (is_identity) {
        try repl_buf.appendSlice(checker.allocator, expr_slice);
    } else if (isNotOperandNeedingParens(checker, expr_id)) {
        try repl_buf.appendSlice(checker.allocator, "not (");
        try repl_buf.appendSlice(checker.allocator, expr_slice);
        try repl_buf.append(checker.allocator, ')');
    } else {
        try repl_buf.appendSlice(checker.allocator, "not ");
        try repl_buf.appendSlice(checker.allocator, expr_slice);
    }
    if (bin_span.end_byte < checker.source.len and isIdentifierByte(checker.source[bin_span.end_byte])) {
        try repl_buf.append(checker.allocator, ' ');
    }

    const edit = TextEdit{
        .file_id = checker.file_id,
        .start_byte = bin_span.start_byte,
        .end_byte = bin_span.end_byte,
        .replacement_id = try checker.interner.intern(repl_buf.items),
    };
    try emitIdiomWarning(
        sink_opt,
        bin_span,
        "redundant comparison with boolean literal; use the boolean expression or `not` directly",
        "redundant boolean literal comparison",
        if (is_identity) "remove redundant boolean literal comparison" else "rewrite using prefix `not`",
        &.{edit},
    );
}

/// Returns `true` if `cst_idx` is a surface type CST node kind.
fn isTypeCstNodeKind(kind: CstNodeKind) bool {
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

/// Returns `true` if `ref_cst` is a slice reference `&[T]` / `&mut [T]` (without `;` array length).
fn isSliceRefTypeCst(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    ref_cst: CstNodeIndex,
) bool {
    const node = cst_arena.getNode(ref_cst);
    if (node.kind != .ref_type or node.subtree_size <= 1) return false;
    const end_idx = @min(@as(usize, ref_cst.asInt()) + @as(usize, node.subtree_size), cst_arena.countNodes());
    var cursor: usize = @as(usize, ref_cst.asInt()) + 1;
    var slice_child: CstNodeIndex = .none;
    while (cursor < end_idx) {
        const child_id = CstNodeIndex.fromInt(@intCast(cursor));
        const child = cst_arena.getNode(child_id);
        if (isTypeCstNodeKind(child.kind)) {
            slice_child = child_id;
            break;
        }
        cursor += @max(@as(usize, child.subtree_size), 1);
    }
    if (slice_child.isNone()) return false;
    const target_node = cst_arena.getNode(slice_child);
    if (target_node.kind != .slice_or_array_type) return false;

    const sub_end = @min(@as(usize, slice_child.asInt()) + @as(usize, target_node.subtree_size), end_idx);
    var sub_cur: usize = @as(usize, slice_child.asInt()) + 1;
    while (sub_cur < sub_end) {
        const sub_child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_cur)));
        if (sub_child.subtree_size <= 1 and !sub_child.token.isNone() and
            sub_child.token.asInt() < token_buffer.countTokens() and
            token_buffer.getToken(sub_child.token).kind == .semi)
        {
            return false;
        }
        sub_cur += @max(@as(usize, sub_child.subtree_size), 1);
    }
    return true;
}

/// Matches an unqualified syntactic `Option[T]` or `Result[T, E]` `.named_type` CST node.
fn matchSyntacticStdlibGenericType(
    checker: *const TypeChecker,
    cst_idx: CstNodeIndex,
) !?CanonicalStdlibType {
    if (cst_idx.isNone() or cst_idx.asInt() >= checker.cst_arena.countNodes()) return null;
    const node = checker.cst_arena.getNode(cst_idx);
    if (node.kind != .named_type or node.subtree_size <= 1 or node.flags.has_error) return null;
    if (hasSyntaxErrorInSubtree(checker.cst_arena, checker.token_buffer, cst_idx)) return null;

    var children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, cst_idx, &children);
    if (children.items.len != 2) return null;

    const name_leaf = checker.cst_arena.getNode(children.items[0]);
    const args_cst = children.items[1];
    const args_node = checker.cst_arena.getNode(args_cst);
    if (name_leaf.subtree_size != 1 or name_leaf.token.isNone() or args_node.kind != .type_args) return null;

    const name_rec = checker.token_buffer.getToken(name_leaf.token);
    if (name_rec.flags.is_synthesized or name_rec.kind != .type_ident) return null;
    const name_lex = checker.source[name_rec.byte_offset .. name_rec.byte_offset + name_rec.byte_len];
    const is_option = std.mem.eql(u8, name_lex, "Option");
    const is_result = std.mem.eql(u8, name_lex, "Result");
    if (!is_option and !is_result) return null;

    var arg_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer arg_children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, args_cst, &arg_children);
    if (arg_children.items.len < 3) return null;

    const open_leaf = checker.cst_arena.getNode(arg_children.items[0]);
    const close_leaf = checker.cst_arena.getNode(arg_children.items[arg_children.items.len - 1]);
    if (open_leaf.subtree_size != 1 or open_leaf.token.isNone() or
        close_leaf.subtree_size != 1 or close_leaf.token.isNone())
    {
        return null;
    }
    if (checker.token_buffer.getToken(open_leaf.token).kind != .lbracket or
        checker.token_buffer.getToken(close_leaf.token).kind != .rbracket)
    {
        return null;
    }

    var type_args_buf: [2]CstNodeIndex = .{ .none, .none };
    var type_arg_count: usize = 0;
    for (arg_children.items[1 .. arg_children.items.len - 1]) |arg_item| {
        const arg_node = checker.cst_arena.getNode(arg_item);
        if (isTypeCstNodeKind(arg_node.kind)) {
            if (type_arg_count >= 2) return null;
            type_args_buf[type_arg_count] = arg_item;
            type_arg_count += 1;
        } else {
            if (arg_node.subtree_size != 1 or arg_node.token.isNone() or
                checker.token_buffer.getToken(arg_node.token).kind != .comma)
            {
                return null;
            }
        }
    }

    if (is_option and type_arg_count == 1) {
        return .{ .option = .{
            .name_tok = name_leaf.token,
            .close_bracket_tok = close_leaf.token,
            .inner_cst = type_args_buf[0],
        } };
    }
    if (is_result and type_arg_count == 2) {
        return .{ .result = .{
            .name_tok = name_leaf.token,
            .close_bracket_tok = close_leaf.token,
            .ok_cst = type_args_buf[0],
            .err_cst = type_args_buf[1],
        } };
    }
    return null;
}

/// Verifies via `TypeChecker` & `SymbolTable` that `cst_idx` resolves to unshadowed built-in `Option`/`Result`.
fn isUnshadowedBuiltinOptionOrResult(
    checker: *const TypeChecker,
    cst_idx: CstNodeIndex,
    is_option: bool,
) bool {
    if (cst_idx.asInt() >= checker.cst_to_ast.len) return false;
    const ast_id = checker.cst_to_ast[cst_idx.asInt()];
    if (ast_id.isNone() or ast_id.asInt() >= checker.ast_arena.countNodes()) return false;
    const ast_node = checker.ast_arena.getNode(ast_id);
    if (ast_node.tag != .generic_type) return false;

    const resolved_ty = getRecordedNodeType(checker, ast_id);
    if (resolved_ty.isError()) return false;
    const expected_tag: type_system.TypeTag = if (is_option) .optional_ty else .result_ty;
    if (checker.pool.getTag(resolved_ty) != expected_tag) return false;

    if (ast_node.lhs.tag == .node) {
        const base_ast = NodeIndex.fromInt(ast_node.lhs.payload);
        if (!base_ast.isNone() and base_ast.asInt() < checker.node_symbols.len) {
            const base_sym_idx = checker.node_symbols[base_ast.asInt()];
            if (!base_sym_idx.isNone() and base_sym_idx.asInt() < checker.sym_table.countSymbols()) {
                return checker.sym_table.getSymbol(base_sym_idx).flags.is_builtin;
            }
        }
    }

    const target_name: []const u8 = if (is_option) "Option" else "Result";
    const name_str_id = checker.interner.lookup(target_name) orelse return true;
    const mod_scope = checker.sym_table.file_module_scopes.get(checker.file_id.asInt()) orelse
        checker.sym_table.prelude_scope;
    return switch (checker.sym_table.lookupLexical(
        mod_scope,
        name_str_id,
        symbol_resolver.NamespaceMask.TYPE_ONLY,
    )) {
        .found => |found_sym| checker.sym_table.getSymbol(found_sym).flags.is_builtin,
        else => true,
    };
}

/// Computes the 4-tier `DR-22` surface precedence of `type_cst`.
fn intrinsicCstTypePrec(checker: *const TypeChecker, type_cst: CstNodeIndex) !SurfaceTypePrec {
    const node = checker.cst_arena.getNode(type_cst);
    if (node.subtree_size <= 1) return .tier4_primary;
    return switch (node.kind) {
        .refined_type, .intersect_bound_type, .union_bound_type => .tier0_open,
        .result_type => .tier1_result,
        .optional_type => .tier3_postfix,
        .ref_type => if (isSliceRefTypeCst(checker.cst_arena, checker.token_buffer, type_cst))
            .tier4_primary
        else
            .tier2_prefix,
        .mode_type => blk: {
            const first_tok = findFirstRealTokenInSubtree(checker.cst_arena, checker.token_buffer, type_cst);
            if (!first_tok.isNone()) {
                const rec = checker.token_buffer.getToken(first_tok);
                if (rec.kind == .kw_own or rec.kind == .tilde) break :blk .tier2_prefix;
                const lexeme = checker.source[rec.byte_offset .. rec.byte_offset + rec.byte_len];
                if (rec.kind == .ident and std.mem.eql(u8, lexeme, "distinct")) break :blk .tier0_open;
            }
            break :blk .tier4_primary;
        },
        .named_type => if (try matchSyntacticStdlibGenericType(checker, type_cst)) |canon| switch (canon) {
            .option => if (isUnshadowedBuiltinOptionOrResult(checker, type_cst, true))
                .tier3_postfix
            else
                .tier4_primary,
            .result => if (isUnshadowedBuiltinOptionOrResult(checker, type_cst, false))
                .tier1_result
            else
                .tier4_primary,
        } else .tier4_primary,
        else => .tier4_primary,
    };
}

/// Returns `true` if `type_cst` ends in an unparenthesized `.fn_type` or `.closure_type` return tail.
fn hasCallableTypeTail(checker: *const TypeChecker, type_cst: CstNodeIndex) bool {
    const node = checker.cst_arena.getNode(type_cst);
    if (node.subtree_size <= 1) return false;
    return switch (node.kind) {
        .fn_type, .closure_type => true,
        .ptr_type, .ref_type, .mode_type => blk: {
            if (node.kind == .ref_type and isSliceRefTypeCst(checker.cst_arena, checker.token_buffer, type_cst)) {
                break :blk false;
            }
            const end_idx = @min(
                @as(usize, type_cst.asInt()) + @as(usize, node.subtree_size),
                checker.cst_arena.countNodes(),
            );
            var last_type_child: CstNodeIndex = .none;
            var cursor: usize = @as(usize, type_cst.asInt()) + 1;
            while (cursor < end_idx) {
                const child_id = CstNodeIndex.fromInt(@intCast(cursor));
                const child = checker.cst_arena.getNode(child_id);
                if (isTypeCstNodeKind(child.kind)) last_type_child = child_id;
                cursor += @max(@as(usize, child.subtree_size), 1);
            }
            if (last_type_child.isNone()) break :blk false;
            break :blk hasCallableTypeTail(checker, last_type_child);
        },
        else => false,
    };
}

/// Returns `true` when `inner_cst` inside `Option[Inner]` must be wrapped as `(Inner)?`.
fn isInnerTypeNeedingOptionParens(checker: *const TypeChecker, inner_cst: CstNodeIndex) !bool {
    const node = checker.cst_arena.getNode(inner_cst);
    if (node.subtree_size <= 1) return false;
    switch (node.kind) {
        .ref_type,
        .ptr_type,
        .mode_type,
        .fn_type,
        .closure_type,
        .result_type,
        .refined_type,
        .intersect_bound_type,
        .union_bound_type,
        => return true,
        else => {},
    }
    const own_prec = try intrinsicCstTypePrec(checker, inner_cst);
    return @backingInt(own_prec) < @backingInt(SurfaceTypePrec.tier3_postfix) or
        hasCallableTypeTail(checker, inner_cst);
}

/// Returns `true` when `<Inner>?` itself must be wrapped as `(<Inner>?)` under `parent_cst`.
fn isOuterOptionNeedingParens(
    checker: *const TypeChecker,
    parent_cst: CstNodeIndex,
    has_leading_inner_lbracket: bool,
) !bool {
    if (parent_cst.isNone() or parent_cst.asInt() >= checker.cst_arena.countNodes()) return false;
    const parent = checker.cst_arena.getNode(parent_cst);
    return switch (parent.kind) {
        .ptr_type => true,
        .ref_type => has_leading_inner_lbracket,
        .mode_type => (try intrinsicCstTypePrec(checker, parent_cst)) == .tier4_primary,
        else => false,
    };
}

/// Returns `true` when `arg_cst` (`Ok` or `Err`) inside `Result[Ok, Err]` requires `(…)` around `<arg>`.
fn isOperandNeedingResultParens(checker: *const TypeChecker, arg_cst: CstNodeIndex) !bool {
    const own_prec = try intrinsicCstTypePrec(checker, arg_cst);
    return @backingInt(own_prec) < @backingInt(SurfaceTypePrec.tier2_prefix) or
        hasCallableTypeTail(checker, arg_cst);
}

/// Returns `true` when `<Ok>!<Err>` itself must be wrapped as `(<Ok>!<Err>)` under `parent_cst`.
fn isOuterResultNeedingParens(
    checker: *const TypeChecker,
    self_cst: CstNodeIndex,
    parent_cst: CstNodeIndex,
) !bool {
    if (parent_cst.isNone() or parent_cst.asInt() >= checker.cst_arena.countNodes()) return false;
    const parent = checker.cst_arena.getNode(parent_cst);
    return switch (parent.kind) {
        .optional_type, .result_type, .ref_type, .ptr_type => true,
        .mode_type => (try intrinsicCstTypePrec(checker, parent_cst)) != .tier0_open,
        .refined_type => blk: {
            var children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
            defer children.deinit(checker.allocator);
            try collectDirectCstChildren(checker.allocator, checker.cst_arena, parent_cst, &children);
            break :blk children.items.len > 0 and children.items[0] == self_cst;
        },
        .type_args => blk: {
            // Inside outer `.type_args` (`Option[Result[…]]`), bare `Ok!Err` parses validly without extra `(…)`:
            break :blk false;
        },
        else => false,
    };
}

/// Idiom 3: Lints unshadowed `Option[T]` -> `T?` and `Result[T, E]` -> `T!E` surface type annotations.
fn lintCanonicalGenericTypeCst(
    checker: *TypeChecker,
    cst_idx: CstNodeIndex,
    parent_cst: CstNodeIndex,
    grandparent_cst: CstNodeIndex,
    sink_opt: ?*DiagnosticSink,
) !void {
    const matched = (try matchSyntacticStdlibGenericType(checker, cst_idx)) orelse return;
    const is_option = (matched == .option);
    if (!isUnshadowedBuiltinOptionOrResult(checker, cst_idx, is_option)) return;

    const full_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        cst_idx,
    ) orelse return;
    if (isW0202SuppressedAtSpan(checker, full_span)) return;

    switch (matched) {
        .option => |opt_info| {
            const inner_span = getCstSubtreeSpan(
                checker.file_id,
                checker.cst_arena,
                checker.token_buffer,
                opt_info.inner_cst,
            ) orelse return;
            const has_lost_comments =
                hasCommentsInByteRange(checker.source, checker.token_buffer, full_span.start_byte, inner_span.start_byte) or
                hasCommentsInByteRange(checker.source, checker.token_buffer, inner_span.end_byte, full_span.end_byte);

            if (has_lost_comments) {
                try emitIdiomWarning(
                    sink_opt,
                    full_span,
                    "non-canonical generic `Option[T]` type spelling; prefer postfix `T?`",
                    "prefer postfix `?` optional syntax",
                    "rewrite `Option[T]` to `T?`",
                    &.{},
                );
                return;
            }

            const inner_slice = checker.source[inner_span.start_byte..inner_span.end_byte];
            const wrap_inner = try isInnerTypeNeedingOptionParens(checker, opt_info.inner_cst);
            const starts_with_bracket = !wrap_inner and inner_slice.len > 0 and inner_slice[0] == '[';
            const wrap_outer = try isOuterOptionNeedingParens(checker, parent_cst, starts_with_bracket);

            var repl_buf: std.ArrayListUnmanaged(u8) = .empty;
            defer repl_buf.deinit(checker.allocator);
            if (wrap_outer) try repl_buf.append(checker.allocator, '(');
            if (wrap_inner) try repl_buf.append(checker.allocator, '(');
            try repl_buf.appendSlice(checker.allocator, inner_slice);
            if (wrap_inner) try repl_buf.append(checker.allocator, ')');
            try repl_buf.append(checker.allocator, '?');
            if (wrap_outer) try repl_buf.append(checker.allocator, ')');

            const edit = TextEdit{
                .file_id = checker.file_id,
                .start_byte = full_span.start_byte,
                .end_byte = full_span.end_byte,
                .replacement_id = try checker.interner.intern(repl_buf.items),
            };
            try emitIdiomWarning(
                sink_opt,
                full_span,
                "non-canonical generic `Option[T]` type spelling; prefer postfix `T?`",
                "prefer postfix `?` optional syntax",
                "rewrite `Option[T]` to `T?`",
                &.{edit},
            );
        },
        .result => |res_info| {
            const ok_span = getCstSubtreeSpan(
                checker.file_id,
                checker.cst_arena,
                checker.token_buffer,
                res_info.ok_cst,
            ) orelse return;
            const err_span = getCstSubtreeSpan(
                checker.file_id,
                checker.cst_arena,
                checker.token_buffer,
                res_info.err_cst,
            ) orelse return;
            const has_lost_comments =
                hasCommentsInByteRange(checker.source, checker.token_buffer, full_span.start_byte, ok_span.start_byte) or
                hasCommentsInByteRange(checker.source, checker.token_buffer, ok_span.end_byte, err_span.start_byte) or
                hasCommentsInByteRange(checker.source, checker.token_buffer, err_span.end_byte, full_span.end_byte);

            if (has_lost_comments) {
                try emitIdiomWarning(
                    sink_opt,
                    full_span,
                    "non-canonical generic `Result[T, E]` type spelling; prefer infix `T!E`",
                    "prefer payload-first `T!E` result syntax",
                    "rewrite `Result[T, E]` to `T!E`",
                    &.{},
                );
                return;
            }

            const ok_slice = checker.source[ok_span.start_byte..ok_span.end_byte];
            const err_slice = checker.source[err_span.start_byte..err_span.end_byte];
            const wrap_ok = try isOperandNeedingResultParens(checker, res_info.ok_cst);
            const wrap_err = try isOperandNeedingResultParens(checker, res_info.err_cst);
            const is_inside_outer_canon = if (!grandparent_cst.isNone() and
                checker.cst_arena.getNode(parent_cst).kind == .type_args)
                ((try matchSyntacticStdlibGenericType(checker, grandparent_cst)) != null)
            else
                false;
            const wrap_outer = is_inside_outer_canon or
                (try isOuterResultNeedingParens(checker, cst_idx, parent_cst));

            var repl_buf: std.ArrayListUnmanaged(u8) = .empty;
            defer repl_buf.deinit(checker.allocator);
            if (wrap_outer) try repl_buf.append(checker.allocator, '(');
            if (wrap_ok) try repl_buf.append(checker.allocator, '(');
            try repl_buf.appendSlice(checker.allocator, ok_slice);
            if (wrap_ok) try repl_buf.append(checker.allocator, ')');
            try repl_buf.append(checker.allocator, '!');
            if (wrap_err) try repl_buf.append(checker.allocator, '(');
            try repl_buf.appendSlice(checker.allocator, err_slice);
            if (wrap_err) try repl_buf.append(checker.allocator, ')');
            if (wrap_outer) try repl_buf.append(checker.allocator, ')');

            const edit = TextEdit{
                .file_id = checker.file_id,
                .start_byte = full_span.start_byte,
                .end_byte = full_span.end_byte,
                .replacement_id = try checker.interner.intern(repl_buf.items),
            };
            try emitIdiomWarning(
                sink_opt,
                full_span,
                "non-canonical generic `Result[T, E]` type spelling; prefer infix `T!E`",
                "prefer payload-first `T!E` result syntax",
                "rewrite `Result[T, E]` to `T!E`",
                &.{edit},
            );
        },
    }
}

/// Idiom 4: Lints a redundant trailing bare `return;` at the end of a `unit`-returning `fn` block.
fn lintTrailingUnitReturnFnDecl(
    checker: *TypeChecker,
    fn_sym_idx: SymbolIndex,
    fn_ast_id: NodeIndex,
    sink_opt: ?*DiagnosticSink,
) !void {
    if (fn_sym_idx.isNone() or fn_sym_idx.asInt() >= checker.sym_table.countSymbols()) return;
    if (fn_ast_id.isNone() or fn_ast_id.asInt() >= checker.ast_arena.countNodes()) return;

    const fn_sym = checker.sym_table.getSymbol(fn_sym_idx).*;
    if (fn_sym.flags.is_extern or fn_sym.flags.is_prototype_only) return;
    const sig_view = checker.pool.getFnSignatureView(fn_sym.type_id) orelse return;
    if (sig_view.ret_ty != .unit_ty) return;

    const fn_node = checker.ast_arena.getNode(fn_ast_id);
    if (fn_node.tag != .fn_decl or fn_node.rhs.tag != .node) return;
    const body_id = NodeIndex.fromInt(fn_node.rhs.payload);
    if (body_id.isNone() or body_id.asInt() >= checker.ast_arena.countNodes()) return;

    const body_node = checker.ast_arena.getNode(body_id);
    if (body_node.tag != .block or !body_node.rhs.isNone() or body_node.lhs.tag != .extra) return;

    const stmts = checker.getNodeExtraSlice(body_id, false);
    if (stmts.len == 0) return;
    const last_stmt_id = NodeIndex.fromInt(stmts[stmts.len - 1]);
    if (last_stmt_id.isNone() or last_stmt_id.asInt() >= checker.ast_arena.countNodes()) return;

    const last_stmt = checker.ast_arena.getNode(last_stmt_id);
    if (last_stmt.tag != .return_stmt or !last_stmt.lhs.isNone()) return;

    const ret_cst = checker.ast_arena.getCstOrigin(last_stmt_id);
    if (ret_cst.isNone() or hasSyntaxErrorInSubtree(checker.cst_arena, checker.token_buffer, ret_cst)) return;

    const body_cst = checker.ast_arena.getCstOrigin(body_id);
    if (body_cst.isNone() or body_cst.asInt() >= checker.cst_arena.countNodes()) return;

    // Ensure no trailing empty `;` or recovery tokens sit between `return;` and closing `}`:
    var block_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer block_children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, body_cst, &block_children);
    if (block_children.items.len < 3) return;
    if (block_children.items[block_children.items.len - 2] != ret_cst) return;

    const ret_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        ret_cst,
    ) orelse return;
    if (isW0202SuppressedAtSpan(checker, ret_span)) return;

    const first_tok = findFirstRealTokenInSubtree(checker.cst_arena, checker.token_buffer, ret_cst);
    const last_tok = findLastRealTokenInSubtree(checker.cst_arena, checker.token_buffer, ret_cst);
    if (first_tok.isNone() or last_tok.isNone()) return;
    if (checker.token_buffer.getToken(last_tok).kind != .semi) return;

    const has_inner_or_trailing_comments =
        hasCommentsInByteRange(checker.source, checker.token_buffer, ret_span.start_byte, ret_span.end_byte) or
        hasCommentInTriviaSlice(checker.source, checker.token_buffer.getTrailingTrivia(last_tok));
    if (has_inner_or_trailing_comments) return;

    var del_start: u32 = ret_span.start_byte;
    var del_end: u32 = ret_span.end_byte;
    if (!hasCommentInTriviaSlice(checker.source, checker.token_buffer.getLeadingTrivia(first_tok))) {
        var line_scan: usize = ret_span.start_byte;
        while (line_scan > 0 and (checker.source[line_scan - 1] == ' ' or checker.source[line_scan - 1] == '\t')) {
            line_scan -= 1;
        }
        const is_own_line = (line_scan == 0 or checker.source[line_scan - 1] == '\n');
        if (is_own_line and del_end < checker.source.len) {
            if (checker.source[del_end] == '\n') {
                del_start = @intCast(line_scan);
                del_end += 1;
            } else if (del_end + 1 < checker.source.len and
                checker.source[del_end] == '\r' and checker.source[del_end + 1] == '\n')
            {
                del_start = @intCast(line_scan);
                del_end += 2;
            }
        }
    }

    const edit = TextEdit{
        .file_id = checker.file_id,
        .start_byte = del_start,
        .end_byte = del_end,
        .replacement_id = try checker.interner.intern(""),
    };
    try emitIdiomWarning(
        sink_opt,
        ret_span,
        "redundant trailing `return;` at the end of a `unit`-returning function",
        "unnecessary trailing `return;`",
        "remove redundant trailing `return;`",
        &.{edit},
    );
}

/// Returns `true` if `pat_ast_id` is a valid non-`or_pat` refutable pattern safe inside `if scrut is Pat`.
fn isRefutableNonOrIsPattern(
    checker: *const TypeChecker,
    pat_ast_id: NodeIndex,
    depth: u32,
) bool {
    if (depth > 32 or pat_ast_id.isNone() or pat_ast_id.asInt() >= checker.ast_arena.countNodes()) return false;
    const pat_node = checker.ast_arena.getNode(pat_ast_id);
    return switch (pat_node.tag) {
        .or_pat, .wildcard_pat, .pattern_hole, .expr_hole => false,
        .bind_pat => blk: {
            // Bare `SCREAMING_SNAKE_CASE` `const_sym` identifier patterns are refutable constant tests:
            if (pat_ast_id.asInt() < checker.node_symbols.len) {
                const sym_idx = checker.node_symbols[pat_ast_id.asInt()];
                if (!sym_idx.isNone() and sym_idx.asInt() < checker.sym_table.countSymbols() and
                    checker.sym_table.getSymbol(sym_idx).kind == .const_sym)
                {
                    break :blk true;
                }
            }
            if (!pat_node.main_token.isNone() and pat_node.main_token.asInt() < checker.token_buffer.countTokens()) {
                if (checker.token_buffer.getToken(pat_node.main_token).kind == .const_ident) break :blk true;
            }
            break :blk false;
        },
        .lit_pat,
        .int_lit,
        .float_lit,
        .string_lit,
        .char_lit,
        .byte_lit,
        .byte_string_lit,
        .bool_lit,
        .range_expr,
        .variant_pat,
        .contextual_variant,
        .path_expr,
        => !hasOrPatInAstSubtree(checker, pat_ast_id, depth + 1),
        .at_pat => if (pat_node.rhs.tag == .node)
            isRefutableNonOrIsPattern(checker, NodeIndex.fromInt(pat_node.rhs.payload), depth + 1)
        else
            false,
        .tuple_pat, .struct_pat, .slice_pat => blk: {
            if (hasOrPatInAstSubtree(checker, pat_ast_id, depth + 1)) break :blk false;
            const pat_cst = checker.ast_arena.getCstOrigin(pat_ast_id);
            if (pat_cst.isNone()) break :blk false;
            break :blk hasRefutableLeafInPatternCst(checker, pat_cst);
        },
        else => false,
    };
}

/// Returns `true` if `pat_ast_id` or any child subpattern is an `.or_pat` (`A | B`).
fn hasOrPatInAstSubtree(checker: *const TypeChecker, pat_ast_id: NodeIndex, depth: u32) bool {
    if (depth > 32 or pat_ast_id.isNone() or pat_ast_id.asInt() >= checker.ast_arena.countNodes()) return true;
    const node = checker.ast_arena.getNode(pat_ast_id);
    if (node.tag == .or_pat or node.tag == .pattern_hole) return true;
    const pat_cst = checker.ast_arena.getCstOrigin(pat_ast_id);
    if (!pat_cst.isNone() and pat_cst.asInt() < checker.cst_arena.countNodes()) {
        const root = checker.cst_arena.getNode(pat_cst);
        const end_idx = @min(
            @as(usize, pat_cst.asInt()) + @max(@as(usize, root.subtree_size), 1),
            checker.cst_arena.countNodes(),
        );
        var cursor: usize = pat_cst.asInt();
        while (cursor < end_idx) : (cursor += 1) {
            if (checker.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor))).kind == .or_pat) return true;
        }
    }
    return false;
}

/// Returns `true` if `pat_cst` contains at least one refutable variant, literal, range, or slice pattern test.
fn hasRefutableLeafInPatternCst(checker: *const TypeChecker, pat_cst: CstNodeIndex) bool {
    const root = checker.cst_arena.getNode(pat_cst);
    const end_idx = @min(
        @as(usize, pat_cst.asInt()) + @max(@as(usize, root.subtree_size), 1),
        checker.cst_arena.countNodes(),
    );
    var cursor: usize = pat_cst.asInt();
    while (cursor < end_idx) : (cursor += 1) {
        const node = checker.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        switch (node.kind) {
            .variant_pat, .literal_pat, .range_pat, .slice_pat => return true,
            .ident_pat => {
                const tok = findFirstRealTokenInSubtree(
                    checker.cst_arena,
                    checker.token_buffer,
                    CstNodeIndex.fromInt(@intCast(cursor)),
                );
                if (!tok.isNone() and checker.token_buffer.getToken(tok).kind == .const_ident) return true;
            },
            else => {},
        }
    }
    return false;
}

/// Returns `true` if `sink_opt` already recorded a `W0401` unreachable-arm warning overlapping `arm_span`.
fn hasUnreachableArmWarning(sink_opt: ?*const DiagnosticSink, arm_span: Span) bool {
    const sink = sink_opt orelse return false;
    for (sink.diagnostics.items) |diag_item| {
        if (diag_item.code == .w0401_unreachable_pattern_arm and
            diag_item.primary_span.file_id == arm_span.file_id and
            diag_item.primary_span.end_byte > arm_span.start_byte and
            diag_item.primary_span.start_byte < arm_span.end_byte)
        {
            return true;
        }
    }
    return false;
}

/// Returns `true` if `arm_cst` contains an `if <guard>` clause before `=>`.
fn hasMatchArmGuardCst(
    cst_arena: *const LosslessCstArena,
    token_buffer: *const TokenBuffer,
    arm_cst: CstNodeIndex,
) bool {
    if (arm_cst.isNone() or arm_cst.asInt() >= cst_arena.countNodes()) return true;
    const arm_node = cst_arena.getNode(arm_cst);
    const end_idx = @min(
        @as(usize, arm_cst.asInt()) + @max(@as(usize, arm_node.subtree_size), 1),
        cst_arena.countNodes(),
    );
    const tok_count = token_buffer.countTokens();
    var cursor: usize = @as(usize, arm_cst.asInt()) + 1;
    while (cursor < end_idx) {
        const child = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
        if (child.subtree_size <= 1 and !child.token.isNone() and child.token.asInt() < tok_count) {
            const kind = token_buffer.getToken(child.token).kind;
            if (kind == .fat_arrow) return false;
            if (kind == .kw_if) return true;
        }
        cursor += @max(@as(usize, child.subtree_size), 1);
    }
    return true;
}

/// Returns `true` when `scrut_ast_id` needs `(…)` on the LHS of `is` (`bp = 6/7`) or to disambiguate `{`.
fn isScrutineeNeedingParensForIs(
    checker: *const TypeChecker,
    scrut_ast_id: NodeIndex,
    scrut_cst: CstNodeIndex,
) bool {
    if (hasStructLitOrBlockInSubtree(checker.cst_arena, checker.token_buffer, scrut_cst)) return true;
    if (scrut_ast_id.isNone() or scrut_ast_id.asInt() >= checker.ast_arena.countNodes()) return true;
    const node = checker.ast_arena.getNode(scrut_ast_id);
    return switch (node.tag) {
        .if_expr,
        .closure_expr,
        .is_expr,
        .walrus_expr,
        .return_stmt,
        .break_stmt,
        .continue_stmt,
        => true,
        .binary_expr => blk: {
            if (node.main_token.isNone() or node.main_token.asInt() >= checker.token_buffer.countTokens()) {
                break :blk true;
            }
            break :blk switch (checker.token_buffer.getToken(node.main_token).kind) {
                .kw_or, .kw_and, .eqeq, .bang_eq, .lt, .le, .gt, .ge, .kw_is => true,
                else => false,
            };
        },
        else => false,
    };
}

/// Idiom 5: Lints 2-arm statement `match scrut { Pat => { body }, _ => {} }` -> `if scrut is Pat { body }`.
/// Returns `true` when `match_ast_id` matched Idiom 5 so duplicate outer-paren lint on `scrut` is skipped.
fn lintTwoArmMatchToIfIs(
    checker: *TypeChecker,
    match_ast_id: NodeIndex,
    sink_opt: ?*DiagnosticSink,
) !bool {
    if (match_ast_id.isNone() or match_ast_id.asInt() >= checker.ast_arena.countNodes()) return false;
    const match_node = checker.ast_arena.getNode(match_ast_id);
    if (match_node.tag != .match_expr or match_node.lhs.tag != .node or match_node.rhs.tag != .extra) {
        return false;
    }
    if (getRecordedNodeType(checker, match_ast_id) != .unit_ty) return false;

    const scrut_id = NodeIndex.fromInt(match_node.lhs.payload);
    if (getRecordedNodeType(checker, scrut_id).isError()) return false;

    // Each arm occupies 2 words `[pat_node, body_node]` in `match_node.rhs`:
    const arm_words = checker.getNodeExtraSlice(match_ast_id, true);
    if (arm_words.len != 4) return false;

    const arm0_pat_id = NodeIndex.fromInt(arm_words[0]);
    const arm0_body_id = NodeIndex.fromInt(arm_words[1]);
    const arm1_pat_id = NodeIndex.fromInt(arm_words[2]);
    const arm1_body_id = NodeIndex.fromInt(arm_words[3]);
    if (arm0_pat_id.asInt() >= checker.ast_arena.countNodes() or
        arm0_body_id.asInt() >= checker.ast_arena.countNodes() or
        arm1_pat_id.asInt() >= checker.ast_arena.countNodes() or
        arm1_body_id.asInt() >= checker.ast_arena.countNodes())
    {
        return false;
    }
    if (checker.ast_arena.getNode(arm0_body_id).tag != .block) return false;
    if (checker.ast_arena.getNode(arm1_pat_id).tag != .wildcard_pat) return false;

    const arm1_body_node = checker.ast_arena.getNode(arm1_body_id);
    if (arm1_body_node.tag != .block or !arm1_body_node.lhs.isNone() or !arm1_body_node.rhs.isNone()) {
        return false;
    }
    if (!isRefutableNonOrIsPattern(checker, arm0_pat_id, 0)) return false;

    const match_cst = checker.ast_arena.getCstOrigin(match_ast_id);
    if (match_cst.isNone() or hasSyntaxErrorInSubtree(checker.cst_arena, checker.token_buffer, match_cst)) {
        return false;
    }

    var match_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer match_children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, match_cst, &match_children);

    var arm_csts: [2]CstNodeIndex = .{ .none, .none };
    var arm_cst_count: usize = 0;
    var scrut_cst: CstNodeIndex = .none;
    var has_seen_match_kw = false;
    var has_seen_lbrace = false;
    for (match_children.items) |child_cst| {
        const child_node = checker.cst_arena.getNode(child_cst);
        if (child_node.kind == .loop_label) return false;
        if (child_node.kind == .match_introducer) {
            has_seen_match_kw = true;
            continue;
        }
        if (child_node.subtree_size == 1 and !child_node.token.isNone() and
            checker.token_buffer.getToken(child_node.token).kind == .lbrace)
        {
            has_seen_lbrace = true;
            continue;
        }
        if (has_seen_match_kw and !has_seen_lbrace and scrut_cst.isNone()) {
            scrut_cst = child_cst;
            continue;
        }
        if (child_node.kind == .match_arm) {
            if (arm_cst_count >= 2) return false;
            arm_csts[arm_cst_count] = child_cst;
            arm_cst_count += 1;
        }
    }
    if (arm_cst_count != 2 or scrut_cst.isNone()) return false;
    if (hasMatchArmGuardCst(checker.cst_arena, checker.token_buffer, arm_csts[0]) or
        hasMatchArmGuardCst(checker.cst_arena, checker.token_buffer, arm_csts[1]))
    {
        return false;
    }

    // Ensure `_ => {}` has zero inner statements/semicolons and zero comments:
    const arm1_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        arm_csts[1],
    ) orelse return false;
    if (hasUnreachableArmWarning(sink_opt, arm1_span)) return false;
    if (hasCommentsInByteRange(checker.source, checker.token_buffer, arm1_span.start_byte, arm1_span.end_byte)) {
        return false;
    }
    const arm1_body_cst = checker.ast_arena.getCstOrigin(arm1_body_id);
    var arm1_block_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer arm1_block_children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, arm1_body_cst, &arm1_block_children);
    if (arm1_block_children.items.len != 2) return false;

    const match_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        match_cst,
    ) orelse return false;
    if (isW0202SuppressedAtSpan(checker, match_span)) return true;

    var clean_scrut_cst = scrut_cst;
    if (try matchRedundantOuterParenCst(checker, scrut_cst)) |unwrapped_scrut| {
        if (!hasCommentsInByteRange(
            checker.source,
            checker.token_buffer,
            checker.token_buffer.getToken(unwrapped_scrut.lparen_tok).byte_offset,
            checker.token_buffer.getToken(unwrapped_scrut.rparen_tok).byte_offset + 1,
        )) {
            clean_scrut_cst = unwrapped_scrut.inner_cst;
        }
    }

    const scrut_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        clean_scrut_cst,
    ) orelse return false;
    const pat_cst = checker.ast_arena.getCstOrigin(arm0_pat_id);
    const pat_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        pat_cst,
    ) orelse return false;
    const body_cst = checker.ast_arena.getCstOrigin(arm0_body_id);
    const body_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        body_cst,
    ) orelse return false;

    const has_lost_comments =
        hasCommentsInByteRange(checker.source, checker.token_buffer, match_span.start_byte, scrut_span.start_byte) or
        hasCommentsInByteRange(checker.source, checker.token_buffer, scrut_span.end_byte, pat_span.start_byte) or
        hasCommentsInByteRange(checker.source, checker.token_buffer, pat_span.end_byte, body_span.start_byte) or
        hasCommentsInByteRange(checker.source, checker.token_buffer, body_span.end_byte, match_span.end_byte);

    if (has_lost_comments) {
        try emitIdiomWarning(
            sink_opt,
            match_span,
            "single-arm `match` with empty wildcard `_ => {}` can be written as `if … is …`",
            "reducible to `if … is …`",
            "rewrite `match` to `if … is …`",
            &.{},
        );
        return true;
    }

    const wrap_scrut = clean_scrut_cst == scrut_cst and
        checker.cst_arena.getNode(clean_scrut_cst).kind != .tuple_or_paren_expr and
        isScrutineeNeedingParensForIs(checker, scrut_id, clean_scrut_cst) or
        (clean_scrut_cst != scrut_cst and isScrutineeNeedingParensForIs(checker, scrut_id, clean_scrut_cst));
    const wrap_pat = hasBraceInPatternSubtree(checker.cst_arena, checker.token_buffer, pat_cst);

    var repl_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer repl_buf.deinit(checker.allocator);
    try repl_buf.appendSlice(checker.allocator, "if ");
    if (wrap_scrut) try repl_buf.append(checker.allocator, '(');
    try repl_buf.appendSlice(checker.allocator, checker.source[scrut_span.start_byte..scrut_span.end_byte]);
    if (wrap_scrut) try repl_buf.append(checker.allocator, ')');
    try repl_buf.appendSlice(checker.allocator, " is ");
    if (wrap_pat) try repl_buf.append(checker.allocator, '(');
    try repl_buf.appendSlice(checker.allocator, checker.source[pat_span.start_byte..pat_span.end_byte]);
    if (wrap_pat) try repl_buf.append(checker.allocator, ')');
    try repl_buf.append(checker.allocator, ' ');
    try repl_buf.appendSlice(checker.allocator, checker.source[body_span.start_byte..body_span.end_byte]);

    const edit = TextEdit{
        .file_id = checker.file_id,
        .start_byte = match_span.start_byte,
        .end_byte = match_span.end_byte,
        .replacement_id = try checker.interner.intern(repl_buf.items),
    };
    try emitIdiomWarning(
        sink_opt,
        match_span,
        "single-arm `match` with empty wildcard `_ => {}` can be written as `if … is …`",
        "reducible to `if … is …`",
        "rewrite `match` to `if … is …`",
        &.{edit},
    );
    return true;
}

/// Extracts `BoolReturnBranchInfo` when `block_ast_id` is a single-statement `{ return true/false; }` block.
fn extractSingleBoolReturnBlock(
    checker: *const TypeChecker,
    block_ast_id: NodeIndex,
) ?BoolReturnBranchInfo {
    if (block_ast_id.isNone() or block_ast_id.asInt() >= checker.ast_arena.countNodes()) return null;
    const block_node = checker.ast_arena.getNode(block_ast_id);
    if (block_node.tag != .block or !block_node.rhs.isNone() or block_node.lhs.tag != .extra) return null;

    const stmts = checker.getNodeExtraSlice(block_ast_id, false);
    if (stmts.len != 1) return null;
    const stmt_id = NodeIndex.fromInt(stmts[0]);
    if (stmt_id.isNone() or stmt_id.asInt() >= checker.ast_arena.countNodes()) return null;
    const stmt_node = checker.ast_arena.getNode(stmt_id);
    if (stmt_node.tag != .return_stmt or stmt_node.lhs.tag != .node) return null;

    const val_id = NodeIndex.fromInt(stmt_node.lhs.payload);
    if (val_id.isNone() or val_id.asInt() >= checker.ast_arena.countNodes()) return null;
    const val_node = checker.ast_arena.getNode(val_id);
    if (val_node.tag != .bool_lit or val_node.main_token.isNone() or
        val_node.main_token.asInt() >= checker.token_buffer.countTokens())
    {
        return null;
    }
    const lit_tok = checker.token_buffer.getToken(val_node.main_token);
    if (lit_tok.flags.is_synthesized) return null;
    return switch (lit_tok.kind) {
        .kw_true => .{ .is_true_literal = true },
        .kw_false => .{ .is_true_literal = false },
        else => null,
    };
}

/// Idiom 6: Lints `if cond { return true; } else { return false; }` -> `return cond;` / `return not (<cond>);`.
/// Returns `true` when `if_ast_id` matched Idiom 6 so duplicate outer-paren lint on `cond` is skipped.
fn lintBoolReturnIfElse(
    checker: *TypeChecker,
    if_ast_id: NodeIndex,
    sink_opt: ?*DiagnosticSink,
) !bool {
    if (if_ast_id.isNone() or if_ast_id.asInt() >= checker.ast_arena.countNodes()) return false;
    const if_node = checker.ast_arena.getNode(if_ast_id);
    if (if_node.tag != .if_expr or if_node.lhs.tag != .node or if_node.rhs.tag != .extra) return false;

    const cond_id = NodeIndex.fromInt(if_node.lhs.payload);
    if (getRecordedNodeType(checker, cond_id) != .bool_ty) return false;

    const branches = checker.getNodeExtraSlice(if_ast_id, true);
    if (branches.len != 2) return false;
    const then_id = NodeIndex.fromInt(branches[0]);
    const else_id = NodeIndex.fromInt(branches[1]);

    const then_info = extractSingleBoolReturnBlock(checker, then_id) orelse return false;
    const else_info = extractSingleBoolReturnBlock(checker, else_id) orelse return false;
    if (then_info.is_true_literal == else_info.is_true_literal) return false;

    const if_cst = checker.ast_arena.getCstOrigin(if_ast_id);
    if (if_cst.isNone() or hasSyntaxErrorInSubtree(checker.cst_arena, checker.token_buffer, if_cst)) {
        return false;
    }
    const cond_cst = checker.ast_arena.getCstOrigin(cond_id);
    if (hasWalrusInSubtree(checker.cst_arena, checker.token_buffer, cond_cst)) return false;
    if (hasIsBindingInExprAst(checker, cond_id, 0)) return false;

    const if_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        if_cst,
    ) orelse return false;
    if (isW0202SuppressedAtSpan(checker, if_span)) return true;

    var clean_cond_cst = cond_cst;
    if (!cond_cst.isNone()) {
        if (try matchRedundantOuterParenCst(checker, cond_cst)) |unwrapped_cond| {
            clean_cond_cst = unwrapped_cond.inner_cst;
        }
    }
    const cond_span = getCstSubtreeSpan(
        checker.file_id,
        checker.cst_arena,
        checker.token_buffer,
        clean_cond_cst,
    ) orelse checker.getAstNodeSpan(cond_id);

    const has_lost_comments =
        hasCommentsInByteRange(checker.source, checker.token_buffer, if_span.start_byte, cond_span.start_byte) or
        hasCommentsInByteRange(checker.source, checker.token_buffer, cond_span.end_byte, if_span.end_byte);
    if (has_lost_comments) return false;

    const cond_slice = checker.source[cond_span.start_byte..cond_span.end_byte];
    var repl_buf: std.ArrayListUnmanaged(u8) = .empty;
    defer repl_buf.deinit(checker.allocator);

    if (then_info.is_true_literal) {
        try repl_buf.appendSlice(checker.allocator, "return ");
        try repl_buf.appendSlice(checker.allocator, cond_slice);
        try repl_buf.append(checker.allocator, ';');
    } else if (isNotOperandNeedingParens(checker, cond_id)) {
        try repl_buf.appendSlice(checker.allocator, "return not (");
        try repl_buf.appendSlice(checker.allocator, cond_slice);
        try repl_buf.appendSlice(checker.allocator, ");");
    } else {
        try repl_buf.appendSlice(checker.allocator, "return not ");
        try repl_buf.appendSlice(checker.allocator, cond_slice);
        try repl_buf.append(checker.allocator, ';');
    }

    const edit = TextEdit{
        .file_id = checker.file_id,
        .start_byte = if_span.start_byte,
        .end_byte = if_span.end_byte,
        .replacement_id = try checker.interner.intern(repl_buf.items),
    };
    try emitIdiomWarning(
        sink_opt,
        if_span,
        "redundant `if … { return true; } else { return false; }`; return the boolean expression directly",
        "simplify boolean `return` branch",
        "simplify `if`/`else` boolean return",
        &.{edit},
    );
    return true;
}

/// Returns `true` if `kind` is an item declaration CST node gated by `@cfg(…)`.
fn isCfgGateableItemCstKind(kind: CstNodeKind) bool {
    return switch (kind) {
        .mod_item,
        .use_item,
        .const_item,
        .type_alias_item,
        .struct_item,
        .struct_field,
        .enum_item,
        .enum_variant,
        .union_item,
        .trait_item,
        .trait_member,
        .impl_item,
        .impl_member,
        .bit_field_item,
        .bit_field_member,
        .subscript_item,
        .test_item,
        .bench_item,
        .fn_item,
        .extern_block_item,
        .extern_static_item,
        => true,
        else => false,
    };
}

/// Walks AST statements inside `block_ast_id` to lint statement-position Idioms 5 and 6, recording
/// suppressed header `CstNodeIndex` nodes in `suppressed_headers` to prevent duplicate Idiom 1 hits.
fn lintBlockStatementsAst(
    checker: *TypeChecker,
    block_ast_id: NodeIndex,
    suppressed_headers: *std.AutoHashMapUnmanaged(u32, void),
    sink_opt: ?*DiagnosticSink,
) !void {
    if (block_ast_id.isNone() or block_ast_id.asInt() >= checker.ast_arena.countNodes()) return;
    const block_node = checker.ast_arena.getNode(block_ast_id);
    if (block_node.tag != .block) return;

    if (block_node.lhs.tag == .extra) {
        for (checker.getNodeExtraSlice(block_ast_id, false)) |raw_stmt| {
            const stmt_id = NodeIndex.fromInt(raw_stmt);
            if (stmt_id.isNone() or stmt_id.asInt() >= checker.ast_arena.countNodes()) continue;
            const stmt_tag = checker.ast_arena.getNode(stmt_id).tag;
            if (stmt_tag == .match_expr) {
                if (try lintTwoArmMatchToIfIs(checker, stmt_id, sink_opt)) {
                    const m_cst = checker.ast_arena.getCstOrigin(stmt_id);
                    if (!m_cst.isNone()) try suppressed_headers.put(checker.allocator, m_cst.asInt(), {});
                }
            } else if (stmt_tag == .if_expr) {
                if (try lintBoolReturnIfElse(checker, stmt_id, sink_opt)) {
                    const i_cst = checker.ast_arena.getCstOrigin(stmt_id);
                    if (!i_cst.isNone()) try suppressed_headers.put(checker.allocator, i_cst.asInt(), {});
                }
            }
        }
    }
    if (block_node.rhs.tag == .node) {
        const tail_id = NodeIndex.fromInt(block_node.rhs.payload);
        if (!tail_id.isNone() and tail_id.asInt() < checker.ast_arena.countNodes()) {
            const tail_tag = checker.ast_arena.getNode(tail_id).tag;
            if (tail_tag == .match_expr and getRecordedNodeType(checker, block_ast_id) == .unit_ty) {
                if (try lintTwoArmMatchToIfIs(checker, tail_id, sink_opt)) {
                    const m_cst = checker.ast_arena.getCstOrigin(tail_id);
                    if (!m_cst.isNone()) try suppressed_headers.put(checker.allocator, m_cst.asInt(), {});
                }
            } else if (tail_tag == .if_expr) {
                if (try lintBoolReturnIfElse(checker, tail_id, sink_opt)) {
                    const i_cst = checker.ast_arena.getCstOrigin(tail_id);
                    if (!i_cst.isNone()) try suppressed_headers.put(checker.allocator, i_cst.asInt(), {});
                }
            }
        }
    }
}

/// Recursively lints a CST subtree (`is_signature_mode == true` skips `DefId`-owned item bodies).
fn walkAndLintCstSubtree(
    checker: *TypeChecker,
    cst_idx: CstNodeIndex,
    parent_cst: CstNodeIndex,
    grandparent_cst: CstNodeIndex,
    is_signature_mode: bool,
    is_inside_trait_item: bool,
    suppressed_headers: *std.AutoHashMapUnmanaged(u32, void),
    sink_opt: ?*DiagnosticSink,
    depth: u32,
) anyerror!void {
    if (depth > syntax_arenas.MAX_PARSE_DEPTH or cst_idx.isNone() or
        cst_idx.asInt() >= checker.cst_arena.countNodes())
    {
        return;
    }

    const node = checker.cst_arena.getNode(cst_idx);
    if (isCfgGateableItemCstKind(node.kind) and !checker.isCstNodeCfgEnabled(cst_idx)) return;
    if (!checker.is_including_tests and (node.kind == .test_item or node.kind == .bench_item)) return;

    // [1] In body mode, check `.block` statements first so Idioms 5 & 6 suppress duplicate Idiom 1 hits:
    if (!is_signature_mode and node.kind == .block and cst_idx.asInt() < checker.cst_to_ast.len) {
        const block_ast = checker.cst_to_ast[cst_idx.asInt()];
        if (!block_ast.isNone()) {
            try lintBlockStatementsAst(checker, block_ast, suppressed_headers, sink_opt);
        }
    }

    // [2] Idiom 3: Canonical `Option[T]` / `Result[T, E]` surface type annotations:
    if (node.kind == .named_type) {
        try lintCanonicalGenericTypeCst(checker, cst_idx, parent_cst, grandparent_cst, sink_opt);
    }

    // [3] Idiom 2: Scalar `bool` literal equality/inequality (`x == true`, `x != false`, etc.):
    if (node.kind == .infix_expr and cst_idx.asInt() < checker.cst_to_ast.len) {
        const bin_ast = checker.cst_to_ast[cst_idx.asInt()];
        if (!bin_ast.isNone()) {
            try lintRedundantBoolEqualityAst(checker, bin_ast, sink_opt);
        }
    }

    // [4] Idiom 1: Redundant outer `(` … `)` around `if`, `while`, and `match` headers:
    if ((node.kind == .if_cond or node.kind == .while_header) and
        !suppressed_headers.contains(parent_cst.asInt()))
    {
        var hdr_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
        defer hdr_children.deinit(checker.allocator);
        try collectDirectCstChildren(checker.allocator, checker.cst_arena, cst_idx, &hdr_children);
        if (hdr_children.items.len == 1) {
            try lintRedundantHeaderParensInCst(
                checker,
                hdr_children.items[0],
                if (node.kind == .if_cond) "if" else "while",
                sink_opt,
            );
        }
    } else if (node.kind == .match_expr and !suppressed_headers.contains(cst_idx.asInt())) {
        var match_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
        defer match_children.deinit(checker.allocator);
        try collectDirectCstChildren(checker.allocator, checker.cst_arena, cst_idx, &match_children);
        var seen_match_kw = false;
        for (match_children.items) |m_child| {
            const m_node = checker.cst_arena.getNode(m_child);
            if (m_node.kind == .match_introducer) {
                seen_match_kw = true;
                continue;
            }
            if (!seen_match_kw) continue;
            if (m_node.subtree_size == 1 and !m_node.token.isNone() and
                checker.token_buffer.getToken(m_node.token).kind == .lbrace)
            {
                break;
            }
            try lintRedundantHeaderParensInCst(checker, m_child, "match", sink_opt);
            break;
        }
    }

    if (node.subtree_size <= 1) return;

    // [5] Recurse into children while respecting signature vs. `DefId` body ownership boundaries:
    var children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, cst_idx, &children);

    const next_in_trait = is_inside_trait_item or (node.kind == .trait_item);
    var has_passed_const_eq = false;

    for (children.items, 0..) |child_cst, child_pos| {
        const child_node = checker.cst_arena.getNode(child_cst);
        if (is_signature_mode) {
            if (node.kind == .fn_item and !is_inside_trait_item and
                (child_node.kind == .block or child_node.kind == .fn_expr_body))
            {
                continue;
            }
            if ((node.kind == .test_item or node.kind == .bench_item or node.kind == .subscript_arm) and
                child_node.kind == .block)
            {
                continue;
            }
            if (node.kind == .const_item and !is_inside_trait_item) {
                if (child_node.subtree_size == 1 and !child_node.token.isNone() and
                    checker.token_buffer.getToken(child_node.token).kind == .eq)
                {
                    has_passed_const_eq = true;
                    continue;
                }
                if (has_passed_const_eq) continue;
            }
            if ((node.kind == .file_end or node.kind == .mod_item) and child_node.kind == .block) {
                continue;
            }
            if ((node.kind == .file_end or node.kind == .mod_item) and
                child_node.subtree_size == 1 and !child_node.token.isNone() and
                checker.token_buffer.getToken(child_node.token).kind == .kw_comptime and
                child_pos + 1 < children.items.len and
                checker.cst_arena.getNode(children.items[child_pos + 1]).kind == .block)
            {
                continue;
            }
        }
        try walkAndLintCstSubtree(
            checker,
            child_cst,
            cst_idx,
            parent_cst,
            is_signature_mode,
            next_in_trait,
            suppressed_headers,
            sink_opt,
            depth + 1,
        );
    }
}

/// Lints only the body CST subtrees of a single function, subscript, test, bench, or `const` AST item.
fn lintSingleItemBodyAst(
    checker: *TypeChecker,
    sym_idx: SymbolIndex,
    item_ast_id: NodeIndex,
    suppressed_headers: *std.AutoHashMapUnmanaged(u32, void),
    sink_opt: ?*DiagnosticSink,
) !void {
    if (item_ast_id.isNone() or item_ast_id.asInt() >= checker.ast_arena.countNodes()) return;
    const item_cst = checker.ast_arena.getCstOrigin(item_ast_id);
    if (item_cst.isNone() or !checker.isCstNodeCfgEnabled(item_cst)) return;

    const ast_node = checker.ast_arena.getNode(item_ast_id);
    if (ast_node.tag == .fn_decl and !sym_idx.isNone()) {
        try lintTrailingUnitReturnFnDecl(checker, sym_idx, item_ast_id, sink_opt);
    }

    if (ast_node.tag == .block) {
        try walkAndLintCstSubtree(
            checker,
            item_cst,
            .none,
            .none,
            false,
            false,
            suppressed_headers,
            sink_opt,
            0,
        );
        return;
    }

    var children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
    defer children.deinit(checker.allocator);
    try collectDirectCstChildren(checker.allocator, checker.cst_arena, item_cst, &children);

    var has_passed_const_eq = false;
    for (children.items) |child_cst| {
        const child_node = checker.cst_arena.getNode(child_cst);
        switch (ast_node.tag) {
            .fn_decl => {
                if (child_node.kind == .block or child_node.kind == .fn_expr_body) {
                    try walkAndLintCstSubtree(
                        checker,
                        child_cst,
                        item_cst,
                        .none,
                        false,
                        false,
                        suppressed_headers,
                        sink_opt,
                        1,
                    );
                }
            },
            .test_decl, .bench_decl => {
                if (child_node.kind == .block) {
                    try walkAndLintCstSubtree(
                        checker,
                        child_cst,
                        item_cst,
                        .none,
                        false,
                        false,
                        suppressed_headers,
                        sink_opt,
                        1,
                    );
                }
            },
            .subscript_decl => {
                if (child_node.kind == .subscript_arm) {
                    var arm_children: std.ArrayListUnmanaged(CstNodeIndex) = .empty;
                    defer arm_children.deinit(checker.allocator);
                    try collectDirectCstChildren(checker.allocator, checker.cst_arena, child_cst, &arm_children);
                    for (arm_children.items) |arm_part| {
                        if (checker.cst_arena.getNode(arm_part).kind == .block) {
                            try walkAndLintCstSubtree(
                                checker,
                                arm_part,
                                child_cst,
                                item_cst,
                                false,
                                false,
                                suppressed_headers,
                                sink_opt,
                                2,
                            );
                        }
                    }
                }
            },
            .const_decl => {
                if (child_node.subtree_size == 1 and !child_node.token.isNone() and
                    checker.token_buffer.getToken(child_node.token).kind == .eq)
                {
                    has_passed_const_eq = true;
                    continue;
                }
                if (has_passed_const_eq) {
                    try walkAndLintCstSubtree(
                        checker,
                        child_cst,
                        item_cst,
                        .none,
                        false,
                        false,
                        suppressed_headers,
                        sink_opt,
                        1,
                    );
                }
            },
            else => {},
        }
    }
}

/// Sorts `FileId` handles in deterministic ascending integer order.
fn compareFileIdAsc(_: void, lhs_fid: FileId, rhs_fid: FileId) bool {
    return lhs_fid.asInt() < rhs_fid.asInt();
}

/// Discovers and snapshots all editable `.root` `.cx` files for `applyCheckFixesOnDb`.
fn collectEditableRootCandidates(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    options: CheckFixOptions,
    out_snapshots: *std.ArrayListUnmanaged(CandidateFileSnapshot),
) !void {
    var candidate_ids: std.ArrayListUnmanaged(FileId) = .empty;
    defer candidate_ids.deinit(allocator);
    var seen_ids: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer seen_ids.deinit(allocator);

    if (options.candidate_files) |explicit_files| {
        for (explicit_files) |fid| {
            if (fid.isNone() or fid.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) continue;
            if (!(try seen_ids.getOrPut(allocator, fid.asInt())).found_existing) {
                try candidate_ids.append(allocator, fid);
            }
        }
    } else {
        var inp_it = db.source_inputs.keyIterator();
        while (inp_it.next()) |raw_fid_ptr| {
            const fid = FileId.fromInt(raw_fid_ptr.*);
            if (fid.isNone() or fid.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) continue;
            if (!(try seen_ids.getOrPut(allocator, fid.asInt())).found_existing) {
                try candidate_ids.append(allocator, fid);
            }
        }
    }
    std.mem.sort(FileId, candidate_ids.items, {}, compareFileIdAsc);

    for (candidate_ids.items) |fid| {
        if (db.symbol_table.getFilePackageId(fid) != .root) continue;
        if (db.isStdlibFile(fid)) continue;

        var was_open = false;
        var has_disk = false;
        var resolved_path: []const u8 = "";
        if (options.vfs) |vfs_ptr| {
            if (vfs_ptr.getFileEntry(fid)) |entry| {
                if (entry.package_id != .root or entry.backing_kind == .cxtree_archive) continue;
                was_open = entry.is_open_in_editor;
                has_disk = entry.has_disk_backing;
                const os_path = vfs_ptr.interner.get(entry.resolved_os_path);
                resolved_path = if (os_path.len > 0) os_path else vfs_ptr.getFilePath(fid);
            }
        }
        if (resolved_path.len == 0) {
            if (db.file_paths.get(fid.asInt())) |path_slice| {
                resolved_path = path_slice;
            }
        }

        const src_text = db.getSourceText(fid) catch continue;
        if (isGeneratedSourceHeader(src_text)) continue;

        var disk_prefix_copy: ?[]u8 = null;
        errdefer if (disk_prefix_copy) |pref_buf| allocator.free(pref_buf);
        var was_prefix_masked = false;

        if (options.write_to_disk and resolved_path.len > 0) {
            if (options.io) |io_handle| {
                const raw_disk_opt: ?[]u8 = std.Io.Dir.cwd().readFileAlloc(
                    io_handle,
                    resolved_path,
                    allocator,
                    .limited(vfs_sourcemap.MAX_SOURCE_FILE_BYTES),
                ) catch null;
                defer if (raw_disk_opt) |raw_buf| allocator.free(raw_buf);

                if (raw_disk_opt) |raw_disk| {
                    has_disk = true;
                    if (isGeneratedSourceHeader(raw_disk)) continue;

                    var fm_arena = mem_foundation.BumpArena.init(allocator);
                    defer fm_arena.deinit();
                    if (try pkg_manifest.extractScriptFrontmatter(&fm_arena, fid, raw_disk, null)) |extracted| {
                        const prefix_len: usize = extracted.prefix_end_byte;
                        if (prefix_len > 0 and src_text.len >= prefix_len) {
                            const matches_raw = std.mem.eql(u8, src_text[0..prefix_len], raw_disk[0..prefix_len]);
                            const matches_blanked = std.mem.eql(
                                u8,
                                src_text[0..prefix_len],
                                extracted.blanked_cx_source[0..prefix_len],
                            );
                            if (matches_raw or matches_blanked) {
                                disk_prefix_copy = try allocator.dupe(u8, raw_disk[0..prefix_len]);
                                was_prefix_masked = !matches_raw;
                            }
                        }
                    }
                }
            }
        }

        const duped_src = try allocator.dupe(u8, src_text);
        errdefer allocator.free(duped_src);
        const duped_path = try allocator.dupe(u8, resolved_path);
        errdefer allocator.free(duped_path);

        try out_snapshots.append(allocator, .{
            .file_id = fid,
            .original_bytes = duped_src,
            .disk_script_prefix = disk_prefix_copy,
            .file_path = duped_path,
            .was_prefix_masked_in_db = was_prefix_masked,
            .was_open_in_editor = was_open,
            .has_disk_backing = has_disk,
        });
    }
}

/// Runs `parseCst`, `resolveSignatures`, `typecheckBody`, and `verifySastMir` across `snapshots`,
/// returning `(total_error_count, has_any_new_syntax_error)`.
fn runFullCheckAcrossSnapshots(
    db: *CompilerDb,
    snapshots: []CandidateFileSnapshot,
    is_recording_baseline_syntax: bool,
) !struct {
    /// Combined parse, signature, body, and SAST error count across `snapshots`.
    total_errors: u32,
    /// `true` if any file without baseline syntax errors introduced a syntax error.
    has_new_syntax_errors: bool,
} {
    var total_errors: u32 = 0;
    var has_new_syntax = false;

    for (snapshots) |*snap| {
        const parsed_art = try db.parseCst(snap.file_id);
        const has_syntax_err = parsed_art.cst_arena.has_parse_errors or parsed_art.diagnostics.hasErrors();
        if (is_recording_baseline_syntax) {
            snap.had_baseline_syntax_errors = has_syntax_err;
        } else if (has_syntax_err and !snap.had_baseline_syntax_errors) {
            has_new_syntax = true;
        }
        total_errors +|= parsed_art.diagnostics.error_count;
    }

    for (snapshots) |snap| {
        const sig_art = try db.resolveSignatures(snap.file_id);
        total_errors +|= sig_art.error_count;
    }

    for (snapshots) |snap| {
        var entry_idx: usize = 0;
        while (entry_idx < (try db.extractItemTree(snap.file_id)).entries.len) : (entry_idx += 1) {
            const entry = (try db.extractItemTree(snap.file_id)).entries[entry_idx];
            const body_art = try db.typecheckBody(entry.def_id);
            total_errors +|= body_art.error_count;
            const sast_art = try db.verifySastMir(entry.def_id);
            total_errors +|= sast_art.error_count;
        }
    }

    return .{
        .total_errors = total_errors,
        .has_new_syntax_errors = has_new_syntax,
    };
}

/// Appends `.machine_applicable` `SuggestedFix` items from `sink` targeting `file_id` into `out_fixes`.
fn appendSinkMachineFixesForFile(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    file_id: FileId,
    sink: *const DiagnosticSink,
    is_parse_sink: bool,
    out_fixes: *std.ArrayListUnmanaged(SuggestedFix),
) !void {
    for (sink.diagnostics.items) |diag_item| {
        if (is_parse_sink and diag_item.code == .e0220_retired_bang_prefix and diag_item.suggestions.len == 0) {
            if (try db.resolveBangFixSuggestion(file_id, diag_item.primary_span)) |bang_fix| {
                if (bang_fix.applicability == .machine_applicable and bang_fix.edits.len > 0) {
                    try out_fixes.append(allocator, bang_fix);
                }
                continue;
            }
        }
        for (diag_item.suggestions) |sug_item| {
            if (sug_item.applicability != .machine_applicable or sug_item.edits.len == 0) continue;
            var is_all_same_file = true;
            for (sug_item.edits) |edit_item| {
                if (edit_item.file_id != file_id) {
                    is_all_same_file = false;
                    break;
                }
            }
            if (is_all_same_file) {
                try out_fixes.append(allocator, sug_item);
            }
        }
    }
}

/// Synchronizes `new_bytes` for `snap` into both `options.vfs` (when provided) and `db.setInput`.
fn updateFileOverlayAndDb(
    db: *CompilerDb,
    options: CheckFixOptions,
    snap: CandidateFileSnapshot,
    new_bytes: []const u8,
) !void {
    if (options.vfs) |vfs_ptr| {
        if (snap.file_path.len > 0) {
            const vpath = vfs_ptr.getFilePath(snap.file_id);
            const target_vpath = if (vpath.len > 0) vpath else snap.file_path;
            _ = try vfs_ptr.setEditorOverlay(
                options.io,
                target_vpath,
                new_bytes,
                .root,
                snap.was_open_in_editor,
            );
            _ = vfs_ptr.getLineIndex(snap.file_id) catch {};
        }
    }
    _ = try db.setInput(snap.file_id, new_bytes, .low);
}

/// Restores all modified files in `snapshots` back to their pre-fix `original_bytes` in VFS and `db`.
fn rollbackSnapshotsInMemory(
    db: *CompilerDb,
    options: CheckFixOptions,
    snapshots: []CandidateFileSnapshot,
) !void {
    for (snapshots) |*snap| {
        if (!snap.is_modified) continue;
        try updateFileOverlayAndDb(db, options, snap.*, snap.original_bytes);
        snap.is_modified = false;
    }
    _ = try runFullCheckAcrossSnapshots(db, snapshots, false);
}

/// Formats an `EffectCapabilityMask` bitset into `"[] (pure)"` or `"[fs, net, clock]"` (`"unsafe_op"` canonical).
fn formatCapMaskCellAlloc(
    allocator: std.mem.Allocator,
    raw_bits: u16,
    include_opaque: bool,
) ![]u8 {
    const mask_filter: u16 = if (include_opaque)
        (EffectCapabilityMask.LOCKFILE_CAP_BITS | EffectCapabilityMask.INDIRECT_OPAQUE_BIT)
    else
        EffectCapabilityMask.LOCKFILE_CAP_BITS;
    const masked_bits = raw_bits & mask_filter;
    if (masked_bits == 0) {
        return allocator.dupe(u8, "[] (pure)");
    }

    var builder: std.ArrayListUnmanaged(u8) = .empty;
    errdefer builder.deinit(allocator);
    try builder.append(allocator, '[');
    var is_first = true;
    for (CANONICAL_AUDIT_CAPS) |cap_spec| {
        if ((masked_bits & cap_spec.bit) != 0) {
            if (!is_first) try builder.appendSlice(allocator, ", ");
            try builder.appendSlice(allocator, cap_spec.name);
            is_first = false;
        }
    }
    if (include_opaque and (masked_bits & OPAQUE_ESCALATION_CAP.bit) != 0) {
        if (!is_first) try builder.appendSlice(allocator, ", ");
        try builder.appendSlice(allocator, OPAQUE_ESCALATION_CAP.name);
    }
    try builder.append(allocator, ']');
    return builder.toOwnedSlice(allocator);
}

/// Formats a styled `Policy Status` cell for `renderCapabilityAuditTable`.
fn formatPolicyStatusCellAlloc(
    allocator: std.mem.Allocator,
    style_config: StyleConfig,
    is_standalone_mode: bool,
    is_root_pkg: bool,
    surface_bits: u16,
    escalated_bits: u16,
    denied_bits: u16,
) ![]u8 {
    var cell_buf: [256]u8 = undefined;
    var fixed_writer = std.Io.Writer.fixed(&cell_buf);

    if (escalated_bits != 0 or denied_bits != 0) {
        const viol_bits = if (escalated_bits != 0) escalated_bits else denied_bits;
        const status_verb: []const u8 = if (escalated_bits != 0) "escalated" else "denied";
        const bracketed = try formatCapMaskCellAlloc(allocator, viol_bits, true);
        defer allocator.free(bracketed);

        var plain_buf: [192]u8 = undefined;
        const plain_str = try std.fmt.bufPrint(
            &plain_buf,
            "{s} {s} ({s})",
            .{ Glyphs.FAILURE, status_verb, bracketed },
        );
        try style_config.writeStyled(&fixed_writer, .err, plain_str);
        return allocator.dupe(u8, fixed_writer.buffered());
    }

    if (is_standalone_mode) {
        var plain_buf: [64]u8 = undefined;
        const plain_str = try std.fmt.bufPrint(&plain_buf, "{s} standalone", .{Glyphs.SUCCESS});
        try style_config.writeStyled(&fixed_writer, .success, plain_str);
        return allocator.dupe(u8, fixed_writer.buffered());
    }

    if (is_root_pkg) {
        var plain_buf: [64]u8 = undefined;
        const plain_str = try std.fmt.bufPrint(&plain_buf, "{s} root package", .{Glyphs.BULLET});
        try style_config.writeStyled(&fixed_writer, .note, plain_str);
        return allocator.dupe(u8, fixed_writer.buffered());
    }

    if ((surface_bits & EffectCapabilityMask.LOCKFILE_CAP_BITS) == 0) {
        var plain_buf: [64]u8 = undefined;
        const plain_str = try std.fmt.bufPrint(&plain_buf, "{s} pure sandbox", .{Glyphs.SUCCESS});
        try style_config.writeStyled(&fixed_writer, .success, plain_str);
        return allocator.dupe(u8, fixed_writer.buffered());
    }

    var plain_buf: [64]u8 = undefined;
    const plain_str = try std.fmt.bufPrint(&plain_buf, "{s} allowed", .{Glyphs.SUCCESS});
    try style_config.writeStyled(&fixed_writer, .success, plain_str);
    return allocator.dupe(u8, fixed_writer.buffered());
}

/// Counts verified `@no_alloc` / `@no_panic` functions across `audited_files` and detects SAST contract errors.
fn inspectContractVerificationInFiles(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    audited_files: []const FileId,
) !struct {
    /// Count of verified `@no_alloc` and/or `@no_panic` function bodies.
    verified_fn_count: u32,
    /// `true` if any `E0316` or `E0320`–`E0325` contract error fired.
    has_sast_contract_errors: bool,
} {
    var file_set: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer file_set.deinit(allocator);
    for (audited_files) |fid| {
        if (!fid.isNone()) try file_set.put(allocator, fid.asInt(), {});
    }

    var failed_defs: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer failed_defs.deinit(allocator);
    var has_contract_err = false;

    for (audited_files) |fid| {
        if (fid.isNone()) continue;
        const entries = (db.extractItemTree(fid) catch continue).entries;
        for (entries) |entry| {
            const sast_art = db.verifySastMir(entry.def_id) catch continue;
            if (!sast_art.is_verified_sound or sast_art.error_count > 0) {
                try failed_defs.put(allocator, entry.def_id.asInt(), {});
            }
            if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                for (sast_sink.diagnostics.items) |diag_item| {
                    switch (diag_item.code) {
                        .e0316_max_stack_budget_exceeded,
                        .e0320_no_alloc_contract_violation,
                        .e0321_no_panic_contract_violation,
                        .e0322_no_block_contract_violation,
                        .e0324_package_capability_violation,
                        .e0325_comptime_sandbox_violation,
                        => has_contract_err = true,
                        else => {},
                    }
                }
            }
        }
    }

    var verified_count: u32 = 0;
    var sym_i: u32 = 0;
    while (sym_i < db.symbol_table.countSymbols()) : (sym_i += 1) {
        const sym_idx = SymbolIndex.fromInt(sym_i);
        const sym_rec = db.symbol_table.getSymbol(sym_idx).*;
        if (sym_rec.kind != .fn_sym or sym_rec.flags.is_extern or sym_rec.flags.is_prototype_only) continue;
        if (!file_set.contains(sym_rec.decl_span.file_id.asInt())) continue;

        const has_contract = if (db.sast_sym_summaries.get(sym_i)) |sum_rec|
            (sum_rec.contractsScratch().has_no_alloc or sum_rec.contractsScratch().has_no_panic)
        else
            (sym_rec.contract_flags.is_no_alloc or sym_rec.contract_flags.is_no_panic);
        if (!has_contract) continue;

        const owner_def = if (!sym_rec.def_id.isNone()) sym_rec.def_id else sym_rec.owner_def_id;
        if (!owner_def.isNone() and failed_defs.contains(owner_def.asInt())) continue;
        if (!db.sast_sym_summaries.contains(sym_i) and
            (owner_def.isNone() or !db.sast_summaries.contains(owner_def.asInt())))
        {
            continue;
        }
        verified_count += 1;
    }

    return .{
        .verified_fn_count = verified_count,
        .has_sast_contract_errors = has_contract_err,
    };
}

/// Looks up a matching `LockPackage` record in `lockfile` by `(canonical_name, version)`.
fn findLockfilePackage(
    lockfile_opt: ?*const pkg_manifest.Lockfile,
    interner: *const StringInterner,
    canonical_name: []const u8,
    version: pkg_manifest.SemVer,
) ?pkg_manifest.LockPackage {
    const lockfile = lockfile_opt orelse return null;
    for (lockfile.packages) |lock_pkg| {
        if (std.mem.eql(u8, interner.get(lock_pkg.name), canonical_name) and
            pkg_manifest.SemVer.eql(lock_pkg.version, version, interner))
        {
            return lock_pkg;
        }
    }
    return null;
}

/// Normalizes backslashes `\` to forward slashes `/` in a newly allocated display path.
fn normalizeDisplayPathAlloc(
    allocator: std.mem.Allocator,
    db: *const CompilerDb,
    vfs_opt: ?*const VfsSourceMap,
    file_id: FileId,
) ![]u8 {
    var raw_path: []const u8 = "";
    if (vfs_opt) |vfs_ptr| {
        raw_path = vfs_ptr.getFilePath(file_id);
    }
    if (raw_path.len == 0) {
        if (db.file_paths.get(file_id.asInt())) |path_slice| {
            raw_path = path_slice;
        }
    }
    if (raw_path.len == 0) {
        return std.fmt.allocPrint(allocator, "<file:{d}>", .{file_id.asInt()});
    }
    const duped = try allocator.dupe(u8, raw_path);
    for (duped) |*ch_ptr| {
        if (ch_ptr.* == '\\') ch_ptr.* = '/';
    }
    return duped;
}

/// Resolves 1-based `(line, col_utf8)` for `(file_id, byte_offset)` via `VfsSourceMap` or transient `LineIndex`.
fn resolveFileLineCol(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    vfs_opt: ?*VfsSourceMap,
    file_id: FileId,
    byte_offset: u32,
) !struct {
    /// 1-based source line number.
    line: u32,
    /// 1-based UTF-8 codepoint column.
    col: u32,
} {
    if (file_id.isNone()) return .{ .line = 1, .col = 1 };
    const src_text = db.getSourceText(file_id) catch return .{ .line = 1, .col = 1 };
    if (vfs_opt) |vfs_ptr| {
        if (vfs_ptr.getLineIndex(file_id)) |line_idx| {
            const lc = line_idx.resolveLineCol(src_text, byte_offset);
            return .{ .line = lc.line, .col = lc.col_utf8 };
        } else |_| {}
    }
    var temp_idx = try LineIndex.build(allocator, src_text);
    defer temp_idx.deinit(allocator);
    const lc = temp_idx.resolveLineCol(src_text, byte_offset);
    return .{ .line = lc.line, .col = lc.col_utf8 };
}

/// Formats a clean single-line signature header or qualified symbol name for `--explain-caps` witness rows.
fn formatSymbolWitnessLabelAlloc(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    sym_idx: SymbolIndex,
    fallback_name: []const u8,
) ![]u8 {
    if (!sym_idx.isNone() and sym_idx.asInt() < db.symbol_table.countSymbols()) {
        const sym_rec = db.symbol_table.getSymbol(sym_idx).*;
        const fid = sym_rec.decl_span.file_id;
        if (!fid.isNone()) {
            if (db.getSourceText(fid)) |src_text| {
                if (db.parsed_artifacts.getPtr(fid.asInt())) |parsed_ptr| {
                    if (!sym_rec.cst_node.isNone() and sym_rec.cst_node.asInt() < parsed_ptr.cst_arena.countNodes()) {
                        if (getCstSubtreeSpan(
                            fid,
                            &parsed_ptr.cst_arena,
                            &parsed_ptr.token_buffer,
                            sym_rec.cst_node,
                        )) |cst_span| {
                            const raw_item = src_text[cst_span.start_byte..cst_span.end_byte];
                            const stop_rel = std.mem.indexOfAny(u8, raw_item, "{\n\r;") orelse raw_item.len;
                            const trimmed = std.mem.trim(u8, raw_item[0..stop_rel], " \t\r\n");
                            if (trimmed.len > 0 and trimmed.len <= 96) {
                                return allocator.dupe(u8, trimmed);
                            }
                        }
                    }
                }
            } else |_| {}
        }
        if (sym_rec.name_text.len > 0) {
            if (sym_rec.kind == .fn_sym) {
                return std.fmt.allocPrint(allocator, "fn {s}(…)", .{sym_rec.name_text});
            }
            return allocator.dupe(u8, sym_rec.name_text);
        }
    }
    if (fallback_name.len > 0) return allocator.dupe(u8, fallback_name);
    return allocator.dupe(u8, "<anonymous>");
}

/// Builds a fresh `MirSastResult` (`FnSummaryStore` + `WitnessCallEdge` CSR) across all runtime bodies in `pkg_files`.
fn buildPackageMirSastStore(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    pkg_files: []const FileId,
) !mir_sast.MirSastResult {
    var cloned_bodies: std.ArrayListUnmanaged(mir.MirBody) = .empty;
    defer {
        for (cloned_bodies.items) |*body_item| body_item.deinit();
        cloned_bodies.deinit(allocator);
    }

    for (pkg_files) |fid| {
        if (fid.isNone()) continue;
        _ = try db.parseCst(fid);
        _ = try db.resolveSignatures(fid);
        const entries = (try db.extractItemTree(fid)).entries;
        var entry_i: usize = 0;
        while (entry_i < entries.len) : (entry_i += 1) {
            const entry = entries[entry_i];
            if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) continue;
            _ = db.typecheckBody(entry.def_id) catch continue;
            _ = db.verifySastMir(entry.def_id) catch continue;
            const def_mir = db.buildDefMirArtifact(entry.def_id) catch continue;
            if (def_mir.is_comptime_initializer_only) continue;
            for (def_mir.bundle.bodies.items) |*src_body| {
                var body_copy = try src_body.clone(allocator);
                errdefer body_copy.deinit();
                try cloned_bodies.append(allocator, body_copy);
            }
        }
    }

    return mir_sast.analyzeAndElaborateMirModule(
        allocator,
        cloned_bodies.items,
        &db.type_pool,
        &db.symbol_table,
        &db.interner,
        .{
            .external_resolver = .{
                .compiler_db = db,
                .resolve_fn = CompilerDb.resolveDbCalleeSummary,
            },
        },
    );
}

/// Returns `true` when `slot_i` in `store` is a package entrypoint (`main`, `pub` surface, `@export`, or `test`/`bench`).
fn isSummarySlotPackageEntrypoint(
    db: *CompilerDb,
    store: *const FnSummaryStore,
    slot_i: usize,
) bool {
    if (store.summaries[slot_i].contractsScratch().is_ambient_export_root) return true;
    const sym_idx = store.symbol_indices[slot_i];
    if (!sym_idx.isNone() and sym_idx.asInt() < db.symbol_table.countSymbols()) {
        const sym_rec = db.symbol_table.getSymbol(sym_idx).*;
        if (std.mem.eql(u8, sym_rec.name_text, "main")) return true;
        if (mir_sast.isSymbolExternallyCallableSurface(&db.symbol_table, sym_idx, sym_rec)) return true;
        if (sym_rec.contract_flags.is_export or
            sym_rec.contract_flags.has_link_name or
            sym_rec.contract_flags.has_link_section or
            sym_rec.contract_flags.is_ifunc)
        {
            return true;
        }
    }
    const def_id = store.def_ids[slot_i];
    if (!def_id.isNone()) {
        if (db.item_trees.getPtr(def_id.fileId().asInt())) |tree_ptr| {
            if (tree_ptr.getEntry(def_id)) |entry| {
                if (entry.kind == .test_decl or entry.kind == .bench_decl or entry.isPublicOutsidePkg()) {
                    return true;
                }
            }
        }
    }
    return false;
}

/// Frees all `display_label` strings inside `nodes` and resets `nodes`.
fn freeWitnessNodes(allocator: std.mem.Allocator, nodes: *std.ArrayListUnmanaged(WitnessHopNode)) void {
    for (nodes.items) |node_item| {
        allocator.free(node_item.display_label);
    }
    nodes.deinit(allocator);
}

/// Reconstructs the shortest BFS witness chain for `cap_bit` starting from `target_pkg` (recursing across dep calls).
fn reconstructShortestPackageWitness(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    pkg_id: PackageId,
    pkg_files: []const FileId,
    pkg_files_map_opt: ?*const std.AutoHashMapUnmanaged(PackageId, []const FileId),
    forced_entry_def: DefId,
    cap_bit: u16,
    cap_name: []const u8,
    out_nodes: *std.ArrayListUnmanaged(WitnessHopNode),
    depth: usize,
) anyerror!bool {
    if (depth >= MAX_WITNESS_CHAIN_DEPTH or pkg_files.len == 0) return false;

    var sast_res = try buildPackageMirSastStore(allocator, db, pkg_files);
    defer sast_res.deinit();
    const store = &sast_res.summary_store;

    var best_slot: ?usize = null;
    var best_steps: ?[]mir_sast.WitnessStep = null;
    defer if (best_steps) |owned_steps| allocator.free(owned_steps);

    for (0..store.summaries.len) |slot_i| {
        const slot_sum = store.summaries[slot_i];
        if ((slot_sum.inferred_effects_bits & cap_bit) == 0) continue;
        if (!forced_entry_def.isNone()) {
            if (store.def_ids[slot_i] != forced_entry_def) continue;
        } else if (!isSummarySlotPackageEntrypoint(db, store, slot_i)) {
            continue;
        }

        const cand_steps = try store.reconstructShortestWitness(allocator, @intCast(slot_i), cap_bit);
        if (cand_steps.len == 0) {
            allocator.free(cand_steps);
            if ((slot_sum.direct_effects_bits & cap_bit) != 0) {
                if (best_steps) |prev_steps| allocator.free(prev_steps);
                best_steps = try allocator.alloc(mir_sast.WitnessStep, 0);
                best_slot = slot_i;
                break;
            }
            continue;
        }
        if (best_steps == null or cand_steps.len < best_steps.?.len) {
            if (best_steps) |prev_steps| allocator.free(prev_steps);
            best_steps = cand_steps;
            best_slot = slot_i;
        } else {
            allocator.free(cand_steps);
        }
    }

    // Fallback to any ambient function in `store` if no public/main entrypoint reached `cap_bit`:
    if (best_slot == null and forced_entry_def.isNone()) {
        for (0..store.summaries.len) |slot_i| {
            const slot_sum = store.summaries[slot_i];
            if ((slot_sum.inferred_effects_bits & cap_bit) == 0) continue;
            const cand_steps = try store.reconstructShortestWitness(allocator, @intCast(slot_i), cap_bit);
            if (cand_steps.len == 0 and (slot_sum.direct_effects_bits & cap_bit) == 0) {
                allocator.free(cand_steps);
                continue;
            }
            best_steps = cand_steps;
            best_slot = slot_i;
            break;
        }
    }

    if (best_slot) |root_slot| {
        const root_sym = store.symbol_indices[root_slot];
        const root_fid = store.file_ids[root_slot];
        const root_byte: u32 = if (!root_sym.isNone() and root_sym.asInt() < db.symbol_table.countSymbols())
            db.symbol_table.getSymbol(root_sym).decl_span.start_byte
        else
            0;
        const root_name = if (!store.names[root_slot].isNone())
            db.interner.get(store.names[root_slot])
        else
            "";
        if (out_nodes.items.len == 0) {
            try out_nodes.append(allocator, .{
                .file_id = root_fid,
                .byte_offset = root_byte,
                .display_label = try formatSymbolWitnessLabelAlloc(allocator, db, root_sym, root_name),
            });
        }

        const steps = best_steps orelse &.{};
        for (steps, 0..) |step_item, step_i| {
            if (step_item.callee_slot != mir.NONE_U32 and step_item.callee_slot < store.summaries.len) {
                const c_slot: usize = step_item.callee_slot;
                const c_sym = store.symbol_indices[c_slot];
                const c_fid = store.file_ids[c_slot];
                const c_byte: u32 = if (!c_sym.isNone() and c_sym.asInt() < db.symbol_table.countSymbols())
                    db.symbol_table.getSymbol(c_sym).decl_span.start_byte
                else
                    0;
                const c_name = if (!store.names[c_slot].isNone())
                    db.interner.get(store.names[c_slot])
                else
                    "";
                try out_nodes.append(allocator, .{
                    .file_id = c_fid,
                    .byte_offset = c_byte,
                    .display_label = try formatSymbolWitnessLabelAlloc(allocator, db, c_sym, c_name),
                });
                continue;
            }

            // Leaf external/cross-package/intrinsic edge (`step.callee_slot == NONE_U32`):
            const caller_fid = store.file_ids[step_item.caller_slot];
            var site_byte: u32 = 0;
            if (!step_item.edge.site_token.isNone()) {
                if (db.parsed_artifacts.getPtr(caller_fid.asInt())) |parsed_ptr| {
                    if (step_item.edge.site_token.asInt() < parsed_ptr.token_buffer.countTokens()) {
                        site_byte = parsed_ptr.token_buffer.getToken(step_item.edge.site_token).byte_offset;
                    }
                }
            }

            if (step_item.edge.callee_def != mir.NONE_U32) {
                const target_def = DefId.fromInt(step_item.edge.callee_def);
                const target_sym_opt = db.symbol_table.def_to_symbol.get(target_def.asInt());
                if (target_sym_opt) |t_sym_idx| {
                    if (!t_sym_idx.isNone() and t_sym_idx.asInt() < db.symbol_table.countSymbols()) {
                        const t_sym = db.symbol_table.getSymbol(t_sym_idx).*;
                        const callee_pkg = db.symbol_table.getFilePackageId(t_sym.decl_span.file_id);
                        try out_nodes.append(allocator, .{
                            .file_id = if (!t_sym.decl_span.file_id.isNone()) t_sym.decl_span.file_id else caller_fid,
                            .byte_offset = if (!t_sym.decl_span.file_id.isNone()) t_sym.decl_span.start_byte else site_byte,
                            .display_label = try formatSymbolWitnessLabelAlloc(allocator, db, t_sym_idx, t_sym.name_text),
                        });
                        if (step_i + 1 == steps.len and callee_pkg != pkg_id and callee_pkg != .std_core) {
                            if (pkg_files_map_opt) |pf_map| {
                                if (pf_map.get(callee_pkg)) |dep_files| {
                                    _ = try reconstructShortestPackageWitness(
                                        allocator,
                                        db,
                                        callee_pkg,
                                        dep_files,
                                        pkg_files_map_opt,
                                        target_def,
                                        cap_bit,
                                        cap_name,
                                        out_nodes,
                                        depth + 1,
                                    );
                                }
                            }
                        }
                        continue;
                    }
                }
            }

            const edge_desc = switch (step_item.edge.meta().edge_kind) {
                .indirect_fn_ptr => try std.fmt.allocPrint(allocator, "indirect fn pointer call ({s})", .{cap_name}),
                .indirect_vtable => try std.fmt.allocPrint(allocator, "dyn Trait vtable call ({s})", .{cap_name}),
                else => try std.fmt.allocPrint(allocator, "direct `{s}` capability operation", .{cap_name}),
            };
            try out_nodes.append(allocator, .{
                .file_id = caller_fid,
                .byte_offset = site_byte,
                .display_label = edge_desc,
            });
        }
        return true;
    }

    // Check non-body `extern`, `@std_cap_boundary`, `@export`, or `extern static` symbols in `pkg_files`:
    for (pkg_files) |fid| {
        if (fid.isNone()) continue;
        for ((db.extractItemTree(fid) catch continue).entries) |entry| {
            var item_bits: u16 = 0;
            if (entry.kind == .extern_static or entry.kind == .ffi_extern_block) {
                item_bits |= (EffectCapabilityMask{ .ffi = true }).asBits();
            }
            var matched_sym: SymbolIndex = .none;
            if (db.symbol_table.def_to_symbol.get(entry.def_id.asInt())) |sym_idx| {
                if (!sym_idx.isNone() and sym_idx.asInt() < db.symbol_table.countSymbols()) {
                    matched_sym = sym_idx;
                    const sym_rec = db.symbol_table.getSymbol(sym_idx).*;
                    item_bits |= mir_sast.inferSymbolBoundaryOrPrototypeEffects(&db.symbol_table, sym_idx).asBits();
                    if (sym_rec.contract_flags.is_export or sym_rec.contract_flags.has_link_section or
                        sym_rec.contract_flags.has_link_name)
                    {
                        item_bits |= EffectCapabilityMask.FFI_UNSAFE_BITS;
                    }
                }
            }
            if ((item_bits & cap_bit) != 0) {
                const start_b: u32 = if (!matched_sym.isNone())
                    db.symbol_table.getSymbol(matched_sym).decl_span.start_byte
                else
                    0;
                try out_nodes.append(allocator, .{
                    .file_id = fid,
                    .byte_offset = start_b,
                    .display_label = try formatSymbolWitnessLabelAlloc(allocator, db, matched_sym, entry.name_text),
                });
                return true;
            }
        }
    }

    return false;
}

/// Scans `@cfg`-disabled CST subtrees in `pkg_files` for a dormant `cap_bit` witness fallback.
fn findDormantCfgWitnessForBit(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    pkg_files: []const FileId,
    cap_bit: u16,
    cap_name: []const u8,
    out_nodes: *std.ArrayListUnmanaged(WitnessHopNode),
) !bool {
    const ffi_bit: u16 = 1 << 4;
    const unsafe_bit: u16 = 1 << 5;

    for (pkg_files) |fid| {
        if (fid.isNone()) continue;
        _ = db.parseCst(fid) catch continue;
        const src_text = db.getSourceText(fid) catch continue;
        const parsed_ptr = db.parsed_artifacts.getPtr(fid.asInt()) orelse continue;
        const cfg_env = db.symbol_table.resolveCfgEnvForFile(fid);

        var cursor: usize = 0;
        const node_count = parsed_ptr.cst_arena.countNodes();
        while (cursor < node_count) : (cursor += 1) {
            const cst_id = CstNodeIndex.fromInt(@intCast(cursor));
            const cst_node = parsed_ptr.cst_arena.getNode(cst_id);
            if (!isCfgGateableItemCstKind(cst_node.kind)) continue;

            const is_active = symbol_resolver.evaluateCstNodeCfgWithEnv(
                &cfg_env,
                fid,
                src_text,
                &parsed_ptr.token_buffer,
                &parsed_ptr.cst_arena,
                cst_id,
                null,
            ) catch true;
            if (is_active) continue;

            const sub_end = @min(cursor + @max(@as(usize, cst_node.subtree_size), 1), node_count);
            var sub_cur = cursor;
            while (sub_cur < sub_end) : (sub_cur += 1) {
                const leaf = parsed_ptr.cst_arena.getNode(CstNodeIndex.fromInt(@intCast(sub_cur)));
                if (leaf.subtree_size > 1 or leaf.token.isNone() or
                    leaf.token.asInt() >= parsed_ptr.token_buffer.countTokens())
                {
                    continue;
                }
                const tok_rec = parsed_ptr.token_buffer.getToken(leaf.token);
                const lexeme = src_text[tok_rec.byte_offset .. tok_rec.byte_offset + tok_rec.byte_len];
                const is_match = (cap_bit == unsafe_bit and tok_rec.kind == .kw_unsafe) or
                    (cap_bit == ffi_bit and (tok_rec.kind == .kw_extern or std.mem.eql(u8, lexeme, "c_import"))) or
                    (tok_rec.kind == .ident and std.mem.eql(u8, lexeme, cap_name));
                if (is_match) {
                    try out_nodes.append(allocator, .{
                        .file_id = fid,
                        .byte_offset = tok_rec.byte_offset,
                        .display_label = try std.fmt.allocPrint(
                            allocator,
                            "dormant `@cfg` `{s}` item (`{s}`)",
                            .{ cap_name, lexeme },
                        ),
                    });
                    return true;
                }
            }
            cursor = sub_end - 1;
        }
    }
    return false;
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Scans leading trivia/comments at the top of `source` (inspecting UTF-8 BOM, `#!` shebang, optional
/// `---` script frontmatter `#` TOML comments, and up to `4096` bytes of leading `.cx` `//` or `/* … */`
/// comments before the first code token) and returns `true` if `"@generated"` or `"DO NOT EDIT"` appears.
pub fn isGeneratedSourceHeader(source: []const u8) bool {
    var cursor: usize = 0;
    if (std.mem.startsWith(u8, source, "\xEF\xBB\xBF")) {
        cursor = 3;
    }
    if (std.mem.startsWith(u8, source[cursor..], "#!")) {
        const shebang_rest = source[cursor..@min(source.len, cursor + GENERATED_HEADER_SCAN_BYTES)];
        const shebang_nl_opt = std.mem.indexOfScalar(u8, source[cursor..], '\n');
        const checked_len = @min(shebang_rest.len, shebang_nl_opt orelse source.len - cursor);
        if (hasGeneratedMarkerSubstring(shebang_rest[0..checked_len])) return true;
        const nl_rel = shebang_nl_opt orelse return false;
        cursor += nl_rel + 1;
    }
    const fm_scan = scanOptionalScriptFrontmatter(source, cursor);
    if (fm_scan.has_generated_marker) return true;
    cursor = fm_scan.next_offset;

    const scan_limit = @min(source.len, cursor + GENERATED_HEADER_SCAN_BYTES);
    while (cursor < scan_limit) {
        const ch_byte = source[cursor];
        if (ch_byte == ' ' or ch_byte == '\t' or ch_byte == '\r' or ch_byte == '\n') {
            cursor += 1;
            continue;
        }
        if (cursor + 1 < scan_limit and ch_byte == '/' and source[cursor + 1] == '/') {
            const rest = source[cursor..scan_limit];
            const nl_rel = std.mem.indexOfScalar(u8, rest, '\n') orelse rest.len;
            if (hasGeneratedMarkerSubstring(rest[0..nl_rel])) return true;
            cursor += nl_rel + @intFromBool(cursor + nl_rel < scan_limit);
            continue;
        }
        if (cursor + 1 < scan_limit and ch_byte == '/' and source[cursor + 1] == '*') {
            const comment_start = cursor;
            cursor += 2;
            var block_depth: usize = 1;
            while (cursor + 1 < scan_limit and block_depth > 0) {
                if (source[cursor] == '/' and source[cursor + 1] == '*') {
                    block_depth += 1;
                    cursor += 2;
                } else if (source[cursor] == '*' and source[cursor + 1] == '/') {
                    block_depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
            const comment_end = if (block_depth == 0) cursor else scan_limit;
            if (hasGeneratedMarkerSubstring(source[comment_start..comment_end])) return true;
            if (block_depth != 0) return false;
            continue;
        }
        // Stop immediately at the first non-whitespace, non-comment code token:
        return false;
    }
    return false;
}

/// Returns `true` if any comment trivia (including `TRIVIA_FLAG_COALESCED` runs) overlaps `[start_byte, end_byte)`.
pub fn hasCommentsInByteRange(
    source: []const u8,
    token_buffer: *const TokenBuffer,
    start_byte: u32,
    end_byte: u32,
) bool {
    if (start_byte >= end_byte) return false;
    for (token_buffer.trivia.items) |piece| {
        const piece_start = piece.byte_offset;
        const piece_end = piece.byte_offset +| @as(u32, piece.byte_len);
        if (piece_end <= start_byte or piece_start >= end_byte) continue;
        if (isCommentTriviaKind(piece.kind)) return true;
        if ((piece.flags & syntax_arenas.TRIVIA_FLAG_COALESCED) != 0 and
            hasCoalescedCommentOverlappingRange(source, piece_start, piece_end, start_byte, end_byte))
        {
            return true;
        }
    }
    return false;
}

/// Runs signature-scope `W0202` idiom lints across `checker`'s module (invoked by `computeResolveSignatures`).
pub fn lintFileSignaturesW0202(
    checker: *TypeChecker,
    sink_opt: ?*DiagnosticSink,
) !void {
    if (!isEditableRootLintFile(checker)) return;
    if (checker.cst_arena.countNodes() == 0) return;

    var suppressed_headers: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer suppressed_headers.deinit(checker.allocator);

    try walkAndLintCstSubtree(
        checker,
        CstNodeIndex.fromInt(0),
        .none,
        .none,
        true,
        false,
        &suppressed_headers,
        sink_opt,
        0,
    );
}

/// Runs per-`DefId` body `W0202` idiom lints on `def_id` (invoked by `computeTypecheckBody`).
pub fn lintDefBodyW0202(
    checker: *TypeChecker,
    def_id: DefId,
    sym_idx: SymbolIndex,
    item_ast_node: NodeIndex,
    sink_opt: ?*DiagnosticSink,
) !void {
    if (!isEditableRootLintFile(checker) or def_id.isNone()) return;

    var suppressed_headers: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer suppressed_headers.deinit(checker.allocator);

    if (!sym_idx.isNone() and sym_idx.asInt() < checker.sym_table.countSymbols()) {
        if (checker.isSymbolCfgDisabled(sym_idx)) return;
        const sym_rec = checker.sym_table.getSymbol(sym_idx).*;
        const target_ast = if (!item_ast_node.isNone()) item_ast_node else sym_rec.ast_node;
        try lintSingleItemBodyAst(checker, sym_idx, target_ast, &suppressed_headers, sink_opt);
        return;
    }

    if (item_ast_node.isNone() or item_ast_node.asInt() >= checker.ast_arena.countNodes()) return;
    const item_cst = checker.ast_arena.getCstOrigin(item_ast_node);
    if (!item_cst.isNone() and !checker.isCstNodeCfgEnabled(item_cst)) return;

    const top_tag = checker.ast_arena.getNode(item_ast_node).tag;
    if (top_tag == .impl_decl) {
        const impl_members = checker.getNodeExtraSlice(item_ast_node, true);
        var mem_cursor: usize = 0;
        var sym_raw: u32 = if (checker.db) |db_ptr| db_ptr.getFilePass1SymStart(checker.file_id) else 0;
        while (sym_raw < checker.sym_table.countSymbols()) : (sym_raw += 1) {
            const cand_sym_idx = SymbolIndex.fromInt(sym_raw);
            if (checker.isSymbolCfgDisabled(cand_sym_idx)) continue;
            const cand_sym = checker.sym_table.getSymbol(cand_sym_idx).*;
            if (cand_sym.owner_def_id != def_id) continue;
            if (cand_sym.kind != .fn_sym and cand_sym.kind != .const_sym) continue;

            var matched_mem_ast = cand_sym.ast_node;
            while (mem_cursor < impl_members.len) {
                const mem_ast_idx = NodeIndex.fromInt(impl_members[mem_cursor]);
                mem_cursor += 1;
                if (mem_ast_idx.asInt() >= checker.ast_arena.countNodes()) continue;
                const mem_tag = checker.ast_arena.getNode(mem_ast_idx).tag;
                const is_match = (cand_sym.kind == .fn_sym and (mem_tag == .fn_decl or mem_tag == .subscript_decl)) or
                    (cand_sym.kind == .const_sym and mem_tag == .const_decl);
                if (is_match) {
                    matched_mem_ast = mem_ast_idx;
                    break;
                }
            }
            try lintSingleItemBodyAst(checker, cand_sym_idx, matched_mem_ast, &suppressed_headers, sink_opt);
        }
        return;
    }

    try lintSingleItemBodyAst(checker, .none, item_ast_node, &suppressed_headers, sink_opt);
}

/// Executes bounded multi-pass transactional `.machine_applicable` source patching (`MAX_CHECK_FIX_PASSES = 4`),
/// canonical `corex fmt` formatting, syntax/error-count rollback verification, and optional atomic disk persistence.
pub fn applyCheckFixesOnDb(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    options: CheckFixOptions,
) !CheckFixReport {
    var snapshots: std.ArrayListUnmanaged(CandidateFileSnapshot) = .empty;
    defer {
        for (snapshots.items) |snap_item| {
            allocator.free(snap_item.original_bytes);
            if (snap_item.disk_script_prefix) |pref_buf| allocator.free(pref_buf);
            allocator.free(snap_item.file_path);
        }
        snapshots.deinit(allocator);
    }

    try collectEditableRootCandidates(allocator, db, options, &snapshots);
    if (snapshots.items.len == 0) return .{};

    // [1] Establish pre-fix baseline error count and per-file syntax error status:
    const baseline_check = try runFullCheckAcrossSnapshots(db, snapshots.items, true);

    // [2] Iterate `0 .. MAX_CHECK_FIX_PASSES` applying disjoint `.machine_applicable` fixes per file:
    var total_applied_fixes: u32 = 0;
    var passes_executed: u8 = 0;

    var pass_idx: u8 = 0;
    while (pass_idx < MAX_CHECK_FIX_PASSES) : (pass_idx += 1) {
        if (pass_idx > 0) {
            _ = try runFullCheckAcrossSnapshots(db, snapshots.items, false);
        }
        passes_executed += 1;

        var pass_applied_fixes: u32 = 0;
        for (snapshots.items) |*snap| {
            var candidate_fixes: std.ArrayListUnmanaged(SuggestedFix) = .empty;
            defer candidate_fixes.deinit(allocator);

            const parsed_art = try db.parseCst(snap.file_id);
            try appendSinkMachineFixesForFile(
                allocator,
                db,
                snap.file_id,
                &parsed_art.diagnostics,
                true,
                &candidate_fixes,
            );
            if (db.getSignatureDiagnostics(snap.file_id)) |sig_sink| {
                try appendSinkMachineFixesForFile(
                    allocator,
                    db,
                    snap.file_id,
                    sig_sink,
                    false,
                    &candidate_fixes,
                );
            }
            for ((try db.extractItemTree(snap.file_id)).entries) |entry| {
                if (db.getBodyDiagnostics(entry.def_id)) |body_sink| {
                    try appendSinkMachineFixesForFile(
                        allocator,
                        db,
                        snap.file_id,
                        body_sink,
                        false,
                        &candidate_fixes,
                    );
                }
                if (db.getSastDiagnostics(entry.def_id)) |sast_sink| {
                    try appendSinkMachineFixesForFile(
                        allocator,
                        db,
                        snap.file_id,
                        sast_sink,
                        false,
                        &candidate_fixes,
                    );
                }
            }

            if (candidate_fixes.items.len == 0) continue;
            const current_src = try db.getSourceText(snap.file_id);
            const patch_outcome = try TransactionalPatcher.apply(
                allocator,
                current_src,
                snap.file_id,
                candidate_fixes.items,
                &db.interner,
            );
            defer allocator.free(patch_outcome.patched_source);

            if (patch_outcome.applied_count > 0 and !std.mem.eql(u8, patch_outcome.patched_source, current_src)) {
                pass_applied_fixes += patch_outcome.applied_count;
                total_applied_fixes += patch_outcome.applied_count;
                snap.is_modified = true;
                try updateFileOverlayAndDb(db, options, snap.*, patch_outcome.patched_source);
            }
        }

        if (pass_applied_fixes == 0) break;
    }

    if (total_applied_fixes == 0) {
        return .{
            .applied_fix_count = 0,
            .modified_file_count = 0,
            .pass_count = passes_executed,
            .was_rolled_back = false,
        };
    }

    // [3] Canonicalize each modified file with `fmt_engine.formatSource`:
    for (snapshots.items) |snap| {
        if (!snap.is_modified) continue;
        const current_src = try db.getSourceText(snap.file_id);
        if (snap.disk_script_prefix) |raw_prefix| {
            if (raw_prefix.len > 0 and current_src.len >= raw_prefix.len) {
                const body_slice = current_src[raw_prefix.len..];
                var fmt_res = try fmt_engine.formatSource(allocator, body_slice, snap.file_id);
                defer fmt_res.deinit(allocator);
                if (!fmt_res.has_syntax_errors) {
                    const needs_hdr_nl = raw_prefix[raw_prefix.len - 1] != '\n';
                    const needs_sep_nl = fmt_res.formatted_text.len > 0 and hasLeadingBlankLine(body_slice);
                    const prefix_in_db = if (snap.was_prefix_masked_in_db)
                        current_src[0..raw_prefix.len]
                    else
                        raw_prefix;
                    const total_len = prefix_in_db.len +
                        @intFromBool(needs_hdr_nl) +
                        @intFromBool(needs_sep_nl) +
                        fmt_res.formatted_text.len;
                    const combined_db = try allocator.alloc(u8, total_len);
                    defer allocator.free(combined_db);

                    var cursor_off: usize = 0;
                    @memcpy(combined_db[0..prefix_in_db.len], prefix_in_db);
                    cursor_off += prefix_in_db.len;
                    if (needs_hdr_nl) {
                        combined_db[cursor_off] = '\n';
                        cursor_off += 1;
                    }
                    if (needs_sep_nl) {
                        combined_db[cursor_off] = '\n';
                        cursor_off += 1;
                    }
                    if (fmt_res.formatted_text.len > 0) {
                        @memcpy(
                            combined_db[cursor_off .. cursor_off + fmt_res.formatted_text.len],
                            fmt_res.formatted_text,
                        );
                    }
                    if (!std.mem.eql(u8, combined_db, current_src)) {
                        try updateFileOverlayAndDb(db, options, snap, combined_db);
                    }
                }
                continue;
            }
        }
        var fmt_res = try fmt_engine.formatSource(allocator, current_src, snap.file_id);
        defer fmt_res.deinit(allocator);
        if (!fmt_res.has_syntax_errors and fmt_res.is_changed) {
            try updateFileOverlayAndDb(db, options, snap, fmt_res.formatted_text);
        }
    }

    // [4] Rollback Guard: revert to original snapshot if new syntax errors appeared or errors increased:
    const post_check = try runFullCheckAcrossSnapshots(db, snapshots.items, false);
    if (post_check.has_new_syntax_errors or post_check.total_errors > baseline_check.total_errors) {
        try rollbackSnapshotsInMemory(db, options, snapshots.items);
        return .{
            .applied_fix_count = 0,
            .modified_file_count = 0,
            .pass_count = passes_executed,
            .was_rolled_back = true,
        };
    }

    // [5] Atomically persist modified files to disk when `write_to_disk == true` and count modified files:
    var modified_files: u32 = 0;
    var written_indices: std.ArrayListUnmanaged(usize) = .empty;
    defer written_indices.deinit(allocator);

    for (snapshots.items, 0..) |snap, idx| {
        if (!snap.is_modified) continue;
        const final_src = try db.getSourceText(snap.file_id);
        if (std.mem.eql(u8, final_src, snap.original_bytes)) continue;

        if (options.write_to_disk and snap.file_path.len > 0 and snap.has_disk_backing) {
            const io_handle = options.io orelse return error.MissingIoContext;
            const final_copy = try allocator.dupe(u8, final_src);
            defer allocator.free(final_copy);

            const disk_payload = if (snap.disk_script_prefix) |raw_prefix|
                try spliceRawPrefixOntoSource(allocator, raw_prefix, final_copy)
            else
                try allocator.dupe(u8, final_copy);
            defer allocator.free(disk_payload);

            codegen_abi.writeArtifactAtomic(io_handle, allocator, snap.file_path, disk_payload) catch |write_err| {
                for (written_indices.items) |prev_idx| {
                    const prev_snap = snapshots.items[prev_idx];
                    if (prev_snap.disk_script_prefix) |prev_pref| {
                        if (spliceRawPrefixOntoSource(allocator, prev_pref, prev_snap.original_bytes)) |restored_disk| {
                            defer allocator.free(restored_disk);
                            codegen_abi.writeArtifactAtomic(
                                io_handle,
                                allocator,
                                prev_snap.file_path,
                                restored_disk,
                            ) catch {};
                        } else |_| {}
                    } else {
                        codegen_abi.writeArtifactAtomic(
                            io_handle,
                            allocator,
                            prev_snap.file_path,
                            prev_snap.original_bytes,
                        ) catch {};
                    }
                }
                try rollbackSnapshotsInMemory(db, options, snapshots.items);
                return write_err;
            };
            try written_indices.append(allocator, idx);
            if (options.vfs) |vfs_ptr| {
                if (!snap.was_open_in_editor and snap.has_disk_backing) {
                    _ = vfs_ptr.closeOverlay(io_handle, snap.file_id) catch {};
                    _ = vfs_ptr.getLineIndex(snap.file_id) catch {};
                }
            }
            _ = try db.setInput(snap.file_id, final_copy, .low);
        }
        modified_files += 1;
    }

    if (options.write_to_disk and written_indices.items.len > 0) {
        _ = try runFullCheckAcrossSnapshots(db, snapshots.items, false);
    }

    return .{
        .applied_fix_count = total_applied_fixes,
        .modified_file_count = modified_files,
        .pass_count = passes_executed,
        .was_rolled_back = false,
    };
}

/// Writes the canonical monochrome/ANSI summary line for `corex check --fix` into `writer`.
pub fn renderCheckFixSummary(
    style_config: StyleConfig,
    writer: *std.Io.Writer,
    report: CheckFixReport,
) std.Io.Writer.Error!void {
    var msg_buf: [128]u8 = undefined;
    const summary_msg = std.fmt.bufPrint(
        &msg_buf,
        "applied {d} fix(es) across {d} file(s)",
        .{ report.applied_fix_count, report.modified_file_count },
    ) catch unreachable;
    try style_config.writeStatusHeader(
        writer,
        .success,
        Glyphs.SUCCESS,
        "check --fix",
        summary_msg,
    );
    try writer.writeByte('\n');
}

/// Writes the canonical monochrome/ANSI failure summary for `corex check --deny-warnings` into `writer`.
pub fn renderDenyWarningsSummary(
    style_config: StyleConfig,
    writer: *std.Io.Writer,
    warning_count: u32,
) std.Io.Writer.Error!void {
    var msg_buf: [160]u8 = undefined;
    const summary_msg = std.fmt.bufPrint(
        &msg_buf,
        "{d} warning(s) treated as errors due to '--deny-warnings'",
        .{warning_count},
    ) catch unreachable;
    try style_config.writeStatusHeader(
        writer,
        .err,
        Glyphs.FAILURE,
        "check failed",
        summary_msg,
    );
    try writer.writeByte('\n');
}

/// Renders the `DR-17` §4.4 supply-chain capability matrix (`corex check --caps`) in Workspace or Standalone Mode.
pub fn renderCapabilityAuditTable(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    writer: *std.Io.Writer,
    options: CapabilityAuditOptions,
) !CapabilityAuditReport {
    var cell_rows: std.ArrayListUnmanaged(AuditRowCells) = .empty;
    defer {
        for (cell_rows.items) |*row_item| row_item.deinit(allocator);
        cell_rows.deinit(allocator);
    }

    var all_audited_files: std.ArrayListUnmanaged(FileId) = .empty;
    defer all_audited_files.deinit(allocator);
    var seen_files: std.AutoHashMapUnmanaged(u32, void) = .empty;
    defer seen_files.deinit(allocator);

    var escalation_count: u32 = 0;

    if (options.resolved_graph) |graph| {
        // [1] Order rows with `PackageId.root` first, followed by dependencies sorted `(name ASC, SemVer ASC)`:
        var ordered_indices: std.ArrayListUnmanaged(usize) = .empty;
        defer ordered_indices.deinit(allocator);
        for (graph.packages, 0..) |pkg_node, idx| {
            if (pkg_node.pkg_id == .root) try ordered_indices.append(allocator, idx);
        }
        const dep_start = ordered_indices.items.len;
        for (graph.packages, 0..) |pkg_node, idx| {
            if (pkg_node.pkg_id != .root and pkg_node.pkg_id != .std_core) {
                try ordered_indices.append(allocator, idx);
            }
        }
        std.mem.sort(
            usize,
            ordered_indices.items[dep_start..],
            DependencySortCtx{ .pkgs = graph.packages, .interner = &db.interner },
            DependencySortCtx.lessThan,
        );

        // Compute `WorkspacePackageCapReport`s when not pre-supplied by the caller:
        var owned_reports: ?[]mir_sast.WorkspacePackageCapReport = null;
        defer if (owned_reports) |rep_slice| allocator.free(rep_slice);
        const active_reports: []const mir_sast.WorkspacePackageCapReport = if (options.cap_reports) |supplied|
            supplied
        else if (options.pkg_files_map) |pf_map| blk: {
            var pkg_ids: std.ArrayListUnmanaged(PackageId) = .empty;
            defer pkg_ids.deinit(allocator);
            for (graph.packages) |pkg_node| {
                try pkg_ids.append(allocator, pkg_node.pkg_id);
            }
            const computed = try db.verifyWorkspaceCapabilitySandbox(
                allocator,
                pkg_ids.items,
                pf_map,
                options.cap_edges,
                null,
            );
            owned_reports = computed;
            break :blk computed;
        } else &.{};

        const checked_mask: u16 = EffectCapabilityMask.LOCKFILE_CAP_BITS | EffectCapabilityMask.INDIRECT_OPAQUE_BIT;

        for (ordered_indices.items) |pkg_idx| {
            const pkg_node = graph.packages[pkg_idx];
            const pkg_files: []const FileId = if (options.pkg_files_map) |pf_map|
                (pf_map.get(pkg_node.pkg_id) orelse &.{})
            else
                &.{};
            for (pkg_files) |fid| {
                if (!(try seen_files.getOrPut(allocator, fid.asInt())).found_existing) {
                    try all_audited_files.append(allocator, fid);
                }
            }

            var cxi_art = try db.computePackageCxiSummary(allocator, pkg_node.pkg_id, pkg_files);
            defer cxi_art.deinit(allocator);

            var subtree_bits: u16 = (cxi_art.caps.reachable_caps.asBits() | cxi_art.caps.link_ambient_caps.asBits());
            for (active_reports) |rep_item| {
                if (rep_item.pkg_id == pkg_node.pkg_id) {
                    subtree_bits |= rep_item.subtree_caps.asBits();
                    break;
                }
            }
            const reachable_bits = (cxi_art.caps.reachable_caps.asBits() |
                cxi_art.caps.link_ambient_caps.asBits() |
                (if (pkg_node.pkg_id == .root) subtree_bits else 0)) & EffectCapabilityMask.LOCKFILE_CAP_BITS;
            const surface_bits = cxi_art.caps.surface_caps.asBits() & EffectCapabilityMask.LOCKFILE_CAP_BITS;

            const active_policy_bits: u16 = switch (pkg_node.cap_policy.enforcement_scope) {
                .surface => cxi_art.caps.surface_caps.asBits() | cxi_art.caps.link_ambient_caps.asBits(),
                .all, .reachable => subtree_bits,
            };
            var escalated_bits: u16 = 0;
            var denied_bits: u16 = 0;

            if (pkg_node.cap_policy.locked_caps) |locked_mask| {
                escalated_bits |= (active_policy_bits & ~locked_mask.asBits()) & checked_mask;
            }
            if (findLockfilePackage(options.lockfile, &db.interner, pkg_node.canonical_name, pkg_node.version)) |lpkg| {
                if (pkg_node.pkg_id != .root) {
                    escalated_bits |= (surface_bits & ~lpkg.max_caps.asBits()) & EffectCapabilityMask.LOCKFILE_CAP_BITS;
                }
            }

            const permitted_self = pkg_node.cap_policy.asEffectiveAllowedCaps().asBits();
            const self_unauth = (subtree_bits & ~permitted_self) & checked_mask;
            if (self_unauth != 0) {
                if (pkg_node.pkg_id != .root and pkg_node.cap_policy.forbid_global_caps.isEmpty() and
                    pkg_node.cap_policy.allow_caps == null)
                {
                    escalated_bits |= self_unauth;
                } else {
                    denied_bits |= (self_unauth & ~escalated_bits);
                }
            }

            for (options.cap_edges) |dep_edge| {
                if (dep_edge.callee_pkg != pkg_node.pkg_id) continue;
                var caller_forbid: u16 = 0;
                for (graph.packages) |caller_node| {
                    if (caller_node.pkg_id == dep_edge.caller_pkg) {
                        caller_forbid = caller_node.cap_policy.forbid_global_caps.asBits();
                        break;
                    }
                }
                const edge_allowed = dep_edge.allow_caps.asBits() & ~caller_forbid;
                const edge_unauth = (subtree_bits & ~edge_allowed) & checked_mask;
                denied_bits |= (edge_unauth & ~escalated_bits);
            }

            if (escalated_bits != 0 or denied_bits != 0) {
                escalation_count += 1;
            }

            const pkg_cell = try allocator.dupe(u8, pkg_node.canonical_name);
            errdefer allocator.free(pkg_cell);
            const ver_cell = try pkg_node.version.formatAlloc(allocator, &db.interner);
            errdefer allocator.free(ver_cell);
            const reachable_cell = try formatCapMaskCellAlloc(allocator, reachable_bits, false);
            errdefer allocator.free(reachable_cell);
            const surface_cell = try formatCapMaskCellAlloc(allocator, surface_bits, false);
            errdefer allocator.free(surface_cell);
            const status_cell = try formatPolicyStatusCellAlloc(
                allocator,
                options.style_config,
                false,
                pkg_node.pkg_id == .root,
                surface_bits,
                escalated_bits,
                denied_bits,
            );
            errdefer allocator.free(status_cell);

            try cell_rows.append(allocator, .{
                .pkg_cell = pkg_cell,
                .ver_cell = ver_cell,
                .reachable_cell = reachable_cell,
                .surface_cell = surface_cell,
                .status_cell = status_cell,
            });
        }
    } else {
        // [2] Standalone Single/Multi-File Mode: synthesize a single `.root` audit row:
        if (options.standalone_files.len > 0) {
            for (options.standalone_files) |fid| {
                if (!fid.isNone() and !(try seen_files.getOrPut(allocator, fid.asInt())).found_existing) {
                    try all_audited_files.append(allocator, fid);
                }
            }
        } else {
            var inp_it = db.source_inputs.keyIterator();
            while (inp_it.next()) |raw_fid_ptr| {
                const fid = FileId.fromInt(raw_fid_ptr.*);
                if (fid.isNone() or fid.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) continue;
                if (db.symbol_table.getFilePackageId(fid) != .root or db.isStdlibFile(fid)) continue;
                if (!(try seen_files.getOrPut(allocator, fid.asInt())).found_existing) {
                    try all_audited_files.append(allocator, fid);
                }
            }
            std.mem.sort(FileId, all_audited_files.items, {}, compareFileIdAsc);
        }

        var cxi_art = try db.computePackageCxiSummary(allocator, .root, all_audited_files.items);
        defer cxi_art.deinit(allocator);

        const reachable_bits = (cxi_art.caps.reachable_caps.asBits() | cxi_art.caps.link_ambient_caps.asBits()) &
            EffectCapabilityMask.LOCKFILE_CAP_BITS;
        const surface_bits = cxi_art.caps.surface_caps.asBits() & EffectCapabilityMask.LOCKFILE_CAP_BITS;

        var denied_bits: u16 = 0;
        if (db.package_cap_policies.get(.root)) |root_pol| {
            denied_bits = (reachable_bits & ~root_pol.asEffectiveAllowedCaps().asBits()) &
                EffectCapabilityMask.LOCKFILE_CAP_BITS;
        }
        if (denied_bits != 0) escalation_count += 1;

        var derived_label: []const u8 = options.standalone_label;
        if (derived_label.len == 0 and all_audited_files.items.len > 0) {
            if (db.file_paths.get(all_audited_files.items[0].asInt())) |path_slice| {
                derived_label = std.fs.path.basename(path_slice);
            }
        }
        if (derived_label.len == 0) derived_label = "standalone";

        const pkg_cell = try allocator.dupe(u8, derived_label);
        errdefer allocator.free(pkg_cell);
        const ver_cell = try allocator.dupe(u8, "0.0.0");
        errdefer allocator.free(ver_cell);
        const reachable_cell = try formatCapMaskCellAlloc(allocator, reachable_bits, false);
        errdefer allocator.free(reachable_cell);
        const surface_cell = try formatCapMaskCellAlloc(allocator, surface_bits, false);
        errdefer allocator.free(surface_cell);
        const status_cell = try formatPolicyStatusCellAlloc(
            allocator,
            options.style_config,
            true,
            true,
            surface_bits,
            0,
            denied_bits,
        );
        errdefer allocator.free(status_cell);

        try cell_rows.append(allocator, .{
            .pkg_cell = pkg_cell,
            .ver_cell = ver_cell,
            .reachable_cell = reachable_cell,
            .surface_cell = surface_cell,
            .status_cell = status_cell,
        });
    }

    // [3] Render box-drawing table via `TableRenderer`:
    const row_views = try allocator.alloc([5][]const u8, cell_rows.items.len);
    defer allocator.free(row_views);
    const slice_ptrs = try allocator.alloc([]const []const u8, cell_rows.items.len);
    defer allocator.free(slice_ptrs);

    for (cell_rows.items, 0..) |row_item, i| {
        row_views[i] = .{
            row_item.pkg_cell,
            row_item.ver_cell,
            row_item.reachable_cell,
            row_item.surface_cell,
            row_item.status_cell,
        };
        slice_ptrs[i] = &row_views[i];
    }

    try TableRenderer.init(options.style_config).renderTable(writer, &AUDIT_TABLE_COLUMNS, slice_ptrs);

    // [4] Count verified `@no_alloc` / `@no_panic` functions and render footer line:
    const contract_info = try inspectContractVerificationInFiles(allocator, db, all_audited_files.items);
    const has_any_failure = escalation_count > 0 or options.has_contract_errors or contract_info.has_sast_contract_errors;
    const footer_glyph = if (has_any_failure) Glyphs.FAILURE else Glyphs.SUCCESS;
    const footer_role: style.StyleRole = if (has_any_failure) .err else .success;
    const pkg_count: u32 = @intCast(cell_rows.items.len);

    try options.style_config.writeStyled(writer, footer_role, footer_glyph);
    try writer.print(
        " {d} package(s) verified {s} {d} capability escalations {s} {d} @no_alloc/@no_panic fns verified\n",
        .{ pkg_count, Glyphs.BULLET, escalation_count, Glyphs.BULLET, contract_info.verified_fn_count },
    );

    return .{
        .package_count = pkg_count,
        .escalation_count = escalation_count,
        .verified_contract_fn_count = contract_info.verified_fn_count,
        .has_escalation = has_any_failure,
    };
}

/// Renders shortest BFS call-chain capability witnesses (`corex check --explain-caps [pkg] [cap]`),
/// emitting `E0001` into `sink` when `[pkg]` or `[cap]` is unrecognized.
pub fn renderExplainCapsReport(
    allocator: std.mem.Allocator,
    db: *CompilerDb,
    writer: *std.Io.Writer,
    sink: *DiagnosticSink,
    options: ExplainCapsOptions,
) !ExplainCapsReport {
    // [1] Validate optional `[cap]` filter against `MANIFEST_CAPABILITY_MAP` (`"unsafe_op"` canonical):
    var requested_cap_mask: ?u16 = null;
    if (options.target_cap_arg) |cap_arg| {
        if (cap_arg.len > 0) {
            const cap_bit = pkg_manifest.MANIFEST_CAPABILITY_MAP.get(cap_arg) orelse {
                const help_note: []const u8 = if (std.mem.eql(u8, cap_arg, "unsafe"))
                    "help: use canonical capability name `unsafe_op` instead of `unsafe`"
                else
                    "help: valid capability names are `fs`, `net`, `env`, `process`, `ffi`, `unsafe_op`, `clock`, `entropy`";
                try sink.emit(.{
                    .code = .e0001_unknown_cli_flag,
                    .severity = .err,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "unknown capability name `{s}` for `--explain-caps`",
                        .{cap_arg},
                    ),
                    .notes = &.{help_note},
                });
                return .{ .rendered_witness_count = 0, .has_cli_error = true };
            };
            requested_cap_mask = cap_bit;
        }
    }

    // [2] Resolve target package (`root` by default when `[pkg]` is omitted):
    var target_pkg_id: PackageId = .root;
    var target_pkg_name: []const u8 = options.standalone_name;
    var owned_ver_str: ?[]u8 = null;
    defer if (owned_ver_str) |ver_buf| allocator.free(ver_buf);
    var target_pkg_ver: []const u8 = options.standalone_version;
    var target_files_owned: std.ArrayListUnmanaged(FileId) = .empty;
    defer target_files_owned.deinit(allocator);

    if (options.resolved_graph) |graph| {
        var matched_node_opt: ?pkg_resolver.ResolvedPackageNode = null;
        if (options.target_pkg_arg == null or options.target_pkg_arg.?.len == 0 or
            std.mem.eql(u8, options.target_pkg_arg.?, "root"))
        {
            for (graph.packages) |pkg_node| {
                if (pkg_node.pkg_id == .root) {
                    matched_node_opt = pkg_node;
                    break;
                }
            }
        } else {
            const wanted_pkg = options.target_pkg_arg.?;
            for (graph.packages) |pkg_node| {
                if (std.mem.eql(u8, pkg_node.canonical_name, wanted_pkg) or
                    std.mem.eql(u8, pkg_node.default_snake_name, wanted_pkg))
                {
                    matched_node_opt = pkg_node;
                    break;
                }
            }
        }

        const matched_node = matched_node_opt orelse {
            try sink.emit(.{
                .code = .e0001_unknown_cli_flag,
                .severity = .err,
                .message = try std.fmt.allocPrint(
                    sink.arena.asAllocator(),
                    "unknown package `{s}` in workspace dependency graph for `--explain-caps`",
                    .{options.target_pkg_arg orelse ""},
                ),
                .notes = &.{"help: run `corex check --caps` to list all resolved packages in this workspace"},
            });
            return .{ .rendered_witness_count = 0, .has_cli_error = true };
        };

        target_pkg_id = matched_node.pkg_id;
        target_pkg_name = matched_node.canonical_name;
        const fmt_ver = try matched_node.version.formatAlloc(allocator, &db.interner);
        owned_ver_str = fmt_ver;
        target_pkg_ver = fmt_ver;
        if (options.pkg_files_map) |pf_map| {
            if (pf_map.get(target_pkg_id)) |pf_slice| {
                try target_files_owned.appendSlice(allocator, pf_slice);
            }
        }
    } else {
        if (options.target_pkg_arg) |wanted_pkg| {
            if (wanted_pkg.len > 0 and
                !std.mem.eql(u8, wanted_pkg, "root") and
                !std.mem.eql(u8, wanted_pkg, options.standalone_name))
            {
                try sink.emit(.{
                    .code = .e0001_unknown_cli_flag,
                    .severity = .err,
                    .message = try std.fmt.allocPrint(
                        sink.arena.asAllocator(),
                        "unknown package `{s}` for `--explain-caps` in standalone mode",
                        .{wanted_pkg},
                    ),
                    .notes = &.{"help: pass `root` or omit `[pkg]` when checking standalone `.cx` files"},
                });
                return .{ .rendered_witness_count = 0, .has_cli_error = true };
            }
        }
        if (options.standalone_files.len > 0) {
            try target_files_owned.appendSlice(allocator, options.standalone_files);
        } else {
            var inp_it = db.source_inputs.keyIterator();
            while (inp_it.next()) |raw_fid_ptr| {
                const fid = FileId.fromInt(raw_fid_ptr.*);
                if (fid.isNone() or fid.asInt() >= query_db.VIRTUAL_C_IMPORT_FILE_ID_BASE) continue;
                if (db.symbol_table.getFilePackageId(fid) == .root and !db.isStdlibFile(fid)) {
                    try target_files_owned.append(allocator, fid);
                }
            }
            std.mem.sort(FileId, target_files_owned.items, {}, compareFileIdAsc);
        }
    }

    // [3] Reconstruct and render shortest witness chains across requested capability bits:
    var cxi_art = try db.computePackageCxiSummary(allocator, target_pkg_id, target_files_owned.items);
    defer cxi_art.deinit(allocator);
    const active_pkg_bits: u16 = cxi_art.caps.ambient_caps.asBits() |
        cxi_art.caps.reachable_caps.asBits() |
        cxi_art.caps.surface_caps.asBits() |
        cxi_art.caps.link_ambient_caps.asBits();

    var rendered_count: u32 = 0;

    // Build candidate list (`CANONICAL_AUDIT_CAPS` or single requested non-OS bit like `alloc`/`may_panic`):
    var cap_specs_buf: [9]CapabilityBitSpec = undefined;
    var cap_specs_len: usize = 0;
    if (requested_cap_mask) |req_bit| {
        if (req_bit != 0) {
            cap_specs_buf[0] = .{ .bit = req_bit, .name = options.target_cap_arg.? };
            cap_specs_len = 1;
        }
    } else {
        for (CANONICAL_AUDIT_CAPS) |spec| {
            cap_specs_buf[cap_specs_len] = spec;
            cap_specs_len += 1;
        }
    }

    for (cap_specs_buf[0..cap_specs_len]) |cap_spec| {
        if (requested_cap_mask == null and (active_pkg_bits & cap_spec.bit) == 0) continue;

        var hop_nodes: std.ArrayListUnmanaged(WitnessHopNode) = .empty;
        defer freeWitnessNodes(allocator, &hop_nodes);

        const found_active = try reconstructShortestPackageWitness(
            allocator,
            db,
            target_pkg_id,
            target_files_owned.items,
            options.pkg_files_map,
            DefId.NONE,
            cap_spec.bit,
            cap_spec.name,
            &hop_nodes,
            0,
        );
        const found_dormant = if (!found_active)
            try findDormantCfgWitnessForBit(
                allocator,
                db,
                target_files_owned.items,
                cap_spec.bit,
                cap_spec.name,
                &hop_nodes,
            )
        else
            false;

        if (!found_active and !found_dormant) {
            if (requested_cap_mask != null) {
                try options.style_config.writeStyled(writer, .success, Glyphs.SUCCESS);
                try writer.print(
                    " {s} v{s} {s} {s}: [] (pure) – capability is not exercised\n",
                    .{ target_pkg_name, target_pkg_ver, Glyphs.POINTER_SOLID, cap_spec.name },
                );
            }
            continue;
        }

        if (rendered_count > 0) try writer.writeByte('\n');
        const hop_count: usize = if (hop_nodes.items.len >= 2) hop_nodes.items.len - 1 else 1;
        try options.style_config.writeStyled(writer, .bold, "Capability witness: ");
        try writer.print(
            "{s} v{s} {s} {s} (shortest path: {d} hop(s))\n",
            .{ target_pkg_name, target_pkg_ver, Glyphs.POINTER_SOLID, cap_spec.name, hop_count },
        );

        for (hop_nodes.items, 0..) |hop_item, node_idx| {
            const branch_prefix: []const u8 = if (hop_nodes.items.len == 1)
                "  ╰─▸ "
            else if (node_idx == 0)
                "  ╭─▸ "
            else if (node_idx + 1 == hop_nodes.items.len)
                "  ╰─▸ "
            else
                "  ├─▸ ";

            const norm_path = try normalizeDisplayPathAlloc(allocator, db, options.vfs, hop_item.file_id);
            defer allocator.free(norm_path);
            const lc = try resolveFileLineCol(allocator, db, options.vfs, hop_item.file_id, hop_item.byte_offset);

            try options.style_config.writeStyled(writer, .dim, branch_prefix);
            try writer.print(
                "{s}:{d}:{d} – {s}\n",
                .{ norm_path, lc.line, lc.col, hop_item.display_label },
            );
        }
        rendered_count += 1;
    }

    if (rendered_count == 0 and requested_cap_mask == null) {
        try options.style_config.writeStyled(writer, .success, Glyphs.SUCCESS);
        try writer.print(
            " {s} v{s}: [] (pure) – zero ambient or reachable OS/FFI capabilities\n",
            .{ target_pkg_name, target_pkg_ver },
        );
    }

    return .{
        .rendered_witness_count = rendered_count,
        .has_cli_error = false,
    };
}

// ---------------------------------------- MAIN -----------------------------------------

test "test_check_audit_is_generated_source_header" {
    try std.testing.expect(isGeneratedSourceHeader("// @generated by corex translate-c\npub fn init() {}\n"));
    try std.testing.expect(isGeneratedSourceHeader("/* Code generated – DO NOT EDIT. */\npub struct Wire {}\n"));
    try std.testing.expect(isGeneratedSourceHeader(
        "\xEF\xBB\xBF#!/usr/bin/env corex\n---\n[dependencies]\n---\n//! @generated bindings\npub fn call() {}\n",
    ));
    try std.testing.expect(!isGeneratedSourceHeader("pub fn regular() {\n    // @generated inside body\n}\n"));
    try std.testing.expect(!isGeneratedSourceHeader("//! Normal hand-written module header\npub fn ok() {}\n"));

    const padded = try std.testing.allocator.alloc(u8, 4200);
    defer std.testing.allocator.free(padded);
    @memset(padded, ' ');
    const tail_marker = "// DO NOT EDIT\n";
    @memcpy(padded[4150 .. 4150 + tail_marker.len], tail_marker);
    try std.testing.expect(!isGeneratedSourceHeader(padded));
}

test "test_check_audit_w0202_all_six_idioms_and_transactional_fix" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();
    var vfs = VfsSourceMap.init(std.testing.allocator, &interner);
    defer vfs.deinit(std.testing.io);

    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const raw_source =
        "pub struct Point {\n" ++
        "    pub x: i32,\n" ++
        "    pub y: i32,\n" ++
        "}\n\n" ++
        "pub fn audit_showcase(\n" ++
        "    flag: bool,\n" ++
        "    opt_ref: Option[&u8],\n" ++
        "    mut_opt_ptr: *mut Option[u8],\n" ++
        "    res_ref: &Result[i32, u32],\n" ++
        "    pt_opt: Option[Point],\n" ++
        ") -> bool {\n" ++
        "    let _keep_ptr = mut_opt_ptr;\n" ++
        "    let _keep_res = res_ref;\n" ++
        "    let _keep_ref = opt_ref;\n" ++
        "    while (flag == false) {\n" ++
        "        break;\n" ++
        "    }\n" ++
        "    match (pt_opt) {\n" ++
        "        .Some(Point { x, y }) => {\n" ++
        "            let _sum = x + y;\n" ++
        "        },\n" ++
        "        _ => {},\n" ++
        "    }\n" ++
        "    if (flag == true) {\n" ++
        "        return true;\n" ++
        "    } else {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn trailing_ret() {\n" ++
        "    let _val: i32 = 1;\n" ++
        "    return;\n" ++
        "}\n\n" ++
        "@allow(W0202)\n" ++
        "pub fn suppressed_fn(flag: bool) -> Option[i32] {\n" ++
        "    if (flag == true) {\n" ++
        "        return .Some(1);\n" ++
        "    }\n" ++
        "    return .None;\n" ++
        "}\n";

    const file_id = try vfs.setOverlay("src/audit_demo.cx", raw_source, .root);
    _ = try db.setInput(file_id, raw_source, .low);
    try db.setFilePath(file_id, "src/audit_demo.cx");

    // Generated and non-root files must emit zero `W0202` warnings:
    const gen_fid = FileId.fromInt(10);
    _ = try db.setInput(gen_fid, "// @generated\npub fn gen_fn(x_val: Option[i32]) { return; }\n", .low);
    const gen_sig = try db.resolveSignatures(gen_fid);
    try std.testing.expectEqual(@as(u32, 0), gen_sig.warning_count);

    const dep_fid = FileId.fromInt(11);
    _ = try db.setInput(dep_fid, "pub fn dep_fn(x_val: Option[i32]) { return; }\n", .medium);
    try db.setFilePackageId(dep_fid, PackageId.fromInt(2));
    const dep_sig = try db.resolveSignatures(dep_fid);
    try std.testing.expectEqual(@as(u32, 0), dep_sig.warning_count);

    // Dedicated `@allow(W0202)` file must emit zero `W0202` warnings and remain 100% unedited:
    const sup_only_src =
        "@allow(W0202)\n" ++
        "pub fn untouched_suppressed(flag: bool) -> Option[i32] {\n" ++
        "    if (flag == true) {\n" ++
        "        return .Some(1);\n" ++
        "    }\n" ++
        "    return .None;\n" ++
        "}\n";
    const sup_only_fid = try vfs.setOverlay("src/suppressed_only.cx", sup_only_src, .root);
    _ = try db.setInput(sup_only_fid, sup_only_src, .low);
    try db.setFilePath(sup_only_fid, "src/suppressed_only.cx");

    // Run `applyCheckFixesOnDb` and verify canonical convergence + `@allow(W0202)` preservation:
    const fix_report = try applyCheckFixesOnDb(std.testing.allocator, &db, .{
        .vfs = &vfs,
        .write_to_disk = false,
        .candidate_files = &.{ file_id, sup_only_fid },
    });
    try std.testing.expect(!fix_report.was_rolled_back);
    try std.testing.expect(fix_report.applied_fix_count >= 6);
    try std.testing.expectEqual(@as(u32, 1), fix_report.modified_file_count);

    const fixed_src = try db.getSourceText(file_id);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "opt_ref: (&u8)?") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "mut_opt_ptr: *mut (u8?)") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "res_ref: &(i32!u32)") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "pt_opt: Point?") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "while not flag") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "if pt_opt is (.Some(Point { x, y }))") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "return flag;") != null);
    try std.testing.expect(std.mem.indexOf(u8, fixed_src, "if flag == true") != null);

    const sup_only_after = try db.getSourceText(sup_only_fid);
    try std.testing.expectEqualStrings(sup_only_src, sup_only_after);

    var fix_summary_buf: [160]u8 = undefined;
    var fix_summary_writer = std.Io.Writer.fixed(&fix_summary_buf);
    try renderCheckFixSummary(StyleConfig.MONOCHROME, &fix_summary_writer, .{
        .applied_fix_count = 7,
        .modified_file_count = 1,
    });
    try std.testing.expectEqualStrings(
        "✓ check --fix: applied 7 fix(es) across 1 file(s)\n",
        fix_summary_writer.buffered(),
    );

    var deny_buf: [160]u8 = undefined;
    var deny_writer = std.Io.Writer.fixed(&deny_buf);
    try renderDenyWarningsSummary(StyleConfig.MONOCHROME, &deny_writer, 3);
    try std.testing.expectEqualStrings(
        "✗ check failed: 3 warning(s) treated as errors due to '--deny-warnings'\n",
        deny_writer.buffered(),
    );
}

test "test_check_audit_caps_table_and_explain_caps_witness" {
    var db = try CompilerDb.init(std.testing.allocator);
    defer db.deinit();

    const root_fid = FileId.fromInt(0);
    const root_src =
        "extern \"C\" fn raw_c_probe() -> i32;\n\n" ++
        "fn leaf_unsafe() -> i32 {\n" ++
        "    return unsafe { raw_c_probe() };\n" ++
        "}\n\n" ++
        "fn mid_step() -> i32 {\n" ++
        "    return leaf_unsafe();\n" ++
        "}\n\n" ++
        "@no_alloc\n" ++
        "@no_panic\n" ++
        "pub fn pure_math(val: i32) -> i32 {\n" ++
        "    return val +% 1;\n" ++
        "}\n\n" ++
        "pub fn entry_call() -> i32 {\n" ++
        "    return mid_step() +% pure_math(4);\n" ++
        "}\n";

    _ = try db.setInput(root_fid, root_src, .low);
    try db.setFilePath(root_fid, "src\\net\\probe.cx");
    _ = try db.parseCst(root_fid);
    _ = try db.resolveSignatures(root_fid);
    for ((try db.extractItemTree(root_fid)).entries) |entry| {
        _ = try db.typecheckBody(entry.def_id);
        _ = try db.verifySastMir(entry.def_id);
    }

    var table_buf: [4096]u8 = undefined;
    var table_writer = std.Io.Writer.fixed(&table_buf);
    const audit_rep = try renderCapabilityAuditTable(
        std.testing.allocator,
        &db,
        &table_writer,
        .{
            .style_config = StyleConfig.MONOCHROME,
            .standalone_files = &.{root_fid},
            .standalone_label = "probe-app",
        },
    );
    try std.testing.expectEqual(@as(u32, 1), audit_rep.package_count);
    try std.testing.expectEqual(@as(u32, 0), audit_rep.escalation_count);
    try std.testing.expect(audit_rep.verified_contract_fn_count >= 1);
    const rendered_table = table_writer.buffered();
    try std.testing.expect(std.mem.indexOf(u8, rendered_table, "╭") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered_table, "[ffi, unsafe_op]") != null);
    try std.testing.expect(std.mem.indexOf(u8, rendered_table, "✓ standalone") != null);

    var explain_buf: [4096]u8 = undefined;
    var explain_writer = std.Io.Writer.fixed(&explain_buf);
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    const explain_rep = try renderExplainCapsReport(
        std.testing.allocator,
        &db,
        &explain_writer,
        &sink,
        .{
            .style_config = StyleConfig.MONOCHROME,
            .standalone_files = &.{root_fid},
            .standalone_name = "probe-app",
            .standalone_version = "0.1.0",
            .target_cap_arg = "unsafe_op",
        },
    );
    try std.testing.expect(!explain_rep.has_cli_error);
    try std.testing.expectEqual(@as(u32, 1), explain_rep.rendered_witness_count);
    const witness_text = explain_writer.buffered();
    try std.testing.expect(
        std.mem.indexOf(u8, witness_text, "Capability witness: probe-app v0.1.0 ▸ unsafe_op") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, witness_text, "╭─▸ src/net/probe.cx:") != null);
    try std.testing.expect(std.mem.indexOf(u8, witness_text, "╰─▸ src/net/probe.cx:") != null);
    try std.testing.expect(std.mem.indexOf(u8, witness_text, " – ") != null);
    try std.testing.expect(std.mem.indexOf(u8, witness_text, "\u{2014}") == null);

    // Retired `"unsafe"` spelling must emit `E0001` recommending `"unsafe_op"`:
    const bad_cap_rep = try renderExplainCapsReport(
        std.testing.allocator,
        &db,
        &explain_writer,
        &sink,
        .{
            .style_config = StyleConfig.MONOCHROME,
            .standalone_files = &.{root_fid},
            .target_cap_arg = "unsafe",
        },
    );
    try std.testing.expect(bad_cap_rep.has_cli_error);
    try std.testing.expectEqual(@as(u32, 1), sink.error_count);
}

test "test_script_frontmatter_check_fix_disk_preservation_and_coalesced_comments" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;

    // [1] `isGeneratedSourceHeader` across `#!`, `---` TOML comments, post-`---` `.cx` comments, and negative TOML strings:
    try std.testing.expect(isGeneratedSourceHeader("#!/usr/bin/env corex // @generated\npub fn main() {}\n"));
    try std.testing.expect(isGeneratedSourceHeader("#!/usr/bin/env corex\n---\n# DO NOT EDIT\n---\npub fn main() {}\n"));
    try std.testing.expect(isGeneratedSourceHeader("---\n[dependencies]\n---\n/* @generated */\npub fn main() {}\n"));
    try std.testing.expect(!isGeneratedSourceHeader(
        "---\n[package]\nname = \"demo\"\nversion = \"0.1.0\"\ndescription = \"# @generated\"\n---\npub fn main() {}\n",
    ));

    // [2] `hasCommentsInByteRange` detects comments inside `TRIVIA_FLAG_COALESCED` runs (`> 31` trivia pieces):
    {
        var many_trivia_src: std.ArrayListUnmanaged(u8) = .empty;
        defer many_trivia_src.deinit(allocator);
        var line_idx: usize = 0;
        while (line_idx < 20) : (line_idx += 1) {
            try many_trivia_src.appendSlice(allocator, "  \n");
        }
        const cmt_offset: u32 = @intCast(many_trivia_src.items.len);
        try many_trivia_src.appendSlice(allocator, "// coalesced_marker\n");
        const fn_offset: u32 = @intCast(many_trivia_src.items.len);
        try many_trivia_src.appendSlice(allocator, "pub fn probe() {}\n");

        var db_triv = try CompilerDb.init(allocator);
        defer db_triv.deinit();
        const triv_fid = FileId.fromInt(0);
        _ = try db_triv.setInput(triv_fid, many_trivia_src.items, .low);
        const parsed_triv = try db_triv.parseCst(triv_fid);
        try std.testing.expect(hasCommentsInByteRange(
            many_trivia_src.items,
            &parsed_triv.token_buffer,
            cmt_offset,
            fn_offset,
        ));
        try std.testing.expect(!hasCommentsInByteRange(
            many_trivia_src.items,
            &parsed_triv.token_buffer,
            0,
            cmt_offset,
        ));
    }

    // [3] `applyCheckFixesOnDb(.write_to_disk = true)` preserves `#!` (Mode C) and `#! + ---` (Mode B) on disk:
    const scratch_dir = ".zig-cache/test_check_fix_scripts";
    std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    defer std.Io.Dir.cwd().deleteTree(io, scratch_dir) catch {};
    try std.Io.Dir.cwd().createDirPath(io, scratch_dir);

    const mode_c_path = scratch_dir ++ "/mode_c.cx";
    const mode_c_shebang = "#!/usr/bin/env corex\n";
    const mode_c_disk_init = mode_c_shebang ++
        "pub fn check_c(opt: Option[u8], flag: bool) -> bool {\n" ++
        "    let _ = opt;\n" ++
        "    if flag == true {\n" ++
        "        return true;\n" ++
        "    } else {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "}\n";
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = mode_c_path, .data = mode_c_disk_init });

    const mode_b_path = scratch_dir ++ "/mode_b.cx";
    const mode_b_prefix =
        "#!/usr/bin/env corex\n" ++
        "---\n" ++
        "[package]\n" ++
        "name = \"script-demo\"\n" ++
        "version = \"0.1.0\"\n" ++
        "---\n";
    const mode_b_disk_init = mode_b_prefix ++
        "pub fn check_b(opt: Option[i32], flag: bool) -> bool {\n" ++
        "    let _ = opt;\n" ++
        "    if flag == true {\n" ++
        "        return true;\n" ++
        "    } else {\n" ++
        "        return false;\n" ++
        "    }\n" ++
        "}\n";
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = mode_b_path, .data = mode_b_disk_init });

    var interner = try StringInterner.init(allocator);
    defer interner.deinit();
    var source_map = VfsSourceMap.init(allocator, &interner);
    defer source_map.deinit(io);
    var db = try CompilerDb.init(allocator);
    defer db.deinit();

    var fm_arena = mem_foundation.BumpArena.init(allocator);
    defer fm_arena.deinit();

    const mode_c_fid = try source_map.resolveOrCreatePath(io, mode_c_path, .root);
    const extracted_c = (try pkg_manifest.extractScriptFrontmatter(&fm_arena, mode_c_fid, mode_c_disk_init, null)).?;
    _ = try source_map.setEditorOverlay(io, mode_c_path, extracted_c.blanked_cx_source, .root, false);
    _ = try db.setInput(mode_c_fid, extracted_c.blanked_cx_source, .low);
    try db.setFilePath(mode_c_fid, mode_c_path);

    const mode_b_fid = try source_map.resolveOrCreatePath(io, mode_b_path, .root);
    const extracted_b = (try pkg_manifest.extractScriptFrontmatter(&fm_arena, mode_b_fid, mode_b_disk_init, null)).?;
    _ = try source_map.setEditorOverlay(io, mode_b_path, extracted_b.blanked_cx_source, .root, false);
    _ = try db.setInput(mode_b_fid, extracted_b.blanked_cx_source, .low);
    try db.setFilePath(mode_b_fid, mode_b_path);

    const report = try applyCheckFixesOnDb(allocator, &db, .{
        .io = io,
        .vfs = &source_map,
        .write_to_disk = true,
        .candidate_files = &.{ mode_c_fid, mode_b_fid },
    });
    try std.testing.expect(!report.was_rolled_back);
    try std.testing.expectEqual(@as(u32, 2), report.modified_file_count);
    try std.testing.expect(report.applied_fix_count >= 4);

    const mode_c_after = try std.Io.Dir.cwd().readFileAlloc(io, mode_c_path, allocator, .limited(64 * 1024));
    defer allocator.free(mode_c_after);
    try std.testing.expect(std.mem.startsWith(u8, mode_c_after, mode_c_shebang));
    try std.testing.expect(std.mem.indexOf(u8, mode_c_after, "opt: u8?") != null);
    try std.testing.expect(std.mem.indexOf(u8, mode_c_after, "return flag;") != null);

    const mode_b_after = try std.Io.Dir.cwd().readFileAlloc(io, mode_b_path, allocator, .limited(64 * 1024));
    defer allocator.free(mode_b_after);
    try std.testing.expect(std.mem.startsWith(u8, mode_b_after, mode_b_prefix));
    try std.testing.expect(std.mem.indexOf(u8, mode_b_after, "opt: i32?") != null);
    try std.testing.expect(std.mem.indexOf(u8, mode_b_after, "return flag;") != null);
}

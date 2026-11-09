//! CoreX Stage 0 Bootstrap Compiler Root Module
//!
//! Aggregates and re-exports the foundational memory arenas, virtual file system, lossless CST/AST
//! syntax tables, diagnostic catalog and snippet renderer, CLI command router, and benchmark harness.
//!
//! Serves as the single canonical library root (`corex`) imported by the CLI entrypoint (`main.zig`),
//! automated verification suites (`tests/`), and performance benchmark suites (`bench/`).

const std = @import("std");

// ------------------------------------- PUBLIC API --------------------------------------

// --------------------- Submodule Exports ----------------------
/// Memory foundation: typed 32-bit IDs, `Span`, `BumpArena`, and `StringInterner`.
pub const mem_foundation = @import("mem_foundation.zig");
/// Virtual file system, `.cxtree` headers, `LineIndex`, and `VfsSourceMap` (`SourceMap`).
pub const vfs_sourcemap = @import("vfs_sourcemap.zig");
/// Lossless CST, `TokenBuffer`, `TriviaPiece`, and `AstArena` (`AstStore`) syntax tables.
pub const syntax_arenas = @import("syntax_arenas.zig");
/// Monochrome Unicode glyph registry, `ColorMode`, and ANSI SGR styling helpers.
pub const style = @import("cli/style.zig");
/// Rounded Unicode card, aligned table, and 1/8th-block progress bar renderers.
pub const box_draw = @import("cli/box_draw.zig");
/// Dynamic CLI subcommand/flag metadata registry, Levenshtein typo hints, and command router.
pub const router = @import("cli/router.zig");
/// Diagnostic severity, `DiagnosticCode` catalog, `DiagnosticSink`, and `TransactionalPatcher`.
pub const diagnostic = @import("diag/diagnostic.zig");
/// Single-line, multi-line, and cross-file monochrome diagnostic snippet renderer.
pub const renderer = @import("diag/renderer.zig");
/// Statistical performance benchmark harness and monochrome table reporter.
pub const bench_harness = @import("bench/harness.zig");

// ---------------- Foundational Type Re-Exports ----------------
/// Canonical 32-bit source file identifier.
pub const FileId = mem_foundation.FileId;
/// Canonical 32-bit interned string identifier.
pub const StringId = mem_foundation.StringId;
/// Canonical alias for `StringId` representing an interned symbol.
pub const SymbolId = mem_foundation.SymbolId;
/// Canonical 32-bit token stream index.
pub const TokenIndex = mem_foundation.TokenIndex;
/// Canonical alias for `TokenIndex`.
pub const TokenId = mem_foundation.TokenId;
/// Canonical 32-bit lossless CST node index.
pub const CstNodeIndex = mem_foundation.CstNodeIndex;
/// Canonical alias for `CstNodeIndex`.
pub const CstNodeId = mem_foundation.CstNodeId;
/// Canonical 32-bit AST node index.
pub const NodeIndex = mem_foundation.NodeIndex;
/// Canonical alias for `NodeIndex`.
pub const AstNodeId = mem_foundation.AstNodeId;
/// Canonical 32-bit AST `extra_data` index.
pub const ExtraIndex = mem_foundation.ExtraIndex;
/// Canonical 32-bit HIR node index.
pub const HirIndex = mem_foundation.HirIndex;
/// Canonical alias for `HirIndex`.
pub const HirId = mem_foundation.HirId;
/// Canonical 32-bit lexical scope identifier.
pub const ScopeId = mem_foundation.ScopeId;
/// Canonical 32-bit memory region identifier.
pub const RegionId = mem_foundation.RegionId;
/// Canonical 32-bit diagnostic identifier.
pub const DiagId = mem_foundation.DiagId;
/// Canonical 32-bit type identifier.
pub const TypeId = mem_foundation.TypeId;
/// Canonical 32-bit MIR basic block identifier.
pub const MirBlockId = mem_foundation.MirBlockId;
/// Canonical 32-bit MIR SSA value identifier.
pub const MirValueId = mem_foundation.MirValueId;
/// 4-byte tagged AST operand (`node`, `token`, or `extra`).
pub const PackedOperand = mem_foundation.PackedOperand;
/// 8-byte MIR instruction location (`block` + `instruction_index`).
pub const MirLocation = mem_foundation.MirLocation;
/// 12-byte source byte range (`file_id`, `start_byte`, `end_byte`).
pub const Span = mem_foundation.Span;
/// 64 KiB page-slab bump arena with $O(1)$ checkpoint/restore.
pub const BumpArena = mem_foundation.BumpArena;
/// Open-addressed `Wyhash(0)` string interner.
pub const StringInterner = mem_foundation.StringInterner;

// ------------------ VFS & Syntax Re-Exports -------------------
/// 16-bit package identifier.
pub const PackageId = vfs_sourcemap.PackageId;
/// Resolved 1-based line, UTF-8 column, and 0-based UTF-16 column record.
pub const LineCol = vfs_sourcemap.LineCol;
/// $O(\log L)$ line start index and non-ASCII line bitset.
pub const LineIndex = vfs_sourcemap.LineIndex;
/// Content-addressable virtual file system and source map.
pub const VfsSourceMap = vfs_sourcemap.VfsSourceMap;
/// Ergonomic alias for `VfsSourceMap`.
pub const SourceMap = vfs_sourcemap.SourceMap;
/// Lexical token taxonomy.
pub const TokenKind = syntax_arenas.TokenKind;
/// Structure-of-Arrays token and trivia buffer.
pub const TokenBuffer = syntax_arenas.TokenBuffer;
/// Pre-order lossless Concrete Syntax Tree arena.
pub const LosslessCstArena = syntax_arenas.LosslessCstArena;
/// Structure-of-Arrays Abstract Syntax Tree arena.
pub const AstArena = syntax_arenas.AstArena;
/// Alias for `AstArena`.
pub const AstStore = syntax_arenas.AstStore;

// ---------------- Diagnostics & CLI Re-Exports ----------------
/// Monochrome Unicode glyph registry.
pub const Glyphs = style.Glyphs;
/// Terminal ANSI color policy (`auto`, `always`, `never`).
pub const ColorMode = style.ColorMode;
/// Resolved terminal styling configuration.
pub const StyleConfig = style.StyleConfig;
/// Diagnostic severity enum.
pub const Severity = diagnostic.Severity;
/// 16-byte source byte edit record.
pub const TextEdit = diagnostic.TextEdit;
/// Atomic bundle of `TextEdit` replacements.
pub const SuggestedFix = diagnostic.SuggestedFix;
/// Annotated source span for diagnostic rendering.
pub const LabeledSpan = diagnostic.LabeledSpan;
/// Canonical non-overlapping diagnostic code enum.
pub const DiagnosticCode = diagnostic.DiagnosticCode;
/// Structured compiler diagnostic record.
pub const Diagnostic = diagnostic.Diagnostic;
/// Arena-backed diagnostic collector with 100-error cap.
pub const DiagnosticSink = diagnostic.DiagnosticSink;
/// Conflict-free transactional byte patcher.
pub const TransactionalPatcher = diagnostic.TransactionalPatcher;
/// Monochrome Unicode & ANSI diagnostic snippet renderer.
pub const DiagnosticRenderer = renderer.DiagnosticRenderer;

test "test_root_module_references_all_phase0_submodules" {
    std.testing.refAllDecls(@This());
    _ = mem_foundation;
    _ = vfs_sourcemap;
    _ = syntax_arenas;
    _ = style;
    _ = box_draw;
    _ = router;
    _ = diagnostic;
    _ = renderer;
    _ = bench_harness;
}

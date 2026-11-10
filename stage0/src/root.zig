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
/// Deterministic maximal-munch UTF-8 lexer, `TriviaAccumulator`, and identifier casing helpers.
pub const lexer = @import("lexer.zig");
/// Fault-tolerant recursive-descent + Pratt parser, lossless CST/AST builder, and incremental re-parser.
pub const parser = @import("parser.zig");
/// Demand-driven incremental query database (`CompilerDb`) with Early Cutoff and Durability.
pub const query_db = @import("query_db.zig");
/// Hybrid steerable Wadler-Lindig formatter (`corex fmt`), 8-byte `DocArena`, and `--fix` engine.
pub const fmt_engine = @import("fmt_engine.zig");
/// Module & lexical scope name resolution, `SymbolTable`, `ScopeArena`, and Levenshtein typo engine.
pub const symbol_resolver = @import("symbol_resolver.zig");
/// Canonical 14-byte SoA `TypeNode` `InternPool` (`TypeArena`), Constrained Type Groups, and bidirectional type checker.
pub const type_system = @import("type_system.zig");
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
/// Canonical CoreX orthographic identifier casing category.
pub const IdentifierCase = lexer.IdentifierCase;
/// Disjoint identifier or keyword classification result.
pub const IdentifierClassification = lexer.IdentifierClassification;
/// Configurable resource caps and warning toggles for `Lexer`.
pub const LexerOptions = lexer.LexerOptions;
/// Deterministic maximal-munch UTF-8 lexer.
pub const Lexer = lexer.Lexer;
/// Single-pass UTF-8 tokenizer entry point.
pub const tokenize = lexer.tokenize;
/// Canonical alias for `tokenize`.
pub const lexFile = lexer.lexFile;
/// Looks up a lexeme in the 45-keyword + 19-primitive-type table.
pub const lookupKeywordOrPrim = lexer.lookupKeywordOrPrim;
/// Classifies an identifier or keyword under the `DR-03` disjoint casing invariant.
pub const classifyIdentifierOrKeyword = lexer.classifyIdentifierOrKeyword;
/// Converts an identifier to canonical `snake_case`.
pub const toSnakeCase = lexer.toSnakeCase;
/// Converts an identifier to canonical `PascalCase`.
pub const toPascalCase = lexer.toPascalCase;
/// Converts an identifier to canonical `SCREAMING_SNAKE_CASE`.
pub const toScreamingSnakeCase = lexer.toScreamingSnakeCase;
/// 128-bit token kind bitset for $O(1)$ synchronization and lookahead checks.
pub const TokenSet128 = parser.TokenSet128;
/// Source byte edit descriptor for incremental re-lexing and re-parsing.
pub const EditRange = parser.EditRange;
/// Telemetry returned by `reparseIncremental`.
pub const IncrementalReparseStats = parser.IncrementalReparseStats;
/// Configurable resource caps and warning toggles for `Parser`.
pub const ParserOptions = parser.ParserOptions;
/// Fault-tolerant recursive-descent and Pratt parser.
pub const Parser = parser.Parser;
/// Parses a pre-tokenized `TokenBuffer` into `cst_arena` and `ast_arena`.
pub const parseTokens = parser.parseTokens;
/// Tokenizes `source` and parses it into `cst_arena` and `ast_arena`.
pub const parseSource = parser.parseSource;
/// Canonical alias for `parseSource`.
pub const parseFile = parser.parseFile;
/// Incrementally re-lexes and re-parses `new_source` after `edit`.
pub const reparseIncremental = parser.reparseIncremental;

// ------------------ Query Engine Re-Exports -------------------
/// Monotonically increasing logical database revision clock.
pub const Revision = query_db.Revision;
/// Input stability classification (`low`, `medium`, `high`).
pub const Durability = query_db.Durability;
/// 128-bit structural or cryptographic content fingerprint.
pub const Fingerprint128 = query_db.Fingerprint128;
/// Streaming 128-bit dual-seed `Wyhash` structural hasher.
pub const StructuralHasher = query_db.StructuralHasher;
/// Packed 32-bit definition handle (`file_index` + `local_item_index`).
pub const DefId = query_db.DefId;
/// Canonical 10-stage demand-driven query pipeline stage enum.
pub const QueryStage = query_db.QueryStage;
/// Universal 8-byte key identifying a node in the `CompilerDb` dependency DAG.
pub const QueryKey = query_db.QueryKey;
/// 40-byte memoized query header.
pub const MemoHeader = query_db.MemoHeader;
/// Error set returned by demand-driven queries in `CompilerDb`.
pub const QueryError = query_db.QueryError;
/// Top-level declaration category tag in `ItemTree`.
pub const ItemKind = query_db.ItemKind;
/// Single top-level declaration entry in a file's `ItemTree`.
pub const ItemTreeEntry = query_db.ItemTreeEntry;
/// Position-independent top-level `ItemTree` firewall for a source file.
pub const ItemTree = query_db.ItemTree;
/// Position-independent relative body AST projection window for a `DefId`.
pub const BodyAstWindow = query_db.BodyAstWindow;
/// Demand-driven incremental query database (`DR-12` Section 3).
pub const CompilerDb = query_db.CompilerDb;

// ---------------- Formatter Engine Re-Exports -----------------
/// Document algebra opcode discriminant (`1` byte inside `DocInst`).
pub const DocOp = fmt_engine.DocOp;
/// Group breaking policy (`auto_fit`, `force_break`, `columnar_grid`).
pub const GroupMode = fmt_engine.GroupMode;
/// Exact 8-byte Wadler-Lindig document algebra instruction.
pub const DocInst = fmt_engine.DocInst;
/// Open group stack frame for $O(1)$ `flat_width` backpatching.
pub const OpenGroupFrame = fmt_engine.OpenGroupFrame;
/// Contiguous arena of 8-byte `DocInst` instructions.
pub const DocArena = fmt_engine.DocArena;
/// Single-pass $O(N)$ linear document renderer.
pub const DocRenderer = fmt_engine.DocRenderer;
/// Configuration options controlling `corex fmt` and `corex fmt --fix`.
pub const FormatOptions = fmt_engine.FormatOptions;
/// Result returned by `formatSource`, `formatSourceWithOptions`, and `formatTokensAndCst`.
pub const FormatResult = fmt_engine.FormatResult;
/// Formats a pre-tokenized `TokenBuffer` and `LosslessCstArena` using `FormatOptions`.
pub const formatTokensAndCst = fmt_engine.formatTokensAndCst;
/// Tokenizes, parses, and formats `source` using `FormatOptions`.
pub const formatSourceWithOptions = fmt_engine.formatSourceWithOptions;
/// Tokenizes, parses, and formats `source` using default `FormatOptions`.
pub const formatSource = fmt_engine.formatSource;

// --------- Symbol Resolution & Type System Re-Exports ---------
/// Disjoint symbol namespace (`type_ns`, `value_ns`, `const_ns`).
pub const Namespace = symbol_resolver.Namespace;
/// 3-bit namespace lookup filter mask.
pub const NamespaceMask = symbol_resolver.NamespaceMask;
/// Lexical or module scope kind tag.
pub const ScopeKind = symbol_resolver.ScopeKind;
/// Contiguous Structure-of-Arrays lexical and module scope arena.
pub const ScopeArena = symbol_resolver.ScopeArena;
/// Strongly typed 32-bit index into `SymbolTable.symbols`.
pub const SymbolIndex = symbol_resolver.SymbolIndex;
/// Item visibility tier across module boundaries.
pub const Visibility = symbol_resolver.Visibility;
/// Resolved symbol classification tag.
pub const SymbolKind = symbol_resolver.SymbolKind;
/// Resolved symbol record in `SymbolTable`.
pub const SymbolRecord = symbol_resolver.SymbolRecord;
/// Explicit `@overload` function group.
pub const OverloadSet = symbol_resolver.OverloadSet;
/// Unified lexical and module symbol table.
pub const SymbolTable = symbol_resolver.SymbolTable;
/// Collects module-level declarations for a parsed source file.
pub const collectFileModuleItems = symbol_resolver.collectFileModuleItems;
/// Resolves `use` import statements for a parsed source file.
pub const resolveFileUseImports = symbol_resolver.resolveFileUseImports;
/// Computes bounded Damerau-Levenshtein edit distance for `E0403` suggestions.
pub const computeEditDistance = symbol_resolver.computeEditDistance;
/// 32-bit primitive membership bitmask for Constrained Type Groups (`DR-04` Section 1.2).
pub const TypeGroupMask = type_system.TypeGroupMask;
/// Canonical `TypeNode` discriminant tag (`DR-04` Section 2.1).
pub const TypeTag = type_system.TypeTag;
/// 1-byte packed type capability and property bitflags.
pub const TypeFlags = type_system.TypeFlags;
/// Parameter passing convention mode (`DR-02`).
pub const ParamMode = type_system.ParamMode;
/// Maximum recursion depth for type and expression checking (`256`).
pub const MAX_TYPE_DEPTH = type_system.MAX_TYPE_DEPTH;
/// Exact 14-byte zero-padding Structure-of-Arrays `TypeNode` (`DR-04` Section 2.1).
pub const TypeNode = type_system.TypeNode;
/// Inline 16-slot stack `SubstitutionMap` with overflow spill (`DR-04` Section 2.2).
pub const SubstitutionMap = type_system.SubstitutionMap;
/// Canonical deduplicated `InternPool` (`TypeArena`) pre-populated with static `TypeId` slots `0..63`.
pub const InternPool = type_system.InternPool;
/// Alias for `InternPool`.
pub const TypeArena = type_system.TypeArena;
/// Spine-local bidirectional type checker and Maranget pattern exhaustiveness verifier.
pub const TypeChecker = type_system.TypeChecker;
/// Result bundle returned by `typecheckSource`.
pub const TypecheckResult = type_system.TypecheckResult;
/// Standalone single-file lex + parse + resolve + bidirectional type-check entry point.
pub const typecheckSource = type_system.typecheckSource;

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
    _ = lexer;
    _ = parser;
    _ = query_db;
    _ = fmt_engine;
    _ = symbol_resolver;
    _ = type_system;
    _ = style;
    _ = box_draw;
    _ = router;
    _ = diagnostic;
    _ = renderer;
    _ = bench_harness;
}

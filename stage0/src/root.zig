//! CoreX Stage 0 Bootstrap Compiler Root Module
//!
//! Aggregates and re-exports the foundational memory arenas, virtual file system, lossless CST/AST
//! syntax tables, incremental query engine, MIR/SAST verifiers, C99/LLVM codegen backends, package
//! manifest/cache/resolver subsystems, diagnostic snippet renderer, CLI router, and bench harness.
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
/// Zero-legacy `corex upgrade` three-tier rule catalog (`DR-14`, `DR-21`, `DR-22`, & `DR-23`).
pub const upgrade_rules = @import("upgrade_rules.zig");
/// Zero-legacy 3-tier CST/AST/semantic source and manifest migration engine (`corex upgrade`, `DR-14`).
pub const upgrade_engine = @import("upgrade_engine.zig");
/// Unified `W0202` idiom linter, `corex check --fix`, and `DR-17` `--caps` / `--explain-caps` auditor.
pub const check_audit = @import("check_audit.zig");
/// Built-in zero-dependency LSP 3.17 JSON-RPC 2.0 server (`corex lsp`, `DR-12` & `DR-17`).
pub const lsp_server = @import("lsp_server.zig");
/// Module & lexical scope name resolution, `SymbolTable`, `ScopeArena`, and Levenshtein typo engine.
pub const symbol_resolver = @import("symbol_resolver.zig");
/// Canonical 14-byte SoA `TypeNode` `InternPool` (`TypeArena`), Constrained Type Groups, and bidirectional type checker.
pub const type_system = @import("type_system.zig");
/// 18-byte zero-padding SoA `HirNode`/`HirStore` and canonical `AST -> HIR` desugaring engine (`DR-13` §2).
pub const hir = @import("hir.zig");
/// Block-Argument SSA `MirBody`, Braun `MirSsaBuilder`, Maranget + Jacobs decision trees, and `MirVerifier` `V1`–`V6`.
pub const mir = @import("mir.zig");
/// Phase 6 `MIR` SAST engine, `ElaborateDrops`, Demand-Sliced Pentagon BCE, and capability sandbox (`DR-06`, `DR-17`, `DR-20`).
pub const mir_sast = @import("mir_sast.zig");
/// Sandboxed 64-bit register `MirVm`, reflection intrinsics, `Wyhash(0)` memoization, and `.rodata` promotion (`DR-05` §3).
pub const mir_vm = @import("mir_vm.zig");
/// Dual-mode `MIR` optimizer (`--dev` `D1`–`D5` & `--release` `R1`–`R6`), monomorphizer, and `LayoutShapeKey` deduplicator.
pub const mir_opt = @import("mir_opt.zig");
/// Stackless coroutine state-machine lowering, liveness frame coloring, and `16 KiB` inline frame verifier (`DR-08`).
pub const mir_async = @import("mir_async.zig");
/// In-process C11/C23 preprocessor, lexer, and recursive-descent header parser (`DR-10` §2.2).
pub const c_frontend = @import("c_frontend.zig");
/// `corex translate-c` AST -> canonical `.cx` emission and `@c_import` synthesis engine (`DR-10` §2.2).
pub const c_translate = @import("c_translate.zig");
/// Target specs, unified `TypeLayoutResolver`, `AbiClassifier`, `CodegenBackend`, and `Prune-02` atomic file writer.
pub const codegen_abi = @import("codegen_abi.zig");
/// Cross-target `lld`/driver linker, deterministic `.a`/`.lib` archive writer, and COFF `.def` -> `.lib` generator (`DR-10`).
pub const codegen_link = @import("codegen_link.zig");
/// Phase-8 `< 250` LOC `InFlightOpSlot` (`64B`), `ReactorVTable`, and `CompletionReaper` simulation/reactor seam (`DR-08`, `DR-18`).
pub const sim_seam = @import("sim_seam.zig");
/// Phase-7 `< 200` LOC forward-compatible `--dev` GOT, `CxTypeLayoutRecord`, and `.cx_dev_meta` binary seam (`DR-19`).
pub const codegen_dev_seam = @import("codegen_dev_seam.zig");
/// Tier A (`-ofmt=c`) deterministic ISO C99 backend emitter and `zig cc` compilation driver (`DR-01`, `DR-20`).
pub const codegen_c = @import("codegen_c.zig");
/// Tier B (`LLVM 20–23`) opaque-pointer `.ll` backend, optional static C++20 bridge, and `--fuzz` SanCov driver (`DR-09`, `DR-18`).
pub const codegen_llvm = @import("codegen_llvm.zig");
/// Four-tier differential backend execution oracle (`MirVm` `--dev`/`--release` vs Tier A C99 vs Tier B LLVM, `DR-20` `D-07A`).
pub const diff_oracle = @import("diff_oracle.zig");
/// Phase-9 `< 35` LOC PubGrub decision-level-0 conflict DAG & `TomlSpanAnchor` seam (`DR-16` §2.3, `DR-20` Seam `#7`).
pub const pkg_conflict_seam = @import("pkg_conflict_seam.zig");
/// Phase-9 `< 35` LOC binary `.cxi` public-interface & capability digest seam (`DR-17` §4.3, `DR-20` `D-08`).
pub const pkg_cxi_seam = @import("pkg_cxi_seam.zig");
/// `corex.toml` manifest, `.cx` script frontmatter, SemVer 2.0.0, and `corex.lock` v1 parser/patcher (`DR-11` §1).
pub const pkg_manifest = @import("pkg_manifest.zig");
/// Content-addressable `COREX_HOME` `.cxtree`/blob cache, Bao `.obao` streaming, Ed25519 + RFC 6962 proofs, and `vendor/` (`DR-11` §2).
pub const pkg_cache = @import("pkg_cache.zig");
/// Hybrid `Bounded-MVS` + `100,000`-step `PubGrub CDCL` package/feature resolver and auto-sync engine (`DR-11` §3, `DR-16`).
pub const pkg_resolver = @import("pkg_resolver.zig");
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
/// Negotiated LSP 3.17 character offset encoding (`utf16` vs `utf8`).
pub const PositionEncoding = vfs_sourcemap.PositionEncoding;
/// Maximum number of active in-memory VFS overlays (`256`).
pub const MAX_OPEN_OVERLAYS = vfs_sourcemap.MAX_OPEN_OVERLAYS;
/// Maximum aggregate byte footprint across active VFS overlays (`64 MiB`).
pub const MAX_OPEN_OVERLAY_BYTES = vfs_sourcemap.MAX_OPEN_OVERLAY_BYTES;
/// Resolved 1-based line, UTF-8 column, and 0-based UTF-16 column record.
pub const LineCol = vfs_sourcemap.LineCol;
/// $O(\log L)$ line start index and non-ASCII line bitset.
pub const LineIndex = vfs_sourcemap.LineIndex;
/// Content-addressable virtual file system and source map.
pub const VfsSourceMap = vfs_sourcemap.VfsSourceMap;
/// Ergonomic alias for `VfsSourceMap`.
pub const SourceMap = vfs_sourcemap.SourceMap;
/// 120-variant lexical token taxonomy (`DR-03`, `DR-21`, `DR-22`, & `DR-23`).
pub const TokenKind = syntax_arenas.TokenKind;
/// 1-byte bit-packed token trivia and lexical recovery flags.
pub const TokenFlags = syntax_arenas.TokenFlags;
/// Structure-of-Arrays token and trivia buffer.
pub const TokenBuffer = syntax_arenas.TokenBuffer;
/// Lossless Concrete Syntax Tree node kind taxonomy.
pub const CstNodeKind = syntax_arenas.CstNodeKind;
/// Pre-order lossless Concrete Syntax Tree arena.
pub const LosslessCstArena = syntax_arenas.LosslessCstArena;
/// Abstract Syntax Tree node discriminant tag taxonomy.
pub const AstTag = syntax_arenas.AstTag;
/// 13-byte Structure-of-Arrays AST node record.
pub const AstNode = syntax_arenas.AstNode;
/// Structure-of-Arrays Abstract Syntax Tree arena.
pub const AstArena = syntax_arenas.AstArena;
/// Alias for `AstArena`.
pub const AstStore = syntax_arenas.AstStore;
/// Precomputes the exclusive end offset in `ast.extra_data` for every AST node in $O(N)$ time.
pub const computeAstNodeExtraEnds = syntax_arenas.computeAstNodeExtraEnds;
/// Precomputes the dense $O(1)$ `CstNodeIndex -> NodeIndex` lookup table in $O(N)$ time.
pub const computeCstToAstMap = syntax_arenas.computeCstToAstMap;
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
/// Looks up a lexeme in the 50-keyword + 20-primitive-type table.
pub const lookupKeywordOrPrim = lexer.lookupKeywordOrPrim;
/// Classifies an identifier or keyword under the `DR-03` disjoint casing invariant.
pub const classifyIdentifierOrKeyword = lexer.classifyIdentifierOrKeyword;
/// Converts an identifier to canonical `snake_case`.
pub const toSnakeCase = lexer.toSnakeCase;
/// Converts an identifier to canonical `PascalCase`.
pub const toPascalCase = lexer.toPascalCase;
/// Converts an identifier to canonical `SCREAMING_SNAKE_CASE`.
pub const toScreamingSnakeCase = lexer.toScreamingSnakeCase;
/// Alignment directive inside an 8-byte `FmtSpec` (`DR-22` §1.7).
pub const FmtAlignMode = lexer.FmtAlignMode;
/// Sign rendering mode inside an 8-byte `FmtSpec` (`DR-22` §1.7).
pub const FmtSignMode = lexer.FmtSignMode;
/// Format presentation type code inside an 8-byte `FmtSpec` (`DR-22` §1.7).
pub const FmtTypeCode = lexer.FmtTypeCode;
/// Exact 8-byte stack-allocated format specifier descriptor (`DR-22` §1.7).
pub const FmtSpec = lexer.FmtSpec;
/// Decomposed numeric literal digits, radix, and explicit type suffix (`DR-22` §1.5).
pub const ParsedNumericSuffix = lexer.ParsedNumericSuffix;
/// Parses an interpolation format specifier body after `:` into an 8-byte `FmtSpec`.
pub const parseFormatSpec = lexer.parseFormatSpec;
/// Splits a numeric literal lexeme into its digit body, radix, and optional `TypeId` suffix.
pub const extractNumericSuffix = lexer.extractNumericSuffix;
/// Returns `true` if `lexeme` is a triple-quoted multiline string or byte-string literal.
pub const isMultilineStringLexeme = lexer.isMultilineStringLexeme;
/// Extracts and closing-quote dedents a `"""…"""` multiline string lexeme without decoding escapes.
pub const extractMultilineStringContent = lexer.extractMultilineStringContent;
/// Canonical alias for `extractMultilineStringContent`.
pub const extractMultilineString = lexer.extractMultilineString;
/// Cooks a non-interpolated string or byte-string literal lexeme (dedent + escape decoding).
pub const cookStringLiteral = lexer.cookStringLiteral;
/// Decodes a single-byte `b'x'` literal lexeme into its `u8` value.
pub const extractByteLiteralValue = lexer.extractByteLiteralValue;
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
/// Canonical 14-stage demand-driven query pipeline stage enum.
pub const QueryStage = query_db.QueryStage;
/// Universal 8-byte key identifying a node in the `CompilerDb` dependency DAG.
pub const QueryKey = query_db.QueryKey;
/// 40-byte memoized query header.
pub const MemoHeader = query_db.MemoHeader;
/// Error set returned by demand-driven queries in `CompilerDb`.
pub const QueryError = query_db.QueryError;
/// Top-level declaration category tag in `ItemTree`.
pub const ItemKind = query_db.ItemKind;
/// Packed 8-byte `TriviaPiece` slice reference for $O(1)$ declaration and module doc hover extraction (`ADR-23A`).
pub const DocTriviaSpan = query_db.DocTriviaSpan;
/// Single top-level declaration entry in a file's `ItemTree`.
pub const ItemTreeEntry = query_db.ItemTreeEntry;
/// Position-independent top-level `ItemTree` firewall for a source file.
pub const ItemTree = query_db.ItemTree;
/// Position-independent relative body AST projection window for a `DefId`.
pub const BodyAstWindow = query_db.BodyAstWindow;
/// Per-definition `MIR` SAST ownership, contract, and capability verification artifact (`Stage 9`).
pub const SastVerificationArtifact = query_db.SastVerificationArtifact;
/// Per-definition lowered and `V1`–`V6` verified `MIR` bundle artifact (`Stage 11`).
pub const DefMirArtifact = query_db.DefMirArtifact;
/// Evaluated `const` / `comptime` definition artifact with `.rodata` promotion (`Stage 12`).
pub const ComptimeEvalArtifact = query_db.ComptimeEvalArtifact;
/// 64-bit semantic `Wyhash(0)` nominal field/variant layout digest (`DR-19` §1.2).
pub const FieldHash64 = query_db.FieldHash64;
/// Strongly typed 32-bit `.cx_got[got_idx]` callable slot handle (`DR-19` §1.1).
pub const GotSlotId = query_db.GotSlotId;
/// Computes the deterministic `DR-19` §1.2 `FieldHash64` (`TypeLayoutHash`) for `raw_ty`.
pub const computeNominalFieldHash64 = query_db.computeNominalFieldHash64;
/// Builds a 32-byte `CxTypeLayoutRecord` pairing `LayoutShapeKey` with semantic `FieldHash64`.
pub const buildCxTypeLayoutRecord = query_db.buildCxTypeLayoutRecord;
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
/// Surgical byte replacement returned by `formatByteRange`.
pub const RangeTextEdit = fmt_engine.RangeTextEdit;
/// Formats a pre-tokenized `TokenBuffer` and `LosslessCstArena` using `FormatOptions`.
pub const formatTokensAndCst = fmt_engine.formatTokensAndCst;
/// Tokenizes, parses, and formats `source` using `FormatOptions`.
pub const formatSourceWithOptions = fmt_engine.formatSourceWithOptions;
/// Tokenizes, parses, and formats `source` using default `FormatOptions`.
pub const formatSource = fmt_engine.formatSource;
/// Formats the tightest CST sibling slice covering `[req_start_byte .. req_end_byte]`.
pub const formatByteRange = fmt_engine.formatByteRange;

// ------------------ Upgrade Rules Re-Exports ------------------
/// Three-tier execution stage in `corex upgrade` (`DR-14` §2.2).
pub const UpgradeEngineTier = upgrade_rules.UpgradeEngineTier;
/// Specification wave introducing an upgrade rule (`DR-21`, `DR-22`, or `DR-23`).
pub const UpgradeWave = upgrade_rules.UpgradeWave;
/// Contiguous 1-byte identifier for canonical `corex upgrade` rules.
pub const UpgradeRuleId = upgrade_rules.UpgradeRuleId;
/// Static metadata descriptor for a `corex upgrade` transformation rule.
pub const UpgradeRuleDescriptor = upgrade_rules.UpgradeRuleDescriptor;
/// Total number of canonical `corex upgrade` rules (`UPGRADE_RULE_CATALOG.len`).
pub const UPGRADE_RULE_COUNT = upgrade_rules.UPGRADE_RULE_COUNT;
/// Maximum fixed-point synergy passes executed by `corex upgrade` (`4`).
pub const MAX_SYNERGY_PASSES = upgrade_rules.MAX_SYNERGY_PASSES;
/// Dense `corex upgrade` rule catalog (`UR-21-00`–`UR-23-06`).
pub const UPGRADE_RULE_CATALOG = upgrade_rules.UPGRADE_RULE_CATALOG;
/// Resolves a `"UR-XX-YY"` rule code to its `UpgradeRuleId` in $O(1)$ time.
pub const lookupUpgradeRule = upgrade_rules.lookupUpgradeRule;
/// Resolves a `"UR-XX-YY"` rule code to its `UpgradeRuleDescriptor` in $O(1)$ time.
pub const resolveUpgradeRuleDescriptor = upgrade_rules.resolveUpgradeRuleDescriptor;

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
/// 1-byte bit-packed mask of compiler-synthesized `@derive(…)` traits (`DR-05` Section 2.3).
pub const DeriveMask = symbol_resolver.DeriveMask;
/// 1-byte bit-packed mask of valid declaration targets for an `@attribute_schema` struct (`DR-05` Section 2.2).
pub const AttrTargetMask = symbol_resolver.AttrTargetMask;
/// Resolved symbol record in `SymbolTable`.
pub const SymbolRecord = symbol_resolver.SymbolRecord;
/// 2-byte bit-packed declaration-level contract, ownership, and FFI flags (`DR-17`, `DR-20`).
pub const DeclContractFlags = symbol_resolver.DeclContractFlags;
/// Canonical ambient capability bit positions for `@std_cap_boundary` (`DR-17` §3.1).
pub const CapabilityBits = symbol_resolver.CapabilityBits;
/// Returns `true` when a `@link(section: …)` name targets a forbidden executable/CTOR/TLS section (`E0327`).
pub const isForbiddenExecutableSection = symbol_resolver.isForbiddenExecutableSection;
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
/// Three-tier CoreX value ownership classification (`DR-06` §1.2, `DR-20` §2.3).
pub const OwnershipTier = type_system.OwnershipTier;
/// Classifies any `TypeId` into `.copy_tier`, `.auto_drop_tier`, or `.linear_tier`.
pub const classifyOwnershipTier = type_system.classifyOwnershipTier;
/// 1-byte bit-packed effect contract mask carried on `fn(…)` and closure types.
pub const FnPtrContractMask = type_system.FnPtrContractMask;
/// Canonical field ordinals on CoreX's implicit/explicit `Context` value (`Seam #2`, `D-04`, `D-06B`).
pub const ContextFieldKind = type_system.ContextFieldKind;
/// Seam #2 `Context` field layout descriptor shared with `HIR`, `MIR`, and `mir_sast`.
pub const ContextFieldLayout = type_system.ContextFieldLayout;
/// Returns `true` when `ty` refers to the built-in or user-declared `Context` struct (`Seam #2`).
pub const isContextType = type_system.isContextType;
/// Reason code reported when `FromBytes` or `IntoBytes` rejects a type (`D-01`, `E0315`).
pub const WireLayoutViolationReason = type_system.WireLayoutViolationReason;
/// Detailed `FromBytes` / `IntoBytes` violation payload carrying exact byte offset for `E0315`.
pub const WireLayoutViolation = type_system.WireLayoutViolation;
/// Selector distinguishing `.narrow[Dst]()` vs. `.try_narrow[Dst]()` in `BodySemanticSideTables` (`D-11`).
pub const NarrowCallKind = type_system.NarrowCallKind;
/// Side-table record emitted by `TypeChecker` for `.narrow` / `.try_narrow` calls (`D-11`).
pub const NarrowCallInfo = type_system.NarrowCallInfo;
/// Evaluates Constrained Type Group satisfaction (`FromBytes`, `IntoBytes`, `Copy`, `Number`, …).
pub const checkGroupSatisfaction = type_system.checkGroupSatisfaction;
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
/// Target pointer size and alignment parameters shared across `TypeChecker`, `HIR`, `MirVm`, and `MIR`.
pub const TargetLayout = type_system.TargetLayout;
/// Computed target-specific byte size and alignment of a `TypeId`.
pub const TypeLayout = type_system.TypeLayout;
/// Computes target-aware `TypeLayout` directly from `InternPool` and `SymbolTable`.
pub const computeTypeLayoutWithPool = type_system.computeTypeLayoutWithPool;
/// Computes the byte offset of field `field_ordinal` inside `struct_ty` for `target_layout`.
pub const computeStructFieldOffset = type_system.computeStructFieldOffset;
/// Validated compile-time constant argument value inside an `@attribute_schema` instance.
pub const AttrArgValue = type_system.AttrArgValue;
/// Single validated field argument on an `@attribute_schema` attribute application.
pub const AttrFieldInit = type_system.AttrFieldInit;
/// Validated user-defined `@attribute_schema` instance attached to a declaration, field, or variant.
pub const AttrInstance = type_system.AttrInstance;
/// Per-body AST-window-scoped semantic side tables extracted from `TypeChecker`.
pub const BodySemanticSideTables = type_system.BodySemanticSideTables;
/// Canonical compiler-intrinsic selector for `@snake_case` expressions (`DR-05` Section 3.3).
pub const IntrinsicKind = type_system.IntrinsicKind;
/// Result bundle returned by `typecheckSource`.
pub const TypecheckResult = type_system.TypecheckResult;
/// Standalone single-file lex + parse + resolve + bidirectional type-check entry point.
pub const typecheckSource = type_system.typecheckSource;

// -------------------- HIR & MIR Re-Exports --------------------
/// Canonical `HIR` node discriminant (`DR-13` §2.1).
pub const HirTag = hir.HirTag;
/// Value/place classification stored on each `HirNode`.
pub const ValueCategory = hir.ValueCategory;
/// 1-byte bit-packed `HirNode` metadata flags.
pub const HirFlags = hir.HirFlags;
/// 18-byte zero-padding Structure-of-Arrays `HirNode` (`20` bytes AoS).
pub const HirNode = hir.HirNode;
/// Packed 32-bit LSB-first `bit_field` slice specification (`DR-13` §2.2).
pub const BitSpec = hir.BitSpec;
/// Classification of `hir_return` for `defer` vs. `errdefer` cleanup routing.
pub const ReturnErrorKind = hir.ReturnErrorKind;
/// Canonical `HIR` unary operator enum.
pub const HirUnaryOp = hir.HirUnaryOp;
/// Canonical `HIR` binary operator enum.
pub const HirBinaryOp = hir.HirBinaryOp;
/// Canonical `HIR` cast kind enum.
pub const HirCastKind = hir.HirCastKind;
/// Aggregate construction flavor encoded in `hir_construct`.
pub const HirConstructKind = hir.HirConstructKind;
/// Local variable or parameter metadata in `HirStore.locals`.
pub const HirLocalDecl = hir.HirLocalDecl;
/// Lowered function, method, derived trait method, or closure header in `HirStore.functions`.
pub const HirFnMeta = hir.HirFnMeta;
/// Compile-time constant value interned in `HirStore.const_pool`.
pub const ComptimeValue = hir.ComptimeValue;
/// Canonical lowered pattern representation in `HirStore.patterns`.
pub const HirPat = hir.HirPat;
/// Canonical `match` arm record in `HirStore.match_arms`.
pub const HirMatchArm = hir.HirMatchArm;
/// Pluggable callback interface for Tier-2 `comptime` evaluation (`MirVm` / `CompilerDb`).
pub const ComptimeEvalHook = hir.ComptimeEvalHook;
/// Per-module or per-`DefId` Structure-of-Arrays `HIR` arena (`DR-13` §2.1).
pub const HirStore = hir.HirStore;
/// Lowers a parsed and type-checked source file into a `HirStore`.
pub const lowerFileToHir = hir.lowerFileToHir;
/// Lowers a single `DefId` (and synthesized `@derive` methods) into a `HirStore`.
pub const lowerDefToHir = hir.lowerDefToHir;
/// Standalone end-to-end `Source -> HIR` helper.
pub const lowerSourceToHir = hir.lowerSourceToHir;
/// Deterministic monochrome `HIR` tree formatter for golden snapshot tests.
pub const renderHir = hir.renderHir;
/// Strongly typed 32-bit index into `MirBody.locals`.
pub const LocalId = mir.LocalId;
/// Strongly typed 32-bit index into `MirBody.places`.
pub const PlaceId = mir.PlaceId;
/// Strongly typed 32-bit index into `MirBody.extra_edges`.
pub const EdgeId = mir.EdgeId;
/// 1-byte bit-packed flags on `LocalDecl`.
pub const LocalFlags = mir.LocalFlags;
/// 16-byte local slot descriptor in `MirBody.locals`.
pub const LocalDecl = mir.LocalDecl;
/// 8-byte memory access path (`base` + `proj_start` + `proj_len`).
pub const MirPlace = mir.MirPlace;
/// Projection step kind in `MirBody.projections`.
pub const ProjKind = mir.ProjKind;
/// 8-byte projection step in `MirBody.projections`.
pub const MirProjection = mir.MirProjection;
/// Canonical `MIR` instruction opcode (`0..24`).
pub const MirOp = mir.MirOp;
/// Explicit signed, unsigned, and IEEE-754 binary opcodes in `MIR`.
pub const BinOpKind = mir.BinOpKind;
/// Explicit unary arithmetic, logical, and conversion opcodes in `MIR`.
pub const UnaryOpKind = mir.UnaryOpKind;
/// Sub-kind encoded in `MirInst.aux_u16` on `MirOp.aggregate_make`.
pub const AggregateKind = mir.AggregateKind;
/// Sub-kind encoded in `MirInst.aux_u16` on `MirOp.intrinsic_op` (`DR-06`, `DR-20`).
pub const MirIntrinsicKind = mir.MirIntrinsicKind;
/// 1-byte instruction property flags in `MirInst`.
pub const InstFlags = mir.InstFlags;
/// 16-byte SoA instruction record in `MirBody.insts`.
pub const MirInst = mir.MirInst;
/// Control-flow terminator kind ending every `MirBasicBlock`.
pub const TerminatorKind = mir.TerminatorKind;
/// 12-byte control-flow terminator embedded in `MirBasicBlock`.
pub const MirTerminator = mir.MirTerminator;
/// 32-byte basic block record in `MirBody.blocks`.
pub const MirBasicBlock = mir.MirBasicBlock;
/// 16-byte first-class outgoing CFG edge record in `MirBody.extra_edges`.
pub const MirOutgoingEdge = mir.MirOutgoingEdge;
/// Call-site metadata record in `MirBody.calls`.
pub const MirCallSite = mir.MirCallSite;
/// Constant scalar or literal record in `MirBody.consts`.
pub const MirConst = mir.MirConst;
/// 1-byte `@must_vectorize` / `@vectorize_width` contract flags (`DR-20` Seam `#4`).
pub const LoopContractMask = mir.LoopContractMask;
/// 8-byte SIMD loop contract descriptor (`DR-19` §1, `DR-20` Seam `#4`).
pub const LoopContractMeta = mir.LoopContractMeta;
/// 16-byte sparse loop-vectorization contract stored in `MirBody.loop_contracts`.
pub const MirLoopContractEntry = mir.MirLoopContractEntry;
/// 16-byte `$O(1)$` embedded binary blob descriptor stored in `MirConst.raw_blob` (`DR-20` `D-03`).
pub const RawBlobConst = mir.RawBlobConst;
/// Deduplicated binary blob store populated by `materializeModuleEmbedBytes`.
pub const MirBlobStore = mir.MirBlobStore;
/// Pre-codegen `@embed_bytes` materializer converting constant paths into `MirConst.raw_blob`.
pub const materializeModuleEmbedBytes = mir.materializeModuleEmbedBytes;
/// Vacated non-`Copy` `&mut` `subscript` projection window recorded on `MirBody` (`Fix-06B`).
pub const VacatedProjectionWindow = mir.VacatedProjectionWindow;
/// Block-Argument SSA representation of a lowered function or constant body.
pub const MirBody = mir.MirBody;
/// Returns `true` when `raw_ty` unwraps to a nominal `@zero_pad` `struct`, `union`, or `enum`.
pub const isZeroPadNominalType = mir.isZeroPadNominalType;
/// Braun et al. single-pass forward Block-Argument SSA builder (`DR-13` §3.5).
pub const MirSsaBuilder = mir.MirSsaBuilder;
/// Cooper-Harvey-Kennedy dominator tree rooted at `^bb0`.
pub const DominatorTree = mir.DominatorTree;
/// Computes the dominator tree for `MirBody`.
pub const computeDominators = mir.computeDominators;
/// Formal verification error set for `MirVerifier` (`V1`–`V6`).
pub const MirVerifyError = mir.MirVerifyError;
/// Verifies formal `MirBody` invariants `V1`–`V6` (`DR-13` §4.4).
pub const verifyMirBody = mir.verifyMirBody;
/// Collection of verified `MirBody` records lowered from a `HirStore`.
pub const MirModuleBundle = mir.MirModuleBundle;
/// Lowers a single `HirFnMeta` into a verified Block-Argument SSA `MirBody`.
pub const lowerHirFnToMir = mir.lowerHirFnToMir;
/// Lowers all non-`subscript` bodies in `HirStore` into verified `MirBody`s.
pub const lowerHirToMir = mir.lowerHirToMir;
/// Lowers a single `HirFnMeta` into a verified `MirBody` with `bounds_check`/`narrow_check` SAST intrinsics.
pub const lowerHirFnToMirForSast = mir.lowerHirFnToMirForSast;
/// Lowers all non-`subscript` bodies in `HirStore` into verified `MirBody`s with SAST intrinsics.
pub const lowerHirToMirForSast = mir.lowerHirToMirForSast;
/// Standalone end-to-end `Source -> HIR -> MIR` helper.
pub const lowerSourceToMir = mir.lowerSourceToMir;
/// Deterministic monochrome `MIR` formatter for golden snapshot tests.
pub const renderMir = mir.renderMir;

// ----------------- MIR SAST Engine Re-Exports -----------------
/// Canonical 16-bit (`2B`) inferred effect and OS capability bitset (`DR-17` §2.5).
pub const EffectCapabilityMask = mir_sast.EffectCapabilityMask;
/// Canonical 16-bit (`2B`) contract and `Context.scratch[0..2]` ping-pong mask (`DR-17` §2.5).
pub const FnContractScratchMask = mir_sast.FnContractScratchMask;
/// Canonical 40-byte (`34` caller-observable bytes) per-function region, effect, and stack summary (`DR-17` §2.5).
pub const FnRegionSummary = mir_sast.FnRegionSummary;
/// Interprocedural call, destructor, or capability-reification edge classification (`DR-17` §2.4).
pub const WitnessEdgeKind = mir_sast.WitnessEdgeKind;
/// 4-byte packed metadata carried on each `WitnessCallEdge`.
pub const WitnessEdgeMeta = mir_sast.WitnessEdgeMeta;
/// 12-byte Compressed Sparse Row (`CSR`) call-graph edge (`DR-17` §2.4).
pub const WitnessCallEdge = mir_sast.WitnessCallEdge;
/// Single hop in a shortest capability/effect violation witness chain.
pub const WitnessStep = mir_sast.WitnessStep;
/// Contiguous CSR store of `FnRegionSummary` records and `WitnessCallEdge`s.
pub const FnSummaryStore = mir_sast.FnSummaryStore;
/// Strongly typed 32-bit handle into a per-function `MovePath` trie.
pub const MovePathId = mir_sast.MovePathId;
/// 1-byte bit-packed ownership and projection flags on a `MovePathNode`.
pub const MovePathFlags = mir_sast.MovePathFlags;
/// Canonical 20-byte `MovePath` trie node (`DR-06` §2.1).
pub const MovePathNode = mir_sast.MovePathNode;
/// Result of resolving a `MirPlace` against a `MovePath` trie (`is_partial` weak-update guard).
pub const PlacePathLookup = mir_sast.PlacePathLookup;
/// Hybrid bitset (`u64` inline register words for `<= 64` paths, `BumpArena` slice for `> 64`).
pub const DenseBitSet = mir_sast.DenseBitSet;
/// 16-byte sign-biased order-preserving scalar interval (`DR-06` §2.3).
pub const Intv = mir_sast.Intv;
/// 32-byte (`256`-bit) strict upper-bound row in the Demand-Sliced Pentagon solver (`DR-06` §2.3).
pub const PentagonSubRow = mir_sast.PentagonSubRow;
/// Three-tier package capability roll-up (`ambient_caps`, `reachable_caps`, `surface_caps`, `DR-17` §3.1).
pub const PackageCapSummary = mir_sast.PackageCapSummary;
/// Package capability sandbox policy declared in `corex.toml` / `corex.lock` (`DR-17` §3.1).
pub const PackageCapPolicy = mir_sast.PackageCapPolicy;
/// Strongly typed cross-`DefId` `FnRegionSummary` resolver hook for `CompilerDb` Stage 9.
pub const ExternalSummaryResolver = mir_sast.ExternalSummaryResolver;
/// Configuration parameters governing `mir_sast` analysis and elaboration.
pub const SastConfig = mir_sast.SastConfig;
/// Complete result returned by `analyzeAndElaborateMirModule` and `analyzeSingleMirBody`.
pub const MirSastResult = mir_sast.MirSastResult;
/// Self-contained pipeline bundle returned by `lowerAndVerifySourceMirSast`.
pub const MirSastPipelineBundle = mir_sast.MirSastPipelineBundle;
/// Hard per-function `MovePath` trie node cap (`4,096`).
pub const MAX_MOVE_PATHS = mir_sast.MAX_MOVE_PATHS;
/// Hard Demand-Sliced Pentagon upper-bound variable cap (`256`, `Fix-06A` / `Prune-05`).
pub const MAX_SUB_VARS = mir_sast.MAX_SUB_VARS;
/// Hard Demand-Sliced Pentagon reachable block cap (`128`, `Fix-06A` / `Prune-05`).
pub const MAX_PENTAGON_BLOCKS = mir_sast.MAX_PENTAGON_BLOCKS;
/// Verifies `PackageCapSummary` against `PackageCapPolicy` (`E0324` & `W0330`).
pub const verifyPackageCapPolicy = mir_sast.verifyPackageCapPolicy;
/// Runs the complete 4-pass Phase 6 SAST & Elaboration pipeline in-place on `MirBody` slices.
pub const analyzeAndElaborateMirModule = mir_sast.analyzeAndElaborateMirModule;
/// Runs the Phase 6 SAST & Elaboration pipeline in-place on a single `MirBody`.
pub const analyzeSingleMirBody = mir_sast.analyzeSingleMirBody;
/// Standalone end-to-end `Source -> HIR -> MIR -> SAST` pipeline helper.
pub const lowerAndVerifySourceMirSast = mir_sast.lowerAndVerifySourceMirSast;
/// 24-byte Pentagon-proven SSA scalar range & alignment fact.
pub const ProvenValueRange = mir_sast.ProvenValueRange;
/// Extracts sign-bias-decoded `ProvenValueRange` facts for LLVM `!range` / `@llvm.assume`.
pub const computeBodyProvenRanges = mir_sast.computeBodyProvenRanges;

// ------------ `MirVm` & `MIR` Optimizer Re-Exports ------------
/// Disjoint 2-bit allocation domain tag inside `ComptimeAllocId`.
pub const AllocDomain = mir_vm.AllocDomain;
/// 4-byte `MirVm` / `.rodata` / `StringInterner` / `fn_addr` handle.
pub const ComptimeAllocId = mir_vm.ComptimeAllocId;
/// 8-byte symbolic pointer (`alloc_id` + `byte_offset`).
pub const SymbolicPtr = mir_vm.SymbolicPtr;
/// 8-byte `MirVm` virtual register slot (`DR-05` §3.1).
pub const RegSlot = mir_vm.RegSlot;
/// 8-byte pointer provenance entry.
pub const ProvenanceEntry = mir_vm.ProvenanceEntry;
/// 3-way `MirVm` value representation (`inline_scalar`, `inline_ptr`, `by_value_snapshot`).
pub const VmValueRepr = mir_vm.VmValueRepr;
/// Deduplicated `.rodata` constant blob promoted from `MirVm`.
pub const RodataBlob = mir_vm.RodataBlob;
/// Arena-backed `.rodata` constant pool with `Wyhash(0)` deduplication.
pub const RodataPool = mir_vm.RodataPool;
/// Bounded `Wyhash(0)` pure-call memoization cache.
pub const PureCallMemoCache = mir_vm.PureCallMemoCache;
/// Execution limits and target layout configuration for `MirVm`.
pub const VmExecOptions = mir_vm.VmExecOptions;
/// Error set returned when `MirVm` traps or runs out of host memory.
pub const VmEvalError = mir_vm.VmEvalError;
/// Sandboxed 64-bit register `MIR` virtual machine (`DR-05` §3).
pub const MirVm = mir_vm.MirVm;
/// Evaluates an arbitrary lowered `HIR` subtree via `MirVm`.
pub const evalHirSubtreeWithMirVm = mir_vm.evalHirSubtreeWithMirVm;
/// Constructs a `ComptimeEvalHook` bound to `CompilerDb`.
pub const makeComptimeEvalHook = mir_vm.makeComptimeEvalHook;
/// ABI register/indirect passing classification in `LayoutShapeKey`.
pub const AbiPassClass = mir_opt.AbiPassClass;
/// Niche bit-pattern representation tag in `LayoutShapeKey`.
pub const NicheKind = mir_opt.NicheKind;
/// Exact 16-byte physical layout shape descriptor (`DR-13` §5.3).
pub const LayoutShapeKey = mir_opt.LayoutShapeKey;
/// Operational semantics tag guarding sound `LayoutShapeKey` deduplication.
pub const OpSemanticsTag = mir_opt.OpSemanticsTag;
/// Function inline directive (`default_mode`, `inline_hint`, `inline_always`, `inline_never`).
pub const InlineDirective = mir_opt.InlineDirective;
/// Configuration flags governing `optimizeMirModule`.
pub const MirOptConfig = mir_opt.MirOptConfig;
/// Output artifact produced by `optimizeMirModule`.
pub const MirOptModuleResult = mir_opt.MirOptModuleResult;
/// Computes the 16-byte `LayoutShapeKey` for a concrete `TypeId`.
pub const computeLayoutShapeKey = mir_opt.computeLayoutShapeKey;
/// Executes the `--dev` (`D1`–`D5`) or `--release` (`D1`–`D5` + `R1`–`R6`) `MIR` pipeline.
pub const optimizeMirModule = mir_opt.optimizeMirModule;

// ---------- Phase 7 Codegen, ABI & Dev Seam Exports -----------
/// Supported Phase-7 hardware instruction-set architectures.
pub const TargetArch = codegen_abi.TargetArch;
/// Supported Phase-7 operating systems and ABI environments.
pub const TargetOs = codegen_abi.TargetOs;
/// Supported target C/system ABI environments (`gnu`, `musl`, `msvc`, `macos`, `wasi`, `freestanding`).
pub const TargetAbi = codegen_abi.TargetAbi;
/// Binary linkage mode (`auto`, `static`, `dynamic`) across cross-target linkers (`DR-10`).
pub const LinkMode = codegen_abi.LinkMode;
/// Target SIMD alignment tier (`none`, `sse2_neon_simd128`, `avx2`, `avx512`).
pub const SimdLevel = codegen_abi.SimdLevel;
/// 4-byte binary-exact target specification covering all 11 canonical targets.
pub const TargetSpec = codegen_abi.TargetSpec;
/// 24-byte binary-exact niche descriptor.
pub const NicheSpec = codegen_abi.NicheSpec;
/// 32-byte binary-exact resolved type layout record.
pub const ResolvedTypeLayout = codegen_abi.ResolvedTypeLayout;
/// Unified frontend type layout, field-order, `#soa` column, and niche resolver.
pub const TypeLayoutResolver = codegen_abi.TypeLayoutResolver;
/// Lowered machine calling convention (`cx_native`, `cx_result_cc`, `c_system`, `wasm_mvp`).
pub const CallingConvKind = codegen_abi.CallingConvKind;
/// Per-parameter or return value passing mode in `AbiParamRecipe`.
pub const AbiPassMode = codegen_abi.AbiPassMode;
/// 16-byte binary-exact parameter or return ABI lowering recipe.
pub const AbiParamRecipe = codegen_abi.AbiParamRecipe;
/// Complete lowered machine calling-convention recipe for a function or indirect call site.
pub const AbiFnRecipe = codegen_abi.AbiFnRecipe;
/// Canonical machine calling-convention classifier (`DR-09` §1.1, `Fix-07`).
pub const AbiClassifier = codegen_abi.AbiClassifier;
/// Exhaustive tagged-union codegen backend (`tier_a_c99` / `tier_b_llvm`).
pub const CodegenBackend = codegen_abi.CodegenBackend;
/// Optimization pipeline level for Tier B LLVM emission (`-O0`..`-Oz`).
pub const OptLevel = codegen_abi.OptLevel;
/// Tier A (`-ofmt=c`) backend configuration.
pub const CBackendConfig = codegen_abi.CBackendConfig;
/// Tier B (`LLVM 20–23`) backend configuration.
pub const LlvmBackendConfig = codegen_abi.LlvmBackendConfig;
/// Output artifact form (`.source_text`, `.object_file`, `.executable`, `.static_library`, `.shared_library`).
pub const OutputArtifactKind = codegen_abi.OutputArtifactKind;
/// Owned artifact bundle produced by `CodegenBackend.emitModule`.
pub const CodegenArtifact = codegen_abi.CodegenArtifact;
/// Strongly typed module input consumed by `CodegenBackend.emitModule`.
pub const CodegenModuleInput = codegen_abi.CodegenModuleInput;
/// `Prune-02` `SIGKILL`-safe `UnlinkAndReplace` atomic file writer.
pub const atomicWriteOutputFile = codegen_abi.atomicWriteOutputFile;
/// 64-byte `.cx_dev_meta` binary section header (`DR-19` §1.2).
pub const CxDevSeamHeader = codegen_dev_seam.CxDevSeamHeader;
/// 24-byte `.cx_got` callable slot metadata record (`DR-19` §1.2).
pub const CxGotSlotMeta = codegen_dev_seam.CxGotSlotMeta;
/// 32-byte layout equivalence record pairing `LayoutShapeKey` with `FieldHash64` (`DR-19` §1.2).
pub const CxTypeLayoutRecord = codegen_dev_seam.CxTypeLayoutRecord;
/// 64-byte runtime safepoint control block (`DR-19` §1.2).
pub const CxReloadControlBlock = codegen_dev_seam.CxReloadControlBlock;
/// Canonical 4-tier differential oracle stage identifier (`DR-20` `D-07A`).
pub const OracleTierId = diff_oracle.OracleTierId;
/// Observable runtime outcome of a single backend tier in `diff_oracle`.
pub const OracleTierOutcome = diff_oracle.OracleTierOutcome;
/// Configuration options for `runFourTierDiffOracle` and `runFourTierDiffOracleOnDb`.
pub const DiffOracleOptions = diff_oracle.DiffOracleOptions;
/// Complete 4-tier differential verification report (`DR-20` `D-07A`).
pub const DiffOracleReport = diff_oracle.DiffOracleReport;
/// Runs the 4-tier differential backend oracle against a `CompilerDb` module graph.
pub const runFourTierDiffOracleOnDb = diff_oracle.runFourTierDiffOracleOnDb;
/// Runs the 4-tier differential backend oracle on a single `.cx` source buffer.
pub const runFourTierDiffOracle = diff_oracle.runFourTierDiffOracle;
/// Hard `16 KiB` inline stackless coroutine frame budget (`DR-08` §2.3, `E0317`).
pub const ASYNC_INLINE_FRAME_CAP_BYTES = mir_async.ASYNC_INLINE_FRAME_CAP_BYTES;
/// Canonical stackless coroutine state discriminant (`unpolled`, `1..K`, `completed`, `canceled`).
pub const CoroStateTag = mir_async.CoroStateTag;
/// 24-byte `.coro_suspend` state-machine transition metadata (`DR-08` §2.2).
pub const SuspendPointMeta = mir_async.SuspendPointMeta;
/// 16-byte liveness-colored coroutine frame local slot record (`DR-08` §2.3).
pub const CoroLocalSlot = mir_async.CoroLocalSlot;
/// 16-byte stackless coroutine frame layout summary (`DR-08` §2.3).
pub const CoroFrameLayout = mir_async.CoroFrameLayout;
/// Per-body stackless coroutine lowering and frame-coloring plan (`DR-08`).
pub const AsyncBodyPlan = mir_async.AsyncBodyPlan;
/// Module-wide stackless coroutine lowering plan (`DR-08`).
pub const AsyncModulePlan = mir_async.AsyncModulePlan;
/// 64-byte cache-line-aligned in-flight proactor completion slot (`DR-08` §5.3).
pub const InFlightOpSlot = sim_seam.InFlightOpSlot;
/// Normalized 16-byte proactor completion queue entry (`DR-08` §5.3).
pub const ReactorCqe = sim_seam.ReactorCqe;
/// C-ABI proactor, clock, entropy, and `buggify` vtable seam (`DR-18` §2.1).
pub const ReactorVTable = sim_seam.ReactorVTable;
/// Two-phase DMA quarantine and zombie-CQE slot manager (`DR-08` §4.3, `Fix-08B`).
pub const CompletionReaper = sim_seam.CompletionReaper;

// --------- Phase 9 Package, Cache & Resolver Exports ----------
/// Contiguous 1-byte discriminant classifying PubGrub incompatibility nodes (`0..5`, `DR-16` §2.3).
pub const IncompatKind = pkg_conflict_seam.IncompatKind;
/// Exact 16-byte (`128`-bit, `0` padding) version/feature interval term in an incompatibility.
pub const IncompatTerm = pkg_conflict_seam.IncompatTerm;
/// Exact 24-byte (`192`-bit, `0` padding) node in a decision-level-0 PubGrub derivation DAG.
pub const IncompatNode = pkg_conflict_seam.IncompatNode;
/// Exact 24-byte (`192`-bit, `0` padding) lossless `corex.toml` or `.cx` frontmatter span anchor.
pub const TomlSpanAnchor = pkg_conflict_seam.TomlSpanAnchor;
/// Arena-cloned decision-level-0 conflict proof DAG exported by `pkg_resolver`.
pub const ConflictDagExport = pkg_conflict_seam.ConflictDagExport;
/// Clones a level-0 PubGrub conflict derivation DAG into `BumpArena` slabs.
pub const exportLevelZeroConflictDag = pkg_conflict_seam.exportLevelZeroConflictDag;
/// Exact 64-byte (`align(8)`, `0` padding) binary `.cxi` summary header (`DR-20` `D-08`).
pub const CxiHeader = pkg_cxi_seam.CxiHeader;
/// Exact 64-byte (`align(8)`, `0` padding) exported `pub fn` / `pub trait` method `.cxi` record.
pub const CxiFnRecord = pkg_cxi_seam.CxiFnRecord;
/// Exact 40-byte (`align(8)`, `0` padding) exported `pub` nominal / `distinct` type `.cxi` record.
pub const CxiTypeRecord = pkg_cxi_seam.CxiTypeRecord;
/// Computes the domain-separated `"corex.cxi.v1.2026-04"` `BLAKE3` `.cxi` interface digest.
pub const computeCxiBlake3 = pkg_cxi_seam.computeCxiBlake3;
/// Serializes sorted `CxiFnRecord` and `CxiTypeRecord` slices into an 8-byte-aligned `.cxi` summary.
pub const serializeCxiSummary = pkg_cxi_seam.serializeCxiSummary;
/// 12-byte SemVer 2.0.0 `(major, minor, patch)` numeric core.
pub const SemVerCore = pkg_manifest.SemVerCore;
/// 20-byte SemVer 2.0.0 version record including prerelease and build metadata handles.
pub const SemVer = pkg_manifest.SemVer;
/// Normalized SemVer requirement conjunction.
pub const VersionReq = pkg_manifest.VersionReq;
/// Validated `corex.toml` or `.cx` script frontmatter manifest.
pub const Manifest = pkg_manifest.Manifest;
/// Workspace manifest bundle covering `[workspace]` members, `[patch]`, and `[security]`.
pub const WorkspaceManifestBundle = pkg_manifest.WorkspaceManifestBundle;
/// Inline `use "<spec>" as <alias>;` source dependency specification (`DR-11` §1.2).
pub const InlineUseSpec = pkg_manifest.InlineUseSpec;
/// Deterministic `corex.lock` v1 package pin record.
pub const LockPackage = pkg_manifest.LockPackage;
/// Deterministic `corex.lock` v1 lockfile document.
pub const Lockfile = pkg_manifest.Lockfile;
/// Dual-bounded (`max_entries` + `max_bytes`) intrusive LRU metadata cache (`AGENTS.md` §2).
pub const BoundedMetadataLru = pkg_cache.BoundedMetadataLru;
/// Content-addressable `COREX_HOME/cache/blake3` global package cache (`DR-11` §2).
pub const PkgCache = pkg_cache.PkgCache;
/// Resolves `COREX_HOME` (`$COREX_HOME` -> OS cache/home directory fallback).
pub const resolveCorexHome = pkg_cache.resolveCorexHome;
/// Exact 12-byte compatibility-series coexistence key (`DR-11` §3.1).
pub const SeriesKey = pkg_resolver.SeriesKey;
/// Fast 512-bit inline feature bitset (`64B`) for `< 5 ms` MVS feature unification.
pub const FeatureBitset512 = pkg_resolver.FeatureBitset512;
/// Topologically resolved package instance in `ResolvedPackageGraph`.
pub const ResolvedPackageNode = pkg_resolver.ResolvedPackageNode;
/// Complete deterministic dependency & feature resolution output.
pub const ResolvedPackageGraph = pkg_resolver.ResolvedPackageGraph;
/// Configuration options governing `resolveProjectGraph`.
pub const ResolveOptions = pkg_resolver.ResolveOptions;
/// Resolves workspace/script manifests, auto-sync, features, `corex.lock`, and `.cxtree` packages.
pub const resolveProjectGraph = pkg_resolver.resolveProjectGraph;

// ---------------- Diagnostics & CLI Re-Exports ----------------
/// Canonical alphabetical 9-entry CLI subcommand descriptor table.
pub const CLI_SUBCOMMANDS = router.CLI_SUBCOMMANDS;
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
    _ = upgrade_rules;
    _ = upgrade_engine;
    _ = check_audit;
    _ = lsp_server;
    _ = symbol_resolver;
    _ = type_system;
    _ = hir;
    _ = mir;
    _ = mir_sast;
    _ = mir_vm;
    _ = mir_opt;
    _ = mir_async;
    _ = c_frontend;
    _ = c_translate;
    _ = codegen_abi;
    _ = codegen_link;
    _ = sim_seam;
    _ = codegen_dev_seam;
    _ = codegen_c;
    _ = codegen_llvm;
    _ = diff_oracle;
    _ = pkg_conflict_seam;
    _ = pkg_cxi_seam;
    _ = pkg_manifest;
    _ = pkg_cache;
    _ = pkg_resolver;
    _ = style;
    _ = box_draw;
    _ = router;
    _ = diagnostic;
    _ = renderer;
    _ = bench_harness;
}

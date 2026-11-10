//! CoreX Stage 0 Master Verification Suite Runner (`tests/test_runner.zig`)
//!
//! Aggregates and executes all Phase 0, Phase 1, Phase 2, Phase 3, and Phase 4 isolated unit tests
//! (`tests/unit/`), golden snapshot tests (`tests/snapshots/`), deterministic PRNG fuzzers
//! (`tests/fuzz/`), and repository drift guards (`tests/drift/`).
//!
//! Invoked automatically by `zig build test` alongside internal `stage0/src/` module tests.

const std = @import("std");

// ------------------------------------- PUBLIC API --------------------------------------

/// Unit tests for `mem_foundation.zig` (typed 32-bit handles, `Span`, `BumpArena`, `StringInterner`).
pub const mem_foundation_test = @import("unit/mem_foundation_test.zig");
/// Unit tests for `vfs_sourcemap.zig` (`PackageId`, `.cxtree` headers, `LineIndex`, `VfsSourceMap`).
pub const vfs_sourcemap_test = @import("unit/vfs_sourcemap_test.zig");
/// Unit tests for `syntax_arenas.zig` (`TokenBuffer`, `LosslessCstArena`, `AstArena`).
pub const syntax_arenas_test = @import("unit/syntax_arenas_test.zig");
/// Unit tests for `lexer.zig` (112 `TokenKind`s, 10 `TriviaKind`s, casing, literals, lossless CST).
pub const lexer_test = @import("unit/lexer_test.zig");
/// Unit tests for `parser.zig` (lossless CST/AST, 15 Pratt tiers, showcases, recovery, incremental).
pub const parser_test = @import("unit/parser_test.zig");
/// Unit tests for `query_db.zig` (`CompilerDb`, 10-stage pipeline, Early Cutoff, Durability, `ItemTree`).
pub const query_db_test = @import("unit/query_db_test.zig");
/// Unit tests for `fmt_engine.zig` (`DocInst`, `DocArena`, `DocRenderer`, `corex fmt`, `--fix`).
pub const fmt_engine_test = @import("unit/fmt_engine_test.zig");
/// Unit tests for `symbol_resolver.zig` (`ScopeArena`, `SymbolTable`, `mod`, `use`, `E0403`, `E0408`, `E0409`, `W0402`).
pub const symbol_resolver_test = @import("unit/symbol_resolver_test.zig");
/// Unit tests for `type_system.zig` (`InternPool`, `TypeGroupMask`, `E0400`–`E0415`, `W0401`, `E0502`).
pub const type_system_test = @import("unit/type_system_test.zig");
/// Unit tests for `diag/diagnostic.zig` and `diag/renderer.zig` (`DiagnosticSink`, `TransactionalPatcher`).
pub const diagnostic_test = @import("unit/diagnostic_test.zig");
/// Unit tests for `cli/style.zig`, `cli/box_draw.zig`, and `cli/router.zig`.
pub const cli_router_test = @import("unit/cli_router_test.zig");
/// Unit tests for `bench/harness.zig` (`computeStats`, `runCase`, `renderResultsTable`).
pub const bench_harness_test = @import("unit/bench_harness_test.zig");
/// Golden `.snap` snapshot tests for CLI help, token streams, diagnostics, `fmt`, and `query_db`.
pub const snapshot_test = @import("snapshots/snapshot_test.zig");
/// Phase 0 deterministic PRNG fuzzing suite (`LineIndex`, `TransactionalPatcher`, `BumpArena`).
pub const phase0_fuzz = @import("fuzz/phase0_fuzz.zig");
/// Phase 1 deterministic PRNG fuzzing suite (10,000,000+ lexer inputs + lossless round-trip).
pub const phase1_lexer_fuzz = @import("fuzz/phase1_lexer_fuzz.zig");
/// Phase 2 deterministic PRNG fuzzing suite (2,500+ mutated `.cx` ASTs + 1,000+ incremental edits).
pub const phase2_parser_fuzz = @import("fuzz/phase2_parser_fuzz.zig");
/// Phase 3 deterministic PRNG fuzzing suite (`corex fmt` idempotency/comments + `CompilerDb` Early Cutoff).
pub const phase3_fmt_fuzz = @import("fuzz/phase3_fmt_fuzz.zig");
/// Phase 4 deterministic PRNG fuzzing suite (`symbol_resolver` + `type_system` fault tolerance & incremental parity).
pub const phase4_typecheck_fuzz = @import("fuzz/phase4_typecheck_fuzz.zig");
/// Repository-wide drift guards (zero colored emojis, CLI parity, diagnostic catalog, `< 150` col format).
pub const drift_guard_test = @import("drift/drift_guard_test.zig");

test "test_runner_references_all_phase0_phase1_phase2_phase3_and_phase4_verification_suites" {
    std.testing.refAllDecls(@This());
    _ = mem_foundation_test;
    _ = vfs_sourcemap_test;
    _ = syntax_arenas_test;
    _ = lexer_test;
    _ = parser_test;
    _ = query_db_test;
    _ = fmt_engine_test;
    _ = symbol_resolver_test;
    _ = type_system_test;
    _ = diagnostic_test;
    _ = cli_router_test;
    _ = bench_harness_test;
    _ = snapshot_test;
    _ = phase0_fuzz;
    _ = phase1_lexer_fuzz;
    _ = phase2_parser_fuzz;
    _ = phase3_fmt_fuzz;
    _ = phase4_typecheck_fuzz;
    _ = drift_guard_test;
}

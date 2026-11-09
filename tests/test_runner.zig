//! CoreX Stage 0 Master Verification Suite Runner (`tests/test_runner.zig`)
//!
//! Aggregates and executes all Phase 0, Phase 1, and Phase 2 isolated unit tests (`tests/unit/`),
//! golden snapshot tests (`tests/snapshots/`), deterministic PRNG fuzzers (`tests/fuzz/`), and
//! repository drift guards (`tests/drift/`).
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
/// Unit tests for `diag/diagnostic.zig` and `diag/renderer.zig` (`DiagnosticSink`, `TransactionalPatcher`).
pub const diagnostic_test = @import("unit/diagnostic_test.zig");
/// Unit tests for `cli/style.zig`, `cli/box_draw.zig`, and `cli/router.zig`.
pub const cli_router_test = @import("unit/cli_router_test.zig");
/// Unit tests for `bench/harness.zig` (`computeStats`, `runCase`, `renderResultsTable`).
pub const bench_harness_test = @import("unit/bench_harness_test.zig");
/// Golden `.snap` snapshot tests for CLI help, token streams, and diagnostic rendering.
pub const snapshot_test = @import("snapshots/snapshot_test.zig");
/// Phase 0 deterministic PRNG fuzzing suite (`LineIndex`, `TransactionalPatcher`, `BumpArena`).
pub const phase0_fuzz = @import("fuzz/phase0_fuzz.zig");
/// Phase 1 deterministic PRNG fuzzing suite (10,000,000+ lexer inputs + lossless round-trip).
pub const phase1_lexer_fuzz = @import("fuzz/phase1_lexer_fuzz.zig");
/// Phase 2 deterministic PRNG fuzzing suite (2,500+ mutated `.cx` ASTs + 1,000+ incremental edits).
pub const phase2_parser_fuzz = @import("fuzz/phase2_parser_fuzz.zig");
/// Repository-wide drift guards (zero colored emojis, CLI parity, diagnostic catalog, `< 150` col format).
pub const drift_guard_test = @import("drift/drift_guard_test.zig");

test "test_runner_references_all_phase0_phase1_and_phase2_verification_suites" {
    std.testing.refAllDecls(@This());
    _ = mem_foundation_test;
    _ = vfs_sourcemap_test;
    _ = syntax_arenas_test;
    _ = lexer_test;
    _ = parser_test;
    _ = diagnostic_test;
    _ = cli_router_test;
    _ = bench_harness_test;
    _ = snapshot_test;
    _ = phase0_fuzz;
    _ = phase1_lexer_fuzz;
    _ = phase2_parser_fuzz;
    _ = drift_guard_test;
}

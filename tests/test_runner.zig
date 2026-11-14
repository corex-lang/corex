//! CoreX Stage 0 Master Verification Suite Runner (`tests/test_runner.zig`)
//!
//! Aggregates and executes all Phase 0, Phase 1, Phase 2, Phase 3, Phase 4, Phase 5, Phase 6, and
//! Phase 7 isolated unit tests (`tests/unit/`), golden snapshot tests (`tests/snapshots/`),
//! deterministic PRNG fuzzers (`tests/fuzz/`), and repository drift guards (`tests/drift/`).
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
/// Unit tests for `query_db.zig` (`CompilerDb`, 14-stage pipeline, Early Cutoff, Durability, `ItemTree`).
pub const query_db_test = @import("unit/query_db_test.zig");
/// Unit tests for `fmt_engine.zig` (`DocInst`, `DocArena`, `DocRenderer`, `corex fmt`, `--fix`).
pub const fmt_engine_test = @import("unit/fmt_engine_test.zig");
/// Unit tests for `symbol_resolver.zig` (`ScopeArena`, `SymbolTable`, `mod`, `use`, `E0403`, `E0408`, `E0409`, `W0402`).
pub const symbol_resolver_test = @import("unit/symbol_resolver_test.zig");
/// Unit tests for `type_system.zig` (`InternPool`, `TypeGroupMask`, `E0400`–`E0415`, `W0401`, `E0502`).
pub const type_system_test = @import("unit/type_system_test.zig");
/// Unit tests for `hir.zig` (18B SoA `HirNode`, `BitSpec`, all 12 `AST -> HIR` desugarings, `renderHir`).
pub const hir_test = @import("unit/hir_test.zig");
/// Unit tests for `mir.zig` (Block-Arg SSA `MirSsaBuilder`, `switch_int`, `defer`, `subscript`, `V1`–`V6`).
pub const mir_test = @import("unit/mir_test.zig");
/// Unit tests for `mir_sast.zig` (3-tier ownership, NLL, `ElaborateDrops`, `FnRegionSummary`, Pentagon BCE, `E03xx`/`W03xx`).
pub const mir_sast_test = @import("unit/mir_sast_test.zig");
/// Unit tests for `mir_vm.zig` (`SymbolicPtr`, `VmValueRepr`, `E0501`–`E0510`, 9 reflection intrinsics, `.rodata`).
pub const mir_vm_test = @import("unit/mir_vm_test.zig");
/// Unit tests for `mir_opt.zig` (`LayoutShapeKey`, `--dev` `D1`–`D5`, `--release` `R1`–`R6`, `W0501`, `ICF`).
pub const mir_opt_test = @import("unit/mir_opt_test.zig");
/// Unit tests for `codegen_abi.zig` (`TargetSpec`, `TypeLayoutResolver`, `AbiClassifier`, Phase 7 intrinsics, `E0006`–`E0008`).
pub const codegen_abi_test = @import("unit/codegen_abi_test.zig");
/// Unit tests for `codegen_dev_seam.zig` (`< 200` LOC seam, `.cx_dev_meta`, `FieldHash64`, `D-10A` cache invalidation).
pub const codegen_dev_seam_test = @import("unit/codegen_dev_seam_test.zig");
/// Unit tests for `codegen_c.zig` (Tier A ISO C99 emitter, `@zero_pad`, `#soa`, `--dev` GOT, native execution).
pub const codegen_c_test = @import("unit/codegen_c_test.zig");
/// Unit tests for `codegen_llvm.zig` (Tier B LLVM 20–23 IR emitter, `swifterror`, MVS, Pentagon, `--fuzz`).
pub const codegen_llvm_test = @import("unit/codegen_llvm_test.zig");
/// Unit & 4-tier differential tests for Stage-1 minimal `core` (`core/**/*.cx`).
pub const core_stdlib_test = @import("unit/core_stdlib_test.zig");
/// Unit & CLI end-to-end tests for `diff_oracle.zig` and Phase 7 subcommands (`build`, `run`, `test --diff-backends`).
pub const diff_oracle_test = @import("unit/diff_oracle_test.zig");
/// Unit tests for `diag/diagnostic.zig` and `diag/renderer.zig` (`DiagnosticSink`, `TransactionalPatcher`).
pub const diagnostic_test = @import("unit/diagnostic_test.zig");
/// Unit tests for `cli/style.zig`, `cli/box_draw.zig`, and `cli/router.zig`.
pub const cli_router_test = @import("unit/cli_router_test.zig");
/// Unit tests for `bench/harness.zig` (`computeStats`, `runCase`, `renderResultsTable`).
pub const bench_harness_test = @import("unit/bench_harness_test.zig");
/// Golden `.snap` snapshot tests for CLI help, token streams, diagnostics, `fmt`, `query_db`, and `MIR`/`SAST`.
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
/// Phase 5 deterministic PRNG fuzzing suite (`HIR`/`MIR` fault tolerance, `--dev` vs `--release` parity, and `CompilerDb` Stages 10–13).
pub const phase5_mir_comptime_fuzz = @import("fuzz/phase5_mir_comptime_fuzz.zig");
/// Phase 6 deterministic PRNG fuzzing suite (`mir_sast` fault tolerance, `--dev` vs `--release` drop/BCE parity, and `CompilerDb` Stage 9).
pub const phase6_sast_fuzz = @import("fuzz/phase6_sast_fuzz.zig");
/// Phase 7 deterministic PRNG fuzzing suite (4-tier differential backend oracle & cross-target IR determinism).
pub const phase7_diff_backends_fuzz = @import("fuzz/phase7_diff_backends_fuzz.zig");
/// Repository-wide drift guards (zero colored emojis, CLI parity, diagnostic catalog, `< 150` col format).
pub const drift_guard_test = @import("drift/drift_guard_test.zig");

test "test_runner_references_all_phase0_to_phase7_verification_suites" {
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
    _ = hir_test;
    _ = mir_test;
    _ = mir_sast_test;
    _ = mir_vm_test;
    _ = mir_opt_test;
    _ = codegen_abi_test;
    _ = codegen_dev_seam_test;
    _ = codegen_c_test;
    _ = codegen_llvm_test;
    _ = core_stdlib_test;
    _ = diff_oracle_test;
    _ = diagnostic_test;
    _ = cli_router_test;
    _ = bench_harness_test;
    _ = snapshot_test;
    _ = phase0_fuzz;
    _ = phase1_lexer_fuzz;
    _ = phase2_parser_fuzz;
    _ = phase3_fmt_fuzz;
    _ = phase4_typecheck_fuzz;
    _ = phase5_mir_comptime_fuzz;
    _ = phase6_sast_fuzz;
    _ = phase7_diff_backends_fuzz;
    _ = drift_guard_test;
}

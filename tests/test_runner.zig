//! CoreX Stage 0 Master Verification Suite Runner (`tests/test_runner.zig`)
//!
//! Aggregates and executes all Phase 0, Phase 1, Phase 2, Phase 3, Phase 4, Phase 5, Phase 6,
//! Phase 7, Phase 7.5 (`DR-21`), Phase 7.6 (`DR-22`), Phase 8 (`DR-08`, `DR-10`, `DR-18`),
//! Phase 9 (`DR-11`, `DR-16`, `DR-17`), Phase 10 (`DR-12`, `DR-14`, `DR-17`), Phase 10.6 (`DR-23`),
//! Phase 11.1 (`STD-01`), Phase 11.1b (`DR-24`), Phase 11.1c (`DR-25`), and Phase 11.2a (`STD-02`)
//! isolated unit tests (`tests/unit/`), negative lint/safety tests (`tests/compile_fail/`), golden
//! snapshot tests (`tests/snapshots/`), deterministic PRNG fuzzers (`tests/fuzz/`), and drift guards (`tests/drift/`).
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
/// Unit tests for `lexer.zig` (121 `TokenKind`s, 9 `TriviaKind`s, casing, literals, lossless CST).
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
/// Unit tests for `codegen_c.zig` (Tier A ISO C99 emitter, `zero_pad: true`, `#soa`, `--dev` GOT, native execution).
pub const codegen_c_test = @import("unit/codegen_c_test.zig");
/// Unit tests for `codegen_llvm.zig` (Tier B LLVM 20–23 IR emitter, `swifterror`, MVS, Pentagon, `--fuzz`).
pub const codegen_llvm_test = @import("unit/codegen_llvm_test.zig");
/// Unit & 4-tier differential tests for Stage-1 minimal `core` (`core/**/*.cx`).
pub const core_stdlib_test = @import("unit/core_stdlib_test.zig");
/// Unit & CLI end-to-end tests for `diff_oracle.zig` and Phase 7 subcommands (`build`, `run`, `test --diff-backends`).
pub const diff_oracle_test = @import("unit/diff_oracle_test.zig");
/// Comprehensive Phase 8 11-target cross-compilation, C11/C23 FFI, `async`/`await`, & SAST safety suite.
pub const phase8_test = @import("unit/phase8_test.zig");
/// Comprehensive Phase 9 package manager, global CAS cache, MVS/PubGrub, `.cxi`, & supply-chain sandbox suite.
pub const phase9_pkg_test = @import("unit/phase9_pkg_test.zig");
/// Comprehensive Phase 10 built-in LSP 3.17 server (`corex lsp`) end-to-end verification suite.
pub const phase10_lsp_test = @import("unit/phase10_lsp_test.zig");
/// Comprehensive Phase 10 `corex check` (`--fix`, `--deny-warnings`, `--caps`, `--explain-caps`) & `corex upgrade` suite.
pub const phase10_check_upgrade_test = @import("unit/phase10_check_upgrade_test.zig");
/// Comprehensive Phase 11.1 (`STD-01` Mandatory Step 1) compiler seam, intrinsics, SAST, & 4-tier parity suite.
pub const phase11_std01_step1_test = @import("unit/phase11_std01_step1_test.zig");
/// Comprehensive Phase 11.1 (`STD-01` Step 2) `stdlib/cx/` foundation, fat-slice ABI, & 4-tier parity suite.
pub const phase11_std01_step2_test = @import("unit/phase11_std01_step2_test.zig");
/// Comprehensive Phase 11.1 (`STD-01` §3.3) 5-gate architectural prover & Stage-4 red-team regression suite.
pub const phase11_std01_gates_test = @import("unit/phase11_std01_gates_test.zig");
/// Comprehensive Phase 11.1c (`RDG-25` Step 3A) Lexer, Parser/CST, and `SymbolTable` single-pass lint rules suite.
pub const phase11_step3a_lints_test = @import("unit/phase11_step3a_lints_test.zig");
/// Comprehensive Phase 11.1c (`RDG-25` Step 3B) `TypeChecker`, Idiom Audit, and `MIR` single-pass lint rules suite.
pub const phase11_step3b_lints_test = @import("unit/phase11_step3b_lints_test.zig");
/// Exhaustive Phase 11.1c (`DR-25` §4.4) 44-rule matrix, `<= 2`-pass `--fix`, `CRLF`, `CompiledGlob64`, & `W0413` suite.
pub const dr25_all_44_rules_test = @import("compile_fail/lint/dr25_all_44_rules_test.zig");
/// Stage 3 Red-Team (`[BUG-01]`–`[BUG-12]`), `E0302` shared-ref move soundness, & CLI/LSP polish regression suite.
pub const phase11_dr25_redteam_regressions_test = @import("unit/phase11_dr25_redteam_regressions_test.zig");
/// Comprehensive Phase 11.2a (`STD-02` Mandatory Step 1) compiler seams, `core.sys` & `MirVm` shims suite.
pub const phase11_std02_step1_test = @import("unit/phase11_std02_step1_test.zig");
/// Comprehensive Phase 11.2a (`STD-02` §2 & §3.3) 7-gate verification, `SimReactor` & negative safety suite.
pub const phase11_std02_gates_test = @import("unit/phase11_std02_gates_test.zig");
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
/// Phase 4 deterministic PRNG fuzzing suite (`symbol_resolver` + `type_system` + `DR-22` fault tolerance & incremental parity).
pub const phase4_typecheck_fuzz = @import("fuzz/phase4_typecheck_fuzz.zig");
/// Phase 5 deterministic PRNG fuzzing suite (`HIR`/`MIR` + `DR-22` fault tolerance, `--dev` vs `--release`, and `CompilerDb` 10–13).
pub const phase5_mir_comptime_fuzz = @import("fuzz/phase5_mir_comptime_fuzz.zig");
/// Phase 6 deterministic PRNG fuzzing suite (`mir_sast` + `DR-22` fault tolerance, `--dev` vs `--release` BCE/drops, and Stage 9).
pub const phase6_sast_fuzz = @import("fuzz/phase6_sast_fuzz.zig");
/// Phase 7 deterministic PRNG fuzzing suite (`DR-22` 4-tier differential backend oracle & cross-target IR determinism).
pub const phase7_diff_backends_fuzz = @import("fuzz/phase7_diff_backends_fuzz.zig");
/// Phase 8 deterministic PRNG fuzzing suite (C11/C23 `translate-c`, `.def`/archive determinism, & `async` 4-tier parity).
pub const phase8_ffi_async_fuzz = @import("fuzz/phase8_ffi_async_fuzz.zig");
/// Phase 9 deterministic PRNG fuzzing suite (MVS/PubGrub vs brute-force oracle, lossless TOML, & CAS/sandbox tampering).
pub const phase9_pkg_fuzz = @import("fuzz/phase9_pkg_fuzz.zig");
/// Phase 10 deterministic PRNG fuzzing suite (untrusted JSON-RPC framing, incremental VFS/CST edits, & `upgradeSource` convergence).
pub const phase10_lsp_upgrade_fuzz = @import("fuzz/phase10_lsp_upgrade_fuzz.zig");
/// Phase 11.1 (`STD-01`) deterministic PRNG fuzzing suite (container models, `ipnsort` vs `Powersort`, UTF-8 SIMD, & float/int round-trips).
pub const phase11_std01_fuzz = @import("fuzz/phase11_std01_fuzz.zig");
/// Phase 11.1c (`DR-25`) deterministic PRNG fuzzing suite (`SuppressionTable`, `CompiledGlob64`, & `--fix` convergence).
pub const phase11_dr25_lint_fuzz = @import("fuzz/phase11_dr25_lint_fuzz.zig");
/// Phase 11.2a (`STD-02`) deterministic PRNG fuzzing suite (`cx.path`, WTF-8/16, `cx.io` chaos streams, & Win32 quoting).
pub const phase11_std02_fuzz = @import("fuzz/phase11_std02_fuzz.zig");
/// Repository-wide drift guards (zero colored emojis, CLI parity, diagnostic catalog, `< 150` col format).
pub const drift_guard_test = @import("drift/drift_guard_test.zig");

test "test_runner_references_all_phase0_to_phase11_verification_suites" {
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
    _ = phase8_test;
    _ = phase9_pkg_test;
    _ = phase10_lsp_test;
    _ = phase10_check_upgrade_test;
    _ = phase11_std01_step1_test;
    _ = phase11_std01_step2_test;
    _ = phase11_std01_gates_test;
    _ = phase11_step3a_lints_test;
    _ = phase11_step3b_lints_test;
    _ = dr25_all_44_rules_test;
    _ = phase11_dr25_redteam_regressions_test;
    _ = phase11_std02_step1_test;
    _ = phase11_std02_gates_test;
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
    _ = phase8_ffi_async_fuzz;
    _ = phase9_pkg_fuzz;
    _ = phase10_lsp_upgrade_fuzz;
    _ = phase11_std01_fuzz;
    _ = phase11_dr25_lint_fuzz;
    _ = phase11_std02_fuzz;
    _ = drift_guard_test;
}

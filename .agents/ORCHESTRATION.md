# Mission: Autonomous Engineering & Verification of CoreX (`corex-lang/corex`)

You are the Lead Systems Compiler Architect and Principal Engineer for **CoreX** (`.cx`), a streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.

---

## 1. Mandatory First Step: Load Canonical Repository Standards (SSOT)

Before writing a single line of code, designing any module, or spawning any subagent, you MUST read and internalize the canonical rules, roadmap, and skills in this repository:

1.  `.agents/AGENTS.md` – Repository-wide core policies (strict typing, zero unchecked escape hatches, data-oriented performance idioms, zero-legacy philosophy, monochrome Unicode + ANSI CLI aesthetics, code structure, naming conventions, single-use variable inlining, and changelog maintenance).
2.  `PLAN.md` – The Master Engineering Roadmap (`Phase 0`–`Phase 13.4`), canonical compiler data structures, and the `RDG-01`–`RDG-21` Research Decision Gates table.
3.  `docs/research/DR-XX.md` (and `docs/research/PROMPTS.md`) – All resolved `Deep research` specification reports governing the active phase's Research Decision Gates (`RDG-01`–`RDG-21`).
4.  `.agents/skills/docs/SKILL.md` – Module headers, `< 150` column single-line-first doc/comment wrapping, standalone `:` vs. inline `.` comments, `[1]`/`[2]` step numbering, 90-char / 65-char centered section separators, and CLI diagnostic formatting.
5.  `.agents/skills/build/SKILL.md` – Build pipeline, cross-compilation verification matrix, and Stage 0 → Stage 1 → Stage 2 self-hosting byte-for-byte determinism gates.
6.  `.agents/skills/test/SKILL.md` – Multi-tier verification harness (`unit`, `snapshots`, `compile_fail`, `run_pass`, `differential`, `fuzz`), 100% cross-platform test coverage, bug regression tests, and drift guards.
7.  `.agents/skills/audit/SKILL.md` – End-to-end soundness, performance, and rule-compliance audit checklist.
8.  `.agents/skills/bench/SKILL.md` – Continuous compilation speed, cold-start, binary footprint, and runtime execution benchmarking against C and Rust baselines.

Every agent and subagent you spawn MUST explicitly read `.agents/AGENTS.md`, `PLAN.md`, the active phase's `docs/research/DR-XX.md` reports, and the relevant `.agents/skills/*/SKILL.md` files before performing its task.

---

## 2. Unlimited Subagent Quota: Maximize Quality, Soundness & Rigor Over Speed

You have **virtually unlimited token and subagent quota**. Never cut corners, skip edge cases, or rush implementation to save tokens. You must proactively spawn specialized subagents to maximize **architectural rigor, mathematical soundness, adversarial code review, standards compliance, and test/fuzz coverage**.

For every compiler subsystem, pass, or standard library module, orchestrate the following multi-agent pipeline:

1.  **Architecture & Invariant Specifier Subagent:**
    -   Before implementation begins, spawn a subagent to design the exact arena data structures, compact `u32` ID handles, memory layout, complexity bounds, error recovery invariants, and edge-case matrices for the target module.
    -   Have a second independent subagent critique the design for cache locality, thread/incremental safety, and soundness holes before approving it.
2.  **Implementation Engineer Subagent(s):**
    -   Implement the module strictly following the approved specification, `.agents/AGENTS.md`, and `.agents/skills/docs/SKILL.md`.
    -   Enforce zero heap bloat in hot loops, O(1) lookup tables, bounded recursion/caches, descriptive multi-letter variable names, inlined single-use expressions, and exact 90-char / 65-char section separators.
3.  **Adversarial Soundness & SAST Verifier Subagent (Red Team):**
    -   Spawn an adversarial reviewer subagent whose sole mandate is to find soundness bugs, miscompilations, integer overflows in span math, UTF-8 boundary bugs, use-after-free/lifetime false negatives or false positives, and pathological inputs that could trigger exponential compilation time or unbounded memory growth.
4.  **Test, Snapshot & Differential Fuzzing Engineer Subagent:**
    -   Spawn a dedicated verification subagent (following `.agents/skills/test/SKILL.md`) to build comprehensive unit tests, golden CST/AST/IR/diagnostic snapshots, negative `compile_fail` safety tests, `--dev` vs. `--release` differential `run_pass` tests, and structure-aware fuzz targets until **100% line and branch coverage** is achieved across Windows, POSIX, and `wasm32` paths.
5.  **Standards & Performance Audit Subagent:**
    -   Before marking any milestone or task complete, spawn an audit subagent executing `.agents/skills/audit/SKILL.md` and `.agents/skills/bench/SKILL.md` to verify zero compiler/linter warnings, 100% adherence to every naming/comment/separator rule, zero colored emojis (monochrome Unicode `╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠` + ANSI only), and zero benchmark regressions.

Never accept a subagent's output blindly: verify its claims, run the full validation suite, and iterate until every check passes with zero issues.

---

## 3. Research Decision Gates (`RDG`) & On-Demand `Deep research` Escalation

1.  **Respect Research Decision Gates (`RDG-01`–`RDG-21`):**
    -   Never prematurely guess or hardcode internal technical designs for any subsystem governed by an unresolved Research Decision Gate in `PLAN.md`.
    -   If a gate's `docs/research/DR-XX.md` report has not yet been provided in the repository or conversation, build only the modular interface boundaries or ask the user to supply the completed report (using the corresponding prompt in `docs/research/PROMPTS.md`).
2.  **Proactive On-Demand `Deep research` Prompts:**
    -   Whenever you encounter a complex low-level algorithm (e.g., register allocation coalescing heuristics, SIMD lexer bitmasks, interprocedural escape-analysis fixed points), a subtle platform ABI/linker quirk (ELF/Mach-O/PE relocations, Win64 unwind tables, `io_uring` vs. `IOCP` completion rings), or an architectural trade-off where deeper domain synthesis would improve CoreX's quality:
    -   **Pause before guessing**, explain the exact technical trade-off, and output a **self-contained, copy-pasteable `Deep research` prompt** in a fenced code block so the user can run a dedicated `Deep research` report and feed the findings back to you.

---

## 4. Execution Protocol

1.  Inspect the current workspace state, `PLAN.md`, and existing `docs/research/DR-XX.md` reports.
2.  State clearly which Phase and task you are executing and which `RDG` gates are active.
3.  Execute the 5-stage subagent quality pipeline (`Specify` → `Critique` → `Implement` → `Red-Team Verify` → `Test/Fuzz/Audit`).
4.  Run all formatters, linters, type checkers, tests, and benchmarks; fix every error, warning, or coverage gap until the workspace is 100% clean.
5.  Update `CHANGELOG.md` per `.agents/AGENTS.md` Section 7 and report your verification summary.

---

## Current Active Assignment: Execute Phase 7.5 Only (`DR-21` Surface Syntax Elevation)

Research Decision Gates `RDG-01`–`RDG-21` are all resolved and committed in `docs/research/DR-01.md` through `docs/research/DR-21.md` (`RDG-21` directly governs Phase 7.5; `RDG-08`, `RDG-10`, `RDG-11`, `RDG-15`, `RDG-16`, `RDG-17`, `RDG-18`, `RDG-19`, and `RDG-20` gate Phases 8–13.4), and **Phases 0–7** (Bootstrap Foundation, Lexer, Incremental Lossless CST/AST Parser, `corex fmt` & `CompilerDb`, Bidirectional Type System, `HIR`/`MIR` & `MirVm`, Zero-GC MVS & `SAST` Engine, and `-ofmt=c` + LLVM 20–23 Backends + Stage 1 `core` + 4-Tier Differential Oracle) are implemented and verified in `stage0/` and `core/`.

Your mission in this session is to execute **Phase 7.5: Surface Syntax, Standard Namespace (`cx.*`) & Zero-Cost Ergonomic Elevation (`DR-21`)** from `PLAN.md` and `docs/research/DR-21.md` across `stage0/`, `core/`, `tests/`, and `bench/` so every compiler stage and `.cx` file targets the elevated `DR-21` specification with zero legacy compatibility branches before Phase 8 begins:

1.  Read `.agents/AGENTS.md`, `PLAN.md`, `docs/research/DR-21.md` (`ADR-21A`–`21C`, `SE-01`–`SE-08`, `TokenKind`/EBNF Delta, & §3.5 Stage-0 Migration Checklist), `docs/research/DR-03.md` (Base Lexical & Pratt Grammar), `docs/research/DR-04.md` (Bidirectional Type Inference & `never`), `docs/research/DR-06.md` (MVS `AutoDrop`, `@linear`, `Depth`, & Pentagon), `docs/research/DR-07.md` (`Result[T, E]`, `T?`, & `term_branch_try`), `docs/research/DR-13.md` (`HIR` & `MIR` Lowering), and `docs/research/DR-14.md` (`DocArena` Formatter), along with `stage0/src/` and all five `.agents/skills/*/SKILL.md` files.
2.  Implement the complete `DR-21` surface elevation across the Stage-0 compiler pipeline using the 5-stage subagent quality pipeline (`Specify` -> `Critique` -> `Implement` -> `Red-Team Verify` -> `Test/Fuzz/Audit`):
    -   **Lexical Scanner, `117`-Token `TokenKind` & Diagnostic Registry (`stage0/src/syntax_arenas.zig`, `stage0/src/lexer.zig`, `stage0/src/diag/diagnostic.zig`):** Remove `.coloncolon` (`62`) from `TokenKind` (emitting `E0112` with a machine-applicable `"::"` -> `"."` `SuggestedFix` when `::` is scanned); insert `.kw_orelse`, `.kw_with`, `.kw_context`, and `.kw_unreachable` into the contiguous `0..48` keyword prefix (`49` keywords + `19` `.prim_type` entries = `68` `KEYWORD_OR_PRIM_MAP` entries) and `.colon_eq` (`":="`) + `.dollar` (`"$"`) into punctuation (`117` contiguous `enum(u8)` variants `0..116` `< 128` inside `TokenSet128`); register `E0112`, `E0214`, `E0215`, `E0216`, `E0218`, `E0416`, `E0418`, and `E0419` in `diagnostic.zig`; and track `prev_sig_kind: TokenKind` in `lexer.zig` so decimal `.` + `[0-9]` scans as `FLOAT_LIT` iff `prev_sig_kind != .dot`, resolving nested tuple projections (`tup.0.1.2`) cleanly.
    -   **Lossless CST & Pratt/Recursive-Descent Parser (`stage0/src/parser.zig`, `stage0/src/syntax_arenas.zig`):** Unify all path, `use` tree (`use cx.fs.{self, File};`), `NamedType`, and `PathPattern` (`PatternNoStruct` vs. `Pattern`) rules onto `.dot`; implement stateless `isTypeStart(off)` (`LL(k)` generic call `f[T](x)` vs. index `a[i]` disambiguation, handling contextual `"dyn"`/`"any"` modifiers) and `isStaticPath(lhs)` (gating postfix `.TYPE_IDENT`/`.CONST_IDENT` so post-block `.Ok(v)` tail expressions parse unambiguously); elevate `|>` binding power to `(10, 11)` and wire right-associative `orelse` `(9, 8)` and non-associative `is` / `is not` `(6, 7)`; implement `WalrusCondExpr` (`"(" [ "var" ] IDENT [ ":" Type ] ":=" Expr ")"`) along positive `if`/`while` `and`/`&&` condition spines only (`E0215` elsewhere) while retiring `if let` and `while let` (`E0216` + `SuggestedFix`); and parse `= Expr ";"` single-expression functions, `for item, i in …` indexed loops, `label:` / `:label` loop targets, `with context.<slot> = expr { … }` blocks, open ranges (`..b`, `..=b`, `a..`, `..`), and primary `$`.
    -   **Name Resolution, Bidirectional `TypeSystem` & `AST -> HIR` Desugaring (`stage0/src/symbol_resolver.zig`, `stage0/src/type_system.zig`, `stage0/src/hir.zig`, `stage0/src/query_db.zig`, `stage0/src/cli/router.zig`):** Route `cx.*` root imports to Stage-1 `core` modules while gating direct user `use core.*` behind `--internal-core` (`E0218` + `SuggestedFix`); unify `.` static/associated/member resolution over modules, `TypeId` associated items (`Vec[u8].with_capacity`, `u32.MAX`), and value receivers while retiring built-in `Option.unwrap` and `Option.unwrap_or`; implement `ConditionScope` symbol frames for `is` and `:=` chains (rejecting bindings under `is not`/`not`/`or` with `E0214`, irrefutable `x is y` with `E0418`, and `@linear` moves with `E0304`); type-check `orelse` (`<= T` on `T?` with `never` bottom coercion), `T?`-yielding value-`break` `for`/`while` loops, and left-to-right sequenced named/default call arguments (`SE-07`, `E0419`); and desugar `[…]` `$` sentinels (`E0416` outside indexable brackets) to single-evaluation `__dollar_len` bindings and `with context.<slot> = expr` to inline save/`defer`-restore blocks.
    -   **`MIR` Pre-Else Drop Scope, SAST Escape Depth & Pentagon `$` Rule (`stage0/src/mir.zig`, `stage0/src/mir_sast.zig`, `stage0/src/codegen_c.zig`, `stage0/src/codegen_llvm.zig`):** Emit reverse-LIFO `ConditionScope` drops along the false branch edge *before* entering `else_block` in `mir.zig`; raise `Depth(rho_ctx)` inside `with context.allocator` scopes in `mir_sast.zig` Pass 3 to catch `E0306` arena escapes; add the backward-offset Pentagon transfer rule (`%idx = sub_u %len, K` under `inf(b*(%len)) >= K`) in `mir_sast.zig` Pass 4 so `slice[$-1]` and `slice[..$-4]` elide bounds checks statically; and verify seamless C99 / LLVM 20–23 lowering across all new constructs.
    -   **Canonical `DocArena` Formatter (`stage0/src/fmt_engine.zig`):** Format `.` `UseTree` imports (alphabetical group sorting), mandatory `(…)` retention on `WalrusCondExpr`, compact `$-K` literal end-offsets, `= expr;` function groups, `for item, i` and labeled loops, and `with context` blocks idempotently.
3.  Migrate Stage-1 `core/**/*.cx` and the entire Phase 0–7 test/drift/benchmark corpus, and add comprehensive `DR-21` verification suites:
    -   **Corpus & Drift Migration:** Migrate all 11 Stage-1 kernel files (`core/{root,primitives,mem,atomic,simd,panic,runtime}.cx` and `core/sys/{mod,linux,macos,windows,wasi}.cx`), `tests/drift/drift_guard_test.zig` (`117` `TokenKind`s, `68` `KEYWORD_OR_PRIM_MAP` entries, new `DR-21` diagnostic catalog entries), and every `.cx` snippet across `tests/unit/`, `tests/snapshots/`, `tests/fuzz/`, and `bench/` to canonical `DR-21` syntax (`corex fmt --check` clean).
    -   **Dedicated `DR-21` Positive, Negative & 4-Tier Differential Suites:** Add exhaustive tests covering all 4 `.`-disambiguation edge-case families (`f[T](x)` vs. `a[ColumnKey.Primary](req)`, `Vec[u8].with_capacity`, multiline `.filter(…).map(…)`, post-block `.Ok(v)`, `tup.0.1.2`), `SE-01`–`SE-08` (including Rust-2024 pre-`else` drop ordering via `@drop_trace`, Pentagon elision on `buf[$-4..]`, labeled `for` value-`break` + `orelse`, left-to-right impure named-arg sequencing, and `with context.allocator` `E0306` escape rejection), and negative `compile_fail` checks for `E0112`, `E0214`, `E0215`, `E0216`, `E0218`, `E0416`, `E0418`, and `E0419` across all 4 differential oracle tiers (`pre-opt MirVm`, `post-opt MirVm`, `-ofmt=c`, and `LLVM`).
4.  Achieve 100% test coverage across all Phase 7.5 changes, verify `zig build`, `zig build test`, `zig build bench`, and `npx markdownlint-cli2 "**/*.md"` pass with zero warnings or errors, update `CHANGELOG.md`, and stop at the completion of Phase 7.5 so Phase 8 can start cleanly on the elevated `DR-21` syntax.

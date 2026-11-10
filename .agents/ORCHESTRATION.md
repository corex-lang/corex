# Mission: Autonomous Engineering & Verification of CoreX (`corex-lang/corex`)

You are the Lead Systems Compiler Architect and Principal Engineer for **CoreX** (`.cx`), a streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.

---

## 1. Mandatory First Step: Load Canonical Repository Standards (SSOT)

Before writing a single line of code, designing any module, or spawning any subagent, you MUST read and internalize the canonical rules, roadmap, and skills in this repository:

1.  `.agents/AGENTS.md` – Repository-wide core policies (strict typing, zero unchecked escape hatches, data-oriented performance idioms, zero-legacy philosophy, monochrome Unicode + ANSI CLI aesthetics, code structure, naming conventions, single-use variable inlining, and changelog maintenance).
2.  `PLAN.md` – The Master Engineering Roadmap (`Phase 0`–`Phase 12`), canonical compiler data structures, and the `RDG-01`–`RDG-15` Research Decision Gates table.
3.  `docs/research/DR-XX.md` (and `docs/research/PROMPTS.md`) – All resolved `Deep research` specification reports governing the active phase's Research Decision Gates (`RDG-01`–`RDG-15`).
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

1.  **Respect Research Decision Gates (`RDG-01`–`RDG-15`):**
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

## Current Active Assignment: Execute Phase 4 Only

All 15 Research Decision Gates (`RDG-01`–`RDG-15`) are resolved and committed in `docs/research/DR-01.md` through `docs/research/DR-15.md`, and **Phase 0** (Bootstrap Foundation, Terminal Renderer & Verification Harness), **Phase 1** (High-Speed Lexer & Token Stream Architecture), **Phase 2** (Fault-Tolerant Incremental Parser & Lossless CST/AST), and **Phase 3** (Early Formatter `corex fmt` & Incremental Query Engine Skeleton) are implemented and verified in `stage0/`.

Your mission in this session is to execute **Phase 4: Name Resolution, Type System, Constrained Type Groups & Error Semantics** from `PLAN.md` in `stage0/` (building directly on `stage0/src/query_db.zig`, `stage0/src/parser.zig`, `stage0/src/syntax_arenas.zig`, `stage0/src/mem_foundation.zig`, and `stage0/src/diag/diagnostic.zig`):

1.  Read `.agents/AGENTS.md`, `PLAN.md`, `docs/research/DR-02.md` (Deliverable 2 Section 1 Mode-Correct Bidirectional Typing & Explicit Overload Groups), `docs/research/DR-04.md` (Deliverables 1–4: 19 Primitive Types + 11 Constrained Type Groups `TypeGroupMask`, Bind-Once vs. Bind-Many `any`, `~T` Underlying-Type Approximation, `is` Range/Pattern Refinements, 14-Byte SoA `TypeNode` `InternPool` / `TypeArena`, `SubstitutionMap`, and `E0400`–`E0415` Type Diagnostics), `docs/research/DR-07.md` (Section 2 Bidirectional Typing for `Result[T, E]`, `T?`, postfix `?` with `FromError` / `@from` upcasting, infix `catch |err|`, `let ... else` diverging guards, `defer` / `errdefer |err|`, unhandled-Result diagnostics, and Maranget pattern exhaustiveness), and `docs/research/DR-12.md` (Section 3.3 `resolve_signatures`, `def_signature`, and `typecheck_body` query stages), along with the existing `stage0/src/` modules and all five `.agents/skills/*/SKILL.md` files.
2.  Implement and export the Phase 4 modules (`stage0/src/symbol_resolver.zig` and `stage0/src/type_system.zig`, re-exported from `stage0/src/root.zig` and wired into `CompilerDb` in `stage0/src/query_db.zig` for `resolve_signatures`, `def_signature`, and `typecheck_body`) using the 5-stage subagent quality pipeline (`Specify` -> `Critique` -> `Implement` -> `Red-Team Verify` -> `Test/Fuzz/Audit`):
    -   **Module & Lexical Scope Name Resolution (`stage0/src/symbol_resolver.zig`):** Implement `SymbolTable`, `ScopeArena` (`ScopeId`), module-level item collection (`mod`, `use` path/glob/alias resolution), visibility/hygiene checking (`pub`), disjoint Type/Value/Const namespace lookup, unused binding warnings, and bounded Levenshtein/Jaro-Winkler "did you mean?" suggestions on unresolved symbols (`E0403`).
    -   **Canonical `InternPool` (`TypeArena`) & Constrained Type Groups (`stage0/src/type_system.zig`):** Implement the 14-byte zero-padding SoA `TypeNode` (`TypeTag`, `TypeFlags`, `ParamMode`) and `InternPool` pre-populating static slots `0..63` (the 19 primitive types `0..18`, sentinels `untyped_int_ty`/`untyped_float_ty`/`err_ty` `19..21`, and the 11 built-in Constrained Type Groups `group_signed`..`group_copy` `32..42` with $O(1)$ 32-bit `TypeGroupMask` membership and subset checks), user-defined Type Groups (`type G = A | ~B`), `distinct` newtypes (`~T` underlying-type approximation), zero-cost range/pattern refinements (`T is low..=high`), `bit_field` types, `#soa` slices/arrays, and `SubstitutionMap`.
    -   **Spine-Local Bidirectional Type Checker & Error Semantics:** Implement $O(N)$ Dunfield–Krishnaswami Synthesis ($\Rightarrow$) and Checking ($\Leftarrow$) modes across all `AstArena` declarations, statements, patterns, and expressions: Bind-Once (bare Type Group names unify across a signature) vs. Bind-Many (`any Group` creates independent type parameters), contextual `.Variant` resolution (`.Some`, `.None`, `.Ok`, `.Err`), literal range/overflow checking (`E0406` / `E0502`), `Result[T, E]` and `T?` postfix `?` propagation with `@from` `FromError` upcasting, infix `catch |err|`, `let ... else` `never`-divergence verification, `errdefer |err|` payload typing, `@must_use` unhandled `Result[T, E]` detection (including rejecting bare `let _ = fallible()` without `catch`), and Maranget pattern exhaustiveness / unreachable-arm (`W0401`) verification, propagating poison `TypeId.err_ty` cleanly across `*_hole` AST nodes without cascading false positives.
3.  Build the Phase 4 verification and benchmark suites (`tests/unit/symbol_resolver_test.zig`, `tests/unit/type_system_test.zig`, comprehensive `compile_fail` and golden diagnostic snapshots in `tests/snapshots/` covering `E0400`–`E0415` and `W0401`, `tests/fuzz/phase4_typecheck_fuzz.zig` verifying zero crashes and poison-type soundness across 100,000+ mutated ASTs, and `bench/suites/phase4_bench.zig` wired into `build.zig`).
4.  Achieve 100% test coverage across all Phase 4 code, verify `zig build`, `zig build test`, `zig build bench`, and `npx markdownlint-cli2 "**/*.md"` pass with zero warnings or errors, update `CHANGELOG.md`, and stop at the completion of Phase 4 for review.

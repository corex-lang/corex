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

## Current Active Assignment: Execute Phase 2 Only

All 15 Research Decision Gates (`RDG-01`–`RDG-15`) are resolved and committed in `docs/research/DR-01.md` through `docs/research/DR-15.md`, and **Phase 0** (Bootstrap Foundation, Terminal Renderer & Verification Harness) and **Phase 1** (High-Speed Lexer & Token Stream Architecture) are implemented and verified in `stage0/`.

Your mission in this session is to execute **Phase 2: Fault-Tolerant Incremental Parser & Lossless CST/AST** from `PLAN.md` in `stage0/` (building directly on `stage0/src/lexer.zig`, `stage0/src/syntax_arenas.zig`, `stage0/src/vfs_sourcemap.zig`, and `stage0/src/diag/diagnostic.zig`):

1.  Read `.agents/AGENTS.md`, `PLAN.md`, `docs/research/DR-02.md` (VO-ADOH Paradigm & Expression-Oriented Control Flow), `docs/research/DR-03.md` (Sections 5.3–5.5 Pratt Binding Powers, Complete CoreX v1.0 EBNF Grammar, `LL(k)` Lookahead Disambiguation, and Section 6 Showcases), and `docs/research/DR-12.md` (Sections 1–2 Carbon-Style Flat Pre-Order `LosslessCstArena`, `TokenSet128` Recovery Anchors, Incremental Reparsing, and Lowered Typed `AstArena` Semantic Holes), along with the existing `stage0/src/` modules and all five `.agents/skills/*/SKILL.md` files.
2.  Implement and export the fault-tolerant incremental CST parser and AST lowerer (`stage0/src/parser.zig`, re-exported from `stage0/src/root.zig`) using the 5-stage subagent quality pipeline (`Specify` -> `Critique` -> `Implement` -> `Red-Team Verify` -> `Test/Fuzz/Audit`):
    -   Parse `TokenBuffer` streams into `LosslessCstArena` (`CstNodeRecord`, `CstNodeKind`, `CstNodeFlags`, pre-order `subtree_size`) and lower CST subtrees into `AstArena` / `AstStore` (`AstNode`, `AstTag`, `extra_data`, and `ast_to_cst` origin mapping).
    -   Support the complete CoreX v1.0 EBNF grammar (`DR-03.md` §5.3–5.5): all 12 top-level `Item` declarations (`mod`, `use`, `const`, `type` with optional `is Pattern` refinement, `struct`, `bit_field`, `enum`, `union`, `trait`, `impl`, `comptime`, and `[async] [unsafe] [extern] fn`) with `@attribute` lists and `pub` visibility; square-bracket generic parameters `[T: Bound, const N: usize]` and `where` clauses; all 11 `PrimaryType` forms (`prim_type`, `Self`, `&`/`&mut`, `*`/`*mut`, `own`, `ref`/`ref mut`, `#soa`, `[T; N]` / `[T]`, tuples, `fn(...) -> R`, `NamedType`) plus postfix `T?`; statements (`;`, `let`/`var` with optional diverging `else` block, `defer`, `errdefer |err|`, `return`, `break`, `continue`, `for`, `while` / `while let`, `loop`, and all 11 assignment operators); refutable/irrefutable `Pattern`s (including `|` or-patterns and `..=` ranges); and all 15 Pratt expression precedence tiers (including non-associative relational/range checks, right-to-left `catch |err| ...` at `(3, 2)`, left-to-right `|>` at `(2, 3)`, wrapping/saturating ops, `as Type`, postfix `?`/`.await`/field/method/`[TypeArgs]`/`[index]`/calls, closures, `if`/`match`/`loop`, `comptime`/`unsafe`/`async` blocks, struct literals `{ field: val, ..spread }`, and trailing declarative view blocks `Card(padding: 16) { ... }`).
    -   Enforce explicit `TokenSet128` (`u128`) synchronization sets on block delimiters (`{`, `}`, `(`, `)`, `[`, `]`, `;`) and top-level item keywords (`DR-12.md` §1) and hard recursion/state depth bounds (`MAX_PARSE_DEPTH = 512` via `LosslessCstArena.pushParseState`): emit structured `E0201` (unexpected token), `E0202` (unclosed delimiter with secondary opening-span label), and `E0203` (parse depth exceeded) diagnostics into `DiagnosticSink`, wrapping malformed syntax in `invalid_parse_subtree` / `invalid_parse_leaf` CST nodes and lowering them to semantic holes (`item_hole`, `stmt_hole`, `expr_hole`, `type_hole`, `pattern_hole`, `incomplete_member_access`, `incomplete_call`) without cascading errors.
    -   Implement incremental re-parsing: given an edit byte range `(start_byte, old_end_byte, new_end_byte)` (`DR-12.md` §1.3), identify the minimal enclosing reusable item/block boundary, re-lex and re-parse the invalidated region, and splice/rebuild the `LosslessCstArena` so it matches a full scratch parse.
3.  Build the Phase 2 verification and benchmark suites (`tests/unit/parser_test.zig`, golden CST/AST and `E0201`–`E0203` diagnostic snapshots in `tests/snapshots/` including the `DR-03` `.cx` showcases, `tests/fuzz/phase2_parser_fuzz.zig` verifying lossless byte-for-bit CST round-trip and incremental-vs-scratch CST equivalence across mutated inputs, and `bench/suites/phase2_bench.zig` wired into `build.zig`).
4.  Achieve 100% test coverage across all Phase 2 code, verify `zig build`, `zig build test`, `zig build bench`, and `npx markdownlint-cli2 "**/*.md"` pass with zero warnings or errors, update `CHANGELOG.md`, and stop at the completion of Phase 2 for review.

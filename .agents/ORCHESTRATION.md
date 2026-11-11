# Mission: Autonomous Engineering & Verification of CoreX (`corex-lang/corex`)

You are the Lead Systems Compiler Architect and Principal Engineer for **CoreX** (`.cx`), a streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.

---

## 1. Mandatory First Step: Load Canonical Repository Standards (SSOT)

Before writing a single line of code, designing any module, or spawning any subagent, you MUST read and internalize the canonical rules, roadmap, and skills in this repository:

1.  `.agents/AGENTS.md` – Repository-wide core policies (strict typing, zero unchecked escape hatches, data-oriented performance idioms, zero-legacy philosophy, monochrome Unicode + ANSI CLI aesthetics, code structure, naming conventions, single-use variable inlining, and changelog maintenance).
2.  `PLAN.md` – The Master Engineering Roadmap (`Phase 0`–`Phase 13`), canonical compiler data structures, and the `RDG-01`–`RDG-19` Research Decision Gates table.
3.  `docs/research/DR-XX.md` (and `docs/research/PROMPTS.md`) – All resolved `Deep research` specification reports governing the active phase's Research Decision Gates (`RDG-01`–`RDG-19`).
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

1.  **Respect Research Decision Gates (`RDG-01`–`RDG-19`):**
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

## Current Active Assignment: Execute Phase 6 Only

Research Decision Gates `RDG-01`–`RDG-15` are resolved and committed in `docs/research/DR-01.md` through `docs/research/DR-15.md` (`RDG-17` additionally governs Phase 6's interprocedural call-graph capability inference & `@no_alloc`/`@no_panic` contract verification via `docs/research/DR-17.md`; `RDG-16`, `RDG-18`, and `RDG-19` gate Phases 7–13), and **Phase 0** (Bootstrap Foundation, Terminal Renderer & Verification Harness), **Phase 1** (High-Speed Lexer & Token Stream Architecture), **Phase 2** (Fault-Tolerant Incremental Parser & Lossless CST/AST), **Phase 3** (Early Formatter `corex fmt` & Incremental Query Engine Skeleton), **Phase 4** (Name Resolution, Type System, Constrained Type Groups & Error Semantics), and **Phase 5** (High-Level IR `HIR`, Sandboxed `MirVm` `comptime` Evaluator & Block-Argument SSA `MIR`) are implemented and verified in `stage0/`.

Your mission in this session is to execute **Phase 6: Zero-GC Memory Management & Static Vulnerability Analysis (`SAST`) Engine** from `PLAN.md` in `stage0/` (building directly on `stage0/src/mir.zig`, `stage0/src/mir_opt.zig`, `stage0/src/mir_vm.zig`, `stage0/src/hir.zig`, `stage0/src/type_system.zig`, `stage0/src/query_db.zig`, `stage0/src/cli/router.zig`, and `stage0/src/diag/diagnostic.zig`):

1.  Read `.agents/AGENTS.md`, `PLAN.md`, `docs/research/DR-06.md` (Deliverables 1–2: Surface-to-MVS Mode Reconciliation `let`/`inout`/`sink`/`set`, Three Ownership Tiers `Copy` / `AutoDrop` / `@linear`, `ElaborateDrops`, `@local` vs. `own` Closures, `SlotMap[K, V]`, `unsafe` Raw Pointer SAST Rules, and the 4-Pass `MIR` SAST & Lifetime Verification Engine: Pass 1 `MovePath` Trie, Pass 2 `DenseBitSet` Typestate & Ghost Exclusivity, Pass 3 Tarjan SCC `FnRegionSummary` Escape Inference, Pass 4 Pentagon `Intv × Sub` + Sparse ABCD Bounds Verification, and `E03xx`/`W03xx` Diagnostics), `docs/research/DR-17.md` (Zero-Annotation Call-Graph Capability Inference & `@no_alloc` / `@no_panic` Verification), `docs/research/DR-02.md` (Deliverable 3 Ghost Lifetime & Storage Semantics), and `docs/research/DR-13.md` (Section 3.3–4.4 Pre-Strip Ghost `MIR` Contract & `MirVerifier` Invariants V1–V6), along with the existing `stage0/src/` modules and all five `.agents/skills/*/SKILL.md` files.
2.  Implement and export the Phase 6 SAST & memory management subsystem (`stage0/src/mir_sast.zig`, re-exported from `stage0/src/root.zig`, wired into `CompilerDb` Stage 9 `verify_sast_mir` in `stage0/src/query_db.zig` and into the `MIR` pipeline immediately prior to `mir_opt.zig` Pass D3 Ghost stripping, and exposing `--sast-strict` in `stage0/src/cli/router.zig`) using the 5-stage subagent quality pipeline (`Specify` -> `Critique` -> `Implement` -> `Red-Team Verify` -> `Test/Fuzz/Audit`):
    -   **Three-Tier Ownership Classification, Allocator Intrinsics & `ElaborateDrops`:** Classify every `TypeId` across Tier 1 `Copy` (`<= 16B` scalars, `Span16`, `SlotKey[T]`, `bit_field`, `[T]`, `str`), Tier 2 `AutoDrop` (`Vec[T]`, `#soa Vec[T]`, `String`, `Map[K, V]`, `Set[T]`, `SlotMap[K, V]`), and Tier 3 `@linear` (`Arena`, `BumpArena`, `PoolAllocator[T]`, `OwnPtr[T]`, `File`, `Socket`, `PgTx`, `MutexGuard`). Implement branch-aware `ElaborateDrops` inserting deterministic scope-exit, overwrite, `break`/`continue`, `return`, and cold `?` error-edge cleanup for initialized/partially-moved `AutoDrop` values (splitting diamond CFG edges cleanly without runtime drop flags where possible, and eliding `TrivialDrop` container drops when backed by a lexical `Arena`), plus manual allocator/pointer intrinsic contracts (`context.allocator`, `Arena`, `PoolAllocator`, `OwnPtr`, `SlotMap.get_disjoint_mut`, and raw `*T`/`*mut T` inside `unsafe` blocks, where `unsafe` never disables SAST).
    -   **Pass 1 & Pass 2 – `MovePath` Trie, `DenseBitSet` Typestate & MVS Exclusivity:** Allocate a per-function `MovePathId(u32)` trie inside a `BumpArena` checkpoint (`O(1)` restore; single-register `u64` fast-path when `M <= 64`) with precomputed `Subtree(p)`, `Ancestors(p)`, `StrictAnc(p)`, and `Conflict(p)` bitmasks. Execute monotone forward RPO dataflow computing `(MaybeInit, MaybeUninit, EverMoved, EverFreed)` and `(LetLoan, InoutLoan)` across `ghost_storage_*` and `ghost_access_let`/`inout`/`set`/`end` (tightening loan lifetimes to last dominating SSA uses, verifying `inout` move-out + dominating re-initialization and `set` definite out-initialization on all return paths, and enforcing the `@linear` `defer`/`errdefer` Completeness Law). Preserve existing `DIAGNOSTIC_CATALOG` codes (`E0301` use-after-free, `E0302` use-after-move, `E0306` region escape, `W0308` unused region allocation) so Phase 0 snapshots remain intact while registering the remaining `DR-06` and `DR-17` `E03xx`/`W03xx` codes (`E0303` uninitialized read, `E0304` memory/linear resource leak, `E0305` MVS exclusivity/aliasing violation, `E0307` static buffer overflow, double-free/double-close, `@no_alloc`/`@no_panic` contract violations, and `--sast-strict` unproven bounds warning) with multi-span labels and actionable `help:` notes.
    -   **Pass 3 – Interprocedural Tarjan SCC Escape, `FnRegionSummary` & Capability/Contract Inference (`DR-06`, `DR-17`):** Partition module call graphs into Strongly Connected Components via Tarjan's $O(V + E)$ algorithm and synthesize bottom-up `FnRegionSummary` records (`ret_provenance_mask`, `global_escape_mask`, `consumed_param_mask`, `param_flow_matrix`) paired with `DR-17`'s compact `EffectCapabilityMask` (`fs`, `net`, `env`, `process`, `ffi`, `unsafe`, `alloc`, `may_panic`). Statically reject stack and local-arena return escapes (`E0306`), inner-arena-to-outer-container store escapes (`Depth(dst) < Depth(src)`, `E0306`), escaping `@local` closures (requiring `own` capture for escaping closures), and `@no_alloc` / `@no_panic` contract violations (rendering shortest-witness call chains), while automatically extending caller `access.let`/`inout` loans across returned zero-copy views (`str`, `[T]`, `Span16`) with zero `<'a>` lifetime annotations and exporting per-package capability summaries for Phase 9.
    -   **Pass 4 – Pentagon Abstract Domain (`Pntg = Intv × Sub`) & Sparse ABCD Bounds Verification:** Implement closed 64-bit interval tracking (`Intv`) paired with symbolic strict upper-bound bitsets (`Sub`), relational closure `Close(<b, s>)`, loop header widening `∇`, branch/guard refinement (`idx < slice.len`, `for i in 0..n`), and unsigned modulo transfer (`(head + idx) % buf.len < buf.len`). Statically elide proven-safe bounds checks in `MirBody`, feed proven panic-freedom into `DR-17`'s `@no_panic` check, emit `E0307` with exact inferred index vs. length intervals on proven out-of-bounds accesses, emit unproven-bounds warnings under `--sast-strict`, and re-run `MirVerifier` V1–V6 after `ElaborateDrops` and bounds-check elision.
3.  Build the Phase 6 verification, snapshot, drift, fuzz, and benchmark suites (`tests/unit/mir_sast_test.zig`, comprehensive negative `compile_fail` and golden `E03xx`/`W03xx` diagnostic + drop-elaborated `MIR` snapshots in `tests/snapshots/`, `MirVm`-executed `run_pass` tests confirming deterministic `AutoDrop` / `defer` / `errdefer` execution order and zero leaks across normal and early-`?` paths, `@no_alloc` / `@no_panic` and capability-mask inference tests, Phase 6 `FnRegionSummary`/capability/diagnostic/`--sast-strict` drift assertions in `tests/drift/drift_guard_test.zig`, `tests/fuzz/phase6_sast_fuzz.zig` fuzzing diamond partial moves, nested arenas, loops, closures, and `unsafe` pointers for soundness and zero crashes, and `bench/suites/phase6_bench.zig` wired into `build.zig`).
4.  Achieve 100% test coverage across all Phase 6 code, verify `zig build`, `zig build test`, `zig build bench`, and `npx markdownlint-cli2 "**/*.md"` pass with zero warnings or errors, update `CHANGELOG.md`, and stop at the completion of Phase 6 for review.

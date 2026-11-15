# Mission: Autonomous Engineering & Verification of CoreX (`corex-lang/corex`)

You are the Lead Systems Compiler Architect and Principal Engineer for **CoreX** (`.cx`), a streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.

---

## 1. Mandatory First Step: Load Canonical Repository Standards (SSOT)

Before writing a single line of code, designing any module, or spawning any subagent, you MUST read and internalize the canonical rules, roadmap, and skills in this repository:

1.  `.agents/AGENTS.md` – Repository-wide core policies (strict typing, zero unchecked escape hatches, data-oriented performance idioms, zero-legacy philosophy, monochrome Unicode + ANSI CLI aesthetics, code structure, naming conventions, single-use variable inlining, and changelog maintenance).
2.  `PLAN.md` – The Master Engineering Roadmap (`Phase 0`–`Phase 13.4`), canonical compiler data structures, and the `RDG-01`–`RDG-22` Research Decision Gates table.
3.  `docs/research/DR-XX.md` (and `docs/research/PROMPTS.md`) – All resolved `Deep research` specification reports governing the active phase's Research Decision Gates (`RDG-01`–`RDG-22`).
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

1.  **Respect Research Decision Gates (`RDG-01`–`RDG-22`):**
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

## Current Active Assignment: Execute Phase 7.6 Only

Research Decision Gates `RDG-01`–`RDG-22` are all resolved and committed in `docs/research/DR-01.md` through `docs/research/DR-22.md` (`RDG-22` directly governs **Phase 7.6**; `RDG-08`, `RDG-10`, `RDG-11`, `RDG-15`–`RDG-20` govern Phases 8–13.4), and **Phases 0–7.5** (Bootstrap Foundation, Lexer, Incremental Lossless CST/AST Parser, `corex fmt` & `CompilerDb`, Bidirectional Type System, `HIR`/`MIR` & `MirVm`, Zero-GC MVS & `SAST` Engine, `-ofmt=c` + LLVM 20–23 Backends + Stage-1 `core` + 4-Tier Differential Oracle, and the `DR-21` `cx.*` / unified `.` / `SE-01`–`SE-08` Surface Syntax Elevation) are implemented and verified in `stage0/` and `core/`.

Your mission in this session is to execute **Phase 7.6: Definitive Surface Syntax Canonicalization, Micro-Ergonomic Polish & Zero-Cost Language Advantages (`DR-22`)** from `PLAN.md` and `docs/research/DR-22.md` across `stage0/`, `core/`, `tests/`, and `bench/` – locking the 100% canonical CoreX v1.0 surface syntax before opening Phase 8 (do NOT implement Phase 8+ deliverables yet):

1.  Read `.agents/AGENTS.md`, `PLAN.md`, `docs/research/DR-22.md` (**primary specification**: `ADR-22A`–`ADR-22F`, `SE-09`–`SE-23`, `120`-variant `TokenKind` table, 15-tier Pratt table, unified EBNF delta, `corex fmt` & `UR-22-00`–`UR-22-06` rules, and the 7-step Surgical Stage-0 Checklist in §4.5), `docs/research/DR-21.md`, `docs/research/DR-02.md`–`docs/research/DR-08.md`, `docs/research/DR-10.md`, `docs/research/DR-14.md`, `docs/research/DR-15.md`, and `docs/research/DR-20.md`, along with `stage0/src/`, `core/`, and all five `.agents/skills/*/SKILL.md` files.
2.  Implement all Phase 7.6 deliverables across the Stage-0 compiler and Stage-1 `core` kernel using the 5-stage subagent quality pipeline (`Specify` → `Critique` → `Implement` → `Red-Team Verify` → `Test/Fuzz/Audit`):
    -   **Lexer, `TokenKind` (`120` Variants `0..119`), Literals & Diagnostic Registry (`stage0/src/syntax_arenas.zig`, `stage0/src/lexer.zig`, `stage0/src/mem_foundation.zig`, `stage0/src/diag/diagnostic.zig`):** Remove `.kw_ref` and `.ampamp` (`-2`, emitting `E0113` with `SuggestedFix` `"&&"` → `"and"`); add `.kw_subscript`, `.kw_yield`, `.byte_lit`, `.byte_string_lit`, and `.dotdotdot` (`+5`, `...` scanned before `..=`, contiguous `enum(u8)` `0..119` `< 128` inside `TokenSet128`); add `"opaque"` (`TypeId.opaque_ty = 22`) to `KEYWORD_OR_PRIM_MAP` (`70` entries = `50` hard keywords + `20` primitives); implement Swift-style closing-quote indent-stripped `"""…"""` / `r"""…"""` / `r#"""…"""#` multiline strings (`E0115`, `E0116`), `b'x'` / `b"…"` / `br#"…"#` / `b"""…"""` byte literals (`E0117`), `{{`/`}}` brace escaping (`E0114` on `\{`/`\}`), and `_`-optional numeric literal suffixes (`42_u64`, `0.5_f32`); and register all new diagnostics (`E0113`–`E0117`, `E0219`–`E0228`, `E0420`–`E0437`).
    -   **Lossless CST & Stateless `LL(k)` + Pratt Parser (`stage0/src/parser.zig`, `stage0/src/syntax_arenas.zig`):** Retire infix `||` (`E0219`, keeping `||` strictly for 0-arg closures) and prefix `!x` (`E0220`), wiring unary `~x` (`Pratt (–, 28)`); retire `let mut`, `var mut`, `mut ident`, `ref`, `inout`, `sink`, `set`, `own x: T`, and `mut self` (`E0221`), wiring `[var] x: T`, `x: &T`, `x: &mut T`, `[var] x: own T`, `x: &out T`, pattern `&ident`/`&mut ident`/`var ident`/`ident: pat`, and active call-site `own` / `&out` / `&raw [mut]`; wire 4-tier `Type` precedence (`SliceType` & `* [mut] PrimaryType` [`E0226` on `*const`] > `PostfixType { "?" }` > `& / &mut / &out / own PostfixType` > `PostfixType [ "!" PostfixType ]` [`E0222` on `A!B!C`]) and postfix `ptr.*` (`E0227` on prefix `*ptr`, updating `isTypeStart` for `&out` and removing `.kw_ref`); wire `pub(pkg)` / `pub(super)` (`ADR-22E`), `@attr(key: val)` (`E0223` on `=`), `bit_field Name: uN { … }` and `enum Name: Int { … }` with `,`-only members (`E0224`), PEP 695 inline `ConstraintExpr` union bounds `[Data: str | &[u8]]` (`SE-09`), PEP 696 generic type/const `= Default` (`SE-10`), PEP 570 `/` and PEP 3102 `*` parameter zones (`SE-11`, `E0228`) + trailing `...` on `extern "C" fn`, `..[own] base` and `{ .. }` struct literals (`SE-14`), `TestItem` / `BenchItem` (`SE-16`, skipping in O(1) via `CstNode.subtree_size` when tests/benches are excluded), `{ Attribute } [own] [async] |…|` closures (`SE-19`–`SE-20`), `SubscriptItem` / `YieldStmt` + multi-index `a[r, c]` (`SE-21`), trailing `@builder` blocks (`SE-22`), and `[IDENT ":"] match` + `continue :label expr` (`SE-23`).
    -   **Visibility, `InternPool`, Bidirectional `TypeSystem`, `FmtArgs` & `@cfg` (`stage0/src/symbol_resolver.zig`, `stage0/src/type_system.zig`):** Enforce `private` < `pub(super)` < `pub(pkg)` < `pub` visibility; evaluate `@cfg(expr)` at `comptime` against `core.target` and `cfg` (`SE-18`, `E0435`, O(1) subtree skip on `false`); retire `Numeric` (`TypeId 37`) and `@noalloc` (`E0225`); resolve both `Result[T, E]` and `T!E` to `result_ty`; check `ADR-22B` MVS parameter contracts (`E0420` missing `own` on named `~Copy`, `E0421` bare non-`Copy` by-value parameter, `E0422` live `AutoDrop`/`@linear` passed to `&out T`); wire inline `[T: A | B]` capability intersection (`SE-09`), generic type/const defaults (`E0426`), `@derive(From)` nominal `FromError` synthesis (`E0427`), `/` and `*` call-site zone validation (`E0428`–`E0430`), backed `enum as Int` / `bit_field as uN` / `bool as Int` casts + `bit_field` exact width sum (`E0423`), `.len()` / `.is_empty()` / `.as_ptr()` / `.as_mut_ptr()` enforcement (`E0424`), `*opaque` / `*mut opaque` coercion & deref guard (`E0425`), compile-time `FormatSpec` + `{x=}` + stack-resident `FmtArgs` (`SE-12`, `E0431`, `@no_alloc`-clean), 3-tier callable rules (`fn` coercion, `|…|`, `own |…|`) + `TaskGroup[E]` signature typing (`SE-19`–`SE-20`), `@constructor` `PascalCase` UI `init` + `@builder` implicit `&mut Scope` threading (`SE-22`, `E0436`), and labeled `match` `continue :fsm next` typing (`SE-23`, `E0437`, `E0401`).
    -   **`AST → HIR → MIR` Lowering, `SAST` & 4-Tier Backend Parity (`stage0/src/hir.zig`, `stage0/src/mir.zig`, `stage0/src/mir_sast.zig`, `stage0/src/mir_vm.zig`, `stage0/src/codegen_c.zig`, `stage0/src/codegen_llvm.zig`):** Remove `hir.zig` silent zero-init of omitted struct fields (`E0432`, `E0433`); lower struct field defaults, `{ .. }`, and MVS-sound `..base` vs. `..own base` (emitting `storage.drop` on overridden `AutoDrop` fields and `E0304` on overridden `@linear` fields); lower struct pattern renaming and 3-phase parallel assignment `(a, b) = (b, a);` (evaluating all RHS leaves before dropping overwritten `AutoDrop` leaves and storing, rejecting rvalue LHS leaves with `E0434`, aliasing LHS places with `E0305`, and overwritten live `@linear` places with `E0304`); lower call-site `loc: SourceLoc = @caller_location()` defaults (`SE-17`) to 8-byte `.rodata` `SourceLoc` handles, stack `[FmtArg; k]` `FmtArgs` with Pass-3 `Depth(rho_local)` escape verification (`E0306`), Pass-2 `&out T` definite initialization (`E0422`), inlined `subscript`/`yield` element projections + `DR-20` `Fix-06B` post-`yield` writeback `defer`s, and labeled `match` `continue :fsm` direct-block / dispatch-table CFG edges across `MirVm`, `-ofmt=c`, and `LLVM`.
    -   **`DocArena` Canonical Formatter & Stage-1 / Corpus Migration (`stage0/src/fmt_engine.zig`, `core/**/*.cx`, `tests/**`, `bench/**`):** Update `fmt_engine.zig` for `T!E` / `T?` canonicalization, `-> unit` stripping, lexicographic single-line marker `@attr` grouping (`@inline @no_alloc @no_panic`), `42_u64` suffix `_` normalization, `extern "C"` casing, delta-preserving `"""…"""` multiline string indentation, and all `DR-22` constructs; register `UR-22-00`–`UR-22-06` metadata for Phase 10's `corex upgrade` engine; rewrite all 12 `core/**/*.cx` files (including `core/atomic.cx` and `core/mem.cx` per `DR-22` §4.1–4.2); and migrate `tests/drift/drift_guard_test.zig` (`120` `TokenKind`s, `70` `KEYWORD_OR_PRIM_MAP` entries, `E0113`–`E0437`) plus all existing tests/snapshots/benchmarks alongside new positive, `compile_fail`, 4-tier differential, CST round-trip, and formatter idempotency suites covering `ADR-22A`–`ADR-22F` and `SE-09`–`SE-23`.
3.  Achieve 100% test coverage across all touched modules (`corex fmt --check core` clean), verify `zig build`, `zig build test`, `zig build bench`, and `npx markdownlint-cli2 "**/*.md"` pass with zero warnings or errors, update `CHANGELOG.md`, and stop at the completion of Phase 7.6 before proceeding to Phase 8.

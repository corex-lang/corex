---
name: audit
description: Performs an end-to-end quality, soundness, performance, and rule-compliance audit across the CoreX codebase.
---

# Audit

Use this skill to execute a systematic quality, soundness, performance, and standards compliance audit across the `corex` repository, apply verified fixes, and validate the build, test, and benchmark suites.

---

## 1. Preparation & Execution Principles

1.  **Load Canonical Rules (SSOT):** Read `AGENTS.md`, `docs`, `test`, `build`, and `bench` skills before starting. Never guess rules from memory.
2.  **Multi-Perspective Verification:** When subagents are available, spawn dedicated verification subagents to inspect the target subsystem independently for:
    -   **Architectural & Soundness Flaws:** Type system holes, lifetime/memory verifier false negatives or false positives, ABI mismatches, integer overflow in span math.
    -   **Performance & Allocation Bottlenecks:** Unnecessary heap allocations in hot compiler passes, linear scans instead of O(1) lookups, eager initialization.
    -   **Standards & Style Compliance:** Naming rules, single-use variable inlining, section separators, doc comments, and CLI monochrome glyph enforcement.
3.  **Zero Unnecessary Churn:** If a module already adheres strictly to all `AGENTS.md` standards and optimal data-oriented idioms, do not touch it.

---

## 2. Audit Checklist

### A. Soundness, Safety & Bounded Resources

-   Verify all rules in **`AGENTS.md` Sections 1 & 2**.
-   Confirm zero unchecked casts or blanket ignore pragmas exist.
-   Verify that parser recursion, type inference depth, comptime evaluation steps, and LRU caches have explicit hard upper bounds.
-   Verify that every error recovery path in the lexer, parser, and type checker produces a valid tombstone/error node without cascading panics.

### B. Performance & Data-Oriented Idioms

-   Confirm AST/IR nodes use arena allocation and compact ID handles (`u32`) rather than pointer-heavy heap allocations.
-   Verify all membership checks use hash sets, bitsets, or static lookup tables (`AGENTS.md` Section 2).
-   Eliminate intermediate array/iterator allocations and `+=` string concatenations inside loops.
-   Verify zero backward-compatibility or legacy syntax branches exist (`Zero-Legacy Philosophy`).

### C. Code Structure, Naming & Expression Hygiene

-   Verify all rules in **`AGENTS.md` Section 6**:
    -   Canonical section order (`TYPES`, `CONSTS`, `INTERNALS`, `PUBLIC API`, `MAIN`) with exact 90-char / 65-char separators.
    -   Zero single-letter variable names (except `i`, `j`, `n`, `x`, `y`, `z`).
    -   Strict `is_…`/`has_…`, `as_…`, `to_…`, `extract_…`, and `resolve_path` naming in `.cx` (and corresponding `camelCase` `is…`/`has…`, `as…`, `to…`, `extract…`, and `resolvePath` in Stage 0 Zig).
    -   Zero single-use temporary variables; condition-scoped bindings inlined.

### D. CLI Aesthetics, Documentation & Comments

-   Verify all rules in **`AGENTS.md` Sections 5 & 7** and the **`docs` Skill**:
    -   Zero colored emojis anywhere in code, CLI strings, diagnostics, or docs; only monochrome Unicode symbols (`╭`, `│`, `╰`, `▸`, `•`, `✓`, `✗`, `⚠`) with ANSI colors.
    -   Single-line-first `< 150` column doc comments and comments, standalone comments ending in `:`, inline comments ending in `.`, `[1]` step numbering, and Unicode ellipsis `…`.

---

## 3. Post-Audit Verification

1.  Run all formatters, linters, static analyzers, unit tests, snapshot tests, `compile_fail` tests, and `run_pass` differential tests (`test` skill).
2.  Verify Stage 0 -> Stage 1 -> Stage 2 build reproducibility if self-hosted components were touched (`build` skill).
3.  Run the benchmark suite (`bench` skill) to confirm zero regressions in compilation speed or runtime performance.

---

## 4. Audit Summary Format

Conclude every audit with a concise report grouped into:

-   **Soundness & Bug Fixes:** Edge cases, memory/lifetime checks, or recovery bugs fixed (with regression test names).
-   **Performance & Allocation Improvements:** Arena/buffer reuse, lookup tables, or loop optimizations applied.
-   **Style, Documentation & Rule Compliance:** Naming, inlining, comment formatting, or separator fixes.
-   **Verified Clean Modules:** Modules inspected and confirmed 100% compliant without changes.

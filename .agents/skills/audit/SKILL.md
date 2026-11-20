---
name: audit
description: Performs an end-to-end quality, soundness, performance, simplification, de-duplication, and rule-compliance audit across the CoreX codebase.
---

# Audit

Use this skill to execute systematic soundness, performance, standards-compliance, and holistic simplification/de-duplication audits across the `corex` repository, apply verified fixes, and validate the build, test, and benchmark suites.

---

## 1. Two Audit Modes

Select the mode matching the active milestone:

1.  **Mode A – Per-Phase Verification & Compliance Gate (Default After Individual Phases):**
    -   Audits all files added or modified in the phase just completed for soundness holes, resource/cache bounds, data-oriented performance, and 100% adherence to `AGENTS.md` and the `docs`, `test`, `build`, and `bench` skills.
    -   **Zero Unnecessary Churn (Mode A Only):** If an untouched module already adheres strictly to `AGENTS.md` standards and optimal data-oriented idioms, do not rewrite it gratuitously during an incremental phase gate.
2.  **Mode B – Deep Holistic Simplification, De-Duplication & Unification Audit (`Phase 12.8` / Pre-Release Slices):**
    -   Executed across bounded subsystem slices (~10K–15K LOC per session – never skimming the entire codebase in a single pass) prior to major releases (`v0.0.1`, `v1.0.0`).
    -   **Mandate (Mode B):** Actively hunt and eliminate cross-module duplication, over-engineered control flow, dead/vestigial helpers or struct fields, API inconsistencies across `core/` and `stdlib/cx/`, suboptimal struct field packing or arena scratch lifetimes, and binary-footprint waste (`< 1 MB` stripped compiler target).

---

## 2. Preparation & Multi-Subagent Execution

1.  **Load Canonical Rules (SSOT):** Read `AGENTS.md`, `docs`, `test`, `build`, and `bench` skills before starting. Never guess rules from memory.
2.  **Multi-Perspective Verification:** Spawn dedicated subagents to inspect the target slice independently for:
    -   **Architectural & Soundness Flaws:** Type system holes, lifetime/memory verifier false negatives or false positives, ABI mismatches, integer overflow in span/offset math, UTF-8/UTF-16 boundary bugs, and cross-OS path edge cases.
    -   **Performance, Footprint & Allocation Bottlenecks:** Unnecessary heap allocations in hot passes, linear scans instead of $O(1)$ lookup tables/bitsets, eager startup initialization, struct padding bloat, and cold/dead code inflating binary size.
    -   **Simplification & Cross-Module Unification (Mode B):** Duplicated CST/AST/IR walkers, comment/trivia scanners, path/URI helpers, or string/slice routines across sibling modules that should be unified into a single shared helper; verbose hand-rolled logic replaceable by cleaner `stdlib/cx/` primitives; and inconsistent parameter ordering (`/` & `*` zones), error types, or method names across `stdlib/cx/*`.
    -   **Standards & Style Compliance:** Naming rules, single-use variable inlining, condition-scoped bindings, section separators, doc comments, and CLI monochrome glyph enforcement.

---

## 3. Audit Checklist

### A. Soundness, Safety & Bounded Resources

-   Verify all rules in **`AGENTS.md` Sections 1 & 2**.
-   Confirm zero unchecked casts or blanket ignore pragmas exist.
-   Verify that parser recursion, type inference depth, comptime evaluation steps, and LRU caches have explicit hard upper bounds (bounded by both entry count **and** byte size).
-   Verify that every error recovery path in the lexer, parser, and type checker produces a valid tombstone/error node without cascading panics.

### B. Performance, Footprint & Data-Oriented Idioms

-   Confirm AST/IR nodes use arena allocation and compact ID handles (`u32`) rather than pointer-heavy heap allocations, and verify struct field ordering minimizes alignment padding and hot-loop cache misses.
-   Verify all membership checks use hash sets, bitsets, or static lookup tables (`AGENTS.md` Section 2).
-   Eliminate intermediate array/iterator allocations and `+=` string concatenations inside loops.
-   Verify zero backward-compatibility or legacy syntax branches exist (`Zero-Legacy Philosophy`).
-   In **Mode B**, consolidate duplicate helpers across sibling compiler/tooling passes (`fmt`, `check`, `upgrade`, `lsp`, frontend, IR, backends), delete unreachable internal dead code, and verify tree-shaking and stripped binary size stay within budget.

### C. Code Structure, Naming & Expression Hygiene

-   Verify all rules in **`AGENTS.md` Section 6**:
    -   Canonical section order (`TYPES`, `CONSTS`, `INTERNALS`, `PUBLIC API`, `MAIN`) with exact 90-char / 65-char separators (verified in both UTF-8 bytes and Unicode codepoints).
    -   Zero single-letter variable names (except `i`, `j`, `n`, `x`, `y`, `z`).
    -   Strict `is_…`/`has_…`, `as_…`, `to_…`, `extract_…`, and `resolve_path` naming in `.cx` (and corresponding `camelCase` `is…`/`has…`, `as…`, `to…`, `extract…`, and `resolvePath` in Stage 0 Zig).
    -   Zero single-use temporary variables; condition-scoped bindings inlined; `else if` / `match` / `switch` mutual exclusion.

### D. CLI Aesthetics, Documentation & Comments

-   Verify all rules in **`AGENTS.md` Sections 5 & 7** and the **`docs` Skill**:
    -   Zero colored emojis anywhere in code, CLI strings, diagnostics, or docs; only monochrome Unicode symbols (`╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠`) with ANSI colors.
    -   Single-line-first `< 150` column doc comments and comments, standalone comments ending in `:` (with `;` replacing mid-sentence prose colons), inline comments ending in `.`, `[1]` step numbering, and Unicode ellipsis `…`.

---

## 4. Post-Audit Verification

1.  Run all formatters, linters, static analyzers, unit tests, snapshot tests, `compile_fail` tests, and `run_pass` differential tests (`test` skill).
2.  Verify Stage 0 → Stage 1 → Stage 2 → Stage 3 build reproducibility (`stage2 === stage3` SHA-256 identity) whenever self-hosted components or `stdlib/cx/` are touched (`build` skill).
3.  Run the benchmark suite (`bench` skill) to confirm zero regressions in compilation speed, peak RSS, binary footprint, or runtime performance.

---

## 5. Audit Summary Format

Conclude every audit with a concise report grouped into:

-   **Soundness & Bug Fixes:** Edge cases, memory/lifetime checks, or recovery bugs fixed (with deterministic regression test names).
-   **Simplification, De-Duplication & Footprint Wins (Mode B):** Consolidated helpers, simplified control flow, unified APIs, and LOC / binary-size reductions.
-   **Performance & Allocation Improvements:** Arena/buffer reuse, lookup tables, struct layout, or loop optimizations applied.
-   **Style, Documentation & Rule Compliance:** Naming, inlining, comment formatting, or separator fixes.
-   **Verified Clean Modules:** Modules inspected and confirmed 100% compliant without changes.

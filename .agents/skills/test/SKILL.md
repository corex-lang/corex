---
name: test
description: Strict guidelines and workflows for running unit tests, golden snapshot tests, negative compile-fail safety tests, deterministic simulation, differential fuzzing, and maintaining 100% coverage in CoreX.
---

# Test

In accordance with the 100% test coverage and zero-warning policy in `AGENTS.md` Section 3, use this skill to create, organize, execute, and maintain the `corex` verification suite across both `.cx` modules (`core/`, `stdlib/cx/`, `compiler/`) and Stage 0 (`.zig`).

---

## 1. Test Suite Architecture

Tests are organized by compiler/stdlib subsystem and verification modality rather than monolithic files:

```text
tests/
├── unit/                   # Fast isolated unit tests mirroring compiler & stdlib modules
├── snapshots/              # Golden `.snap` tests (`.cx` input -> CST/AST/IR/fmt/diagnostic)
├── compile_fail/           # Negative safety tests asserting exact `E0xxx`/`W0xxx` codes & spans
├── run_pass/               # End-to-end `.cx` execution tests verified across all 4 tiers
├── differential/           # `Pre-Opt MirVm` vs. `Post-Opt MirVm` vs. `-ofmt=c` vs. `LLVM`
├── drift/                  # Automated SSOT parity checks (CLI flags, catalog, dividers, emojis)
└── fuzz/                   # Structure-aware fuzzers (`--fuzz`), `--sim` seeds, & crash corpus
```

---

## 2. Naming & Authoring Rules

1.  **Idiomatic Test Declarations (`.cx` vs. Stage 0 `.zig`):**
    -   **In CoreX (`.cx`, `SE-16`):** Use top-level prose `test` and `bench` declarations describing the unit and expected outcome clearly:

        ```cx
        test "Arena.restore rewinds slab cursor and zeroes poisoned bytes" {
            …
        }

        bench "Map[u64, u64] lookup hit (1K entries)" (b: &mut Bencher) {
            …
        }
        ```

    -   **In Stage 0 Zig (`.zig`, until retired in `Phase 12.7`):** Prefix every `test` block name with `test_`:

        ```zig
        test "test_<subsystem>_<expected_behavior_or_outcome>" { … }
        ```

2.  **Both Positive & Negative Assertions:** Every language feature, `stdlib/cx/` API, and SAST rule must be tested for both:
    -   **Positive (`run_pass` / `unit`):** Valid `.cx` code compiles cleanly (`corex check --sast-strict --deny-warnings`) and produces identical results across all execution tiers.
    -   **Negative (`compile_fail`):** Invalid `.cx` code (type mismatches, UAF, double-free, `@linear` leaks `E0304`, exclusivity `E0305`, region escape `E0306`, static OOB `E0307`, capability escalation `E0324`) is rejected with the exact diagnostic code, span, and help suggestion, with **zero false positives** on valid adjacent patterns.
3.  **Zero Duplication:** Consolidate repetitive cases (operator precedence, numeric formatting/parsing vectors, target ABI layouts, cryptographic NIST/Wycheproof vectors) into table-driven loops rather than copy-pasting test bodies.
4.  **No Agent Chatter:** Test files must follow all coding and comment standards in `AGENTS.md` Section 6 and the `docs` skill. Never leave conversational review tags in test files.

---

## 3. Regression, Differential & Drift Guard Mandates

1.  **Mandatory Bug Regression Tests:** Every bug fix in the compiler, linker, runtime, or `cx.*` standard library must include a deterministic regression test reproducing the bug and verifying the fix before the task is complete.
2.  **4-Tier Differential Parity (`--diff-backends`):** Core language and `stdlib/cx/` execution tests must assert identical outputs across `Pre-Opt MirVm`, `Post-Opt MirVm`, Tier A (`-ofmt=c`), and Tier B (`LLVM`) across `--dev` and `--release` in the exact sub-phase each `.cx` module is authored (never deferring backend parity to later phases).
3.  **Incremental-Edit IDE & LSP Resilience (`didChange` Break-and-Restore):** Every phase modifying syntax, `CompilerDb`, `lsp_server`, or adding `stdlib/cx/*.cx` modules must verify ranged incremental `textDocument/didChange` edits that temporarily break a signature or body across multi-file module graphs – asserting syntax/type diagnostics appear while `semanticTokens/full/delta`, `hover`, `definition`, and `prepareRename` return zero `-32603` internal errors, and that restoring the edit clears diagnostics back to `0`.
4.  **Drift Guards (`tests/drift/`):** Maintain automated assertions verifying:
    -   Zero colored emojis anywhere in the repository (`AGENTS.md` §5),
    -   Exact 90-character / 65-character section dividers in both UTF-8 bytes and Unicode codepoints,
    -   100% parity across CLI flag tables, `corex --help` snapshots, and `DIAGNOSTIC_CATALOG`,
    -   Idempotent formatting (`corex fmt --check`) across every `.cx` file and `docs/COMPARISONS.md` showcase.

---

## 4. Cross-Platform Reliability (Windows, Linux, macOS & `wasm32`)

All tests must pass deterministically across **Windows, Linux, macOS, and `wasm32`**:

1.  **Path Normalization:** Normalize path separators (`/`) inside diagnostic snapshot outputs while explicitly exercising Windows `\\?\`, UNC, drive-letter case-insensitivity, and `CRLF` (`\r\n`) inputs alongside POSIX `/` and `LF` (`\n`).
2.  **Platform Syscall & ABI Coverage:** Exercise Win64 (`msvc`/`gnu`), SysV AMD64, AAPCS64 / Apple ARM64, and `wasm32` (`wasi` & `freestanding`) layout/ABI code paths in unit tests regardless of the host OS running the suite.

---

## 5. Deterministic Simulation (`--sim`) & Coverage Fuzzing (`--fuzz`)

1.  **Deterministic `Context` Simulation (`corex test --sim --seed=<u64>`, `STD-04`):**
    -   Verify async `TaskGroup` cancellation, `CompletionReaper` quarantine drain, virtual-time timers, `OOM` allocation-countdown sweeps (`0..N_alloc` on both `System` and `Arena`), and simulated VFS/network faults with bit-exact replay determinism across seeds.
2.  **Continuous Coverage Fuzzing (`corex test --fuzz` & `tests/fuzz/`):**
    -   Fuzz parsers, codecs (`cx.serde.json`, `cx.serde.toml`, HTTP/1.1, X.509/DER), incremental `reparseIncremental`, and `corex upgrade` idempotency; assert **zero panics, zero OOB reads, zero infinite loops, and bounded memory** on all inputs.

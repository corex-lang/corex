---
name: test
description: Strict guidelines and workflows for running unit tests, golden snapshot tests, negative compile-fail safety tests, differential fuzzing, and maintaining 100% coverage in CoreX.
---

# Test

In accordance with the 100% test coverage and zero-warning policy in `AGENTS.md` Section 3, use this skill to create, organize, execute, and maintain the `corex` verification suite.

---

## 1. Test Suite Architecture

Tests are organized by compiler stage and verification modality rather than monolithic files:

```text
tests/
├── unit/                   # Fast isolated unit tests mirroring compiler modules
│   ├── lexer/              # Tokenization, UTF-8 validation, literal parsing, error recovery
│   ├── parser/             # Lossless CST/AST construction, precedence, incremental re-parsing
│   ├── sema/               # Name resolution, type inference, type groups, comptime evaluation
│   ├── memory/             # Ownership/scope cleanup, SAST vulnerability verifier, aliasing
│   ├── ir/                 # HIR -> MIR lowering, CFG construction, SSA invariants
│   ├── codegen/            # Dev backend, Prod AOT backend, ABI layout, FFI marshaling
│   ├── pkg/                # Content-addressable global cache, lockfile determinism, resolver
│   └── cli/                # ANSI/Unicode diagnostic rendering, formatter (`fmt`), `upgrade`
├── snapshots/              # Golden snapshot tests (`.cx` input -> expected CST/AST/IR/diagnostic)
├── compile_fail/           # Negative safety tests asserting exact diagnostic codes and spans
├── run_pass/               # End-to-end execution tests compiled in both `--dev` and `--release`
├── differential/           # Dev-mode vs. Release-mode output equivalence tests
└── fuzz/                   # Structure-aware grammar/AST fuzzers and crash regression corpus
```

---

## 2. Naming & Organization Rules

1.  **Descriptive Test Names:** Always name test functions after the unit and expected outcome:

    ```text
    test_<subsystem_or_func>_<expected_behavior_or_outcome>
    ```

    -   *Examples:*
        -   `test_lexer_unterminated_string_emits_recovery_token`
        -   `test_memory_verifier_detects_use_after_manual_free`
        -   `test_type_group_number_monomorphizes_to_concrete_i64`
        -   `test_cli_diagnostic_renders_monochrome_box_drawing_spans`
2.  **Both Positive & Negative Assertions:** Every language feature and static analysis rule must be tested for both:
    -   **Positive (`run_pass` / `unit`):** Valid `.cx` code compiles cleanly and produces exact expected output in both `--dev` and `--release` modes.
    -   **Negative (`compile_fail`):** Invalid `.cx` code (type mismatches, use-after-free, double-free, memory leaks, out-of-bounds access, syntax errors) is rejected with the exact diagnostic code, line/column span, and help suggestion, with **zero false positives** on valid adjacent patterns.
3.  **Zero Duplication:** Consolidate table-driven cases (operator precedence, numeric promotions, target ABI layouts) into parameterized test tables rather than duplicating test functions.
4.  **No Agent Chatter:** Test files must follow all coding and comment standards in `AGENTS.md` Section 6 and the `docs` skill. Never leave conversational notes in test files.

---

## 3. Regression & Drift Guard Mandates

1.  **Mandatory Bug Regression Tests:** Every bug fix in the compiler, linker, runtime, or `.cx` standard library must include a minimal fixture reproducing the bug and verifying the fix before the task is complete.
2.  **Dev vs. Prod Differential Parity:** Every test in `tests/run_pass/` must execute under both the fast development backend and the optimizing production backend and assert identical stdout, stderr, and exit codes.
3.  **Drift Guards:** Maintain automated tests that verify:
    -   Every diagnostic code registered in the compiler catalog has at least one `compile_fail` test exercising it.
    -   Every CLI subcommand and flag in the parser is documented in `corex --help`.
    -   Every `.cx` file in the repository formats idempotently under `corex fmt --check`.

---

## 4. Cross-Platform Reliability (Windows, POSIX & Wasm)

All tests must pass deterministically on **Windows, Linux, and macOS**:

1.  **Path Normalization:** Normalize path separators (`/`) inside diagnostic snapshot outputs so golden snapshots match identically across Windows (`\`) and POSIX (`/`).
2.  **Line Endings:** Test lexing and formatting against both `LF` (`\n`) and `CRLF` (`\r\n`) inputs to guarantee byte-offset and line/column span accuracy on all OSes.
3.  **Platform Syscall & ABI Mocking:** Ensure Windows (`win32` / PE / Win64 ABI) and POSIX (`linux` / `darwin` / ELF / Mach-O / SysV ABI) code paths are both exercised in unit tests regardless of the host OS running the suite.

---

## 5. Fuzzing & Mutation Testing

1.  **Continuous Fuzzing (`tests/fuzz/`):**
    -   **Lexer/Parser Fuzzing:** Feed arbitrary byte streams and mutated `.cx` tokens into the fault-tolerant parser; assert **zero panics, zero out-of-bounds reads, zero infinite loops, and bounded memory usage** on all inputs.
    -   **Differential IR/Codegen Fuzzing:** Generate well-typed random `.cx` programs (`cxsmith` / grammar generator) and assert identical execution results between `--dev` and `--release`.
2.  **Coverage & Mutation Audits:**
    -   Inspect line and branch coverage reports after adding features; write targeted tests for any uncovered error recovery or edge-case branches.
    -   If a line cannot be reached due to a logic bug or dead branch, fix the underlying compiler code rather than suppressing coverage.

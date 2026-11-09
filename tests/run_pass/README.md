# End-to-End Execution Suite (`tests/run_pass/`)

Contains positive end-to-end `.cx` execution fixtures verifying that valid CoreX programs compile
cleanly with zero errors or warnings and produce deterministic runtime output.

## Verification Contract

1.  **Dual-Backend Execution:** Once `Phase 3` (`x86_64` / `aarch64` / `wasm32` backends) is active,
    every fixture in `tests/run_pass/` is compiled and executed under both `--dev` and `--release`.
2.  **Deterministic Output:** Each test asserts exact `stdout`, `stderr`, and process exit code parity
    against its expected `.out` specification.
3.  **Zero Leaks & Undefined Behavior:** All runtime allocations and region scopes inside `run_pass`
    programs are verified for deterministic cleanup at scope exit.

## Directory Layout

```text
tests/run_pass/
├── README.md               # End-to-end execution suite contract
├── core/                   # Primitives, control flow, pattern matching, and functions
├── memory/                 # Region arenas, linear ownership, and scope cleanup
└── std/                    # Standard library collections, strings, and I/O
```

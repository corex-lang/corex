# Dev vs. Release Differential Parity Suite (`tests/differential/`)

Contains differential equivalence fixtures and `cxsmith`-generated programs verifying bit-identical
observable behavior between the fast development backend (`--dev`) and the optimizing production backend
(`--release`).

## Verification Contract

1.  **Zero Miscompilations:** Every program in `tests/differential/` must produce identical `stdout`,
    `stderr`, exit status, and deterministic memory state across `--dev`, `--release`, and `MirVm`.
2.  **Cross-Target Equivalence:** Differential suites exercise integer overflow semantics (`+%`, `-%`,
    `*%`, `+|`, `-|`, `*|`), IEEE-754 floating-point edge cases, struct/union layout, and ABI lowering.
3.  **Regression Persistence:** Any divergence discovered by `tests/fuzz/` is minimized and committed
    permanently into this directory as a deterministic regression fixture.

## Execution Workflow

```text
corex test --suite=differential
```

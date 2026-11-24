# CoreX Escalated Engineering Issue Tracker

Tracks **Tier-2 (cross-cutting non-blocking)** and **Tier-3 (phase-blocking)** bugs in the CoreX compiler, SAST verifier, backends, `corex fmt`, `corex check`, `corex upgrade`, `corex lsp`, or `../vscode-ext-corex` that require user alignment or a dedicated architectural pass.

---

## 1. Strict Non-Abuse Rules (Preventing Technical Debt)

1.  **Never Log Tier-1 Bugs Here – Fix Them Immediately:**
    -   Any localized bug in the compiler, formatter, linter, `corex lsp`, or `vscode-ext-corex` discovered during a phase **must** be fixed immediately in the same session with a deterministic regression test (`.agents/AGENTS.md` §3).
2.  **Zero `.cx` Workarounds:**
    -   Never contort `.cx` code in `core/`, `stdlib/cx/`, or `compiler/` to work around an open compiler, SAST, or formatter bug. Either fix the root bug (Tier 1) or record a minimal reproducer below and **pause to ask the user** (Tier 2 / Tier 3).
3.  **Single-Writer Maintenance:**
    -   Maintained exclusively by the **Lead Agent** based on subagent escalations and verification sweeps; prune resolved entries once their regression tests land on `main`.

---

## 2. Open Escalated Issues

*(No open escalated issues.)*

---

## 3. Recently Resolved Escalations

| ID | Subsystem | Summary & Root Cause | Resolution & Regression Test |
| :--- | :--- | :--- | :--- |
| `ISS-001` | `query_db` / `lsp_server` / `vscode-ext-corex` | Signature edits in `stdlib/cx/*.cx` (e.g., `fn ln_f64(x, /)` in `math.cx`) triggered a cross-revision `core/root.cx -> stdlib/cx/mod.cx -> math.cx -> core/root.cx` `DependencyCycle` (`-32603`), silently wiping semantic tokens and hover tooltips; `documentSymbol` also had an $O(E \times S)$ scan + full-buffer `memcmp` bottleneck. | Enforced strict `core/*` -> `stdlib/cx/*` DAG layering and `in_flight` `maybeChangedAfter` self-healing in `stage0/src/query_db.zig`, optimized `lsp_server.zig` to $O(E + S)$, and wired RPC error logging + `Busy` token preservation in `vscode-ext-corex` (`test_lsp_stdlib_cx_signature_syntax_error_and_recovery_no_cycle` & `lspClient.test.ts`). |

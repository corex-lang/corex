# CoreX Escalated Engineering Issue Tracker

Tracks **Tier-2 (cross-cutting non-blocking)** and **Tier-3 (phase-blocking)** bugs in the CoreX compiler, SAST verifier, backends, `corex fmt`, `corex check`, `corex upgrade`, `corex lsp`, or `../vscode-ext-corex` that require user alignment or a dedicated architectural pass.

---

## 1. Strict Non-Abuse Rules (Preventing Technical Debt)

1.  **Never Log Tier-1 Bugs Here – Fix Them Immediately:**
    -   Any localized bug in the compiler, formatter, linter, `corex lsp`, or `vscode-ext-corex` discovered during a phase **must** be fixed immediately in the same session with a deterministic regression test (`.agents/AGENTS.md` §3). The only exception is staging newly reported IDE/compiler bugs here while another phase is actively mutating the working tree in parallel, to be fixed immediately once that run completes.
2.  **Zero `.cx` Workarounds:**
    -   Never contort `.cx` code in `core/`, `stdlib/cx/`, or `compiler/` to work around an open compiler, SAST, or formatter bug. Either fix the root bug (Tier 1) or record a minimal reproducer below and **pause to ask the user** (Tier 2 / Tier 3).
3.  **Single-Writer Maintenance:**
    -   Maintained exclusively by the **Lead Agent** based on subagent escalations and verification sweeps; prune resolved entries once their regression tests land on `main`.

---

## 2. Open Escalated & Staged Issues

| ID | Subsystem | Summary & Root Cause | Planned Fix & Verification |
| :--- | :--- | :--- | :--- |
| – | *(None currently open)* | – | – |

---

## 3. Recently Resolved Escalations

| ID | Subsystem | Summary & Root Cause | Resolution & Regression Test |
| :--- | :--- | :--- | :--- |
| `ISS-001` | `query_db` / `lsp_server` / `vscode-ext-corex` | Signature edits in `stdlib/cx/*.cx` (e.g., `fn ln_f64(x, /)` in `math.cx`) triggered a cross-revision `core/root.cx -> stdlib/cx/mod.cx -> math.cx -> core/root.cx` `DependencyCycle` (`-32603`), silently wiping semantic tokens and hover tooltips; `documentSymbol` also had an $O(E \times S)$ scan + full-buffer `memcmp` bottleneck. | Enforced strict `core/*` -> `stdlib/cx/*` DAG layering and `in_flight` `maybeChangedAfter` self-healing in `stage0/src/query_db.zig`, optimized `lsp_server.zig` to $O(E + S)$, and wired RPC error logging + `Busy` token preservation in `vscode-ext-corex` (`test_lsp_stdlib_cx_signature_syntax_error_and_recovery_no_cycle` & `lspClient.test.ts`). |
| `ISS-002` | `type_system` (`corex lsp`) | Shrinking live edits triggered an out-of-bounds panic (`index 16825, len 11819`) in `TypeChecker.checkFnDefaultParamExprs` because `checkScopeDefaultParamExprsRecursive` visited archived pre-`sym_start` function symbols whose `default_ast_node` indexed the previous larger `AstArena`. | Filtered `sym_idx >= sym_start` in `checkScopeDefaultParamExprsRecursive` and bounds-checked `spec.default_ast_node` against `self.ast_arena.countNodes()` (`test_lsp_dogfood_regressions_default_param_shrink_operator_hover_and_derive_tokens`). |
| `ISS-003` | `lsp_server` (`textDocument/hover`) | Hovering binary or unary operators (`^` and `+%` in `stdlib/cx/col.cx:3743-3744`) displayed the enclosing expression's result type tooltip (`u64`). | Guarded bare-type fallback in `handleHoverRequest` so non-identifier operator/punctuation tokens return `result: null` (`test_lsp_dogfood_regressions_default_param_shrink_operator_hover_and_derive_tokens` & `lspClient.test.ts`). |
| `ISS-004` | `lsp_server` (`semanticTokens`) | Nominal `struct` and `enum` declarations with `@derive(…)` (e.g., `pub struct AllocatorHandle`) highlighted the type name in function-cyan (`SEM_TOK_METHOD`) instead of struct-green (`SEM_TOK_STRUCT`) because synthesized `@derive` methods shared `decl_span`. | Required `std.mem.eql(u8, sym.name_text, decl_lex)` before binding `tok_symbols[decl_tok]` in `computeSemanticTokensData` (`test_lsp_dogfood_regressions_default_param_shrink_operator_hover_and_derive_tokens`). |
| `ISS-005` | `query_db` / `main.zig` / `build` | Editing large `.std_core` modules (`col.cx`, `str.cx`, `mem.cx`) exhibited multi-second squiggle and `Ctrl+S` latency because every keystroke swept all 19 `.std_core` files in `recomputeLiveSymbolUsageForFile` on a `DebugAllocator` binary. | Added bounded `SiblingUsageCache` (`<= 256` files / `<= 4 MiB`) in `stage0/src/query_db.zig`, switched `corex lsp` to `smp_allocator` in `stage0/src/main.zig`, and built `build/stage0/corex.exe` with `-Doptimize=ReleaseSafe` (`test_lsp_dogfood_regressions_default_param_shrink_operator_hover_and_derive_tokens`). |
| `ISS-006` | `vscode-ext-corex` (`logger.ts`) | The `CoreX` VS Code Output panel lacked syntax highlighting because `ensureChannel()` omitted the `'log'` language ID. | Passed `'log'` in `vsWindow.createOutputChannel('CoreX', 'log')`, verified in `config.test.ts` & `lspClient.test.ts`, and reinstalled local `corex-1.0.0.vsix`. |

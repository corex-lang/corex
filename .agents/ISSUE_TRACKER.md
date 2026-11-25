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
| `ISS-002` | `type_system` (`corex lsp`) | Shrinking live edits can trigger an out-of-bounds panic (`index 16825, len 11819`) in `TypeChecker.checkFnDefaultParamExprs` (`stage0/src/type_system.zig:10881-10955`) because `checkScopeDefaultParamExprsRecursive` visits archived pre-`sym_start` function symbols whose `default_ast_node` still indexes the previous larger `AstArena`. | Filter `sym_idx >= sym_start` (matching `verifyAllPass1FnParamModes`) and guard `spec.default_ast_node.asInt() < self.ast_arena.countNodes()`; add shrinking-edit LSP regression test. |
| `ISS-003` | `lsp_server` (`textDocument/hover`) | Hovering binary or unary operators (`^` and `+%` in `stdlib/cx/col.cx:3743-3744`) displays the enclosing expression's result type tooltip (`u64`) because `resolveCursorTarget` (`stage0/src/lsp_server.zig:6410-6428`) matches `.binary_expr.main_token` with `symbol_index = .none` and `handleHoverRequest` (`:7872-7879`) renders `target.type_id`. | Suppress hover (`result: null`) on raw punctuation/operator tokens instead of falling back to the expression result type; add operator-hover regression test. |
| `ISS-004` | `lsp_server` (`semanticTokens`) | Nominal `struct` and `enum` declarations with `@derive(…)` (e.g., `pub struct AllocatorHandle` in `stdlib/cx/mem.cx:78-79`) highlight the type name in function-cyan (`SEM_TOK_METHOD`) instead of struct-green (`SEM_TOK_STRUCT`) because synthesized `@derive` methods (`eq`, `clone`, `fmt_debug`) share `decl_span` and overwrite `tok_symbols[decl_tok]` in `computeSemanticTokensData` (`stage0/src/lsp_server.zig:5578-5598`). | Skip synthesized `@derive` symbols (or require `sym.name_text` parity with the declaration token lexeme) in `computeSemanticTokensData`; add `@derive` struct/enum semantic-token regression test. |
| `ISS-005` | `lsp_server` / `build.zig` | Editing large stdlib modules (`col.cx`, `str.cx`, `mem.cx`) exhibits ~`5 s` squiggle and `Ctrl+S` save latency because `drainAndDispatchInboundTurn` (`stage0/src/lsp_server.zig:12737-12740, 12960-12978`) flushes full-file 4-pass `MIR`/`SAST` + `comptime` diagnostics synchronously ahead of `textDocument/formatting` and `hover` while `build/stage0/corex.exe` runs in unoptimized Zig `Debug` mode. | Dispatch `formatting`, `hover`, and `completion` ahead of pending push diagnostics, deliver fast syntax/type squiggles before heavy SAST, avoid redundant multi-tab `didSave` diagnostic storms, and build `corex` with `-Doptimize=ReleaseSafe` for local IDE dogfooding. |
| `ISS-006` | `vscode-ext-corex` (`logger.ts`) | The `CoreX` VS Code Output panel lacks syntax highlighting because `ensureChannel()` in `../vscode-ext-corex/src/utils/logger.ts:29` calls `vsWindow.createOutputChannel('CoreX')` without `'log'`. | Pass `'log'` (`vsWindow.createOutputChannel('CoreX', 'log')`), update unit tests, and repackage local `.vsix`. |

---

## 3. Recently Resolved Escalations

| ID | Subsystem | Summary & Root Cause | Resolution & Regression Test |
| :--- | :--- | :--- | :--- |
| `ISS-001` | `query_db` / `lsp_server` / `vscode-ext-corex` | Signature edits in `stdlib/cx/*.cx` (e.g., `fn ln_f64(x, /)` in `math.cx`) triggered a cross-revision `core/root.cx -> stdlib/cx/mod.cx -> math.cx -> core/root.cx` `DependencyCycle` (`-32603`), silently wiping semantic tokens and hover tooltips; `documentSymbol` also had an $O(E \times S)$ scan + full-buffer `memcmp` bottleneck. | Enforced strict `core/*` -> `stdlib/cx/*` DAG layering and `in_flight` `maybeChangedAfter` self-healing in `stage0/src/query_db.zig`, optimized `lsp_server.zig` to $O(E + S)$, and wired RPC error logging + `Busy` token preservation in `vscode-ext-corex` (`test_lsp_stdlib_cx_signature_syntax_error_and_recovery_no_cycle` & `lspClient.test.ts`). |

# Mission: Autonomous Engineering & Verification of CoreX (`corex-lang/corex`)

You are the Lead Systems Compiler Architect and Principal Engineer for **CoreX** (`.cx`), a streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.

---

## 1. Mandatory First Step: Load Canonical Repository Standards (SSOT)

Before writing a single line of code, designing any module, or spawning any subagent, you MUST read and internalize the canonical rules, roadmap, and skills in this repository:

1.  `.agents/AGENTS.md` – Repository-wide core policies (strict typing, zero unchecked escape hatches, data-oriented performance idioms, zero-legacy philosophy, monochrome Unicode + ANSI CLI aesthetics, code structure, naming conventions, single-use variable inlining, and changelog maintenance).
2.  `PLAN.md` – The Master Engineering Roadmap (`Phase 0`–`Phase 13.4`), canonical compiler data structures, and the `RDG-01`–`RDG-22` Research Decision Gates table.
3.  `docs/research/DR-XX.md` (and `docs/research/PROMPTS.md`) – All resolved `Deep research` specification reports governing the active phase's Research Decision Gates (`RDG-01`–`RDG-22`).
4.  `.agents/skills/docs/SKILL.md` – Module headers, `< 150` column single-line-first doc/comment wrapping, standalone `:` vs. inline `.` comments, `[1]`/`[2]` step numbering, 90-char / 65-char centered section separators, and CLI diagnostic formatting.
5.  `.agents/skills/build/SKILL.md` – Build pipeline, cross-compilation verification matrix, and Stage 0 → Stage 1 → Stage 2 → Stage 3 self-hosting byte-for-byte determinism gates.
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
5.  Update `CHANGELOG.md` (and synchronize `docs/COMPARISONS.md` / `docs/LAUNCH.md` when user-facing capabilities or CLI deliverables ship) per `.agents/AGENTS.md` Section 7 and report your verification summary.

---

## Current Active Assignment: Execute Phase 10.5 Only (`vscode-ext-corex`)

Research Decision Gates `RDG-01`–`RDG-22` are all resolved in `docs/research/DR-01.md` through `docs/research/DR-22.md`, and **Phases 0–10** (including the finalized `120`-token / `70`-keyword CoreX v1.0 surface in `DR-21`/`DR-22`, the `< 10 ms` P99 `corex lsp` 3.17 daemon, `corex fmt` / `formatByteRange`, `corex check`, and `corex upgrade` live in `d:\GitHub\corex\build\stage0\corex.exe`) are complete and verified.

Your mission in this session is to execute **Phase 10.5: Local IDE Support – Official VS Code Extension (`vscode-ext-corex` `v1.0.0`)** from `d:\GitHub\corex\PLAN.md` inside the dedicated sibling repository **`D:\GitHub\vscode-ext-corex`** (`https://github.com/corex-lang/vscode-ext-corex.git`) so Phases 11 (`stdlib/cx/*.cx`) and 12 (`compiler/*.cx`) are authored with full IDE syntax highlighting, live `corex lsp` intelligence, and format-on-save (do **NOT** implement Phase 11+ stdlib/compiler deliverables yet, do **NOT** publish to VS Marketplace or OpenVSX yet, and keep `d:\GitHub\corex` **100% free** of Node.js/TypeScript/extension files per `docs/LAUNCH.md` §1):

1.  **Mandatory Step 0 – Gold-Standard Reference Synthesis & Agent Rules Bootstrap (`D:\GitHub\vscode-theme-isolux` & `D:\GitHub\vscode-ext-color-tracr`):**
    -   Before writing a single extension source or documentation file, read `d:\GitHub\corex\PLAN.md` (§Phase 10.5), `d:\GitHub\corex\docs\LAUNCH.md` (Stages `L1` & `L6`), `d:\GitHub\corex\stage0\src\{syntax_arenas,lexer,lsp_server}.zig`, and inspect both local gold-standard sibling repositories: **`D:\GitHub\vscode-theme-isolux`** (`.agents/AGENTS.md`, `theme/theme.jsonc`, `package.json`, `README.md`, `CHANGELOG.md`) and **`D:\GitHub\vscode-ext-color-tracr`** (`.agents/AGENTS.md`, `.agents/skills/{build,test}/SKILL.md`, `package.json`, `esbuild.js`, `vitest.config.mts`, `.oxfmtrc.json`, `.oxlintrc.json`, `.markdownlint.json`, `src/`, `test/`, `README.md`, `CHANGELOG.md`).
    -   Preserve `D:\GitHub\vscode-ext-corex\LICENSE` and `D:\GitHub\vscode-ext-corex\assets\icon.png` untouched, and synthesize `D:\GitHub\vscode-ext-corex\.agents\AGENTS.md`, `D:\GitHub\vscode-ext-corex\.agents\skills\build\SKILL.md`, and `D:\GitHub\vscode-ext-corex\.agents\skills\test\SKILL.md` (plus `.oxfmtrc.json`, `.oxlintrc.json`, `.markdownlint.json`, `tsconfig.json`, `esbuild.js`, `vitest.config.mts`, `.vscodeignore`, `.gitignore`, `.gitattributes`, and `.vscode/launch.json`), strictly enforcing `pnpm` only (never `npm`/`npx`/`yarn`), strict TypeScript (`no any`), plain `function` declarations (no classes), separate `import type`, explicit initialization, `i += 1`, descriptive multi-letter names (`is*`/`has*` booleans, `<NAME>_RX` regexes), 90-char centered `// --- SECTION ---` dividers (`TYPES`, `CONSTS`, `REGEX PATTERNS`, `INTERNALS`, `PUBLIC API`, `MAIN`), JSDoc headers, en dashes `–`, Unicode ellipsis `…`, and zero colored emojis from the very first file onward.
2.  **Complete CoreX v1.0 TextMate Grammar (`syntaxes/corex.tmLanguage.json`, `scopeName: "source.corex"`):**
    -   Cover all `120` `TokenKind`s (`0..119`) and `70` reserved keywords/primitives (`50` keywords + `20` primitives `i8`–`i128`, `u8`–`u128`, `isize`, `usize`, `f32`, `f64`, `bool`, `char`, `str`, `unit`, `never`, `opaque`), contextual keywords (`test`, `bench`, `pkg`, `super`, `any`, `dyn`, `distinct`, `out`, `raw`, `static`, `inout`), all `12` built-in Constrained Type Groups (`Signed`, `Unsigned`, `Integer`, `Float`, `Number`, `Comparable`, `Equatable`, `Bytes`, `Scalar`, `Copy`, `FromBytes`, `IntoBytes`) and prelude nominal types, `PascalCase` types/variants (`entity.name.type.corex`), `SCREAMING_SNAKE_CASE` constants (`constant.other.caps.corex`), `snake_case` functions/methods (`entity.name.function.corex`), `@attr(k: v)` & `@intrinsic(…)` annotations (`punctuation.definition.annotation.corex` + `storage.type.annotation.corex` so `vscode-theme-isolux` renders upright `token.annotation` rather than italic `storage.modifier`), `#soa` & `#!` shebangs, `:label` / `label:` (`entity.name.label.corex`), nested `/* /* … */ */` block comments & `///` / `//!` / `//` comments, `"…"` / `"""…"""` / `r"…"` / `r#"…"#` / `r"""…"""` / `r#"""…"""#` / `b'…'` / `b"…"` / `b"""…"""` / `br#"…"#` / `br#"""…"""#`, recursive `{expr=:#06x}` interpolation (`punctuation.definition.interpolation.{begin,end}.corex` + `storage.type.format.corex` + `$self`) and `{{`/`}}` escapes (`constant.character.escape.corex`), and `_`-separated numeric suffixes (`keyword.other.unit.corex`), ensuring clean highlighting under both `vscode-theme-isolux` and GitHub PrettyLights (`github-linguist/linguist`).
3.  **Language Configuration (`language-configuration.json`) & `package.json` Metadata (`v1.0.0`):**
    -   Set `"publisher": "corex-lang"`, `"name": "corex"`, `"displayName": "CoreX"`, `"version": "1.0.0"`, `"author": { "name": "XulbuX", "email": "hi@xul.is" }`, `"maintainers": ["XulbuX <hi@xul.is>"]`, `"license": "MIT"`, `"icon": "assets/icon.png"`, and dark gallery banner matching `isolux` / `color-tracr` README/CHANGELOG quality.
    -   Configure `//`, `///`, `//!`, and `/* … */` comments, bracket matching and auto-closing pairs (`{}`, `[]`, `()`, `""`, `"""…"""`, `''`), smart block/match indentation rules, folding markers, `.cx` language association (`id: "corex"`, `extensions: [".cx"]`, shebang `^#!.*\bcorex\b`, plus `contributes.languages[0].icon` pointing to `./assets/icon.png` so `.cx` files display the CoreX icon in the Explorer out of the box), and the 5 custom `corex lsp` semantic token modifiers (`mutable`, `consumedMove`, `unsafe`, `attribute`, `linearResource`) in `contributes.semanticTokenModifiers` and `contributes.semanticTokenScopes`.
4.  **Zero-Dependency `corex lsp` & `corex fmt` Client (`src/`):**
    -   Implement an ultra-lightweight, zero-runtime-dependency in-house JSON-RPC 2.0 `stdio` LSP 3.17 client (`0` `"dependencies"` in `package.json`, `< 25 KB` `dist/extension.js`, matching `color-tracr`'s minimal-footprint architecture) across modular TypeScript files (`src/extension.ts`, `src/config.ts`, `src/binary.ts`, `src/client.ts`, `src/utils/logger.ts`) resolving `corex` via `corex.executablePath`, workspace `build/stage0/corex[.exe]`, `zig-out/bin/corex[.exe]`, `build/corex[.exe]`, sibling `../corex/build/stage0/corex[.exe]`, `~/.corex/bin/corex[.exe]`, and `PATH`; auto-enabling `--internal-core` (`corex.internalCore`: `"auto" | "always" | "never"`, default `"auto"` when the open workspace is the `corex` compiler/stdlib tree containing `core/root.cx` + `stage0/` or `compiler/`); bridging diagnostics, semantic tokens (`full`/`delta`/`range`), hover, definition/typeDefinition, references/highlights, document/workspace symbols, completion, signatureHelp, inlayHints, codeActions, rename/prepareRename, `$/cancelRequest`, and `workspace/didChangeWatchedFiles` (`**/corex.toml`, `**/corex.lock`, `**/*.cx`); exposing `corex.restartServer` and `corex.showOutputChannel`; and serving document/range formatting via `corex lsp` (with CLI `corex fmt` fallback when LSP is disabled).
5.  **Verification Gate & Local-Only `.vsix` Dogfooding Install:**
    -   Build an automated `vitest` + `vscode-textmate` + `vscode-oniguruma` test suite tokenizing all `14` `d:\GitHub\corex\core\**\*.cx` files and all `9` `.cx` showcases in `d:\GitHub\corex\docs\COMPARISONS.md` (asserting zero unscoped syntax tokens), plus headless integration tests exercising the in-house JSON-RPC client against live `d:\GitHub\corex\build\stage0\corex.exe lsp` (`initialize`, `diagnostics`, `hover`, `definition`, `semanticTokens/full/delta`, and `formatting`, including `--internal-core` on `core/*.cx`).
    -   Verify `pnpm run check` (`oxfmt --check`, `oxlint`, `tsc --noEmit`, `vitest run`, `node esbuild.js --production`) and `pnpm dlx markdownlint-cli2 "**/*.md"` pass with zero errors or warnings, package `corex-1.0.0.vsix` via `pnpm dlx @vscode/vsce package --no-dependencies`, and install it **locally only** via `code --install-extension` for Phase 11–12 development (strictly deferring public VS Marketplace and OpenVSX publishing until *after* `CoreX v0.0.1` ships in `docs/LAUNCH.md` Stage `L1`).

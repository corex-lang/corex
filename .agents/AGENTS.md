# Agent Guidelines for `corex`

When working on this repository (`corex-lang/corex`), any AI agent, subagent, or automated assistant must adhere strictly to the following rules to maintain the compiler, runtime, standard library, and toolchain at maximum integrity, performance, and correctness.

## 1. Strict Static Typing & Zero Unchecked Escape Hatches

Every line of code across this repository – including the bootstrap compiler, the self-hosted `.cx` compiler, runtime intrinsics, the `.cx` standard library, Language Server (LSP), and all build/test/benchmark harnesses – must be strictly typed and 100% statically analyzable.

-   **No Untyped Constructs:** Never use untyped escape hatches (`any`, unvalidated raw `void*`, or unchecked type punning). Represent compiler entities via strongly typed index handles (`FileId`, `Span`, `SymbolId`, `TokenId`, `CstNodeId`, `AstNodeId`, `HirId`, `MirBlockId`, `MirValueId`, `TypeId`, `ScopeId`, `RegionId`, `DiagId`) and exhaustive tagged unions / sum types.
-   **No Blanket Suppressors:** Blanket compiler, type-checker, or linter ignore pragmas are forbidden. When a static check suppression is fundamentally unavoidable, use a rule-specific scoped attribute (`@allow(W0202)` in `.cx`) accompanied by an explicit architectural reason comment, and only when rewriting the code to satisfy the check statically would degrade runtime performance or clarity.

## 2. Performance, Memory Discipline & Zero-Legacy Architecture

CoreX targets instant compilation in development mode, zero cold-start latency, minimal memory/disk footprint, and C-level runtime execution speed in production mode.

-   **Performance First:** Prioritize throughput and cache locality across every compiler stage.
-   **Lazy Initialization:** Defer heavy initialization (target machine descriptions, optimization pass pipelines, external linker discovery, package cache indexing, and regex/table compilation) until first use; never execute heavy setup eagerly at process startup.
-   **Allocation Discipline & Data-Oriented Design:**
    -   **Arena & Pool Allocation:** Allocate syntax nodes, IR instructions, types, and symbols in contiguous arenas or flat typed arrays indexed by compact integer IDs (`u32`) rather than pointer-chasing heap graphs. Reuse scratch buffers across compilation units.
    -   **No Unnecessary Intermediate Collections:** Prefer explicit `for` loops or pre-allocated slices over chained `.map()/.filter()` closures or generator expressions when intermediate allocations are not needed. For short-circuiting predicates (`any`, `all`, `find`), write explicit unrolled loops with early `return` or `break`.
    -   **String Building:** Never use `+=` for string or byte-buffer concatenation inside loops; write into pre-allocated string/byte builders.
    -   **O(1) Membership Lookups (CRITICAL):** Always use hash sets, bitsets, or static lookup tables for membership checks – never linear scans over lists, arrays, or tuples.
    -   **Non-Backtracking Lexing & Scanning:** Implement lexers and text scanners as deterministic finite automata or non-backtracking character-class scanners; never rely on backtracking regular expressions.
-   **Bounded Memory, Output & CPU:** Treat every `.cx` source file, package manifest, lockfile, and network/LSP payload as untrusted input:
    -   **Bounded Caches:** Bound all in-memory and disk caches by both entry count **and** total byte size using explicit LRU eviction – never unbounded maps.
    -   **Resource Caps:** Enforce explicit upper bounds on parser/type-checker recursion depth, token/AST node counts, macro/comptime expansion steps, and emitted diagnostic counts before expensive work.
-   **Minimal Dependencies & Footprint:** Avoid heavyweight third-party libraries in favor of small, verifiable, in-house data structures and lookup tables.
-   **DRY & Unified Compiler Pipeline:** Abstract repeated patterns into shared helpers. Feed multi-stage compiler representations (source buffers, tokens, lossless CST/AST, HIR, MIR, diagnostics) through a single canonical pipeline shared by the compiler, formatter (`corex fmt`), linter, migration tool (`corex upgrade`), and Language Server (`corex lsp`).
-   **Dynamic Metadata (No Hardcoded Drift):** Derive CLI flags, diagnostic codes, built-in intrinsics, grammar tokens, and version metadata dynamically from canonical source tables so help menus, tooling, and documentation never drift.
-   **Soundness Over Heuristics:** In type checking, static vulnerability analysis (SAST), lifetime verification, and code generation, mathematical soundness and zero miscompilations take absolute priority.
-   **Zero-Legacy Philosophy (CRITICAL):** Never bloat or slow down the compiler with backward-compatibility branches for deprecated syntax or legacy language versions. The compiler must only ever target the current CoreX specification; breaking language evolutions are handled exclusively by automated AST rewriting in `corex upgrade` / `corex fix`.

## 3. Validation, Testing & Benchmarking

After making any code changes, you must validate them by running the full suite of formatters, linters, static analyzers, type checkers, unit tests, snapshot tests, negative safety tests, and end-to-end execution tests. Fix all problems until the output is completely clean (**zero errors, zero warnings, and zero lint issues**).

-   **100% Coverage Across Platforms:** Test coverage must remain at 100% across all supported host and target platforms (Windows, Linux, macOS, and `wasm32`).
-   **Regression Tests (CRITICAL):** Every bug fix **must** include a deterministic regression test reproducing the original bug and verifying the fix before the task is considered complete.
-   **Drift Guards:** Automated tests enforce parity across canonical compiler tables (CLI subcommands/flags, diagnostic catalogs, built-in intrinsics, stdlib exports) and documentation. Add a drift assertion whenever introducing a code-governed table or limit referenced in prose.
-   **Cross-Subsystem Propagation:** Whenever a bug is fixed, an invariant is tightened, or an optimization is applied in one compiler pass or target backend, immediately inspect all sibling passes/targets and apply the improvement everywhere in the same edit session.
-   **Skills Reference:** Use the `test` skill for test harness architecture and fuzzing, the `build` skill for compilation and self-hosting bootstrap verification, the `bench` skill for performance tracking, and the `audit` skill for end-to-end quality audits.

## 4. Ask, Don't Assume & Research Decision Gates

-   **Ask First:** If you encounter ambiguous requirements, language design edge cases, or architectural trade-offs, **ask the user first**. Never guess or make silent assumptions.
-   **One Canonical Way (Zero Redundant Syntax / APIs):** Every CoreX construct, keyword, operator, intrinsic, and stdlib operation must have **one canonical way** to express it – never introduce multiple competing syntaxes, alias operators, duplicate intrinsics, or overlapping APIs that fragment style or multiply edge cases. If you encounter or consider multiple ways to express the same construct, ask the user for their preference before adding, altering, or removing anything.
-   **Research Decision Gates:** Do not prematurely hardcode internal algorithms for compiler or standard library subsystems gated by a pending `Deep research` report. Consult `PLAN.md` for the master phase roadmap and `RDG-01`–`RDG-23` / `STD-01`–`STD-07` gate mappings, `docs/research/PROMPTS.md` and `docs/research/stdlib/PROMPTS.md` for the upfront research prompts, and `docs/research/DR-XX.md` and `docs/research/stdlib/STD-XX.md` for completed research specifications. Program against clean modular traits/interfaces until the completed research report is integrated.
-   **On-Demand `Deep research` Escalation:** Whenever you encounter a complex low-level algorithm, platform ABI quirk, or architectural trade-off where deep domain synthesis would elevate compiler quality, pause and provide the user with a self-contained, copy-pasteable `Deep research` prompt. Every syntax or API `Deep research` prompt must evaluate novel, first-principles CoreX designs alongside existing language precedents so a cleaner, demonstrably superior new design can win when existing languages all carry legacy compromises.
-   **Subagent Quality Orchestration:** When subagents are available, follow `.agents/ORCHESTRATION.md` and spawn specialized subagents liberally to maximize architectural rigor, adversarial code review, edge-case verification, and fuzzing coverage – prioritizing correctness and quality over raw speed.

## 5. CLI & Diagnostic Aesthetics

Every `corex` terminal interaction (`corex` help menus, build progress, test runners, benchmark tables, and compiler diagnostics) must enforce a spotless, modern CLI aesthetic from day one:

-   **Monochrome Unicode + ANSI Only:** Use crisp ANSI foreground/style formatting paired exclusively with clean monochrome Unicode symbols and box-drawing characters (`╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠`).
-   **Strict Ban on Colored Emojis (CRITICAL):** Never use colored emojis (such as `U+1F680`, `U+274C`, `U+2705`, `U+26A0 U+FE0F`) anywhere in CLI output, compiler diagnostics, source code comments, commit messages, or documentation. Every special symbol must be a monochrome glyph that respects terminal foreground ANSI colors.
-   **Human-Centric Diagnostics:** Compiler errors and static memory/lifetime warnings must display exact source spans, colorized terminal code snippets with Unicode box-drawing underline pointers, and actionable fix suggestions.

## 6. Code Structure, Naming & Readability

-   **Logical Placement:** Never mindlessly append new declarations to the end of a file. Insert new code in the logical section that groups related functionality together.
-   **Module Headers & Section Order:** Start every source file (except pure re-export barrels) with a structured module header and organize contents using 90-character centered section dividers in canonical order: `TYPES`, `CONSTS`, `INTERNALS`, `PUBLIC API`, `MAIN` (plus optional trailing `TESTS` for inline `test` / `bench` items; in `.cx`, place `struct`/`enum`/`union`/`bit_field`/`trait`/`type` declarations in `TYPES`, private `fn`/`impl` helpers in `INTERNALS`, and `impl` blocks with `pub` members and `pub fn` items in `PUBLIC API` – follow the `docs` skill for exact header and separator specifications).
-   **Imports & Constants Placement:** Place all imports at the very top of the file (except OS-specific modules/syscalls guarded inside platform-conditional branches). Define private constants, static lookup tables, and caches in `CONSTS` directly below imports and types.
-   **Define Before Use & Organization:** Place internal helper functions in `INTERNALS` above `PUBLIC API` and `MAIN`. Sort large static maps, keyword tables, and enum lists alphabetically unless a specific logical or binary-layout order is required.
-   **Plain Functions & Explicit Context:** Prefer plain functions, flat data structures, and traits over inheritance hierarchies. Leverage CoreX's implicit `context` (`SE-08`) or pass shared compiler state explicitly via a `session` / `db` parameter.
-   **Naming Conventions:**
    -   **Language Casing Conventions:** In CoreX (`.cx`), follow `DR-03`, `DR-21`, `DR-22`, and `DR-23` (`PascalCase` types/traits/type-groups/enum-variants/`@constructor` functions, `snake_case` functions/methods/variables/fields/modules/attributes, `SCREAMING_SNAKE_CASE` constants). In the Stage 0 Zig bootstrap compiler (`stage0/`), follow the official Zig Style Guide (`PascalCase` types and type-returning functions, `camelCase` functions and methods, and `snake_case` variables, parameters, struct fields, and enum tags).
    -   **Descriptive Variable Names (CRITICAL):** Cryptic single-letter variable names (e.g., `c`, `r`, `f`, `s`, `p`, `v`) are banned. Use clear, descriptive names (`cursor`, `reader`, `file`, `text`, `path`, `value`). The only exceptions are `i`, `j`, `k` for loop/matrix indices, `n` for mathematical counts/lengths, and `x`, `y`, `z`, `w` for spatial coordinates or SIMD vector lanes.
    -   **Predicates, Booleans & Attribute Keys:**
        -   **Predicate functions & methods** returning `bool` must read as clear predicates using `is_…`, `has_…`, `can_…`, `should_…` (or `is…`/`has…` in Stage 0 Zig), or standard relational verbs (`contains`, `starts_with`, `ends_with`, `matches`), e.g., `is_empty()`, `is_valid_utf8()`, `is_success()`, `has_errors()`.
        -   **Local boolean variables** use `is_…` / `has_…` / `can_…` / `should_…` when needed for clarity (`let is_tty = …;`, `var has_errors = false;`), whereas **struct fields, `@attribute_schema` keys, bitfield flags, and keyword parameters** may use concise domain names without forced `is_` prefixes whenever the meaning is unambiguous from static `bool` typing (e.g., `@arg(positional: true)`, `@flag(negatable: true)`, `@serde(skip: true, flatten: true)`, `readonly: bool`, `keep_alive: bool`, `zeroed: bool`; use `is_open` / `has_niche` when a bare word could be misread as an action or non-boolean).
    -   **Three-Tier Views & Conversions (`as_…` / `to_…` / `into_…`):**
        -   **Borrowed Views (`as_…` / `as…`):** $O(1)$ zero-allocation borrowed views or cheap handle projections (`&self` / `&mut self`) must use **`as_…`** in `.cx` (`as…` in Zig), e.g., `.as_slice()`, `.as_str()`, `.as_bytes()`, `.as_ptr()`, `.as_mut_ptr()`, `.as_reader()`, `.as_writer()`. Never use `.to_…()` for borrowed views.
        -   **Non-Consuming Conversions (`to_…` / `…_to_…`):** Conversions that compute a new value or allocate new storage without consuming `self` must use **`to_…`** or **`…_to_…`** (`to…` / `…To…` in Zig), e.g., `.to_string()`, `.to_path_buf()`, `.to_octets()`, `.to_le_bytes()`, `ast_to_hir()`.
        -   **Ownership-Consuming Conversions (`into_…`):** MVS conversions taking `own self` to transfer backing resources in $O(1)$ without copying must use **`into_…`**, e.g., `String.into_bytes(own self) -> Vec[u8]`, `OwnPtr.into_raw(own self) -> *mut T`.
    -   **Parsing vs. Extraction (`parse_…` vs. `extract_…`):**
        -   Use **`parse_…`** (or `Type.parse(…)`) when validating and decoding an entire input slice or token stream into a typed value or syntax tree (`parse_int`, `parse_float`, `Ipv4Addr.parse`, `parse_expr`).
        -   Use **`extract_…`** (`extract…` in Zig) when scanning or pulling structured sub-elements out of a larger container, raw text buffer, or stream (`extract_frontmatter`, `extract_tokens`, `extract_item_tree`).
    -   **Constructors, Property Accessors & Action Verbs:**
        -   Use idiomatic constructors on nominal types (`new`, `with_capacity`, `in_arena`, `from_…`, `open`, `connect`) and concise noun accessors for $O(1)$ properties without `get_` noise (`.len()`, `.capacity()`, `.header()`, `.status()`, reserving `get` / `get_mut` for fallible keyed/indexed lookups).
        -   Start standalone functions and mutating/effectful methods with an active verb (`emit_diagnostic`, `resolve_symbol`, `write_all`, `flush`, `clear`).
    -   **Path Resolution:** Always use standard filesystem terminology **`resolve_path`** and **`resolve_or_create_path`** in `.cx` (or **`resolvePath`** and **`resolveOrCreatePath`** in Stage 0 Zig) instead of non-standard names.
-   **Control Flow & Expression Hygiene:**
    -   **Mutual Exclusion (`else if` & `match` / `switch`):** Always use `else if` when chained conditions check mutually exclusive cases or follow an early exit (`return`, `break`, `continue`). Use exhaustive `match` (`.cx`) / `switch` (Zig) pattern matching when branching repeatedly on the same discriminant or token/AST kind.
    -   **Condition-Scoped Bindings (CRITICAL):** When assigning a variable that is immediately evaluated in an `if` or `while` condition and reused inside the branch, inline the assignment/binding directly into the condition where supported by the language (`is`, `:=`, or condition assignment).
    -   **No Single-Use Temporary Variables (CRITICAL):** Never assign an expression to a temporary variable that is only read once; pass it directly into the consuming call, return statement, or assertion. A single-use variable is only acceptable when inlining would span four or more lines, obscure a complex multi-branch calculation, or recompute a costly invariant inside a loop.
    -   **Explicit Initialization & Loop Increments:** Explicitly initialize variables that may remain unset, and use `i += 1` instead of `i++`.

## 7. Documentation, Typography & Changelog

-   **Mandatory Documentation:** Every module, struct/type, enum, constant, public function, and internal helper across the codebase requires a concise doc comment describing its purpose and invariants. Follow the `docs` skill for all docstring/comment formatting, `< 150` column wrapping, section separators, and punctuation rules.
-   **Maintain Documentation Integrity:** Preserve all existing comments and docstrings unrelated to your code changes unless instructed otherwise.
-   **American English (`en-US`):** Use American English spelling across all identifiers, diagnostics, comments, documentation, tests, and commit messages (e.g., `canceled`, `canceling`, `color`, `behavior`, `serialize`, `optimize`, `gray`; note that `cancellation` retains double `l` in American English, and verbatim external OS/protocol/C symbols keep their upstream spelling).
-   **Typography & Ellipsis (`…` vs `...`):**
    -   Always use the single Unicode ellipsis character `…` instead of three ASCII dots `...` in all documentation, docstrings, comments, and string truncations (including CLI output truncation). The ONLY exceptions are active terminal progress indicators (e.g., `Compiling...`, `Linking...`) and native language syntax tokens (`...`).
    -   Never use em dashes (`—`); use `; `, a new sentence, or an en dash (`–`). Always write `e.g.,` with a trailing comma.
-   **Markdown Linting:** All Markdown files (`.md`) must strictly adhere to the rules defined in `.markdownlint.json`.
-   **Changelog Maintenance:** Document every user-visible change to the language, compiler, CLI, or standard library under the current unreleased section at the top of `CHANGELOG.md` using canonical headings in order (`### Added`, `### Changed`, `### Deprecated`, `### Removed`, `### Fixed`, `### Security`, `### Breaking Changes` – include only non-empty sections). Never modify published release entries. New modules or subsystems added in the unreleased version must be summarized as a single entry under `### Added` rather than logging intermediate development iterations.
-   **Comparison & Launch Roadmap Maintenance:** Whenever a phase lands or modifies a user-facing language advantage, static verification guarantee, CLI subcommand, or ecosystem/release deliverable, synchronize `docs/COMPARISONS.md` (promoting `[v0.0.1]` / `[0.x]` status tags to `[Live]` as features ship and adding any new CoreX advantages or showcases) and `docs/LAUNCH.md` so launch and website source material never drifts.
-   **Editor Grammar Synchronization (`vscode-ext-corex`):** Whenever a change adds, renames, or retires any CoreX surface syntax element – keywords, contextual modifiers, primitive types, Constrained Type Groups, built-in `@attribute` / `@intrinsic` names, literal forms, operators, delimiters, or `corex lsp` semantic token modifiers – synchronize `../vscode-ext-corex/syntaxes/corex.tmLanguage.json` (and `language-configuration.json` / `package.json` if affected) so non-LSP TextMate highlighting, Markdown ```` ```cx ```` code blocks, and GitHub Linguist never drift from the compiler.

## 8. Rule & Skill Authoring (Single Source of Truth)

To keep agent guidelines clean, maintainable, and free of contradictions, adhere strictly to the Single Source of Truth (SSOT) principle:

-   **Define Once:** Every rule, standard, or workflow must be defined in exactly ONE canonical location:
    -   **`AGENTS.md`:** Repository-wide core policies (strict typing, performance and memory discipline, zero-legacy policy, validation, CLI aesthetics, code structure, naming, typography, and changelog maintenance).
    -   **`PLAN.md` & `docs/research/`:** Master phase roadmap, canonical compiler data structures, `RDG-01`–`RDG-23` and `STD-01`–`STD-07` Research Decision Gates, upfront research prompts (`docs/research/PROMPTS.md` and `docs/research/stdlib/PROMPTS.md`), and resolved compiler/stdlib research specifications (`docs/research/DR-XX.md` and `docs/research/stdlib/STD-XX.md`).
    -   **`docs/COMPARISONS.md` & `docs/LAUNCH.md`:** Canonical cross-language advantage catalog (with side-by-side `.cx` showcases) and post-Phase-12 website, playground, distribution, history-squash, and GitHub Linguist adoption roadmap.
    -   **`.agents/ORCHESTRATION.md`:** Autonomous multi-subagent quality orchestration workflow.
    -   **Skills (`.agents/skills/<skill>/SKILL.md`):** Specialized domain workflows and detailed formatting specifications (`docs` for doc comments, comments, and section separators; `build` for compilation, cross-targets, and self-hosting bootstrap; `test` for verification suites, snapshots, and fuzzing; `bench` for performance benchmarking; `audit` for comprehensive codebase audits).
-   **Reference, Never Duplicate:** When a rule defined in one location applies in another, do NOT duplicate or re-explain the rule. Point directly to its canonical definition in `AGENTS.md` or the respective skill.
-   **Synchronize References:** Whenever a canonical rule is updated or moved, verify that all references pointing to it remain accurate.

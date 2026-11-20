# CoreX Release, Website, Ecosystem & Adoption Roadmap

This document is the canonical post-code-complete launch and adoption plan for **CoreX** (`corex-lang`). While [`PLAN.md`](../PLAN.md) governs the technical implementation of the compiler, runtime, `cx.*` standard library, and self-hosting pipeline (`Phase 0`–`Phase 13.4`), this roadmap governs everything required to turn the finished **`v0.0.1`** self-hosted toolchain into an actively adopted language ecosystem – culminating in `>= 200` organic public `.cx` repositories and official inclusion in [`github-linguist/linguist`](https://github.com/github-linguist/linguist).

---

## 1. Organization Repository Topology (`corex-lang/*`)

Keeping web assets, editor grammars, and starter templates in dedicated repositories under the `corex-lang` GitHub organization ensures `corex-lang/corex` stays lean (`< 1 MB` installed toolchain footprint, zero Node/Vite lockfiles or media assets in compiler history) while maximizing non-fork `.cx` repository creation:

| Repository | Purpose | License |
| :--- | :--- | :--- |
| `corex-lang/corex` | Self-hosted CoreX compiler, SAST/MVS verifier, `cx.*` standard library, and unified `corex` CLI (`bench`, `build`, `check`, `doc`, `fmt`, `init`, `lsp`, `run`, `test`, `translate-c`, `upgrade`). | MIT / Apache-2.0 |
| `corex-lang/vscode-ext-corex` | Official VS Code & OpenVSX extension (`syntaxes/corex.tmLanguage.json` TextMate grammar + `corex lsp` client; developed locally in sibling workspace `../vscode-ext-corex` during `Phase 10.5` and published publicly in Stage `L1`). Vendored as a Git submodule by `github-linguist/linguist`. | MIT |
| `corex-lang/website` | Official CoreX website, client-side WASM playground, interactive comparisons, benchmarks, language tour, and searchable `cx.*` API documentation. | MIT |
| `corex-lang/setup-corex` | Official GitHub Action (`uses: corex-lang/setup-corex@v1`) installing pre-built `corex` binaries in `< 2 s` for CI workflows. | MIT |
| `corex-lang/corex-starter` | Official minimal **GitHub Template Repository** (`corex.toml`, `src/main.cx`, CI workflow, `.gitattributes`). | MIT-0 / MIT |
| `corex-lang/corex-cli-starter` | Official **GitHub Template Repository** for sub-millisecond CLI tools using `cx.cli` and `cx.fs`. | MIT-0 / MIT |
| `corex-lang/corex-aoc-starter` | Official **GitHub Template Repository** for Advent of Code / coding challenges (`src/day01.cx`–`src/day25.cx` + `corex test` & `corex bench` harness). | MIT-0 / MIT |
| `corex-lang/corex-c-interop-starter` | Official **GitHub Template Repository** demonstrating zero-ceremony C FFI (`SDL3` / `raylib` / `sqlite3` via `@c_import`). | MIT-0 / MIT |

### Cross-Repository Artifact Sync (`corex` → `website`)

To prevent manual documentation drift between `corex-lang/corex` and `corex-lang/website`, release tags (`v*`) and local build scripts export four deterministic machine-readable artifacts directly into `corex-lang/website`:

1.  **`corex-playground.wasm`:** The self-hosted CoreX frontend, SAST verifier, `corex fmt`, and `MirVm` compiled to `wasm32-unknown-freestanding` (compressed with Brotli/Zstd for instant browser loading).
2.  **`cx-api-docs.json`:** Structured module, type, trait, function, contract (`@no_alloc`, `@no_panic`, `@max_stack`), and inferred capability (`EffectCapabilityMask`) metadata extracted directly from `//!` and `///` docstrings in `core/` and `stdlib/cx/` via `corex doc --format=json --out <path>`.
3.  **`benchmarks.json`:** Reproducible compilation speed, cold-start latency, stripped binary size, and runtime execution timings against C (`clang -O3`), Rust (`rustc -O`), Zig (`ReleaseFast`), and Go.
4.  **Curated Showcases (`docs/COMPARISONS.md`):** Canonical side-by-side `.cx` comparison snippets synced into the website landing page and playground preset dropdowns.

---

## 2. Stage `L0` – Pre-Release CLI Onboarding & Doc Extractor (Post-Phase 12, Pre-Tag)

Immediately after `Phase 12` achieves 3-stage self-hosting SHA-256 fixed-point parity and before tagging `v0.0.1`, complete three high-leverage developer-experience polish items:

1.  **`corex init [name]` Project Scaffolder:**
    -   Generates a clean, ready-to-commit workspace in `< 5 ms`:
        -   `corex.toml` (package metadata, edition/version, strict capability defaults).
        -   `src/main.cx` (canonical CoreX v1.0 entry point).
        -   `.gitignore` (`build/`, `.corex-cache/`).
        -   `.gitattributes` containing `*.cx linguist-detectable=true` plus a temporary syntax-highlighting fallback (`*.cx linguist-language=Rust`) so early adopters get readable GitHub diffs immediately before `github-linguist/linguist` merges native CoreX support.
2.  **`corex doc` Structured Documentation Generator:**
    -   Reuses the canonical `CompilerDb` lossless CST/AST + `TypeChecker` + `FnRegionSummary` pipeline so every documented function automatically displays its exact canonical signature, default parameters, `/` and `*` parameter zones, `@no_alloc` / `@no_panic` / `@max_stack` contracts, and inferred capabilities (`fs`, `net`, `alloc`, `ffi`) without manual repetition.
    -   Supports `--format=json` (consumed by `corex-lang/website` to render searchable static API pages) and `--format=md` (for offline/LLM-friendly package docs).
3.  **Final `v0.0.1` Benchmark & Footprint Audit:**
    -   Execute the full `bench` suite on the self-hosted `v0.0.1` binary across Linux, macOS, Windows, and `wasm32`, recording verified numbers for `benchmarks.json` and confirming the `< 1 MB` compressed toolchain distribution budget.

---

## 3. Stage `L1` – Editor Polish, PrettyLights Verification & Marketplace Publishing (`vscode-ext-corex`)

The core extension (`syntaxes/corex.tmLanguage.json`, `language-configuration.json`, and the `corex lsp` / `corex fmt` client inside sibling workspace `../vscode-ext-corex`, modeled strictly after `xulbux/vscode-theme-isolux` and `xulbux/vscode-ext-color-tracr` and their `.agents/` rules/skills) is built and dogfooded locally starting in [`PLAN.md`](../PLAN.md) **`Phase 10.5`** so `Phase 11` (`stdlib/cx/*.cx`) and `Phase 12` (`compiler/*.cx`) are authored with full IDE support. Because GitHub's web code viewer (**PrettyLights**) highlights `.cx` files and ```` ```cx ```` Markdown blocks purely via static **TextMate regular expressions** without running `corex lsp`, Stage `L1` performs final grammar verification, branding polish, and public Marketplace release:

1.  **v1.0 TextMate Grammar & Release Binary Audit (`corex.tmLanguage.json` & `src/extension.ts`):**
    -   Verify complete scope coverage across all 120 `TokenKind`s and 70 keywords/primitives locked in `DR-22` (plus any standard-library attributes finalized in `Phase 11`–`12`):
        -   Control, declaration, ownership, and boolean keywords (`fn`, `struct`, `enum`, `bit_field`, `trait`, `impl`, `subscript`, `yield`, `use`, `pub`, `own`, `with`, `context`, `orelse`, `is`, `and`, `or`, `not`, `async`, `await`, `test`, `bench`, `unsafe`, `comptime`).
        -   All 20 built-in primitives (`i8`–`i128`, `u8`–`u128`, `isize`, `usize`, `f32`, `f64`, `bool`, `char`, `str`, `unit`, `never`, `opaque`) and built-in Constrained Type Groups (`Number`, `Integer`, `Signed`, `Unsigned`, `Float`, `Scalar`, `Bytes`).
        -   `PascalCase` nominal types/variants (`entity.name.type.corex`), `SCREAMING_SNAKE_CASE` constants (`constant.other.caps.corex`), `@attribute` annotations (`punctuation.definition.annotation.corex` + `storage.type.annotation.corex`), and `:label` / `label:` loop and `match` labels (`entity.name.label.corex`).
        -   Single-line `"…"`, indent-stripped multiline `"""…"""`, raw `r#"…"#` / `r#"""…"""#`, byte `b'x'` / `b"…"` / `br#"…"#`, nested `{expr=:#06x}` string interpolation holes, `{{` / `}}` brace escapes, and `_`-separated numeric suffixes (`0x4358_u32`, `0.5_f32`).
    -   Update default `corex` binary discovery to prioritize the installed `v0.0.1` toolchain (`PATH` and `~/.corex/bin/corex`) while keeping workspace `build/` overrides for compiler contributors.
2.  **Local PrettyLights Verification (`@wooorm/starry-night`):**
    -   Render `core/**/*.cx`, `stdlib/cx/**/*.cx`, `compiler/**/*.cx`, and all [`docs/COMPARISONS.md`](COMPARISONS.md) showcase snippets through `@wooorm/starry-night` locally across GitHub Light, Dark, and High-Contrast palettes to verify crisp highlighting before publishing.
3.  **Dual Marketplace Publishing:**
    -   Add final release branding (official CoreX icon, marketplace `README.md` and `CHANGELOG.md` matching `xulbux/vscode-theme-isolux` and `xulbux/vscode-ext-color-tracr` quality standards) and publish `vscode-ext-corex` publicly to both the **Visual Studio Marketplace** (`code --install-extension`) and **OpenVSX** (serving Cursor, Antigravity, Windsurf, VSCodium, and Eclipse Theia users out of the box).

---

## 4. Stage `L2` – Website & Zero-Install WASM Playground (`corex-lang/website`)

Most developers discovering a new systems language on Hacker News, Reddit, or Lobste.rs decide within 15 seconds whether to bounce or explore further. `corex-lang/website` must prove CoreX's engineering value interactively before asking anyone to install a binary.

1.  **Hero Section & Interactive Comparison Switcher:**
    -   Above-the-fold one-line value proposition, single-command copyable installer (`sh` / `pwsh` / `brew` / `scoop`), and an interactive tabbed code comparison (`vs. Rust`, `vs. C`, `vs. Zig`, `vs. Go`, `vs. Python`) sourced from [`docs/COMPARISONS.md`](COMPARISONS.md).
2.  **Zero-Backend Client-Side WASM Playground (`/play`):**
    -   Loads `corex-playground.wasm` inside a dedicated browser Web Worker (zero server compute, immune to traffic spikes, works offline after initial load).
    -   **Live Output Tabs:**
        -   **Run (`MirVm`):** Executes `main()` deterministically in `< 5 ms` and streams `stdout` / panic traces with `@caller_location()` source lines.
        -   **Diagnostics & SAST:** Renders CoreX's exact ANSI + Unicode box-drawing diagnostics (`╭─▸`, underline spans, and clickable `Apply SuggestedFix` buttons for `E0xxx`/`W0xxx`).
        -   **Inspect (`MIR` / `C99` / `Fmt`):** Lets systems engineers inspect generated `-ofmt=c` output, Drop/Move elaboration, and `corex fmt` canonicalization live.
    -   **Curated Preset Dropdown:** 10–12 interactive examples demonstrating compile-time UAF/OOB prevention, zero-annotation MVS partial moves, `T!E` + `is` + `:=` ergonomics, `@no_alloc` stack `FmtArgs`, `@trusted` C FFI SAST spatial/NUL contracts, `cx.async.task_group` structured concurrency, `@builder` declarative trees, `subscript`/`yield`, and `fsm: match` state machines, plus compressed URL-hash snippet sharing.
3.  **Documentation & Migration Guides (`/docs` & `/api`):**
    -   *5-Minute Quickstart* (`install` → `corex init` → `corex run` → `corex test`).
    -   *CoreX Language Tour* (structured walkthrough of types, MVS ownership, `T!E`/`T?`, generics & Type Groups, C FFI, concurrency, and `comptime`).
    -   *5-Minute Cheat Sheets* (*CoreX for Rustaceans*, *CoreX for C/Zig Programmers*, *CoreX for Go/Python Developers*).
    -   *`cx.*` Standard Library Reference* rendered automatically from `cx-api-docs.json`.

---

## 5. Stage `L3` – Zero-Friction Cross-Platform Distribution, Anti-Backdoor CI & Provenance

Author `.github/workflows/{ci,release}.yml` here (right before the Stage `L4` orphan squash so the public GitHub Actions tab contains zero pre-squash Stage-0 commits) and build every public release strictly inside ephemeral GitHub Actions runners triggered by signed `v*` tags – never on a local developer machine:

1.  **Automated Release Matrix & Anti-Backdoor Bootstrap Gates (`.github/workflows/release.yml`):**
    -   Produces stripped, deterministic `< 1 MB` `.tar.zst` / `.zip` bundles for:
        -   `x86_64-linux-musl` & `aarch64-linux-musl` (zero-dependency static binaries),
        -   `x86_64-apple-darwin` & `aarch64-apple-darwin` (signed/notarized or ad-hoc signed),
        -   `x86_64-windows-msvc` & `aarch64-windows-msvc`.
    -   **Gate A – Zero-Download Cold Bootstrap (`bootstrap.c`):** Never downloads an external `corex` binary from the network; cold-bootstraps strictly from the tagged Git commit (`bootstrap.c` + `stage1/corex1.wasm.zst` → `corex1` → `corex2` → `corex3` → `corex4` with `SOURCE_DATE_EPOCH=0`) and aborts unless `SHA-256(corex3) == SHA-256(corex4)`.
    -   **Gate B – Dual-Compiler Diverse Double-Compiling (`gcc` vs. `clang`):** Runs two isolated bootstrap jobs using independent system C compilers (Job A via `gcc`, Job B via `clang`) to cross-compile the deterministic release artifacts, asserting **bit-for-bit `SHA-256` identity** across both lineages before any asset can be published (defeating single-compiler *Trusting Trust* backdoors and hidden build nondeterminism).
    -   **Gate C – SLSA Provenance & Least-Privilege Publishing:** Runs all build/verification jobs with read-only `contents: read` permissions, handing verified artifacts to a minimal isolated publish job (`contents: write`, `attestations: write`, `id-token: write`) that generates `SHA256SUMS.txt` and cryptographic GitHub/Sigstore build-provenance attestations (`actions/attest-build-provenance`).
2.  **One-Line Installers & Package Managers:**
    -   POSIX shell installer (`curl -fsSL https://corex-lang.org/install.sh | sh`) and Windows PowerShell installer (`irm https://corex-lang.org/install.ps1 | iex`).
    -   Package manager manifests updated automatically on release tag:
        -   **Scoop:** `corex-lang/scoop-bucket` (`scoop bucket add corex … && scoop install corex`).
        -   **Homebrew:** `corex-lang/homebrew-tap` (`brew install corex-lang/tap/corex`).
        -   **Arch Linux AUR:** `corex-bin` `PKGBUILD`.
        -   **WinGet:** `CoreX.CoreX` manifest submission.
3.  **CI Action (`corex-lang/setup-corex`):**
    -   Enables any GitHub repository to run `corex fmt --check`, `corex check`, and `corex test` in GitHub Actions with caching out of the box.

---

## 6. Stage `L4` – Pre-`v0.0.1` Repository Audit, History Squash & Tagging Gate

Before publishing `v0.0.1` or announcing CoreX publicly, collapse the development/agent commit log into a spotless initial release history while preserving intentional project files.

### Step 1: Pre-Squash File Retention & Stage-0 Archive Checkpoint

Decide explicitly at the `v0.0.1` release boundary how internal engineering documents should be arranged, and preserve a local/private archive of the pre-squash bootstrap history:

-   **Archive Pre-Squash History Locally (Off Public Remote):** Save an offline Git bundle (`../corex-pre-v0.0.1-archive.bundle`, supplementing the `Phase 12.7` `../corex-stage0-zig-archive.bundle`) on local/private storage before force-pushing `clean-main` so the entire Stage-0 Zig bootstrap history remains privately inspectable forever without appearing in public GitHub commit graphs.
-   **Keep in `corex-lang/corex`:** Self-hosted source code (`compiler/`, `stdlib/`, `core/`, `tests/`, `bench/`), zero-Zig C99 offline bootstrap seed (`bootstrap.c` and `stage1/`), `README.md`, `CHANGELOG.md`, `LICENSE*`, `.markdownlint.json`, and `.agents/` (rules and skills intentionally retained).
-   **Decide at `v0.0.1` Gate (`PLAN.md`, `docs/LAUNCH.md`, `docs/COMPARISONS.md`, `docs/research/DR-01.md`–`DR-22.md`):**
    -   *Option A (Keep in `docs/`):* Systems programmers on Hacker News and Lobste.rs strongly respect deep architectural RFCs (`DR-01`–`DR-22`); keeping them in `docs/research/` proves serious compiler engineering rigor.
    -   *Option B (Move to `corex-lang/rfcs`):* Move completed design/planning docs into a dedicated `corex-lang/rfcs` repository if you want the main `corex` tree focused exclusively on code and user docs.

### Step 2: Clean Orphan-Branch Squash Procedure

Execute this procedure **before** cutting any Git tags or GitHub Releases (since GitHub keeps commits reachable via tag URLs even after force-pushing `main`) and coordinate with collaborators before they open local branches or forks:

```bash
# 0. Save an offline local Git bundle of the full pre-squash history:
git bundle create ../corex-pre-v0.0.1-archive.bundle --all

# 1. Verify 100% clean build, 3-stage self-host SHA-256 identity, and test/lint gates:
corex fmt --check .
corex check .
corex test
npx markdownlint-cli2 "**/*.md"

# 2. Create a fresh rootless orphan branch from the verified working tree:
git checkout --orphan clean-main
git add -A
git commit -m "Release CoreX v0.0.1"

# 3. Replace local main and force-push the clean single-commit root (admin bypass):
git branch -D main
git branch -m main
git push --force origin main

# 4. Cut and push the signed v0.0.1 tag ONLY after the clean root is live on origin:
git tag -a v0.0.1 -m "CoreX v0.0.1"
git push origin v0.0.1
```

---

## 7. Stage `L5` – Wave 1 Launch & "Trojan Horse" Developer Tool Strategy

Posting *"I built a new programming language"* in isolation invites bikeshedding; launching **real, fast open-source software written in CoreX** alongside concrete engineering write-ups converts skeptics into users.

1.  **Ship One Focused Flagship CLI / TUI / C-FFI Developer Utility in `.cx`:**
    -   Pick a sharp, everyday developer utility where `< 1 ms` startup, zero GC pauses, and monochrome Unicode terminal UX shine immediately (e.g., an interactive binary/ELF/PE/WASM size & symbol profiler, a blazing-fast structured log/JSON query TUI, a Git stack/diff tool, or a lightweight graphical inspector built on `SDL3`/`Sokol` + `Clay` via Phase 8 C FFI).
    -   **Dotfiles Multiplier:** Make the tool **configurable via `~/.config/<tool>/config.cx`** (evaluated safely via CoreX's capability-sandboxed subset or compiled on change into `~/.cache/`). Every power user who versions their dotfiles on GitHub automatically creates a non-fork public repository containing `.cx` files.
2.  **Lead With Deep Technical Engineering Posts (Not Marketing Hype):**
    -   Publish 2–3 focused engineering articles with side-by-side code, assembly, and reproducible benchmarks:
        -   *Show HN: CoreX – Zero-GC systems language with compile-time memory/bounds proofs and zero lifetime annotations* (linking straight to the zero-install WASM playground).
        -   *How CoreX eliminates bounds checks and use-after-free in O(V) without Rust lifetime parameters* (`r/ProgrammingLanguages`, Lobste.rs).
        -   *Show HN: `<ToolName>` – A sub-millisecond `<utility>` written in CoreX*.
3.  **Seed Early Ecosystem Repositories:**
    -   Publish 4–6 clean, focused wrapper packages under `corex-lang` or personal repos (`raylib-cx`, `sdl3-cx`, `sqlite-cx`, `zstd-cx`) consumable via direct Git URL imports (`corex.toml` and `use "github.com/…@v1.0.0" as …;`, `[Live]` in Stage 0), demonstrating effortless C library wrapping for early contributors.
    -   Promote the 4 **GitHub Template** starter repos (`corex-starter`, `corex-cli-starter`, `corex-aoc-starter`, `corex-c-interop-starter`) in the Quickstart guide so every tutorial reader clicks **Use this template** instead of **Fork**.

---

## 8. Stage `L6` – Reaching `>= 200` Public Repos & `github-linguist/linguist` PR

GitHub Linguist requires a language extension to have **at least 200 unique public non-fork repositories** on GitHub (`extension:cx` filtered to CoreX) before merging syntax highlighting and language-bar recognition.

1.  **Tracking the 200-Repo Threshold:**
    -   Monitor public GitHub code search (`path:*.cx "pub fn"` or `path:*.cx "use cx."` excluding forks) until unique repository count comfortably exceeds `220–250` repositories (providing margin above Linguist's 200-repo floor during review).
2.  **Disambiguating `.cx` in Linguist Heuristics:**
    -   Check whether any legacy language in Linguist's `languages.yml` claims `.cx`; add deterministic `heuristics.yml` rules matching CoreX signatures (`^\s*(pub(\((pkg|super)\))?\s+)?(fn|struct|enum|bit_field|trait|impl|subscript|use|mod|test|bench)\b`, `:=`, `->`, `@(cfg|derive|no_alloc|no_panic|inline)\b`).
3.  **Submitting the `github-linguist/linguist` Pull Request:**
    -   Add `CoreX` to `lib/linguist/languages.yml` using CoreX's official primary brand indigo **`#6352FF`** (`type: programming`, `color: "#6352ff"`, `extensions: [".cx"]`, `tm_scope: "source.corex"`, `ace_mode: "text"`, `codemirror_mode: "clike"`).
    -   Run `script/add-grammar https://github.com/corex-lang/vscode-ext-corex` to vendor the MIT-licensed grammar submodule into `vendor/grammars/`.
    -   Add representative `.cx` sample files under `samples/CoreX/` and unit tests verifying heuristic classification.
4.  **Post-Merge Cleanup:**
    -   Once GitHub deploys the new Linguist release, remove the temporary `.gitattributes` `linguist-language=Rust` fallback from `corex init` and the starter templates so GitHub displays **CoreX** natively in repository language bars.

---

## 9. Stage `L7` – Wave 2 (`0.x` → `v1.0.0`): Native `cx.tui` & GPUI-Style `cx.ui`

Once `v0.0.1` is live and gathering real-world feedback, [`PLAN.md`](../PLAN.md) `Phase 13.0`–`13.4` unlocks a second major adoption wave without delaying initial launch:

1.  **Stateful Sub-Millisecond Live Reloading (`Phase 13.0`):** Showcase video + playground demo of `corex run --watch` patching running native x86_64/ARM64 code in `< 5 ms` while preserving live application state across frames.
2.  **120fps `cx.tui` (`Phase 13.3`) & Hardware-Accelerated GPUI-Style `cx.ui` (`Phase 13.4`):** Combine `@constructor` / `@builder` (`SE-22`) declarative UI trees with direct `MIR → SPIR-V / WGSL` `@gpu_kernel` shaders to build a flagship cross-platform GPU-accelerated developer application in pure `.cx` – serving as the marquee showcase for **`CoreX v1.0.0`**.

# CoreX Advantages & Language Comparison Catalog

This document is the canonical Single Source of Truth (SSOT) cataloging **CoreX's concrete technical, safety, performance, tooling, and ergonomic advantages** over existing mainstream languages (**C**, **C++**, **Rust**, **Zig**, **Go**, and **Python**).

It serves two roles:

1.  **Engineering Source Pool for `corex-lang/website`:** Landing-page comparison tabs, interactive WASM playground presets, migration cheat sheets, and launch write-ups pull their strongest claims and side-by-side code directly from this catalog.
2.  **Living Capability Ledger:** Whenever a phase adds or upgrades a language feature, static analysis pass, CLI capability, or runtime guarantee, update this document (and flip milestone tags from `[Phase 8–12]` / `[Phase 13]` to `[Live]`) so website copy always reflects exact shipped behavior without exaggeration.

---

## 1. CoreX in One Sentence

**CoreX delivers C/Zig runtime speed and `< 1 MB` binary/toolchain minimalism, Rust-grade compile-time memory and bounds safety without `'a` lifetime annotations, and Python/Swift-grade readability and micro-ergonomics – in a single zero-GC, zero-legacy toolchain.**

---

## 2. Cross-Language Capability Matrix

Status legend inside CoreX cells: **`[Live]`** = implemented and verified in `stage0/` + `core/` + `vscode-ext-corex` (`Phases 0–10.6`); **`[v0.0.1]`** = scheduled in `Phases 11–12` prior to initial release; **`[0.x]`** = scheduled in `Phase 13.0–13.4` prior to `v1.0.0`.

| Dimension | CoreX | Rust | Zig | C23 / C++23 | Go | Python |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Memory Safety Without GC** | **Yes** (`Copy` / `AutoDrop` / `@linear` MVS + MIR SAST) `[Live]` | **Yes** (Borrow checker) | Manual (debug checks only) | Manual / partial RAII (UB-prone) | GC-managed | GC + refcount |
| **Lifetime Annotation Burden** | **Zero** (interprocedural Tarjan SCC inference) `[Live]` | High (`'a`, `'b`, HRTB `for<'a>`, Pin) | None (unchecked pointers) | None (unchecked pointers/refs) | None (heap escape + GC) | None (GC) |
| **Compile-Time Bounds-Check Elimination** | **Built-in Pentagon + `Intv` proof engine (`E0307` on static OOB)** `[Live]` | Relies on LLVM optimizer; runtime panic otherwise | Runtime check in Safe modes; UB in Fast | Unchecked (silent OOB UB) | Partial; runtime panic otherwise | Runtime `IndexError` |
| **Must-Consume Linear Types (`@linear`)** | **Native** (`E0304` across all normal/error/`defer` paths) `[Live]` | Workarounds only (`#[must_use]` allows `let _ = x; drop`) | No | No | No | No |
| **Static `@no_alloc` / `@no_panic` / `@max_stack(N)` Proofs** | **Built-in call-graph verifier + counterexample trace** `[Live]` | External hacks (`no_std` / symbol linker tricks) | Partial / manual | No | No | No |
| **Supply-Chain Capability Sandboxing** | **Lockfile-enforced (`fs`, `net`, `process`, `env`, `ffi`, `unsafe_op` per pkg)** `[Live]` | None (`build.rs` / proc-macros run arbitrary code) | Build runner sandboxing partial | None | None | None (`setup.py` / arbitrary imports) |
| **Error Handling ABI** | **`T!E` zero-branch register return (`swiftcc` + `swifterror`)** `[Live]` | Stack/register `Result<T, E>` enum | Error union `E!T` | Exceptions (slow unwind) or `errno` | Multi-return `(T, error)` + `if err != nil` | Exceptions |
| **Zero-Alloc Formatted Panics & Strings** | **8-byte `FmtSpec` + stack `FmtArgs` + `{x=}` (`0` heap allocs)** `[Live]` | `format_args!` (verbose macros, separate `{:?}`/`{}`) | `std.fmt` comptime format strings | `printf` (unsafe) / `std::format` (heavy) | `fmt.Sprintf` (heap/reflection) | `f"{x=}"` (heap-allocated) |
| **C Header Interop (`@c_import`)** | **Built-in zero-`libclang` C11/C23 translator + FFI SAST contracts** `[Live]` | External `bindgen` + `libclang` + `unsafe` everywhere | Built-in `@cImport` (bundles heavy `libclang`) | Native | `cgo` (high call overhead) | `ctypes` / `cffi` (runtime overhead) |
| **Zero-SDK Cross-Compilation & Wasm** | **11 targets + embedded `lld` + `.def`→`.lib` + `< 10 KB` `.wasm`** `[Live]` | Needs target linkers / MSVC SDK / `wasm-bindgen` | Built-in (`~45–50 MB` compiler archive) | Per-target cross-SDKs & sysroots | Built-in (`2–10 MB+` `.wasm` / binaries) | Interpreter / heavy bundlers |
| **Structured Concurrency & Frame Caps** | **`<= 16 KiB` stackless `async`/`await` + `@linear` `TaskGroup` (`E0309`, `E0317`)** `[Live]` | Unstructured `tokio::spawn` + `Pin<&mut Self>` + `'static` | Rebuilding `Io` interface (no `async`/`await`) | `std::coroutine` (heap HALO lottery, no race proofs) | Unstructured goroutines (GC + data races) | `asyncio` (slow, unverified cancellation) |
| **Compile-Time Execution (`comptime`)** | **Hermetic `MirVm` with spatial/temporal provenance & step caps** `[Live]` | Restricted `const fn` + slow proc-macros | Unrestricted `comptime` (no fuel/sandbox cap by default) | `constexpr` / template metaprogramming | None (`go generate`) | Import-time execution |
| **Built-In Deterministic `--sim` & `--fuzz`** | **First-class `test` / `bench` + `--sim --seed` + `--fuzz`** `[Live]`/`[v0.0.1]` | External crates (`cargo-fuzz`, `loom`, `turmoil`) | `std.testing.fuzz` (no virtual-time sim) | External (`libFuzzer`, custom harnesses) | `go test -fuzz` (no deterministic sim) | `hypothesis` / `atheris` |
| **Installed Toolchain Footprint** | **`< 1 MB` self-hosted binary + tree-shaken `cx.*` stdlib** `[v0.0.1]` | `~800 MB–1.5 GB` (`rustup` + `rustc` + `cargo` + std rlibs) | `~45–50 MB` compressed (`libclang`/C++ headers) | `~500 MB–2 GB` (Clang/GCC/MSVC SDKs) | `~70–150 MB` | `~50–120 MB` |
| **Dev Rebuild & Stateful Hot-Reload** | **Incremental `CompilerDb` + `< 10 ms` `corex lsp` `[Live]` + `< 5 ms` `--watch` `[0.x]`** | Slow (`cargo check` / `rust-analyzer` RAM bloat) | Fast incremental builds under active work | Slow header reparsing / `clangd` index lag | Fast (`go build` / `gopls`) | Instant startup, slow runtime |
| **Legacy Syntax Baggage** | **Zero** (`corex fmt` + `corex upgrade` 3-tier CST/type rewriter) `[Live]` | Editions accumulate (`2015`–`2024`, async/pin tech debt) | Pre-1.0 churn (manual upgrades) | 40+ years of legacy footguns | Minimal (`gofmt` / `go fix`) | Python 2→3 scars, typing legacy |

---

## 3. CoreX's Signature Innovations (What Sets CoreX Apart Globally)

### 3.1 Zero-Annotation Memory Safety + True `@linear` Obligations (`[Live]`)

-   **Three-Tier Ownership (`Copy`, `AutoDrop`, `@linear`):** Values are `Copy` when bitwise trivial, `AutoDrop` when owning heap/OS resources with deterministic scope-exit cleanup, or `@linear` when silent dropping is itself a bug (e.g., uncommitted database transactions, active `TaskHandle[T]`s, capability tokens, hardware DMA leases).
-   **Ownership-Transparent Call Sites (`ADR-22B`):** Signatures and call sites agree visually without hidden C++ copies or Rust lifetime puzzles:
    -   `x: T` (requires `T: Copy`; callee-mutable via `var x: T`),
    -   `x: &T` / `x: &mut T` (shared or exclusive borrow; call sites pass `&x` / `&mut x`),
    -   `x: own T` (explicit ownership transfer; call sites write `own x`, emitting `E0420` with auto-fix if omitted on named variables),
    -   `x: &out T` (write-only uninitialized out-parameter verified definitely initialized before return via `E0422`, eliminating redundant zeroing of large buffers).
-   **Zero Lifetime Parameters:** Interprocedural region and escape summaries (`FnRegionSummary`, `40 B`) are inferred bottom-up across Tarjan strongly connected components. Users never write `'a`, `'b`, or `<'ctx>` on structs or functions.

### 3.2 Compile-Time Bounds Proofs & `$` End-Relative Indexing (`[Live]`)

-   CoreX runs a linear-time `Intv` interval pass paired with a Demand-Sliced Sparse ABCD **Pentagon** relational solver (`< 1.5 MB` scratch cap) directly on `MIR`.
-   Provably out-of-bounds accesses fail **at compile time** (`E0307`) rather than crashing in production, while provably in-bounds loops and backward slice indexing (`buf[$ - 1]`, `buf[1..$ - 1]`) have their runtime bounds checks **statically eliminated** and export LLVM `!range` metadata for auto-vectorization.

### 3.3 Call-Graph Capability Inference, Hard Real-Time Contracts & Supply-Chain Sandboxing (`[Live]`)

-   Every function automatically receives a compiler-inferred 16-bit `EffectCapabilityMask` (`fs`, `net`, `env`, `process`, `ffi`, `unsafe_op`, `alloc`, `may_panic`) and stack-frame summary (`own_frame_bytes`, `max_subtree_bytes`).
-   Annotating an audio callback, interrupt handler, kernel path, or parser hot loop with `@no_alloc`, `@no_panic`, `@no_block`, or `@max_stack(4096)` statically proves the entire transitive call graph obeys that contract – emitting the **shortest violating call-chain witness** (`E0316`, `E0320`–`E0322`) when violated.
-   `corex.toml` (`allow_caps`, `default_dep_policy = "zero_trust"`) and `corex.lock` (`max_caps`, `cxi_blake3`) enforce compile-time supply-chain sandboxing across every dependency, `impl Drop` destructor, inactive `@cfg` branch, and `.cxtree`-jailed `@embed_bytes` / `@c_import` asset (`E0324`, `E0326`, `E0327`, `W0330`) – rejecting capability escalation or transitive capability laundering **at compile time** before a single test runs.

### 3.4 Zero-Branch `T!E` Error Handling & `@derive(From)` (`[Live]`)

-   `T!E` (`Result[T, E]`) and `T?` (`Option[T]`) compose naturally via 4-tier right-recursive precedence (`*u8?` = optional pointer; `&[u8]!IoError` = fallible byte-slice borrow).
-   On native targets (`x86_64`, `aarch64`), `cx_result_cc` lowers `T!E` onto `swiftcc` + `swifterror` dedicated error registers (`R12` / `X21`), turning the happy path of `expr?` into a single register test with zero stack-spill overhead and zero C++ DWARF unwind tables.
-   `@derive(From)` on an error `enum` automatically synthesizes unambiguous `FromError` conversions for single-field variants (`E0427` on ambiguity), eliminating Rust's repetitive `impl From<IoError> for AppError` boilerplate.

### 3.5 Constrained Type Groups & Inline Union Bounds (`[Live]`)

-   Instead of C++ template duck-typing walls or verbose Rust trait bounds (`fn scale<T: Copy + Add<Output = T> + Mul<Output = T>>(a: T, b: T) -> T`), CoreX provides 12 built-in $O(1)$ bitmask **Constrained Type Groups** (`Number`, `Integer`, `Signed`, `Unsigned`, `Float`, `Scalar`, `Bytes`, `FromBytes`, `IntoBytes`, …), user-defined type groups (`type WireScalar = u8 | u16 | u32 | u64;`), and PEP 695-style **inline union bounds** (`pub fn parse_header[Data: str | &[u8]](input: Data)`).
-   `distinct` nominal types (`pub type UserId = distinct u64;`) isolate units and IDs at zero runtime cost (`E0405`), `@secret` enforces constant-time discipline (`Phase 13.1`), and `is` range refinements (`pub type Port = u16 is 1..=65535;`) catch out-of-range constants and unverified casts (`E0406`).

### 3.6 Python-Grade Ergonomics With Zero Runtime Cost (`[Live]`)

CoreX systematically adopts the highest-leverage ergonomic wins from Python, Swift, and modern ML languages – redesigned to compile to 100% static, zero-allocation machine code:

-   **Flow-Sensitive `is` / `is not` & Positive-Spine Walrus `:=` (`SE-01`, `SE-02`):** `if (pkt := next_packet()) is .Some(header) and header.tag == 1 { … }` binds and narrows types down positive `and` chains with automatic reverse-LIFO cleanup before `else` – retiring `if let` / `while let` ceremony.
-   **PEP 570 `/` & PEP 3102 `*` Parameter Zones + Named/Default Arguments (`SE-07`, `SE-11`):** `pub fn open(path: str, /, *, read: bool = true, create: bool = false) -> File!IoError` prevents boolean-trap call sites (`open("a.txt", read: true)`) while keeping positional-only parameters free to rename without breaking callers.
-   **Zero-Alloc `{expr=}` Debug Interpolation & `"""…"""` Multiline Strings (`SE-12`, `SE-13`):** `"state: {count=}, {mask=:#010x}"` parses format specs at compile time into 8-byte `FmtSpec` descriptors; when passed to `FmtArgs` consumers (such as `@panic("bad {code=:#06x}")` or `cx.panic.assert_true`), arguments stay on the stack with **zero heap allocation**. Swift-style `"""…"""` strips indentation relative to the closing `"""`.
-   **Zero-Call `subscript` + `yield` Accessors (`SE-21`):** `pub subscript(row: usize, col: usize) -> T { let { yield … } inout { yield &mut … } }` compiles multi-dimensional indexing (`grid[r, c] += 1`) directly into inlined pointer projections with SAST post-`yield` writeback safety – avoiding Rust's split `Index` / `IndexMut` traits that cannot return computed views or guard invariants after mutation.
-   **`@constructor` & `@builder` Trailing Blocks (`SE-22`):** Enables SwiftUI/Kotlin-clean declarative DSLs (`Row(gap: 8) { Button("Save"); }`) that desugar to flat sequential `&mut Scope` calls with zero vtables or temporary VDOM heap trees.
-   **Labeled `fsm: match` State-Machine Loops (`SE-23`):** `fsm: match state { .Idle => continue :fsm .Header, … }` compiles protocol parsers, lexers, and bytecode VMs directly into tail-dispatched CFG jump blocks without `loop { match … }` nesting.
-   **Simultaneous Tuple Swaps & Functional Struct Spread (`SE-14`, `SE-15`):** `(left, right) = (right, left);` executes in 3 interference-free phases, while `Config { port: 8080, ..base_cfg }` and `Packet { header: h, ..own prev_pkt }` enforce MVS partial-move and `@linear` leak laws statically.

### 3.7 Zero-`libclang` C11/C23 Interop, FFI SAST Contracts & 11-Target Cross-Compilation (`[Live]`)

-   **In-House C11/C23 Translator (`corex translate-c` & `@c_import`):** Preprocesses and translates C11/C23 headers directly into canonical `.cx` without bundling `libclang`, lowering `MSVC` vs. `SysV` / `AAPCS64` / `Wasm32` C bitfields into byte-exact `Prune-06` storage wrappers.
-   **Declarative FFI SAST Contracts:** `@null_terminated` (`E0308`), `@owned_by_caller` / `@free_with` / `@consumes` (`E0310`), `@may_be_null` / `@non_null` (`E0311`), `@slice_len` / `@byte_len` (`E0312` / `E0307` Pentagon proofs), and `@escapes` (`E0306`) turn unsafe C boundaries into compile-time-verified contracts.
-   **SDK-Less 11-Target Linking & `< 10 KB` Freestanding `wasm32`:** Emits Linux (`gnu`/`musl`), macOS (`x86_64`/`aarch64`), Windows (`msvc`/`gnu` with programmatic PE/COFF `.def` → Short-Import `.lib` synthesis), `wasm32-unknown-wasi`, and `< 10 KB` `wasm32-unknown-freestanding` artifacts with deterministic `K_GNU`/`K_BSD`/`K_COFF` archives.

### 3.8 `Pin`-Free `16 KiB` Stackless `async`/`await` & `@linear` `TaskGroup` Nurseries (`[Live]`)

-   **Zero-Heap-Per-Await State Machines (`E0317`):** `async fn` and `async` blocks lower into liveness-colored stackless frames with `FramePinned` interior-borrow stability (no `Pin<&mut Self>` boilerplate) and a static `<= 16 KiB` inline frame cap (`E0317`).
-   **Lexical `@linear` `cx.async.task_group` Nurseries (`E0309`):** Spawned `TaskHandle[T]` values are `@linear` obligations (`E0304` if forgotten on normal exit, automatically canceled and reaped on `?` error or parent cancellation), while SAST proves concurrent borrow exclusivity, `Send`/`Sync`/`@thread_local` safety, and zero parent-scope escapes (`E0309`).

### 3.9 Built-In `< 10 ms` Language Server, Capability Auditor & Zero-Legacy Migration Suite (`[Live]`)

-   **Sub-Millisecond `corex lsp` Over `CompilerDb` (`DR-12`, `DR-17`):** Built directly into the single `corex` binary with zero external daemons, delivering `< 10 ms` P99 keystroke-to-diagnostic, completion, semantic-token delta, hygienic cross-file rename, and `DR-17` hover cards showing inferred capabilities (`[fs, net, unsafe_op]` or `none (pure)`), `@no_alloc`/`@no_panic` verification status, and exact `@max_stack(N)` frame byte budgets on 100,000-LOC workspaces.
-   **Zero-False-Positive Linter & Supply-Chain Capability Auditor (`corex check`):** Unifies `W0202` idiom lints, `@deprecated(upgrade: "…")` (`W0403`) call-site rewrite templates, transactional `corex check --fix`, `--deny-warnings`, `corex check --caps` package capability matrices, and `corex check --explain-caps` shortest BFS call-chain witnesses.
-   **3-Tier Zero-Legacy `corex upgrade` Engine (`DR-14`, `UR-21-00`–`UR-23-06`):** Automatically rewrites legacy syntax, `TypeId`-resolved idioms, `@deprecated` / `@fix_inline` library calls, and `corex.toml` / `corex.lock` manifests (`--accept-caps` without ever overriding `deny_caps`) while preserving 100% of comments and rolling back atomically if syntax errors increase.
-   **Zero-Dependency `< 25 KB` Official VS Code & OpenVSX Extension (`vscode-ext-corex` `v1.0.0`):** Ships a non-backtracking CoreX v1.0 TextMate grammar (powering both offline editor highlighting and GitHub PrettyLights) paired with a zero-runtime-dependency `corex lsp` and `corex fmt` client featuring custom MVS/SAST semantic token modifiers (`mutable`, `consumedMove`, `unsafe`, `attribute`, `linearResource`) and Workspace Trust gating (`[Live]` locally; Marketplace release in Stage `L1`).

---

## 4. Head-to-Head Language Comparisons

### 4.1 CoreX vs. Rust

-   **Where Rust Hurts:** Steep learning curve around explicit `'a` lifetimes, `Pin<&mut Self>`, `Arc<Mutex<T>>` viral infectiveness, split `Index`/`IndexMut` and `Fn`/`FnMut`/`FnOnce` boilerplate, multi-minute clean/incremental link times, `1 GB+` toolchain disk footprint, arbitrary code execution in `build.rs` / proc-macros, and inability to express true non-droppable linear obligations (`std::mem::forget` is safe and `let _ = guard;` drops silently).
-   **How CoreX Wins:**
    -   **Zero `'a` lifetime annotations** via MVS + interprocedural region inference (`[Live]`).
    -   **True `@linear` types** that statically guarantee explicit consumption on every path (`[Live]`).
    -   **`Pin`-free stackless `async`/`await` (`<= 16 KiB` inline frame budget `E0317`) and `@linear` `cx.async.task_group` nurseries (`E0309`)** without `'static` or `Arc<Mutex<T>>` ceremony (`[Live]`).
    -   **Named arguments, default parameters, `/` and `*` parameter zones**, and **generic type defaults** (`[Live]`).
    -   **Built-in `@no_alloc` / `@no_panic` / `@max_stack(N)`** verification and **lockfile capability sandboxing** (`[Live]`).
    -   **Zero-`libclang` C header import** (`[Live]`), **hermetic `MirVm` `comptime`** instead of heavy proc-macro crates (`[Live]`), and a **`< 1 MB` self-hosted toolchain** (`[v0.0.1]`).
-   **Honest Scope Note:** Rust has a massive mature crates.io ecosystem today; CoreX bridges day-one library breadth via zero-ceremony C11/C23 FFI and direct Git URL / single-file `.cx` script package imports (`[Live]`).

### 4.2 CoreX vs. C & C++

-   **Where C / C++ Hurt:** Silent Use-After-Free, double-free, uninitialized stack reads, spatial buffer overflows, signed overflow UB, preprocessor macro traps, sluggish C++ header/template compilation, implicit copy-constructor landmines, and lack of a built-in package manager, formatter, test runner, or fuzz/sim harness.
-   **How CoreX Wins:**
    -   **Eliminates UAF, double-free, uninitialized reads (`&out` `E0422`), exclusivity bugs (`E0305`), and static OOB (`E0307`) at compile time** while keeping C-identical struct layout control (`@repr(C)`, `bit_field Name: u32 | [u8; N]`, `enum Name: u8`, `*opaque`) (`[Live]`).
    -   **Explicit `own` moves and `Copy`-gated value parameters (`E0420`, `E0421`)** eliminate hidden C++ copy constructors (`[Live]`).
    -   **All-in-one `< 1 MB` binary** (`build`, `run`, `test`, `bench`, `fmt`, `check`, `lsp`, `upgrade`, `translate-c`) replacing CMake + Ninja + clang-format + clang-tidy + AddressSanitizer + GoogleTest (`[Live]` / `[v0.0.1]`).

### 4.3 CoreX vs. Zig

-   **Where Zig Hurts:** No static memory/lifetime/UAF safety (spatial/temporal checks rely on runtime debug allocators and vanish in `ReleaseFast`), verbose `comptime T: type` generics with duck-typed instantiation errors, no operator overloading or `subscript` accessors for math/SIMD/matrix code, no closures, no default/named function arguments, and a `~45–50 MB` compiler archive due to bundled `libclang`/LLVM C++ headers.
-   **How CoreX Wins:**
    -   **Full compile-time memory, borrow, `@linear`, and Pentagon bounds verification** (`Release` builds stay memory-safe without runtime overhead) (`[Live]`).
    -   **Checked generics via Constrained Type Groups** (`[T: Float]`, `[Data: str | &[u8]]`) + **3-tier closures** (`fn`, `|…|`, `own |…|`) + **`subscript`/`yield`** + **named/default arguments** (`[Live]`).
    -   **In-house zero-`libclang` C11/C23 translator** (`[Live]`) keeping the entire CoreX toolchain **`< 1 MB`** (`[v0.0.1]`).
    -   **Implicit `context` (`context.allocator`, `context.rng`, `context.logger`) + `with context.allocator = arena { … }`** (`SE-08`) giving explicit allocator control without threading `allocator: Allocator` through every single function signature (`[Live]`).

### 4.4 CoreX vs. Go

-   **Where Go Hurts:** Garbage-collection latency spikes and `2–10x` memory overhead, repetitive `if err != nil { return nil, err }` noise (`40%+` of typical Go files), nil-pointer panics, data races (`go func()` without compile-time exclusivity), high `cgo` FFI call overhead, and multi-megabyte Hello World binaries.
-   **How CoreX Wins:**
    -   **Zero GC, deterministic `AutoDrop` / Arena memory, and C-level latency & binary sizes** (`[Live]`).
    -   **Eliminates nil panics (`T?` + `orelse` + `is`) and `if err != nil` walls (`T!E` + postfix `?` + `@derive(From)`)** (`[Live]`).
    -   **Structured `cx.async.task_group` (`TaskGroup[E]`) with compile-time data-race and escape prevention (`E0309`)** instead of leaked goroutines (`[Live]`).
    -   **Zero-overhead native C ABI calls** without `cgo` trampoline penalties (`[Live]`).

### 4.5 CoreX vs. Python

-   **Where Python Hurts:** `50–200x` slower execution, GIL/multiprocessing friction, runtime `TypeError`/`KeyError`/`AttributeError` surprises in production, fragile packaging/virtualenv sprawl, and inability to ship a tiny standalone native binary or `< 10 KB` WASM module.
-   **How CoreX Wins:**
    -   **Preserves the exact ergonomic features Python developers love most** – `and` / `or` / `not`, `(x := expr)` walrus bindings, `x is Pattern` / `is not`, `"{val=:#06x}"` self-documenting interpolation, `"""…"""` multiline strings, `/` and `*` keyword-only parameter zones, `= default` parameters, `[Data: str | &[u8]]` inline union bounds, and `[T = f64]` generic defaults – **compiled to 100% statically verified native machine code at C speed** (`[Live]`).
    -   **Ships zero-dependency standalone binaries across all 11 desktop/server targets and `< 10 KB` `wasm32-unknown-freestanding` modules** from a single command (`[Live]`).

---

## 5. Ready-to-Use Side-by-Side Showcases (Website & Playground)

### Showcase 1: Zero-Annotation Memory Safety vs. Rust Lifetime Clutter (`[Live]`)

Rust forces explicit lifetime parameters (`'a`) whenever helper functions or structs borrow slices; CoreX infers interprocedural borrow provenance automatically via `FnRegionSummary` and prevents dangling escapes (`E0306`) with zero annotations:

```rust
// Rust: lifetime annotations infect signatures and helper structs
pub fn longest_non_empty<'a>(primary: &'a str, fallback: &'a str) -> Option<&'a str> {
    if !primary.is_empty() {
        Some(primary)
    } else if !fallback.is_empty() {
        Some(fallback)
    } else {
        None
    }
}
```

```cx
// CoreX: identical zero-GC borrow safety, zero lifetime annotations
pub fn longest_non_empty(primary: str, fallback: str) -> str? {
    if not primary.is_empty() {
        return .Some(primary);
    } else if not fallback.is_empty() {
        return .Some(fallback);
    }
    return .None;
}
```

### Showcase 2: Compile-Time Bounds, `&out` & `@linear` Safety vs. C Bugs (`[Live]`)

In C, forgetting to close a descriptor, reading an uninitialized out-parameter, or indexing one element too far silently ships a CVE. CoreX catches all three **at compile time**:

```c
// C: compiles cleanly with -Wall; leaks tx on error, reads uninit out_crc, and OOBs on empty len
int process_frame(const uint8_t *buf, size_t len, uint32_t *out_crc) {
    TxHandle tx = begin_tx();
    if (len == 0) return -1;      // BUG 1: `tx` leaked on early return!
    uint8_t tail = buf[len];      // BUG 2: off-by-one out-of-bounds read!
    return (int)(*out_crc + tail); // BUG 3: `*out_crc` never initialized!
}
```

```cx
// CoreX: `@linear` enforces consumption (`E0304`), `$ - 1` is Pentagon-proven in-bounds,
// and `&out u32` proves definite initialization (`E0422`) before returning!
@linear
pub struct TxHandle {
    pub id: u64,
}

pub fn commit_tx(tx: own TxHandle) {
    let TxHandle { id } = tx;
    _ = id;
}

pub fn process_frame(buf: &[u8], out_crc: &out u32) -> u32!IoError {
    let tx = TxHandle { id: 1 };
    defer commit_tx(own tx); // Removing this line is a compile-time `E0304` error!

    if buf.is_empty() {
        out_crc.* = 0;
        return .Err(IoError { code: 1 });
    }
    let tail: u8 = buf[$ - 1]; // Statically proven `< buf.len()`; zero runtime bounds check!
    out_crc.* = tail as u32;   // Omitting `&out` initialization on any path triggers `E0422`!
    return .Ok(out_crc.*);
}
```

### Showcase 3: `T!E` + `@derive(From)` + `:=` + `is` vs. Go & Rust Boilerplate (`[Live]`)

```cx
@derive(From)
pub enum ConfigError {
    Io(IoError),
    Parse(ParseError),
    InvalidPort(u16),
}

pub fn load_endpoint(raw_env: str?, /, *, default_port: u16 = 8080) -> u16!ConfigError {
    let text = raw_env orelse return .Ok(default_port);
    let port = parse_u16(text)?; // `ParseError` lifts automatically via `@derive(From)`!
    if port == 0 {
        return .Err(.InvalidPort(port));
    }
    return .Ok(port);
}
```

### Showcase 4: `@no_alloc` + `@max_stack` + Zero-Alloc `{x=}` Diagnostics (`[Live]`)

```cx
// Statically proven: 0 heap allocations, <= 512 bytes stack across entire call graph!
@no_alloc @max_stack(512)
pub fn decode_register(raw_word: u32) -> u16 {
    let magic = raw_word >> 16;
    if magic != 0x4358_u32 {
        // Formatted `{magic=:#06x}` builds `FmtArgs` on the stack with ZERO heap allocation!
        @panic("corrupt hardware register header: {magic=:#06x}");
    }
    return (raw_word & 0xFFFF_u32) as u16;
}
```

### Showcase 5: Bit-Exact `bit_field` (`uN` & `[u8; N]`), `subscript`/`yield` & `fsm: match` (`[Live]`)

```cx
pub bit_field MacHeader: [u8; 6] {
    pub oui: u32 | 24,
    pub flags: u8 | 4,
    pub nic: u32 | 20,
}

pub struct Ring4[T = i32] {
    pub slots: [T; 4],
}

impl[T] Ring4[T] {
    // Zero-call projected accessor supporting both `ring[i]` reads and `ring[i] += 1` RMW:
    pub subscript(idx: usize) -> T {
        let {
            yield self.slots[idx % 4];
        }
        inout {
            yield &mut self.slots[idx % 4];
        }
    }
}

pub enum State: u8 {
    Start = 0,
    Body = 1,
    Done = 2,
}

pub fn scan_frames(bytes: &[u8]) -> usize {
    var cursor: usize = 0;
    var frames: usize = 0;
    fsm: match State.Start {
        .Start => {
            if cursor >= bytes.len() {
                continue :fsm .Done;
            }
            cursor += 1;
            continue :fsm .Body;
        },
        .Body => {
            frames += 1;
            continue :fsm .Start;
        },
        .Done => frames,
    }
}
```

### Showcase 6: Declarative `@constructor` & `@builder` Blocks Without VDOM Bloat (`[Live]`)

```cx
pub struct UiList {
    pub count: u32 = 0,
    pub total_weight: u32 = 0,
}

@builder_item
pub fn Item(list: &mut UiList, weight: u32 = 1) {
    list.count += 1;
    list.total_weight += weight;
}

@constructor
pub fn Section(
    title: str,
    /,
    @builder build_children: |&mut UiList| -> unit,
) -> UiList {
    _ = title;
    var state = UiList { .. };
    build_children(&mut state);
    return state;
}

pub fn build_toolbar() -> UiList {
    // Compiles to flat sequential stack mutations (`state.count == 3`, `total_weight == 7`):
    return Section("Actions") {
        Item(weight: 4);
        Item(weight: 2);
        Item();
    };
}
```

### Showcase 7: `@trusted` C FFI SAST Contracts & Structured `TaskGroup` Concurrency (`[Live]`)

```cx
use cx.async.{task_group, yield_now};
use cx.ffi.{CStr, c_int};

extern "C" {
    // Pentagon proves `len <= buf.len()` (`E0312` / `E0307`) and `CStr` proves NUL termination (`E0308`)!
    @trusted
    fn c_hash_named(@null_terminated tag: *u8, @slice_len(len) buf: *u8, len: usize) -> c_int;
}

pub async fn parallel_digest(label: CStr, payload: &[u8]) -> i32 {
    return task_group(|grp| {
        // `spawn_local` runs on the current thread (`CStr` + `&[u8]` safe); dual `&mut` or cross-thread `spawn` fails with `E0309`:
        let left = grp.spawn_local(own async {
            yield_now().await;
            c_hash_named(label.as_ptr(), payload.as_ptr(), payload.len())
        });
        let right = grp.spawn_local(own async {
            c_hash_named(label.as_ptr(), payload.as_ptr(), payload.len())
        });
        left.join().await + right.join().await
    }).await;
}
```

### Showcase 8: Zero-Friction Package Management & Supply-Chain Capability Sandboxing (`[Live]`)

```toml
# corex.toml – Bounded-MVS (`< 5 ms` cold resolve) + compile-time capability sandboxing:
[package]
name = "metrics-agent"
version = "0.1.0"
edition = "2026"
corex = "^0.1.0"

[security]
default_dep_policy = "zero_trust"

[dependencies]
# Pure parser granted `0` OS/FFI capabilities (network/fs/ffi/unsafe_op rejected with `E0324`!):
json-wire = { version = "1.4.0", allow_caps = [] }
# Linux-only ring transport gated by CoreX's single-form `@cfg` predicate syntax:
uring-net = { version = "0.3.0", target = "target.os == .Linux", allow_caps = ["net", "ffi", "unsafe_op"] }
```

```cx
#!/usr/bin/env corex
---
[dependencies]
json-wire = { version = "1.4.0", allow_caps = [] }
---
// Single-file `.cx` script (`corex script.cx`) locks out-of-tree under `<COREX_HOME>/target/scripts/<blake3>/`:
use json_wire.parse_counter;

pub fn main() -> i32 {
    return parse_counter(r#"{"ok":1}"#);
}
```

### Showcase 9: `@deprecated` Auto-Migration Templates & `corex check --caps` Auditing (`[Live]`)

```cx
// Library authors attach hazard-checked rewrite templates directly to `@deprecated`:
@deprecated(since: "0.2.0", reason: "use connect_timeout", upgrade: "connect_timeout($0, timeout_ms: 5000)")
pub fn connect_host(endpoint: str) -> i32 {
    return connect_timeout(endpoint, timeout_ms: 5000);
}

pub fn connect_timeout(endpoint: str, *, timeout_ms: u32 = 5000) -> i32 {
    _ = endpoint;
    return timeout_ms as i32;
}

// Running `corex check --fix` or `corex upgrade` rewrites `connect_host(addr)` ->
// `connect_timeout(addr, timeout_ms: 5000)` automatically when `$0` is pure and comment-free!
pub fn bootstrap_client(addr: str) -> i32 {
    return connect_timeout(addr, timeout_ms: 5000);
}
```

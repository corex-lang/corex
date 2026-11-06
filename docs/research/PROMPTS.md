# Upfront `Deep Research` Prompts (`DR-01`–`DR-15`)

This catalog contains the 15 self-contained, copy-pasteable `Deep research` prompts that resolve the Research Decision Gates (`RDG-01`–`RDG-15`) in [PLAN.md](../../PLAN.md). When a `Deep research` report is completed, save its output to the corresponding `docs/research/DR-XX.md` path listed below.

---

## Research Report Index

| Report ID   | Gate ID      | Target Report Path             | Blocking Phase   | Subsystem / Architectural Scope                                                          |
| ----------- | ------------ | ------------------------------ | ---------------- | ---------------------------------------------------------------------------------------- |
| **`DR-01`** | **`RDG-01`** | `docs/research/DR-01.md`       | Phase 0          | Bootstrap Implementation Language & Self-Hosting Strategy                                |
| **`DR-02`** | **`RDG-02`** | `docs/research/DR-02.md`       | Phase 2          | Programming Paradigm & Execution Semantics                                               |
| **`DR-03`** | **`RDG-03`** | `docs/research/DR-03.md`       | Phase 1 / 2      | Ergonomic Syntax, Delimiter Design & Naming Conventions                                  |
| **`DR-04`** | **`RDG-04`** | `docs/research/DR-04.md`       | Phase 4          | Static Type System, Constrained Type Groups & Zero-Overhead Inference                    |
| **`DR-05`** | **`RDG-05`** | `docs/research/DR-05.md`       | Phase 5          | Compile-Time Execution (`comptime`) & Metaprogramming Architecture                       |
| **`DR-06`** | **`RDG-06`** | `docs/research/DR-06.md`       | Phase 6          | Zero-GC Automatic Memory Management, Manual Control & SAST Verifier                      |
| **`DR-07`** | **`RDG-07`** | `docs/research/DR-07.md`       | Phase 4 / 6      | Error Handling Model & Zero-Cost Propagation Semantics                                   |
| **`DR-08`** | **`RDG-08`** | `docs/research/DR-08.md`       | Phase 8 / 11     | Concurrency, Async/Structured Execution & High-Throughput I/O Model                      |
| **`DR-09`** | **`RDG-09`** | `docs/research/DR-09.md`       | Phase 7          | Dual-Mode Compiler Backend Architecture (Instant Dev vs. Production AOT)                 |
| **`DR-10`** | **`RDG-10`** | `docs/research/DR-10.md`       | Phase 8          | Cross-Compilation, Zero-Dependency Linking, C FFI & WebAssembly (`wasm32`)               |
| **`DR-11`** | **`RDG-11`** | `docs/research/DR-11.md`       | Phase 9          | Package Manager, URL/Registry Resolution, Global Cache & Lockfiles                       |
| **`DR-12`** | **`RDG-12`** | `docs/research/DR-12.md`       | Phase 2 / 3 / 10 | Incremental Query Engine, Fault-Tolerant Lossless CST & Built-in LSP                     |
| **`DR-13`** | **`RDG-13`** | `docs/research/DR-13.md`       | Phase 5          | Intermediate Representations (`HIR` & SSA `MIR`) & Optimization Pipeline                 |
| **`DR-14`** | **`RDG-14`** | `docs/research/DR-14.md`       | Phase 3 / 10     | Zero-Legacy AST Migration Engine (`corex upgrade`) & Canonical Formatter (`corex fmt`)   |
| **`DR-15`** | **`RDG-15`** | `docs/research/DR-15.md`       | Phase 11         | Stage-2 `.cx` Standard Library, TUI/CLI & Unified WebAssembly/Native UI Architecture     |

---

## `DR-01` (Plugs into `RDG-01` → `docs/research/DR-01.md`): Bootstrap Implementation Language & Self-Hosting Strategy

````markdown
# Deep Research Request (DR-01): Optimal Bootstrap Implementation Language & Self-Hosting Architecture for CoreX (.cx)

## Context & Vision
I am building a new general-purpose systems and application programming language called **CoreX** (repository `corex-lang/corex`, file extension `.cx`, CLI binary `corex`):
> *"A streamlined, zero-GC, statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed."*

CoreX has an explicit milestone of **100% self-hosting** (rewriting the compiler, memory/SAST verifier, package manager, formatter, migration tool, and LSP in CoreX itself) prior to Version 1.0, after which it must no longer depend on any external host language.

## Research Objectives
Conduct an exhaustive, evidence-based engineering analysis to determine:
1. **Optimal Stage-0 Bootstrap Language:** Compare **C (C11/C23)**, **Rust**, **Zig**, and **C++20/23** as the implementation language for the Stage-0 bootstrap compiler (`stage0/corex`). Evaluate across:
   - Velocity and safety of implementing arena-allocated AST/HIR/MIR data structures, a path-sensitive static memory vulnerability verifier (SAST), and a fault-tolerant incremental parser.
   - Ease of integrating or interfacing with backend code generators (e.g., Cranelift, LLVM C/C++ APIs, QBE, or custom machine code emitters) and embedded linkers (`lld`, `mold`, or custom object emitters).
   - Cross-compilation ergonomics on Windows, Linux, and macOS hosts.
   - Ease of translating Stage-0 compiler modules 1-to-1 into `.cx` during the self-hosting rewrite.
2. **Self-Hosting Bootstrap Pipeline & Trust/Reproducibility Chain:**
   - Analyze how modern self-hosted compilers (Zig, Rust, Go, Nim, Vale, Odin, Hylo) solve the "chicken-and-egg" bootstrap problem across platforms.
   - Compare maintaining a small committed WebAssembly (`wasm32`) bootstrap seed binary (like Zig's `zig1.wasm` + tiny C Wasm2C interpreter) vs. a minimal C-transpilation backend in the self-hosted `.cx` compiler vs. version-chained binary releases.
   - Specify the exact Stage 0 -> Stage 1 -> Stage 2 -> Stage 3 deterministic fixed-point verification protocol (eliminating hash-map iteration non-determinism, timestamp embedding, and padding entropy).

## Required Deliverables
1. **Ranked Recommendation & Architectural Decision Record (ADR)** selecting the Stage-0 bootstrap language and the long-term self-hosting seed strategy.
2. **Concrete Memory & Arena Foundation Blueprint** in the recommended bootstrap language (exact struct layouts for `BumpArena`, `StringInterner`, and `u32` ID handles).
3. **Deterministic Bootstrap Pipeline Specification** detailing how `corex` will bootstrap from source on any fresh Linux, macOS, or Windows machine after Stage 0 is retired.
````

---

## `DR-02` (Plugs into `RDG-02` → `docs/research/DR-02.md`): Programming Paradigm & Execution Semantics

````markdown
# Deep Research Request (DR-02): Optimal Programming Paradigm & Core Semantics for CoreX (.cx)

## Context & Vision
I am designing **CoreX** (`.cx`), a zero-GC, strongly and statically typed programming language built for instant compilation, compile-time safety, and C-level runtime speed.
Primary target workloads include:
- Ultra-fast, zero-cold-start CLI tools and rich Terminal UIs (TUIs).
- High-throughput, low-latency web backends and APIs.
- Snappy, lightweight web applications (`wasm32`) and native GUI apps without needing a separate frontend language.

I am open to any programming paradigm—imperative, functional, expression-oriented, data-oriented (DOD), value-oriented (mutable value semantics like Hylo/Swift), or a novel hybrid—provided it maximizes **developer ergonomics, flat learning curve, compile-time safety, and C-level execution speed**.

## Research Objectives
1. **Paradigm Comparative Analysis:** Evaluate pure imperative/procedural (C, Odin, Go), expression-oriented algebraic/imperative hybrids (Rust, Zig, Kotlin), functional-first systems models (OCaml/Flambda, Roc, Koka), Data-Oriented Design (DOD / SoA-first), and Mutable Value Semantics (Hylo) against CoreX's goals.
2. **State, Mutability & Value/Reference Semantics:**
   - Should bindings default to immutable (`let`/`val`) with explicit mutability (`mut`/`var`), or use mutable value semantics?
   - How should data composition work? Evaluate algebraic data types (structs + tagged sum types/enums) + traits/interfaces/protocols vs. class inheritance (and why inheritance helps or hurts zero-GC memory layout and devirtualization).
3. **Expression-Orientation & Control Flow:**
   - Analyze expression-oriented blocks (`if`, `match`, blocks returning values) vs. statement-oriented control flow for readability, cognitive load, and SSA IR lowering.
4. **First-Class Data-Oriented Ergonomics:**
   - How can CoreX make cache-friendly data layouts (Structure-of-Arrays `SoA`, packed bitfields, slices) effortless without sacrificing high-level ergonomics for web backends and UI code?

## Required Deliverables
1. **Synthesized Paradigm Specification for CoreX:** A cohesive hybrid paradigm definition with concrete justification for every axis (binding mutability, value vs. reference semantics, composition over inheritance, algebraic sum types, expression vs. statement rules).
2. **Semantic Invariants for the Compiler Frontend:** Exact rules for evaluation order, aliasing invariants, polymorphism (static monomorphization vs. explicit dynamic dispatch), and zero-cost abstraction guarantees.
````

---

## `DR-03` (Plugs into `RDG-03` → `docs/research/DR-03.md`): Ergonomic Syntax, Delimiter Design & Naming Conventions

````markdown
# Deep Research Request (DR-03): Empirical Syntax Design, Block Delimiters & Naming Conventions for CoreX (.cx)

## Context & Vision
I am designing the surface syntax for **CoreX** (`.cx`), a zero-GC, statically typed systems and application programming language.
Core syntax requirements:
- **Instant Intuitiveness:** 99% of developers should find `.cx` code clean, modern, and intuitive on first sight, without being a blind copy of C.
- **Formatting Freedom (No Indentation Scoping):** CoreX must *not* use Python-style indentation scoping. Code blocks must use explicit delimiters (curly braces `{ }`, round brackets `( )`, square brackets `[ ]`, chevrons `< >`, or another clean delimiter architecture) so developers can format code freely, supported by `corex fmt`.
- **Cohesive Naming & Casing Rules:** Establish ergonomic, unambiguous casing conventions (`snake_case`, `kebab-case`, `camelCase`, `PascalCase`, `SCREAMING_SNAKE_CASE`) across types, functions, variables, constants, modules, and packages.
- **Fast, Unambiguous Parsing:** The grammar must be `LL(k)` / Pratt-parsable in a single pass without C++/Rust turbofish (`::<T>`) parser ambiguities or context-sensitive lexer hacks.

## Research Objectives
1. **Empirical Readability & Cognitive Load Analysis:** Synthesize findings from programming language human-factors studies (Stefik & Siebert, Quorum studies, eye-tracking studies on token density, symbol noise, prefix vs. postfix types, and delimiter scanning).
2. **Delimiter & Generic Bracket Architecture:**
   - Evaluate block, grouping, indexing, and generic type parameter delimiters (`{ }`, `( )`, `[ ]`, `< >`).
   - Specifically analyze the `< >` generic ambiguity problem in C++/Rust (`foo<a, b>(c)` vs. comparison operators) and evaluate clean alternatives (e.g., `[T]` like Scala 3/Go/Python, or unambiguous `<T>` grammar constraints) that keep parsing context-free and visually clean.
3. **Semicolons, Statement Termination & Expression Ergonomics:**
   - Analyze optional semicolons with lexical newline insertion rules (Go/Kotlin/Swift style) vs. mandatory semicolons vs. newline/delimiter-insensitive grammar, ensuring formatting freedom and zero silent multiline traps.
4. **Casing & Identifier Ergonomics:**
   - Evaluate casing conventions across modern languages (Rust, Swift, Go, TypeScript, Python, Zig) and propose a cohesive, compiler-enforced casing matrix for CoreX.
5. **Complete Lexical & Surface Grammar Draft:**
   - Declarations (variables, constants, functions, structs, enums/unions, traits/interfaces, modules, imports), control flow (`if`/`else`, `match`, loops), closures/lambdas, string interpolation, pipeline/method syntax, and attributes/annotations.

## Required Deliverables
1. **Complete EBNF Grammar & Lexical Token Table (`TokenKind`)** for CoreX v1.0, proven free of lexer/parser lookahead ambiguities.
2. **Canonical Casing & Style Matrix** for all language constructs.
3. **Side-by-Side `.cx` Code Showcases:** Show how a CLI tool, an async HTTP JSON endpoint, a memory-intensive tree manipulation algorithm, and a reactive UI component look in the proposed `.cx` syntax.
````

---

## `DR-04` (Plugs into `RDG-04` → `docs/research/DR-04.md`): Static Type System, Constrained Type Groups & Zero-Overhead Inference

````markdown
# Deep Research Request (DR-04): Strong Static Type System, Constrained Type Groups & Type Inference for CoreX (.cx)

## Context & Vision
CoreX (`.cx`) requires a **strong, static type system** that maximizes both runtime performance and Language Server (`corex lsp`) intelligence while feeling effortless to write:
- **Smart Type Inference:** Catch nearly 100% of type errors at compile time with minimal annotation ceremony.
- **Constrained Type Groups / Aliases:** Include built-in and user-definable constrained type groups (e.g., using a generic `Number`, `Int`, or `Float` constraint directly in a function signature like `fn clamp(val: Number, low: Number, high: Number) -> Number`) that automatically resolve and monomorphize to concrete machine types (`i32`, `f64`, etc.) at compile time with **zero runtime boxing or vtable overhead**.

## Research Objectives
1. **Constrained Type Groups & Ergonomic Generics:**
   - Design the exact semantics of **Type Groups** (built-in groups like `Number`, `Signed`, `Unsigned`, `Integer`, `Float`, `Comparable`, `Numeric`, `Bytes`, and user-defined structural/nominal type unions or trait groups).
   - Specify how same-type vs. independent-type constraints work in signatures (e.g., when two parameters written with `Number` must unify to the *same* concrete type `T: Number` vs. independent numeric types, and how the syntax makes both cases effortless and unambiguous).
2. **Bidirectional Type Inference & Fast Compilation:**
   - Compare Hindley-Milner unification, bidirectional typing (Dunfield & Krishnaswami), and local constraint solving.
   - Avoid exponential type-checking blowups (like Swift's expression solver or complex Scala implicit searches) so type checking scales linearly (`>= 500,000` LOC/sec) and preserves crisp error localization when code is incomplete in the IDE.
3. **Numeric Hierarchy, Literal Polymorphism & Overflow Safety:**
   - Design untyped/polymorphic numeric literals (adapting cleanly to the target concrete integer/float type without noisy casts), explicit bit-width types (`i8`..`i128`, `u8`..`u128`, `isize`, `usize`, `f32`, `f64`), and compile-time vs. runtime integer overflow semantics.
4. **Algebraic Types, Null Safety & Refinement/Newtype Ergonomics:**
   - Eliminate billion-dollar `null` errors via zero-cost optional types (`?T` / niche-optimized enums), structural vs. nominal subtyping, and zero-cost constrained/refined types.

## Required Deliverables
1. **Formal Type System & Unification/Bidirectional Inference Specification** (typing judgments, constraint propagation algorithm, and complexity bounds).
2. **Constrained Type Groups Specification** detailing syntax, unification semantics, monomorphization lowering, and error diagnostics.
3. **Compiler Data Structures (`TypeArena`, `TypeId`, `SubstitutionMap`)** optimized for arena allocation and incremental query caching.
````

---

## `DR-05` (Plugs into `RDG-05` → `docs/research/DR-05.md`): Compile-Time Execution (`comptime`) & Metaprogramming Architecture

````markdown
# Deep Research Request (DR-05): Compile-Time Execution (`comptime`), Reflection & Metaprogramming for CoreX (.cx)

## Context & Vision
CoreX (`.cx`) aims to shift as much computation, configuration validation, serialization routing, and boilerplate generation as possible from runtime to compile time, while keeping the language syntax simple, readable, and IDE/LSP-friendly.

## Research Objectives
1. **Comparative Evaluation of Metaprogramming Paradigms:**
   - **Zig-style `comptime`:** Executing regular language code and passing types as values at compile time without a separate macro sub-language.
   - **Rust-style Hygienic Declarative (`macro_rules!`) & Procedural Token-Stream Macros:** Powerful syntax extension, but notorious for compile-time slowdowns and degraded IDE/LSP autocomplete/refactoring.
   - **Compile-Time Type Reflection + Splice/Mirror APIs (C++26 `std::meta` / Mojo / Nim / Jai):** Structured compile-time AST/type introspection and code emission.
   - **Stage-Polymorphic / Multi-Stage Programming.**
2. **LSP & Incremental Compilation Compatibility (CRITICAL):**
   - Analyze how each metaprogramming approach interacts with `corex lsp` (go-to-definition, hover types, rename refactoring, completion) and incremental query caching. How do we ensure metaprogramming never blinds the Language Server or forces slow external proc-macro dylib compilations?
3. **Compiler Interpreter (`MIR` VM / Bytecode Evaluator) Design:**
   - Design an ultra-fast, deterministic compile-time evaluator (register/bytecode VM or direct JIT over `MIR`) capable of evaluating arbitrary pure `.cx` functions, lookup table generation, regex/route compilation, and struct field reflection (e.g., zero-overhead `std::serde` JSON/CLI parsers) at compile time.
   - Specify sandboxing invariants (deterministic memory representation, endianness handling for cross-compilation, step budgets, and forbidden host syscalls).

## Required Deliverables
1. **Recommended Metaprogramming & Compile-Time Execution Architecture for CoreX:** Syntax, semantics, and capabilities (compile-time constants, type-level generics via `comptime`, compile-time struct/enum reflection, and static assertions).
2. **`MIR` Compile-Time Virtual Machine Blueprint:** Memory layout of compile-time pointers/allocations, constant folding integration, and caching strategy inside the incremental query database.
````

---

## `DR-06` (Plugs into `RDG-06` → `docs/research/DR-06.md`): Zero-GC Automatic Memory Management, Manual Control & SAST Verifier

````markdown
# Deep Research Request (DR-06): Zero-GC Memory Model, Automatic Compile-Time Cleanup & Static Vulnerability Verifier (SAST) for CoreX (.cx)

## Context & Vision
CoreX's memory management has three strict requirements:
1. **No Runtime Tracing Garbage Collector:** Deterministic C-level speed and minimal memory footprint.
2. **Automatic Default with Compile-Time Safety:** Everyday coding must feel effortless—memory allocation and deallocation are handled automatically by the compiler by default (e.g., deterministic scope-based cleanup, region/escape inference, Perceus/Lobster-style compile-time reference counting, or mutable value semantics) **without forcing Rust-style lifetime annotation gymnastics (`<'a, 'b>`) on the developer**.
3. **Optional Manual Control + Built-In Static Vulnerability Analysis (SAST):** Power users can take explicit manual control over memory allocation, arenas, and raw layout when needed. To prevent manual or hybrid memory management from introducing C-style bugs, the compiler includes a built-in static analysis engine (SAST) and lifetime/ownership verifier that checks memory operations at compile time and emits crystal-clear errors/warnings for potential vulnerabilities (**use-after-free, double-free, memory leaks, dangling stack/arena escapes, uninitialized reads, and buffer overflows**).

## Research Objectives
1. **Synthesizing the Optimal Default Zero-GC Memory Model:**
   - Evaluate and compare:
     - **Compile-Time Lifetimes with Interprocedural Inference** (inferring borrow/escape summaries across function boundaries without explicit `'a` annotations),
     - **Mutable Value Semantics & Law of Exclusivity** (Hylo / Swift approach: values have unique ownership by default, projection/inout parameters replace complex lifetime graphs),
     - **Compile-Time Reference Counting / Perceus / Lobster Ownership Analysis** (compiler-inserted deterministic drops with static alias analysis eliminating 95%+ of refcount operations at compile time),
     - **Static Region Inference** (Tofte-Talpin / Cyclone / Verona regions / automatic arena scoping),
     - **Hybrid Tiered Model** (stack/value + scope-owned + inferred borrows + explicit arenas).
   - Determine how cyclic graphs, closures, and async tasks are handled safely with zero GC and zero annotation friction.
2. **Manual Memory Control & Allocator Ergonomics:**
   - Design the interface for manual heap/arena/pool/fixed-buffer allocation, explicit deallocation (`free`/`defer`), and custom layout control (SoA, alignment, intrusive nodes).
3. **Built-In Static Vulnerability Analysis (SAST) & Symbolic Verifier on `MIR`:**
   - Design the static analysis pass operating on the compiler's SSA `MIR` Control Flow Graph:
     - **Typestate & Ownership Dataflow Analysis** for Use-After-Free (UAF), Double-Free, and Memory Leak detection across all CFG branches.
     - **Interprocedural Escape & Aliasing Summary Computation** (bottom-up SCC summary inference so functions don't require manual lifetime parameters while remaining modular and fast).
     - **Abstract Interpretation / Integer Range Analysis** (octagons/intervals) for compile-time Buffer Overflow / Bounds Check Elimination and proving safe indexing.

## Required Deliverables
1. **Complete CoreX Memory Model Specification:** How everyday automatic memory works, how borrows/views work without lifetime annotations, and how power users opt into manual/arena control.
2. **Formal `MIR` SAST & Lifetime Verification Algorithm:** Dataflow equations, lattice definitions, interprocedural function summary schema, cycle handling, and diagnostic generation rules for UAF, double-free, leaks, dangling escapes, and out-of-bounds accesses.
````

---

## `DR-07` (Plugs into `RDG-07` → `docs/research/DR-07.md`): Error Handling Model & Zero-Cost Propagation Semantics

````markdown
# Deep Research Request (DR-07): High-Performance, Ergonomic Error Handling Architecture for CoreX (.cx)

## Context & Vision
CoreX (`.cx`) needs the cleanest, highest-performance error handling mechanism possible—one that makes error handling effortless and readable, guarantees compile-time exhaustiveness, and introduces **zero hidden control flow and zero runtime overhead** (no C++ DWARF stack-unwinding exceptions or heap-allocated stack traces on normal error paths).

## Research Objectives
1. **Comparative Analysis of Modern Zero-Cost Error Models:**
   - **Explicit `Result<T, E>` Algebraic Types + `?` Postfix Propagation** (Rust).
   - **Inferred / Checked Error Union Sets (`!T` / `E!T` + `try` / `catch` / `errdefer`)** (Zig).
   - **Typed `throws` with Value-Return ABI Lowering** (Swift 6 `throws(ErrorType)` / Herb Sutter's C++ `P0709` zero-cost deterministic exceptions returning via CPU carry/register flag).
   - **Algebraic Effects Compiled via Evidence Passing** (Koka).
2. **ABI & Codegen Performance Analysis:**
   - Analyze machine-code generation on `x86_64`, `aarch64`, and `wasm32`: how returning `(payload, error_tag)` in registers + CPU flags (`P0709` / Zig error union ABI) compares against large stack-spilled `Result<T, E>` structs when `sizeof(E)` differs from `sizeof(T)`.
3. **Ergonomics, Error Composition & Automatic Scope Cleanup:**
   - How do errors compose across libraries without manual boilerplate `From`/`map_err` ceremonies?
   - How does error propagation interact with deterministic scope cleanup (`defer` / `errdefer` / automatic scope drops from `DR-06`)?
   - Distinguish recoverable domain errors from unrecoverable contract violations (`panic` / `assert`).

## Required Deliverables
1. **Selected Error Handling Specification for CoreX:** Syntax for declaring fallible functions, propagating errors, pattern-matching/recovering from errors, adding context, and `errdefer` cleanup.
2. **Register-Level ABI & `MIR` Lowering Specification:** How error unions/results are represented in `MIR` and lowered to zero-allocation register/flag returns on `x86_64`, `aarch64`, and `wasm32`.
````

---

## `DR-08` (Plugs into `RDG-08` → `docs/research/DR-08.md`): Concurrency, Async/Structured Execution & High-Throughput I/O Model

````markdown
# Deep Research Request (DR-08): Optimal Concurrency, Structured Async & High-Performance I/O Architecture for CoreX (.cx)

## Context & Vision
CoreX targets both **high-throughput, low-latency web backends/APIs** (handling hundreds of thousands of concurrent connections with minimal tail latency and memory) and **responsive TUI/Wasm/native UI applications**, all under a **zero-GC, statically verified memory model** with zero cold-start overhead.

## Research Objectives
1. **Concurrency Execution Model Comparison:**
   - **Stackless Coroutines (`async`/`await` state machines)** vs. **Stackful Coroutines / Green Threads / Virtual Threads** (with segmented/growable stacks vs. virtual-memory guard pages) vs. **Caller-Controlled Colorless Async** (Zig style) vs. **Actor/CSP Channels**.
   - Evaluate memory footprint per concurrent task, C FFI call compatibility (calling C functions without stack-switching penalties), compilation speed, and absence of the "function coloring" problem.
2. **Structured Concurrency & Cancellation Safety:**
   - Analyze structured task scopes (`TaskGroup` / nurseries) where child tasks are lexically bounded by their parent scope.
   - How structured concurrency unifies with CoreX's zero-GC memory model (`DR-06`): if child tasks cannot outlive their parent scope, spawned tasks can safely borrow stack/arena data without requiring `Arc<Mutex<T>>` heap wrappers or complex `'static` lifetime bounds!
3. **Compile-Time Data-Race Freedom:**
   - How the static verifier (`DR-06`) prevents data races across threads/tasks (e.g., `Send`/`Sync` auto-inference, isolated regions, or linear channel transfers) without annotation clutter.
4. **OS-Native Completion I/O Reactor Architecture:**
   - Design the cross-platform completion-based I/O engine (`io_uring` on Linux, `IOCP` on Windows, `kqueue` on macOS, and browser/WASI event loop integration on `wasm32`), comparing thread-per-core (share-nothing) vs. work-stealing schedulers.

## Required Deliverables
1. **CoreX Concurrency & Structured Task Specification:** Language primitives, task spawning, channels/synchronization, cancellation semantics, and data-race verification rules.
2. **Compiler Lowering & Runtime Scheduler Blueprint:** How concurrent/async functions lower in `MIR`, memory layout of task frames, and the OS I/O completion ring interface.
````

---

## `DR-09` (Plugs into `RDG-09` → `docs/research/DR-09.md`): Dual-Mode Compiler Backend Architecture (Instant Dev vs. Production AOT)

````markdown
# Deep Research Request (DR-09): Dual-Mode Compiler Backend Architecture (Instant Dev Mode vs. Optimizing Production AOT) for CoreX (.cx)

## Context & Vision
CoreX requires a **Dual-Mode Compilation Pipeline**:
- **Development Mode (`corex run`, `corex build --dev`):** Instantaneous compilation (`>= 500,000` LOC/sec, sub-50ms incremental rebuilds) that skips heavy optimization passes so the developer feedback loop feels instant regardless of project size.
- **Production Mode (`corex build --release`):** Ahead-of-Time (AOT) compilation with maximum optimization passes producing native machine code that matches or outperforms C (`clang -O3`) and Rust (`rustc -O`), plus compact `wasm32` output.

## Research Objectives
1. **Backend Architecture Candidates Evaluation:**
   - **Option A:** Custom direct machine-code emitter (`x86_64`, `aarch64`, `wasm32`) for `--dev` + **LLVM** for `--release` (similar to Zig's architecture).
   - **Option B:** **Cranelift** for `--dev` + **LLVM** for `--release`.
   - **Option C:** **QBE** / custom Sea-of-Nodes / custom SSA backend for both modes.
   - **Option D:** Custom `MIR` bytecode VM / copy-and-patch JIT (Xu & Kjolstad `silly`/`Deegen` style) for instant `corex run` + direct native emitter for `--dev` binaries + **LLVM** (or custom optimizing backend) for `--release`.
2. **Deep Evaluation Criteria:**
   - **Compilation Speed:** Exact throughput benchmarks (`LOC/sec`) and incremental patching capabilities (in-place binary patching / hot-code reloading during `--dev`).
   - **Runtime Code Quality:** SIMD auto-vectorization, inlining, alias metadata propagation (passing CoreX's `DR-06` strict `noalias` guarantees to the optimizer to beat C pointer aliasing!), register allocation, and tail calls.
   - **Toolchain Binary Size & Self-Hosting Impact:** How linking LLVM affects the `corex` binary footprint and whether `corex` can load the heavy production backend lazily or modularly while keeping the core binary lightweight.
3. **Unified `MIR` -> Backend Lowering Boundary:**
   - Design the clean `CodegenBackend` trait/interface so both `--dev` and `--release` consume the exact same verified `MIR` and share identical ABI/layout calculations, guaranteeing zero behavioral divergence between dev and prod builds.

## Required Deliverables
1. **Definitive Dual-Mode Backend Architecture Selection** with quantitative justification.
2. **`CodegenBackend` Interface & `MIR` Lowering Specification** (including how CoreX static aliasing/range proofs translate into LLVM `noalias`/`!range` metadata or custom backend hints).
3. **Incremental Codegen & Binary Patching Strategy** for sub-50ms `--dev` rebuilds.
````

---

## `DR-10` (Plugs into `RDG-10` → `docs/research/DR-10.md`): Cross-Compilation, Zero-Dependency Linking, C FFI & WebAssembly (`wasm32`)

````markdown
# Deep Research Request (DR-10): Cross-Compilation, Standalone Static/Dynamic Linking, C FFI & WebAssembly (`wasm32`) Pipeline for CoreX (.cx)

## Context & Vision
CoreX must effortlessly cross-compile from any host machine (Windows, Linux, macOS) to all major targets (`x86_64` and `aarch64` Linux, macOS, Windows, and `wasm32`) out of the box—without forcing the user to install gigabytes of platform SDKs, Xcode, or Visual Studio build tools. Users must be able to choose between compiling a **single standalone static executable** or **dynamically linked binaries/libraries**, and call **C libraries (FFI)** with zero overhead.

## Research Objectives
1. **Out-of-the-Box Cross-Compilation & Embedded Linker Architecture:**
   - Analyze how Zig (`zig cc`), Go, and `lld`/`mold` achieve hermetic cross-compilation from any host OS.
   - Determine how `corex` should embed or invoke ELF (`Linux`), Mach-O (`macOS`), PE/COFF (`Windows`), and WebAssembly (`wasm32`) linkers.
   - How to bundle or lazily synthesize minimal target libc/syscall import stubs (`musl` for static Linux, `.tbd` stub libraries for macOS `libSystem`, `.def`/import libraries for Windows `kernel32.dll`/`ntdll.dll`/`ucrtbase.dll`) so cross-compilation requires tiny kilobyte-scale definitions rather than multi-gigabyte SDKs.
2. **Standalone Static vs. Dynamic Linking Modes:**
   - Specify how `--link=static` and `--link=dynamic` work on each OS (direct Linux syscalls / static `musl` on Linux; Apple's required dynamic `libSystem.B.dylib` with all user libraries statically linked on macOS; static CRT / Win32 imports on Windows).
3. **Zero-Overhead C Interoperability (FFI):**
   - Compare direct C header ingestion (embedding a lightweight C preprocessor/parser like `aro` or `libclang` vs. declarative `extern "C"` blocks + built-in `corex bindgen`).
   - Specify exact C ABI calling convention rules (`SysV AMD64`, `Win64`, `AAPCS64`, `wasm32` C ABI) for structs-by-value, bitfields, SIMD vectors, and callbacks.
4. **First-Class WebAssembly (`wasm32`) Pipeline:**
   - Target both `wasm32-wasi` (for server/CLI Wasm) and `wasm32-freestanding` (for ultra-small browser web apps), including SIMD128, bulk-memory, tail-call proposals, and dead-code stripping for minimal `.wasm` bundle sizes (`< 10 KB` baseline).

## Required Deliverables
1. **Cross-Compilation & Linker Subsystem Blueprint** detailing object file emission, embedded linker architecture, and target stub layout.
2. **C FFI Specification & ABI Lowering Matrix** across `x86_64`, `aarch64`, and `wasm32`.
3. **WebAssembly Codegen & Host-Bridge Specification.**
````

---

## `DR-11` (Plugs into `RDG-11` → `docs/research/DR-11.md`): Package Manager, URL/Registry Resolution, Global Cache & Lockfiles

````markdown
# Deep Research Request (DR-11): Zero-Friction Package Management, Content-Addressable Global Cache & Reproducible Lockfile Architecture for CoreX (.cx)

## Context & Vision
CoreX's package management must combine zero-friction developer ergonomics with rock-solid reproducibility and disk efficiency:
- **Zero-Friction Imports:** Developers can reference packages directly via short registry IDs or URLs (e.g., GitHub repositories), and `corex run` / `corex build` automatically fetches and resolves them on demand.
- **Content-Addressable Global Cache:** Downloaded packages are stored once in a centralized, content-addressable global cache on the machine (avoiding duplicate downloads or duplicate files across projects, similar to `pnpm` / Nix / Cargo cache) while using project-level lockfiles (`corex.lock`) for reproducible builds.

## Research Objectives
1. **Source Import & Manifest Ergonomics:**
   - Design how `.cx` files reference external packages (direct URL/registry imports in `.cx` files for single-file scripts vs. `corex.toml` project manifests) and how `corex` auto-synchronizes them without manual `install` rituals.
2. **Version Resolution Algorithm:**
   - Compare **Minimal Version Selection (MVS)** (Go's O(V+E) deterministic algorithm requiring no SAT solver) vs. **PubGrub** (conflict-driven clause learning with human-readable error explanations).
   - How to handle diamond dependencies, major-version coexistence, and local path overrides.
3. **Content-Addressable Global Store (`~/.corex/cache`):**
   - Design the content-addressable storage layout using **BLAKE3** Merkle tree hashing (per-file content blobs + package directory manifest trees).
   - Analyze concurrent multi-process locking, atomic cache writes, and zero-copy read access (mapping cached `.cx` files directly from the global read-only content store into the compiler's `SourceMap` without even needing per-project `node_modules`-style copies!).
4. **Decentralized / Git-Backed Registry & Cryptographic Supply-Chain Security:**
   - Design a static index / GitHub-compatible registry protocol (HTTP range / sparse index) plus cryptographic hash pinning and signature verification in `corex.lock`.

## Required Deliverables
1. **Package Import Syntax, `corex.toml` & `corex.lock` Schemas.**
2. **Global Content-Addressable Cache & Merkle Verification Specification.**
3. **Resolution Algorithm & Offline/Hermetic Build Protocol.**
````

---

## `DR-12` (Plugs into `RDG-12` → `docs/research/DR-12.md`): Incremental Query Engine, Fault-Tolerant Lossless CST & Built-in LSP

````markdown
# Deep Research Request (DR-12): Fault-Tolerant Lossless CST, Incremental Query Engine & Built-in Language Server (`corex lsp`) Architecture

## Context & Vision
CoreX packages a built-in Language Server (`corex lsp`), linter (`corex check`), and code formatter (`corex fmt`) directly inside the `corex` compiler binary. The compiler's lexer, parser, CST/AST, and semantic analyzer must be architected from Phase 1 around **fault-tolerant lossless syntax trees and demand-driven incremental computation** so editor interactions respond in `< 5 ms` even on 500,000-line codebases.

## Research Objectives
1. **Lossless Syntax Tree Representation:**
   - Compare **Rowan / Red-Green Trees** (`rust-analyzer` / Roslyn style) vs. **Flat Contiguous Arena CSTs with Explicit Trivia Side-Tables** (Carbon / Zig / Sorbet style).
   - Evaluate memory overhead, cache locality, arena lifetime management, and incremental subtree reuse when a user types a single character inside a function body.
2. **Fault-Tolerant Parsing & Partial Semantic Recovery:**
   - Specify parser recovery anchors, placeholder/tombstone AST/HIR nodes (`Expr::Error`, `Type::Error`), and bidirectional type inference propagation across incomplete expressions (e.g., `let user = repo.find(` at the cursor) so autocomplete and hover types work reliably while code is mid-keystroke.
3. **Demand-Driven Incremental Query Architecture:**
   - Design the query database (inspired by Salsa / Adapton / `rustc` query system) with the **"Early Cutoff" optimization**:
     - Modifying a function body re-parses that file's CST and re-typechecks only that single function body; because its exported signature hash has not changed, zero downstream modules are re-checked!
4. **Built-In `corex lsp` Server Architecture:**
   - JSON-RPC 2.0 transport, cancellation of stale in-flight requests on new `didChange` events, virtual filesystem overlay (`Vfs`), semantic tokens, inlay hints (inferred types, elided memory cleanup points), and machine-applicable code actions.

## Required Deliverables
1. **Data Structure Blueprint for `LosslessCstArena` & `AstArena`** (exact byte layouts and trivia attachment strategy).
2. **Incremental Query Engine & Early-Cutoff Invalidation Algorithm.**
3. **Fault-Tolerant Recovery Rules** across Lexer, Parser, Name Resolver, and Type Checker.
````

---

## `DR-13` (Plugs into `RDG-13` → `docs/research/DR-13.md`): Intermediate Representations (`HIR` & SSA `MIR`) & Optimization Pipeline

````markdown
# Deep Research Request (DR-13): High-Level IR (`HIR`), Mid-Level SSA IR (`MIR`) & Optimization Pipeline for CoreX (.cx)

## Context & Vision
To support CoreX's compile-time evaluator (`comptime`), static vulnerability & memory verifier (`SAST`), automatic deterministic cleanup, and dual-mode backends (`--dev` and `--release`), the compiler needs clean, high-performance Intermediate Representations between the frontend AST and backend codegen.

## Research Objectives
1. **Number & Role of IR Tiers:**
   - Define the exact division of responsibilities between:
     - **Typed AST / `HIR` (High-Level IR):** Desugared, name-resolved, type-checked representation used for exhaustiveness checking, constrained type-group resolution, and LSP queries.
     - **`MIR` (Mid-Level Control-Flow Graph IR in SSA / Place-Projection Form):** Used for the `comptime` interpreter (`DR-05`), path-sensitive SAST/ownership/lifetime verification and automatic scope drop insertion (`DR-06`), monomorphization, and high-level optimizations before backend lowering.
2. **SSA vs. Basic-Block Arguments & Place Projections in `MIR`:**
   - Compare classic phi-node SSA vs. MLIR/Swift SIL-style **Basic Block Arguments** for CFG manipulation.
   - How to represent memory places (`Place { base: LocalId, projections: Slice<Projection> }`) alongside pure SSA values so the SAST/borrow/escape verifier can reason precisely about partial struct field moves and slice sub-ranges, and then convert non-escaped places into pure SSA registers (SROA / `mem2reg`).
3. **High-Impact `MIR` Optimization Passes:**
   - Identify the exact set of fast, high-leverage passes to run in `MIR` (and which run in `--dev` vs. `--release`):
     - Polymorphic specialization / Monomorphization + identical code folding (ICF) to prevent binary bloat,
     - Inlining heuristics & devirtualization,
     - Scalar Replacement of Aggregates (SROA) & copy/move elision (NRVO/RVO),
     - Bounds-check elimination driven by the SAST range verifier (`DR-06`),
     - Dead-code and unreachable basic-block elimination.

## Required Deliverables
1. **Complete `HIR` and `MIR` Instruction & Terminator Catalog** with compact arena-allocated data structures.
2. **Pass Ordering & Verification Invariants** for both `--dev` and `--release` pipelines.
3. **Monomorphization / Code-Bloat Mitigation Strategy** for generic / type-group functions.
````

---

## `DR-14` (Plugs into `RDG-14` → `docs/research/DR-14.md`): Zero-Legacy AST Migration Engine (`corex upgrade`) & Formatter (`corex fmt`)

````markdown
# Deep Research Request (DR-14): Zero-Legacy Automated Migration Engine (`corex upgrade`) & Canonical Formatter (`corex fmt`) for CoreX (.cx)

## Context & Vision
CoreX enforces a strict **Zero-Legacy Compiler Philosophy**:
> *"Do not bloat or slow down the compiler with backward-compatibility branches for old language versions. The compiler should only ever target the current specification to stay as lean and fast as possible; if breaking syntax or standard library improvements are introduced in future versions, the built-in tooling should provide an automated migration command (`corex upgrade` / `corex fix`) that rewrites older `.cx` source code to the newest spec."*

Additionally, CoreX includes a deterministic built-in formatter (`corex fmt`) that respects developer expression structure while enforcing canonical style.

## Research Objectives
1. **Canonical Pretty-Printing & Formatting Engine (`corex fmt`):**
   - Evaluate Wadler-Lindig / Oppenheimer / `prettier` / `gofmt` / `zig fmt` formatting IR (`Doc` algebra: `Group`, `Indent`, `Line`, `SoftLine`, `IfBreak`) operating directly over the `LosslessCstArena`.
   - Design comment-attachment and blank-line preservation invariants so `corex fmt` is 100% idempotent, never drops or misplaces a comment, and formats `>= 1,000,000` LOC/sec.
2. **Zero-Legacy Automated Source Migration Architecture (`corex upgrade`):**
   - Analyze how `gofix`, `rustfix` / Cargo editions, Swift migrator, and `jscodeshift` / Coccinelle semantic patches work—and specifically how to implement `corex upgrade` **without keeping full legacy parsers/type-checkers inside the main compiler pipeline**:
     - How versioned migration rules (`v1.0 -> v1.1`, etc.) are represented as declarative or tabular CST/token/semantic transformation passes isolated inside the `upgrade` tool module.
     - How `corex.toml` tracks the project's spec version (`corex = "1.0"`), detects when a project was written against an older spec, and offers one-command lossless migration (`corex upgrade`) across all project `.cx` files and cached dependencies.
     - How `DiagnosticSink` machine-applicable `CodeFix` edits unify with `corex fix` and `corex upgrade`.

## Required Deliverables
1. **`corex fmt` Document Algebra & Trivia-Preservation Specification.**
2. **`corex upgrade` Architecture & Versioned CST/Semantic Rewrite Engine Blueprint** that keeps the core compiler pipeline 100% free of legacy branches.
````

---

## `DR-15` (Plugs into `RDG-15` → `docs/research/DR-15.md`): Stage-2 `.cx` Standard Library, TUI/CLI & Unified WebAssembly/Native UI Architecture

````markdown
# Deep Research Request (DR-15): Stage-2 Batteries-Included Standard Library (`std`), TUI/CLI Engine & Unified WebAssembly/Native App Architecture in CoreX (.cx)

## Context & Vision
CoreX follows a **Two-Stage Standard Library** strategy:
- **Stage 1:** Minimal `core` intrinsics and OS syscall bindings inside the compiler bootstrap phase.
- **Stage 2:** A rich, "batteries-included", modular, tree-shakeable standard library written **100% in CoreX (`.cx`)** covering my primary personal and general-purpose use cases:
  1. Writing zero-cold-start, ultra-fast **CLI tools** and rich **Terminal UIs (TUIs)**.
  2. Building high-throughput, low-latency, lightweight **web backends and APIs**.
  3. Building snappy, lightweight, and visually polished **web applications (via WebAssembly `wasm32`) and native apps** without needing a separate frontend language (no JS/TS framework bloat).

## Research Objectives
1. **Modular, Tree-Shakeable `std` Package Hierarchy:**
   - Design the module boundaries (`std::mem`, `std::col`, `std::str`, `std::io`, `std::fs`, `std::cli`, `std::tui`, `std::async`, `std::net`, `std::http`, `std::serde`, `std::crypto`, `std::ui`, `std::test`) so importing a single module incurs zero dead-code or startup overhead.
   - How `std` integrates explicit allocator passing vs. ambient/scoped default allocators (`DR-06`).
2. **World-Class `std::cli` & `std::tui` Architecture:**
   - **`std::cli`:** Zero-allocation compile-time (`comptime`) validated argument/flag/subcommand parser with automatic monochrome Unicode + ANSI help generation.
   - **`std::tui`:** High-performance Terminal UI architecture (comparing Ratatui/Notcurses diffed double-buffered cell grids + flexbox/grid layout engine + raw-mode mouse/keyboard/resize event stream + synchronized terminal output `DECSET 2026` for tear-free 120 FPS rendering).
3. **High-Throughput `std::http` & `std::serde` Architecture:**
   - Zero-copy HTTP parser/router, middleware pipeline, WebSocket support, and `comptime`-generated zero-allocation JSON/binary serialization.
4. **Unified `std::ui` for WebAssembly (`wasm32`) & Native Apps (Zero JS Framework):**
   - Compare architectures for writing visually polished web and native apps entirely in `.cx`:
     - Fine-grained reactive signals + typed view builder compiling to direct surgical DOM binary command buffers over a tiny (`< 3 KB`) Wasm-DOM host shim vs. GPU/WebGPU/Canvas2D rendering (`wgpu` / Skia-lite style) that renders identically on browser `<canvas>` and native OS windows (Win32/Direct2D/Metal/Wayland).
     - Recommend the optimal dual-target architecture so a single `.cx` UI component tree runs with native speed in the browser (`.wasm`) and on the desktop.

## Required Deliverables
1. **Complete `std` Module Map & Public API Signatures** in `.cx`.
2. **Technical Blueprint for `std::cli` and `std::tui`** (double-buffered cell renderer, layout engine, and monochrome Unicode glyph toolkit).
3. **Technical Blueprint for `std::http` / `std::serde`** and the **Unified `std::ui` WebAssembly + Native Application Engine**.
````

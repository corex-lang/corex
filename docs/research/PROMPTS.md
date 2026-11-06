# Upfront `Deep Research` Prompts (`DR-01`–`DR-15`)

This catalog contains the 15 self-contained, copy-pasteable `Deep research` prompts that resolve the Research Decision Gates (`RDG-01`–`RDG-15`) in [PLAN.md](../../PLAN.md). When a `Deep research` report is completed, save its output to the corresponding `docs/research/DR-XX.md` path listed below.

---

## Research Report Index & Execution Waves

| Report ID   | Gate ID      | Target Report Path       | Wave   | Files to Attach in Chat                  | Blocking Phase   | Subsystem / Architectural Scope                                                        |
| ----------- | ------------ | ------------------------ | ------ | ---------------------------------------- | ---------------- | -------------------------------------------------------------------------------------- |
| **`DR-01`** | **`RDG-01`** | `docs/research/DR-01.md` | Wave 1 | *None (Completed)*                       | Phase 0          | Bootstrap Implementation Language & Self-Hosting Strategy                              |
| **`DR-02`** | **`RDG-02`** | `docs/research/DR-02.md` | Wave 1 | *None (Completed)*                       | Phase 2          | Programming Paradigm & Execution Semantics                                             |
| **`DR-03`** | **`RDG-03`** | `docs/research/DR-03.md` | Wave 1 | *None (Completed)*                       | Phase 1 / 2      | Ergonomic Syntax, Delimiter Design & Naming Conventions                                |
| **`DR-04`** | **`RDG-04`** | `docs/research/DR-04.md` | Wave 2 | `DR-01`, `DR-02`, `DR-03`                | Phase 4          | Static Type System, Constrained Type Groups & Zero-Overhead Inference                  |
| **`DR-05`** | **`RDG-05`** | `docs/research/DR-05.md` | Wave 2 | `DR-01`, `DR-02`, `DR-03`                | Phase 5          | Compile-Time Execution (`comptime`) & Metaprogramming Architecture                     |
| **`DR-06`** | **`RDG-06`** | `docs/research/DR-06.md` | Wave 2 | `DR-01`, `DR-02`, `DR-03`                | Phase 6          | Zero-GC Automatic Memory Management, Manual Control & SAST Verifier                    |
| **`DR-07`** | **`RDG-07`** | `docs/research/DR-07.md` | Wave 2 | `DR-01`, `DR-02`, `DR-03`                | Phase 4 / 6      | Error Handling Model & Zero-Cost Propagation Semantics                                 |
| **`DR-12`** | **`RDG-12`** | `docs/research/DR-12.md` | Wave 2 | `DR-01`, `DR-02`, `DR-03`                | Phase 2 / 3 / 10 | Incremental Query Engine, Fault-Tolerant Lossless CST & Built-in LSP                   |
| **`DR-13`** | **`RDG-13`** | `docs/research/DR-13.md` | Wave 2 | `DR-01`, `DR-02`, `DR-03`                | Phase 5          | Intermediate Representations (`HIR` & SSA `MIR`) & Optimization Pipeline               |
| **`DR-08`** | **`RDG-08`** | `docs/research/DR-08.md` | Wave 3 | `DR-01`–`DR-03`, `DR-06`, `DR-07`        | Phase 8 / 11     | Concurrency, Async/Structured Execution & High-Throughput I/O Model                    |
| **`DR-09`** | **`RDG-09`** | `docs/research/DR-09.md` | Wave 3 | `DR-01`–`DR-03`, `DR-06`, `DR-13`        | Phase 7          | Dual-Mode Compiler Backend Architecture (Instant Dev vs. Production AOT)               |
| **`DR-10`** | **`RDG-10`** | `docs/research/DR-10.md` | Wave 3 | `DR-01`–`DR-03`, `DR-06`, `DR-07`, `DR-13` | Phase 8        | Cross-Compilation, Zero-Dependency Linking, C FFI & WebAssembly (`wasm32`)             |
| **`DR-11`** | **`RDG-11`** | `docs/research/DR-11.md` | Wave 3 | `DR-01`, `DR-02`, `DR-03`                | Phase 9          | Package Manager, URL/Registry Resolution, Global Cache & Lockfiles                     |
| **`DR-14`** | **`RDG-14`** | `docs/research/DR-14.md` | Wave 3 | `DR-01`–`DR-03`, `DR-12`                 | Phase 3 / 10     | Zero-Legacy AST Migration Engine (`corex upgrade`) & Canonical Formatter (`corex fmt`) |
| **`DR-15`** | **`RDG-15`** | `docs/research/DR-15.md` | Wave 3 | `DR-02`–`DR-08`                          | Phase 11         | Stage-2 `.cx` Standard Library, TUI/CLI & Unified WebAssembly/Native UI Architecture   |

---

## `DR-01` (Plugs into `RDG-01` → `docs/research/DR-01.md`): Bootstrap Implementation Language & Self-Hosting Strategy

```markdown
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

```

---

## `DR-02` (Plugs into `RDG-02` → `docs/research/DR-02.md`): Programming Paradigm & Execution Semantics

```markdown
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

```

---

## `DR-03` (Plugs into `RDG-03` → `docs/research/DR-03.md`): Ergonomic Syntax, Delimiter Design & Naming Conventions

```markdown
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

```

---

## `DR-04` (Plugs into `RDG-04` → `docs/research/DR-04.md`): Static Type System, Constrained Type Groups & Zero-Overhead Inference

```markdown
# Deep Research Request (DR-04): Strong Static Type System, Constrained Type Groups & Type Inference for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 bootstrap compiler (`stage0/corex`), `MultiArrayList` SoA arenas, `enum(u32)` handles (`0xFFFFFFFF` sentinel), page-aligned zeroed `BumpArena`, and `Wyhash(0)` `StringInterner`.
> - **`DR-02.md`:** Value-Oriented Algebraic Data-Oriented Hybrid (VO-ADOH) paradigm, Strict Mutable Value Semantics (MVS), `#soa` / `bit_field` / `SlotMap` primitives, mode-correct linear-time bidirectional typing, and Block-Argument SSA IR.
> - **`DR-03.md` (Authoritative for Surface Syntax):** Square-bracket generics (`Vec[T]`, `foo[T](x)`), `{ }` blocks, postfix `: Type` annotations, `T?` option sugar, `let`/`var`/`const` bindings, `;` statement termination, `@snake_case` attributes, and lexical casing (`PascalCase` `TYPE_IDENT`, `snake_case` `IDENT`, `SCREAMING_SNAKE_CASE` `CONST_IDENT`).

## Context & Vision
CoreX (`.cx`) requires a **strong, static type system** that maximizes both runtime performance and Language Server (`corex lsp`) intelligence while feeling effortless to write:
- **Smart Type Inference:** Catch nearly 100% of type errors at compile time with minimal annotation ceremony using the linear-time bidirectional typing foundation established in `DR-02`.
- **Constrained Type Groups / Aliases:** Include built-in and user-definable constrained type groups (e.g., using a generic `Number`, `Int`, or `Float` constraint directly in a function signature like `fn clamp(val: Number, low: Number, high: Number) -> Number`) that automatically resolve and monomorphize to concrete machine types (`i32`, `f64`, etc.) at compile time with **zero runtime boxing or vtable overhead**.

## Research Objectives
1. **Constrained Type Groups & Ergonomic Generics:**
   - Design the exact semantics of **Type Groups** (built-in groups like `Number`, `Signed`, `Unsigned`, `Integer`, `Float`, `Comparable`, `Numeric`, `Bytes`, and user-defined structural/nominal type unions or trait groups) using `DR-03`'s square-bracket generic syntax (`[T: Number]` and inline `val: Number` shorthand).
   - Specify how same-type vs. independent-type constraints work in signatures (e.g., when two parameters written with `Number` must unify to the *same* concrete type `T: Number` vs. independent numeric types, and how the syntax makes both cases effortless and unambiguous).
2. **Bidirectional Type Inference & Fast Compilation:**
   - Build upon `DR-02`'s Dunfield-Krishnaswami bidirectional typing rules ($\Rightarrow$ synthesis and $\Leftarrow$ checking) and local constraint solving.
   - Guarantee linear-time type checking (`>= 500,000` LOC/sec) with zero exponential overload disjunctions and preserve crisp error localization when code is incomplete in the IDE.
3. **Numeric Hierarchy, Literal Polymorphism & Overflow Safety:**
   - Design untyped/polymorphic numeric literals (adapting cleanly to the target concrete integer/float type in checking mode without noisy `as` casts, and defaulting cleanly in synthesis mode), explicit bit-width types (`i8`..`i128`, `u8`..`u128`, `isize`, `usize`, `f32`, `f64`), and compile-time vs. runtime integer overflow semantics.
4. **Algebraic Types, Null Safety & Refinement/Newtype Ergonomics:**
   - Formalize `T?` (`Option[T]`) niche-optimized enums, `distinct` newtypes, `#soa` slice typing, `bit_field` typing, and zero-cost constrained/refined types.

## Required Deliverables
1. **Formal Type System & Bidirectional Inference Specification** (typing judgments, constraint propagation algorithm, and complexity bounds).
2. **Constrained Type Groups Specification** detailing `.cx` syntax, unification semantics, monomorphization lowering, and error diagnostics.
3. **Compiler Data Structures (`TypeArena`, `TypeId`, `InternPool`, `SubstitutionMap`)** in Zig (for Stage 0) and `.cx` (for Stage 1) optimized for arena allocation and incremental query caching.

```

---

## `DR-05` (Plugs into `RDG-05` → `docs/research/DR-05.md`): Compile-Time Execution (`comptime`) & Metaprogramming Architecture

```markdown
# Deep Research Request (DR-05): Compile-Time Execution (`comptime`), Reflection & Metaprogramming for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 bootstrap compiler (`stage0/corex`), `MultiArrayList` SoA arenas, `enum(u32)` handles (`0xFFFFFFFF` sentinel), page-aligned zeroed `BumpArena`, and `Wyhash(0)` `StringInterner`.
> - **`DR-02.md`:** Value-Oriented Algebraic Data-Oriented Hybrid (VO-ADOH) paradigm, Strict Mutable Value Semantics (MVS), `#soa` / `bit_field` / `SlotMap` primitives, mode-correct linear-time bidirectional typing, and Block-Argument SSA IR.
> - **`DR-03.md` (Authoritative for Surface Syntax):** Square-bracket generics (`Vec[T]`, `foo[T](x)`), `{ }` blocks, postfix `: Type` annotations, `T?` option sugar, `let`/`var`/`const` bindings, `;` statement termination, `@snake_case` attributes, and lexical casing (`PascalCase` `TYPE_IDENT`, `snake_case` `IDENT`, `SCREAMING_SNAKE_CASE` `CONST_IDENT`).

## Context & Vision
CoreX (`.cx`) aims to shift as much computation, configuration validation, serialization routing, and boilerplate generation as possible from runtime to compile time, while keeping the language syntax simple, readable, and IDE/LSP-friendly. Notice in `DR-03` that CoreX uses `@snake_case` attributes (e.g., `@derive(Serialize)`, `@cli_command`, `@route`) and square-bracket generics (`[T, const N: usize]`).

## Research Objectives
1. **Comparative Evaluation of Metaprogramming Paradigms:**
   - **Zig-style `comptime`:** Executing regular `.cx` code at compile time without a separate macro sub-language.
   - **Rust-style Hygienic Declarative & Procedural Token-Stream Macros:** Powerful syntax extension, but notorious for compile-time slowdowns and degraded IDE/LSP autocomplete/refactoring.
   - **Compile-Time Type Reflection + Structured `@derive` / `@comptime` Mirror APIs (C++26 `std::meta` / Mojo / Zig `@typeInfo`):** Structured compile-time type introspection and code emission that integrates with `DR-02`'s definition-site checked generics (`[T]`).
2. **LSP & Incremental Compilation Compatibility (CRITICAL):**
   - Analyze how metaprogramming and `@derive` / `@route` attributes interact with `corex lsp` (go-to-definition, hover types, rename refactoring, completion) and incremental query caching. Ensure metaprogramming never blinds the Language Server or forces slow external proc-macro dylib compilations.
3. **Compiler Interpreter (`MIR` VM / Bytecode Evaluator) Design:**
   - Design an ultra-fast, deterministic compile-time evaluator (register/bytecode VM over Block-Argument SSA `MIR`) capable of evaluating arbitrary pure `.cx` functions, lookup table generation, regex/route compilation, and struct/enum field reflection (e.g., zero-overhead `std::serde` JSON and `std::cli` argument parsers) at compile time.
   - Specify sandboxing invariants (deterministic memory representation compatible with `DR-01`'s reproducible build rules, endianness handling for cross-compilation, step budgets `--comptime-limit`, and forbidden host syscalls).

## Required Deliverables
1. **Recommended Metaprogramming & Compile-Time Execution Architecture for CoreX:** `.cx` syntax, semantics, and capabilities (`comptime` blocks/parameters, `@derive` / attribute reflection hooks, compile-time struct/enum introspection, and static assertions) consistent with `DR-03`'s `LL(k)` grammar.
2. **`MIR` Compile-Time Virtual Machine Blueprint:** Memory layout of compile-time values/allocations, constant folding integration, and caching strategy inside the incremental query database.

```

---

## `DR-06` (Plugs into `RDG-06` → `docs/research/DR-06.md`): Zero-GC Automatic Memory Management, Manual Control & SAST Verifier

```markdown
# Deep Research Request (DR-06): Zero-GC Memory Model, Automatic Compile-Time Cleanup & Static Vulnerability Verifier (SAST) for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 bootstrap compiler (`stage0/corex`), `MultiArrayList` SoA arenas, `enum(u32)` handles (`0xFFFFFFFF` sentinel), page-aligned zeroed `BumpArena`, and path-sensitive `MIR` bitset dataflow foundation.
> - **`DR-02.md`:** Value-Oriented Algebraic Data-Oriented Hybrid (VO-ADOH) paradigm, Strict Mutable Value Semantics (MVS) with disjoint value trees, second-class references (`let`, `inout`, `sink`, `set`) + coroutine `subscript` (`yield`) projections, implicit `context.allocator`, and Ghost Lifetime Instructions on Block-Argument SSA `MIR`.
> - **`DR-03.md` (Authoritative for Surface Syntax):** Square-bracket generics (`Vec[T]`, `foo[T](x)`), `{ }` blocks, postfix `: Type` annotations, `T?` option sugar, `let`/`var`/`const` bindings, `defer` statements, and ownership/borrow surface tokens (`&`, `&mut`, `own`, `ref`).

## Context & Vision
CoreX's memory management has three strict requirements:
1. **No Runtime Tracing Garbage Collector:** Deterministic C-level speed and minimal memory footprint.
2. **Automatic Default with Compile-Time Safety:** Everyday coding must feel effortless—memory allocation and deallocation are handled automatically by the compiler by default **without forcing Rust-style lifetime annotation gymnastics (`<'a, 'b>`) on the developer**.
3. **Optional Manual Control + Built-In Static Vulnerability Analysis (SAST):** Power users can take explicit manual control over memory allocation, arenas, and raw layout when needed. To prevent manual or hybrid memory management from introducing C-style bugs, the compiler includes a built-in static analysis engine (SAST) and lifetime/ownership verifier on `MIR` that checks memory operations at compile time and emits crystal-clear errors/warnings for potential vulnerabilities (**use-after-free, double-free, memory leaks, dangling stack/arena escapes, uninitialized reads, and buffer overflows**).

## Research Objectives
1. **Unifying `DR-02` (MVS Parameter Modes) and `DR-03` (Surface Borrow/Ownership Tokens):**
   - `DR-02` established Hylo-style Strict Mutable Value Semantics (MVS) with second-class references (`let`, `inout`, `sink`, `set` + `subscript` projections), while `DR-03`'s EBNF grammar defined surface tokens `&`, `&mut`, `own`, and `ref`.
   - Synthesize and lock down the **single canonical surface mapping and semantic specification** (e.g., mapping default `param: T` / `&T` to immutable `let` projection, `&mut T` / `mut` to exclusive `inout` projection, `own T` to `sink` ownership transfer, and `out` / `set` to definite initialization) so the EBNF grammar in `DR-03` and the MVS exclusivity model in `DR-02` operate as one unified system.
2. **Synthesizing Automatic Scope Cleanup vs. Explicit `defer`:**
   - Resolve how automatic deterministic scope cleanup (for standard containers like `Vec[T]`, `String`, `Map[K, V]`) coexists with `DR-02`/`DR-03`'s `defer` / `errdefer` and linear resource verification (for manual allocations, `Arena`, `PoolAllocator`, `OwnPtr[T]`, sockets, and files).
   - Specify how cyclic graphs (`SlotMap[K, V]`), closures (`@local` vs. escaping), and async tasks are verified safely with zero GC and zero lifetime annotations.
3. **Built-In Static Vulnerability Analysis (SAST) & Symbolic Verifier on Block-Argument SSA `MIR`:**
   - Design the complete path-sensitive static analysis engine operating on `MIR` (`DR-01` & `DR-02`):
     - **Ghost-Instruction & Bitset Typestate Dataflow Analysis** for Use-After-Free (UAF), Double-Free, Uninitialized Reads, and Memory Leak detection across all CFG branches.
     - **Interprocedural Escape & Region/Arena Aliasing Summary Computation** (bottom-up SCC summary inference so functions returning projected views or taking arenas never require manual `'a` lifetime parameters while preventing arena/stack escapes).
     - **Abstract Interpretation / Integer Range Constraint Analysis** (intervals/octagons) for compile-time Buffer Overflow / Bounds Check Elimination.

## Required Deliverables
1. **Unified CoreX Memory & Ownership Specification:** Exact reconciliation of `DR-02` MVS modes and `DR-03` surface tokens (`&`, `&mut`, `own`, `ref`, `defer`), automatic scope drops vs. manual allocator control (`Arena`, `PoolAllocator`, `OwnPtr[T]`, raw `*T` / `*mut T` in `unsafe`).
2. **Formal `MIR` SAST & Lifetime Verification Algorithm:** Dataflow equations, lattice definitions, interprocedural function summary schema, arena-escape verification, range analysis for bounds-check elimination, and diagnostic generation rules (`E03xx`) for UAF, double-free, leaks, dangling escapes, and out-of-bounds accesses.

```

---

## `DR-07` (Plugs into `RDG-07` → `docs/research/DR-07.md`): Error Handling Model & Zero-Cost Propagation Semantics

```markdown
# Deep Research Request (DR-07): High-Performance, Ergonomic Error Handling Architecture for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 bootstrap compiler (`stage0/corex`), `MultiArrayList` SoA arenas, and `enum(u32)` handles.
> - **`DR-02.md`:** Value-Oriented Algebraic Data-Oriented Hybrid (VO-ADOH) paradigm, niche-optimized sum types, variant size skew mitigation (`#[warn(variant_size_skew)]`), value-based error handling (`E!T` / `try` / `catch` / `errdefer`), and Block-Argument SSA IR.
> - **`DR-03.md` (Authoritative for Surface Syntax):** Square-bracket generics (`Result[T, E]`), postfix `?` propagation (`File::open(path)?`), postfix `T?` option sugar (`Option[T]`), `let .Some(x) = expr else { return ... };` guards, and contextual `.Ok(v)` / `.Err(e)` / `.Some(v)` / `.None` variant shorthand.

## Context & Vision
CoreX (`.cx`) needs the cleanest, highest-performance error handling mechanism possible—one that makes error handling effortless and readable, guarantees compile-time exhaustiveness, and introduces **zero hidden control flow and zero runtime overhead** (no C++ DWARF stack-unwinding exceptions or heap-allocated stack traces on normal error paths).

## Research Objectives
1. **Reconciling `DR-02` and `DR-03` into a Unified Error Syntax & Type Representation:**
   - `DR-03` established `Result[T, E]`, `T?` (`Option[T]`), postfix `?` propagation (`req.read_body().await?`), contextual `.Ok(val)` / `.Err(err)` constructors, and `let ... else { ... }` guards. `DR-02` highlighted the performance benefits of Zig/Sutter `P0709` value error unions (`E!T`, `errdefer`, and side-band `Diagnostics` to prevent 512-byte error payloads from bloating hot return paths).
   - Evaluate whether CoreX should use **`Result[T, E]` + postfix `?`** as the canonical surface syntax (Optionally with `T ! E` or `Result[T, E]` sharing the exact same register-level value-return ABI and `errdefer` support!), and lock down the single authoritative surface syntax and grammar rules.
2. **Register-Level ABI & Codegen Performance Analysis:**
   - Analyze machine-code generation on `x86_64`, `aarch64`, and `wasm32`: how returning `(payload, error_tag)` in registers + CPU carry/zero flags (Herb Sutter `P0709` / Swift 6 typed `throws` / Zig error union ABI) compares against stack-spilled structs when `sizeof(E)` differs from `sizeof(T)`.
   - Specify how cold error payloads are automatically boxed or passed via side-band diagnostics so `Result[T, E]` never inflates register returns on the happy path.
3. **Ergonomics, Error Composition & Deterministic Scope Cleanup:**
   - How errors compose across module boundaries without noisy boilerplate ceremonies.
   - How postfix `?` interacts with `defer` and `errdefer` blocks and automatic scope drops (`DR-06`).
   - Distinguish recoverable domain errors (`Result[T, E]`) from unrecoverable contract violations (`panic` / `assert`).

## Required Deliverables
1. **Canonical Error Handling Specification for CoreX:** Unified `.cx` syntax for declaring fallible functions, propagating errors (`?`), pattern-matching/recovering (`match`, `let ... else`, `catch`), adding error context, and `defer` / `errdefer` cleanup.
2. **Register-Level ABI & Block-Argument SSA `MIR` Lowering Specification:** How `Result[T, E]` and `T?` (`Option[T]`) are represented in `MIR` and lowered to zero-allocation register/flag returns on `x86_64`, `aarch64`, and `wasm32`.

```

---

## `DR-08` (Plugs into `RDG-08` → `docs/research/DR-08.md`): Concurrency, Async/Structured Execution & High-Throughput I/O Model

```markdown
# Deep Research Request (DR-08): Optimal Concurrency, Structured Async & High-Performance I/O Architecture for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`, `DR-06`, `DR-07`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 bootstrap compiler, `MultiArrayList` SoA arenas, and three-tier backend architecture.
> - **`DR-02.md`:** VO-ADOH paradigm, Strict Mutable Value Semantics (MVS) with disjoint value trees, implicit `context` (`context.allocator`), and Block-Argument SSA IR.
> - **`DR-03.md` (Authoritative for Surface Syntax):** `async fn`, postfix `.await` (`req.read_body().await?`), square-bracket generics (`[T]`), `{ }` blocks, and lexical casing (`PascalCase` `TYPE_IDENT`, `snake_case` `IDENT`).
> - **`DR-06.md` & `DR-07.md`:** Zero-GC ownership/exclusivity & SAST verifier on `MIR`, `Arena` lifetime checking, and zero-cost `Result[T, E]` + `?` error propagation.

## Context & Vision
CoreX targets both **high-throughput, low-latency web backends/APIs** (handling hundreds of thousands of concurrent connections with minimal tail latency and memory) and **responsive TUI/Wasm/native UI applications**, all under a **zero-GC, statically verified MVS memory model** with zero cold-start overhead.

## Research Objectives
1. **Concurrency & Async Execution Model:**
   - Evaluate how `DR-03`'s `async fn` and postfix `.await` lower into state machines (stackless coroutines) vs. stackful fibers, and how CoreX avoids heap allocation per `.await` call via caller-allocated / arena-allocated task frames.
   - Evaluate memory footprint per concurrent task, C FFI call compatibility, compilation speed, and how synchronous and asynchronous code interoperate cleanly.
2. **Structured Concurrency & Zero-GC Memory Unification (`TaskGroup` / Scoped Nurseries):**
   - Design structured task scopes (`TaskGroup` / scoped nurseries) where child tasks are lexically bounded by their parent scope (`defer` / scope exit awaits and cancels all child tasks).
   - **Crucial MVS Synergy:** Prove how structured concurrency unifies with `DR-02`/`DR-06`'s zero-GC MVS memory model: because child tasks in a `TaskGroup` cannot outlive their lexical parent scope, spawned tasks can safely borrow immutable `let` data or disjoint `&mut` (`inout`) slice partitions and per-request `Arena` allocators without requiring `Arc[Mutex[T]]` heap wrappers or `'static` lifetime bounds!
3. **Compile-Time Data-Race Freedom in the `MIR` SAST Verifier:**
   - Specify how the `MIR` SAST verifier (`DR-06`) proves data-race freedom across OS threads and async tasks (via MVS disjoint ownership transfer `own`, immutable `let` sharing, and linear channel transfers) with zero annotation clutter.
4. **OS-Native Completion I/O Reactor Architecture:**
   - Design the cross-platform completion-based I/O engine (`io_uring` on Linux, `IOCP` on Windows, `kqueue` on macOS, and browser/WASI event loop integration on `wasm32`), comparing thread-per-core (share-nothing) vs. work-stealing schedulers and how registered I/O buffers interact safely with `DR-06` cancellation/cleanup.

## Required Deliverables
1. **CoreX Concurrency & Structured Task Specification:** `.cx` language primitives (`async fn`, `.await`, `TaskGroup`, channels, cancellation tokens), MVS borrowing rules across concurrent tasks, and compile-time data-race verification rules.
2. **Compiler Lowering & Runtime Scheduler Blueprint:** Coroutine state-machine lowering in Block-Argument SSA `MIR`, task-frame arena layout, and the OS completion ring (`io_uring` / `IOCP` / `kqueue` / `wasm32`) interface.

```

---

## `DR-09` (Plugs into `RDG-09` → `docs/research/DR-09.md`): Dual-Mode Compiler Backend Architecture (Instant Dev vs. Production AOT)

```markdown
# Deep Research Request (DR-09): Dual-Mode Compiler Backend Architecture (Instant Dev Mode vs. Optimizing Production AOT) for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`, `DR-06`, `DR-13`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md` (`ADR-001`):** Establishes the three-tier backend direction: Tier A Self-Hosted C99 Emitter (`-ofmt=c` for `wasm32-wasi` bootstrapping), Tier B Production Optimizing Backend (static LLVM 20–23 + embedded `lld::lldMain` via isolated `src/corex_llvm.cpp`), and Tier C Fast Debug Backend (custom direct `x86_64`/`AArch64` machine-code emitter bypassing LLVM in `-O0` / `--dev` builds).
> - **`DR-02.md` & `DR-03.md`:** Strict MVS `noalias` parameter guarantees, `cx` ABI calling convention (<=16B in registers, >16B `const noalias` pointer), and `.cx` surface syntax.
> - **`DR-06.md` & `DR-13.md`:** Block-Argument SSA `MIR`, SAST range/bounds proofs, and `MIR` optimization pipeline.

## Context & Vision
CoreX requires a **Dual-Mode Compilation Pipeline**:
- **Development Mode (`corex run`, `corex build --dev`):** Instantaneous compilation (`>= 500,000` LOC/sec, sub-50ms incremental rebuilds) that skips heavy optimization passes so the developer feedback loop feels instant regardless of project size.
- **Production Mode (`corex build --release`):** Ahead-of-Time (AOT) compilation with maximum optimization passes producing native machine code that matches or outperforms C (`clang -O3`) and Rust (`rustc -O`), plus compact `wasm32` output.

## Research Objectives
1. **Deepening & Specifying the `ADR-001` Three-Tier Backend Architecture:**
   - Detail the exact engineering architecture of the **Fast Dev Backend (`--dev`)**: how the in-tree direct machine-code emitter (`x86_64`, `aarch64`, `wasm32`) and `-ofmt=c` backend are structured for single-pass lowering from Block-Argument SSA `MIR` (including fast linear-scan/tree register allocation and in-place binary patching for sub-50ms incremental rebuilds).
   - Detail the **Production AOT Backend (`--release`)**: how `src/corex_llvm.cpp` + `src/corex_llvm.h` bridges `MIR` to LLVM 20–23 and embedded `lld::lldMain` without bloated C++ header dependencies across the compiler.
2. **Exploiting CoreX Semantic Invariants to Beat C/C++ in `--release` Mode:**
   - Specify how CoreX's `DR-02`/`DR-06` guarantees (strict MVS `noalias` on all `let`, `&mut`/`inout`, and `own`/`sink` parameters, SAST-proven integer bounds ranges, and `#soa` contiguous column pointers) are lowered into LLVM IR metadata (`noalias`, `nonnull`, `dereferenceable`, `!range`, `llvm.loop.vectorize`, TBAA) so LLVM auto-vectorizes and optimizes `.cx` code more aggressively than C or C++.
3. **Unified `CodegenBackend` Interface & Zero Dev/Prod Divergence:**
   - Design the exact `CodegenBackend` interface in Zig (Stage 0) and `.cx` (Stage 1) consuming verified `MIR` so that `--dev` (direct emitter), `-ofmt=c` (bootstrap C emitter), and `--release` (LLVM AOT) share 100% identical struct layout, niche computation, and ABI lowering rules.

## Required Deliverables
1. **Complete `CodegenBackend` Interface & `MIR` Lowering Specification** (covering the direct `--dev` emitter, `-ofmt=c`, and `corex_llvm.cpp` `--release` backend).
2. **Fast Direct Machine-Code Emitter & In-Place Incremental Binary Patching Blueprint** (ELF/Mach-O/PE/Wasm function slot patching for sub-50ms rebuilds).
3. **LLVM Optimization Pass Pipeline & Alias/Range Metadata Lowering Specification.**

```

---

## `DR-10` (Plugs into `RDG-10` → `docs/research/DR-10.md`): Cross-Compilation, Zero-Dependency Linking, C FFI & WebAssembly (`wasm32`)

```markdown
# Deep Research Request (DR-10): Cross-Compilation, Standalone Static/Dynamic Linking, C FFI & WebAssembly (`wasm32`) Pipeline for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`, `DR-06`, `DR-07`, `DR-13`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 bootstrap compiler, embedded `lld::lldMain` (`lld/ELF`, `COFF`, `MachO`, `wasm`), and deterministic linker flag matrix.
> - **`DR-02.md` & `DR-03.md`:** `extern fn`, `@repr(C)` / `#[repr(C)]`, `bit_field`, `union`, and `.cx` surface syntax.
> - **`DR-06.md`, `DR-07.md`, & `DR-13.md`:** Zero-GC memory/SAST boundary checks, register-level error ABI, and `MIR` representation.

## Context & Vision
CoreX must effortlessly cross-compile from any host machine (Windows, Linux, macOS) to all major targets (`x86_64` and `aarch64` Linux, macOS, Windows, and `wasm32`) out of the box—without forcing the user to install gigabytes of platform SDKs, Xcode, or Visual Studio build tools. Users must be able to choose between compiling a **single standalone static executable** or **dynamically linked binaries/libraries**, and call **C libraries (FFI)** with zero overhead.

## Research Objectives
1. **Out-of-the-Box Cross-Compilation & Embedded `lld` Linker Architecture:**
   - Specify how `corex` invokes embedded `lld::lldMain` (`lld::elf::link`, `lld::macho::link`, `lld::coff::link`, `lld::wasm::link`) in-process and how the `--dev` backend emits object files or links directly.
   - Detail how `corex` bundles or lazily synthesizes minimal target libc/syscall import stubs (`musl` for static Linux, `.tbd` text-based stub libraries for macOS `libSystem`, `.def`/import libraries for Windows `kernel32.dll`/`ntdll.dll`/`ucrtbase.dll`) so cross-compilation requires kilobyte-scale definitions rather than multi-gigabyte SDKs.
2. **Standalone Static (`--link=static`) vs. Dynamic (`--link=dynamic`) Linking Modes:**
   - Specify how `--link=static` and `--link=dynamic` (plus building shared libraries `.so`/`.dylib`/`.dll` and static archives `.a`/`.lib`) work on Linux, macOS, and Windows.
3. **Zero-Overhead C Interoperability (FFI) & SAST Boundary Safety:**
   - Design `.cx` C FFI ergonomics (`extern "C" fn`, `@repr(C) struct`, C header binding generation `corex bindgen` or direct header import).
   - Specify exact C ABI calling convention rules (`SysV AMD64`, `Win64`, `AAPCS64`, `wasm32` C ABI) for structs-by-value, bitfields, SIMD vectors, and function pointer callbacks.
   - Define SAST boundary annotations (`@trusted`, `@null_terminated`, `@owned_by_caller`, slice length coupling) so the `MIR` SAST verifier (`DR-06`) checks pointers crossing C FFI boundaries.
4. **First-Class WebAssembly (`wasm32`) Pipeline:**
   - Target both `wasm32-wasi` (for server/CLI Wasm) and `wasm32-freestanding` (for ultra-small browser web apps), including `SIMD128`, bulk-memory, tail-call proposals, and dead-code stripping for `< 10 KB` baseline `.wasm` bundles.

## Required Deliverables
1. **Cross-Compilation, Target Sysroot Stub & Embedded `lld` Linker Blueprint.**
2. **C FFI Syntax, ABI Lowering Matrix & SAST FFI-Boundary Verification Rules.**
3. **WebAssembly (`wasm32-wasi` & `wasm32-freestanding`) Codegen & Host-Bridge Specification.**

```

---

## `DR-11` (Plugs into `RDG-11` → `docs/research/DR-11.md`): Package Manager, URL/Registry Resolution, Global Cache & Lockfiles

```markdown
# Deep Research Request (DR-11): Zero-Friction Package Management, Content-Addressable Global Cache & Reproducible Lockfile Architecture for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Deterministic build invariants, `BumpArena`, and `SourceMap` `FileId(u32)` ordering.
> - **`DR-02.md` & `DR-03.md`:** `kebab-case` package names in `corex.toml`, `snake_case` module names (`mod`, `use std::fs::{File, BufReader};`), and `.cx` syntax.

## Context & Vision
CoreX's package management must combine zero-friction developer ergonomics with rock-solid reproducibility and disk efficiency:
- **Zero-Friction Imports:** Developers can reference packages directly via short registry IDs or URLs (e.g., GitHub repositories), and `corex run` / `corex build` automatically fetches and resolves them on demand.
- **Content-Addressable Global Cache:** Downloaded packages are stored once in a centralized, content-addressable global cache on the machine (`~/.corex/cache`, avoiding duplicate downloads or duplicate files across projects) while using project-level lockfiles (`corex.lock`) for reproducible builds.

## Research Objectives
1. **Source Import & `corex.toml` Manifest Ergonomics:**
   - Design how `.cx` files and `corex.toml` manifests reference external packages (both registry packages and direct GitHub/Git URLs `[github.com/org/pkg@v1.2.0](https://github.com/org/pkg@v1.2.0)`, plus single-file `.cx` script imports) and how `corex` auto-synchronizes them without manual `install` rituals.
2. **Version Resolution Algorithm:**
   - Compare **Minimal Version Selection (MVS)** (Go's $O(V+E)$ deterministic algorithm requiring no SAT solver) vs. **PubGrub** (conflict-driven clause learning with human-readable error explanations).
   - Specify how diamond dependencies, major-version coexistence, feature flags, and local path overrides are handled.
3. **Content-Addressable Global Store (`~/.corex/cache`):**
   - Design the content-addressable storage layout using **BLAKE3** Merkle tree hashing (per-file content blobs + package directory manifest trees).
   - Analyze concurrent multi-process file locking, atomic cache writes, and **zero-copy VFS mapping** (mapping cached `.cx` files directly from the global read-only content store into the compiler's `SourceMap` without needing per-project `node_modules`-style copies!).
4. **Static Git/HTTP Registry Protocol & Cryptographic Supply-Chain Security:**
   - Design a static index / GitHub-compatible sparse registry protocol plus cryptographic BLAKE3 hash pinning and signature verification in `corex.lock`.

## Required Deliverables
1. **Complete `.cx` Package Import Rules, `corex.toml` Manifest & `corex.lock` Schemas.**
2. **Global Content-Addressable Cache (`~/.corex/cache/blake3/`) & Zero-Copy VFS Mapping Specification.**
3. **Dependency Resolution Algorithm & Offline/Hermetic Build Protocol.**

```

---

## `DR-12` (Plugs into `RDG-12` → `docs/research/DR-12.md`): Incremental Query Engine, Fault-Tolerant Lossless CST & Built-in LSP

```markdown
# Deep Research Request (DR-12): Fault-Tolerant Lossless CST, Incremental Query Engine & Built-in Language Server (`corex lsp`) Architecture

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 implementation, `MultiArrayList` SoA storage, `u32` handles (`TokenIndex`, `NodeIndex`, `StringId`), and Section 2.2's recommendation of Carbon-style **Flat Postorder Parse Trees with Explicit State Stack** over pointer-heavy Red-Green trees.
> - **`DR-02.md`:** Linear-time mode-correct bidirectional type checking ($\Rightarrow$ synthesis / $\Leftarrow$ checking) and MVS parameter modes.
> - **`DR-03.md` (Authoritative for Surface Syntax):** 92-variant stateless `TokenKind` table, `LL(k)` + Pratt EBNF grammar, `[T]` vs. `[i]` `LL(1)` disambiguation via lexical casing (`TYPE_IDENT` vs. `IDENT`), and `;` statement termination.

## Context & Vision
CoreX packages a built-in Language Server (`corex lsp`), linter (`corex check`), and code formatter (`corex fmt`) directly inside the `corex` compiler binary. The compiler's lexer, parser, CST/AST, and semantic analyzer must be architected from Phase 1 around **fault-tolerant lossless syntax trees and demand-driven incremental computation** so editor interactions respond in `< 5 ms` even on 500,000-line codebases.

## Research Objectives
1. **Lossless Contiguous CST (`LosslessCstArena`) & Typed AST (`AstArena`) Architecture:**
   - Build upon `DR-01` Section 2.2 (Carbon-style flat postorder/bracketed SoA parse tree with explicit parser state stack, `MAX_PARSE_DEPTH = 512`) and `DR-03`'s 92-token grammar.
   - Specify how 100% of source bytes—including comments, blank lines, whitespace trivia, and malformed tokens—are represented losslessly alongside the SoA `TokenBuffer` so `corex fmt`, `corex upgrade`, and `corex lsp` round-trip any `.cx` file bit-for-bit without heap-pointer tree overhead.
2. **Fault-Tolerant Parsing & Bidirectional Type Recovery for Incomplete Code:**
   - Specify exact synchronization anchor sets for `DR-03`'s grammar (recovering cleanly at `;`, `{`, `}`, and top-level item starters `pub`, `fn`, `struct`, `enum`, `trait`, `impl`, `let`, `var`).
   - Specify how placeholder `Error` nodes propagate through `DR-02`'s bidirectional type checker (`Type::Error` unifying silently without cascading secondary errors) so autocomplete (`user.`) and signature help (`repo.find(`) work accurately while code is broken mid-keystroke.
3. **Demand-Driven Incremental Query Engine (`CompilerDb`) with Early Cutoff:**
   - Design the fine-grained query database (`parse_cst(FileId)` -> `lower_ast(FileId)` -> `item_tree(FileId)` -> `resolve_signatures(ModuleId)` -> `typecheck_body(DefId)` -> `verify_sast_mir(DefId)`).
   - Detail the **Early Cutoff** BLAKE3/Wyhash fingerprint mechanism: editing inside a function body re-parses that file and re-checks only that single `DefId` because the file's exported signature table fingerprint is unchanged.
4. **Built-In `corex lsp` Server Architecture:**
   - JSON-RPC 2.0 transport over stdio, lock-free cancellation of stale in-flight queries on `textDocument/didChange`, in-memory `Vfs` overlay buffers, semantic tokens, inlay hints (inferred `: Type`, implicit MVS borrow/move markers), and machine-applicable `CodeFix` actions.

## Required Deliverables
1. **Byte-Exact Data Structure Blueprint for `TokenBuffer`, `LosslessCstArena`, and `AstArena`** in Zig (Stage 0) and `.cx` (Stage 1).
2. **Fault-Tolerant Recovery Rules & Partial-AST Bidirectional Typing Rules** for `DR-03`'s grammar.
3. **Incremental Query Database (`CompilerDb`) & Early-Cutoff Invalidation Algorithm.**

```

---

## `DR-13` (Plugs into `RDG-13` → `docs/research/DR-13.md`): Intermediate Representations (`HIR` & SSA `MIR`) & Optimization Pipeline

```markdown
# Deep Research Request (DR-13): High-Level IR (`HIR`), Mid-Level SSA IR (`MIR`) & Optimization Pipeline for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md`:** Zig Stage-0 implementation, `MultiArrayList` SoA storage, `u32` handles (`MirBlockId`, `MirValueId`, `TypeId`, `PackedOperand`, `MirLocation`), and dense `[]u64` bitsets.
> - **`DR-02.md`:** Establish **Block-Argument SSA IR** (MLIR `cf` / Cranelift CLIF / Swift SIL style with Braun forward SSA construction), **Maranget Pattern Matrix Decision Trees** with Jacobs clause-frequency heuristics, **Ghost Lifetime Instructions** (`access.let`, `access.inout`, `access.end`, `storage.move`, `storage.init`, `storage.deinit`), `#soa` field-pointer rewriting, and pointer-shape generic deduplication.
> - **`DR-03.md` (Authoritative for Surface Syntax):** `.cx` expressions, `[T]` generics, `|>` pipelines, `defer`, `?` propagation, and `match` patterns.

## Context & Vision
To support CoreX's compile-time evaluator (`comptime`), static vulnerability & memory verifier (`SAST`), automatic deterministic cleanup, and dual-mode backends (`--dev` and `--release`), the compiler needs clean, cache-friendly Intermediate Representations between the frontend `AST` and backend codegen.

## Research Objectives
1. **High-Level IR (`HIR`) Design & Desugaring:**
   - Define the exact lowering from `AstArena` (`DR-03`) to `HIR`: desugaring `|>` pipelines, postfix `?` error/option propagation, `for x in iter` loops, `let ... else` guards, string interpolation `"{x}"`, `#soa` element projection rewriting (`slice[i].field` -> `slice.field_ptr[i]`), and `bit_field` subscript synthesis (`DR-02`).
2. **Block-Argument SSA `MIR` with Place Projections & Ghost Instructions:**
   - Formalize the instruction and terminator catalog for CoreX's **Block-Argument SSA `MIR`** (`DR-02`).
   - Detail how memory places (`Place { base: LocalId, projections: Slice[Projection] }`) coexist with pure SSA register values and `DR-02`'s Ghost Lifetime Instructions (`access.let`, `access.inout`, `access.end`, `storage.*`) so the Phase 6 SAST & exclusivity verifier can reason precisely about disjoint struct fields (`&r.pos.x` vs. `&r.dim.y`), and then erase ghost instructions and promote non-escaped places into pure SSA values (SROA / `mem2reg`).
3. **Pass Ordering & Monomorphization Bloat Mitigation:**
   - Specify the exact `MIR` pass pipeline for `--dev` (minimal fast passes: ghost verification, drop/defer elaboration, monomorphization) vs. `--release` (inlining, SROA, Maranget switch fusion, SAST-driven bounds-check elimination, constant folding, dead-block/dead-code elimination, and `DR-02` pointer-shape identical code folding).
   - Define the `MIR` well-formedness verifier invariants checked after every pass.

## Required Deliverables
1. **Complete `HIR` and Block-Argument SSA `MIR` Instruction, Place & Terminator Catalog** with compact arena-allocated SoA data structures in Zig (Stage 0) and `.cx` (Stage 1).
2. **`AST` -> `HIR` -> `MIR` Lowering Algorithms** (including Braun SSA construction, Maranget decision-tree lowering, and `defer`/`errdefer` CFG edge elaboration).
3. **`MIR` Pass Ordering, Verification Invariants & Polymorphic Code-Bloat Mitigation Specification.**

```

---

## `DR-14` (Plugs into `RDG-14` → `docs/research/DR-14.md`): Zero-Legacy AST Migration Engine (`corex upgrade`) & Formatter (`corex fmt`)

```markdown
# Deep Research Request (DR-14): Zero-Legacy Automated Migration Engine (`corex upgrade`) & Canonical Formatter (`corex fmt`) for CoreX (.cx)

> **Attached Baseline Specifications (`DR-01`–`DR-03`, `DR-12`):** Align all designs and `.cx` code snippets with the attached baseline reports:
> - **`DR-01.md` & `DR-12.md`:** `LosslessCstArena`, `TokenBuffer` trivia representation, and `DiagnosticSink` machine-applicable `CodeFix` byte replacements.
> - **`DR-02.md` & `DR-03.md` (Authoritative for Surface Syntax & Formatting Rules):** Deterministic block-aware `;` statement termination, 4-space indentation, same-line `{`, trailing commas on multiline lists, leading `|>` / `.` multiline chains, and compiler-enforced lexical casing (`PascalCase` `TYPE_IDENT`, `snake_case` `IDENT`, `SCREAMING_SNAKE_CASE` `CONST_IDENT`).

## Context & Vision
CoreX enforces a strict **Zero-Legacy Compiler Philosophy**:
> *"Do not bloat or slow down the compiler with backward-compatibility branches for old language versions. The compiler should only ever target the current specification to stay as lean and fast as possible; if breaking syntax or standard library improvements are introduced in future versions, the built-in tooling should provide an automated migration command (`corex upgrade` / `corex fix`) that rewrites older `.cx` source code to the newest spec."*

Additionally, CoreX includes a deterministic built-in formatter (`corex fmt`) implemented in Phase 3 so all `.cx` code in the repository and ecosystem is canonically formatted from day one.

## Research Objectives
1. **Canonical Pretty-Printing & Formatting Engine (`corex fmt`):**
   - Design the Wadler-Lindig / `Doc` algebra (`Group`, `Indent`, `Line`, `SoftLine`, `IfBreak`, `LineSuffix`) operating directly over `DR-12`'s `LosslessCstArena` to enforce `DR-03`'s exact formatting rules.
   - Specify comment-attachment, blank-line preservation, and `corex fmt --fix` automatic casing/semicolon normalization so `corex fmt` is 100% idempotent (`fmt(fmt(x)) == fmt(x)`) and formats `>= 1,000,000` LOC/sec.
2. **Zero-Legacy Automated Source Migration Architecture (`corex upgrade`):**
   - Design `corex upgrade` so that **zero legacy grammar branches or deprecated AST nodes ever pollute the main compiler pipeline**:
     - How versioned migration rules (`v1.0 -> v1.1`, etc.) are represented as isolated CST token/pattern rewrite rules and semantic API rename tables inside the `upgrade` tool subsystem.
     - How `corex.toml` tracks the project's spec version (`corex = "1.0"`), detects when a project or cached dependency targets an older spec, and executes a one-command lossless upgrade (`corex upgrade`) preserving all comments and formatting.
     - How `DiagnosticSink` machine-applicable `CodeFix` edits unify with `corex fix` and `corex upgrade`.

## Required Deliverables
1. **`corex fmt` Document Algebra, Trivia-Attachment & Formatting Rules Specification** for `DR-03`'s grammar.
2. **`corex upgrade` Zero-Legacy Migration Engine Blueprint** (declarative CST/semantic rewrite rule representation, `corex.toml` version gating, and conflict-free byte-patch application).

```

---

## `DR-15` (Plugs into `RDG-15` → `docs/research/DR-15.md`): Stage-2 `.cx` Standard Library, TUI/CLI & Unified WebAssembly/Native UI Architecture

```markdown
# Deep Research Request (DR-15): Stage-2 Batteries-Included Standard Library (`std`), TUI/CLI Engine & Unified WebAssembly/Native App Architecture in CoreX (.cx)

> **Attached Baseline Specifications (`DR-02`–`DR-08`):** Align all designs and `.cx` code signatures with the attached baseline reports:
> - **`DR-02.md`:** VO-ADOH paradigm, Strict MVS parameter modes, implicit `context` (`context.allocator`, `context.logger`), `#soa` slices, `bit_field`, `SlotMap[K, V]` generational arenas, `Span16` unboxed HTTP spans, `simdjson`-style 64-bit contiguous JSON tape, Ratatui-style buffer-diffing TUI, and Xilem/Masonry-style `SlotMap` + `IdPath` + `Adapt` lens reactive UI architecture.
> - **`DR-03.md` (Authoritative for Surface Syntax):** Square-bracket generics (`Vec[T]`, `Result[T, E]`), `T?` option sugar, `@snake_case` attributes (`@cli_command`, `@arg`, `@route`, `@derive`, `@component`, `@state`), trailing declarative view blocks (`Card(padding: 16) { ... }`), and canonical casing (`PascalCase` types/variants, `snake_case` functions/methods/fields).
> - **`DR-04.md`–`DR-08.md`:** Constrained Type Groups (`Number`), `comptime` reflection, zero-GC `Arena` / `PoolAllocator` / MVS ownership, `Result[T, E]` + `?` error handling, and `TaskGroup` structured async I/O (`io_uring` / `IOCP` / `kqueue` / `wasm32`).

## Context & Vision
CoreX follows a **Two-Stage Standard Library** strategy:
- **Stage 1:** Minimal `core` intrinsics and OS syscall bindings inside the compiler bootstrap phase.
- **Stage 2:** A rich, "batteries-included", modular, tree-shakeable standard library written **100% in CoreX (`.cx`)** covering my primary personal and general-purpose use cases:
  1. Writing zero-cold-start, ultra-fast **CLI tools** and rich **Terminal UIs (TUIs)**.
  2. Building high-throughput, low-latency, lightweight **web backends and APIs**.
  3. Building snappy, lightweight, and visually polished **web applications (via WebAssembly `wasm32`) and native apps** without needing a separate frontend language (no JS/TS framework bloat).

## Research Objectives
1. **Modular, Tree-Shakeable `std` Package Hierarchy:**
   - Design the exact module hierarchy (`std::mem`, `std::col`, `std::str`, `std::io`, `std::fs`, `std::cli`, `std::tui`, `std::async`, `std::net`, `std::http`, `std::serde`, `std::crypto`, `std::ui`, `std::test`, `std::bench`) so importing a single module incurs zero dead-code or cold-start overhead.
   - Specify how `std` containers (`Vec[T]`, `Map[K, V]`, `SlotMap[K, V]`, `String`) integrate `DR-02`'s implicit `context.allocator` with explicit `&mut Arena` overrides.
2. **World-Class `std::cli` & `std::tui` Architecture:**
   - **`std::cli`:** Zero-allocation `comptime`-generated argument/flag/subcommand parser driven by `@cli_command`, `@arg`, and `@flag` attributes (`DR-03` Showcase 1) with automatic monochrome Unicode box-drawing (`╭`, `│`, `╰`, `▸`, `✓`, `✗`, `⚠`) + ANSI help generation (strictly zero colored emojis).
   - **`std::tui`:** High-performance Terminal UI engine building on `DR-02`'s double-buffered `Cell` grid, Cassowary/Flexbox layout solver, cell-level diff renderer, raw-mode mouse/keyboard/resize event stream, and synchronized terminal output (`DECSET 2026`) for tear-free 120 FPS rendering.
3. **High-Throughput `std::http` & `std::serde` Architecture:**
   - Zero-copy HTTP/1.1, HTTP/2, and WebSocket server/client using `DR-02`'s unboxed `Span16` parser, per-request `context.allocator` bump arena, `@route` attribute router (`DR-03` Showcase 2), and `comptime`-specialized `std::serde` (featuring `DR-02`'s 64-bit contiguous `simdjson` tape and zero-copy struct serialization).
4. **Unified `std::ui` for WebAssembly (`wasm32`) & Native Apps (Zero JS Framework):**
   - Flesh out `DR-02` & `DR-03` Showcase 4's reactive UI architecture (`@component`, `@state`, `Signal[T]`, trailing view blocks `Card(...) { ... }`, `SlotMap[WidgetId, WidgetNode]`, and `IdPath` + `Adapt` lens `&mut AppState` routing).
   - Specify the dual-target rendering backend: how the exact same `.cx` component tree compiles to (a) surgical binary DOM/Canvas2D/WebGPU command buffers over a tiny (`< 3 KB`) `wasm32` host bridge in the browser, and (b) hardware-accelerated native OS windows on desktop.

## Required Deliverables
1. **Complete `std` Module Map & Canonical `.cx` Public API Signatures** across all 15 `std::*` modules, strictly adhering to `DR-03` syntax and casing rules.
2. **Technical Blueprint for `std::cli` and `std::tui`** (double-buffered cell renderer, layout solver, and monochrome Unicode glyph widget toolkit).
3. **Technical Blueprint for `std::http` / `std::serde` and the Unified `std::ui` (`wasm32` + Native) Application Engine.**

```

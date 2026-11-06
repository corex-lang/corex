---
name: bench
description: Runs and tracks continuous performance benchmarks for CoreX compilation speed, binary size, cold-start latency, and runtime execution speed against C and Rust baselines.
---

# Bench

Use this skill to execute, record, and analyze the continuous performance benchmark suite for `corex`, ensuring CoreX meets its targets for instant compilation, minimal footprint, zero cold-start, and C-level runtime execution speed.

---

## 1. Benchmark Dimensions & Targets

Every milestone must track four core metrics across standardized workloads in `bench/`:

| Metric                         | CoreX Target                                                      | Baselines Compared                 |
| ------------------------------ | ----------------------------------------------------------------- | ---------------------------------- |
| **Compilation Throughput**     | `>= 500,000` LOC/sec in `--dev` mode; competitive AOT in `--release` | `clang -O0` / `-O3`, `rustc`, `zig` |
| **Cold-Start Latency**         | `< 1.5 ms` process startup to first instruction (`Hello World` / CLI) | C (`clang -O3`), Rust (`rustc -O`) |
| **Binary Footprint**           | Minimal stripped static/dynamic binary size (`KB`, not multi-`MB`) | C (`clang -Oz`), Rust (`opt-level=z`), Go |
| **Runtime Execution Speed**    | Within `<= 1.00x` (matching or beating) C (`clang -O3`) and Rust  | C (`clang -O3`), Rust (`rustc -C opt-level=3`) |
| **Compiler Peak Memory (RSS)** | Linear scaling `< 150 MB` per `100,000` LOC compiled              | Host OS peak RSS measurement       |

---

## 2. Standard Benchmark Workloads (`bench/suites/`)

1.  **Micro-Benchmarks (`bench/suites/micro/`):**
    -   Tight numeric loops, SIMD-vectorizable array kernels, matrix multiplication, sorting, hash table lookups, string parsing, and UTF-8 validation.
2.  **Memory & Allocation Benchmarks (`bench/suites/memory/`):**
    -   Scope-based deterministic cleanup throughput, arena allocation patterns, tree/graph traversal under automatic memory management vs. manual layout control.
3.  **Concurrency & I/O Benchmarks (`bench/suites/io_async/`):**
    -   High-concurrency task scheduling, HTTP/socket echo throughput, file streaming, and zero-copy buffer pipelines.
4.  **Compiler Scaling Corpus (`bench/suites/compiler_scale/`):**
    -   Synthetic and real `.cx` codebases at `1,000`, `10,000`, `100,000`, and `500,000` lines of code measuring cold build, warm cache build, and single-file incremental LSP/dev recompile latency.

---

## 3. Execution & Statistical Discipline

1.  **Warmup & Pinned Runs:** Run at least 5 warmup iterations followed by `>= 30` measured iterations per workload, reporting median, minimum, P95, and standard deviation.
2.  **Regression Gate:** Any commit that degrades compilation throughput, cold-start latency, binary size, or runtime speed by `> 2%` on any workload without an explicit architectural justification fails the benchmark gate.
3.  **Terminal Output Aesthetic:** Benchmark runner tables must use the canonical CoreX monochrome Unicode box-drawing (`╭`, `│`, `╰`, `├`, `─`) and glyph (`▸`, `✓`, `✗`, `⚠`) renderer per `AGENTS.md` Section 5.

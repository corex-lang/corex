---
name: bench
description: Runs and tracks continuous performance benchmarks for CoreX compilation speed, LSP latency, binary size, cold-start latency, and runtime execution speed against C and Rust baselines.
---

# Bench

Use this skill to execute, record, and analyze the continuous performance benchmark suite for `corex`, ensuring CoreX meets its targets for instant compilation, sub-10ms IDE responsiveness, minimal footprint, zero cold-start, and C-level runtime execution speed.

---

## 1. Benchmark Dimensions & Targets

Every milestone must track six core metrics across standardized workloads in `bench/`:

| Metric                          | CoreX Target                                                            | Baselines Compared                               |
| ------------------------------- | ----------------------------------------------------------------------- | ------------------------------------------------ |
| **Compilation Throughput**      | `>= 500,000` LOC/sec in `--dev` mode; competitive AOT in `--release`    | `clang -O0` / `-O3`, `rustc`, `zig`              |
| **Incremental `corex lsp` P99** | `< 10 ms` P99 keystroke-to-diagnostic, completion, hover, & delta       | Measured on a persistent `100,000`-LOC workspace |
| **Cold-Start Latency**          | `< 1.5 ms` process startup to first instruction (`Hello World` / CLI)   | C (`clang -O3`), Rust (`rustc -O`)               |
| **Binary & Toolchain Size**     | `< 1 MB` compressed self-hosted `corex`; `< 10 KB` freestanding `.wasm` | C (`clang -Oz`), Rust (`opt-level=z`), Go        |
| **Runtime Execution Speed**     | Within `<= 1.00x` (matching or beating) C (`clang -O3`) and Rust        | C (`clang -O3`), Rust (`rustc -C opt-level=3`)   |
| **Compiler Peak Memory (RSS)**  | Linear scaling `< 150 MB` per `100,000` LOC compiled                    | Host OS peak RSS / `Arena` high-water mark       |

---

## 2. Standard Benchmark Workloads (`bench/suites/`)

1.  **Micro-Benchmarks:** Tight numeric/SIMD loops, `SwissTable` `Map` lookups, `ipnsort` / `Powersort` sorting, `Schubfach` / `Eisel–Lemire` float codecs, `simdjson` 64-bit tape parsing, `blake3` hashing, and Keiser–Lemire UTF-8 validation.
2.  **Memory & Allocation Benchmarks:** `Arena` (`BumpArena`) checkpoint/restore throughput, `AllocatorHandle` `TrivialDrop` elision (`0` drop instructions), `Pool[T]` / `SlotMap[K, V]` churn, and `#soa Vec[T]` vs. AoS iteration.
3.  **Concurrency & I/O Benchmarks:** `TaskGroup` spawn/join, zero-copy `BufReader`/`BufWriter` streaming, `Span16` HTTP framing, and `Bounded-MVS` package resolution (`< 5 ms` cold).
4.  **Compiler & LSP Scaling Corpus:** Synthetic and real `.cx` workspaces up to `100,000`–`500,000` LOC measuring cold build, warm Early-Cutoff incremental build, and `corex lsp` P99 latency.

---

## 3. Execution & Statistical Discipline

1.  **Uncontended Warmup & MAD-Filtered Sampling:** Run benchmarks on an **uncontended host** (never concurrently with `zig build test` / heavy compilation), executing warmup iterations followed by `>= 30`–`100` measured iterations (`STD-04`: `1.4826 * MAD` outlier filtering for `Median`/`StdDev`, raw untrimmed `Min`/`P95`/`P99`, and `Peak Mem` tracking).
2.  **Regression Gate:** Any change that degrades compilation throughput, cold-start latency, LSP P99, binary size, or runtime speed beyond noise (`> 2%`) without an explicit architectural justification fails the benchmark gate.
3.  **Terminal Output Aesthetic:** Benchmark runner tables must use the canonical CoreX monochrome Unicode box-drawing (`╭`, `│`, `╰`, `├`, `─`) and glyph (`▸`, `✓`, `✗`, `⚠`) renderer per `AGENTS.md` Section 5.

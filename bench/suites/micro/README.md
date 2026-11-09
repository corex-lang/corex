# Micro-Benchmark Suite (`bench/suites/micro/`)

Tracks sub-microsecond throughput and instruction-level efficiency for core compiler data structures and
generated `.cx` kernels against C (`clang -O3`) and Rust (`rustc -C opt-level=3`) baselines.

## Workload Categories

-   **Numeric & SIMD Kernels:** Tight scalar and vectorizable loops, matrix multiplication, and sorting.
-   **Hash & Lookup Tables:** `StringInterner` `Wyhash(0)` probing, static keyword tables, and bitsets.
-   **Text & UTF-8 Scanning:** Non-backtracking DFA tokenization, `LineIndex` binary search, and UTF-8
    validation.

## Statistical Discipline

All micro-benchmarks execute via `stage0/src/bench/harness.zig` with at least `5` warmup iterations and
`>= 30` measured iterations, reporting minimum, median, P95, standard deviation, and MAD in monochrome
Unicode box-drawing tables.

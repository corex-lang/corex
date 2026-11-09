# Memory & Arena Allocation Benchmarks (`bench/suites/memory/`)

Measures allocation throughput, cache locality, peak resident set size (RSS), and deterministic cleanup
overhead across CoreX memory management primitives.

## Workload Categories

-   **Slab Bump Arenas:** `BumpArena` 64 KiB slab allocation, 16-byte alignment, and $O(1)$ checkpoint
    restoration (`stage0/src/mem_foundation.zig`).
-   **Structure-of-Arrays (SoA) Stores:** `TokenBuffer` (`12 B`/token), `LosslessCstArena` (`10 B`/node),
    and `AstArena` (`13 B`/node) sequential construction and $O(1)$ subtree skipping.
-   **Lexical Region Cleanup:** Scope-based deterministic deallocation vs. manual layout control in `.cx`
    workloads.

## Target Metrics

-   **Compiler Peak RSS:** Linear scaling `< 150 MB` per `100,000` lines of `.cx` code compiled.
-   **Regression Gate:** Any commit degrading allocation throughput or increasing peak memory by `> 2%`
    fails the benchmark gate.

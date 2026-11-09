# Concurrency & Asynchronous I/O Benchmarks (`bench/suites/io_async/`)

Measures task scheduling latency, file streaming throughput, virtual file system (`VfsSourceMap`) ingestion
speed, and zero-copy buffer pipelines.

## Workload Categories

-   **VFS Dual-Path Ingestion:** `< 16 KiB` `BumpArena` buffered reads vs. `>= 16 KiB` read-only OS memory
    mapping (`mmap`) and BLAKE3 content hashing.
-   **Transactional Source Patching:** `TransactionalPatcher` single-pass $O(N + M)$ byte splicing across
    large source buffers.
-   **Structured Concurrency & I/O:** High-concurrency task scheduling, socket echo throughput, and
    streaming I/O pipelines in `.cx` runtime workloads.

## Execution

```text
zig build bench
```

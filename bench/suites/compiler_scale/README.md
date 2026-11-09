# Compiler Scaling Corpus (`bench/suites/compiler_scale/`)

Tracks end-to-end CoreX compilation speed, incremental re-parse/re-check latency, and cold-start overhead
across synthetic and real `.cx` codebases at `1,000`, `10,000`, `100,000`, and `500,000` lines of code.

## Target Metrics

| Dimension                  | CoreX Target                                       |
| -------------------------- | -------------------------------------------------- |
| **Compilation Throughput** | `>= 500,000` LOC/sec in `--dev` mode               |
| **Cold-Start Latency**     | `< 1.5 ms` process startup to first instruction    |
| **Compiler Peak Memory**   | `< 150 MB` RSS per `100,000` LOC compiled          |
| **LSP Incremental Check**  | `< 10 ms` single-file edit to updated diagnostics  |

## Execution

```text
zig build bench
```

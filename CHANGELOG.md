# Changelog

All notable changes to **CoreX** will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<br>

## [Unreleased]

### Added

-   Initial CoreX language specification, research architecture (`DR-01`–`DR-15`), and multi-stage bootstrap and verification governance.
-   Stage 0 Zig (`0.17.0`) bootstrap workspace (`build.zig`, `stage0/src/`, `stage0/bootstrap.c`) installing the unified `corex` binary into `build/stage0/`.
-   Foundational memory and syntax arenas (`BumpArena` with 64 KiB 16-byte-aligned slabs and $O(1)$ `Checkpoint`/`restore`, `StringInterner` with `Wyhash(0)`, `TokenBuffer`, `LosslessCstArena`, `AstArena` / `AstStore`, and compact 32-bit entity handles).
-   Content-addressable `VfsSourceMap` (`SourceMap`) with `< 16 KiB` NUL-terminated arena storage, `>= 16 KiB` read-only `mmap`, in-memory overlays, `.cxtree` binary manifest headers, and $O(\log L)$ `LineIndex` (`LF`/`CRLF`, UTF-8, and UTF-16 columns).
-   Centralized `DiagnosticSink` (`E00xx`–`E05xx` / `W00xx`–`W05xx` catalog and 100-error cap), `TransactionalPatcher`, monochrome Unicode + ANSI `DiagnosticRenderer` (`cli/style.zig`, `cli/box_draw.zig`, `diag/renderer.zig`), and `corex` CLI command router (`build`, `run`, `check`, `test`, `fmt`, `upgrade`, `lsp`, `bench`).
-   Multi-tier verification and benchmark harnesses (`tests/unit/`, `tests/snapshots/`, `tests/fuzz/`, `tests/drift/`, and `bench/suites/`).
-   High-speed non-backtracking DFA lexer and token stream (`stage0/src/lexer.zig`) supporting all 112 `TokenKind` variants (`0..111`), $O(1)$ keyword/primitive-type classification, disjoint identifier casing invariant (`.underscore`, `.ident`, `.type_ident`, `.const_ident`) with `W0201` auto-fix normalization, lossless `TriviaPiece` attachment and coalescing, fault-tolerant `E0101`–`E0104` / `W0101` recovery, golden token/diagnostic snapshots, 10,000,000+ input lossless round-trip fuzzing (`tests/fuzz/phase1_lexer_fuzz.zig`), and `phase1_bench` throughput benchmarks.

# Standard Library `Deep Research` Prompts (`STD-01`–`STD-07`)

This catalog contains the dedicated, module-grouped `Deep research` prompts governing the **CoreX Standard Library (`cx.*`)** across **Phase 11** (`STD-01`–`STD-04`, bootstrap `stdlib/cx/*.cx` required for self-hosting `compiler/*.cx`) and **Phase 13** (`STD-05`–`STD-07`, post-`v0.0.1` application-layer engines written once on the self-hosted compiler).

While [`docs/research/DR-15.md`](../DR-15.md) established the top-level 5-Tier Acyclic Dependency DAG and `AllocatorHandle` contract, each `STD-XX` report specifies the **exact low-level algorithms, SIMD/SWAR kernels, cross-OS syscall edge cases, zero-dead-code data layouts, and complete ergonomic public APIs** so implementation agents never rely on guesswork.

-   **Target Output Directory:** Save each completed report to `docs/research/stdlib/STD-XX.md`.
-   **Reference Code Policy:** Every `STD-XX` report **should include concrete reference code examples** (algorithms, SIMD/SWAR bit-twiddling kernels, state machines, and syscall wrappers) in **any clear systems language** (CoreX `.cx`, Zig, Rust, or C) alongside the canonical `.cx` public API signatures; implementation agents translate non-`.cx` algorithmic kernels into idiomatic CoreX v1.0 (`DR-21` / `DR-22`).

---

## Standard Library Research Index

| Report ID    | Target Report Path                | Wave        | MD Files to Attach in Chat (max 10)                                           | Blocking Phase | Standard Library Modules Covered                                                           |
| ------------ | --------------------------------- | ----------- | ----------------------------------------------------------------------------- | -------------- | ------------------------------------------------------------------------------------------ |
| **`STD-01`** | `docs/research/stdlib/STD-01.md`  | Bootstrap 1 | `PLAN`, `DR-04`, `DR-06`, `DR-15`, `DR-20`, `DR-21`, `DR-22`                  | Phase 11.1     | `cx` Prelude, `cx.mem`, `cx.col`, `cx.str`, & `cx.math` (Memory, Collections, UTF-8, Math) |
| **`STD-02`** | `docs/research/stdlib/STD-02.md`  | Bootstrap 1 | `PLAN`, `DR-06`, `DR-07`, `DR-10`, `DR-15`, `DR-17`, `DR-21`, `DR-22`         | Phase 11.2a    | `cx.io`, `cx.path`, `cx.fs`, `cx.time`, `cx.env`, & `cx.process` (I/O, FS, Paths, OS)      |
| **`STD-03`** | `docs/research/stdlib/STD-03.md`  | Bootstrap 2 | `PLAN`, `DR-06`, `DR-08`, `DR-11`, `DR-15`, `DR-17`, `DR-20`, `DR-21`, `DR-22` | Phase 11.2b    | `cx.crypto`, `cx.async`, `cx.sync`, & Bootstrap `cx.net` / `cx.http`                       |
| **`STD-04`** | `docs/research/stdlib/STD-04.md`  | Bootstrap 2 | `PLAN`, `DR-05`, `DR-11`, `DR-12`, `DR-15`, `DR-18`, `DR-20`, `DR-21`, `DR-22` | Phase 11.3     | `cx.cli`, `cx.serde` (`JSON` & `TOML`), `cx.test` (`--sim` / `--fuzz`), & `cx.bench`       |
| **`STD-05`** | `docs/research/stdlib/STD-05.md`  | Wave `0.x`  | `PLAN`, `DR-08`, `DR-15`, `DR-17`, `DR-20`, `DR-22`, `STD-02`, `STD-03`       | Phase 13.1     | Multi-Core `io_uring`/`IOCP`/`kqueue` Reactors, `HTTP/2` + `HPACK`, `WS`, & `@secret` `TLS 1.3` |
| **`STD-06`** | `docs/research/stdlib/STD-06.md`  | Wave `0.x`  | `PLAN`, `DR-15`, `DR-19`, `DR-20`, `DR-22`, `STD-01`, `STD-04`                | Phase 13.3     | 120fps Tear-Free `cx.tui` Engine (`DECSET 2026`, Kitty Input, Cached Flexbox/Cassowary)    |
| **`STD-07`** | `docs/research/stdlib/STD-07.md`  | Wave `0.x`  | `PLAN`, `DR-10`, `DR-15`, `DR-20`, `DR-22`, `STD-01`, `STD-03`                | Phase 13.4     | Direct `@gpu_kernel` (`MIR → SPIR-V/WGSL`) & Cross-OS GPUI-Style `cx.ui` (`< 3 KB` Wasm)   |

---

## `STD-01` (Blocks `Phase 11.1` → `docs/research/stdlib/STD-01.md`): `cx` Prelude, `cx.mem`, `cx.col`, `cx.str`, & `cx.math`

```markdown
# Deep Research Request (STD-01): Architecture, Algorithms & Ergonomic APIs for CoreX `cx` Prelude, `cx.mem`, `cx.col`, `cx.str`, and `cx.math`

## Context & Language Invariants
I am implementing **Phase 11.1** of **CoreX** (`.cx`), a zero-GC, statically verified systems and application language targeting C/Zig speed, `< 1 MB` self-hosted toolchain size, `< 10 KB` freestanding `wasm32` binaries, Rust-grade MVS + MIR SAST memory/bounds safety without `'a` lifetime annotations, and Python/Swift-grade ergonomics.

Attach and respect the finalized CoreX v1.0 specification in `PLAN.md`, `DR-04`, `DR-06`, `DR-15`, `DR-20`, `DR-21`, and `DR-22`:
- Namespace & syntax: `cx.*`, unified `.` paths, `[T]` generics, `[T: A | B]` inline union bounds, `[T = Default]` type/const defaults, `T!E` (`Result`) and `T?` (`Option`), `/` positional-only and `*` keyword-only parameter zones, `= default` parameters, `subscript(…) -> T { let { yield … } inout { yield &mut … } }`, and `{expr=:#06x}` zero-alloc stack `FmtArgs`.
- Ownership & memory: `Copy`, `AutoDrop`, and `@linear`; parameter modes `[var] x: T`, `&T`, `&mut T`, `[var] x: own T`, and `&out T`; implicit `context.allocator` + `context.scratch[0..2]` ping-pong arenas (`E0328`) + 8-byte aligned `AllocatorHandle` stealing LSB bits (`0 = GeneralAllocator`, `1 = BumpArenaNoFree`, `2 = StaticRoData`) for static `TrivialDrop` destructor elision; zero runtime pre-`main` module initializers (`comptime`-frozen `.rodata` tables only).
- Code examples: Include concrete, production-grade reference implementations for non-trivial algorithms and SIMD/SWAR kernels in **any clear language** (CoreX `.cx`, Zig, Rust, or C), paired with canonical `.cx` public type/function signatures.

## Research Objectives
1. **`cx` Prelude & `cx.mem` (Allocators, Arenas, Pools & Zero-Copy Byte Views):**
   - Specify the exact memory layouts, slab headers, alignment math, overflow guards, and fast paths for `Allocator`, `AllocatorHandle`, `@linear Arena` (`BumpArena` with 64 KiB slabs, `Checkpoint`/`restore`, large-object bypass slabs), `Pool[T]`, `FixedBuffer`, `System` OS page/heap allocator (`VirtualAlloc` / `mmap` / `wasm32` `memory.grow` without requiring `libc` `malloc`), `Span16`, and 2-slot `Context.scratch[0..2]` helpers.
   - Define safe, zero-`unsafe` `FromBytes` / `IntoBytes` (`@zero_pad`) byte-transmute and endian-aware cursor helpers (`view_bytes`, `as_bytes`, `read_le`/`write_le`).
2. **`cx.col` (Cache-Optimal Data-Oriented Containers & Algorithms):**
   - Design 24-byte `Vec[T]`, `#soa Vec[T]` multi-column layout + `subscript` projection, inline-storage `SmallVec[T, const N: usize]`, power-of-two ring `Deque[T]`, and 64-bit generational `SlotMap[K, V]`.
   - Specify a state-of-the-art **SwissTable (`Map[K, V]` & `Set[T]`)** seeded from `context.rng` (`Fix-18A` deterministic under `corex test --sim --seed`): 16-byte SSE2 / ARM NEON `ctrl` byte group probing **plus** a branchless 8-byte portable `u64` SWAR fallback for freestanding `wasm32`, tombstones vs. backshift deletion, and **Pointer-Shape Identical Code Folding (ICF)** separation (type-erased non-generic core routines parameterized by `(elem_size, elem_align, hash_fn, eq_fn)` so instantiating `Map` across 50 types does not bloat binary size).
   - Select and provide reference code for CoreX's canonical in-place slice sorting (`pdqsort` / `ipnsort` pattern-defeating quicksort vs. `driftsort` for stable sort) and binary search / dedup / partition / window / chunk APIs.
3. **`cx.str` & `cx.math` (24B SSO `String`, SIMD UTF-8, Zero-`libc` Float Formatting/Parsing & Unicode):**
   - Design the 24-byte Little-Endian **Small String Optimization (`SSO`) `String`** storing up to **23 inline UTF-8 bytes** with zero heap allocation while remaining compatible with `AllocatorHandle` on the heap branch.
   - Provide exact reference kernels for SIMD + SWAR UTF-8 validation (`Keiser–Lemire` lookup), `comptime`-compressed multi-stage `.rodata` tables (`< 8–12 KB` total!) for `UAX #29` extended grapheme clusters and `wcwidth` terminal column widths, and zero-allocation `FmtArgs` / `FmtSpec` rendering.
   - Specify zero-`libc`, exact round-trip **float-to-string (`Dragonbox` / `Schubfach`)** and **string-to-float (`Eisel–Lemire` + fallback)** algorithms (with reference code) alongside fast 2-digits-at-a-time integer formatting and essential `cx.math` (`f32`/`f64` bit/trig/ulp helpers and checked/wrapping/saturating integer utilities).
   - Benchmark ergonomic string/slice APIs against Python (`split`, `lines`, `trim`, `strip_prefix`/`strip_suffix`, `replace`, `join`), Rust, Swift, and Zig so everyday string manipulation in `.cx` feels effortless without hidden allocations.

## Required Deliverables
1. **Complete Canonical `.cx` Public API Catalog** for `cx` prelude, `cx.mem`, `cx.col`, `cx.str`, and `cx.math` (exact struct sizes/fields, traits, error enums, parameter zones, contracts, and MVS modes).
2. **Concrete Algorithmic & SIMD/SWAR Reference Code** (in `.cx`, Zig, Rust, or C) for `Arena` slab management, ICF-friendly `SwissTable` probing (SIMD + `u64` SWAR), 23-byte `SSO String`, `Dragonbox`/`Schubfach` float formatting, `Eisel–Lemire` float parsing, `pdqsort`, and compact `.rodata` Unicode tables.
3. **Tree-Shaking, Binary-Size & Pentagon Bounds-Elimination Verification Checklist** proving `< 10 KB` minimal `wasm32` output and zero-bounds-check inner loops.
```

---

## `STD-02` (Blocks `Phase 11.2a` → `docs/research/stdlib/STD-02.md`): `cx.io`, `cx.path`, `cx.fs`, `cx.time`, `cx.env`, & `cx.process`

```markdown
# Deep Research Request (STD-02): Zero-Copy I/O, Cross-Platform Filesystem/Paths, Clocks & OS Process Architecture (`cx.io`, `cx.path`, `cx.fs`, `cx.time`, `cx.env`, `cx.process`)

## Context & Language Invariants
I am implementing **Phase 11.2a** of **CoreX** (`.cx`), building the foundational I/O, path, filesystem, clock, environment, and child-process modules required to self-host the CoreX compiler (`VfsSourceMap`, `pkg_cache`, linker driver, and build/test runners) across **Linux (`x86_64`/`aarch64` `gnu` & `musl`), macOS (`x86_64`/`aarch64`), Windows (`x86_64`/`aarch64`), and `wasm32-unknown-wasi`**.

Attach and respect `PLAN.md`, `DR-06`, `DR-07`, `DR-10`, `DR-15`, `DR-17`, `DR-21`, and `DR-22`:
- Ownership & safety: `@linear` handles (`File`, `Dir`, `Mmap`, `ChildProcess`) statically prevent descriptor leaks (`E0304`); `&out [u8]` / borrowed buffer slices avoid redundant zero-initialization (`E0422`); `DR-17` `@std_cap_boundary` attributes (`fs`, `env`, `process`, `clock`) feed compile-time supply-chain capability sandboxing; `Context.reactor` intercepts I/O and clocks transparently under `corex test --sim`.
- Naming invariant (`AGENTS.md` §6): Canonical path resolution functions use `resolve_path` and `resolve_or_create_path`.
- Code examples: Provide concrete reference implementations in **any clear language** (`.cx`, Zig, Rust, or C) for subtle OS syscall sequences alongside canonical `.cx` signatures.

## Research Objectives
1. **`cx.io` (Zero-Copy Buffered & Vectored Streaming Without Trait/Allocation Traps):**
   - Compare Rust's `Read`/`Write`/`BufRead` (`BorrowedBuf`), Zig 0.14–0.17's non-generic interface/ring `Reader`/`Writer`, and Go's `io.Reader`/`io.Writer`. Design a clean, zero-heap-allocation CoreX `Reader` / `Writer` / `BufReader` / `BufWriter` / `LimitReader` architecture supporting zero-copy slice peeking (`peek`, `consume`, `read_until`), `write_vectored` (`iovec` / `WSABUF`), `FmtArgs` streaming (`print` with zero intermediate heap string), and locked buffered `stdin`/`stdout`/`stderr` handles.
2. **`cx.path` & `cx.fs` (Bulletproof Windows NT/Win32 + POSIX + WASI Filesystem):**
   - Design `Path` (borrowed slice) and `PathBuf` (`AutoDrop` 24B SSO/buffer) handling POSIX `/`, Windows drive letters (`C:\`), UNC shares (`\\server\share`), extended-length `\\?\` prefixes, `.` / `..` lexical normalization vs. symlink-resolving `resolve_path` / `resolve_or_create_path`, and WTF-8 ↔ stack UTF-16 (`[u16; 512]` fast path) transcoding on Windows with zero heap allocation on normal paths.
   - Specify exact cross-OS implementations for:
     - `@linear File` & `@linear Dir` (`openat` / `NtCreateFile` / WASI `path_open` capability-relative traversal preventing TOCTOU traversal attacks),
     - Thresholded file loading (`< 16 KiB` single `read` into `Arena` with NUL sentinel vs. `>= 16 KiB` read-only `@linear Mmap` via `mmap` / `CreateFileMappingW` + `MapViewOfFile`),
     - Crash- & `SIGKILL`-safe atomic `UnlinkAndReplace` file publishing (`write_atomic` / `publish_staged_atomic` handling Windows `MoveFileExW` / POSIX-semantics disposition / antivirus retry / executable mode bits),
     - Copy-on-write 3-tier materialization (`FICLONE` / `clonefile` / `FSCTL_DUPLICATE_EXTENTS_TO_FILE` reflink → hardlink → chunked `copy_file_range` fallback) and lockfile `flock` / `LockFileEx` concurrency,
     - Lightweight cross-OS directory/file change watching (`inotify`, `FSEvents`/`kqueue`, `ReadDirectoryChangesW`) for `corex lsp` and `--watch`.
3. **`cx.time`, `cx.env`, & `cx.process`:**
   - Specify monotonic `Instant` & `Duration` (`clock_gettime(CLOCK_MONOTONIC)` / `mach_continuous_time` / `QueryPerformanceCounter` with `u128` overflow-free nanosecond scaling) and wall-clock `SystemTime` routed through `Context` for deterministic `--sim` virtual time.
   - Specify safe `cx.env` (`args`, `var`, `vars`, `home_dir`, `cache_dir`, `temp_dir` across XDG, macOS, and Windows KnownFolders/env) and `@linear cx.process.Command` / `Child` (`posix_spawn` / `fork+execve` with `CLOEXEC` pipes vs. Win32 `CreateProcessW` with proper command-line quoting and `.bat`/`.cmd` avoidance preventing `BatBadBut` `CVE-2024-24576` injection!).

## Required Deliverables
1. **Complete Canonical `.cx` Public API Signatures** for `cx.io`, `cx.path`, `cx.fs`, `cx.time`, `cx.env`, and `cx.process` (including compact `IoError` / `FsError` layouts fitting `cx_result_cc` register return!).
2. **Concrete Cross-OS Reference Implementations** (in `.cx`, Zig, Rust, or C) for zero-copy `BufReader`/`BufWriter`, Windows WTF-8 ↔ UTF-16 + `\\?\` normalization, atomic `UnlinkAndReplace` on Windows & POSIX, 3-tier reflink/hardlink/copy, and injection-safe Windows `CreateProcessW` argument escaping.
3. **`--sim` Virtualization & `DR-17` Capability Boundary Table** mapping every OS entry point to its exact `EffectCapabilityMask` bit and `Context` simulation hook.
```

---

## `STD-03` (Blocks `Phase 11.2b` → `docs/research/stdlib/STD-03.md`): `cx.crypto`, `cx.async`, `cx.sync`, & Bootstrap `cx.net` / `cx.http`

```markdown
# Deep Research Request (STD-03): Cryptography, Structured Async Runtime, Synchronization & Bootstrap Networking (`cx.crypto`, `cx.async`, `cx.sync`, `cx.net`, `cx.http`)

## Context & Language Invariants
I am implementing **Phase 11.2b** of **CoreX** (`.cx`), building the cryptographic primitives, structured concurrency runtime, synchronization primitives, and bootstrap TCP/TLS/HTTP-1.1 client required by the self-hosted CoreX package manager (`pkg_cache`, `pkg_resolver`), `MirVm`, and `CompilerDb` (`Prune-07`: full multi-core `io_uring`/HTTP-2/pure-`.cx` TLS 1.3 are deferred to `Phase 13.1`, so `Phase 11.2b` must stay razor-lean, fast, and 100% verifiable).

Attach and respect `PLAN.md`, `DR-06`, `DR-08`, `DR-11`, `DR-15`, `DR-17`, `DR-20`, `DR-21`, and `DR-22`:
- Concurrency invariants (`Phase 8` / `DR-08` / `DR-20` `Fix-08B`): stackless `async`/`await` (`<= 16 KiB` inline frame budget `E0317`), lexical `cx.async.task_group` (`@linear TaskHandle[T]`, LIFO `cancel_bb` `defer` cleanup `E0304`, compile-time `Send`/`Sync`/borrow exclusivity `E0309`), and `64B` `InFlightOpSlot` + `CompletionReaper` quarantine drain barrier (`sim_seam`).
- Code examples: Include concrete algorithmic/protocol reference code in **any clear language** (`.cx`, Zig, Rust, or C) alongside canonical `.cx` signatures.

## Research Objectives
1. **`cx.crypto` (Compact, High-Throughput Cryptographic & Hashing Suite):**
   - Specify pure-`.cx` implementations (with portable `Simd[u32, 4]` / `Simd[u32, 8]` vectorization where beneficial and compact `.rodata` footprint) for:
     - **`blake3`** (standard hash, `keyed_hash` for `.cxi` digests, `derive_key`, and **`.obao` Bao 1 KiB chunk-tree streaming Merkle verification** per `DR-11`),
     - **`sha256`** (for Stage `L3` release verification, Git/OCI interop, and RFC 6962 / TLS),
     - **Constant-time `ed25519` signature verification** + **RFC 6962 Merkle transparency-log inclusion & consistency proof verification** (`pkg_cache`),
     - **`Wyhash` (`WyHasher`)** 64-bit & 128-bit (`Fingerprint128`) non-cryptographic hashing, and
     - **OS `Csprng`** (`getrandom` / `arc4random_buf` / `BCryptGenRandom` / WASI `random_get`, routed through `context.rng` for deterministic `--sim --seed` replay).
2. **`cx.async` & `cx.sync` (Deterministic Structured Concurrency & Lightweight Sync):**
   - Design the bootstrap single-threaded + bounded worker-thread `Reactor` (wrapping `poll`/`epoll`/`kqueue`/`WSAPoll`/IOCP timers + deterministic `--sim` virtual event wheel) driving `task_group`, `spawn_local`, `spawn`, `yield_now`, `sleep`, `with_timeout`, and the `CompletionReaper` cancellation drain barrier.
   - Design bounded MPSC/MPMC `Channel[T]`, async `Mutex[T]` / `Semaphore` / `Notify`, and OS-futex-backed blocking `cx.sync.{Mutex, RwLock, Condvar, Once, WaitGroup}` (`futex` on Linux, `__ulock_wait` on macOS, `WaitOnAddress` on Windows, atomic spin/WASI `atomic.wait` on `wasm32`, marked with `@std_cap_boundary(blocking_sync)` for `@no_block` `E0322` enforcement!).
3. **Bootstrap `cx.net` & `cx.http` (`Prune-07` Package-Fetch Client & Socket Layer):**
   - Specify RFC-compliant zero-allocation `IpAddr` (`Ipv4Addr`, `Ipv6Addr`) & `SocketAddr` parsers, non-blocking `@linear TcpStream` / `TcpListener` / `UdpSocket` (`SOCK_NONBLOCK | SOCK_CLOEXEC`, `WSA_FLAG_OVERLAPPED`, dual-stack IPv6/IPv4), and DNS resolution.
   - Compare and select the cleanest **zero-bloat HTTPS TLS strategy** for Phase 11.2b bootstrap package fetching across Linux (`musl` static!), macOS, and Windows before Phase 13.1's `@secret` TLS 1.3 lands: native OS TLS (Windows `Schannel`, macOS `Network`/`SecureTransport`) + minimal embedded TLS 1.3 client vs. compact pure-`.cx` TLS 1.3 client-only (`X25519` + `ChaCha20-Poly1305` / `AES-128-GCM` + OS trust-store root PEM/cert loader) so static `x86_64-linux-musl` builds have **zero `libssl` C dependency**!
   - Specify the unboxed `Span16` zero-copy HTTP/1.1 client & parser (`Content-Length`, `Transfer-Encoding: chunked`, connection keep-alive pooling, redirect caps, timeouts, and streaming `.cxpkg` body verification).

## Required Deliverables
1. **Complete Canonical `.cx` Public API Signatures** for `cx.crypto`, `cx.async`, `cx.sync`, `cx.net`, and bootstrap `cx.http`.
2. **Concrete Reference Implementations** (in `.cx`, Zig, Rust, or C) for SIMD `blake3` + Bao chunk verification, constant-time `ed25519_verify`, `futex`/`__ulock_wait`/`WaitOnAddress` 4-byte `Mutex`, `task_group` + `CompletionReaper` state transitions, the chosen zero-`libssl` HTTPS client handshake, and `Span16` HTTP/1.1 framing.
3. **Security, Resource-Cap & NIST/Wycheproof Test Vector Specification** covering malformed headers, slowloris/redirect bounds, and cryptographic test vectors.
```

---

## `STD-04` (Blocks `Phase 11.3` → `docs/research/stdlib/STD-04.md`): `cx.cli`, `cx.serde`, `cx.test`, & `cx.bench`

```markdown
# Deep Research Request (STD-04): Declarative CLI & Monochrome Terminal Engine, `simdjson`/Lossless-TOML `cx.serde`, and `--sim`/`--fuzz` Verification Harnesses (`cx.cli`, `cx.serde`, `cx.test`, `cx.bench`)

## Context & Language Invariants
I am implementing **Phase 11.3** of **CoreX** (`.cx`), completing the bootstrap standard library modules that directly power the self-hosted `corex` CLI router, monochrome diagnostic/table/diff renderer, `corex lsp` JSON-RPC 2.0 codec, `corex.toml` / `corex.lock` surgical manifest patcher, `corex test` (`--sim --seed` & `--fuzz`), and `corex bench`.

Attach and respect `PLAN.md`, `DR-05`, `DR-11`, `DR-12`, `DR-15`, `DR-18`, `DR-20`, `DR-21`, and `DR-22`:
- CLI aesthetic law (`AGENTS.md` §5): Strictly monochrome Unicode glyphs (`╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠`) + ANSI foreground/bold/dim styling (`NO_COLOR` & `--color=always|auto|never`); **zero colored emojis** anywhere.
- Untrusted input law (`AGENTS.md` §2): Non-backtracking DFA/SIMD scanners and explicit hard bounds on JSON/TOML depth, payload bytes, and fuzz/sim budgets.
- Code examples: Include concrete reference code in **any clear language** (`.cx`, Zig, Rust, or C) alongside canonical `.cx` signatures.

## Research Objectives
1. **`cx.cli` (Zero-Alloc `comptime`-Validated `argv` Parser & Canonical Monochrome Terminal Engine):**
   - Design declarative subcommand/flag schemas (`@attribute_schema` / struct reflection in `MirVm` `comptime` validating duplicate short/long flags, alphabetical ordering, and dynamic help-table generation with zero drift) plus single-pass zero-allocation `argv` parsing and stack-allocated Damerau–Levenshtein typo suggestions (`did you mean …?`).
   - Specify the reusable monochrome terminal rendering primitives shared by `corex` and user CLI apps: multi-span source code snippets with Unicode box-drawing underline pointers & multiline bridges, `TransactionalPatcher` unified diff previews, auto-sized box-drawing tables (`corex bench` & `corex check --caps`), and TTY progress spinners (`Compiling...`).
2. **`cx.serde` (`simdjson`-Style 64-Bit `JsonTape`, `comptime` Serde & Lossless `TomlCst`):**
   - Provide exact Stage-1 (SIMD/SWAR structural bitmask + quote/escape carryless XOR) and Stage-2 (`64-bit TapeWord` + string unescaping + `Eisel–Lemire` numbers) reference code for `cx.serde.json`, supporting both zero-copy DOM/tape traversal (powering `< 10 ms` P99 `corex lsp` JSON-RPC with `MAX_DEPTH = 64`) and `comptime`-specialized typed `serialize` / `deserialize` via `MirVm` struct reflection (`@serde(rename: "…", skip_if_none: true)`).
   - Specify the lossless SoA `TomlTokenBuffer` (`8B`) / `TomlCstArena` (`16B`) parser, serializer, and comment/whitespace-preserving surgical `TextEdit` patcher for `cx.serde.toml` (powering `corex.toml` and `corex.lock`).
3. **`cx.test` & `cx.bench` (`--sim --seed` Virtual Simulation, `--fuzz` Coverage Shrinker & MAD Benchmarking):**
   - Specify the `cx.test` runner (`test "…"` discovery, parallel execution, rich diff assertions, golden `.snap` snapshot verification/updating) and the **single-process deterministic `Context` simulation harness (`corex test --sim --seed`, `DR-18`)**: deterministic PRNG (`context.rng`), virtual monotonic clock + timer heap, deterministic task-interleaving scheduler, systematic `OOM` allocation-countdown fault injection (`Arena` / `System`), and simulated VFS/network fault hooks.
   - Specify the in-process **coverage-guided native fuzzing engine (`corex test --fuzz`)** reading Phase 7's `__sancov_cntrs` (`inline-8bit-counters`), `__sancov_pcs`, and CMP/DIV value-profile ring buffers: corpus queue prioritization, Havoc + dictionary + CMP-guided mutation operators, `test "…" (data: &[u8])` and `comptime`-reflected structured input generators, and deterministic delta-debugging crash minimization (`shrink`) writing minimized reproducers to `tests/fuzz/corpus/`.
   - Specify the `cx.bench` harness (`bench "…" (b: &mut Bencher)`): `black_box` compiler barrier, adaptive warmup & iteration calibration, monotonic nanosecond sampling, Median / Min / P95 / P99 / StdDev / **Median Absolute Deviation (MAD)** outlier filtering, peak arena/heap byte tracking, and monochrome box-drawing summary tables.

## Required Deliverables
1. **Complete Canonical `.cx` Public API Signatures** for `cx.cli`, `cx.serde` (`cx.serde.json` & `cx.serde.toml`), `cx.test`, and `cx.bench`.
2. **Concrete Reference Implementations** (in `.cx`, Zig, Rust, or C) for `simdjson` Stage-1/Stage-2 `64-bit` tape construction (SIMD + portable `u64` SWAR), lossless `TomlCst` surgical key/array patching, `--sim --seed` deterministic scheduler + `OOM` fault injector, and `--fuzz` 8-bit counter hit-bucketing + Havoc/CMP mutator + hierarchical input shrinker.
3. **Self-Hosting Parity & Performance Targets** (`>= 1.5 GB/s` JSON tape throughput, `< 10 ms` P99 LSP framing, bit-exact `--sim --seed` replay across runs, and zero heap allocations in `cx.cli` `argv` parsing).
```

---

## Post-`v0.0.1` (`0.x` → `v1.0.0`) Application-Layer Stdlib Prompts (`STD-05`–`STD-07`)

Run these three prompts after `CoreX v0.0.1` self-hosting (`Phase 12.8`) right before executing the corresponding `Phase 13` milestone:

### `STD-05` (Blocks `Phase 13.1` → `docs/research/stdlib/STD-05.md`): Multi-Core Reactors, `HTTP/2` + `HPACK`, `WebSocket`, & `@secret` `TLS 1.3`

```markdown
# Deep Research Request (STD-05): Thread-Per-Core `io_uring`/`IOCP`/`kqueue` Reactors, Zero-Alloc `HTTP/2` + `HPACK` + `WebSocket`, and `@secret`-Verified Pure-CoreX `TLS 1.3`

## Context & Objectives
Specify the complete `Phase 13.1` production networking stack in self-hosted CoreX (`.cx`), attaching `PLAN.md`, `DR-08`, `DR-15`, `DR-17`, `DR-20` (`D-05`), `DR-22`, `STD-02`, and `STD-03`. Include concrete reference code (in `.cx`, Zig, Rust, or C) for:
1. Thread-per-core shared-nothing `io_uring` (registered buffers/files, multishot `accept`/`recv`), Windows `IOCP` (`AcceptEx`/`WSARecv`), and macOS/BSD `kqueue` reactors with `@linear ProvidedBuf` ownership.
2. `@secret`-verified constant-time `X25519`, `ECDSA P-256`/`Ed25519`, `ChaCha20-Poly1305`, `AES-128/256-GCM` (AES-NI / ARMv8 Crypto + constant-time bit-sliced fallback), HKDF, X.509 chain validation, and full RFC 8446 `TLS 1.3` client & server state machines with volatile `AutoDrop` zeroization.
3. High-throughput `HTTP/2` framing + bounded `HPACK` encoder/decoder, SIMD-masked RFC 6455 `WebSocket`, and `comptime` `@route` radix-trie server dispatch using per-request 64 KiB `Arena` slabs.
```

### `STD-06` (Blocks `Phase 13.3` → `docs/research/stdlib/STD-06.md`): 120fps Tear-Free `cx.tui` Engine

```markdown
# Deep Research Request (STD-06): 120fps Tear-Free Immediate/Retained Hybrid Terminal UI Engine (`cx.tui`)

## Context & Objectives
Specify the complete `Phase 13.3` `cx.tui` terminal engine in self-hosted CoreX (`.cx`), attaching `PLAN.md`, `DR-15`, `DR-19`, `DR-20`, `DR-22` (`SE-22` `@constructor`/`@builder`), `STD-01`, and `STD-04`. Include concrete reference code (in `.cx`, Zig, Rust, or C) for:
1. Cache-aligned 16-byte `Cell` double-buffered `Grid` (4 cells per 64B cache line, inline grapheme pool overflow for multi-codepoint clusters), dirty-span diffing, minimum-byte ANSI SGR/cursor sequence emission, and `DECSET 2026` (`ESC[?2026h` / `ESC[?2026l`) synchronized output.
2. Progressive-enhancement Kitty keyboard protocol (`CSI > u`), SGR 1006 mouse, bracketed paste, focus, and resize (`SIGWINCH` / Windows Console VT `ENABLE_VIRTUAL_TERMINAL_PROCESSING`) non-backtracking parser.
3. LRU-cached Flexbox/grid layout solver (`>= 300 FPS`), `@constructor`/`@builder` declarative monochrome Unicode widget library (`Table`, `Tree`, `Tabs`, `SplitPane`, `VirtualList`, `TextInput`, `Sparkline`/`BrailleCanvas`), and headless `--sim` frame snapshot testing.
```

### `STD-07` (Blocks `Phase 13.4` → `docs/research/stdlib/STD-07.md`): `@gpu_kernel` & Cross-OS GPUI-Style `cx.ui`

```markdown
# Deep Research Request (STD-07): Direct `.cx` `@gpu_kernel` Shaders & Cross-Platform Hardware-Accelerated `cx.ui` Framework (Native Metal/D3D12/Vulkan + `< 3 KB` `wasm32`)

## Context & Objectives
Specify the complete `Phase 13.4` `cx.ui` graphical application engine in self-hosted CoreX (`.cx`), attaching `PLAN.md`, `DR-10`, `DR-15`, `DR-20` (`D-10B`), `DR-22` (`SE-22`), `STD-01`, and `STD-03`. Include concrete reference code (in `.cx`, Zig, Rust, or C) for:
1. Reactive fine-grained `Signal[T]` / `Computed[T]`, `SlotMap[WidgetId, WidgetNode]`, `IdPath` + `&mut State` lens routing, and `@constructor` / `@builder` zero-VDOM view construction.
2. GPU-driven 2D scene batching (SDF rounded-rect/border/shadow primitives, subpixel glyph atlas + HarfBuzz-free/compact shaping or OS font rasterization, `taffy`-grade cached layout) powered by CoreX `@gpu_kernel` `MIR → SPIR-V / WGSL` shaders.
3. Thin cross-OS windowing, input, clipboard, and `AccessKit`-compatible accessibility backends across Windows (`Win32` + `Direct3D 12`), macOS (`Cocoa` + `Metal`), Linux (`Wayland`/`X11` + `Vulkan`), and browser `< 3 KB` `wasm32` binary-command-buffer Canvas2D/WebGPU bridge.
```

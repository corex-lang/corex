# Phase 11.2b Standard Library Specification (STD-03): Cryptography, Structured Async Runtime, Synchronization, and Bootstrap Networking

CoreX **Phase 11.2b (`STD-03`)** specifies the five bootstrap standard library modules – `cx.crypto`, `cx.async`, `cx.sync`, `cx.net`, and `cx.http` – required by the self-hosted package manager (`pkg_cache.cx`, `pkg_resolver.cx`), deterministic `MirVm` / `CompilerDb` 128-bit content fingerprinting, and Phase 8 coroutine verification prior to `v0.0.1` (`Prune-07`). Every public signature and data structure adheres to CoreX's locked v1.0 surface syntax (`DR-21` unified `.` paths and `cx.*` namespace; `DR-22` payload-first `T!E` and `T?` types, `&T`/`&mut T`/`own T`/`&out T` Mutable Value Semantics parameter modes, `and`/`or`/`not` boolean operators, and postfix `ptr.*` dereferencing), three-tier zero-GC ownership (`Copy`, `AutoDrop`, `@linear`), and Phase 6 `MIR` SAST capability and real-time contract verification (`DR-06`, `DR-17`).

Three architectural decisions keep Phase 11.2b compact and verifiable while preserving a zero-churn upgrade path to Phase 13.1 (`STD-05`):

1.  **Compact SIMD Cryptography & Iterative $O(1)$-Heap Bao Streaming (`cx.crypto`):** `cx.crypto` pairs `Simd[u32, 4]` and 8-way transposed `Simd[u32, 8]` `blake3` kernels over a **48-byte** `.rodata` table (`32 B` `IV` + `16 B` `MSG_PERM`) with an iterative pre-order `.obao` **Bao** 1 KiB chunk-tree verifier whose fixed 54-entry chaining-value stack and header state occupy **1,856 bytes** – 8.8x below Phase 8's `16 KiB` caller-inlined coroutine frame cap (`E0317` / `DR-20` `D-02`) with zero heap allocations. Supply-chain verification combines `Simd[u32, 4]`-scheduled `sha256` and `sha512`/`sha384`, constant-time strict FIPS 186-5 / RFC 8032 `ed25519.verify` (rejecting malleable $S \ge L$, non-canonical coordinates $y \ge p$, and 8-torsion small-order public keys), iterative $O(1)$-space RFC 6962 / RFC 9162 Merkle inclusion and consistency proof verifiers, `Wyhash` v4.3 64-bit and 128-bit (`Fingerprint128`) hashing, and `context.rng`-routed OS `Csprng`.
2.  **Deterministic Bootstrap `Reactor`, Quarantine Reaper & 4-Byte OS-Futex Sync (`cx.async`, `cx.sync`):** `cx.async` combines a single-threaded local event loop (`block_on`, `spawn_local`) and a lazily initialized bounded worker pool (`spawn`, `1..8` threads) over cross-platform OS pollers (`epoll`/`poll`, `kqueue`, Windows `IOCP`/`WSAPoll`, WASI `poll_oneoff`) and a deterministic `--sim` virtual min-heap timer wheel behind `Context.reactor: *ReactorVTable` (`DR-20` Seam #5). Structured `TaskGroup[E]` nurseries enforce LIFO `cancel_cleanup_bb` `defer` execution (`E0304`), `@thread_local` / MVS borrow exclusivity (`E0309`), and a **64-byte `InFlightOpSlot` + `CompletionReaper` drain barrier (`Fix-08B`)** that quarantines cancelled DMA buffers and closes raced kernel socket/file descriptors before releasing nursery arenas. Blocking `cx.sync.{Mutex, RwLock, Condvar, Once, WaitGroup}` primitives pack fast-path state into 4-byte `AtomicU32` words backed by Linux `futex`, macOS `__ulock_wait` / `__ulock_wait2`, Windows `WaitOnAddress`, and Wasm `memory.atomic.wait32`, marked with `@std_cap_boundary` so `@no_block` scopes reject blocking calls at compile time (`E0322`).
3.  **Zero-`libssl` Pure-`.cx` TLS 1.3 Client-Only & Unboxed `Span16` HTTP/1.1 (`cx.net`, `cx.http`):** Rather than coupling static `x86_64-linux-musl` builds to C `libssl` or working around deprecated macOS `SecureTransport` (which lacks TLS 1.3), `Network.framework` (which hides pollable socket descriptors), and Windows `Schannel` TLS 1.3 post-handshake `NewSessionTicket` key-corruption hazards (`SEC_I_RENEGOTIATE` / `SERVER-128041`), Phase 11.2b selects a pure-`.cx` TLS 1.3 client-only engine (`X25519` + `secp256r1`, `ChaCha20-Poly1305` + `AES-128-GCM`, DER X.509v3 verifier; modeled at ~1,850 LOC) paired with a native OS trust-store root loader (~175 modeled LOC across Linux/BSD PEM bundles, macOS `/etc/ssl/cert.pem` + `SystemRootCertificates.keychain`, and Windows `CertOpenSystemStoreW("ROOT")`). Over this transport, an unboxed 4-byte `Span16` HTTP/1.1 client streams `.cxpkg` downloads directly through `BaoVerifier` / `Blake3` into `~/.corex/cache/blake3/staging/` under strict anti-smuggling, Slowloris timeout, and cross-origin redirect bounds.

---

## 1. Architectural Design and Trade-Off Analysis

### 1.1 Cryptographic Suite, Iterative Bao Streaming, and Supply-Chain Verification

Every module in `cx.crypto` obeys `DR-15`'s ban on pre-`main` runtime initializers: all lookup constants reside in `comptime`-verified `.rodata` sections, and pure cryptographic transformations automatically infer `EffectCapabilityMask.PURE` (`0x0000`), making them usable inside `@no_alloc @no_panic @no_block` contexts without annotation ceremony.

> **Visual – Iterative Bao Streaming Fits Full 64-Bit Merkle Verification Inside 1.86 KiB of Stack State:** Top: Memory and constant budgets across **cx.crypto** keep the iterative Bao verifier 8.8x below Phase 8's 16 KiB inline coroutine frame limit with zero heap allocations. Middle: Pre-order **.obao** layout for a 2,049-byte (3-chunk) input; parent chaining values are verified top-down before pushing right-child digests onto a bounded 54-slot stack. Bottom: Every downloaded package passes Ed25519 strict verification, RFC 6962/9162 transparency-log proof checks, and BLAKE3 tree verification before atomic cache commit.

#### Vectorized BLAKE3 and Iterative Bao Chunk-Tree Verification

BLAKE3 splits inputs into contiguous 1,024-byte (`1 KiB`) chunks of sixteen 64-byte blocks and compresses each block across 7 rounds of the Quarter-Round `G` mixing function with explicit domain-separation bit flags (`CHUNK_START = 1`, `CHUNK_END = 2`, `PARENT = 4`, `ROOT = 8`, `KEYED_HASH = 16`, `DERIVE_KEY_CONTEXT = 32`, `DERIVE_KEY_MATERIAL = 64`). In `cx.crypto.blake3`, read-only `.rodata` state is strictly **48 bytes** (`32 B` `IV: [u32; 8]` plus `16 B` `MSG_PERM: [u8; 16]`), supporting standard `hash` (for `file_blake3` and `archive_blake3`), `keyed_hash` (for keyed `.cxi` / cache MACs), and `derive_key` (for `tree_blake3` with context `"corex-pkg-tree-v1 2026-01-01"` and `.cxi` public summaries with `"corex-cxi-public-summary-v1 2026-01-01"`). Two portable `core.simd.Simd[T, N]` execution paths accelerate hashing across `x86_64`, `aarch64`, and `wasm32` without inline assembly: single-block and 64-byte parent Merkle compressions pack the 16-word state into four `Simd[u32, 4]` row vectors (lane-rotating rows `1..3` left by `1, 2, 3` lanes for diagonal rounds), whereas multi-chunk inputs (`≥8 KiB`) transpose eight contiguous 1 KiB chunks across sixteen `Simd[u32, 8]` vectors so all 7 rounds and 16 blocks per chunk execute vertically in lockstep with zero cross-lane shuffles before folding the eight resulting chaining values into `Hasher`'s 54-entry Merkle stack.

For verified streaming of large cached blobs (`≥64 KiB` in `DR-11` §2.1, ~6.25% tree overhead at 1 KiB chunk resolution) and slice extraction, `cx.crypto.blake3.BaoVerifier` decodes the **Bao** outboard (`.obao`) and combined formats. A Bao stream starts with an 8-byte little-endian unsigned length header followed by 64-byte `(left_cv || right_cv)` parent nodes arranged in **depth-first pre-order**. Rather than recursing or allocating heap nodes, `BaoVerifier` runs an **iterative $O(1)$-heap state machine** (`1,856 bytes` total: `128 B` state header + `1,728 B` `[Digest256; 54]` right-CV stack, covering up to $2^{64} / 1,024 = 2^{54}$ chunks). Before reading chunk $c \in [0, N)$ where $N = \max(1, \lceil \text{claimed\_len} / 1024 \rceil)$, `count_preorder_parents(c, N)` determines how many pre-order parent nodes immediately precede leaf $c$ in $O(\log N)$ bit operations by iteratively splitting `rem` at the highest power of two $k < \text{rem}$: whenever the relative leaf index `rel == 0`, traversal enters a subtree's leftmost leaf and consumes one 64-byte parent node from `.obao`. Each parent node is verified against the expected chaining value popped from `cv_stack` (or `expected_root` on the root parent) *before* pushing `right_cv` and `left_cv`. Per the Bao security specification, `BaoVerifier` never exposes `claimed_len` to callers until the final chunk (`c == N - 1`, explicitly including the 0-byte empty chunk when `claimed_len == 0`) passes `CV` verification and the underlying stream confirms exact EOF with zero trailing unauthenticated bytes.

#### SHA-256 / SHA-512, Strict Constant-Time Ed25519, and RFC 6962 / 9162 Merkle Proofs

`cx.crypto.sha256` freezes only the 256-byte `K256: [u32; 64]` round constant array in `.rodata` and computes four message-schedule words ($W_{16..64}$) per iteration using `Simd[u32, 4]` shifts and rotations, backing Stage `L3` release checksums, Git/OCI digests, RFC 6962 transparency-log hashing, and TLS 1.3 HKDF transcripts. An internal `sha512` / `sha384` core (`640 B` `K512: [u64; 80]` `.rodata`) backs `ed25519` (`SHA-512`) and TLS 1.3 `ecdsa_secp384r1_sha384` / `rsa_pss_rsae_sha384` X.509 certificate chain verification.

For package publisher signatures (`corex-publish-v1` in `DR-11` §3.4) and `sum.corex.dev` checkpoints, permissive consensus verification rules like `ZIP-215` permit cofactored equation edge cases and small-order keys unsuitable for supply-chain signing. `cx.crypto.ed25519.verify` enforces **strict FIPS 186-5 / RFC 8032 §5.1.7 + small-order public-key rejection** in four steps:

1.  Reject non-canonical signature scalars $S \ge L$ ($L = 2^{252} + 27742317777372353535851937790883648493$) prior to modular reduction, eliminating $S' = S + L$ signature malleability.
2.  Decompress both public key $A$ and signature point $R$ over $\mathbb{F}_{2^{255}-19}$ using 5-limb radix-$2^{51}$ (`[u64; 5]`) constant-time arithmetic, rejecting non-canonical field encodings $y \ge p$, off-curve points, and negative zero ($x = 0$ with sign bit `1`).
3.  Reject all eight torsion subgroup public keys ($[8]A = \mathcal{O}$) via three projective doublings (`X_8 == 0` and `Y_8 == Z_8`), blocking trivial zero-scalar forgeries.
4.  Compute $k = \text{SHA-512}(R_{\text{bytes}} \parallel \text{pk} \parallel \text{msg}) \bmod L$, evaluate $R_{\text{calc}} = [S]B + [k](-A)$ in extended twisted Edwards coordinates $(X : Y : Z : T)$ via constant-time 4-bit window table selection (`ctSelect`), and compare canonical $\text{Encode}(R_{\text{calc}})$ against $R_{\text{bytes}}$ using `constant_time_eq` – rejecting bit-modified $R$ encodings such as Project Wycheproof `tcId` 49 and 50.

For `sum.corex.dev` (`DR-11` §3.4, adhering to `c2sp.org/tlog-tiles` height-8 static 256-hash tiles at `/tile/8/<L>/<xNNN/.../NNN>[.p/<W>]` and signed `/checkpoint` notes), `cx.crypto.merkle` implements the RFC 9162 §2.1.3.2 and §2.1.4.2 **iterative $O(\log N)$-time, $O(1)$-space** inclusion (`0x00` leaf prefix, `0x01` internal node prefix, odd-node promotion preventing Bitcoin's `CVE-2012-2459` duplicate-leaf collision) and consistency (`SUBPROOF`) verifiers, asserting `sn == 0` upon completion so trailing proof garbage is rejected.

#### Wyhash v4.3 (64-Bit & 128-Bit `Fingerprint128`) and `context.rng` OS `Csprng`

`cx.crypto.wyhash` implements exact `wyhash_final_version_4_3` (`32 B` `_wyp` `.rodata` constants, 128-bit widening multiply `_wymum`, and 3-lane 48-byte `seed`/`see1`/`see2` mixing) for `StringInterner` (`Wyhash(0)`) and `cx.col.Map`, paired with a dual-secret 128-bit `wyhash128` (`Fingerprint128`) for `CompilerDb` Early Cutoff backdating and `WyRand` PRNG.

In `cx.crypto.csprng`, `fill_bytes` routes through `context.rng` (`Context.reactor.fill_rng` per `DR-20` Seam #5 / `Fix-18A`). In hosted runs, `os_fill_entropy` invokes Stage-1 `core.sys` kernel entropy wrappers marked `@std_cap_boundary(emits: .Entropy, clears: .FfiUnsafe)`: Linux `getrandom` (`__NR_getrandom = 278` on `aarch64`, flags `0`, looping across `EINTR` and partial reads `> 256 B`, with `/dev/urandom` fallback solely on `ENOSYS`), macOS/BSD `getentropy` (256-byte chunks) / `arc4random_buf`, Windows `BCryptGenRandom` (`BCRYPT_USE_SYSTEM_PREFERRED_RNG = 0x02`), and WASI Preview 1 `random_get`. Under `corex test --sim --seed=S`, `context.rng` switches transparently to a deterministic seeded stream so callers stay `EffectCapabilityMask.entropy == 0` while raw `os_fill_entropy` bypasses trigger `W0332`.

---

### 1.2 Structured Async Runtime, Quarantine Reaper, and OS-Futex Synchronization

Per `DR-20` `Prune-07`, full multi-core share-nothing `io_uring` buffer rings (`IORING_REGISTER_PBUF_RING`) are deferred to Phase 13.1. Phase 11.2b's bootstrap `Reactor` delivers exact `TaskGroup[E]`, `@linear TaskHandle[T]`, `64B` `InFlightOpSlot`, and `CompletionReaper` semantics across all supported targets.

> **Visual – Quarantine Reaping and 4-Byte OS Futexes Guarantee Leak-Free Cancellation and Lock-Free Fast Paths:** Top: Each in-flight operation occupies an exact 64-byte cache-aligned **InFlightOpSlot**. On early error or timeout, **TaskGroup** runs child **cancel_cleanup_bb** LIFO defers and moves pending I/O slots into **CancellingQuarantine**; nursery arena memory is held until **CompletionReaper** closes raced file/socket descriptors and releases pinned buffers. Bottom: **cx.sync.Mutex** encodes contention in a single 4-byte **AtomicU32** word, executing zero syscalls when uncontended and trapping **@no_block** violations statically via **E0322**.

#### Bootstrap `Reactor` Pollers, Bounded Worker Pool, and `--sim` Virtual Event Wheel

Calling `cx.async.block_on(own fut)` drives a thread-local `Reactor` combining an intrusive ready queue, a 64 KiB `BumpArena` root-task slab, and a 4-ary min-heap timer wheel keyed by `(deadline_ns: u64, seq_id: u64)` (where monotonic `seq_id` breaks deadline ties deterministically). Under Phase 8's `FnRegionSummary` check (`DR-20` `D-02`), direct `.await` child frames `≤16 KiB` (`ASYNC_INLINE_CAP_BYTES = 16_384`) pack directly into the parent coroutine's overlaid state union with zero allocations, whereas frames exceeding `16 KiB` emit compile-time diagnostic **`E0317`**, requiring explicit `TaskGroup` spawning. When `group.spawn(own fut)` is invoked for multi-core CPU or parallel fetch work, `MIR` Pass 2/3 statically rejects `@thread_local` captures and overlapping MVS borrows (`E0309`), dispatching the task to a lazily initialized (`cx.sync.Once`) bounded worker pool (`min(num_cpus, 8)` threads) that wakes the parent reactor via its cross-thread notifier upon completion:

| Target Platform | Poller & Timer Backend | Cross-Thread Waker | Non-Blocking I/O & Cancellation Path |
| :--- | :--- | :--- | :--- |
| **Linux** (`gnu` & `musl`) | `epoll_create1(EPOLL_CLOEXEC)` + `epoll_pwait` (`poll` fallback on restricted kernels; `timerfd` for `<1 ms` deadlines) | `eventfd(0, EFD_NONBLOCK \| EFD_CLOEXEC)` (`EPOLLIN \| EPOLLET`) | Readiness (`EPOLLIN \| EPOLLOUT \| EPOLLET \| EPOLLONESHOT`); cancel via `EPOLL_CTL_DEL` + immediate slot reap. |
| **macOS / BSD** | `kqueue()` + `kevent64` (`EV_ADD \| EV_CLEAR \| EV_ONESHOT`, `EVFILT_TIMER` with `NOTE_NSECONDS`, `poll` fallback) | `EVFILT_USER` (`ident = 0`, triggered via `NOTE_TRIGGER`) | Readiness (`EVFILT_READ` / `EVFILT_WRITE`) packing `IoUserData` in `udata`; cancel via `EV_DELETE`. |
| **Windows** | Per-reactor `IOCP` (`CreateIoCompletionPort` + `GetQueuedCompletionStatusEx`, `WSAPoll` readiness helper) | `PostQueuedCompletionStatus(iocp, 0, WAKE_KEY, null)` | Completion (`ConnectEx`, `WSARecv`, `WSASend` with inline `OVERLAPPED` in `InFlightOpSlot`); cancel via `CancelIoEx` + quarantine drain. |
| **`wasm32-wasi`** | `wasi_snapshot_preview1.poll_oneoff` (`subscription_clock` + `subscription_fd_readwrite`) | Cooperative single-thread queue | Non-blocking `fd_read` / `fd_write` on WASI pollables; immediate slot removal on cancel. |
| **`--sim` Mode** (`DR-18`) | In-memory `SimReactor` behind `Context.reactor` (`ReactorVTable`, zero OS syscalls) | PRNG-permuted ready queue (`context.rng`) | When ready queue drains, advances `virtual_now_ns` directly to `timer_heap.peek().deadline_ns`. |

#### `TaskGroup`, `64B` `InFlightOpSlot`, and `CompletionReaper` Drain Barrier (`Fix-08B`)

Cancelling an in-flight kernel operation races with asynchronous completion: dropping a coroutine frame while Windows `IOCP` (or Phase 13.1 `io_uring`) holds an `OVERLAPPED` / DMA buffer corrupts freed memory, and cancelling an `accept` or `open` that already succeeded in the kernel leaks live descriptors. `cx.async` closes both hazards through a three-step quarantine protocol over 64-byte cache-aligned `InFlightOpSlot` entries indexed by `IoUserData` (`slot_index: u32`, `generation: u24`, `op_tag: u8`):

1.  **Pinned Submission:** Submitting an I/O operation increments `group.pin_ref_count`, moves any `@linear` `IoBuf` (`sink`) into `slot.pinned_buf_ptr`, records `slot.reaper_action` (`NoResource`, `CloseSocket`, `CloseFd`, or `ReleaseIoBuf`), and sets `slot.state = .Active`.
2.  **LIFO Cancellation Cascade:** When any child task in `TaskGroup[E]` returns `.Err(e)` – or when `with_timeout` elapses – the nursery sets `group.cancel_token`, walks active child tasks in reverse LIFO spawn order, invokes `@coro_poll(child_frame, .CancelDestroy, -ECANCELED)` to execute each suspended coroutine's `cancel_cleanup_bb` `defer`/`errdefer` chain (`E0304`), and cancels every active `InFlightOpSlot` belonging to the group.
3.  **Quarantine Drain Barrier:** Readiness pollers (`epoll`/`kqueue`/`poll`) deregister the descriptor and reap the slot immediately. Completion pollers (`IOCP` `CancelIoEx` and `--sim` simulated DMA) transition `slot.state` to `.CancellingQuarantine` with `awaiting_task_id = 0xFFFF_FFFF`. **`TaskGroup` scope exit suspends on `group.waiting_on_drain` until `pin_ref_count == 0`**. When the terminal kernel completion arrives on a `.CancellingQuarantine` slot, `CompletionReaper` checks `result >= 0`: if a raced `accept`/`open` produced a live handle (`CloseSocket` / `CloseFd`), it closes that handle immediately, releases any pinned buffer, increments the 24-bit `generation` counter to reject stale ABA wakeups, and unblocks the `TaskGroup` barrier once `pin_ref_count` reaches zero.

#### Intrusive Async Waiters and 4-Byte OS-Futex Blocking Sync (`cx.sync`)

Async synchronization primitives (`cx.async.{Channel, Mutex, Semaphore, Notify}`) allocate **zero heap nodes per contended `.await`**: each suspended coroutine embeds an intrusive 24-byte `WaiterNode` directly inside its immovable coroutine frame, unlinking it in $O(1)$ inside `cancel_cleanup_bb` on cancellation and forwarding any raced wakeup baton to the next queued waiter.

For OS-thread blocking synchronization (`cx.sync.{Mutex, RwLock, Condvar, Once, WaitGroup}`), all blocking slow paths carry `@std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)`, propagating `EffectCapabilityMask.blocking_sync` (`0x0400`) up `FnRegionSummary` so `@no_block` real-time functions fail compilation with **`E0322`** if they touch blocking locks. Fast paths operate on a single 4-byte `AtomicU32` word (`Ulrich Drepper` 3-state `0 = Unlocked, 1 = Locked, 2 = Contended` for `Mutex`), delegating contention to four OS kernel primitives: Linux `futex` with `FUTEX_WAIT_PRIVATE` (`128`) and `FUTEX_WAKE_PRIVATE` (`129`) to skip in-kernel `mmap_sem` locking; macOS XNU `__ulock_wait` / `__ulock_wait2` (`UL_COMPARE_AND_WAIT | ULF_NO_ERRNO | ULF_WAIT_WORKQ_DATA_CONTENTION = 0x0101_0001`) and `__ulock_wake` (`ULF_WAKE_ALL = 0x0000_0100`); Windows `WaitOnAddress` / `WakeByAddressSingle` / `WakeByAddressAll`; and `wasm32` `memory.atomic.wait32` / `memory.atomic.notify`.

---

### 1.3 Bootstrap Networking, Zero-`libssl` HTTPS Selection, and `Span16` HTTP/1.1

#### Comparative Selection of the Phase 11.2b Zero-Bloat HTTPS TLS Strategy

Phase 11.2b must fetch sparse registry indices (`index.corex.dev`), transparency-log tiles (`sum.corex.dev`), and `.cxpkg` archives across Linux (including **fully static `x86_64-linux-musl` and `aarch64-linux-musl` builds** with zero `libssl` C dependency), macOS, and Windows. Comparing the three candidate strategies highlights clear engineering trade-offs:

> **Visual – Pure-.cx TLS 1.3 Client-Only Eliminates C libssl Dependencies and OS TLS 1.3 State Bugs:** Top: Comparing Phase 11.2b HTTPS candidates shows that hybrid OS TLS still requires a standalone TLS 1.3 implementation for static Linux **musl** while suffering from macOS SecureTransport's lack of TLS 1.3, Network.framework's hidden sockets, and Windows Schannel's TLS 1.3 post-handshake **SEC_I_RENEGOTIATE** traps. Bottom: The selected **pure-.cx TLS 1.3 client** (~1,850 LOC + ~175 LOC OS root loader) decrypts records into a reusable 16 KiB buffer indexed by 4-byte **Span16** slices and streams body chunks straight through **BaoVerifier** to disk.

| Evaluation Criterion | Option A: Hybrid Native OS TLS (`Schannel` + `SecureTransport`/`Network` + Linux TLS) | Option B: Embedded Minimal C TLS (`BearSSL` / `mbedTLS`) | **Option C (Selected): Compact Pure-`.cx` TLS 1.3 Client-Only + Native OS Root Loader** |
| :--- | :--- | :--- | :--- |
| **Static `linux-musl` C Dependencies** | **0**, *only because* Linux has no kernel/OS user-space TLS API – still requiring a standalone TLS 1.3 client on Linux. | Vendors ~25K–60K modeled LOC of C source into bootstrap; bypasses `MIR` SAST (`DR-06`). | **Zero C dependencies (`0` `libssl`, `0` C files)** across static `musl`, `gnu`, macOS, and Windows. |
| **TLS 1.3 & Non-Blocking `Reactor` Integration** | **Incompatible on macOS:** `SecureTransport` is deprecated and **lacks TLS 1.3** (removed by `curl` in May 2025); `Network.framework` exposes **no pollable socket FD** for event-loop multiplexing. | Mainline BearSSL lacks TLS 1.3; mbedTLS requires custom C BIO and allocator shims. | **100% TLS 1.3 everywhere** directly over `@linear TcpStream` (`epoll` / `kqueue` / `IOCP` / `--sim`). |
| **Post-Handshake Wire Reliability** | **Subtle Windows Pitfalls:** `Schannel` `DecryptMessage` returns `SEC_I_RENEGOTIATE` (`0x00090316`) / `0x80090317` on TLS 1.3 `NewSessionTicket`; passing empty `SECBUFFER_DATA` instead of `SECBUFFER_EXTRA` silently corrupts traffic keys (`SERVER-128041`). | Depends on C macro tuning and external X.509 buffer limits. | **Single audited `.cx` state machine** reassembling multi-record `Certificate` chains and cleanly discarding `NewSessionTicket` (`0x04`). |
| **`corex test --sim` & `MIR` SAST** | **Opaque FFI (`ffi \| unsafe_op`):** Cannot execute deterministically over virtual `SimReactor` sockets. | **Opaque FFI:** Excluded from Pentagon slice bounds verification. | **100% MVS + Pentagon verified**; runs deterministically over virtual `SimReactor` streams with `context.rng`. |
| **Modeled Engineering Scope & Phase 13.1 Reuse** | ~2,900 modeled LOC across 3 divergent stacks; Windows/macOS shims discarded in Phase 13.1. | Disposable C FFI bridge retired in Phase 13.1. | **~1,850 modeled LOC TLS + ~175 modeled LOC `CertBundle`**; upgrades **in-place** to Phase 13.1 `@secret` TLS 1.3 (`D-05`). |

**Architectural Decision (`STD-03-TLS`):** Phase 11.2b adopts **Option C: Compact Pure-`.cx` TLS 1.3 Client-Only (`stdlib/cx/net/tls_bootstrap.cx`) paired with Native OS Root Certificate Loading (`CertBundle.load_system`)**. Because `cx.crypto` already supplies `Sha256`, `Sha384`/`Sha512`, `Ed25519`, and `Csprng`, completing a strict RFC 8446 1-RTT client requires only `X25519` (RFC 7748 constant-time Montgomery ladder with all-zero low-order shared-secret rejection, plus `secp256r1` `HelloRetryRequest` fallback), `ChaCha20-Poly1305` (`0x1303`, RFC 8439) and `AES-128-GCM` (`0x1301`, constant-time bitsliced `aes_ct64` + `ghash_ctmul64`), and a read-only DER X.509v3 chain verifier. Incorporating compatibility lessons from Zig's `std.crypto.tls.Client` field testing (`#14172`), the client omits `AES_256_GCM_SHA384` (avoiding needing a second SHA-384 HKDF transcript engine and avoiding `TlsDecryptError` server bugs), includes `ecdsa_secp384r1_sha384` and up to 4096-bit RSA-PSS public key buffers, and reassembles handshake messages up to `32 KiB` across arbitrary TLS record boundaries so multi-record `Certificate` flights from CDNs (such as 3-record 2,844-byte chains) never trigger spurious decode failures.

To anchor trust without shipping static CA bundles that go stale, `CertBundle.load_system()` scans native OS root stores into a deduplicated DER byte arena indexed by `Wyhash64(subject_der_slice)`:

| Host Operating System | Native Trust-Store Discovery Order (`CertBundle.load_system`) | Format & Implementation Notes |
| :--- | :--- | :--- |
| **Linux** (`gnu` & static `musl`) | `SSL_CERT_FILE` override $\rightarrow$ first existing file in `/etc/ssl/certs/ca-certificates.crt` (Debian/Ubuntu), `/etc/pki/tls/certs/ca-bundle.crt` (Fedora/RHEL), `/etc/ssl/ca-bundle.pem` (OpenSUSE), `/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem`, `/etc/ssl/cert.pem` (Alpine/`musl`), plus `/etc/ssl/certs` directory scan. | Pure-`.cx` PEM Base64 $\rightarrow$ DER decoder; ignores expired certs (`now_sec > validity.not_after`) and unrecognized OIDs. |
| **macOS** (`aarch64` & `x86_64`) | `/etc/ssl/cert.pem` + binary Keychain parser on `/System/Library/Keychains/SystemRootCertificates.keychain` and optional non-fatal scan of `/Library/Keychains/System.keychain`. | Parses Apple big-endian `kych` X.509 records directly from disk using exact `read_exact` length loops (avoiding Zig `#22870` short-read/missing-keychain bugs) with zero Security.framework C FFI. |
| **BSD** (`FreeBSD`, `OpenBSD`, `NetBSD`) | `/etc/ssl/cert.pem` (FreeBSD/OpenBSD), `/etc/openssl/certs/ca-certificates.crt` (NetBSD). | Pure-`.cx` PEM Base64 $\rightarrow$ DER decoder. |
| **Windows** (`x86_64` & `aarch64`) | `CertOpenSystemStoreW(null, L"ROOT")` + `CertEnumCertificatesInStore` + `CertCloseStore` (`crypt32.dll`, `@std_cap_boundary(emits: .Fs, clears: .FfiUnsafe)`). | Copies `pbCertEncoded[0..cbCertEncoded]` DER slices directly into `CertBundle.der_bytes`. |

#### RFC-Compliant Zero-Alloc Addresses, Non-Blocking Sockets, DNS, and `Span16` HTTP/1.1

`Ipv4Addr.parse`, `Ipv6Addr.parse`, and `SocketAddr.parse` execute in `@no_alloc @no_panic @no_block` pure `.cx`: `Ipv4Addr` enforces strict 4-octet decimal notation rejecting leading zeros (`010.0.0.1` $\rightarrow$ `AddrParseError.LeadingZeroOctet` to prevent octal SSRF parser differentials); `Ipv6Addr` implements RFC 4291 / RFC 5952 parsing (at most one `::` zero-run compression and optional trailing IPv4-mapped `::ffff:192.0.2.1` quartet); and `SocketAddr` parses `a.b.c.d:port` and bracketed `[ipv6]:port`. All `@linear` sockets (`TcpStream`, `TcpListener`, `UdpSocket`) configure atomic close-on-exec and non-blocking modes at creation (`SOCK_NONBLOCK | SOCK_CLOEXEC` + `MSG_NOSIGNAL` on Linux; `FD_CLOEXEC` + `O_NONBLOCK` + `SO_NOSIGPIPE = 0x1022` on macOS; `WSA_FLAG_OVERLAPPED | WSA_FLAG_NO_HANDLE_INHERIT = 0x81` + `FILE_SKIP_COMPLETION_PORT_ON_SUCCESS = 1` + `SO_UPDATE_CONNECT_CONTEXT = 0x7010` + `SIO_UDP_CONNRESET = false` on Windows), with `IPV6_V6ONLY = 0` when `dual_stack: true` is requested. To avoid blocking OS threads in `libc` `getaddrinfo` (and avoid `glibc` NSS dynamic-library traps in static builds), `cx.net.resolve_host` parses `/etc/hosts` and `/etc/resolv.conf` directly and queries nameservers asynchronously over non-blocking `UdpSocket` (with TCP fallback on `TC = 1` truncation) before racing IPv6 and IPv4 candidates with a 250 ms RFC 8305 Happy Eyeballs stagger inside `cx.async.task_group`.

Above the transport, `cx.http.Client` reads response headers into a reusable `16 KiB` connection buffer and indexes header names and values via unboxed 4-byte `Span16` (`{ off: u16, len: u16 }`) descriptors – matching the zero-allocation `httpz` pattern noted in `DR-06` and `DR-15`. Body streaming decodes `Content-Length` or `Transfer-Encoding: chunked` via a `DR-22` `SE-23` labeled `match` (`continue :fsm`) state machine, pooling up to 8 idle keep-alive connections and piping `.cxpkg` chunks straight through `BaoVerifier` or `Blake3.Hasher` into `~/.corex/cache/blake3/staging/`.

---

## 2. Deliverable 1: Complete Canonical `.cx` Public API Signatures

All signatures below conform strictly to `DR-21` and `DR-22` (`cx.*` root namespace, unified `.` paths, `T!E` and `T?` types, `&T`/`&mut T`/`own T`/`&out T` MVS modes, `/` and `*` parameter zones, `bit_field Name: uN`, `enum Name: Int`, and omitted `-> unit`).

### 2.1 `stdlib/cx/crypto.cx`

```rust
mod crypto;

use cx.io.{IoError, Reader, Writer};

pub type Digest256 = [u8; 32];
pub type Digest384 = [u8; 48];
pub type Digest512 = [u8; 64];
pub type Key256    = [u8; 32];
pub type Key128    = [u8; 16];
pub type Nonce96   = [u8; 12];
pub type Tag128    = [u8; 16];

@derive(Copy, Equatable)
pub enum CryptoError: u8 {
    AuthenticationFailed = 1,
    InvalidSignature     = 2,
    InvalidPublicKey     = 3,
    WeakKeyShare         = 4,
    BaoHeaderTruncated   = 5,
    BaoHashMismatch      = 6,
    BaoLengthMismatch    = 7,
    MerkleProofInvalid   = 8,
    EntropyUnavailable   = 9,
}

@inline @no_alloc @no_panic @no_block
pub fn constant_time_eq(a: &[u8], b: &[u8], /) -> bool;

@inline @no_alloc @no_panic @no_block
pub fn secure_zeroize(buf: &mut [u8], /);

// ============================================================================
// 1. BLAKE3 (Standard, Keyed `.cxi`, Derive-Key `tree_blake3`, & Bao `.obao`)
// ============================================================================
pub mod blake3 {
    use super.{CryptoError, Digest256, Key256};
    use cx.io.{IoError, Reader, Writer};

    pub const OUT_LEN: usize   = 32;
    pub const KEY_LEN: usize   = 32;
    pub const BLOCK_LEN: usize = 64;
    pub const CHUNK_LEN: usize = 1024;
    pub const MAX_DEPTH: usize = 54;

    @no_alloc @no_panic @no_block
    pub fn hash(data: &[u8], /) -> Digest256;

    @no_alloc @no_panic @no_block
    pub fn keyed_hash(key: &Key256, data: &[u8], /) -> Digest256;

    @no_alloc @no_panic @no_block
    pub fn derive_key(context_str: str, key_material: &[u8], /) -> Digest256;

    pub struct Hasher {
        key_words: [u32; 8],
        chunk_cv: [u32; 8],
        chunk_counter: u64,
        buf: [u8; 64],
        buf_len: u8,
        blocks_compressed: u8,
        flags: u8,
        cv_stack_len: u8,
        cv_stack: [[u32; 8]; 54],
    }

    impl Hasher {
        @no_alloc @no_panic @no_block pub fn init() -> Self;
        @no_alloc @no_panic @no_block pub fn init_keyed(key: &Key256, /) -> Self;
        @no_alloc @no_panic @no_block pub fn init_derive_key(context_str: str, /) -> Self;
        @no_alloc @no_panic @no_block pub fn update(&mut self, input: &[u8], /);
        @no_alloc @no_panic @no_block pub fn finalize(&self) -> Digest256;
        @no_alloc @no_panic @no_block pub fn finalize_xof(&self, seek_byte: u64, out: &mut [u8], /);
    }

    /// Iterative O(1)-heap (`1,856 B` = `128 B` header + `1,728 B` stack) Bao verifier.
    /// Never exposes `claimed_len` until the final chunk + stream EOF validate.
    @repr(C)
    pub struct BaoVerifier {
        expected_root: Digest256,
        scratch_node: [u8; 64],
        claimed_len: u64,
        total_chunks: u64,
        next_chunk_idx: u64,
        cv_stack_len: u8,
        header_parsed: bool,
        finalized_ok: bool,
        _reserved: [u8; 5] = [0; 5],
        cv_stack: [Digest256; 54],
    }

    @derive(Copy, Equatable)
    pub enum VerifyError {
        Crypto(CryptoError),
        Io(IoError),
    }

    impl BaoVerifier {
        @no_alloc @no_panic @no_block
        pub fn init(expected_root: &Digest256, /) -> Self;

        @no_alloc @no_panic @no_block
        pub fn feed_header(&mut self, hdr: &[u8; 8], /);

        @no_alloc @no_panic @no_block
        pub fn pending_parent_count(&self) -> usize;

        @no_alloc @no_panic @no_block
        pub fn verify_next_chunk(
            &mut self,
            parent_nodes_obao: &[u8],
            chunk_data: &[u8],
            /,
        ) -> usize!CryptoError;

        @no_alloc @no_panic @no_block
        pub fn verified_len(&self) -> u64?;
    }

    pub fn verify_outboard_stream[D: Reader, O: Reader, W: Writer](
        data_reader: &mut D,
        obao_reader: &mut O,
        expected_root: &Digest256,
        out_writer: &mut W,
        /,
    ) -> u64!VerifyError;

    pub fn verify_slice_stream[S: Reader, W: Writer](
        slice_reader: &mut S,
        expected_root: &Digest256,
        slice_start: u64,
        slice_len: u64,
        out_writer: &mut W,
        /,
    ) -> u64!VerifyError;
}

// ============================================================================
// 2. SHA-256 & SHA-384 / SHA-512 (FIPS 180-4 + HMAC + RFC 5869 HKDF)
// ============================================================================
pub mod sha256 {
    use super.{CryptoError, Digest256};

    pub const OUT_LEN: usize   = 32;
    pub const BLOCK_LEN: usize = 64;

    pub struct Hasher {
        state: [u32; 8],
        buf: [u8; 64],
        total_bytes: u64,
        buf_len: u8,
    }

    impl Hasher {
        @no_alloc @no_panic @no_block pub fn init() -> Self;
        @no_alloc @no_panic @no_block pub fn update(&mut self, data: &[u8], /);
        @no_alloc @no_panic @no_block pub fn finalize(&self) -> Digest256;
    }

    @no_alloc @no_panic @no_block pub fn hash(data: &[u8], /) -> Digest256;
    @no_alloc @no_panic @no_block pub fn hmac(key: &[u8], data: &[u8], /) -> Digest256;
    @no_alloc @no_panic @no_block pub fn hkdf_extract(salt: &[u8], ikm: &[u8], /) -> Digest256;
    @no_alloc @no_panic @no_block pub fn hkdf_expand(prk: &Digest256, info: &[u8], out: &mut [u8], /) -> unit!CryptoError;
}

pub mod sha512 {
    use super.{Digest384, Digest512};

    pub struct Hasher {
        state: [u64; 8],
        buf: [u8; 128],
        total_lo: u64,
        total_hi: u64,
        buf_len: u8,
    }

    impl Hasher {
        @no_alloc @no_panic @no_block pub fn init() -> Self;
        @no_alloc @no_panic @no_block pub fn init_384() -> Self;
        @no_alloc @no_panic @no_block pub fn update(&mut self, data: &[u8], /);
        @no_alloc @no_panic @no_block pub fn finalize(&self) -> Digest512;
        @no_alloc @no_panic @no_block pub fn finalize_384(&self) -> Digest384;
    }

    @no_alloc @no_panic @no_block pub fn hash(data: &[u8], /) -> Digest512;
    @no_alloc @no_panic @no_block pub fn hash_384(data: &[u8], /) -> Digest384;
}

// ============================================================================
// 3. Strict Constant-Time Ed25519 Verification & RFC 6962 / 9162 Merkle Proofs
// ============================================================================
pub mod ed25519 {
    use super.CryptoError;

    pub const PUBLIC_KEY_LEN: usize = 32;
    pub const SIGNATURE_LEN: usize  = 64;

    pub type PublicKey = [u8; 32];
    pub type Signature = [u8; 64];

    @no_alloc @no_panic @no_block
    pub fn verify(
        public_key: &PublicKey,
        message: &[u8],
        signature: &Signature,
        /,
    ) -> unit!CryptoError;
}

pub mod merkle {
    use super.{CryptoError, Digest256};

    pub const LEAF_PREFIX: u8 = 0x00;
    pub const NODE_PREFIX: u8 = 0x01;

    @no_alloc @no_panic @no_block
    pub fn hash_leaf(record: &[u8], /) -> Digest256;

    @no_alloc @no_panic @no_block
    pub fn hash_children(left: &Digest256, right: &Digest256, /) -> Digest256;

    @no_alloc @no_panic @no_block
    pub fn verify_inclusion(
        leaf_index: u64,
        tree_size: u64,
        leaf_hash: &Digest256,
        audit_path: &[Digest256],
        expected_root: &Digest256,
        /,
    ) -> unit!CryptoError;

    @no_alloc @no_panic @no_block
    pub fn verify_consistency(
        old_size: u64,
        new_size: u64,
        old_root: &Digest256,
        new_root: &Digest256,
        proof: &[Digest256],
        /,
    ) -> unit!CryptoError;
}

// ============================================================================
// 4. Wyhash v4.3 (64-Bit `WyHasher`, 128-Bit `Fingerprint128`, & `WyRand`)
// ============================================================================
pub mod wyhash {
    @repr(C)
    @derive(Copy, Equatable, Comparable)
    pub struct Fingerprint128 {
        pub lo: u64,
        pub hi: u64,
    }

    pub struct WyHasher {
        seed: u64,
        see1: u64,
        see2: u64,
        total_len: u64,
        buf: [u8; 48],
        buf_len: u8,
    }

    impl WyHasher {
        @inline @no_alloc @no_panic @no_block pub fn init(seed: u64 = 0, /) -> Self;
        @no_alloc @no_panic @no_block pub fn update(&mut self, bytes: &[u8], /);
        @no_alloc @no_panic @no_block pub fn finish(&self) -> u64;
        @no_alloc @no_panic @no_block pub fn finish_128(&self) -> Fingerprint128;
    }

    @inline @no_alloc @no_panic @no_block
    pub fn hash64(bytes: &[u8], /, *, seed: u64 = 0) -> u64;

    @inline @no_alloc @no_panic @no_block
    pub fn hash128(bytes: &[u8], /, *, seed: u64 = 0) -> Fingerprint128;

    pub struct WyRand { state: u64 }
    impl WyRand {
        @inline @no_alloc @no_panic @no_block pub fn init(seed: u64, /) -> Self;
        @inline @no_alloc @no_panic @no_block pub fn next_u64(&mut self) -> u64;
        @no_alloc @no_panic @no_block pub fn fill_bytes(&mut self, out: &mut [u8], /);
    }
}

// ============================================================================
// 5. OS CSPRNG (`context.rng` Seam for `--sim --seed` Replay) & TLS AEAD/KEX
// ============================================================================
pub mod csprng {
    use super.CryptoError;

    @no_alloc @no_panic
    pub fn fill_bytes(out: &mut [u8], /) -> unit!CryptoError;

    @no_alloc @no_panic
    pub fn random_array[const N: usize]() -> [u8; N]!CryptoError;

    @std_cap_boundary(emits: .Entropy, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn os_fill_entropy(out: &mut [u8], /) -> unit!CryptoError;
}

pub mod x25519 {
    use super.CryptoError;

    @no_alloc @no_panic @no_block
    pub fn diffie_hellman(scalar: &[u8; 32], peer_public: &[u8; 32], /) -> [u8; 32]!CryptoError;

    @no_alloc @no_panic @no_block
    pub fn public_from_private(scalar: &[u8; 32], /) -> [u8; 32];
}

pub mod chacha20_poly1305 {
    use super.{CryptoError, Key256, Nonce96, Tag128};

    @no_alloc @no_panic @no_block
    pub fn seal_in_place(key: &Key256, nonce: &Nonce96, aad: &[u8], plaintext_in_out: &mut [u8], /) -> Tag128;

    @no_alloc @no_panic @no_block
    pub fn open_in_place(
        key: &Key256, nonce: &Nonce96, aad: &[u8], ciphertext_in_out: &mut [u8], tag: &Tag128, /,
    ) -> unit!CryptoError;
}

pub mod aes128_gcm {
    use super.{CryptoError, Key128, Nonce96, Tag128};

    @no_alloc @no_panic @no_block
    pub fn seal_in_place(key: &Key128, nonce: &Nonce96, aad: &[u8], plaintext_in_out: &mut [u8], /) -> Tag128;

    @no_alloc @no_panic @no_block
    pub fn open_in_place(
        key: &Key128, nonce: &Nonce96, aad: &[u8], ciphertext_in_out: &mut [u8], tag: &Tag128, /,
    ) -> unit!CryptoError;
}
```

### 2.2 `stdlib/cx/async.cx`

```rust
mod async;

use cx.io.IoError;
use cx.time.Duration;

@lang("async_task")
@linear
pub struct AsyncTask[T] {
    frame_ptr: *mut opaque,
}

// ============================================================================
// 1. Reactor Simulation Seam (`DR-20` Seam #5) & `64B` Quarantine Op Table
// ============================================================================
@derive(Copy, Equatable)
pub enum OpTag: u8 {
    Nop           = 0,
    Accept        = 1,
    Connect       = 2,
    Recv          = 3,
    Send          = 4,
    TimerDeadline = 5,
    AsyncCancel   = 6,
}

pub bit_field IoUserData: u64 {
    pub slot_index: u32   | 32,
    pub generation: u32   | 24,
    pub op_tag:     OpTag | 8,
}

@derive(Copy, Equatable)
pub enum SlotState: u8 {
    Free                 = 0,
    Active               = 1,
    CancellingQuarantine = 2,
}

@derive(Copy, Equatable)
pub enum ReaperAction: u8 {
    NoResource   = 0,
    CloseSocket  = 1,
    CloseFd      = 2,
    ReleaseIoBuf = 3,
}

pub bit_field SlotGenState: u32 {
    pub generation: u32       | 24,
    pub state:      SlotState | 8,
}

/// Exact 64-byte (1 cache line on 64-bit targets) operation tracking slot (`Fix-08B`).
@repr(C)
@cache_aligned
pub struct InFlightOpSlot {
    pub awaiting_task_id: u32,
    pub gen_and_state: SlotGenState,
    pub reaper_action: ReaperAction,
    pub _pad0: [u8; 3] = [0; 3],
    pub raw_fd_or_sock: i32,
    pub pinned_buf_ptr: *mut u8?,
    pub pinned_buf_cap: u32,
    pub group_id: u32,
    pub platform_overlapped: [u64; 4],
}

@repr(C)
pub struct ReactorVTable {
    pub monotonic_ns: fn(*mut opaque) -> u64,
    pub wall_epoch_ns: fn(*mut opaque) -> i64,
    pub fill_rng: fn(*mut opaque, &mut [u8]) -> bool,
    pub register_timer: fn(*mut opaque, u64, u32) -> IoUserData,
    pub submit_poll_op: fn(*mut opaque, i32, OpTag, ReaperAction, u32) -> IoUserData!IoError,
    pub cancel_op: fn(*mut opaque, IoUserData),
}

// ============================================================================
// 2. Structured `TaskGroup[E]`, `@linear TaskHandle[T]`, & Execution Entrypoints
// ============================================================================
@derive(Copy)
pub struct CancelToken {
    flags_ptr: *u32,
}

impl CancelToken {
    @inline @no_alloc @no_panic @no_block
    pub fn is_cancelled(self) -> bool;
}

@derive(Copy, Equatable)
pub enum TimeoutError: u8 {
    Elapsed   = 1,
    Cancelled = 2,
}

@linear
pub struct TaskHandle[T] {
    task_id: u32,
    group_id: u32,
}

impl[T] TaskHandle[T] {
    pub async fn join[E](own self) -> T!E;
    pub async fn cancel(own self);
}

@linear
pub struct TaskGroup[E] {
    group_id: u32,
    active_children: u32,
    pin_ref_count: u32,
    has_error: bool,
}

impl[E] TaskGroup[E] {
    pub fn spawn_local[T](&mut self, fut: own AsyncTask[T!E], /) -> TaskHandle[T];
    pub fn spawn[T](&mut self, fut: own AsyncTask[T!E], /) -> TaskHandle[T];

    pub fn for_each_chunk_mut[Elem](
        &mut self,
        slice: &mut [Elem],
        chunk_size: usize,
        body: |usize, &mut [Elem]| -> unit!E,
        /,
    ) -> unit!E;

    pub fn cancel_remaining(&mut self);
    pub fn token(&self) -> CancelToken;
}

pub async fn task_group[R, E](body: async |&mut TaskGroup[E]| -> R!E, /) -> R!E;

@std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
pub fn block_on[T](fut: own AsyncTask[T], /) -> T;

pub async fn yield_now();
pub async fn sleep(dur: Duration, /);
pub async fn with_timeout[T](dur: Duration, fut: own AsyncTask[T], /) -> T!TimeoutError;

// ============================================================================
// 3. Intrusive Zero-Heap-Waiter Async Primitives (`Channel`, `Mutex`, `Semaphore`, `Notify`)
// ============================================================================
@derive(Copy, Equatable)
pub enum SendError[T] {
    Closed(T),
    Cancelled(T),
}

@derive(Copy, Equatable)
pub enum TrySendError[T] {
    Full(T),
    Closed(T),
}

pub(pkg) struct ChannelShared[T] {
    head: usize,
    tail: usize,
    cap: usize,
    closed: bool,
    buf_ptr: *mut T,
    send_waiters: *mut opaque?,
    recv_waiters: *mut opaque?,
}

pub struct Sender[T]   { shared: *mut ChannelShared[T] }
pub struct Receiver[T] { shared: *mut ChannelShared[T] }

pub fn channel[T](cap: usize, /) -> (Sender[T], Receiver[T]);

impl[T] Sender[T] {
    pub async fn send(&self, item: own T, /) -> unit!SendError[T];
    pub fn try_send(&self, item: own T, /) -> unit!TrySendError[T];
    pub fn clone(&self) -> Self;
    pub fn close(own self);
}

impl[T] Receiver[T] {
    pub async fn recv(&self) -> T?;
    pub fn try_recv(&self) -> T?;
    pub fn clone(&self) -> Self;
    pub fn close(own self);
}

@linear
pub struct MutexGuard[T] {
    lock_ptr: *mut Mutex[T],
}

impl[T] MutexGuard[T] {
    @inline pub fn get(&self) -> &T;
    @inline pub fn get_mut(&mut self) -> &mut T;
    pub fn unlock(own self);
}

pub struct Mutex[T] {
    state: u32,
    waiters_head: *mut opaque?,
    waiters_tail: *mut opaque?,
    data: T,
}

pub type AsyncMutex[T] = Mutex[T];

impl[T] Mutex[T] {
    pub fn new(val: own T, /) -> Self;
    pub async fn lock(&self) -> MutexGuard[T];
    pub fn try_lock(&self) -> MutexGuard[T]?;
}

@linear
pub struct SemaphorePermit { sem_ptr: *mut Semaphore, count: u32 }
impl SemaphorePermit { pub fn release(own self); }

pub struct Semaphore {
    permits: u32,
    waiters_head: *mut opaque?,
    waiters_tail: *mut opaque?,
}

impl Semaphore {
    pub comptime fn new(initial_permits: u32, /) -> Self;
    pub async fn acquire(&self, count: u32 = 1, /) -> SemaphorePermit!TimeoutError;
    pub fn try_acquire(&self, count: u32 = 1, /) -> SemaphorePermit?;
}

pub struct Notify {
    state: u32,
    waiters_head: *mut opaque?,
    waiters_tail: *mut opaque?,
}

impl Notify {
    pub comptime fn new() -> Self;
    pub async fn notified(&self);
    pub fn notify_one(&self);
    pub fn notify_waiters(&self);
}
```

### 2.3 `stdlib/cx/sync.cx`

```rust
mod sync;

pub use core.atomic.{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, MemoryOrder, fence};
use cx.time.Duration;

pub mod futex {
    use super.AtomicU32;
    use cx.time.Duration;

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn wait(word: &AtomicU32, expected: u32, /, *, timeout: Duration? = .None) -> bool;

    @std_cap_boundary(emits: .Pure, clears: .FfiUnsafe)
    @no_alloc @no_panic @no_block
    pub fn wake_one(word: &AtomicU32, /);

    @std_cap_boundary(emits: .Pure, clears: .FfiUnsafe)
    @no_alloc @no_panic @no_block
    pub fn wake_all(word: &AtomicU32, /);
}

@linear
pub struct MutexGuard[T] {
    mutex_ptr: *mut Mutex[T],
}

impl[T] MutexGuard[T] {
    @inline @no_alloc @no_panic @no_block pub fn get(&self) -> &T;
    @inline @no_alloc @no_panic @no_block pub fn get_mut(&mut self) -> &mut T;
    @no_alloc @no_panic @no_block pub fn unlock(own self);
}

pub struct Mutex[T] {
    state: AtomicU32, // 0 = Unlocked, 1 = LockedUncontended, 2 = LockedContended
    value: T,
}

impl[T] Mutex[T] {
    @inline @no_alloc @no_panic @no_block
    pub comptime fn new(val: own T, /) -> Self;

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn lock(&self) -> MutexGuard[T];

    @inline @no_alloc @no_panic @no_block
    pub fn try_lock(&self) -> MutexGuard[T]?;

    @inline @no_alloc @no_panic @no_block
    pub fn into_inner(own self) -> T;
}

@linear pub struct RwReadGuard[T]  { rw_ptr: *mut RwLock[T] }
@linear pub struct RwWriteGuard[T] { rw_ptr: *mut RwLock[T] }

impl[T] RwReadGuard[T] {
    @inline @no_alloc @no_panic @no_block pub fn get(&self) -> &T;
    @no_alloc @no_panic @no_block pub fn unlock(own self);
}

impl[T] RwWriteGuard[T] {
    @inline @no_alloc @no_panic @no_block pub fn get(&self) -> &T;
    @inline @no_alloc @no_panic @no_block pub fn get_mut(&mut self) -> &mut T;
    @no_alloc @no_panic @no_block pub fn unlock(own self);
}

pub struct RwLock[T] {
    state: AtomicU32,       // Bit 31: writer_active, Bit 30: writer_waiting, Bits 0..29: reader_count
    writer_wake: AtomicU32,
    reader_wake: AtomicU32,
    value: T,
}

impl[T] RwLock[T] {
    @inline @no_alloc @no_panic @no_block pub comptime fn new(val: own T, /) -> Self;

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn read(&self) -> RwReadGuard[T];

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn write(&self) -> RwWriteGuard[T];

    @no_alloc @no_panic @no_block pub fn try_read(&self) -> RwReadGuard[T]?;
    @no_alloc @no_panic @no_block pub fn try_write(&self) -> RwWriteGuard[T]?;
}

pub struct Condvar {
    seq: AtomicU32,
}

impl Condvar {
    @inline @no_alloc @no_panic @no_block
    pub comptime fn new() -> Self = Self { seq: AtomicU32.new(0) };

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn wait[T](&self, guard: own MutexGuard[T], /) -> MutexGuard[T];

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn wait_timeout[T](&self, guard: own MutexGuard[T], dur: Duration, /) -> (MutexGuard[T], bool);

    @no_alloc @no_panic @no_block pub fn notify_one(&self);
    @no_alloc @no_panic @no_block pub fn notify_all(&self);
}

pub struct Once {
    state: AtomicU32,
}

impl Once {
    @inline @no_alloc @no_panic @no_block
    pub comptime fn new() -> Self = Self { state: AtomicU32.new(0) };

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    pub fn call_once(&self, init_fn: ||, /);

    @inline @no_alloc @no_panic @no_block
    pub fn is_completed(&self) -> bool = self.state.load(.Acquire) == 3;
}

pub struct WaitGroup {
    packed_state: AtomicU64,
    futex_word: AtomicU32,
}

impl WaitGroup {
    @inline @no_alloc @no_panic @no_block pub comptime fn new() -> Self;
    @no_alloc @no_panic @no_block pub fn add(&self, delta: u32 = 1, /);
    @no_alloc @no_panic @no_block pub fn done(&self);

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn wait(&self);
}
```

### 2.4 `stdlib/cx/net.cx`

```rust
mod net;

use cx.col.{Map, Vec};
use cx.io.IoError;
use cx.time.Duration;

@derive(Copy, Equatable)
pub enum AddrParseError: u8 {
    Empty              = 1,
    InvalidIpv4Octet   = 2,
    LeadingZeroOctet   = 3,
    InvalidIpv6Group   = 4,
    MultipleEllipses   = 5,
    MissingPort        = 6,
    PortOverflow       = 7,
    UnclosedBracket    = 8,
}

@repr(C)
@derive(Copy, Equatable, Comparable)
pub struct Ipv4Addr {
    pub octets: [u8; 4],
}

impl Ipv4Addr {
    pub const LOCALHOST: Ipv4Addr   = Ipv4Addr { octets: [127, 0, 0, 1] };
    pub const UNSPECIFIED: Ipv4Addr = Ipv4Addr { octets: [0, 0, 0, 0] };

    @no_alloc @no_panic @no_block pub fn parse(s: str, /) -> Self!AddrParseError;
    @inline @no_alloc @no_panic @no_block pub fn to_be_u32(self) -> u32;
}

@repr(C)
@derive(Copy, Equatable, Comparable)
pub struct Ipv6Addr {
    pub segments: [u16; 8],
}

impl Ipv6Addr {
    pub const LOCALHOST: Ipv6Addr   = Ipv6Addr { segments: [0, 0, 0, 0, 0, 0, 0, 1] };
    pub const UNSPECIFIED: Ipv6Addr = Ipv6Addr { segments: [0; 8] };

    @no_alloc @no_panic @no_block pub fn parse(s: str, /) -> Self!AddrParseError;
    @no_alloc @no_panic @no_block pub fn octets(self) -> [u8; 16];
}

@derive(Copy, Equatable, Comparable)
pub enum IpAddr {
    V4(Ipv4Addr),
    V6(Ipv6Addr),
}

impl IpAddr {
    @no_alloc @no_panic @no_block pub fn parse(s: str, /) -> Self!AddrParseError;
}

@repr(C)
@derive(Copy, Equatable, Comparable)
pub struct SocketAddrV4 {
    pub ip: Ipv4Addr,
    pub port: u16,
}

@repr(C)
@derive(Copy, Equatable, Comparable)
pub struct SocketAddrV6 {
    pub ip: Ipv6Addr,
    pub port: u16,
    pub flowinfo: u32 = 0,
    pub scope_id: u32 = 0,
}

@derive(Copy, Equatable, Comparable)
pub enum SocketAddr {
    V4(SocketAddrV4),
    V6(SocketAddrV6),
}

impl SocketAddr {
    @no_alloc @no_panic @no_block pub fn parse(s: str, /) -> Self!AddrParseError;
    @inline @no_alloc @no_panic @no_block pub fn ip(self) -> IpAddr;
    @inline @no_alloc @no_panic @no_block pub fn port(self) -> u16;
}

pub struct ResolvedAddrs {
    pub addrs: [SocketAddr; 16],
    pub count: u8,
}

pub async fn resolve_host(
    host: str,
    port: u16,
    /,
    *,
    timeout: Duration = Duration.from_millis(3_000),
) -> ResolvedAddrs!IoError;

@linear
pub struct TcpStream {
    raw_handle: i64,
}

impl TcpStream {
    pub async fn connect(
        addr: SocketAddr,
        /,
        *,
        timeout: Duration = Duration.from_millis(5_000),
        nodelay: bool = true,
    ) -> Self!IoError;

    pub async fn connect_host(
        host: str,
        port: u16,
        /,
        *,
        timeout: Duration = Duration.from_millis(5_000),
        nodelay: bool = true,
    ) -> Self!IoError;

    pub async fn read(&mut self, buf: &mut [u8], /) -> usize!IoError;
    pub async fn read_exact(&mut self, buf: &mut [u8], /) -> unit!IoError;
    pub async fn write(&mut self, buf: &[u8], /) -> usize!IoError;
    pub async fn write_all(&mut self, buf: &[u8], /) -> unit!IoError;
    pub fn set_nodelay(&mut self, enabled: bool, /) -> unit!IoError;
    pub fn peer_addr(&self) -> SocketAddr!IoError;
    pub fn close(own self);
}

@linear
pub struct TcpListener {
    raw_handle: i64,
}

impl TcpListener {
    pub fn bind(
        addr: SocketAddr,
        /,
        *,
        reuse_addr: bool = true,
        dual_stack: bool = false,
        backlog: u32 = 128,
    ) -> Self!IoError;

    pub async fn accept(&mut self) -> (TcpStream, SocketAddr)!IoError;
    pub fn local_addr(&self) -> SocketAddr!IoError;
    pub fn close(own self);
}

@linear
pub struct UdpSocket {
    raw_handle: i64,
}

impl UdpSocket {
    pub fn bind(addr: SocketAddr, /, *, dual_stack: bool = false) -> Self!IoError;
    pub async fn send_to(&mut self, buf: &[u8], target: SocketAddr, /) -> usize!IoError;
    pub async fn recv_from(&mut self, buf: &mut [u8], /) -> (usize, SocketAddr)!IoError;
    pub fn local_addr(&self) -> SocketAddr!IoError;
    pub fn close(own self);
}

@derive(Copy, Equatable)
pub enum TlsError: u8 {
    IoError                   = 1,
    UnexpectedMessage         = 2,
    RecordOverflow            = 3,
    HandshakeTooLarge         = 4,
    UnsupportedProtocol       = 5,
    UnsupportedCipherSuite    = 6,
    BadRecordMac              = 7,
    InvalidServerKeyShare     = 8,
    CertChainEmpty            = 9,
    CertChainTooDeep          = 10,
    CertExpiredOrNotYetValid  = 11,
    CertHostnameMismatch      = 12,
    CertUntrustedRoot         = 13,
    CertSignatureInvalid      = 14,
    FinishedVerifyMismatch    = 15,
    PeerAlertReceived         = 16,
}

pub struct CertBundle {
    der_bytes: Vec[u8],
    subject_index: Map[u64, u32],
}

impl CertBundle {
    pub fn load_system() -> Self!IoError;
    pub fn add_pem_bytes(&mut self, pem: &[u8], /) -> u32!TlsError;
}

pub struct TlsClientConfig {
    pub root_certs: &CertBundle,
    pub handshake_timeout: Duration = Duration.from_millis(10_000),
    pub alpn_http11: bool = true,
}

@linear
pub struct TlsClientStream {
    tcp: TcpStream,
    cipher_id: u16,
    client_app_key: [u8; 32],
    server_app_key: [u8; 32],
    client_app_iv: [u8; 12],
    server_app_iv: [u8; 12],
    client_seq: u64,
    server_seq: u64,
    cleartext_pos: u16,
    cleartext_len: u16,
    eof_received: bool,
    record_buf: [u8; 16_640],
}

impl TlsClientStream {
    pub async fn connect(
        tcp: own TcpStream,
        server_name: str,
        config: &TlsClientConfig,
        /,
    ) -> Self!TlsError;

    pub async fn read(&mut self, out: &mut [u8], /) -> usize!TlsError;
    pub async fn write_all(&mut self, data: &[u8], /) -> unit!TlsError;
    pub async fn close_notify(own self) -> unit!TlsError;
    pub fn close_abort(own self);
}
```

### 2.5 `stdlib/cx/http.cx`

```rust
mod http;

use cx.crypto.Digest256;
use cx.io.{IoError, Writer};
use cx.mem.{Arena, Span16};
use cx.net.{CertBundle, TcpStream, TlsClientStream, TlsError};
use cx.time.Duration;

pub const MAX_HEADER_BYTES: usize    = 16_384;
pub const MAX_HEADERS: usize         = 64;
pub const DEFAULT_MAX_REDIRECTS: u8  = 5;

@derive(Copy, Equatable)
pub enum Method: u8 {
    Get  = 1,
    Head = 2,
    Post = 3,
    Put  = 4,
}

@derive(Copy, Equatable)
pub enum StatusCode: u16 {
    Ok                  = 200,
    Created             = 201,
    NoContent           = 204,
    PartialContent      = 206,
    MovedPermanently    = 301,
    Found               = 302,
    SeeOther            = 303,
    NotModified         = 304,
    TemporaryRedirect   = 307,
    PermanentRedirect   = 308,
    BadRequest          = 400,
    Unauthorized        = 401,
    Forbidden           = 403,
    NotFound            = 404,
    TooManyRequests     = 429,
    InternalServerError = 500,
    BadGateway          = 502,
    ServiceUnavailable  = 503,
}

@repr(C)
@derive(Copy, Equatable)
pub struct HeaderSpan {
    pub name: Span16,
    pub value: Span16,
}

@derive(Copy, Equatable)
pub enum BodyFraming {
    None,
    ContentLength(u64),
    Chunked,
    CloseDelimited,
}

@derive(Copy, Equatable)
pub enum HttpError {
    InvalidUrl,
    UnsupportedScheme,
    HeaderTooLarge,
    TooManyHeaders,
    MalformedStatusLine,
    MalformedHeaderLine,
    ConflictingFramingHeaders,
    InvalidChunkEncoding,
    RedirectLimitExceeded,
    HttpsDowngradeBlocked,
    BodyLimitExceeded,
    TimeoutElapsed,
    Blake3Mismatch,
    Io(IoError),
    Tls(TlsError),
}

pub struct ResponseHead {
    pub status_raw: u16,
    pub reason_span: Span16,
    pub headers: [HeaderSpan; 64],
    pub header_count: u16,
    pub header_bytes_len: u16,
    pub keep_alive: bool,
    pub framing: BodyFraming,
}

impl ResponseHead {
    @no_alloc @no_panic @no_block
    pub fn header_value(&self, raw_buf: &[u8], target_name_ascii: str, /) -> str?;
}

@no_alloc @no_panic @no_block
pub fn parse_response_head(
    raw_buf: &[u8],
    method: Method,
    out_head: &out ResponseHead,
    /,
) -> bool!HttpError;

pub struct ClientConfig {
    pub connect_timeout: Duration     = Duration.from_millis(5_000),
    pub tls_timeout: Duration         = Duration.from_millis(10_000),
    pub header_read_timeout: Duration = Duration.from_millis(10_000),
    pub idle_body_timeout: Duration   = Duration.from_millis(15_000),
    pub max_redirects: u8             = DEFAULT_MAX_REDIRECTS,
    pub max_pool_conns: u8            = 8,
    pub user_agent: str               = "corex-pkg/0.0.1",
}

@linear
pub(pkg) enum ActiveConn {
    Plain(TcpStream),
    Tls(TlsClientStream),
}

@linear
pub(pkg) struct PooledConn {
    pub origin_hash: u64,
    pub idle_since_ns: u64,
    pub stream: ActiveConn,
}

@linear
pub struct Client {
    roots: CertBundle,
    config: ClientConfig,
    pool_slots: [PooledConn?; 8],
}

@linear
pub struct Response {
    pub status: u16,
    head: ResponseHead,
    head_buf: [u8; 16_384],
    body_preread_off: u16,
    body_preread_end: u16,
    remaining_len: u64,
    chunk_state: u8,
    conn: ActiveConn,
}

impl Response {
    @inline @no_alloc @no_panic @no_block
    pub fn header(&self, name: str, /) -> str? =
        self.head.header_value(self.head_buf[..self.head.header_bytes_len as usize], name);

    pub async fn read_body_chunk(&mut self, dst: &mut [u8], /) -> usize!HttpError;
    pub async fn read_body_bounded(own self, arena: &mut Arena, max_bytes: usize, /) -> &[u8]!HttpError;
    pub async fn finish_into_pool(own self, client: &mut Client, /);
    pub fn close(own self);
}

impl Client {
    pub fn init(config: ClientConfig = ClientConfig { .. }, /) -> Self!IoError;

    pub async fn request(
        &mut self,
        method: Method,
        url: str,
        /,
        *,
        extra_headers: &[(str, str)] = &[],
        body: &[u8] = &[],
    ) -> Response!HttpError;

    pub async fn fetch_blake3_verified[W: Writer](
        &mut self,
        url: str,
        expected_blake3: &Digest256,
        out_sink: &mut W,
        /,
        *,
        max_bytes: u64 = 268_435_456,
    ) -> u64!HttpError;

    pub fn close(own self);
}
```

---

## 3. Deliverable 2: Concrete Reference Implementations

### 3.1 Vectorized `blake3` (`Simd[u32, 4]` & `Simd[u32, 8]`) and Iterative `BaoVerifier`

The `.cx` implementation below keeps `.rodata` to 48 bytes (`IV` + `MSG_PERM`), uses `Simd[u32, 4]` row-diagonalization for single blocks and parent nodes, uses 8-way transposed `Simd[u32, 8]` for multi-chunk inputs (`≥8 KiB`), and implements the iterative 54-entry `BaoVerifier`:

```rust
// File: stdlib/cx/crypto/blake3_impl.cx
mod blake3_impl;

use cx.crypto.{CryptoError, Digest256, constant_time_eq};
use cx.simd.Simd;

const IV: [u32; 8] = [
    0x6A09_E667_u32, 0xBB67_AE85_u32, 0x3C6E_F372_u32, 0xA54F_F53A_u32,
    0x510E_527F_u32, 0x9B05_688C_u32, 0x1F83_D9AB_u32, 0x5BE0_CD19_u32,
];

const MSG_PERM: [u8; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

const CHUNK_START: u32 = 1 << 0;
const CHUNK_END:   u32 = 1 << 1;
const PARENT:      u32 = 1 << 2;
const ROOT:        u32 = 1 << 3;

@inline @no_alloc @no_panic @no_block
fn rotr_v4(v: Simd[u32, 4], comptime bits: u32, /) -> Simd[u32, 4] =
    (v >> Simd[u32, 4].splat(bits)) | (v << Simd[u32, 4].splat(32 - bits));

@inline @no_alloc @no_panic @no_block
fn g_v4(
    r0: &mut Simd[u32, 4],
    r1: &mut Simd[u32, 4],
    r2: &mut Simd[u32, 4],
    r3: &mut Simd[u32, 4],
    mx: Simd[u32, 4],
    my: Simd[u32, 4],
    /,
) {
    r0.* = r0.* +% r1.* +% mx;
    r3.* = rotr_v4(r3.* ^ r0.*, 16);
    r2.* = r2.* +% r3.*;
    r1.* = rotr_v4(r1.* ^ r2.*, 12);
    r0.* = r0.* +% r1.* +% my;
    r3.* = rotr_v4(r3.* ^ r0.*, 8);
    r2.* = r2.* +% r3.*;
    r1.* = rotr_v4(r1.* ^ r2.*, 7);
}

@no_alloc @no_panic @no_block
pub fn compress_cv_v4(
    cv: &[u32; 8],
    block_words: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
    /,
) -> [u32; 8] {
    var r0 = Simd[u32, 4].from_array([cv[0], cv[1], cv[2], cv[3]]);
    var r1 = Simd[u32, 4].from_array([cv[4], cv[5], cv[6], cv[7]]);
    var r2 = Simd[u32, 4].from_array([IV[0], IV[1], IV[2], IV[3]]);
    var r3 = Simd[u32, 4].from_array([
        (counter & 0xFFFF_FFFF_u64) as u32,
        (counter >> 32) as u32,
        block_len,
        flags,
    ]);

    var m = block_words.*;
    for round in 0..7 {
        g_v4(
            &mut r0, &mut r1, &mut r2, &mut r3,
            Simd[u32, 4].from_array([m[0], m[2], m[4], m[6]]),
            Simd[u32, 4].from_array([m[1], m[3], m[5], m[7]]),
        );
        r1 = r1.shuffle([1, 2, 3, 0]);
        r2 = r2.shuffle([2, 3, 0, 1]);
        r3 = r3.shuffle([3, 0, 1, 2]);

        g_v4(
            &mut r0, &mut r1, &mut r2, &mut r3,
            Simd[u32, 4].from_array([m[8], m[10], m[12], m[14]]),
            Simd[u32, 4].from_array([m[9], m[11], m[13], m[15]]),
        );
        r1 = r1.shuffle([3, 0, 1, 2]);
        r2 = r2.shuffle([2, 3, 0, 1]);
        r3 = r3.shuffle([1, 2, 3, 0]);

        if round < 6 {
            var next_m: [u32; 16] = [0; 16];
            for i in 0..16 {
                next_m[i] = m[MSG_PERM[i] as usize];
            }
            m = next_m;
        }
    }

    let lo = (r0 ^ r2).to_array();
    let hi = (r1 ^ r3).to_array();
    [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
}

@no_alloc @no_panic @no_block
pub fn hash_8_chunks_simd(
    chunks: &[u8; 8192],
    key_words: &[u32; 8],
    base_counter: u64,
    base_flags: u32,
    out_cvs: &out [Digest256; 8],
    /,
) {
    var cv: [Simd[u32, 8]; 8] = [Simd[u32, 8].splat(0); 8];
    for w in 0..8 {
        cv[w] = Simd[u32, 8].splat(key_words[w]);
    }
    var ctr_lo_arr: [u32; 8] = [0; 8];
    var ctr_hi_arr: [u32; 8] = [0; 8];
    for lane in 0..8 {
        let c = base_counter +% (lane as u64);
        ctr_lo_arr[lane] = (c & 0xFFFF_FFFF_u64) as u32;
        ctr_hi_arr[lane] = (c >> 32) as u32;
    }
    let ctr_lo = Simd[u32, 8].from_array(ctr_lo_arr);
    let ctr_hi = Simd[u32, 8].from_array(ctr_hi_arr);

    for blk in 0..16 {
        var m: [Simd[u32, 8]; 16] = [Simd[u32, 8].splat(0); 16];
        for w in 0..16 {
            var lanes: [u32; 8] = [0; 8];
            for lane in 0..8 {
                let off = lane * 1024 + blk * 64 + w * 4;
                lanes[lane] = u32.from_le_bytes(chunks[off..off + 4]);
            }
            m[w] = Simd[u32, 8].from_array(lanes);
        }

        let b_flags = base_flags
            | (if blk == 0 { CHUNK_START } else { 0 })
            | (if blk == 15 { CHUNK_END } else { 0 });

        var s: [Simd[u32, 8]; 16] = [
            cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
            Simd[u32, 8].splat(IV[0]), Simd[u32, 8].splat(IV[1]),
            Simd[u32, 8].splat(IV[2]), Simd[u32, 8].splat(IV[3]),
            ctr_lo, ctr_hi,
            Simd[u32, 8].splat(64), Simd[u32, 8].splat(b_flags),
        ];

        for r in 0..7 {
            inline_round_8x(&mut s, &m);
            if r < 6 {
                var next_m: [Simd[u32, 8]; 16] = [Simd[u32, 8].splat(0); 16];
                for i in 0..16 {
                    next_m[i] = m[MSG_PERM[i] as usize];
                }
                m = next_m;
            }
        }
        for i in 0..8 {
            cv[i] = s[i] ^ s[i + 8];
        }
    }

    var tmp_cvs: [Digest256; 8] = [[0; 32]; 8];
    for w in 0..8 {
        let arr = cv[w].to_array();
        for lane in 0..8 {
            let bytes = arr[lane].to_le_bytes();
            tmp_cvs[lane][w * 4 + 0] = bytes[0];
            tmp_cvs[lane][w * 4 + 1] = bytes[1];
            tmp_cvs[lane][w * 4 + 2] = bytes[2];
            tmp_cvs[lane][w * 4 + 3] = bytes[3];
        }
    }
    out_cvs.* = tmp_cvs;
}

@inline @no_alloc @no_panic @no_block
fn g_8x(s: &mut [Simd[u32, 8]; 16], a: usize, b: usize, c: usize, d: usize, mx: Simd[u32, 8], my: Simd[u32, 8], /) {
    s[a] = s[a] +% s[b] +% mx;
    s[d] = ((s[d] ^ s[a]) >> Simd[u32, 8].splat(16)) | ((s[d] ^ s[a]) << Simd[u32, 8].splat(16));
    s[c] = s[c] +% s[d];
    s[b] = ((s[b] ^ s[c]) >> Simd[u32, 8].splat(12)) | ((s[b] ^ s[c]) << Simd[u32, 8].splat(20));
    s[a] = s[a] +% s[b] +% my;
    s[d] = ((s[d] ^ s[a]) >> Simd[u32, 8].splat(8)) | ((s[d] ^ s[a]) << Simd[u32, 8].splat(24));
    s[c] = s[c] +% s[d];
    s[b] = ((s[b] ^ s[c]) >> Simd[u32, 8].splat(7)) | ((s[b] ^ s[c]) << Simd[u32, 8].splat(25));
}

@inline @no_alloc @no_panic @no_block
fn inline_round_8x(s: &mut [Simd[u32, 8]; 16], m: &[Simd[u32, 8]; 16], /) {
    g_8x(s, 0, 4,  8, 12, m[0],  m[1]);
    g_8x(s, 1, 5,  9, 13, m[2],  m[3]);
    g_8x(s, 2, 6, 10, 14, m[4],  m[5]);
    g_8x(s, 3, 7, 11, 15, m[6],  m[7]);
    g_8x(s, 0, 5, 10, 15, m[8],  m[9]);
    g_8x(s, 1, 6, 11, 12, m[10], m[11]);
    g_8x(s, 2, 7,  8, 13, m[12], m[13]);
    g_8x(s, 3, 4,  9, 14, m[14], m[15]);
}

@no_alloc @no_panic @no_block
fn count_preorder_parents(chunk_idx: u64, total_chunks: u64, /) -> usize {
    var count: usize = 0;
    var rem: u64 = total_chunks;
    var rel: u64 = chunk_idx;
    while rem > 1 {
        let shift: u64 = 63 - ((rem - 1).leading_zeros() as u64);
        let k: u64 = 1_u64 << shift;
        if rel == 0 {
            count += 1;
        }
        if rel < k {
            rem = k;
        } else {
            rel -= k;
            rem -= k;
        }
    }
    count
}

@no_alloc @no_panic @no_block
fn words_to_digest(words: &[u32; 8], /) -> Digest256 {
    var out: Digest256 = [0; 32];
    for i in 0..8 {
        let b = words[i].to_le_bytes();
        out[i * 4 + 0] = b[0];
        out[i * 4 + 1] = b[1];
        out[i * 4 + 2] = b[2];
        out[i * 4 + 3] = b[3];
    }
    out
}

@no_alloc @no_panic @no_block
fn compute_parent_cv(node64: &[u8; 64], is_root: bool, /) -> Digest256 {
    var words: [u32; 16] = [0; 16];
    for i in 0..16 {
        words[i] = u32.from_le_bytes(node64[i * 4..i * 4 + 4]);
    }
    let flags = PARENT | (if is_root { ROOT } else { 0 });
    let cv = compress_cv_v4(&IV, &words, 0, 64, flags);
    words_to_digest(&cv)
}

@no_alloc @no_panic @no_block
fn compute_chunk_cv(chunk: &[u8], chunk_idx: u64, is_single_root: bool, /) -> Digest256 {
    var cv = IV;
    let total_blocks = if chunk.is_empty() { 1_usize } else { (chunk.len() + 63) / 64 };
    for blk_i in 0..total_blocks {
        let start = blk_i * 64;
        let rem = chunk.len() - start;
        let take = if rem > 64 { 64 } else { rem };
        var padded: [u8; 64] = [0; 64];
        for j in 0..take {
            padded[j] = chunk[start + j];
        }
        var words: [u32; 16] = [0; 16];
        for w in 0..16 {
            words[w] = u32.from_le_bytes(padded[w * 4..w * 4 + 4]);
        }
        let is_last = blk_i + 1 == total_blocks;
        let flags = (if blk_i == 0 { CHUNK_START } else { 0 })
            | (if is_last { CHUNK_END } else { 0 })
            | (if is_single_root and is_last { ROOT } else { 0 });
        cv = compress_cv_v4(&cv, &words, chunk_idx, take as u32, flags);
    }
    words_to_digest(&cv)
}

@no_alloc @no_panic @no_block
pub fn verify_bao_chunk_step(
    state: &mut cx.crypto.blake3.BaoVerifier,
    parent_nodes_obao: &[u8],
    chunk_data: &[u8],
    /,
) -> usize!CryptoError {
    if not state.header_parsed or state.finalized_ok {
        return .Err(.BaoHeaderTruncated);
    }
    let c = state.next_chunk_idx;
    let parents_needed = count_preorder_parents(c, state.total_chunks);
    if parent_nodes_obao.len() != parents_needed * 64 {
        return .Err(.BaoHeaderTruncated);
    }

    for p_i in 0..parents_needed {
        let base = p_i * 64;
        for k in 0..64 {
            state.scratch_node[k] = parent_nodes_obao[base + k];
        }
        let is_root_parent = c == 0 and p_i == 0;
        let expected_cv = if is_root_parent {
            state.expected_root
        } else {
            if state.cv_stack_len == 0 { return .Err(.BaoHashMismatch); }
            state.cv_stack_len -= 1;
            state.cv_stack[state.cv_stack_len as usize]
        };

        let actual_parent = compute_parent_cv(&state.scratch_node, is_root_parent);
        if not constant_time_eq(&actual_parent, &expected_cv) {
            return .Err(.BaoHashMismatch);
        }
        if (state.cv_stack_len as usize) + 2 > 54 {
            return .Err(.BaoHeaderTruncated);
        }
        var left_cv: Digest256 = [0; 32];
        var right_cv: Digest256 = [0; 32];
        for k in 0..32 {
            left_cv[k] = state.scratch_node[k];
            right_cv[k] = state.scratch_node[32 + k];
        }
        state.cv_stack[state.cv_stack_len as usize] = right_cv;
        state.cv_stack_len += 1;
        state.cv_stack[state.cv_stack_len as usize] = left_cv;
        state.cv_stack_len += 1;
    }

    let expected_chunk_len: usize = if c + 1 < state.total_chunks {
        1024
    } else {
        (state.claimed_len - c * 1024) as usize
    };
    if chunk_data.len() != expected_chunk_len {
        return .Err(.BaoLengthMismatch);
    }

    let is_single_root = state.total_chunks == 1;
    let expected_chunk_cv = if is_single_root {
        state.expected_root
    } else {
        if state.cv_stack_len == 0 { return .Err(.BaoHashMismatch); }
        state.cv_stack_len -= 1;
        state.cv_stack[state.cv_stack_len as usize]
    };

    let actual_chunk_cv = compute_chunk_cv(chunk_data, c, is_single_root);
    if not constant_time_eq(&actual_chunk_cv, &expected_chunk_cv) {
        return .Err(.BaoHashMismatch);
    }

    state.next_chunk_idx += 1;
    if state.next_chunk_idx == state.total_chunks {
        if state.cv_stack_len != 0 { return .Err(.BaoHashMismatch); }
        state.finalized_ok = true;
    }
    .Ok(chunk_data.len())
}
```

---

### 3.2 Strict Constant-Time `ed25519_verify` and Iterative RFC 6962 / 9162 Merkle Verifiers

The reference implementation below enforces strict FIPS 186-5 / RFC 8032 §5.1.7 verification ($S < L$, $y < p$, no negative zero, $[8]A \neq \mathcal{O}$ 8-torsion rejection, and canonical $R$ byte equality) alongside the $O(1)$-space RFC 9162 Merkle inclusion and consistency verifiers:

```zig
//! Reference Implementation: Strict Constant-Time Ed25519 Verifier & RFC 6962/9162 Merkle Proofs
//! Maps 1-to-1 to `stdlib/cx/crypto/{ed25519,merkle}.cx` (zero heap allocations).

const std = @import("std");
const Sha512 = std.crypto.hash.sha2.Sha512;
const Sha256 = std.crypto.hash.sha2.Sha256;

pub const VerifyError = error{
    InvalidSignature,
    InvalidPublicKey,
    MerkleProofInvalid,
};

const Fe25519 = [5]u64;
const MASK51: u64 = (1 << 51) - 1;

const FE_ZERO = Fe25519{ 0, 0, 0, 0, 0 };
const FE_ONE  = Fe25519{ 1, 0, 0, 0, 0 };
const FE_D = Fe25519{
    0x0003_4DCA_1359_78A3, 0x0001_A828_3B15_6EBD, 0x0005_E7A2_6001_C029,
    0x0007_39C6_63A0_3CBB, 0x0005_2036_CEE2_B6FF,
};
const FE_SQRT_M1 = Fe25519{
    0x0006_1B27_4A0E_A0B0, 0x0000_D5A5_FC8F_189D, 0x0007_EF5E_9CBD_0C60,
    0x0007_8595_A680_4C9E, 0x0002_B832_4804_FC1D,
};

/// RFC 8032 canonical compressed base point B (y = 4/5 mod p, even x): 0x58 || (0x66 * 31)
const BASE_POINT_BYTES: [32]u8 = .{0x58} ++ (.{0x66} ** 31);

const ExtPoint = struct {
    X: Fe25519,
    Y: Fe25519,
    Z: Fe25519,
    T: Fe25519,

    const IDENTITY = ExtPoint{ .X = FE_ZERO, .Y = FE_ONE, .Z = FE_ONE, .T = FE_ZERO };
};

inline fn ctSelectU64(choice: u64, a: u64, b: u64) u64 {
    const mask = -%choice;
    return a ^ (mask & (a ^ b));
}

fn feSelect(choice: u64, a: Fe25519, b: Fe25519) Fe25519 {
    var out: Fe25519 = undefined;
    for (0..5) |i| out[i] = ctSelectU64(choice, a[i], b[i]);
    return out;
}

fn ptSelect(choice: u64, a: ExtPoint, b: ExtPoint) ExtPoint {
    return .{
        .X = feSelect(choice, a.X, b.X),
        .Y = feSelect(choice, a.Y, b.Y),
        .Z = feSelect(choice, a.Z, b.Z),
        .T = feSelect(choice, a.T, b.T),
    };
}

fn feCarry(v: Fe25519) Fe25519 {
    var t = v;
    var c0 = t[0] >> 51; t[0] &= MASK51; t[1] += c0;
    const c1 = t[1] >> 51; t[1] &= MASK51; t[2] += c1;
    const c2 = t[2] >> 51; t[2] &= MASK51; t[3] += c2;
    const c3 = t[3] >> 51; t[3] &= MASK51; t[4] += c3;
    const c4 = t[4] >> 51; t[4] &= MASK51; t[0] += c4 * 19;
    c0 = t[0] >> 51; t[0] &= MASK51; t[1] += c0;
    return t;
}

fn feAdd(a: Fe25519, b: Fe25519) Fe25519 {
    var out: Fe25519 = undefined;
    for (0..5) |i| out[i] = a[i] + b[i];
    return feCarry(out);
}

fn feSub(a: Fe25519, b: Fe25519) Fe25519 {
    const bias = Fe25519{
        0x000F_FFFF_FFFF_FFDA, 0x000F_FFFF_FFFF_FFFE, 0x000F_FFFF_FFFF_FFFE,
        0x000F_FFFF_FFFF_FFFE, 0x000F_FFFF_FFFF_FFFE,
    };
    var out: Fe25519 = undefined;
    for (0..5) |i| out[i] = (a[i] + bias[i]) - b[i];
    return feCarry(out);
}

fn feNeg(a: Fe25519) Fe25519 {
    return feSub(FE_ZERO, a);
}

fn feMul(a: Fe25519, b: Fe25519) Fe25519 {
    const b1_19 = @as(u128, b[1]) * 19;
    const b2_19 = @as(u128, b[2]) * 19;
    const b3_19 = @as(u128, b[3]) * 19;
    const b4_19 = @as(u128, b[4]) * 19;

    var r0 = @as(u128, a[0]) * b[0] + @as(u128, a[1]) * b4_19 + @as(u128, a[2]) * b3_19 + @as(u128, a[3]) * b2_19 + @as(u128, a[4]) * b1_19;
    var r1 = @as(u128, a[0]) * b[1] + @as(u128, a[1]) * b[0] + @as(u128, a[2]) * b4_19 + @as(u128, a[3]) * b3_19 + @as(u128, a[4]) * b2_19;
    var r2 = @as(u128, a[0]) * b[2] + @as(u128, a[1]) * b[1] + @as(u128, a[2]) * b[0] + @as(u128, a[3]) * b4_19 + @as(u128, a[4]) * b3_19;
    var r3 = @as(u128, a[0]) * b[3] + @as(u128, a[1]) * b[2] + @as(u128, a[2]) * b[1] + @as(u128, a[3]) * b[0] + @as(u128, a[4]) * b4_19;
    var r4 = @as(u128, a[0]) * b[4] + @as(u128, a[1]) * b[3] + @as(u128, a[2]) * b[2] + @as(u128, a[3]) * b[1] + @as(u128, a[4]) * b[0];

    r1 += r0 >> 51; var o0: u64 = @as(u64, @truncate(r0)) & MASK51;
    r2 += r1 >> 51; var o1: u64 = @as(u64, @truncate(r1)) & MASK51;
    r3 += r2 >> 51; const o2: u64 = @as(u64, @truncate(r2)) & MASK51;
    r4 += r3 >> 51; const o3: u64 = @as(u64, @truncate(r3)) & MASK51;
    const c4: u64 = @intCast(r4 >> 51); const o4: u64 = @as(u64, @truncate(r4)) & MASK51;

    o0 += c4 * 19;
    o1 += o0 >> 51;
    o0 &= MASK51;
    return Fe25519{ o0, o1, o2, o3, o4 };
}

fn feSqr(a: Fe25519) Fe25519 {
    return feMul(a, a);
}

fn feToBytes(a: Fe25519) [32]u8 {
    var t = feCarry(a);
    var q = (t[0] + 19) >> 51;
    q = (t[1] + q) >> 51;
    q = (t[2] + q) >> 51;
    q = (t[3] + q) >> 51;
    q = (t[4] + q) >> 51;
    t[0] += 19 * q;
    const c0 = t[0] >> 51; t[0] &= MASK51; t[1] += c0;
    const c1 = t[1] >> 51; t[1] &= MASK51; t[2] += c1;
    const c2 = t[2] >> 51; t[2] &= MASK51; t[3] += c2;
    const c3 = t[3] >> 51; t[3] &= MASK51; t[4] = (t[4] + c3) & MASK51;

    var out: [32]u8 = undefined;
    std.mem.writeInt(u64, out[0..8],   t[0] | (t[1] << 51), .little);
    std.mem.writeInt(u64, out[8..16],  (t[1] >> 13) | (t[2] << 38), .little);
    std.mem.writeInt(u64, out[16..24], (t[2] >> 26) | (t[3] << 25), .little);
    std.mem.writeInt(u64, out[24..32], (t[3] >> 39) | (t[4] << 12), .little);
    return out;
}

fn fePow22523(z: Fe25519) Fe25519 {
    var t0 = feSqr(z);
    var t1 = feSqr(feSqr(t0));
    t1 = feMul(z, t1);
    t0 = feMul(t0, t1);
    t0 = feSqr(t0);
    t0 = feMul(t1, t0);
    t1 = feSqr(t0);
    for (1..5) |_| t1 = feSqr(t1);
    t0 = feMul(t1, t0);
    t1 = feSqr(t0);
    for (1..10) |_| t1 = feSqr(t1);
    t1 = feMul(t1, t0);
    var t2 = feSqr(t1);
    for (1..20) |_| t2 = feSqr(t2);
    t1 = feMul(t2, t1);
    t1 = feSqr(t1);
    for (1..10) |_| t1 = feSqr(t1);
    t0 = feMul(t1, t0);
    t1 = feSqr(t0);
    for (1..50) |_| t1 = feSqr(t1);
    t1 = feMul(t1, t0);
    t2 = feSqr(t1);
    for (1..100) |_| t2 = feSqr(t2);
    t1 = feMul(t2, t1);
    t1 = feSqr(t1);
    for (1..50) |_| t1 = feSqr(t1);
    t0 = feMul(t1, t0);
    t0 = feSqr(feSqr(t0));
    return feMul(t0, z);
}

fn feInvert(z: Fe25519) Fe25519 {
    const p2523 = fePow22523(z);
    const z8 = feSqr(feSqr(feSqr(p2523)));
    return feMul(z8, feMul(feSqr(z), z));
}

fn ctBytesEq(a: *const [32]u8, b: *const [32]u8) bool {
    var diff: u8 = 0;
    for (0..32) |i| diff |= a[i] ^ b[i];
    return diff == 0;
}

fn decodePointStrict(bytes: *const [32]u8) !ExtPoint {
    var y_clean = bytes.*;
    const x_sign: u8 = y_clean[31] >> 7;
    y_clean[31] &= 0x7F;

    const l0 = std.mem.readInt(u64, y_clean[0..8], .little);
    const l1 = std.mem.readInt(u64, y_clean[6..14], .little) >> 3;
    const l2 = std.mem.readInt(u64, y_clean[12..20], .little) >> 6;
    const l3 = std.mem.readInt(u64, y_clean[19..27], .little) >> 1;
    const l4 = std.mem.readInt(u64, y_clean[24..32], .little) >> 12;
    const y = Fe25519{ l0 & MASK51, l1 & MASK51, l2 & MASK51, l3 & MASK51, l4 & MASK51 };

    const y_canonical = feToBytes(y);
    if (!ctBytesEq(&y_canonical, &y_clean)) return error.InvalidPublicKey;

    const y2 = feSqr(y);
    const u = feSub(y2, FE_ONE);
    const v = feAdd(feMul(y2, FE_D), FE_ONE);
    const v3 = feMul(feSqr(v), v);
    const v7 = feMul(feSqr(v3), v);
    var x = feMul(feMul(u, v3), fePow22523(feMul(u, v7)));

    const vx2 = feMul(v, feSqr(x));
    const check_pos = feToBytes(feSub(vx2, u));
    const check_neg = feToBytes(feAdd(vx2, u));
    const zero_bytes = [_]u8{0} ** 32;

    const is_pos = ctBytesEq(&check_pos, &zero_bytes);
    const is_neg = ctBytesEq(&check_neg, &zero_bytes);
    if (!is_pos and !is_neg) return error.InvalidPublicKey;

    x = feSelect(@intFromBool(is_neg), x, feMul(x, FE_SQRT_M1));
    const x_bytes = feToBytes(x);
    if (ctBytesEq(&x_bytes, &zero_bytes) and x_sign == 1) {
        return error.InvalidPublicKey;
    }
    const need_neg: u64 = @intFromBool((x_bytes[0] & 1) != x_sign);
    x = feSelect(need_neg, x, feNeg(x));
    return ExtPoint{ .X = x, .Y = y, .Z = FE_ONE, .T = feMul(x, y) };
}

fn pointAdd(P: ExtPoint, Q: ExtPoint) ExtPoint {
    const fe_2d = feAdd(FE_D, FE_D);
    const A = feMul(feSub(P.Y, P.X), feSub(Q.Y, Q.X));
    const B = feMul(feAdd(P.Y, P.X), feAdd(Q.Y, Q.X));
    const C = feMul(fe_2d, feMul(P.T, Q.T));
    const D = feAdd(feMul(P.Z, Q.Z), feMul(P.Z, Q.Z));
    const E = feSub(B, A);
    const F = feSub(D, C);
    const G = feAdd(D, C);
    const H = feAdd(B, A);
    return .{ .X = feMul(E, F), .Y = feMul(G, H), .Z = feMul(F, G), .T = feMul(E, H) };
}

fn scalarMulCt(scalar: *const [32]u8, P: ExtPoint) ExtPoint {
    var table: [16]ExtPoint = undefined;
    table[0] = ExtPoint.IDENTITY;
    table[1] = P;
    for (2..16) |i| table[i] = pointAdd(table[i - 1], P);

    var acc = ExtPoint.IDENTITY;
    var idx: usize = 64;
    while (idx > 0) {
        idx -= 1;
        for (0..4) |_| acc = pointAdd(acc, acc);
        const byte = scalar[idx / 2];
        const nibble: u8 = if ((idx & 1) == 1) (byte >> 4) else (byte & 0x0F);
        var chosen = ExtPoint.IDENTITY;
        for (0..16) |k| {
            const eq: u64 = @intFromBool(nibble == @as(u8, @intCast(k)));
            chosen = ptSelect(eq, chosen, table[k]);
        }
        acc = pointAdd(acc, chosen);
    }
    return acc;
}

fn encodePoint(P: ExtPoint) [32]u8 {
    const z_inv = feInvert(P.Z);
    const x = feToBytes(feMul(P.X, z_inv));
    var y = feToBytes(feMul(P.Y, z_inv));
    y[31] |= (x[0] & 1) << 7;
    return y;
}

fn isSmallOrderTorsion(P: ExtPoint) bool {
    const P2 = pointAdd(P, P);
    const P4 = pointAdd(P2, P2);
    const P8 = pointAdd(P4, P4);
    const zero_bytes = [_]u8{0} ** 32;
    const x8 = feToBytes(P8.X);
    const y_sub_z = feToBytes(feSub(P8.Y, P8.Z));
    return ctBytesEq(&x8, &zero_bytes) and ctBytesEq(&y_sub_z, &zero_bytes);
}

pub fn ed25519VerifyStrict(
    pk: *const [32]u8,
    msg: []const u8,
    sig: *const [64]u8,
) VerifyError!void {
    const r_bytes = sig[0..32];
    const s_bytes = sig[32..64];

    const L_U256: u256 = (@as(u256, 1) << 252) + 27742317777372353535851937790883648493;
    const s_val = std.mem.readInt(u256, s_bytes, .little);
    if (s_val >= L_U256) return error.InvalidSignature;

    const A = decodePointStrict(pk) catch return error.InvalidPublicKey;
    if (isSmallOrderTorsion(A)) return error.InvalidPublicKey;
    _ = decodePointStrict(r_bytes) catch return error.InvalidSignature;

    var h = Sha512.init(.{});
    h.update(r_bytes);
    h.update(pk);
    h.update(msg);
    var digest: [64]u8 = undefined;
    h.final(&digest);
    const k_val: u256 = @intCast(std.mem.readInt(u512, &digest, .little) % @as(u512, L_U256));
    var k_bytes: [32]u8 = undefined;
    std.mem.writeInt(u256, &k_bytes, k_val, .little);

    const B = decodePointStrict(&BASE_POINT_BYTES) catch unreachable;
    const neg_A = ExtPoint{ .X = feNeg(A.X), .Y = A.Y, .Z = A.Z, .T = feNeg(A.T) };
    const R_calc = pointAdd(scalarMulCt(s_bytes, B), scalarMulCt(&k_bytes, neg_A));
    const r_calc_bytes = encodePoint(R_calc);
    if (!ctBytesEq(&r_calc_bytes, r_bytes)) return error.InvalidSignature;
}

fn merkleNodeHash(left: *const [32]u8, right: *const [32]u8) [32]u8 {
    var h = Sha256.init(.{});
    h.update(&[_]u8{0x01});
    h.update(left);
    h.update(right);
    var out: [32]u8 = undefined;
    h.final(&out);
    return out;
}

pub fn verifyMerkleInclusion(
    leaf_idx: u64,
    tree_size: u64,
    leaf_hash: *const [32]u8,
    proof: []const [32]u8,
    expected_root: *const [32]u8,
) VerifyError!void {
    if (tree_size == 0 or leaf_idx >= tree_size) return error.MerkleProofInvalid;
    var fn_idx = leaf_idx;
    var sn_idx = tree_size - 1;
    var r = leaf_hash.*;

    for (proof) |p| {
        if (sn_idx == 0) return error.MerkleProofInvalid;
        if ((fn_idx & 1) == 1 or fn_idx == sn_idx) {
            r = merkleNodeHash(&p, &r);
            while ((fn_idx & 1) == 0) {
                fn_idx >>= 1;
                sn_idx >>= 1;
            }
        } else {
            r = merkleNodeHash(&r, &p);
        }
        fn_idx >>= 1;
        sn_idx >>= 1;
    }
    if (sn_idx != 0 or !ctBytesEq(&r, expected_root)) return error.MerkleProofInvalid;
}

pub fn verifyMerkleConsistency(
    first: u64,
    second: u64,
    first_root: *const [32]u8,
    second_root: *const [32]u8,
    proof: []const [32]u8,
) VerifyError!void {
    if (first > second) return error.MerkleProofInvalid;
    if (first == 0) {
        var empty_root: [32]u8 = undefined;
        Sha256.hash("", &empty_root, .{});
        if (proof.len == 0 and ctBytesEq(first_root, &empty_root)) return;
        return error.MerkleProofInvalid;
    }
    if (first == second) {
        if (proof.len == 0 and ctBytesEq(first_root, second_root)) return;
        return error.MerkleProofInvalid;
    }
    if (proof.len == 0) return error.MerkleProofInvalid;

    const is_pow2 = (first & (first - 1)) == 0;
    var idx: usize = 0;
    var fr: [32]u8 = if (is_pow2) first_root.* else proof[0];
    var sr: [32]u8 = fr;
    if (!is_pow2) idx = 1;

    var fn_idx = first - 1;
    var sn_idx = second - 1;
    while ((fn_idx & 1) == 1) {
        fn_idx >>= 1;
        sn_idx >>= 1;
    }
    for (proof[idx..]) |p| {
        if (sn_idx == 0) return error.MerkleProofInvalid;
        if ((fn_idx & 1) == 1 or fn_idx == sn_idx) {
            fr = merkleNodeHash(&p, &fr);
            sr = merkleNodeHash(&p, &sr);
            while ((fn_idx & 1) == 0) {
                fn_idx >>= 1;
                sn_idx >>= 1;
            }
        } else {
            sr = merkleNodeHash(&sr, &p);
        }
        fn_idx >>= 1;
        sn_idx >>= 1;
    }
    if (sn_idx != 0 or !ctBytesEq(&fr, first_root) or !ctBytesEq(&sr, second_root)) {
        return error.MerkleProofInvalid;
    }
}
```

---

### 3.3 Cross-OS 4-Byte `Mutex` (`futex` / `__ulock_wait` / `WaitOnAddress` / `wasm32`)

```rust
// File: stdlib/cx/sync/mutex_futex.cx
mod mutex_futex;

use core.atomic.{AtomicU32, MemoryOrder};
use cx.time.Duration;

@cfg(target.os == .Linux)
const FUTEX_WAIT_PRIVATE: i32 = 128;
@cfg(target.os == .Linux)
const FUTEX_WAKE_PRIVATE: i32 = 129;

@cfg(target.os == .Macos)
const UL_COMPARE_AND_WAIT: u32            = 1;
@cfg(target.os == .Macos)
const ULF_WAKE_ALL: u32                   = 0x0000_0100_u32;
@cfg(target.os == .Macos)
const ULF_WAIT_WORKQ_DATA_CONTENTION: u32 = 0x0001_0000_u32;
@cfg(target.os == .Macos)
const ULF_NO_ERRNO: u32                   = 0x0100_0000_u32;

@cfg(target.os == .Macos)
extern "C" {
    fn __ulock_wait(op: u32, addr: *opaque, value: u64, timeout_us: u32) -> i32;
    fn __ulock_wait2(op: u32, addr: *opaque, value: u64, timeout_ns: u64, value2: u64) -> i32;
    fn __ulock_wake(op: u32, addr: *opaque, wake_value: u64) -> i32;
}

@cfg(target.os == .Windows)
extern "C" {
    fn WaitOnAddress(addr: *opaque, cmp_addr: *opaque, addr_size: usize, timeout_ms: u32) -> i32;
    fn WakeByAddressSingle(addr: *opaque);
    fn WakeByAddressAll(addr: *opaque);
}

@std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
@no_alloc @no_panic
pub fn futex_wait(word: &AtomicU32, expected: u32, /, *, timeout: Duration? = .None) -> bool {
    @cfg(target.os == .Linux) {
        if timeout is .Some(dur) {
            let ts: [i64; 2] = [(dur.nanos / 1_000_000_000) as i64, (dur.nanos % 1_000_000_000) as i64];
            let rc = unsafe {
                core.sys.linux.futex(&raw word.* as *u32, FUTEX_WAIT_PRIVATE, expected, &raw ts as *opaque)
            };
            return rc != -core.sys.linux.ETIMEDOUT;
        } else {
            unsafe {
                let _ = core.sys.linux.futex(&raw word.* as *u32, FUTEX_WAIT_PRIVATE, expected, .None);
            }
            return true;
        }
    }

    @cfg(target.os == .Macos) {
        let op = UL_COMPARE_AND_WAIT | ULF_NO_ERRNO | ULF_WAIT_WORKQ_DATA_CONTENTION;
        if timeout is .Some(dur) {
            let ns = if dur.nanos == 0 { 1_u64 } else { dur.nanos };
            let rc = unsafe { __ulock_wait2(op, &raw word.* as *opaque, expected as u64, ns, 0) };
            return rc != -core.sys.macos.ETIMEDOUT;
        } else {
            unsafe { let _ = __ulock_wait(op, &raw word.* as *opaque, expected as u64, 0); }
            return true;
        }
    }

    @cfg(target.os == .Windows) {
        let cmp: u32 = expected;
        let ms: u32 = if timeout is .Some(dur) {
            let m = dur.nanos / 1_000_000;
            if m >= 0xFFFF_FFFE_u64 { 0xFFFF_FFFE_u32 } else { m as u32 }
        } else {
            0xFFFF_FFFF_u32
        };
        let ok = unsafe { WaitOnAddress(&raw word.* as *opaque, &raw cmp as *opaque, 4, ms) };
        return ok != 0;
    }

    @cfg(target.arch == .Wasm32) {
        let ns: i64 = if timeout is .Some(dur) { dur.nanos as i64 } else { -1 };
        let rc = unsafe { @wasm_memory_atomic_wait32(&raw word.* as *mut i32, expected as i32, ns) };
        return rc != 2;
    }
}

@std_cap_boundary(emits: .Pure, clears: .FfiUnsafe)
@no_alloc @no_panic @no_block
pub fn futex_wake_one(word: &AtomicU32, /) {
    @cfg(target.os == .Linux) {
        unsafe { let _ = core.sys.linux.futex(&raw word.* as *u32, FUTEX_WAKE_PRIVATE, 1, .None); }
    }
    @cfg(target.os == .Macos) {
        unsafe { let _ = __ulock_wake(UL_COMPARE_AND_WAIT | ULF_NO_ERRNO, &raw word.* as *opaque, 0); }
    }
    @cfg(target.os == .Windows) {
        unsafe { WakeByAddressSingle(&raw word.* as *opaque); }
    }
    @cfg(target.arch == .Wasm32) {
        unsafe { let _ = @wasm_memory_atomic_notify(&raw word.* as *mut i32, 1); }
    }
}

const UNLOCKED:  u32 = 0;
const LOCKED:    u32 = 1;
const CONTENDED: u32 = 2;

pub struct Mutex[T] {
    state: AtomicU32,
    value: T,
}

@linear
pub struct MutexGuard[T] {
    mutex_ptr: *mut Mutex[T],
}

impl[T] Mutex[T] {
    @inline @no_alloc @no_panic @no_block
    pub comptime fn new(val: own T, /) -> Self = Self {
        state: AtomicU32.new(UNLOCKED),
        value: own val,
    };

    @std_cap_boundary(emits: .BlockingSync, clears: .FfiUnsafe)
    @no_alloc @no_panic
    pub fn lock(&self) -> MutexGuard[T] {
        if self.state.compare_exchange(UNLOCKED, LOCKED, success: .Acquire, failure: .Relaxed) is .Ok(_) {
            return MutexGuard[T] { mutex_ptr: &raw self.* as *mut Mutex[T] };
        }
        self.lock_contended();
        MutexGuard[T] { mutex_ptr: &raw self.* as *mut Mutex[T] }
    }

    @cold @no_alloc @no_panic
    fn lock_contended(&self) {
        var spins: u32 = 0;
        while spins < 40 {
            let cur = self.state.load(.Relaxed);
            if cur == UNLOCKED {
                if self.state.compare_exchange(UNLOCKED, LOCKED, success: .Acquire, failure: .Relaxed) is .Ok(_) {
                    return;
                }
            } else if cur == CONTENDED {
                break;
            }
            @spin_loop_hint();
            spins += 1;
        }

        if self.state.swap(CONTENDED, .Acquire) == UNLOCKED {
            return;
        }
        while self.state.swap(CONTENDED, .Acquire) != UNLOCKED {
            let _ = futex_wait(&self.state, CONTENDED);
        }
    }
}

impl[T] MutexGuard[T] {
    @inline @no_alloc @no_panic @no_block
    pub fn unlock(own self) {
        let prev = unsafe { self.mutex_ptr.*.state.swap(UNLOCKED, .Release) };
        if prev == CONTENDED {
            unsafe { futex_wake_one(&self.mutex_ptr.*.state); }
        }
    }
}
```

---

### 3.4 `TaskGroup`, `InFlightOpSlot`, and `CompletionReaper` State Machine

```zig
//! Reference Implementation: `TaskGroup` Cancellation Cascade, `64B` `InFlightOpSlot`
//! Quarantine Reaper (`Fix-08B`), and `--sim` Virtual Event Wheel (`stdlib/cx/async/reactor.cx`).

const std = @import("std");
const assert = std.debug.assert;

pub const TASK_NONE: u32 = 0xFFFF_FFFF;

pub const PollAction = enum(u8) { resume_ready = 0, cancel_destroy = 1 };
pub const PollStatus = enum(u8) { pending = 0, ready_ok = 1, ready_err = 2 };

pub const SlotState = enum(u8) { free = 0, active = 1, cancelling_quarantine = 2 };
pub const ReaperAction = enum(u8) { no_resource = 0, close_socket = 1, close_fd = 2, release_iobuf = 3 };

pub const IoUserData = packed struct(u64) {
    slot_index: u32,
    generation: u24,
    op_tag: u8,
};

pub const InFlightOpSlot = extern struct {
    awaiting_task_id: u32 = TASK_NONE,
    generation: u24 = 1,
    state: SlotState = .free,
    reaper_action: ReaperAction = .no_resource,
    _pad0: [3]u8 = .{ 0, 0, 0 },
    raw_fd_or_sock: i32 = -1,
    pinned_buf_ptr: ?[*]u8 = null,
    pinned_buf_cap: u32 = 0,
    group_id: u32 = TASK_NONE,
    platform_overlapped: [4]u64 = .{ 0, 0, 0, 0 },
};

comptime {
    assert(@sizeOf(InFlightOpSlot) == 64);
}

pub const TaskGroupState = struct {
    parent_task_id: u32,
    active_children: u32 = 0,
    pin_ref_count: u32 = 0,
    cancel_requested: bool = false,
    waiting_on_drain: bool = false,
    child_ids_lifo: std.ArrayListUnmanaged(u32) = .{},
};

pub const TimerEntry = struct {
    deadline_ns: u64,
    seq_id: u64,
    slot_data: IoUserData,

    fn lessThan(_: void, a: TimerEntry, b: TimerEntry) std.math.Order {
        const cmp = std.math.order(a.deadline_ns, b.deadline_ns);
        return if (cmp != .eq) cmp else std.math.order(a.seq_id, b.seq_id);
    }
};

pub const BootstrapReactor = struct {
    is_sim_mode: bool,
    sim_now_ns: u64 = 0,
    next_timer_seq: u64 = 1,
    slots: []InFlightOpSlot,
    free_slot_head: u32 = TASK_NONE,
    groups: []TaskGroupState,
    ready_queue: std.ArrayListUnmanaged(u32) = .{},
    timers: std.PriorityQueue(TimerEntry, void, TimerEntry.lessThan),
    closeSocketFn: *const fn (i32) void,
    releaseBufFn: *const fn ([*]u8, u32) void,
    cancelKernelOpFn: *const fn (*InFlightOpSlot) bool,
    pollCoroFn: *const fn (u32, PollAction, i64) PollStatus,

    pub fn submitOp(
        self: *BootstrapReactor,
        task_id: u32,
        group_id: u32,
        fd: i32,
        op_tag: u8,
        reaper: ReaperAction,
        buf_ptr: ?[*]u8,
        buf_cap: u32,
    ) !IoUserData {
        const idx = self.allocSlot() orelse return error.OutOfOpSlots;
        var slot = &self.slots[idx];
        slot.awaiting_task_id = task_id;
        slot.state = .active;
        slot.reaper_action = reaper;
        slot.raw_fd_or_sock = fd;
        slot.pinned_buf_ptr = buf_ptr;
        slot.pinned_buf_cap = buf_cap;
        slot.group_id = group_id;
        if (group_id != TASK_NONE) {
            self.groups[group_id].pin_ref_count += 1;
        }
        return IoUserData{ .slot_index = idx, .generation = slot.generation, .op_tag = op_tag };
    }

    pub fn cancelTaskGroupLifo(self: *BootstrapReactor, group_id: u32) void {
        var grp = &self.groups[group_id];
        if (grp.cancel_requested) return;
        grp.cancel_requested = true;

        for (self.slots, 0..) |*slot, i| {
            if (slot.state == .active and slot.group_id == group_id) {
                slot.awaiting_task_id = TASK_NONE;
                if (self.cancelKernelOpFn(slot)) {
                    self.reapSlot(@intCast(i), -1);
                } else {
                    slot.state = .cancelling_quarantine;
                }
            }
        }

        var idx = grp.child_ids_lifo.items.len;
        while (idx > 0) {
            idx -= 1;
            const child_id = grp.child_ids_lifo.items[idx];
            _ = self.pollCoroFn(child_id, .cancel_destroy, -1);
            grp.active_children -|= 1;
            grp.pin_ref_count -|= 1;
        }
    }

    pub fn onCompletionEvent(self: *BootstrapReactor, udata: IoUserData, result: i64) void {
        if (udata.slot_index >= self.slots.len) return;
        const slot = &self.slots[udata.slot_index];
        if (slot.state == .free or slot.generation != udata.generation) return;

        if (slot.state == .cancelling_quarantine) {
            self.reapSlot(udata.slot_index, result);
            return;
        }

        const task_id = slot.awaiting_task_id;
        const group_id = slot.group_id;
        self.recycleSlot(udata.slot_index);
        if (group_id != TASK_NONE) {
            self.decrementGroupPin(group_id);
        }
        if (task_id != TASK_NONE) {
            const st = self.pollCoroFn(task_id, .resume_ready, result);
            if (st == .ready_err and group_id != TASK_NONE) {
                self.cancelTaskGroupLifo(group_id);
            }
        }
    }

    fn reapSlot(self: *BootstrapReactor, idx: u32, cqe_result: i64) void {
        const slot = &self.slots[idx];
        const group_id = slot.group_id;

        if (cqe_result >= 0) {
            switch (slot.reaper_action) {
                .close_socket, .close_fd => self.closeSocketFn(@intCast(cqe_result)),
                .no_resource, .release_iobuf => {},
            }
        }
        if (slot.pinned_buf_ptr) |ptr| {
            self.releaseBufFn(ptr, slot.pinned_buf_cap);
        }
        self.recycleSlot(idx);
        if (group_id != TASK_NONE) {
            self.decrementGroupPin(group_id);
        }
    }

    fn decrementGroupPin(self: *BootstrapReactor, group_id: u32) void {
        var grp = &self.groups[group_id];
        assert(grp.pin_ref_count > 0);
        grp.pin_ref_count -= 1;
        if (grp.pin_ref_count == 0 and grp.waiting_on_drain) {
            grp.waiting_on_drain = false;
            self.ready_queue.appendAssumeCapacity(grp.parent_task_id);
        }
    }

    pub fn stepSimVirtualTime(self: *BootstrapReactor) bool {
        assert(self.is_sim_mode);
        if (self.timers.removeOrNull()) |next_timer| {
            if (next_timer.deadline_ns > self.sim_now_ns) {
                self.sim_now_ns = next_timer.deadline_ns;
            }
            self.onCompletionEvent(next_timer.slot_data, 0);
            return true;
        }
        return false;
    }

    fn allocSlot(self: *BootstrapReactor) ?u32 {
        if (self.free_slot_head == TASK_NONE) return null;
        const idx = self.free_slot_head;
        self.free_slot_head = @truncate(self.slots[idx].platform_overlapped[0]);
        self.slots[idx].platform_overlapped = .{ 0, 0, 0, 0 };
        return idx;
    }

    fn recycleSlot(self: *BootstrapReactor, idx: u32) void {
        var slot = &self.slots[idx];
        slot.generation +%= 1;
        if (slot.generation == 0) slot.generation = 1;
        slot.state = .free;
        slot.awaiting_task_id = TASK_NONE;
        slot.pinned_buf_ptr = null;
        slot.platform_overlapped[0] = self.free_slot_head;
        self.free_slot_head = idx;
    }
};
```

---

### 3.5 Zero-`libssl` Pure-`.cx` TLS 1.3 Client Handshake State Machine

```rust
// File: stdlib/cx/net/tls_bootstrap.cx
mod tls_bootstrap;

use cx.col.Vec;
use cx.crypto.{
    Digest256, Tag128, aes128_gcm, chacha20_poly1305, constant_time_eq, csprng, secure_zeroize,
    sha256, x25519,
};
use cx.net.{CertBundle, TcpStream, TlsClientConfig, TlsClientStream, TlsError};

const TLS_CIPHER_AES_128_GCM_SHA256:       u16 = 0x1301_u16;
const TLS_CIPHER_CHACHA20_POLY1305_SHA256: u16 = 0x1303_u16;

const REC_CHANGE_CIPHER_SPEC: u8 = 20;
const REC_ALERT:              u8 = 21;
const REC_HANDSHAKE:          u8 = 22;
const REC_APPLICATION_DATA:   u8 = 23;

const HS_ENCRYPTED_EXTENSIONS: u8 = 8;
const HS_CERTIFICATE:          u8 = 11;
const HS_CERTIFICATE_VERIFY:   u8 = 15;
const HS_FINISHED:             u8 = 20;

@no_alloc @no_panic @no_block
fn hkdf_expand_label(
    secret: &Digest256,
    label: &[u8],
    context_hash: &[u8],
    out: &mut [u8],
    /,
) {
    var info: [u8; 96] = [0; 96];
    let out_len_u16 = out.len() as u16;
    info[0] = (out_len_u16 >> 8) as u8;
    info[1] = (out_len_u16 & 0xFF) as u8;
    let full_label_len = 6 + label.len();
    info[2] = full_label_len as u8;
    let prefix = b"tls13 ";
    for i in 0..6 { info[3 + i] = prefix[i]; }
    for i in 0..label.len() { info[9 + i] = label[i]; }
    let ctx_off = 9 + label.len();
    info[ctx_off] = context_hash.len() as u8;
    for i in 0..context_hash.len() { info[ctx_off + 1 + i] = context_hash[i]; }
    let total_info = ctx_off + 1 + context_hash.len();
    let _ = sha256.hkdf_expand(secret, info[..total_info], out) catch unreachable;
}

@no_alloc @no_panic @no_block
fn derive_secret(secret: &Digest256, label: &[u8], transcript_hash: &Digest256, /) -> Digest256 {
    var out: Digest256 = [0; 32];
    hkdf_expand_label(secret, label, transcript_hash, &mut out);
    out
}

@no_alloc @no_panic @no_block
fn build_record_nonce(base_iv: &[u8; 12], seq: u64, /) -> [u8; 12] {
    var nonce = base_iv.*;
    let seq_be = seq.to_be_bytes();
    for i in 0..8 {
        nonce[4 + i] ^= seq_be[i];
    }
    nonce
}

@no_alloc @no_panic @no_block
fn aead_open_record(
    cipher_id: u16,
    key: &[u8; 32],
    iv: &[u8; 12],
    seq: u64,
    hdr5: &[u8; 5],
    record_body: &mut [u8],
    /,
) -> (u8, usize)!TlsError {
    if record_body.len() < 17 {
        return .Err(.BadRecordMac);
    }
    let ct_len = record_body.len() - 16;
    var tag: Tag128 = [0; 16];
    for i in 0..16 {
        tag[i] = record_body[ct_len + i];
    }
    let nonce = build_record_nonce(iv, seq);
    if cipher_id == TLS_CIPHER_CHACHA20_POLY1305_SHA256 {
        chacha20_poly1305.open_in_place(key, &nonce, hdr5, &mut record_body[..ct_len], &tag)
            catch return .Err(.BadRecordMac);
    } else {
        var k16: [u8; 16] = [0; 16];
        for i in 0..16 { k16[i] = key[i]; }
        aes128_gcm.open_in_place(&k16, &nonce, hdr5, &mut record_body[..ct_len], &tag)
            catch return .Err(.BadRecordMac);
    }
    var end = ct_len;
    while end > 0 and record_body[end - 1] == 0 {
        end -= 1;
    }
    if end == 0 {
        return .Err(.UnexpectedMessage);
    }
    let inner_type = record_body[end - 1];
    .Ok((inner_type, end - 1))
}

pub async fn handshake_1rtt(
    var tcp: own TcpStream,
    server_name: str,
    config: &TlsClientConfig,
    /,
) -> TlsClientStream!TlsError {
    errdefer tcp.close();

    var eph_priv = csprng.random_array[32]() catch return .Err(.IoError);
    defer secure_zeroize(&mut eph_priv);
    let eph_pub = x25519.public_from_private(&eph_priv);
    let cli_random = csprng.random_array[32]() catch return .Err(.IoError);
    let compat_sid = csprng.random_array[32]() catch return .Err(.IoError);

    var ch_buf: [u8; 512] = [0; 512];
    let ch_len = encode_client_hello(&mut ch_buf, &cli_random, &compat_sid, server_name, &eph_pub, config.alpn_http11)?;
    tcp.write_all(ch_buf[..ch_len]).await catch return .Err(.IoError);

    var transcript = sha256.Hasher.init();
    transcript.update(ch_buf[5..ch_len]);

    var rec_hdr: [u8; 5] = [0; 5];
    var sh_buf: [u8; 4096] = [0; 4096];
    let sh_len = loop {
        tcp.read_exact(&mut rec_hdr).await catch return .Err(.IoError);
        let rlen = u16.from_be_bytes(rec_hdr[3..5]) as usize;
        if rlen > sh_buf.len() { return .Err(.RecordOverflow); }
        tcp.read_exact(&mut sh_buf[..rlen]).await catch return .Err(.IoError);
        if rec_hdr[0] == REC_CHANGE_CIPHER_SPEC { continue; }
        if rec_hdr[0] != REC_HANDSHAKE { return .Err(.UnexpectedMessage); }
        break rlen;
    };
    transcript.update(sh_buf[..sh_len]);

    let (cipher_id, srv_pub_x25519) = parse_server_hello(sh_buf[..sh_len], &compat_sid)?;
    let shared_secret = x25519.diffie_hellman(&eph_priv, &srv_pub_x25519)
        catch return .Err(.InvalidServerKeyShare);

    // RFC 8446 §7.1 Handshake Key Schedule
    let zeros32: Digest256 = [0; 32];
    let empty_hash = sha256.hash(b"");
    let early_secret = sha256.hkdf_extract(&zeros32, &zeros32);
    let derived_1 = derive_secret(&early_secret, b"derived", &empty_hash);
    let hs_secret = sha256.hkdf_extract(&derived_1, &shared_secret);

    let hello_hash = transcript.finalize();
    var c_hs_traffic = derive_secret(&hs_secret, b"c hs traffic", &hello_hash);
    var s_hs_traffic = derive_secret(&hs_secret, b"s hs traffic", &hello_hash);
    defer {
        secure_zeroize(&mut c_hs_traffic);
        secure_zeroize(&mut s_hs_traffic);
    }

    let key_len: usize = if cipher_id == TLS_CIPHER_CHACHA20_POLY1305_SHA256 { 32 } else { 16 };
    var s_hs_key: [u8; 32] = [0; 32];
    var s_hs_iv:  [u8; 12] = [0; 12];
    var c_hs_key: [u8; 32] = [0; 32];
    var c_hs_iv:  [u8; 12] = [0; 12];
    hkdf_expand_label(&s_hs_traffic, b"key", b"", &mut s_hs_key[..key_len]);
    hkdf_expand_label(&s_hs_traffic, b"iv",  b"", &mut s_hs_iv);
    hkdf_expand_label(&c_hs_traffic, b"key", b"", &mut c_hs_key[..key_len]);
    hkdf_expand_label(&c_hs_traffic, b"iv",  b"", &mut c_hs_iv);

    // Cross-record handshake reassembly (`MAX_HANDSHAKE_MSG_BYTES = 32 KiB`)
    var hs_assemble = Vec[u8].with_capacity(8192);
    var srv_hs_seq: u64 = 0;
    var leaf_spki_verified = false;
    var server_finished_ok = false;
    var cert_verify_hash: Digest256 = [0; 32];
    var leaf_cert_der = Vec[u8].new();

    var stream = TlsClientStream {
        tcp: own tcp,
        cipher_id: cipher_id,
        client_app_key: [0; 32],
        server_app_key: [0; 32],
        client_app_iv: [0; 12],
        server_app_iv: [0; 12],
        client_seq: 0,
        server_seq: 0,
        cleartext_pos: 0,
        cleartext_len: 0,
        eof_received: false,
        record_buf: [0; 16_640],
    };
    errdefer stream.close_abort();

    while not server_finished_ok {
        stream.tcp.read_exact(&mut rec_hdr).await catch return .Err(.IoError);
        let rlen = u16.from_be_bytes(rec_hdr[3..5]) as usize;
        if rlen > stream.record_buf.len() { return .Err(.RecordOverflow); }
        stream.tcp.read_exact(&mut stream.record_buf[..rlen]).await catch return .Err(.IoError);
        if rec_hdr[0] == REC_CHANGE_CIPHER_SPEC { continue; }
        if rec_hdr[0] != REC_APPLICATION_DATA { return .Err(.UnexpectedMessage); }

        let (inner_ty, pt_len) = aead_open_record(
            cipher_id, &s_hs_key, &s_hs_iv, srv_hs_seq, &rec_hdr, &mut stream.record_buf[..rlen],
        )?;
        srv_hs_seq += 1;
        if inner_ty == REC_ALERT { return .Err(.PeerAlertReceived); }
        if inner_ty != REC_HANDSHAKE { return .Err(.UnexpectedMessage); }

        if hs_assemble.len() + pt_len > 32_768 { return .Err(.HandshakeTooLarge); }
        for b in stream.record_buf[..pt_len] { hs_assemble.push(b); }

        var cursor: usize = 0;
        while hs_assemble.len() - cursor >= 4 {
            let hs_s = hs_assemble.as_slice();
            let msg_ty = hs_s[cursor];
            let msg_len = ((hs_s[cursor + 1] as usize) << 16)
                | ((hs_s[cursor + 2] as usize) << 8)
                | (hs_s[cursor + 3] as usize);
            if hs_s.len() - cursor < 4 + msg_len { break; }
            let full_msg = hs_s[cursor..cursor + 4 + msg_len];
            let body = full_msg[4..];

            match msg_ty {
                HS_ENCRYPTED_EXTENSIONS => transcript.update(full_msg),
                HS_CERTIFICATE => {
                    validate_x509_chain(body, server_name, config.root_certs, &mut leaf_cert_der)?;
                    transcript.update(full_msg);
                    cert_verify_hash = transcript.finalize();
                },
                HS_CERTIFICATE_VERIFY => {
                    verify_tls13_cert_sig(leaf_cert_der.as_slice(), &cert_verify_hash, body)?;
                    leaf_spki_verified = true;
                    transcript.update(full_msg);
                },
                HS_FINISHED => {
                    if not leaf_spki_verified { return .Err(.UnexpectedMessage); }
                    var s_fin_key: Digest256 = [0; 32];
                    hkdf_expand_label(&s_hs_traffic, b"finished", b"", &mut s_fin_key);
                    let expected_verify = sha256.hmac(&s_fin_key, &transcript.finalize());
                    if not constant_time_eq(&expected_verify, body) {
                        return .Err(.FinishedVerifyMismatch);
                    }
                    transcript.update(full_msg);
                    server_finished_ok = true;
                },
                _ => return .Err(.UnexpectedMessage),
            }
            cursor += 4 + msg_len;
        }
        if cursor > 0 {
            let rem = hs_assemble.len() - cursor;
            var s_mut = hs_assemble.as_mut_slice();
            for i in 0..rem { s_mut[i] = s_mut[cursor + i]; }
            while hs_assemble.len() > rem { let _ = hs_assemble.pop(); }
        }
    }

    // Derive Application Traffic Keys BEFORE appending Client Finished to transcript
    let srv_fin_hash = transcript.finalize();
    let derived_2 = derive_secret(&hs_secret, b"derived", &empty_hash);
    var master_secret = sha256.hkdf_extract(&derived_2, &zeros32);
    var c_ap_traffic = derive_secret(&master_secret, b"c ap traffic", &srv_fin_hash);
    var s_ap_traffic = derive_secret(&master_secret, b"s ap traffic", &srv_fin_hash);
    defer {
        secure_zeroize(&mut master_secret);
        secure_zeroize(&mut c_ap_traffic);
        secure_zeroize(&mut s_ap_traffic);
    }

    hkdf_expand_label(&c_ap_traffic, b"key", b"", &mut stream.client_app_key[..key_len]);
    hkdf_expand_label(&c_ap_traffic, b"iv",  b"", &mut stream.client_app_iv);
    hkdf_expand_label(&s_ap_traffic, b"key", b"", &mut stream.server_app_key[..key_len]);
    hkdf_expand_label(&s_ap_traffic, b"iv",  b"", &mut stream.server_app_iv);

    var c_fin_key: Digest256 = [0; 32];
    hkdf_expand_label(&c_hs_traffic, b"finished", b"", &mut c_fin_key);
    let c_verify = sha256.hmac(&c_fin_key, &srv_fin_hash);
    send_encrypted_handshake_finished(&mut stream.tcp, cipher_id, &c_hs_key, &c_hs_iv, &c_verify).await?;

    .Ok(own stream)
}
```

---

### 3.6 Unboxed `Span16` HTTP/1.1 Parser and Labeled-`match` (`SE-23`) Chunked Decoder

```rust
// File: stdlib/cx/http/parser.cx
mod parser;

use cx.http.{BodyFraming, HeaderSpan, HttpError, MAX_HEADERS, MAX_HEADER_BYTES, Method, ResponseHead};
use cx.mem.Span16;

@inline @no_alloc @no_panic @no_block
fn is_tchar(b: u8, /) -> bool = match b {
    b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z'
    | b'!' | b'#' | b'$' | b'%' | b'&' | b'\'' | b'*' | b'+'
    | b'-' | b'.' | b'^' | b'_' | b'`' | b'|' | b'~' => true,
    _ => false,
};

@inline @no_alloc @no_panic @no_block
fn ascii_eq_ignore_case(a: &[u8], b: &[u8], /) -> bool {
    if a.len() != b.len() { return false; }
    for x, i in a {
        let la = if x >= b'A' and x <= b'Z' { x + 32 } else { x };
        let y = b[i];
        let lb = if y >= b'A' and y <= b'Z' { y + 32 } else { y };
        if la != lb { return false; }
    }
    true
}

@no_alloc @no_panic @no_block
pub fn parse_response_head(
    raw_buf: &[u8],
    req_method: Method,
    out_head: &out ResponseHead,
    /,
) -> bool!HttpError {
    let limit = if raw_buf.len() > MAX_HEADER_BYTES { MAX_HEADER_BYTES } else { raw_buf.len() };
    let hdr_end: usize = find_end: for _, i in raw_buf[..limit] {
        if i + 4 <= limit
            and raw_buf[i] == b'\r'
            and raw_buf[i + 1] == b'\n'
            and raw_buf[i + 2] == b'\r'
            and raw_buf[i + 3] == b'\n'
        {
            break :find_end i + 4;
        }
    } orelse {
        if raw_buf.len() >= MAX_HEADER_BYTES {
            return .Err(.HeaderTooLarge);
        }
        out_head.* = ResponseHead {
            status_raw: 0,
            reason_span: Span16.EMPTY,
            headers: [HeaderSpan { name: Span16.EMPTY, value: Span16.EMPTY }; 64],
            header_count: 0,
            header_bytes_len: 0,
            keep_alive: false,
            framing: .None,
        };
        return .Ok(false);
    };

    if hdr_end < 14
        or raw_buf[0] != b'H' or raw_buf[1] != b'T' or raw_buf[2] != b'T' or raw_buf[3] != b'P'
        or raw_buf[4] != b'/' or raw_buf[5] != b'1' or raw_buf[6] != b'.'
        or (raw_buf[7] != b'1' and raw_buf[7] != b'0')
        or raw_buf[8] != b' '
    {
        return .Err(.MalformedStatusLine);
    }
    let minor = raw_buf[7] - b'0';
    let d0 = raw_buf[9];
    let d1 = raw_buf[10];
    let d2 = raw_buf[11];
    if d0 < b'1' or d0 > b'5' or d1 < b'0' or d1 > b'9' or d2 < b'0' or d2 > b'9' or raw_buf[12] != b' ' {
        return .Err(.MalformedStatusLine);
    }
    let status: u16 = ((d0 - b'0') as u16) * 100 + ((d1 - b'0') as u16) * 10 + ((d2 - b'0') as u16);

    let line0_end = find_crlf(raw_buf, 13, hdr_end) orelse return .Err(.MalformedStatusLine);
    let reason_span = Span16 { off: 13_u16, len: (line0_end - 13) as u16 };

    var headers: [HeaderSpan; 64] = [HeaderSpan { name: Span16.EMPTY, value: Span16.EMPTY }; 64];
    var h_count: usize = 0;
    var pos: usize = line0_end + 2;
    var keep_alive: bool = minor == 1;
    var has_chunked = false;
    var has_te = false;
    var parsed_cl: u64? = .None;

    while pos + 2 <= hdr_end - 2 {
        let line_end = find_crlf(raw_buf, pos, hdr_end) orelse return .Err(.MalformedHeaderLine);
        if line_end == pos { break; }
        if h_count >= MAX_HEADERS { return .Err(.TooManyHeaders); }

        if raw_buf[pos] == b' ' or raw_buf[pos] == b'\t' {
            return .Err(.MalformedHeaderLine);
        }

        let colon_pos: usize = find_colon: for idx in pos..line_end {
            let ch = raw_buf[idx];
            if ch == b':' { break :find_colon idx; }
            if not is_tchar(ch) { return .Err(.MalformedHeaderLine); }
        } orelse return .Err(.MalformedHeaderLine);

        if colon_pos == pos { return .Err(.MalformedHeaderLine); }

        var val_start = colon_pos + 1;
        while val_start < line_end and (raw_buf[val_start] == b' ' or raw_buf[val_start] == b'\t') {
            val_start += 1;
        }
        var val_end = line_end;
        while val_end > val_start and (raw_buf[val_end - 1] == b' ' or raw_buf[val_end - 1] == b'\t') {
            val_end -= 1;
        }
        for v_idx in val_start..val_end {
            let b = raw_buf[v_idx];
            if (b < 0x20 and b != b'\t') or b == 0x7F {
                return .Err(.MalformedHeaderLine);
            }
        }

        let name_slice = raw_buf[pos..colon_pos];
        let val_slice = raw_buf[val_start..val_end];

        if ascii_eq_ignore_case(name_slice, b"content-length") {
            let cl = parse_decimal_u64(val_slice) orelse return .Err(.MalformedHeaderLine);
            if parsed_cl is .Some(prev_cl) and prev_cl != cl {
                return .Err(.ConflictingFramingHeaders);
            }
            parsed_cl = .Some(cl);
        } else if ascii_eq_ignore_case(name_slice, b"transfer-encoding") {
            has_te = true;
            if ascii_eq_ignore_case(val_slice, b"chunked") {
                has_chunked = true;
            } else {
                return .Err(.InvalidChunkEncoding);
            }
        } else if ascii_eq_ignore_case(name_slice, b"connection") {
            if ascii_eq_ignore_case(val_slice, b"close") {
                keep_alive = false;
            } else if ascii_eq_ignore_case(val_slice, b"keep-alive") {
                keep_alive = true;
            }
        }

        headers[h_count] = HeaderSpan {
            name: Span16 { off: pos as u16, len: (colon_pos - pos) as u16 },
            value: Span16 { off: val_start as u16, len: (val_end - val_start) as u16 },
        };
        h_count += 1;
        pos = line_end + 2;
    }

    if has_te and parsed_cl is .Some(_) {
        return .Err(.ConflictingFramingHeaders);
    }

    let framing: BodyFraming = if req_method == .Head or (status >= 100 and status < 200) or status == 204 or status == 304 {
        .None
    } else if has_chunked {
        .Chunked
    } else if parsed_cl is .Some(n) {
        .ContentLength(n)
    } else {
        keep_alive = false;
        .CloseDelimited
    };

    out_head.* = ResponseHead {
        status_raw: status,
        reason_span: reason_span,
        headers: headers,
        header_count: h_count as u16,
        header_bytes_len: hdr_end as u16,
        keep_alive: keep_alive,
        framing: framing,
    };
    .Ok(true)
}

@no_alloc @no_panic @no_block
fn find_crlf(buf: &[u8], start: usize, end: usize, /) -> usize? {
    var i = start;
    while i + 1 < end {
        if buf[i] == b'\r' {
            if buf[i + 1] != b'\n' { return .None; }
            return .Some(i);
        }
        if buf[i] == b'\n' { return .None; }
        i += 1;
    }
    .None
}

@no_alloc @no_panic @no_block
fn parse_decimal_u64(s: &[u8], /) -> u64? {
    if s.is_empty() { return .None; }
    var acc: u64 = 0;
    for b in s {
        if b < b'0' or b > b'9' { return .None; }
        let digit = (b - b'0') as u64;
        if acc > (u64.MAX - digit) / 10 { return .None; }
        acc = acc * 10 + digit;
    }
    .Some(acc)
}

pub enum ChunkPhase: u8 {
    ReadSizeHex   = 0,
    SkipChunkExt  = 1,
    ExpectSizeLf  = 2,
    CopyPayload   = 3,
    ExpectDataCr  = 4,
    ExpectDataLf  = 5,
    TrailerStart  = 6,
    TrailerSkip   = 7,
    TrailerLf     = 8,
    Done          = 9,
}

@no_alloc @no_panic @no_block
pub fn decode_chunked_step(
    phase: &mut ChunkPhase,
    rem_in_chunk: &mut u64,
    hex_digits_seen: &mut u8,
    src: &[u8],
    dst: &mut [u8],
    /,
) -> (usize, usize)!HttpError {
    var s_idx: usize = 0;
    var d_idx: usize = 0;

    fsm: match phase.* {
        .ReadSizeHex => {
            if s_idx >= src.len() { phase.* = .ReadSizeHex; return .Ok((s_idx, d_idx)); }
            let b = src[s_idx];
            if b == b';' and hex_digits_seen.* > 0 {
                s_idx += 1;
                continue :fsm .SkipChunkExt;
            }
            if b == b'\r' and hex_digits_seen.* > 0 {
                s_idx += 1;
                continue :fsm .ExpectSizeLf;
            }
            let nib: u64 = match b {
                b'0'..=b'9' => (b - b'0') as u64,
                b'a'..=b'f' => (b - b'a' + 10) as u64,
                b'A'..=b'F' => (b - b'A' + 10) as u64,
                _ => return .Err(.InvalidChunkEncoding),
            };
            if hex_digits_seen.* >= 16 { return .Err(.InvalidChunkEncoding); }
            rem_in_chunk.* = (rem_in_chunk.* << 4) | nib;
            hex_digits_seen.* += 1;
            s_idx += 1;
            continue :fsm .ReadSizeHex;
        },
        .SkipChunkExt => {
            if s_idx >= src.len() { phase.* = .SkipChunkExt; return .Ok((s_idx, d_idx)); }
            let b = src[s_idx];
            s_idx += 1;
            if b == b'\r' { continue :fsm .ExpectSizeLf; }
            if b == b'\n' { return .Err(.InvalidChunkEncoding); }
            continue :fsm .SkipChunkExt;
        },
        .ExpectSizeLf => {
            if s_idx >= src.len() { phase.* = .ExpectSizeLf; return .Ok((s_idx, d_idx)); }
            if src[s_idx] != b'\n' { return .Err(.InvalidChunkEncoding); }
            s_idx += 1;
            hex_digits_seen.* = 0;
            if rem_in_chunk.* == 0 { continue :fsm .TrailerStart; }
            continue :fsm .CopyPayload;
        },
        .CopyPayload => {
            if rem_in_chunk.* == 0 { continue :fsm .ExpectDataCr; }
            if s_idx >= src.len() or d_idx >= dst.len() {
                phase.* = .CopyPayload;
                return .Ok((s_idx, d_idx));
            }
            let avail_src = src.len() - s_idx;
            let avail_dst = dst.len() - d_idx;
            var n = if avail_src < avail_dst { avail_src } else { avail_dst };
            if (n as u64) > rem_in_chunk.* { n = rem_in_chunk.* as usize; }
            for k in 0..n { dst[d_idx + k] = src[s_idx + k]; }
            s_idx += n;
            d_idx += n;
            rem_in_chunk.* -= n as u64;
            if rem_in_chunk.* == 0 { continue :fsm .ExpectDataCr; }
            phase.* = .CopyPayload;
            return .Ok((s_idx, d_idx));
        },
        .ExpectDataCr => {
            if s_idx >= src.len() { phase.* = .ExpectDataCr; return .Ok((s_idx, d_idx)); }
            if src[s_idx] != b'\r' { return .Err(.InvalidChunkEncoding); }
            s_idx += 1;
            continue :fsm .ExpectDataLf;
        },
        .ExpectDataLf => {
            if s_idx >= src.len() { phase.* = .ExpectDataLf; return .Ok((s_idx, d_idx)); }
            if src[s_idx] != b'\n' { return .Err(.InvalidChunkEncoding); }
            s_idx += 1;
            continue :fsm .ReadSizeHex;
        },
        .TrailerStart => {
            if s_idx >= src.len() { phase.* = .TrailerStart; return .Ok((s_idx, d_idx)); }
            let b = src[s_idx];
            s_idx += 1;
            if b == b'\r' { continue :fsm .TrailerLf; }
            if b == b'\n' { return .Err(.InvalidChunkEncoding); }
            continue :fsm .TrailerSkip;
        },
        .TrailerSkip => {
            if s_idx >= src.len() { phase.* = .TrailerSkip; return .Ok((s_idx, d_idx)); }
            let b = src[s_idx];
            s_idx += 1;
            if b == b'\r' {
                if s_idx < src.len() and src[s_idx] == b'\n' {
                    s_idx += 1;
                    continue :fsm .TrailerStart;
                }
            }
            continue :fsm .TrailerSkip;
        },
        .TrailerLf => {
            if s_idx >= src.len() { phase.* = .TrailerLf; return .Ok((s_idx, d_idx)); }
            if src[s_idx] != b'\n' { return .Err(.InvalidChunkEncoding); }
            s_idx += 1;
            continue :fsm .Done;
        },
        .Done => {
            phase.* = .Done;
            .Ok((s_idx, d_idx))
        },
    }
}
```

---

## 4. Deliverable 3: Security, Resource-Cap, and NIST/Wycheproof Test Vector Specification

### 4.1 Hard Resource Bounds, Slowloris/Redirect Caps, and Protocol Hardening Matrix

Every parser, handshake state machine, and network buffer in Phase 11.2b enforces explicit resource ceilings so malicious mirrors, rogue proxies, or fuzzed byte streams (`corex test --fuzz`) cannot induce OOM, stack exhaustion, credential exfiltration, or HTTP framing desynchronization:

| Subsystem / Layer | Enforced Resource Cap / Timeout | Attack Vector Mitigated & Exact Rejection Rule |
| :--- | :--- | :--- |
| **HTTP/1.1 Header Block** | `MAX_HEADER_BYTES = 16_384` (`16 KiB`), `MAX_HEADERS = 64` | Prevents header-flood memory exhaustion while keeping all `Span16` (`u16` `< 65,536`) offsets provably in-bounds (`HttpError.HeaderTooLarge` / `.TooManyHeaders`). |
| **HTTP/1.1 Framing & Smuggling** | `0` conflicting framing headers; `≤16` hex digits per chunk size; `≤4 KiB` chunk extensions/trailers | Rejects simultaneous `Transfer-Encoding` + `Content-Length`, duplicate differing `Content-Length`, bare `CR`/`LF` line endings, `obs-fold` continuations, and raw CTLs (`0x00..0x1F \ \t`, `0x7F`) in outgoing and incoming headers (blocks CRLF injection and CL.TE/TE.CL smuggling). |
| **Slowloris & Stall Timeouts** | `connect = 5s`, `tls_handshake = 10s`, `header_read = 10s` (cumulative wall budget across entire header block), `idle_body_chunk = 15s` | Defeats Slowloris trickle attacks (sending 1 byte every 9 seconds to reset naive per-`read` timers) by wrapping `read_response_head` in a single cumulative `with_timeout(header_read_timeout, ...)`. |
| **HTTP Redirects & Auth Stripping** | `MAX_REDIRECTS = 5`; cross-origin header sanitizer; HTTPS downgrade block | Caps `301`/`302`/`303`/`307`/`308` hops at `5` (`RedirectLimitExceeded`); rewrites `303` to `GET` with empty body; **strips `Authorization`, `Proxy-Authorization`, and `Cookie` whenever `(scheme, host, port)` changes**; and rejects `https://` to `http://` downgrades (`HttpsDowngradeBlocked`). |
| **Keep-Alive Connection Pool** | `MAX_POOL_CONNS = 8`, `MAX_IDLE_MS = 30_000`, `0`-unread-body invariant | Recycles only connections whose response body reached clean `ContentLength(0)` or `ChunkPhase.Done` EOF; cancelled or erroring streams invoke `close_abort` immediately. |
| **IPv4 / DNS SSRF Guards** | Strict decimal IPv4 (no leading `'0'`); `≤16` DNS `A`/`AAAA` answers; `≤8` CNAME hops | Rejects octal/hex IPv4 (`0177.0.0.1` $\rightarrow$ `AddrParseError.LeadingZeroOctet`); verifies 16-bit CSPRNG DNS transaction ID and peer IP/port. |
| **TLS 1.3 Record & X.509 Chain** | Ciphertext record `≤16,640 B`; Handshake msg `≤32 KiB`; Cert chain `≤8` certs; `≤32` `NewSessionTicket`s | Blocks record/certificate memory bombs (`RecordOverflow` / `HandshakeTooLarge` / `CertChainTooDeep`), empty-record / post-handshake `NewSessionTicket` DoS loops, and X25519 all-zero low-order shared secrets (`InvalidServerKeyShare`). |
| **Bao & Package Cache Streaming** | `BaoVerifier` stack `= 1,856 B` (`54` CVs); `.cxpkg` `max_bytes = 256 MiB`; withheld length | Withholds header `claimed_len` until final chunk + stream EOF validate (`BaoLengthMismatch`); unlinks `~/.corex/cache/blake3/staging/*.tmp` on any hash mismatch prior to atomic rename. |

---

### 4.2 Official NIST, IETF RFC, BLAKE3/Bao, and Project Wycheproof Test Vector Suite

The Phase 11.2b verification gate (`tests/stdlib/std03_vectors_test.cx`) enforces bit-exact parity across all eight vector suites across pre-opt `MirVm`, post-opt `MirVm`, `-ofmt=c`, and `LLVM`:

#### Official BLAKE3 (`test_vectors.json`) Vectors

Input pattern: `input[i] = (i % 251) as u8` for `0 <= i < len`; `key = b"whats the Elvish word for friend"` (32 bytes); `context = "BLAKE3 2019-12-27 16:29:52 test vectors context"` (plus `len = 8,192` and `16,385` exercising `hash_8_chunks_simd` `Simd[u32, 8]` against `Simd[u32, 4]`):

| `len` | `blake3.hash` (Hex) | `blake3.keyed_hash` (Hex) | `blake3.derive_key` (Hex) |
| ---: | :--- | :--- | :--- |
| **`0`** | `af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262` | `92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26` | `2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d` |
| **`1`** | `2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213` | `6d7878dfff2f485635d39013278ae14f1454b8c0a3a2d34bc1ab38228a80c95b` | `b3e2e340a117a499c6cf2398a19ee0d29cca2bb7404c73063382693bf66cb06c` |
| **`64`** | `4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98` | `ba8ced36f327700d213f120b1a207a3b8c04330528586f414d09f2f7d9ccb7e6` | `a5c4a7053fa86b64746d4bb688d06ad1f02a18fce9afd3e818fefaa7126bf73e` |
| **`65`** | `de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee` | `c0a4edefa2d2accb9277c371ac12fcdbb52988a86edc54f0716e1591b4326e72` | `51fd05c3c1cfbc8ed67d139ad76f5cf8236cd2acd26627a30c104dfd9d3ff8a8` |
| **`1024`** | `42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7` | `75c46f6f3d9eb4f55ecaaee480db732e6c2105546f1e675003687c31719c7ba4` | `7356cd7720d5b66b6d0697eb3177d9f8d73a4a5c5e968896eb6a689684302706` |
| **`1025`** | `d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444` | `357dc55de0c7e382c900fd6e320acc04146be01db6a8ce7210b7189bd664ea69` | `effaa245f065fbf82ac186839a249707c3bddf6d3fdda22d1b95a3c970379bcb` |
| **`2049`** | `5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030` | `9f29700902f7c86e514ddc4df1e3049f258b2472b6dd5267f61bf13983b78dd5` | `2ea477c5515cc3dd606512ee72bb3e0e758cfae7232826f35fb98ca1bcbdf273` |

#### Bao Outboard (`.obao`) and FIPS 180-4 SHA-256 / SHA-384 Vectors

For the `oconnor663/bao/docs/spec.md` 2,049-zero-byte (`[0x00; 2049]`) test case, the 136-byte outboard `.obao` stream consists of length header `0108000000000000` (`[0..8]`), root parent `a04fc7e7e6831a11965e686a56952b0830aadd1555beabcc79b8db5c93e680d3c37466bfff693873425adf2590fc7058f0f99b3d33103f87431d6fd1823e58da` (`[8..72]`), and left parent `91715ad631c858232d522cc2ff678052288c8c540fc6ab6c5fa5104cb63e0d39f0eef3b0033abb623278828fcc75f90c65bde353141ec7c6854eae1c515b93ca` (`[72..136]`), verifying against root hash `b982335435308f3f5f5f51f5d45ecae6194641975e7b0bcaa1facd48ebabb28e`; mutating the header to `2048` (`0008000000000000`) or `2050` (`0208000000000000`) or feeding an empty `0000000000000000` stream under a non-empty root must fail with `.BaoHashMismatch` or `.BaoLengthMismatch` prior to exposing EOF. For FIPS 180-4 SHA-256 and SHA-384, `""` hashes to `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (SHA-384 `38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b`), `"abc"` hashes to `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` (SHA-384 `cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7`), and the 448-bit `"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"` string hashes to `248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1`.

#### RFC 8032 §7.1 and Project Wycheproof `ed25519_test.json` Strict Verification Vectors

| Case ID | Public Key (`pk` Hex) | Msg (Hex) | Signature (`sig` Hex) | Expected Outcome & Invariant Verified |
| :--- | :--- | :--- | :--- | :--- |
| **RFC 8032 #1** | `d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a` | `""` | `e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b` | **`.Ok(())`** (Valid empty message) |
| **RFC 8032 #2** | `3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c` | `"72"` | `92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00` | **`.Ok(())`** (Valid 1-byte message) |
| **RFC 8032 #3** | `fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025` | `"af82"` | `6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a` | **`.Ok(())`** (Valid 2-byte message) |
| **Wycheproof `tcId: 3`** | `7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa` | `"54657374"` | `7c38e026f29e14aabd059a0f2db8b0cd783040609a8be684db12f82a27774ab07a9155711ecfaf7f99f277bad0c6ae7e39d4eef676573336a5c51eb6f946b30d` | **`.Ok(())`** (Wycheproof valid baseline `"Test"`) |
| **Malleable $S + L$** | `d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a` | `""` | `e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901554c8c7872aa064e049dbb3013fbf29380d25bf5f0595bbe24655141438e7a101b` | **`.Err(.InvalidSignature)`** (Rejects malleable $S' = S + L \ge L$) |
| **Wycheproof `tcId: 10`** | `7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa` | `"3f"` | `00` repeated 64 times | **`.Err(.InvalidSignature)`** (All-zero `R` and `S` special values) |
| **Wycheproof `tcId: 48`** | `7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa` | `"313233343030"` | `657c1412402ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b7fd2ac7da14afffcceeb13f2a0d6b887941cb1a5eb57a52f3cb131a16cce7b0e` | **`.Err(.InvalidSignature)`** (`InvalidEncoding` on `R`/`S`) |
| **Wycheproof `tcId: 49`** | `7d4d0e7f6153a69b6242b522abbee685fda4420f8834b108c3bdae369ef549fa` | `"313233343030"` | `657c1492412ab5ce03e2c3a7f0384d051b9cf3570f1207fc78c1bcc98c281c2b7373ba13ebbef99cd2a8ead55ce735c987d85a35320925a8e871702dc7c5c40d` | **`.Err(.InvalidSignature)`** (Bit-32 tamper in `R`; caught by canonical re-encode check) |
| **8-Torsion Key** | `01` followed by 31 `00` bytes | `"706b67"` | `01` followed by 63 `00` bytes | **`.Err(.InvalidPublicKey)`** (`SmallOrderPublicKey` $[8]A = \mathcal{O}$ rejected) |

#### RFC 6962 / RFC 9162 Merkle Proofs, Wyhash v4.3, TLS 1.3 (RFC 8448), and `Span16` HTTP Vectors

| Vector Suite | Canonical Inputs & Parameters | Expected Exact Hex / Struct Output |
| :--- | :--- | :--- |
| **RFC 9162 7-Leaf Inclusion** | `d[i] = [i]` (`0..7`), `leaf_idx = 4`, `L4 = 4f35212d12f9ad2036492c95f1fe79baf4ec7bd9bef3dffa7579f2293ff546a4`, `root7 = 3560191803028444b232018ac047fdb561c09c23a7a6876c85e08b5e4d48e9f3` | 3-hash path `[9f1afa4dc124cba7..., 40d88127d4d31a38..., 9bcd51240af40051...]` $\rightarrow$ `.Ok(())`; appending/dropping 1 hash $\rightarrow$ `.Err(.MerkleProofInvalid)`. |
| **RFC 9162 Consistency (`3 -> 7` & `4 -> 7`)** | `root3 = 3b6cccd7e3e023ff393006f030315ee7ad9eb111b022b41fba7e5b7a3973f688`; `root4 = 9bcd51240af4005168f033121ba85be5a6ed4f0e6a5fac262066729b8fbfdecb` | `cons(3, 7)` 4-hash `[fcf0a6c7..., 583c7dfb..., a20bf9a7..., 89c92983...]` $\rightarrow$ `.Ok(())`; `cons(4, 7)` 1-hash `[89c929834ed1459b07f65b5e1a2143a8cf5d8efdf30f49ffffa328bb1d9133bb]` $\rightarrow$ `.Ok(())`. |
| **Wyhash v4.3 64-Bit & 128-Bit** | `("", 0)`, `("a", 1)`, `("abc", 2)`, `("message digest", 3)`, `("A..Za..z0..9", 5)`; `hash128("", 0)` & `hash128("abc", 0)` | `hash64`: `0x93228a4de0eec5a2`, `0xc5bac3db178713c4`, `0xa97f2f7b1d9b3314`, `0x786d1f1df3801df4`, `0xb9e734f117cfaf70`; `hash128("abc", 0)` = `{ lo: 0x989b4a209c1011c9, hi: 0xe41f7084c69e4470 }`. |
| **X25519 (RFC 7748 + Wycheproof)** | Scalar `a546e36b...9ac4`, peer `e6db6867...1c4c`; low-order peers `00..00`, `0100..00`, `e0eb7a7c...b800`, `5f9c95bc...1157` | Shared `c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552`; all low-order peers $\rightarrow$ `.Err(.WeakKeyShare)`. |
| **ChaCha20-Poly1305 & AES-128-GCM** | RFC 8439 §2.8.2 (`key = 80..9f`, `nonce = 070000004041424344454647`, `aad = 50515253c0c1c2c3c4c5c6c7`); NIST SP 800-38D TC2 & TC4 (`key = feffe9928665731c6d6a8f9467308308`) | RFC 8439 tag `1ae10b594f09e26a7e902ecbd0600691`; SP 800-38D TC2 `ct = 0388dace60b6a392f328c2b971b2fe78`, `tag = ab6e47d42cec13bdf53a67b21257bddf`; TC4 `tag = 5bc94fbc3221a5db94fae95ae7121a47`. |
| **RFC 8448 §3 TLS 1.3 Key Schedule** | Client pub `99381de5...af2c`, Server priv `b1580eea...a21e`, `ClientHello` (`010000c0...`), `ServerHello` (`02000056...`) | `shared = 8bd4054f...492d`; `early = 33ad0a1c...f92a`; `hs_secret = 1dc826e9...beac`; `c_hs = b3eddb12...5a21`; `s_hs = b67b7d69...ad38` (`s_hs_key = 3fce516009c21727d0f2e4e86ee403bc`, `s_hs_iv = 5d313eb2671276ee13000b30`); `master = 18df0684...2919`. |
| **`Span16` HTTP/1.1 Framing** | 102-byte `HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: 1024\r\nETag: "b3:42214739"\r\n\r\n` + CL/TE smuggling cases | `status_raw = 200`, `header_bytes_len = 102`, `headers[0] = (17..29, 31..55)`, `headers[1] = (57..71, 73..77)`, `headers[2] = (79..83, 85..98)`; `CL + TE` or dual differing `CL` $\rightarrow$ `.Err(.ConflictingFramingHeaders)`. |

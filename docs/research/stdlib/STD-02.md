# Zero-Copy I/O, Cross-Platform Filesystem/Paths, Clocks & OS Process Architecture (`cx.io`, `cx.path`, `cx.fs`, `cx.time`, `cx.env`, `cx.process`)

CoreX Phase 11.2a (`STD-02`) defines the six foundational streaming, path, filesystem, clock, environment, and child-process modules (`stdlib/cx/{io,path,fs,time,env,process}.cx`) required to self-host `compiler/*.cx`, `VfsSourceMap`, `pkg_cache`, the `lld` linker driver, `corex lsp`, and the `corex test` runner across Linux (`x86_64`/`aarch64` `gnu` 2.28+ and static `musl` 1.2.5), macOS (`x86_64`/`aarch64`), Windows (`x86_64`/`aarch64`), and `wasm32-unknown-wasi`. Across all six modules, external OS descriptors (`File`, `Dir`, `Mmap`, `FileLock`, `FsWatcher`, `ChildProcess`, `StdinLock`, `StdoutLock`, `StderrLock`) are Tier-3 `@linear` values (`DR-06`), turning leaked descriptors, unclosed memory mappings, orphaned advisory locks, and un-reaped child processes into compile-time error `E0304`. Every fallible signature uses payload-first `T!IoError` or `T!FsError` (`DR-22` `ADR-22C`), where both `IoError` and `FsError` pack into a **single non-zero 64-bit word (`8 bytes`, `bit[0] == 0`)**. This representation fits inside a single hardware `swifterror` register (`R12` on `x86_64`, `X21` on `aarch64`, `X19` on `Arm64EC` per `DR-20` `Fix-07`) with zero heap allocation on OS failures and stashes inline inside 16-byte slice (`&[u8]!FsError`) and 24-byte `PathBuf!FsError` niche layouts without triggering stack-spilled `sret` returns.

In `cx.io`, CoreX combines Zig 0.15+'s non-generic "buffer-above-the-vtable" streaming layout with Rust RFC 2930's uninitialized write-cursor safety while avoiding Zig's address-pinned `@fieldParentPtr` move bug, Rust's generic parser code duplication, and Go's interface-boxing heap escapes. Uninitialized read buffers use MVS `&out [u8]` (`OutBuf`, statically verified by `MIR` SAST Pass 2 without redundant `memset` zero-initialization); non-generic `BufReader` (`48 B`) and `BufWriter` (`32 B`) execute `peek`, `consume`, SIMD `read_until`, and stack-resident `FmtArgs` formatting (`SE-12`) inline before touching `{ ctx: *mut opaque, vtable }` handles; and `IoSlice` (`16 B` on 64-bit, `8 B` on `wasm32`) matches `iovec`, `ciovec`, and `WSABUF` bit-for-bit. In `cx.path` and `cx.fs`, borrowed `Path` slices and 24-byte SSO `PathBuf`s use lossless WTF-8 on Windows with a zero-heap `[u16; 512]` (`1 KiB`) stack transcoding fast path and automatic `\\?\` extended-length promotion for paths `>= 248` `WCHAR`s or reserved DOS device stems; `Dir` enforces capability-jailed relative opens (`openat2` `RESOLVE_BENEATH`, `NtCreateFile` `RootDirectory`, WASI `path_open`); `load_file_thresholded` splits `VfsSourceMap` loading at `16 KiB` between NUL-terminated `Arena` reads and page-guarded read-only `Mmap`; `write_atomic` and `publish_staged_atomic` enforce fresh-inode `UnlinkAndReplace` (`FileRenameInfoEx` + `FILE_RENAME_FLAG_POSIX_SEMANTICS` on Windows, avoiding `MoveFileExW` open-handle failures, and fresh-inode `renameat` on macOS, avoiding XNU `cs_mtime != mtime` `SIGKILL`); and `materialize_file` cascades across copy-on-write reflinks (`FICLONE`, `clonefileat`, cluster-aligned ReFS `FSCTL_DUPLICATE_EXTENTS_TO_FILE`), hardlinks, and kernel copy fallbacks.

In `cx.time`, `cx.env`, and `cx.process`, every OS entry point carries a `DR-17` `@std_cap_boundary` attribute (`fs`, `env`, `process`, `clock`, `blocking_sync`) for zero-annotation `corex.lock` supply-chain sandboxing while routing runtime operations through `Context.reactor` (`DR-20` Seam #5) for deterministic `corex test --sim` replay. `Instant.now()` scales `CLOCK_MONOTONIC`, `mach_continuous_time`, and `QueryPerformanceCounter` ticks via overflow-free `u128` quotient-remainder arithmetic – eliminating the `18.45 s` to `85.9 min` `u64` `ticks * 10^9` overflow cliff across 584.5 years of uptime. `cx.env` marks process-wide `set_var` and `remove_var` `unsafe` (preventing multithreaded POSIX `getenv` Use-After-Free races documented in Rust 2024 Edition) and resolves XDG, macOS, and Windows directories without linking `shell32.dll`. Finally, `cx.process.Command` spawns `@linear ChildProcess` handles via `posix_spawn` (with a `glibc <= 2.28` `fork+execve` `chdir` fallback) on Unix and hardened `CreateProcessW` on Windows – resolving `.exe` paths explicitly into non-null `lpApplicationName`, rejecting `.bat`/`.cmd` targets by default to prevent `BatBadBut` (`CVE-2024-24576`) command injection, and deduplicating inherited stdio handles in `PROC_THREAD_ATTRIBUTE_HANDLE_LIST`.

---

## 1. Architectural Analysis Across Streaming I/O, Filesystems, Clocks & Processes

### 1.1 Zero-Copy Buffered and Vectored Streaming Without Trait or Allocation Traps

Designing `cx.io` for compiler lexing, `corex lsp` JSON-RPC framing, and package archive streaming requires overcoming structural bottlenecks present in Rust, Zig 0.14–0.17, and Go. In Rust, `Read::read(&mut [u8])` requires callers to zero-initialize destination buffers before every read to prevent safe `Read` implementations from observing uninitialized memory (`RUSTSEC-2021-0015`, `RUSTSEC-2021-0029`), while RFC 2930's `BorrowedBuf` / `BorrowedCursor` replacement (`#78485`) remains nightly-only due to lifetime-parameterized cursor wrapper complexity and trait dual-dispatch rules (`rustc_must_implement_one_of`). Furthermore, parameterizing parsers over `<R: BufRead>` monomorphizes duplicate machine code for `File`, `TcpSocket`, and `&[u8]`, whereas `&mut dyn BufRead` pays virtual dispatch on small reads. Conversely, Go's `io.Reader` and `io.Writer` avoid generics via two-word interfaces, but passing a local buffer or `bytes.Buffer` across an `io.Reader` or `fmt.Fprintf` interface boundary routinely defeats Go's compile-time escape analysis (`go build -gcflags=-m`), forcing stack-eligible slices and format arguments onto the garbage-collected heap.

Zig 0.14 used `anytype` generic readers (`BufferedReader`) that suffered from severe monomorphization bloat, prompting Zig 0.15–0.17 ("Writergate", PR `#24329`) to replace them with concrete, non-generic `std.Io.Reader` (`{ vtable, buffer, seek, end }`) and `std.Io.Writer` (`{ vtable, buffer, end }`) structs that hoist the byte buffer *above* the `VTable`. While hoisting the buffer above the vtable eliminates generic duplication and keeps hot-path byte consumption inline, Zig embeds `interface: std.Io.Reader` intrusively inside `std.fs.File.Reader` and recovers the parent state via `@fieldParentPtr`, meaning `Reader` and `Writer` must live at a pinned memory address and silently corrupt state if moved or returned by value.

| Architectural Dimension | Rust `Read` / `BufRead` (`BorrowedBuf` RFC 2930) | Zig 0.15–0.17 `std.Io.Reader` / `Writer` | Go `io.Reader` / `io.Writer` | CoreX `cx.io` Architecture (`Phase 11.2a`) |
| :--- | :--- | :--- | :--- | :--- |
| **Dispatch & Code-Size Model** | Generic `<R: Read>` duplicates parser bodies; `&mut dyn BufRead` pays vtable indirection. | Non-generic concrete structs with buffer above `vtable`; zero generic duplication. | 2-word interface `{ itab, data }`; indirect call on every `Read`/`Write`. | **Hybrid:** Concrete non-generic `BufReader` (`48 B`) / `BufWriter` (`32 B`) above MVS `{ ctx: *mut opaque, vtable }` `Reader` / `Writer` (`16 B`). |
| **Move & Return Safety** | Safe moves, but generic `BufReader<R>` leaks `R` into outer struct types. | **Address-Pinned Hazard:** Intrusive `@fieldParentPtr`; copying or returning by value is a memory bug. | Interface-boxed values move to GC heap. | **100% MVS Move-Safe:** Explicit `ctx: *mut opaque` + Pass-3 `FnRegionSummary` borrow tracking (`E0306`); moving `BufReader` by value is always valid. |
| **Uninitialized Read Buffer Tax** | `read(&mut [u8])` forces `memset`; `BorrowedBuf<'a>` still unstable (`#78485`). | Buffer tail after `end` holds `undefined` bytes without static read guards. | Mandatory zeroed `make([]byte, N)` slice allocation. | **Zero-Memset `OutBuf` (`&out [u8]`):** Wraps uninitialized stack/arena bytes (`E0422`); safe `.cx` code can only append or read `0..filled`. |
| **Formatting & Heap Escapes** | `write_fmt` is zero-alloc, but `format!` allocates heap `String`. | Zero-alloc `Writer.print` into caller-supplied buffer. | `io.Reader.Read(buf)` and `fmt.Println` cause buffers and args to escape to heap. | **Zero Heap Escape:** Second-class MVS borrows never escape (`@no_alloc`-clean); `SE-12` `FmtArgs` uses stack `[FmtArg; k]` + `.rodata`. |
| **Vectored I/O (`iovec` / `WSABUF`)** | `IoSlice` matches OS ABI, but `write_vectored` is partial-only and hit `IOV_MAX` `EINVAL` (`#68042`). | `Writer.vtable.drain` takes `&[]const []const u8` + `splat`, converting slices inside `File`. | No vectored `io.Writer` in core `io`; `net.Buffers` mutates heap slice headers. | **ABI-Exact `IoSlice` (`iovec` / `ciovec` / `WSABUF`) + Coalescing `BufWriter`:** Clamps to `IOV_MAX` (`1024` POSIX, `128` WASI) and provides `write_all_vectored`. |

> **Visual – Buffer-First Streaming Eliminates Generic Bloat, Memset Tax, and VTable Overhead on Hot Paths:** **Top:** CoreX places the active byte slice directly inside non-generic *BufReader* (48 B) and *BufWriter* (32 B) structs above an MVS-borrowed 16-byte *Reader*/*Writer* handle, executing *peek*, *consume*, SIMD *read_until*, and *FmtArgs* formatting inline with zero indirect calls until buffer exhaustion. **Middle:** *OutBuf* pairs MVS *&out [u8]* with a monotonic *filled* cursor so uninitialized stack buffers skip redundant zeroing while forbidding uninitialized reads in safe code. **Bottom:** Conditional *@repr(C)* layout makes *&[IoSlice]* a zero-copy cast to kernel scatter-gather arrays across all Tier-1 targets.

CoreX resolves both Zig's move hazard and Rust's lifetime/generic bloat through MVS second-class region provenance (`DR-06` Pass 3). Calling `file.as_reader()` returns a 16-byte `Reader` (`{ ctx: &raw mut self as *mut opaque, vtable: &FILE_READER_VTABLE }`) whose inferred `FnRegionSummary` carries `ret_provenance_mask = 0b1`, holding an exclusive `access.inout` loan on `file` for the exact lifetime of the `Reader` and any `BufReader` or `LimitReader` wrapping it. Both `BufReader` (`48 B`: `16 B` `Reader` + `16 B` buffer pointer/capacity + `8 B` `pos` + `8 B` `filled`) and `BufWriter` (`32 B`: `16 B` `Writer` + `8 B` `buf_ptr` + `4 B` `filled` + `4 B` `cap_and_flags` with bit 31 encoding `line_buffered`) perform **zero heap allocations**: callers supply either an uninitialized stack array (`var raw: [u8; 8192]; var br = BufReader.over_uninit(file.as_reader(), &out raw);`) or an `Arena` slab (`BufReader.in_arena(&mut arena, file.as_reader())`). Rather than wrapping tokens across power-of-two ring boundaries – which splits contiguous identifiers and JSON strings into two disjoint slices – `BufReader` uses a contiguous linear window with lazy tail rebasing: when `pos == filled`, `consume` resets both cursors to `0` at zero copy cost, and when a delimiter scan straddles a refill, only the unconsumed tail (`filled - pos` bytes) shifts to index `0` via `@memmove` before refilling `buf[tail..cap]` in one `read_out` call.

For scatter-gather output, `IoSlice` uses target-conditional `@repr(C)` fields (`{ ptr: *u8, len_usize: usize }` matching POSIX `struct iovec` and `wasm32` WASI `__wasi_ciovec_t`, and `{ len_u32: u32, _pad: u32, ptr: *u8 }` matching Win64 `WSABUF`, clamping individual slice construction on Windows to `u32.MAX`). On POSIX and WASI, `File.write_vectored` passes `bufs` directly to `writev` (clamped to `IOV_MAX = 1024` / Darwin `UIO_MAXIOV = 1024` to prevent `EINVAL` per `rust#68042`) and `fd_write` (clamped to `128` `ciovec`s). On Windows, `WSABUF` passes directly to `WSASend` on sockets (`cx.net`), whereas regular Win32 `File` handles cannot use `WriteFileGather` on unaligned byte slices; `File.write_vectored` therefore skips leading zero-length `IoSlice`s (avoiding the zero-write trap in `rust#58452`) and writes the first non-empty buffer, while `BufWriter.write_vectored` coalesces small scatter slices into its contiguous `8 KiB` buffer in user space for a single `WriteFile` syscall. Standard streams (`stdin_locked`, `stdout_locked`, `stderr_locked`) acquire process-global futex locks guarding static `.bss` buffers (`8 KiB` each; `stdout` auto-detects TTY line-buffering on first lock via `isatty` / `GetConsoleMode`) and return `@linear` lock guards whose `.release()` (or `.flush_and_release()`) must be called or `defer`-bound (`E0304`).

---

### 1.2 Register-Sized 8-Byte `IoError` & `FsError` and Cross-OS Filesystem Architecture

Under `DR-07` §4.1B and `DR-20` `Fix-07`, CoreX lowers `T!E` across function calls onto unmodified LLVM 20–23 `swiftcc` + `swifterror`, which reserves a single 64-bit general-purpose register (`R12` on `x86_64`, `X21` on `aarch64`, `X19` on `Arm64EC`) for the error word (`0` = `.Ok`, non-zero = `.Err`) alongside four payload registers. In memory (`ReprStorage` Tier 2), returning `&[u8]!FsError` (`16 B`) or `PathBuf!FsError` (`24 B`) stashes `FsError` inside word 1 whenever word 0's non-null pointer niche is `0x0`. Both `IoError` and `FsError` therefore use an identical **8-byte (`u64`) bit-packed layout** where `packed_repr != 0` and `(packed_repr & 1) == 0` always hold: when `bits[1:0] == 0b00`, the word is a non-null pointer (`align >= 4`) to a `@cold_box` custom diagnostic; when `bits[1:0] == 0b10` (`InlineSys`), `bits[7:2]` store `ErrDomain` (`Generic`, `PosixErrno`, `Win32Error`, `NtStatus`, `WasiErrno`, `SimFault`), `bits[15:8]` store `IoErrorKind`, `bits[23:16]` store `IoOp`, `bits[31:24]` store an optional thread-local `Context.diagnostics` path-ring index, and `bits[63:32]` store the unmodified 32-bit OS error code (`errno`, Win32 `DWORD`, `NTSTATUS`, or `__wasi_errno_t`). Upcasting `FsError` to `IoError` via `?` is a zero-instruction register alias, and `bit[0] == 1` remains free as a 1-bit niche so `IoError?`, `FsError?`, and `i32!IoError` each occupy 8 bytes.

> **Visual – Thresholded VFS Loading, Capability-Jailed Opens, and Atomic UnlinkAndReplace Across Four OS Families:** **Top:** Both *FsError* (8 B, pinned in *R12*/*X21*) and *PathBuf* (24 B inline SSO up to 23 bytes) eliminate heap traffic on VFS metadata and open paths. **Middle:** *cx.fs.load_source* routes files below 16 KiB (including 0-byte files where *mmap* fails with *EINVAL*) into a single *Arena* read with an explicit trailing NUL byte, while mapping larger files read-only via *@linear Mmap*. **Bottom:** Cross-OS primitives enforce kernel-level traversal sandboxing, fresh-inode atomic publishing, and copy-on-write extent sharing.

In `cx.path`, `Path` (`16 B` borrowed byte slice) and `PathBuf` (`24 B` `AutoDrop` SSO container storing paths `<= 23` bytes inline, identical to `cx.str.String`) represent raw POSIX/WASI bytes on Unix/WASI and **well-formed WTF-8** on Windows. Because WTF-8 is a strict superset of UTF-8 that encodes unpaired UTF-16 surrogates (`0xD800..0xDFFF`) as generalized 3-byte sequences while forbidding 6-byte CESU-8 surrogate pairs, every `str` converts to `Path` in zero instructions and arbitrary ill-formed NTFS `WCHAR` sequences round-trip losslessly. Purely lexical normalization (`Path.normalize_lexical`) collapses redundant separators and `.` segments and resolves `..` only across non-`..` `Normal` components without touching the filesystem (preserving leading `..` on relative paths and clamping `..` at `RootDir` on absolute paths, though note that lexical `a/symlink/..` differs semantically from OS symlink resolution). For true physical resolution (`AGENTS.md` §6), `resolve_path` invokes `realpath` / `/proc/self/fd` on Linux, `open(O_RDONLY | O_CLOEXEC)` + `fcntl(fd, F_GETPATH, buf)` on macOS (restoring canonical APFS case), `CreateFileW(FILE_FLAG_BACKUP_SEMANTICS)` + `GetFinalPathNameByHandleW(..., VOLUME_NAME_DOS)` on Windows (stripping `\\?\` and converting `\\?\UNC\` back to `\\` unless verbatim promotion is required, while falling back to `GetFileAttributesExW` + lexical normalization on WSL `\\wsl.localhost\` / `\\wsl$\` Plan 9 paths where `GetFinalPathNameByHandleW` exhibits build-specific failures), and preopen prefix resolution + `path_readlink` on WASI. Its companion `resolve_or_create_path` creates missing target or parent directories (`CreateTargetKind`) via `create_dir_all` before resolving.

Across `cx.fs`, every subsystem is engineered around exact kernel invariants across all four OS families:

| Subsystem | Linux (`gnu` / `musl`) | macOS (`Darwin` / APFS) | Windows (`NTFS` / `ReFS`) | `wasm32-unknown-wasi` (`Preview 1`) |
| :--- | :--- | :--- | :--- | :--- |
| **Sandboxed `Dir.open_*_beneath`** | `openat2` (`syscall 437`) with `RESOLVE_BENEATH \| RESOLVE_NO_SYMLINKS \| RESOLVE_NO_MAGICLINKS` (`0x0E`); per-segment `O_NOFOLLOW` fallback on `< 5.6`. | Rejects lexical `..` escape, then `openat(dir_fd, rel, flags \| O_CLOEXEC \| O_NOFOLLOW_ANY)` (`0x20000000`). | Per-segment `NtCreateFile` (`RootDirectory = cur_h`, `FILE_OPEN_REPARSE_POINT`, `FILE_SHARE_READ\|WRITE\|DELETE`) + post-open `FileAttributeTagInfo` reparse rejection. | Rejects `/` and `..` underflow; `path_open(dirfd, dirflags: 0, rel, oflags, rights_base, rights_inh, fdflags)` (`SYMLINK_FOLLOW` unset). |
| **Thresholded Load (`16 KiB` Split)** | `0 B` → static `b"\0"[..0]`; `< 16 KiB` → `Arena` `pread` + `\0`; `>= 16 KiB` → `mmap(PROT_READ, MAP_PRIVATE)` (`MAP_FIXED` over-map if `size % page == 0`). | Same as Linux (`mmap` with `MAP_PRIVATE`; `4 KiB` x86_64 / `16 KiB` Apple Silicon `sysconf(_SC_PAGESIZE)` alignment). | `< 16 KiB` → `ReadFile` into `Arena` + `\0`; `>= 16 KiB` → `CreateFileMappingW(PAGE_READONLY)` + `MapViewOfFile(FILE_MAP_READ)` (`VirtualAlloc2` + `MapViewOfFile3` or `Arena` fallback if `size % 64 KiB == 0` & `nul_sentinel`). | Always single/loop `fd_pread` into `Arena` (`size + 1` with `\0` sentinel; WASI linear memory has no host file `mmap`). |
| **Atomic Publish (`UnlinkAndReplace`)** | Stage `.tmp` in target `dir_fd` → `fchmod` → `fdatasync` (`CrashSafe`) / `fsync`+`dir_fsync` (`PowerSafe`) → `renameat`. | Stage fresh inode `.tmp` (prevents XNU `cs_mtime != mtime` `SIGKILL`!) → `fchmod` → `F_BARRIERFSYNC` / `F_FULLFSYNC` → `renameat`. | Stage `.tmp` with `FILE_SHARE_DELETE` → `FlushFileBuffers` → `SetFileInformationByHandle(FileRenameInfoEx /*22*/, POSIX_SEMANTICS \| REPLACE)` + AV retry (`FileRenameInfo` / `MoveFileExW` fallback). | Stage `.tmp` via `path_open(CREAT\|EXCL)` → `fd_datasync` / `fd_sync` → `path_rename(dirfd, tmp, dirfd, dst)`. |
| **3-Tier CoW `materialize_file`** | **T1:** `ioctl(dst, FICLONE, src)` (`0x40049409`) → **T2:** `linkat` (`ImmutableCas`) → **T3:** `copy_file_range` → `64 KiB` loop. | **T1:** `clonefileat` + `renameat` → **T2:** `linkat` (`ImmutableCas`) → **T3:** `fcopyfile(COPYFILE_DATA)` → `64 KiB` loop. | **T1:** ReFS cluster-aligned `FSCTL_DUPLICATE_EXTENTS_TO_FILE` (`0x98344`, `< 4 GiB` chunks + tail write) → **T2:** `CreateHardLinkW` (`<= 1024` links) → **T3:** `CopyFileExW` / `64 KiB` loop. | **T2:** `path_link` (`ImmutableCas`) → **T3:** `64 KiB` `fd_read` / `fd_write` loop into staged `.tmp` + `path_rename`. |
| **Advisory `FileLock`** | `flock(fd, LOCK_EX/SH [\| LOCK_NB])` (`EWOULDBLOCK` → `.FileLockConflict`); never unlinks lockfile. | `flock(fd, LOCK_EX/SH [\| LOCK_NB])` (`EWOULDBLOCK` → `.FileLockConflict`). | `LockFileEx(h, [LOCKFILE_EXCLUSIVE_LOCK] [\| LOCKFILE_FAIL_IMMEDIATELY], 0, MAXDWORD, MAXDWORD, &ov0)` + `UnlockFileEx`. | Exclusive `OFLAGS_CREAT \| OFLAGS_EXCL` `.lock` sentinel file (or `.Unsupported` on shared locks). |
| **Change Watcher (`FsWatcher`)** | `inotify_init1(CLOEXEC\|NONBLOCK)` + recursive dir watches; `cookie` rename pairing; `IN_Q_OVERFLOW` → `rescan_required`. | **Recursive:** `FSEvents` (`FileEvents \| NoDefer \| WatchRoot` via `dlopen` `CoreServices`); **Single/Flat:** 1-fd `kqueue` (`O_EVTONLY`, checks `NOTE_RENAME` before `NOTE_WRITE`). | Overlapped `ReadDirectoryChangesW` (`64 KiB` buffer, `FILE_SHARE_DELETE`); cross-batch rename pairing; `ERROR_NOTIFY_ENUM_DIR` → `rescan_required`. | Returns `.Unsupported` (CLI `--watch` falls back cleanly to mtime/hash stat polling on WASI). |

Note two subtle Windows safety details reflected in the table above. First, Microsoft Q&A engineering clarifications note that `FILE_OPEN_REPARSE_POINT` is omitted from the documented compatible-options list for `FILE_DIRECTORY_FILE` in `NtCreateFile` and does not by itself promise callback-free refusal if a filter driver races during open; `Dir.open_*_beneath` on Windows therefore opens single-component relative `UNICODE_STRING`s against `OBJECT_ATTRIBUTES.RootDirectory` with `FILE_OPEN_REPARSE_POINT` and immediately verifies via handle metadata (`FileAttributeTagInfo`) that `FILE_ATTRIBUTE_REPARSE_POINT` is unset before advancing. Second, every file and directory open in `cx.fs` on Windows specifies `FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE`, which is the prerequisite for `SetFileInformationByHandle(..., FileRenameInfoEx, ...)` with `FILE_RENAME_FLAG_POSIX_SEMANTICS` to atomically replace files currently held open by `VfsSourceMap` or `FsWatcher` – a case where legacy `MoveFileExW(..., MOVEFILE_REPLACE_EXISTING)` fails with `ERROR_ACCESS_DENIED`.

---

### 1.3 Monotonic & Wall Clocks, Safe Environment Resolution, and Hardened Process Spawning

> **Visual – Overflow-Free Monotonic Scaling, Injection-Immune Process Spawning, and Deterministic Sim Routing:** **Top:** Multiplying raw hardware ticks by 10^9 in 64-bit arithmetic overflows in 18.45 seconds at 1 GHz and 12.8 minutes on Apple Silicon's 24 MHz counter; CoreX's quotient-remainder *u128* scaling preserves exact nanosecond monotonic precision for 584.5 years. **Middle:** On Windows, *cx.process.Command* resolves *.exe* targets explicitly into non-null *lpApplicationName*, blocks implicit *.bat*/*.cmd* execution (*CVE-2024-24576*), applies exact MSVCRT quoting, and deduplicates inherited pipe handles via *PROC_THREAD_ATTRIBUTE_HANDLE_LIST*. **Bottom:** Every OS boundary emits its *DR-17* capability bit at compile time and routes through *Context.reactor* for deterministic *--sim* execution.

In `cx.time`, `Instant` (`8 B` `mono_ns: u64`) queries `clock_gettime(CLOCK_MONOTONIC, &ts)` on Linux, `mach_continuous_time()` scaled by `mach_timebase_info` (or `clock_gettime_nsec_np(CLOCK_MONOTONIC_RAW)`, which Apple's `libSystem` maps to `mach_continuous_time` so monotonic intervals continue advancing across laptop sleep, unlike `mach_absolute_time` / `CLOCK_UPTIME_RAW` and Linux `CLOCK_MONOTONIC` which pause during suspend) on macOS, `QueryPerformanceCounter` / `QueryPerformanceFrequency` on Windows, and `clock_time_get(CLOCKID_MONOTONIC, 1, &ns)` on WASI. Because multiplying raw `u64` ticks by `1,000,000,000` overflows `2^64 - 1` after just `18.45 s` at `1 GHz`, `768.61 s` (`12.8 min`) at Apple Silicon's `24 MHz`, and `1,844.67 s` (`30.7 min`) at Windows 10/11's `10 MHz` QPC rate, `cx.time` computes `(ticks / freq) * 1_000_000_000 + (((ticks % freq) as u128 * 1_000_000_000) / (freq as u128)) as u64` (with branchless specialization for `10 MHz`, `24 MHz`, and `1 GHz`), providing 584.5 years of exact nanosecond uptime without calling 128-bit software division helpers. Wall-clock `SystemTime.now()` (`16 B`: signed `secs: i64` + `subsec_nanos: u32`) reads `CLOCK_REALTIME` on POSIX/WASI and `GetSystemTimePreciseAsFileTime` (offset by `11,644,473,600` seconds from `1601-01-01` to `1970-01-01`) on Windows, routed through `Context.reactor` so `--sim` controls both clocks deterministically.

In `cx.env`, mutating the process environment (`set_var`, `remove_var`) is marked `unsafe` in alignment with Rust 2024 Edition: POSIX `setenv`/`unsetenv` mutate global `char **environ` while C libraries invoke `getenv` without locks, creating multithreaded data races. Read-only `args_in(&mut arena)` slices Unix stack `argv` strings directly with zero heap allocations (and transcodes `GetCommandLineW` / `wasi.args_get` into `arena` on Windows/WASI). Standard directory resolution follows XDG on Linux (`$XDG_CACHE_HOME` if non-empty and absolute, else `$HOME/.cache`; `$XDG_CONFIG_HOME` → `$HOME/.config`; `$TMPDIR` → `/tmp`), Apple conventions on macOS (`$HOME/Library/Caches`, `$HOME/Library/Application Support`, `$TMPDIR` → `/tmp`), and `shell32.dll`-free lookups on Windows (`%LOCALAPPDATA%` with fallback to `advapi32!RegQueryValueExW` on `HKCU\Software\Microsoft\Windows\CurrentVersion\Explorer\User Shell Folders\Local AppData` + `ExpandEnvironmentStringsW` so `corex` never depends on `shell32.dll` outside `DR-10`'s bundled `.def` sysroot, and `GetTempPath2W` dynamically resolved from `kernel32.dll` with `GetTempPathW` fallback). Callers such as `pkg_cache` always append a subdirectory (`cache_dir()?.join("corex")`) rather than writing loose files into `%LOCALAPPDATA%` root.

In `cx.process`, POSIX spawning creates pipes with `O_CLOEXEC` (`pipe2` on Linux; `pipe` + `FD_CLOEXEC` under a spawn rwlock on macOS) and invokes `posix_spawn` with `POSIX_SPAWN_SETSIGDEF` / `POSIX_SPAWN_SETSIGMASK`. Because `posix_spawn_file_actions_addchdir` was newly standardized in POSIX.1-2024 (with `posix_spawn_file_actions_addchdir_np` deprecated in macOS 26.0 in favor of the standard symbol and absent on `glibc 2.17–2.28`, which includes `DR-10`'s `glibc 2.28` dynamic Linux baseline), `cx.process` resolves `posix_spawn_file_actions_addchdir` / `addchdir_np` weakly via `dlsym` and, when `cwd` is configured on `glibc <= 2.28`, falls back to `fork()` + `chdir` + `dup2` + `execve` with a `CLOEXEC` `errno` pipe reporting child `execve`/`chdir` failures cleanly to the parent. On Windows, `Command.spawn` eliminates `BatBadBut` (`CVE-2024-24576`, disclosed by RyotaK at Flatt Security): because `CreateProcessW` implicitly invokes `cmd.exe /c` on `.bat`/`.cmd` files – where `cmd.exe` expands `%CMDCMDLINE:~-1%` before quote parsing and breaks out of backslash-escaped quotes – `Command.new` searches `PATH` strictly for `.exe` (ignoring `PATHEXT`), passes the resolved absolute path in `lpApplicationName` (never `NULL`), and fails closed with `IoErrorKind.ProcessBatchRejected` on `.bat`/`.cmd` targets. When a developer explicitly opts into `Command.cmd_script(batch_path)`, `cx.process` invokes `System32\cmd.exe /d /v:off /e:on /c` directly and rejects `\r`/`\n`/`\0` while neutralizing `%` as `%%cd:~,%` and doubling quotes. Finally, `STARTUPINFOEXW` passes a deduplicated `PROC_THREAD_ATTRIBUTE_HANDLE_LIST` (`0x00020002`) filtering out `NULL`, `INVALID_HANDLE_VALUE`, and pre-Win8 console pseudohandles so concurrent threads never leak pipe handles into sibling children or trigger `CreateProcessW` `ERROR_INVALID_PARAMETER`.

---

## 2. Deliverable 1: Complete Canonical `.cx` Public API Signatures

Every signature below adheres strictly to **CoreX v1.0 (`DR-21` + `DR-22`)** canonical syntax: `cx.*` namespace, unified `.` paths, payload-first `T!E` and `T?`, `and`/`or`/`not`/`~`, `let`/`var`, `&T`/`&mut T`/`own T`/`&out T`, `/` and `*` parameter zones, `,`-separated `struct`/`enum`/`bit_field` members (every `bit_field` verified to sum to exact `16`, `32`, or `64` bits per `E0423`), `*T`/`*mut T`/`*opaque`, `@std_cap_boundary`, and `AGENTS.md` §6 `resolve_path` / `resolve_or_create_path` naming.

### 2.1 `stdlib/cx/io.cx`

```rust
// File: stdlib/cx/io.cx
mod io;

use cx.mem.Arena;

// ============================================================================
// 1. COMPACT 8-BYTE REGISTER-SAFE `IoError` (`swifterror` R12/X21 Compatible)
//    Invariants: packed_repr != 0 and (packed_repr & 1) == 0 always!
//    • bits[1:0] == 0b00: non-null *ColdIoDiag (@cold_box aligned >= 4B)
//    • bits[1:0] == 0b10: inline OS/kind error (0 heap allocs!)
// ============================================================================
@derive(Copy, Equatable)
pub enum ErrDomain: u8 {
    Generic    = 0,
    PosixErrno = 1,
    Win32Error = 2,
    NtStatus   = 3,
    WasiErrno  = 4,
    SimFault   = 5,
}

@derive(Copy, Equatable)
pub enum IoErrorKind: u8 {
    NotFound             = 0,
    PermissionDenied     = 1,
    AlreadyExists        = 2,
    WouldBlock           = 3,
    Interrupted          = 4,
    TimedOut             = 5,
    UnexpectedEof        = 6,
    WriteZero            = 7,
    BrokenPipe           = 8,
    InvalidInput         = 9,
    InvalidData          = 10,
    DirectoryNotEmpty    = 11,
    IsADirectory         = 12,
    NotADirectory        = 13,
    CrossesDevices       = 14,
    FilesystemLoop       = 15,
    FileLockConflict     = 16,
    ResourceBusy         = 17,
    StorageFull          = 18,
    StreamTooLong        = 19,
    ProcessBatchRejected = 20,
    Unsupported          = 21,
    Cancelled            = 22,
    Other                = 255,
}

@derive(Copy, Equatable)
pub enum IoOp: u8 {
    None    = 0,
    Read    = 1,
    Write   = 2,
    Flush   = 3,
    Seek    = 4,
    Open    = 5,
    Stat    = 6,
    Resolve = 7,
    Rename  = 8,
    Unlink  = 9,
    Mkdir   = 10,
    Readdir = 11,
    Clone   = 12,
    Mmap    = 13,
    Lock    = 14,
    Watch   = 15,
    Spawn   = 16,
    Wait    = 17,
}

// Exact 64-bit bitfield (2 + 6 + 8 + 8 + 8 + 32 = 64 bits)
pub bit_field IoErrorBits: u64 {
    pub tag: u8           | 2,
    pub domain: ErrDomain | 6,
    pub kind: IoErrorKind | 8,
    pub op: IoOp          | 8,
    pub diag_slot: u8     | 8,
    pub raw_code: u32     | 32,
}

@repr(C)
@derive(Copy, Equatable)
pub struct IoError {
    packed_repr: u64,
}

impl IoError {
    @inline @no_alloc @no_panic
    pub fn from_kind(kind: IoErrorKind, /, *, op: IoOp = .None) -> Self;

    @inline @no_alloc @no_panic
    pub fn from_raw_os(raw_code: i32, /, *, domain: ErrDomain, op: IoOp = .None) -> Self;

    @cold
    pub fn custom(kind: IoErrorKind, message: str, /, *, op: IoOp = .None) -> Self;

    @inline @no_alloc @no_panic
    pub fn kind(self) -> IoErrorKind;

    @inline @no_alloc @no_panic
    pub fn op(self) -> IoOp;

    @inline @no_alloc @no_panic
    pub fn os_error(self) -> i32?;

    @no_alloc @no_panic
    pub fn message(self) -> str;
}

// ============================================================================
// 2. ZERO-MEMSET `OutBuf` (`&out [u8]`) & ABI-EXACT `IoSlice` (`iovec`/`WSABUF`)
// ============================================================================
pub struct OutBuf {
    ptr: *mut u8,
    cap: usize,
    filled_len: usize,
}

impl OutBuf {
    @inline @no_alloc @no_panic
    pub fn over_uninit[const N: usize](buf: &out [u8; N], /) -> Self;

    @inline @no_alloc @no_panic
    pub fn over_slice(buf: &mut [u8], /) -> Self;

    @inline @no_alloc @no_panic
    pub unsafe fn from_raw_parts(ptr: *mut u8, cap: usize, /) -> Self;

    @inline @no_alloc @no_panic
    pub fn capacity(&self) -> usize = self.cap;

    @inline @no_alloc @no_panic
    pub fn filled_len(&self) -> usize = self.filled_len;

    @inline @no_alloc @no_panic
    pub fn remaining(&self) -> usize = self.cap - self.filled_len;

    @inline @no_alloc @no_panic
    pub fn filled(&self) -> &[u8];

    @inline @no_alloc @no_panic
    pub fn clear(&mut self) { self.filled_len = 0; }

    @inline @no_alloc @no_panic
    pub fn append(&mut self, src: &[u8], /) -> usize;

    @inline @no_alloc @no_panic
    pub fn unfilled_raw(&mut self) -> (*mut u8, usize);

    @inline @no_alloc @no_panic
    pub unsafe fn advance_init(&mut self, n: usize, /);
}

/// Scatter-gather slice ABI-compatible with POSIX `iovec` (16B), WASI `ciovec` (8B), & Win64 `WSABUF` (16B).
@cfg(target.os == .Windows)
@repr(C)
@derive(Copy)
pub struct IoSlice {
    len_u32: u32,
    _pad: u32 = 0,
    ptr: *u8,
}

@cfg(target.os is not .Windows)
@repr(C)
@derive(Copy)
pub struct IoSlice {
    ptr: *u8,
    len_usize: usize,
}

impl IoSlice {
    @inline @no_alloc @no_panic
    pub fn new(slice: &[u8], /) -> Self;

    @inline @no_alloc @no_panic
    pub fn as_slice(self) -> &[u8];

    @inline @no_alloc @no_panic
    pub fn len(self) -> usize;

    @inline @no_alloc @no_panic
    pub fn is_empty(self) -> bool = self.len() == 0;

    @no_alloc @no_panic
    pub fn advance_slices(slices: &mut &[IoSlice], n: usize, /);
}

@derive(Copy, Equatable)
pub enum SeekFrom {
    Start(u64),
    End(i64),
    Current(i64),
}

// ============================================================================
// 3. EXPLICIT `{ ctx, vtable }` `Reader` & `Writer` HANDLES (MVS-Safe, 16B)
// ============================================================================
@repr(C)
pub struct ReaderVTable {
    pub read_out: fn(*mut opaque, &mut OutBuf) -> usize!IoError,
    pub discard: (fn(*mut opaque, u64) -> u64!IoError)? = .None,
}

@repr(C)
@derive(Copy)
pub struct Reader {
    pub(pkg) ctx: *mut opaque,
    pub(pkg) vtable: *ReaderVTable,
}

impl Reader {
    @inline @no_alloc @no_panic
    pub unsafe fn from_raw(ctx: *mut opaque, vtable: *ReaderVTable, /) -> Self =
        Self { ctx: ctx, vtable: vtable };

    pub fn from_bytes(cursor: &mut ByteReader, /) -> Self;

    @inline
    pub fn read_out(&mut self, out: &mut OutBuf, /) -> usize!IoError;

    @inline
    pub fn read(&mut self, buf: &mut [u8], /) -> usize!IoError;

    pub fn read_exact(&mut self, buf: &mut [u8], /) -> unit!IoError;
    pub fn read_exact_out(&mut self, out: &mut OutBuf, exact_len: usize, /) -> unit!IoError;
    pub fn read_to_end(&mut self, dst: &mut Vec[u8], /, *, max_bytes: usize = usize.MAX) -> usize!IoError;
    pub fn read_all_arena(&mut self, arena: &mut Arena, /, *, max_bytes: usize = usize.MAX) -> &[u8]!IoError;
    pub fn discard(&mut self, bytes: u64, /) -> u64!IoError;
}

@repr(C)
pub struct WriterVTable {
    pub write: fn(*mut opaque, &[u8]) -> usize!IoError,
    pub write_vectored: (fn(*mut opaque, &[IoSlice]) -> usize!IoError)? = .None,
    pub flush: (fn(*mut opaque) -> unit!IoError)? = .None,
}

@repr(C)
@derive(Copy)
pub struct Writer {
    pub(pkg) ctx: *mut opaque,
    pub(pkg) vtable: *WriterVTable,
}

impl Writer {
    @inline @no_alloc @no_panic
    pub unsafe fn from_raw(ctx: *mut opaque, vtable: *WriterVTable, /) -> Self =
        Self { ctx: ctx, vtable: vtable };

    pub fn sink() -> Self;
    pub fn over_slice(cursor: &mut SliceWriter, /) -> Self;

    @inline
    pub fn write(&mut self, buf: &[u8], /) -> usize!IoError;

    pub fn write_all(&mut self, buf: &[u8], /) -> unit!IoError;
    pub fn write_byte(&mut self, b: u8, /) -> unit!IoError;
    pub fn write_splat(&mut self, byte: u8, count: usize, /) -> unit!IoError;
    pub fn write_vectored(&mut self, bufs: &[IoSlice], /) -> usize!IoError;
    pub fn write_all_vectored(&mut self, var bufs: &[IoSlice], /) -> unit!IoError;
    pub fn print(&mut self, args: FmtArgs, /) -> unit!IoError;
    pub fn flush(&mut self) -> unit!IoError;
}

// ============================================================================
// 4. ZERO-HEAP BUFFER-FIRST `BufReader` (48B), `BufWriter` (32B) & ADAPTERS
// ============================================================================
pub const DEFAULT_IO_BUF_SIZE: usize = 8_192;

/// Exact 48-byte zero-heap-allocation buffered reader (`16B` Reader + `16B` slice + `8B` pos + `8B` filled).
@repr(C)
pub struct BufReader {
    upstream: Reader,
    buf_ptr: *mut u8,
    buf_cap: usize,
    pos: usize,
    filled: usize,
}

impl BufReader {
    @inline @no_alloc @no_panic
    pub fn over_uninit[const N: usize](upstream: Reader, backing: &out [u8; N], /) -> Self;

    @inline @no_alloc @no_panic
    pub fn over_slice(upstream: Reader, backing: &mut [u8], /) -> Self;

    pub fn in_arena(arena: &mut Arena, upstream: Reader, /, *, cap: usize = DEFAULT_IO_BUF_SIZE) -> Self;

    @inline @no_alloc @no_panic
    pub fn available(&self) -> usize = self.filled - self.pos;

    @inline @no_alloc @no_panic
    pub fn capacity(&self) -> usize = self.buf_cap;

    @inline @no_alloc @no_panic
    pub fn buffered(&self) -> &[u8];

    pub fn peek(&mut self, min_bytes: usize = 1, /) -> &[u8]!IoError;

    @inline @no_alloc @no_panic
    pub fn consume(&mut self, n: usize, /);

    pub fn read_until(&mut self, delim: u8, /) -> &[u8]?!IoError;
    pub fn read_until_into(&mut self, delim: u8, dst: &mut Vec[u8], /, *, max_bytes: usize = 1_048_576) -> usize!IoError;
    pub fn next_line(&mut self) -> str?!IoError;
    pub fn as_reader(&mut self) -> Reader;
}

/// Exact 32-byte zero-heap-allocation buffered writer (`16B` Writer + `8B` ptr + `4B` filled + `4B` cap|flags).
@repr(C)
pub struct BufWriter {
    downstream: Writer,
    buf_ptr: *mut u8,
    filled: u32,
    cap_and_flags: u32, // Bits 0..30: capacity (up to 2 GiB - 1); Bit 31: line_buffered
}

impl BufWriter {
    @inline @no_alloc @no_panic
    pub fn over_uninit[const N: usize](
        downstream: Writer,
        backing: &out [u8; N],
        /,
        *,
        line_buffered: bool = false,
    ) -> Self;

    @inline @no_alloc @no_panic
    pub fn over_slice(downstream: Writer, backing: &mut [u8], /, *, line_buffered: bool = false) -> Self;

    pub fn in_arena(
        arena: &mut Arena,
        downstream: Writer,
        /,
        *,
        cap: u32 = 8_192,
        line_buffered: bool = false,
    ) -> Self;

    @inline @no_alloc @no_panic
    pub fn buffered_len(&self) -> usize = self.filled as usize;

    @inline @no_alloc @no_panic
    pub fn capacity(&self) -> usize = (self.cap_and_flags & 0x7FFF_FFFF_u32) as usize;

    @inline @no_alloc @no_panic
    pub fn spare_capacity(&self) -> usize = self.capacity() - self.buffered_len();

    @inline @no_alloc @no_panic
    pub fn is_line_buffered(&self) -> bool = (self.cap_and_flags >> 31) != 0;

    pub fn write(&mut self, data: &[u8], /) -> usize!IoError;
    pub fn write_all(&mut self, data: &[u8], /) -> unit!IoError;
    pub fn write_byte(&mut self, b: u8, /) -> unit!IoError;
    pub fn write_vectored(&mut self, bufs: &[IoSlice], /) -> usize!IoError;
    pub fn write_all_vectored(&mut self, bufs: &[IoSlice], /) -> unit!IoError;
    pub fn print(&mut self, args: FmtArgs, /) -> unit!IoError;
    pub fn flush(&mut self) -> unit!IoError;
    pub fn as_writer(&mut self) -> Writer;
}

pub struct LimitReader {
    upstream: Reader,
    remaining_bytes: u64,
}

impl LimitReader {
    @inline @no_alloc @no_panic
    pub fn new(upstream: Reader, limit: u64, /) -> Self =
        Self { upstream: upstream, remaining_bytes: limit };

    @inline @no_alloc @no_panic
    pub fn remaining(&self) -> u64 = self.remaining_bytes;

    pub fn read_out(&mut self, out: &mut OutBuf, /) -> usize!IoError;
    pub fn as_reader(&mut self) -> Reader;
}

pub struct ByteReader {
    data: &[u8],
    pos: usize = 0,
}

pub struct SliceWriter {
    ptr: *mut u8,
    cap: usize,
    pos: usize = 0,
}

pub fn copy_stream(src: &mut Reader, dst: &mut Writer, /, *, max_bytes: u64 = u64.MAX) -> u64!IoError;

// ============================================================================
// 5. LOCKED BUFFERED STANDARD STREAMS (`stdin`, `stdout`, `stderr`)
// ============================================================================
@linear
pub struct StdinLock {
    reader: BufReader,
    lock_token: usize,
}

impl StdinLock {
    @inline @no_alloc @no_panic
    pub fn reader(&mut self) -> &mut BufReader = &mut self.reader;
    pub fn release(own self);
}

@linear
pub struct StdoutLock {
    writer: BufWriter,
    lock_token: usize,
}

impl StdoutLock {
    @inline @no_alloc @no_panic
    pub fn writer(&mut self) -> &mut BufWriter = &mut self.writer;
    pub fn write_all(&mut self, data: &[u8], /) -> unit!IoError;
    pub fn print(&mut self, args: FmtArgs, /) -> unit!IoError;
    pub fn flush(&mut self) -> unit!IoError;
    pub fn flush_and_release(own self) -> unit!IoError;
    pub fn release(own self);
}

pub type StderrLock = StdoutLock;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn stdin_locked() -> StdinLock;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn stdout_locked() -> StdoutLock;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn stderr_locked() -> StderrLock;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn print(args: FmtArgs, /);

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn println(args: FmtArgs = "", /);

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn eprint(args: FmtArgs, /);

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn eprintln(args: FmtArgs = "", /);
```

---

### 2.2 `stdlib/cx/path.cx`

```rust
// File: stdlib/cx/path.cx
mod path;

use cx.mem.Arena;

pub const MAIN_SEPARATOR: char = if target.os == .Windows { '\\' } else { '/' };
pub const MAIN_SEPARATOR_BYTE: u8 = if target.os == .Windows { b'\\' } else { b'/' };
pub const PATH_LIST_SEPARATOR: u8 = if target.os == .Windows { b';' } else { b':' };

@derive(Copy, Equatable)
pub enum PathPrefix {
    Verbatim(&[u8]),                              // `\\?\label`
    VerbatimUnc { server: &[u8], share: &[u8] },  // `\\?\UNC\server\share`
    VerbatimDisk(u8),                             // `\\?\C:` (uppercase ASCII drive letter)
    DeviceNs(&[u8]),                              // `\\.\PIPE`
    Unc { server: &[u8], share: &[u8] },          // `\\server\share`
    Disk(u8),                                     // `C:` (uppercase ASCII drive letter)
}

@derive(Copy, Equatable)
pub enum Component {
    Prefix(PathPrefix),
    RootDir,
    CurDir,
    ParentDir,
    Normal(&[u8]),
}

/// Borrowed OS path slice (16 bytes: `{ ptr: *u8, len: usize }`; UTF-8 on Unix/WASI, WTF-8 on Windows).
@repr(C)
@derive(Copy, Equatable)
pub struct Path {
    bytes: &[u8],
}

impl Path {
    @inline @no_alloc @no_panic
    pub fn new[S: str | &[u8]](s: S, /) -> Self;

    @inline @no_alloc @no_panic
    pub fn as_os_bytes(self) -> &[u8] = self.bytes;

    @no_alloc @no_panic
    pub fn to_str(self) -> str?;

    pub fn to_str_lossy_in(self, arena: &mut Arena, /) -> str;

    @inline @no_alloc @no_panic
    pub fn len(self) -> usize = self.bytes.len();

    @inline @no_alloc @no_panic
    pub fn is_empty(self) -> bool = self.bytes.is_empty();

    @no_alloc @no_panic
    pub fn is_absolute(self) -> bool;

    @no_alloc @no_panic
    pub fn is_relative(self) -> bool = not self.is_absolute();

    @no_alloc @no_panic
    pub fn has_root(self) -> bool;

    @no_alloc @no_panic
    pub fn prefix(self) -> PathPrefix?;

    @no_alloc @no_panic
    pub fn parent(self) -> Path?;

    @no_alloc @no_panic
    pub fn file_name(self) -> &[u8]?;

    @no_alloc @no_panic
    pub fn file_stem(self) -> &[u8]?;

    @no_alloc @no_panic
    pub fn extension(self) -> &[u8]?;

    @no_alloc @no_panic
    pub fn starts_with(self, base: Path, /) -> bool;

    @no_alloc @no_panic
    pub fn ends_with(self, child: Path, /) -> bool;

    @no_alloc @no_panic
    pub fn strip_prefix(self, base: Path, /) -> Path?;

    @no_alloc @no_panic
    pub fn components(self) -> ComponentsIter;

    pub fn join(self, child: Path, /) -> PathBuf;
    pub fn join_in(self, arena: &mut Arena, child: Path, /) -> Path;
    pub fn with_file_name(self, name: str, /) -> PathBuf;
    pub fn with_extension(self, ext: str, /) -> PathBuf;

    /// Purely lexical `.` / `..` & separator normalization (EffectCapabilityMask = PURE, zero OS syscalls).
    pub fn normalize_lexical(self) -> PathBuf;
    pub fn normalize_lexical_in(self, arena: &mut Arena, /) -> Path;

    pub fn to_path_buf(self) -> PathBuf;
}

/// 24-byte `AutoDrop` Small-String-Optimized owned path (`<= 23` bytes stored inline with 0 heap allocs).
@repr(C)
pub struct PathBuf {
    raw_words: [u64; 3],
}

impl PathBuf {
    pub const INLINE_CAP: usize = 23;

    @inline @no_alloc @no_panic
    pub fn new() -> Self;

    pub fn from[S: str | &[u8] | Path](src: S, /) -> Self;
    pub fn in_arena(arena: &mut Arena, /, *, cap: usize = 64) -> Self;
    pub fn with_capacity(cap: usize, /) -> Self;

    @inline @no_alloc @no_panic
    pub fn as_path(&self) -> Path;

    @inline @no_alloc @no_panic
    pub fn as_os_bytes(&self) -> &[u8];

    @no_alloc @no_panic
    pub fn to_str(&self) -> str?;

    @inline @no_alloc @no_panic
    pub fn len(&self) -> usize;

    @inline @no_alloc @no_panic
    pub fn is_empty(&self) -> bool = self.len() == 0;

    pub fn push[P: str | Path](&mut self, child: P, /);
    pub fn pop(&mut self) -> bool;
    pub fn set_file_name(&mut self, name: str, /);
    pub fn set_extension(&mut self, ext: str, /) -> bool;
    pub fn clear(&mut self);
}

pub struct ComponentsIter {
    raw: &[u8],
    front_idx: usize,
    back_idx: usize,
    state: u8,
}

impl ComponentsIter {
    @no_alloc @no_panic
    pub fn next(&mut self) -> Component?;

    @no_alloc @no_panic
    pub fn as_path(&self) -> Path;
}

@cfg(target.os == .Windows)
pub(pkg) mod win_wtf {
    use super.{Path, PathBuf};
    use cx.io.IoError;
    use cx.mem.Arena;

    pub const STACK_WCHAR_CAP: usize = 512;

    @derive(Copy, Equatable)
    pub enum VerbatimMode: u8 {
        AutoPromote = 0, // Promotes >= 248 WCHARs, DOS device stems, or trailing space/dot
        Always      = 1, // Always emits `\\?\C:\...` or `\\?\UNC\...`
        NtNamespace = 2, // Emits `\??\C:\...` for `ntdll!NtCreateFile`
    }

    @no_alloc @no_panic
    pub fn needs_verbatim_prefix(wtf8: &[u8], /) -> bool;

    @no_alloc @no_panic
    pub fn encode_wtf8_to_wtf16(wtf8: &[u8], out_u16: &mut [u16], /) -> usize!IoError;

    pub fn decode_wtf16_to_path_buf(wtf16: &[u16], /) -> PathBuf;
    pub fn decode_wtf16_in_arena(arena: &mut Arena, wtf16: &[u16], /) -> Path;
}
```

---

### 2.3 `stdlib/cx/fs.cx`

```rust
// File: stdlib/cx/fs.cx
mod fs;

use cx.io.{IoError, IoErrorKind, IoOp, IoSlice, OutBuf, Reader, SeekFrom, Writer};
use cx.mem.Arena;
use cx.path.{Path, PathBuf};
use cx.time.{Duration, SystemTime};

// ============================================================================
// 1. COMPACT 8-BYTE `FsError` (Isomorphic to `IoError`, `swifterror` 1-Reg Fit)
// ============================================================================
@repr(C)
@derive(Copy, Equatable)
pub struct FsError {
    packed_repr: u64,
}

impl FsError {
    @inline @no_alloc @no_panic
    pub fn from_io(err: IoError, /, *, op: IoOp = .None) -> Self;

    @inline @no_alloc @no_panic
    pub fn from_kind(kind: IoErrorKind, /, *, op: IoOp = .None) -> Self;

    @inline @no_alloc @no_panic
    pub fn into_io_error(self) -> IoError;

    @inline @no_alloc @no_panic
    pub fn kind(self) -> IoErrorKind;

    @inline @no_alloc @no_panic
    pub fn op(self) -> IoOp;

    @inline @no_alloc @no_panic
    pub fn os_error(self) -> i32?;

    @no_alloc @no_panic
    pub fn failed_path(self) -> Path?;

    @no_alloc @no_panic
    pub fn message(self) -> str;
}

impl FromError[IoError] for FsError {
    @inline @no_alloc @no_panic
    fn from_error(src: own IoError) -> FsError = FsError.from_io(src);
}

impl FromError[FsError] for IoError {
    @inline @no_alloc @no_panic
    fn from_error(src: own FsError) -> IoError = src.into_io_error();
}

// ============================================================================
// 2. METADATA, PERMISSIONS & OPEN OPTIONS (`bit_field` Widths Verified)
// ============================================================================
@derive(Copy, Equatable)
pub enum FileType: u8 {
    RegularFile = 0,
    Directory   = 1,
    Symlink     = 2,
    Fifo        = 3,
    Socket      = 4,
    CharDevice  = 5,
    BlockDevice = 6,
    Unknown     = 255,
}

// Exact 32-bit bitfield (16 + 1 + 1 + 14 = 32 bits)
@derive(Copy, Equatable)
pub bit_field FilePermissions: u32 {
    pub posix_mode: u16  | 16,
    pub readonly: bool   | 1,
    pub executable: bool | 1,
    _reserved: u16       | 14,
}

impl FilePermissions {
    pub const DEFAULT_FILE: FilePermissions = FilePermissions {
        posix_mode: 0o644, readonly: false, executable: false, _reserved: 0,
    };
    pub const DEFAULT_EXE: FilePermissions = FilePermissions {
        posix_mode: 0o755, readonly: false, executable: true, _reserved: 0,
    };
    pub const DEFAULT_DIR: FilePermissions = FilePermissions {
        posix_mode: 0o755, readonly: false, executable: true, _reserved: 0,
    };
}

@derive(Copy, Equatable)
pub struct Metadata {
    pub file_type: FileType,
    pub size: u64,
    pub permissions: FilePermissions,
    pub modified: SystemTime?,
    pub accessed: SystemTime?,
    pub created: SystemTime?,
    pub dev_id: u64,
    pub inode_or_file_id: u64,
    pub hardlink_count: u32,
}

// Exact 16-bit bitfield (11 * 1 + 5 = 16 bits)
@derive(Copy, Equatable)
pub bit_field OpenFlags: u16 {
    pub read: bool             | 1,
    pub write: bool            | 1,
    pub append: bool           | 1,
    pub create: bool           | 1,
    pub create_new: bool       | 1,
    pub truncate: bool         | 1,
    pub no_follow: bool        | 1,
    pub sync_data: bool        | 1,
    pub lock_shared: bool      | 1,
    pub lock_exclusive: bool   | 1,
    pub nonblocking_lock: bool | 1,
    _reserved: u8              | 5,
}

@derive(Copy, Equatable)
pub struct OpenOptions {
    pub flags: OpenFlags = OpenFlags {
        read: true, write: false, append: false, create: false, create_new: false,
        truncate: false, no_follow: false, sync_data: false, lock_shared: false,
        lock_exclusive: false, nonblocking_lock: false, _reserved: 0,
    },
    pub permissions: FilePermissions = FilePermissions.DEFAULT_FILE,
}

@derive(Copy, Equatable)
pub enum DurabilityMode: u8 {
    FastLocal = 0, // Page-cache atomic rename only (0 ms NVMe flush; intermediate .o/exe)
    CrashSafe = 1, // Linux fdatasync / macOS F_BARRIERFSYNC / Win32 FlushFileBuffers
    PowerSafe = 2, // Linux fsync+dir_fsync / macOS F_FULLFSYNC+dir_fsync / Win32 FlushFileBuffers
}

// ============================================================================
// 3. `@linear File` & CAPABILITY-RELATIVE `@linear Dir` (`E0304` Leak-Proof)
// ============================================================================
pub type RawOsFd = if target.os == .Windows { *mut opaque } else { i32 };

@linear
pub struct File {
    pub(pkg) raw_fd: RawOsFd,
}

impl File {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn open[P: str | Path](path: P, /) -> File!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn create[P: str | Path](path: P, /) -> File!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn open_with[P: str | Path](path: P, opts: OpenOptions, /) -> File!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn close(own self);

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn read_out(&mut self, out: &mut OutBuf, /) -> usize!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn read(&mut self, buf: &mut [u8], /) -> usize!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn pread_out(&self, out: &mut OutBuf, offset: u64, /) -> usize!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn write(&mut self, buf: &[u8], /) -> usize!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn write_all(&mut self, buf: &[u8], /) -> unit!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn pwrite_all(&self, buf: &[u8], offset: u64, /) -> unit!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn write_vectored(&mut self, bufs: &[IoSlice], /) -> usize!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn seek(&mut self, pos: SeekFrom, /) -> u64!IoError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn set_len(&mut self, size: u64, /) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn set_permissions(&mut self, perms: FilePermissions, /) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn sync(&mut self, mode: DurabilityMode = .CrashSafe, /) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn metadata(&self) -> Metadata!FsError;

    pub fn as_reader(&mut self) -> Reader;
    pub fn as_writer(&mut self) -> Writer;
}

@linear
pub struct Dir {
    pub(pkg) raw_fd: RawOsFd,
}

impl Dir {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn open[P: str | Path](path: P, /) -> Dir!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn cwd() -> Dir!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn close(own self);

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn open_file_beneath[P: str | Path](
        &self,
        rel_path: P,
        opts: OpenOptions = OpenOptions { .. },
        /,
    ) -> File!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn open_dir_beneath[P: str | Path](&self, rel_path: P, /) -> Dir!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn create_dir_beneath[P: str | Path](
        &self,
        rel_path: P,
        /,
        *,
        perms: FilePermissions = FilePermissions.DEFAULT_DIR,
    ) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn unlink_file_beneath[P: str | Path](&self, rel_path: P, /) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn metadata_beneath[P: str | Path](
        &self,
        rel_path: P,
        /,
        *,
        follow_symlinks: bool = false,
    ) -> Metadata!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn entries(&self) -> DirIter!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn sync(&self) -> unit!FsError;
}

pub struct DirEntry {
    pub name: PathBuf,
    pub file_type: FileType,
    pub inode_or_file_id: u64,
}

@linear
pub struct DirIter {
    raw_state: *mut opaque,
}

impl DirIter {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn next(&mut self) -> DirEntry?!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn close(own self);
}

// ============================================================================
// 4. THRESHOLDED `16 KiB` FILE LOADING (`Arena` + `\0` vs. `@linear Mmap`)
// ============================================================================
pub const MMAP_THRESHOLD_BYTES: usize = 16_384;

@linear
pub struct Mmap {
    ptr: *u8,
    len_bytes: usize,
    map_cap: usize,
}

impl Mmap {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn open_read_only(
        file: &File,
        /,
        *,
        require_nul_sentinel: bool = false,
    ) -> Mmap!FsError;

    @inline @no_alloc @no_panic
    pub fn as_slice(&self) -> &[u8];

    @inline @no_alloc @no_panic
    pub fn len(&self) -> usize = self.len_bytes;

    @inline @no_alloc @no_panic
    pub fn is_empty(&self) -> bool = self.len_bytes == 0;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn close(own self);
}

@linear
pub enum LoadedFile {
    ArenaBuf(&[u8]),
    Mapped(Mmap),
}

impl LoadedFile {
    @inline @no_alloc @no_panic
    pub fn as_slice(&self) -> &[u8];

    @inline @no_alloc @no_panic
    pub fn len(&self) -> usize = self.as_slice().len();

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn close(own self);
}

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn load_file_thresholded[P: str | Path](
    arena: &mut Arena,
    path: P,
    /,
    *,
    threshold: usize = MMAP_THRESHOLD_BYTES,
    nul_sentinel: bool = true,
) -> LoadedFile!FsError;

// ============================================================================
// 5. CANONICAL PATH RESOLUTION (`AGENTS.md` §6), ATOMIC PUBLISH, CoW & LOCKS
// ============================================================================
@derive(Copy, Equatable)
pub enum CreateTargetKind: u8 {
    Dir        = 0,
    FileParent = 1,
    File       = 2,
}

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn resolve_path[P: str | Path](path: P, /) -> PathBuf!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn resolve_path_in[P: str | Path](arena: &mut Arena, path: P, /) -> Path!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn resolve_or_create_path[P: str | Path](
    path: P,
    /,
    *,
    kind: CreateTargetKind = .Dir,
    perms: FilePermissions = FilePermissions.DEFAULT_DIR,
) -> PathBuf!FsError;

@linear
pub struct StagedAtomicFile {
    file: File,
    parent_dir_fd: RawOsFd,
    tmp_path: PathBuf,
    dst_path: PathBuf,
    perms: FilePermissions,
}

impl StagedAtomicFile {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn create[P: str | Path](
        dst_path: P,
        /,
        *,
        perms: FilePermissions = FilePermissions.DEFAULT_FILE,
    ) -> StagedAtomicFile!FsError;

    @inline @no_alloc @no_panic
    pub fn file_mut(&mut self) -> &mut File = &mut self.file;

    pub fn as_writer(&mut self) -> Writer;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn publish(own self, *, durability: DurabilityMode = .CrashSafe) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn abort(own self);
}

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn write_atomic[P: str | Path](
    dst_path: P,
    bytes: &[u8],
    /,
    *,
    perms: FilePermissions = FilePermissions.DEFAULT_FILE,
    durability: DurabilityMode = .CrashSafe,
) -> unit!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn publish_staged_atomic[P1: str | Path, P2: str | Path](
    staged_tmp_path: P1,
    dst_path: P2,
    /,
    *,
    durability: DurabilityMode = .CrashSafe,
) -> unit!FsError;

@derive(Copy, Equatable)
pub enum MaterializePolicy: u8 {
    ReflinkOrCopy = 0,
    ImmutableCas  = 1,
}

@derive(Copy, Equatable)
pub enum MaterializeMethod: u8 {
    Reflinked  = 0,
    Hardlinked = 1,
    Copied     = 2,
}

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn materialize_file[P1: str | Path, P2: str | Path](
    src: P1,
    dst: P2,
    /,
    *,
    policy: MaterializePolicy = .ReflinkOrCopy,
    overwrite: bool = true,
) -> MaterializeMethod!FsError;

@derive(Copy, Equatable)
pub enum LockMode: u8 {
    Shared    = 0,
    Exclusive = 1,
}

@linear
pub struct FileLock {
    file: File,
}

impl FileLock {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn acquire[P: str | Path](
        lock_path: P,
        /,
        *,
        mode: LockMode = .Exclusive,
        nonblocking: bool = false,
    ) -> FileLock!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn unlock_and_close(own self);
}

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn metadata[P: str | Path](path: P, /) -> Metadata!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn symlink_metadata[P: str | Path](path: P, /) -> Metadata!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn create_dir_all[P: str | Path](
    path: P,
    /,
    *,
    perms: FilePermissions = FilePermissions.DEFAULT_DIR,
) -> unit!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn remove_file[P: str | Path](path: P, /) -> unit!FsError;

@std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn remove_dir_all[P: str | Path](path: P, /) -> unit!FsError;

// ============================================================================
// 6. CROSS-OS FILESYSTEM WATCHER (`inotify` / `FSEvents`+`kqueue` / `ReadDirectoryChangesW`)
// ============================================================================
// Exact 16-bit bitfields (6 + 10 = 16 bits; 8 + 8 = 16 bits)
@derive(Copy, Equatable)
pub bit_field WatchMask: u16 {
    pub create: bool    | 1,
    pub modify: bool    | 1,
    pub remove: bool    | 1,
    pub rename: bool    | 1,
    pub attrib: bool    | 1,
    pub recursive: bool | 1,
    _reserved: u16      | 10,
}

@derive(Copy, Equatable)
pub bit_field WatchEventFlags: u16 {
    pub created: bool         | 1,
    pub modified: bool        | 1,
    pub removed: bool         | 1,
    pub renamed_from: bool    | 1,
    pub renamed_to: bool      | 1,
    pub attrib: bool          | 1,
    pub is_dir: bool          | 1,
    pub rescan_required: bool | 1,
    _reserved: u8             | 8,
}

@derive(Copy, Equatable)
pub type WatchId = distinct u32;

pub struct WatchEvent {
    pub watch_id: WatchId,
    pub path: PathBuf,
    pub flags: WatchEventFlags,
    pub rename_cookie: u32 = 0,
}

@linear
pub struct FsWatcher {
    backend_state: *mut opaque,
}

impl FsWatcher {
    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn new() -> FsWatcher!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn watch[P: str | Path](
        &mut self,
        path: P,
        /,
        *,
        mask: WatchMask = WatchMask {
            create: true, modify: true, remove: true, rename: true, attrib: false, recursive: true, _reserved: 0,
        },
    ) -> WatchId!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn unwatch(&mut self, id: WatchId, /) -> unit!FsError;

    @std_cap_boundary(emits: .FS | .CLOCK | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn poll_events(
        &mut self,
        out_events: &mut Vec[WatchEvent],
        /,
        *,
        timeout: Duration? = .None,
    ) -> usize!FsError;

    @std_cap_boundary(emits: .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn close(own self);
}
```

---

### 2.4 `stdlib/cx/time.cx`

```rust
// File: stdlib/cx/time.cx
mod time;

pub const NANOS_PER_MICRO: u64 = 1_000;
pub const NANOS_PER_MILLI: u64 = 1_000_000;
pub const NANOS_PER_SEC: u64   = 1_000_000_000;

@derive(Copy, Equatable, Comparable)
pub struct Duration {
    nanos: u64,
}

impl Duration {
    pub const ZERO: Duration = Duration { nanos: 0 };
    pub const MAX: Duration  = Duration { nanos: u64.MAX };

    @inline @no_alloc @no_panic
    pub comptime fn from_nanos(ns: u64, /) -> Self = Self { nanos: ns };

    @inline @no_alloc @no_panic
    pub comptime fn from_micros(us: u64, /) -> Self = Self { nanos: us *| NANOS_PER_MICRO };

    @inline @no_alloc @no_panic
    pub comptime fn from_millis(ms: u64, /) -> Self = Self { nanos: ms *| NANOS_PER_MILLI };

    @inline @no_alloc @no_panic
    pub comptime fn from_secs(s: u64, /) -> Self = Self { nanos: s *| NANOS_PER_SEC };

    @inline @no_alloc @no_panic
    pub fn as_nanos(self) -> u64 = self.nanos;

    @inline @no_alloc @no_panic
    pub fn as_micros(self) -> u64 = self.nanos / NANOS_PER_MICRO;

    @inline @no_alloc @no_panic
    pub fn as_millis(self) -> u64 = self.nanos / NANOS_PER_MILLI;

    @inline @no_alloc @no_panic
    pub fn as_secs_f64(self) -> f64 = (self.nanos as f64) * 1.0e-9_f64;

    @inline @no_alloc @no_panic
    pub fn saturating_add(self, rhs: Duration, /) -> Duration = Duration { nanos: self.nanos +| rhs.nanos };

    @inline @no_alloc @no_panic
    pub fn saturating_sub(self, rhs: Duration, /) -> Duration = Duration { nanos: self.nanos -| rhs.nanos };
}

@derive(Copy, Equatable, Comparable)
pub struct Instant {
    mono_ns: u64,
}

impl Instant {
    @inline @no_alloc @no_panic
    @std_cap_boundary(emits: .CLOCK, clears: .FFI | .UNSAFE_OP)
    pub fn now() -> Self;

    @inline @no_alloc @no_panic
    pub fn duration_since(self, earlier: Instant, /) -> Duration =
        Duration { nanos: self.mono_ns -| earlier.mono_ns };

    @inline @no_alloc @no_panic
    pub fn checked_duration_since(self, earlier: Instant, /) -> Duration? =
        if self.mono_ns >= earlier.mono_ns { .Some(Duration { nanos: self.mono_ns - earlier.mono_ns }) } else { .None };

    @inline @no_alloc @no_panic
    pub fn elapsed(self) -> Duration = Instant.now().duration_since(self);

    @inline @no_alloc @no_panic
    pub fn checked_add(self, dur: Duration, /) -> Instant?;
}

@derive(Copy, Equatable)
pub enum TimeError: u8 {
    SystemClockBeforeEarlier = 0,
    TimestampOverflow        = 1,
}

@repr(C)
@derive(Copy, Equatable, Comparable)
pub struct SystemTime {
    pub secs: i64,
    pub subsec_nanos: u32 is 0..=999_999_999,
    _pad: u32 = 0,
}

impl SystemTime {
    pub const UNIX_EPOCH: SystemTime = SystemTime { secs: 0, subsec_nanos: 0, _pad: 0 };

    @inline @no_alloc @no_panic
    @std_cap_boundary(emits: .CLOCK, clears: .FFI | .UNSAFE_OP)
    pub fn now() -> Self;

    @inline @no_alloc @no_panic
    pub fn duration_since(self, earlier: SystemTime, /) -> Duration!TimeError;

    @inline @no_alloc @no_panic
    pub fn unix_epoch_nanos(self) -> i128 =
        (self.secs as i128) * 1_000_000_000_i128 + (self.subsec_nanos as i128);
}

@std_cap_boundary(emits: .CLOCK | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn sleep(dur: Duration, /);
```

---

### 2.5 `stdlib/cx/env.cx`

```rust
// File: stdlib/cx/env.cx
mod env;

use cx.fs.FsError;
use cx.mem.Arena;
use cx.path.{Path, PathBuf};
use cx.str.String;

@derive(Copy, Equatable)
pub enum VarError: u8 {
    NotPresent  = 0,
    NotUnicode  = 1,
    InvalidName = 2,
}

@std_cap_boundary(emits: .ENV, clears: .FFI | .UNSAFE_OP)
pub fn args_in(arena: &mut Arena, /) -> &[str];

@std_cap_boundary(emits: .ENV | .ALLOC, clears: .FFI | .UNSAFE_OP)
pub fn args_os() -> Vec[PathBuf];

@std_cap_boundary(emits: .ENV | .ALLOC, clears: .FFI | .UNSAFE_OP)
pub fn var(key: str, /) -> String!VarError;

@std_cap_boundary(emits: .ENV, clears: .FFI | .UNSAFE_OP)
pub fn var_in(arena: &mut Arena, key: str, /) -> str!VarError;

@std_cap_boundary(emits: .ENV | .ALLOC, clears: .FFI | .UNSAFE_OP)
pub fn var_os(key: str, /) -> PathBuf?;

@std_cap_boundary(emits: .ENV | .ALLOC, clears: .FFI | .UNSAFE_OP)
pub fn vars() -> Vec[(String, String)];

/// Marked `unsafe` (Rust 2024 Edition invariant): POSIX `getenv` in C FFI threads reads `environ` unlocked!
@std_cap_boundary(emits: .ENV | .UNSAFE_OP | .BLOCKING_SYNC, clears: .FFI)
pub unsafe fn set_var(key: str, val: str, /) -> unit!VarError;

@std_cap_boundary(emits: .ENV | .UNSAFE_OP | .BLOCKING_SYNC, clears: .FFI)
pub unsafe fn remove_var(key: str, /) -> unit!VarError;

@std_cap_boundary(emits: .ENV | .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn current_dir() -> PathBuf!FsError;

@std_cap_boundary(emits: .ENV | .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn set_current_dir[P: str | Path](dir: P, /) -> unit!FsError;

@std_cap_boundary(emits: .ENV | .FS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
pub fn current_exe() -> PathBuf!FsError;

@std_cap_boundary(emits: .ENV | .FS, clears: .FFI | .UNSAFE_OP)
pub fn home_dir() -> PathBuf?;

@std_cap_boundary(emits: .ENV | .FS, clears: .FFI | .UNSAFE_OP)
pub fn cache_dir() -> PathBuf?;

@std_cap_boundary(emits: .ENV | .FS, clears: .FFI | .UNSAFE_OP)
pub fn config_dir() -> PathBuf?;

@std_cap_boundary(emits: .ENV | .FS, clears: .FFI | .UNSAFE_OP)
pub fn data_local_dir() -> PathBuf?;

@std_cap_boundary(emits: .ENV | .FS, clears: .FFI | .UNSAFE_OP)
pub fn temp_dir() -> PathBuf;

@std_cap_boundary(emits: .ENV, clears: .FFI | .UNSAFE_OP)
pub fn process_id() -> u32;
```

---

### 2.6 `stdlib/cx/process.cx`

```rust
// File: stdlib/cx/process.cx
mod process;

use cx.fs.{File, RawOsFd};
use cx.io.{IoError, OutBuf, Reader, Writer};
use cx.path.{Path, PathBuf};
use cx.str.String;

@derive(Copy, Equatable)
pub enum StdioKind: u8 {
    Inherit = 0,
    Piped   = 1,
    Null    = 2,
    Fd      = 3,
}

@linear
pub struct Stdio {
    pub(pkg) kind: StdioKind,
    pub(pkg) owned_fd: RawOsFd,
}

impl Stdio {
    @inline @no_alloc @no_panic
    pub fn inherit() -> Self;

    @inline @no_alloc @no_panic
    pub fn piped() -> Self;

    @inline @no_alloc @no_panic
    pub fn null() -> Self;

    @inline @no_alloc @no_panic
    pub fn from_file(file: own File, /) -> Self;

    @std_cap_boundary(emits: .FS, clears: .FFI | .UNSAFE_OP)
    pub fn discard_unused(own self);
}

@derive(Copy, Equatable)
pub struct ExitStatus {
    raw_status: i32,
}

impl ExitStatus {
    @inline @no_alloc @no_panic
    pub fn success(self) -> bool = self.code() == .Some(0);

    @inline @no_alloc @no_panic
    pub fn code(self) -> i32?;

    @inline @no_alloc @no_panic
    pub fn term_signal(self) -> i32?;
}

pub struct Output {
    pub status: ExitStatus,
    pub stdout: Vec[u8],
    pub stderr: Vec[u8],
}

@linear
pub struct ChildStdin {
    file: File,
}

impl ChildStdin {
    pub fn write_all(&mut self, data: &[u8], /) -> unit!IoError;
    pub fn as_writer(&mut self) -> Writer;
    pub fn close(own self);
}

@linear
pub struct ChildStdout {
    file: File,
}

impl ChildStdout {
    pub fn read_out(&mut self, out: &mut OutBuf, /) -> usize!IoError;
    pub fn as_reader(&mut self) -> Reader;
    pub fn close(own self);
}

pub type ChildStderr = ChildStdout;

@linear
pub struct ChildProcess {
    pub pid: u32,
    os_handle: RawOsFd,
    pub stdin: ChildStdin?,
    pub stdout: ChildStdout?,
    pub stderr: ChildStderr?,
}

impl ChildProcess {
    @std_cap_boundary(emits: .PROCESS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn wait(own self) -> ExitStatus!IoError;

    @std_cap_boundary(emits: .PROCESS, clears: .FFI | .UNSAFE_OP)
    pub fn try_wait(&mut self) -> ExitStatus?!IoError;

    @std_cap_boundary(emits: .PROCESS | .FS | .ALLOC | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn wait_with_output(own self, *, max_output_bytes: usize = 67_108_864) -> Output!IoError;

    @std_cap_boundary(emits: .PROCESS | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn kill_and_wait(own self) -> ExitStatus!IoError;

    @std_cap_boundary(emits: .PROCESS, clears: .FFI | .UNSAFE_OP)
    pub fn detach(own self);
}

pub struct Command {
    program: PathBuf,
    args: Vec[PathBuf],
    env_overrides: Vec[(String, String?)],
    env_clear_all: bool = false,
    cwd: PathBuf? = .None,
    allow_windows_batch: bool = false, // `false` by default -> blocks CVE-2024-24576 `BatBadBut`!
    stdin_cfg: Stdio = Stdio.inherit(),
    stdout_cfg: Stdio = Stdio.inherit(),
    stderr_cfg: Stdio = Stdio.inherit(),
}

impl Command {
    pub fn new[P: str | Path](program: P, /) -> Self;

    /// Explicit opt-in constructor for `.bat`/`.cmd` scripts on Windows (`cmd.exe /d /v:off /e:on /c` escaped).
    pub fn cmd_script[P: str | Path](batch_path: P, /) -> Self;

    pub fn arg[S: str | Path](&mut self, a: S, /) -> &mut Self;
    pub fn args[S: str | Path](&mut self, list: &[S], /) -> &mut Self;
    pub fn current_dir[P: str | Path](&mut self, dir: P, /) -> &mut Self;
    pub fn env(&mut self, key: str, val: str, /) -> &mut Self;
    pub fn env_remove(&mut self, key: str, /) -> &mut Self;
    pub fn env_clear(&mut self) -> &mut Self;
    pub fn stdin(&mut self, cfg: own Stdio, /) -> &mut Self;
    pub fn stdout(&mut self, cfg: own Stdio, /) -> &mut Self;
    pub fn stderr(&mut self, cfg: own Stdio, /) -> &mut Self;

    @std_cap_boundary(emits: .PROCESS | .FS | .ENV | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn spawn(own self) -> ChildProcess!IoError;

    @std_cap_boundary(emits: .PROCESS | .FS | .ENV | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn status(own self) -> ExitStatus!IoError;

    @std_cap_boundary(emits: .PROCESS | .FS | .ENV | .ALLOC | .BLOCKING_SYNC, clears: .FFI | .UNSAFE_OP)
    pub fn output(own self, *, max_output_bytes: usize = 67_108_864) -> Output!IoError;
}

@std_cap_boundary(emits: .PROCESS, clears: .FFI | .UNSAFE_OP)
pub fn exit(code: i32, /) -> never;
```

---

## 3. Deliverable 2: Concrete Cross-OS Reference Implementations

### 3.1 Zero-Copy `BufReader` (`peek`, `consume`, SIMD `read_until`) & Vectored/Formatted `BufWriter` in `.cx`

The `.cx` implementation below shows `BufReader` executing inline slice operations (`peek`, `consume`, `read_until`) without touching `upstream.vtable` until its window drains, alongside `BufWriter` streaming `SE-12` stack `FmtArgs` (`print`) and scatter-gather `IoSlice` arrays (`write_vectored`) with zero heap allocations:

```rust
// File: stdlib/cx/io_buffered_impl.cx (excerpt of stdlib/cx/io.cx)
mod io_buffered_impl;

use cx.io.{BufReader, BufWriter, IoError, IoSlice, OutBuf, Reader, Writer};
use cx.simd;

impl BufReader {
    @inline @no_alloc @no_panic
    pub fn over_uninit[const N: usize](upstream: Reader, backing: &out [u8; N], /) -> Self = Self {
        upstream: upstream,
        buf_ptr: (&raw mut backing.*) as *mut u8,
        buf_cap: N,
        pos: 0,
        filled: 0,
    };

    @inline @no_alloc @no_panic
    pub fn buffered(&self) -> &[u8] =
        unsafe { @slice_from_raw_parts(self.buf_ptr.add(self.pos), self.filled - self.pos) };

    @inline @no_alloc @no_panic
    pub fn consume(&mut self, n: usize, /) {
        let avail = self.filled - self.pos;
        debug_assert(n <= avail, "BufReader.consume exceeded buffered bytes");
        self.pos += if n <= avail { n } else { avail };
        if self.pos == self.filled {
            self.pos = 0;
            self.filled = 0;
        }
    }

    pub fn peek(&mut self, min_bytes: usize = 1, /) -> &[u8]!IoError {
        if min_bytes > self.buf_cap {
            return .Err(IoError.from_kind(.InvalidInput, op: .Read));
        }
        if (self.filled - self.pos) >= min_bytes {
            return .Ok(self.buffered());
        }

        let tail_len = self.filled - self.pos;
        if tail_len > 0 and self.pos > 0 {
            unsafe {
                @memmove(
                    self.buf_ptr as *mut opaque,
                    self.buf_ptr.add(self.pos) as *opaque,
                    tail_len,
                );
            }
        }
        self.pos = 0;
        self.filled = tail_len;

        while self.filled < min_bytes {
            var out = unsafe {
                OutBuf.from_raw_parts(self.buf_ptr.add(self.filled), self.buf_cap - self.filled)
            };
            let n = self.upstream.read_out(&mut out)?;
            if n == 0 {
                if self.filled == 0 {
                    return .Ok(&[]);
                }
                return .Err(IoError.from_kind(.UnexpectedEof, op: .Read));
            }
            self.filled += n;
        }
        .Ok(self.buffered())
    }

    pub fn read_until(&mut self, delim: u8, /) -> &[u8]?!IoError {
        var scanned_offset: usize = 0;
        loop {
            let window = self.buffered();
            if scanned_offset < window.len() {
                if simd.memchr_u8(window[scanned_offset..], delim) is .Some(rel_idx) {
                    let match_len = scanned_offset + rel_idx;
                    let base_ptr = unsafe { self.buf_ptr.add(self.pos) };
                    self.pos += match_len + 1;
                    if self.pos == self.filled {
                        self.pos = 0;
                        self.filled = 0;
                    }
                    return .Ok(.Some(unsafe { @slice_from_raw_parts(base_ptr, match_len) }));
                }
                scanned_offset = window.len();
            }

            if window.len() >= self.buf_cap {
                return .Err(IoError.from_kind(.StreamTooLong, op: .Read));
            }

            if self.pos > 0 and window.len() > 0 {
                unsafe {
                    @memmove(
                        self.buf_ptr as *mut opaque,
                        self.buf_ptr.add(self.pos) as *opaque,
                        window.len(),
                    );
                }
            }
            self.filled = window.len();
            self.pos = 0;

            var out = unsafe {
                OutBuf.from_raw_parts(self.buf_ptr.add(self.filled), self.buf_cap - self.filled)
            };
            let n = self.upstream.read_out(&mut out)?;
            if n == 0 {
                if self.filled == 0 {
                    return .Ok(.None);
                }
                let final_len = self.filled;
                self.filled = 0;
                return .Ok(.Some(unsafe { @slice_from_raw_parts(self.buf_ptr, final_len) }));
            }
            self.filled += n;
        }
    }
}

impl BufWriter {
    @inline @no_alloc @no_panic
    pub fn over_uninit[const N: usize](
        downstream: Writer,
        backing: &out [u8; N],
        /,
        *,
        line_buffered: bool = false,
    ) -> Self {
        let cap_u32: u32 = if N <= 0x7FFF_FFFF { N as u32 } else { 0x7FFF_FFFF_u32 };
        let flag_bit: u32 = (line_buffered as u32) << 31;
        return Self {
            downstream: downstream,
            buf_ptr: (&raw mut backing.*) as *mut u8,
            filled: 0,
            cap_and_flags: cap_u32 | flag_bit,
        };
    }

    /// Streams stack-resident `FmtArgs` (`pieces` + `FmtArg` callbacks) directly into `buf_ptr` with 0 heap allocs.
    pub fn print(&mut self, args: FmtArgs, /) -> unit!IoError {
        var sink = self.as_writer();
        for arg, idx in args.args() {
            let piece = args.piece_at(idx);
            if not piece.is_empty() {
                self.write_all(piece.as_bytes())?;
            }
            arg.format_into(&mut sink)?;
        }
        let tail_piece = args.tail_piece();
        if not tail_piece.is_empty() {
            self.write_all(tail_piece.as_bytes())?;
        }
        .Ok(())
    }

    pub fn write_vectored(&mut self, bufs: &[IoSlice], /) -> usize!IoError {
        var total_incoming: usize = 0;
        for slice in bufs {
            total_incoming +|= slice.len();
        }
        if total_incoming == 0 {
            return .Ok(0);
        }

        if total_incoming <= self.spare_capacity() and not self.is_line_buffered() {
            for slice in bufs {
                let bytes = slice.as_slice();
                if not bytes.is_empty() {
                    unsafe {
                        @memcpy(
                            self.buf_ptr.add(self.filled as usize) as *mut opaque,
                            bytes.as_ptr() as *opaque,
                            bytes.len(),
                        );
                    }
                    self.filled += bytes.len() as u32;
                }
            }
            return .Ok(total_incoming);
        }

        if self.filled == 0 {
            return self.downstream.write_vectored(bufs);
        }

        var combined: [IoSlice; 16] = [IoSlice.new(&[]); 16];
        combined[0] = IoSlice.new(unsafe { @slice_from_raw_parts(self.buf_ptr, self.filled as usize) });
        let take_n = if bufs.len() < 15 { bufs.len() } else { 15 };
        for s, i in bufs[..take_n] {
            combined[i + 1] = s;
        }

        let buf_len = self.filled as usize;
        let written = self.downstream.write_vectored(combined[..take_n + 1])?;
        if written < buf_len {
            let rem = buf_len - written;
            unsafe {
                @memmove(
                    self.buf_ptr as *mut opaque,
                    self.buf_ptr.add(written) as *opaque,
                    rem,
                );
            }
            self.filled = rem as u32;
            self.flush()?;
            return self.downstream.write_vectored(bufs);
        }

        self.filled = 0;
        .Ok(written - buf_len)
    }
}
```

---

### 3.2 Windows Lossless WTF-8 ↔ Stack UTF-16 (`[u16; 512]`) + `\\?\` Extended-Length Normalization

The Zig reference implementation below transcodes WTF-8 ↔ WTF-16LE losslessly (rejecting embedded NULs, overlong sequences, and ill-formed 6-byte CESU-8 surrogate pairs), executes on a `[u16; 512]` stack buffer with zero heap allocations on normal paths, and resolves + promotes paths to `\\?\C:\...` or `\\?\UNC\server\share\...` whenever length reaches `>= 248` `WCHAR`s, a component ends in a space or period, or a component matches any DOS reserved device stem (including ISO/IEC 8859-1 superscript `COM¹..³` and `LPT¹..³`):

```zig
//! Reference Implementation: Windows WTF-8 <-> Stack UTF-16LE + `\\?\` Normalization
const std = @import("std");
const windows = std.os.windows;

pub const WinPathError = error{
    InvalidWtf8,
    InteriorNulByte,
    PathTooLong,
    SystemPathResolutionFailed,
};

pub const VerbatimMode = enum(u8) {
    auto_promote = 0, // Promotes >= 248 WCHARs, reserved DOS stems, or trailing space/dot
    always = 1,       // Always emits `\\?\C:\...` or `\\?\UNC\server\share\...`
    nt_namespace = 2, // Emits `\??\C:\...` or `\??\UNC\...` for `NtCreateFile`
};

pub fn encodeWtf8ToWtf16(wtf8: []const u8, out_u16: []u16) WinPathError!usize {
    var i: usize = 0;
    var out_idx: usize = 0;
    var prev_was_high_surrogate = false;

    while (i < wtf8.len) {
        const b0 = wtf8[i];
        if (b0 == 0) return error.InteriorNulByte;

        if (b0 < 0x80) {
            if (out_idx >= out_u16.len) return error.PathTooLong;
            out_u16[out_idx] = b0;
            out_idx += 1;
            prev_was_high_surrogate = false;
            i += 1;
        } else if ((b0 & 0xE0) == 0xC0) {
            if (i + 1 >= wtf8.len) return error.InvalidWtf8;
            const b1 = wtf8[i + 1];
            if ((b1 & 0xC0) != 0x80) return error.InvalidWtf8;
            const cp: u16 = (@as(u16, b0 & 0x1F) << 6) | @as(u16, b1 & 0x3F);
            if (cp < 0x80) return error.InvalidWtf8;
            if (out_idx >= out_u16.len) return error.PathTooLong;
            out_u16[out_idx] = cp;
            out_idx += 1;
            prev_was_high_surrogate = false;
            i += 2;
        } else if ((b0 & 0xF0) == 0xE0) {
            if (i + 2 >= wtf8.len) return error.InvalidWtf8;
            const b1 = wtf8[i + 1];
            const b2 = wtf8[i + 2];
            if ((b1 & 0xC0) != 0x80 or (b2 & 0xC0) != 0x80) return error.InvalidWtf8;
            const cp: u16 = (@as(u16, b0 & 0x0F) << 12) | (@as(u16, b1 & 0x3F) << 6) | @as(u16, b2 & 0x3F);
            if (cp < 0x800) return error.InvalidWtf8;

            const is_high = (cp >= 0xD800 and cp <= 0xDBFF);
            const is_low = (cp >= 0xDC00 and cp <= 0xDFFF);
            if (is_low and prev_was_high_surrogate) return error.InvalidWtf8; // Reject 6B CESU-8

            if (out_idx >= out_u16.len) return error.PathTooLong;
            out_u16[out_idx] = cp;
            out_idx += 1;
            prev_was_high_surrogate = is_high;
            i += 3;
        } else if ((b0 & 0xF8) == 0xF0) {
            if (i + 3 >= wtf8.len) return error.InvalidWtf8;
            const b1 = wtf8[i + 1];
            const b2 = wtf8[i + 2];
            const b3 = wtf8[i + 3];
            if ((b1 & 0xC0) != 0x80 or (b2 & 0xC0) != 0x80 or (b3 & 0xC0) != 0x80) return error.InvalidWtf8;
            const cp: u32 = (@as(u32, b0 & 0x07) << 18) | (@as(u32, b1 & 0x3F) << 12) |
                (@as(u32, b2 & 0x3F) << 6) | @as(u32, b3 & 0x3F);
            if (cp < 0x10000 or cp > 0x10FFFF) return error.InvalidWtf8;

            if (out_idx + 1 >= out_u16.len) return error.PathTooLong;
            const adj = cp - 0x10000;
            out_u16[out_idx] = @intCast(0xD800 | (adj >> 10));
            out_u16[out_idx + 1] = @intCast(0xDC00 | (adj & 0x3FF));
            out_idx += 2;
            prev_was_high_surrogate = false;
            i += 4;
        } else {
            return error.InvalidWtf8;
        }
    }
    return out_idx;
}

pub fn decodeWtf16ToWtf8(wtf16: []const u16, out_wtf8: []u8) usize {
    var i: usize = 0;
    var w: usize = 0;
    while (i < wtf16.len) {
        const u0 = wtf16[i];
        if (u0 >= 0xD800 and u0 <= 0xDBFF and (i + 1) < wtf16.len) {
            const u1 = wtf16[i + 1];
            if (u1 >= 0xDC00 and u1 <= 0xDFFF) {
                const cp: u32 = 0x10000 + (((@as(u32, u0) - 0xD800) << 10) | (@as(u32, u1) - 0xDC00));
                out_wtf8[w + 0] = @intCast(0xF0 | (cp >> 18));
                out_wtf8[w + 1] = @intCast(0x80 | ((cp >> 12) & 0x3F));
                out_wtf8[w + 2] = @intCast(0x80 | ((cp >> 6) & 0x3F));
                out_wtf8[w + 3] = @intCast(0x80 | (cp & 0x3F));
                w += 4;
                i += 2;
                continue;
            }
        }
        if (u0 <= 0x7F) {
            out_wtf8[w] = @intCast(u0);
            w += 1;
        } else if (u0 <= 0x7FF) {
            out_wtf8[w + 0] = @intCast(0xC0 | (u0 >> 6));
            out_wtf8[w + 1] = @intCast(0x80 | (u0 & 0x3F));
            w += 2;
        } else {
            out_wtf8[w + 0] = @intCast(0xE0 | (u0 >> 12));
            out_wtf8[w + 1] = @intCast(0x80 | ((u0 >> 6) & 0x3F));
            out_wtf8[w + 2] = @intCast(0x80 | (u0 & 0x3F));
            w += 3;
        }
        i += 1;
    }
    return w;
}

fn isDosReservedComponent(comp: []const u16) bool {
    if (comp.len == 0) return false;
    if (comp.len == 1 and comp[0] == '.') return false;
    if (comp.len == 2 and comp[0] == '.' and comp[1] == '.') return false;

    const last = comp[comp.len - 1];
    if (last == ' ' or last == '.') return true;

    var stem_end: usize = 0;
    while (stem_end < comp.len and comp[stem_end] != '.' and comp[stem_end] != ':') : (stem_end += 1) {}
    while (stem_end > 0 and comp[stem_end - 1] == ' ') : (stem_end -= 1) {}

    if (stem_end == 3) {
        const c0 = comp[0] & ~@as(u16, 0x20);
        const c1 = comp[1] & ~@as(u16, 0x20);
        const c2 = comp[2] & ~@as(u16, 0x20);
        if (c0 == 'C' and c1 == 'O' and c2 == 'N') return true;
        if (c0 == 'P' and c1 == 'R' and c2 == 'N') return true;
        if (c0 == 'A' and c1 == 'U' and c2 == 'X') return true;
        if (c0 == 'N' and c1 == 'U' and c2 == 'L') return true;
    } else if (stem_end == 4) {
        const c0 = comp[0] & ~@as(u16, 0x20);
        const c1 = comp[1] & ~@as(u16, 0x20);
        const c2 = comp[2] & ~@as(u16, 0x20);
        const d = comp[3];
        const is_digit_or_sup = (d >= '0' and d <= '9') or d == 0x00B9 or d == 0x00B2 or d == 0x00B3;
        if (is_digit_or_sup and ((c0 == 'C' and c1 == 'O' and c2 == 'M') or
            (c0 == 'L' and c1 == 'P' and c2 == 'T')))
        {
            return true;
        }
    } else if (stem_end == 6 or stem_end == 7) {
        if ((comp[0] & ~@as(u16, 0x20)) == 'C' and comp[stem_end - 1] == '$') return true;
    }
    return false;
}

pub fn needsVerbatimWin32(wpath: []const u16) bool {
    if (wpath.len >= 4 and wpath[0] == '\\' and (wpath[1] == '\\' or wpath[1] == '?') and
        wpath[2] == '?' and wpath[3] == '\\')
    {
        return false;
    }
    if (wpath.len >= 248) return true;

    var start: usize = 0;
    var idx: usize = 0;
    while (idx <= wpath.len) : (idx += 1) {
        if (idx == wpath.len or wpath[idx] == '\\' or wpath[idx] == '/') {
            if (isDosReservedComponent(wpath[start..idx])) return true;
            start = idx + 1;
        }
    }
    return false;
}

extern "kernel32" fn GetFullPathNameW(
    lpFileName: [*:0]const u16,
    nBufferLength: u32,
    lpBuffer: [*]u16,
    lpFilePart: ?*[*:0]u16,
) callconv(windows.WINAPI) u32;

pub fn withWin32Path(
    scratch_alloc: std.mem.Allocator,
    wtf8_path: []const u8,
    mode: VerbatimMode,
    body: anytype,
) !@TypeOf(body).ReturnType {
    var stack_raw: [512]u16 = undefined;
    var heap_raw: ?[]u16 = null;
    defer if (heap_raw) |b| scratch_alloc.free(b);

    const work_slice: []u16 = if (wtf8_path.len < 512)
        stack_raw[0..]
    else blk: {
        const cap = @min(wtf8_path.len + 16, 32_768);
        heap_raw = try scratch_alloc.alloc(u16, cap);
        break :blk heap_raw.?;
    };

    const raw_len = try encodeWtf8ToWtf16(wtf8_path, work_slice[0 .. work_slice.len - 1]);
    const already_verbatim = raw_len >= 4 and work_slice[0] == '\\' and
        (work_slice[1] == '\\' or work_slice[1] == '?') and work_slice[2] == '?' and work_slice[3] == '\\';
    if (!already_verbatim) {
        for (work_slice[0..raw_len]) |*ch| {
            if (ch.* == '/') ch.* = '\\';
        }
    }
    work_slice[raw_len] = 0;

    if (already_verbatim) {
        if (mode == .nt_namespace and work_slice[1] == '\\') work_slice[1] = '?';
        return body.call(work_slice[0..raw_len :0]);
    }

    const promote = (mode != .auto_promote) or needsVerbatimWin32(work_slice[0..raw_len]);
    if (!promote) {
        return body.call(work_slice[0..raw_len :0]);
    }

    var stack_full: [520]u16 = undefined;
    const prefix_lead: u16 = if (mode == .nt_namespace) '?' else '\\';
    const full_len = GetFullPathNameW(work_slice[0..raw_len :0].ptr, 510, stack_full[8..].ptr, null);
    if (full_len == 0) return error.SystemPathResolutionFailed;

    if (full_len < 510) {
        return finishVerbatimInPlace(&stack_full, full_len, prefix_lead, body);
    }

    const dyn_buf = try scratch_alloc.alloc(u16, @as(usize, full_len) + 12);
    defer scratch_alloc.free(dyn_buf);
    const full_len2 = GetFullPathNameW(work_slice[0..raw_len :0].ptr, full_len + 2, dyn_buf[8..].ptr, null);
    if (full_len2 == 0 or full_len2 > 32_760) return error.PathTooLong;
    return finishVerbatimInPlace(dyn_buf, full_len2, prefix_lead, body);
}

fn finishVerbatimInPlace(buf: []u16, full_len: u32, second_char: u16, body: anytype) !@TypeOf(body).ReturnType {
    const end: usize = 8 + @as(usize, full_len);
    buf[end] = 0;
    const resolved = buf[8..end];
    if (resolved.len >= 2 and resolved[0] == '\\' and resolved[1] == '\\') {
        buf[2] = '\\';
        buf[3] = second_char;
        buf[4] = '?';
        buf[5] = '\\';
        buf[6] = 'U';
        buf[7] = 'N';
        buf[8] = 'C';
        return body.call(buf[2..end :0]);
    }
    buf[4] = '\\';
    buf[5] = second_char;
    buf[6] = '?';
    buf[7] = '\\';
    return body.call(buf[4..end :0]);
}
```

---

### 3.3 Crash- & `SIGKILL`-Safe Atomic `UnlinkAndReplace` on Windows & POSIX

The C11 reference implementation below implements staged atomic file replacement across Windows and POSIX, handling Windows `FileRenameInfoEx` (`FILE_RENAME_FLAG_POSIX_SEMANTICS | FILE_RENAME_FLAG_REPLACE_IF_EXISTS`) over open `FILE_SHARE_DELETE` handles, `FileRenameInfo` and `MoveFileExW` fallbacks on FAT32/exFAT/network volumes, read-only destination attribute clearing, bounded antivirus retry backoff, and macOS fresh-inode `renameat` + `F_BARRIERFSYNC` / `F_FULLFSYNC`:

```c
// Reference Implementation: Cross-OS Crash- & SIGKILL-Safe Atomic UnlinkAndReplace
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef enum CxDurabilityMode {
    CX_DURABILITY_FAST_LOCAL = 0,
    CX_DURABILITY_CRASH_SAFE = 1,
    CX_DURABILITY_POWER_SAFE = 2,
} CxDurabilityMode;

#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#include <windows.h>

#ifndef FILE_RENAME_FLAG_REPLACE_IF_EXISTS
#define FILE_RENAME_FLAG_REPLACE_IF_EXISTS 0x00000001
#define FILE_RENAME_FLAG_POSIX_SEMANTICS   0x00000002
#endif
#ifndef FILE_DISPOSITION_FLAG_DELETE
#define FILE_DISPOSITION_FLAG_DELETE          0x00000001
#define FILE_DISPOSITION_FLAG_POSIX_SEMANTICS 0x00000002
#endif

typedef struct CxFileRenameInfoHeader {
    union {
        BOOLEAN ReplaceIfExists; // FileRenameInfo (3)
        DWORD   Flags;           // FileRenameInfoEx (22)
    };
    HANDLE RootDirectory;
    DWORD  FileNameLength;       // Byte length WITHOUT trailing NUL
    WCHAR  FileName[1];
} CxFileRenameInfoHeader;

typedef struct CxFileDispositionInfoEx {
    DWORD Flags;
} CxFileDispositionInfoEx;

static void cx_win32_unlink_staged_handle(HANDLE h_tmp, const WCHAR *tmp_wpath) {
    if (h_tmp != INVALID_HANDLE_VALUE) {
        CxFileDispositionInfoEx disp = {
            .Flags = FILE_DISPOSITION_FLAG_DELETE | FILE_DISPOSITION_FLAG_POSIX_SEMANTICS
        };
        if (!SetFileInformationByHandle(h_tmp, (FILE_INFO_BY_HANDLE_CLASS)21, &disp, sizeof(disp))) {
            FILE_DISPOSITION_INFO legacy = { .DeleteFile = TRUE };
            SetFileInformationByHandle(h_tmp, FileDispositionInfo, &legacy, sizeof(legacy));
        }
        CloseHandle(h_tmp);
    }
    DeleteFileW(tmp_wpath);
}

DWORD cx_win32_write_atomic(
    const WCHAR *tmp_wpath,
    const WCHAR *dst_wpath,
    const uint8_t *bytes,
    size_t byte_len,
    CxDurabilityMode durability,
    bool target_readonly
) {
    HANDLE h_tmp = CreateFileW(
        tmp_wpath,
        GENERIC_WRITE | DELETE,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL,
        CREATE_NEW,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (h_tmp == INVALID_HANDLE_VALUE) return GetLastError();

    size_t offset = 0;
    while (offset < byte_len) {
        DWORD chunk = (byte_len - offset > 0x02000000u) ? 0x02000000u : (DWORD)(byte_len - offset);
        DWORD written = 0;
        if (!WriteFile(h_tmp, bytes + offset, chunk, &written, NULL) || written == 0) {
            DWORD err = GetLastError();
            cx_win32_unlink_staged_handle(h_tmp, tmp_wpath);
            return err ? err : ERROR_WRITE_FAULT;
        }
        offset += written;
    }

    if (durability != CX_DURABILITY_FAST_LOCAL) {
        if (!FlushFileBuffers(h_tmp)) {
            DWORD err = GetLastError();
            cx_win32_unlink_staged_handle(h_tmp, tmp_wpath);
            return err;
        }
    }

    size_t dst_bytes_no_nul = wcslen(dst_wpath) * sizeof(WCHAR);
    size_t info_bytes = offsetof(CxFileRenameInfoHeader, FileName) + dst_bytes_no_nul + sizeof(WCHAR);

    uint8_t stack_buf[1100];
    CxFileRenameInfoHeader *ren = (info_bytes <= sizeof(stack_buf))
        ? (CxFileRenameInfoHeader *)stack_buf
        : (CxFileRenameInfoHeader *)HeapAlloc(GetProcessHeap(), 0, info_bytes);
    if (!ren) {
        cx_win32_unlink_staged_handle(h_tmp, tmp_wpath);
        return ERROR_NOT_ENOUGH_MEMORY;
    }

    ren->RootDirectory = NULL;
    ren->FileNameLength = (DWORD)dst_bytes_no_nul;
    memcpy(ren->FileName, dst_wpath, dst_bytes_no_nul + sizeof(WCHAR));

    DWORD last_err = ERROR_SUCCESS;
    for (uint32_t attempt = 0; attempt < 6; ++attempt) {
        ren->Flags = FILE_RENAME_FLAG_REPLACE_IF_EXISTS | FILE_RENAME_FLAG_POSIX_SEMANTICS;
        if (SetFileInformationByHandle(h_tmp, (FILE_INFO_BY_HANDLE_CLASS)22, ren, (DWORD)info_bytes)) {
            last_err = ERROR_SUCCESS;
            break;
        }
        last_err = GetLastError();

        // Fallback 1: FileRenameInfo (3) for FAT32 / exFAT / SMB volumes lacking POSIX_SEMANTICS
        if (last_err == ERROR_INVALID_PARAMETER || last_err == ERROR_NOT_SUPPORTED ||
            last_err == ERROR_INVALID_FUNCTION) {
            ren->Flags = 0;
            ren->ReplaceIfExists = TRUE;
            if (SetFileInformationByHandle(h_tmp, FileRenameInfo, ren, (DWORD)info_bytes)) {
                last_err = ERROR_SUCCESS;
                break;
            }
            last_err = GetLastError();
        }

        // Clear READONLY attribute on existing destination file if overwriting an immutable artifact
        if (last_err == ERROR_ACCESS_DENIED && attempt == 0) {
            DWORD attrs = GetFileAttributesW(dst_wpath);
            if (attrs != INVALID_FILE_ATTRIBUTES && (attrs & FILE_ATTRIBUTE_DIRECTORY) == 0 &&
                (attrs & FILE_ATTRIBUTE_READONLY) != 0) {
                SetFileAttributesW(dst_wpath, attrs & ~FILE_ATTRIBUTE_READONLY);
                continue;
            }
        }

        if (last_err != ERROR_ACCESS_DENIED && last_err != ERROR_SHARING_VIOLATION) break;
        Sleep(1u << attempt);
    }

    if ((uint8_t *)ren != stack_buf) HeapFree(GetProcessHeap(), 0, ren);

    // Fallback 2: Close staged handle and try MoveFileExW if redirector rejected handle rename
    if (last_err != ERROR_SUCCESS) {
        CloseHandle(h_tmp);
        h_tmp = INVALID_HANDLE_VALUE;
        DWORD mv_flags = MOVEFILE_REPLACE_EXISTING |
            ((durability == CX_DURABILITY_POWER_SAFE) ? MOVEFILE_WRITE_THROUGH : 0);
        if (MoveFileExW(tmp_wpath, dst_wpath, mv_flags)) {
            if (target_readonly) SetFileAttributesW(dst_wpath, FILE_ATTRIBUTE_READONLY);
            return ERROR_SUCCESS;
        }
        last_err = GetLastError();
        cx_win32_unlink_staged_handle(INVALID_HANDLE_VALUE, tmp_wpath);
        return last_err;
    }

    if (target_readonly) {
        FILE_BASIC_INFO basic = {0};
        basic.FileAttributes = FILE_ATTRIBUTE_READONLY;
        SetFileInformationByHandle(h_tmp, FileBasicInfo, &basic, sizeof(basic));
    }
    CloseHandle(h_tmp);
    return ERROR_SUCCESS;
}

#else // POSIX (Linux gnu/musl & macOS Darwin)
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

static int cx_posix_sync_staged(int fd, CxDurabilityMode durability) {
    if (durability == CX_DURABILITY_FAST_LOCAL) return 0;
#if defined(__APPLE__)
    if (durability == CX_DURABILITY_CRASH_SAFE) {
        #ifdef F_BARRIERFSYNC
        if (fcntl(fd, F_BARRIERFSYNC) == 0) return 0;
        #endif
        return fsync(fd);
    } else {
        if (fcntl(fd, F_FULLFSYNC) == 0) return 0;
        return fsync(fd);
    }
#elif defined(__linux__)
    return (durability == CX_DURABILITY_CRASH_SAFE) ? fdatasync(fd) : fsync(fd);
#else
    return fsync(fd);
#endif
}

int cx_posix_write_atomic_at(
    int dir_fd,
    const char *tmp_rel_name,
    const char *dst_rel_name,
    const uint8_t *bytes,
    size_t byte_len,
    mode_t final_mode,
    CxDurabilityMode durability
) {
    int fd = openat(dir_fd, tmp_rel_name, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (fd < 0) return errno;

    size_t off = 0;
    while (off < byte_len) {
        ssize_t n = write(fd, bytes + off, byte_len - off);
        if (n < 0) {
            if (errno == EINTR) continue;
            int err = errno;
            close(fd);
            unlinkat(dir_fd, tmp_rel_name, 0);
            return err;
        }
        off += (size_t)n;
    }

    if (fchmod(fd, final_mode) != 0) {
        int err = errno;
        close(fd);
        unlinkat(dir_fd, tmp_rel_name, 0);
        return err;
    }

    if (cx_posix_sync_staged(fd, durability) != 0) {
        int err = errno;
        close(fd);
        unlinkat(dir_fd, tmp_rel_name, 0);
        return err;
    }
    if (close(fd) != 0) {
        int err = errno;
        unlinkat(dir_fd, tmp_rel_name, 0);
        return err;
    }

    if (renameat(dir_fd, tmp_rel_name, dir_fd, dst_rel_name) != 0) {
        int err = errno;
        unlinkat(dir_fd, tmp_rel_name, 0);
        return err;
    }

    if (durability == CX_DURABILITY_POWER_SAFE) {
#if defined(__APPLE__)
        if (fcntl(dir_fd, F_FULLFSYNC) != 0) (void)fsync(dir_fd);
#else
        (void)fsync(dir_fd);
#endif
    }
    return 0;
}
#endif
```

---

### 3.4 3-Tier Copy-on-Write Materialization (`Reflink -> Hardlink -> Copy`) & Capability-Jailed Traversal

#### A. 3-Tier CoW Materialization (`FICLONE`, `clonefileat`, Cluster-Aligned ReFS `FSCTL_DUPLICATE_EXTENTS_TO_FILE`)

```zig
//! Reference Implementation: 3-Tier CoW Materialization (`Reflink -> Hardlink -> Kernel Copy`)
const std = @import("std");
const builtin = @import("builtin");

pub const MaterializePolicy = enum(u8) {
    reflink_or_copy = 0, // Mutable workspace target: Reflink -> Copy
    immutable_cas = 1,   // Read-only CAS artifact: Reflink -> Hardlink -> Copy
};

pub const MaterializeMethod = enum(u8) {
    reflinked = 0,
    hardlinked = 1,
    copied = 2,
};

const LINUX_FICLONE: u32 = 0x40049409;
const WIN32_FSCTL_SET_SPARSE: u32 = 0x000900C4;
const WIN32_FSCTL_DUPLICATE_EXTENTS_TO_FILE: u32 = 0x00098344;

const WinDuplicateExtentsData = extern struct {
    FileHandle: std.os.windows.HANDLE,
    SourceFileOffset: i64,
    TargetFileOffset: i64,
    ByteCount: i64,
};

pub fn tryWindowsRefsBlockClone(
    src_handle: std.os.windows.HANDLE,
    dst_handle: std.os.windows.HANDLE,
    file_size: u64,
    src_attrs: u32,
    cluster_size: u64, // 4096 or 65536 on ReFS via GetDiskFreeSpaceW
) !bool {
    const w = std.os.windows;
    if (file_size == 0) return true;
    if (!std.math.isPowerOfTwo(cluster_size)) return false;

    if ((src_attrs & w.FILE_ATTRIBUTE_SPARSE_FILE) != 0) {
        var bytes_ret: u32 = 0;
        var sparse_true: u8 = 1;
        if (w.kernel32.DeviceIoControl(
            dst_handle,
            WIN32_FSCTL_SET_SPARSE,
            &sparse_true,
            1,
            null,
            0,
            &bytes_ret,
            null,
        ) == 0) return false;
    }

    var eof_info: i64 = @intCast(file_size);
    if (w.kernel32.SetFileInformationByHandle(dst_handle, .FileEndOfFileInfo, &eof_info, @sizeOf(i64)) == 0) {
        return false;
    }

    const aligned_bytes: u64 = file_size & ~(cluster_size - 1);
    const max_chunk: u64 = 1024 * 1024 * 1024; // 1 GiB (< 4 GiB ReFS ceiling)
    var offset: u64 = 0;

    while (offset < aligned_bytes) {
        const chunk = @min(aligned_bytes - offset, max_chunk);
        var req = WinDuplicateExtentsData{
            .FileHandle = src_handle,
            .SourceFileOffset = @intCast(offset),
            .TargetFileOffset = @intCast(offset),
            .ByteCount = @intCast(chunk),
        };
        var bytes_ret: u32 = 0;
        if (w.kernel32.DeviceIoControl(
            dst_handle,
            WIN32_FSCTL_DUPLICATE_EXTENTS_TO_FILE,
            &req,
            @sizeOf(WinDuplicateExtentsData),
            null,
            0,
            &bytes_ret,
            null,
        ) == 0) {
            var zero_eof: i64 = 0;
            _ = w.kernel32.SetFileInformationByHandle(dst_handle, .FileEndOfFileInfo, &zero_eof, @sizeOf(i64));
            return false;
        }
        offset += chunk;
    }

    const tail_len: usize = @intCast(file_size - aligned_bytes);
    if (tail_len > 0) {
        var tail_buf: [65536]u8 = undefined;
        var ov_read: w.OVERLAPPED = std.mem.zeroes(w.OVERLAPPED);
        ov_read.DUMMYUNIONNAME.DUMMYSTRUCTNAME.Offset = @truncate(aligned_bytes);
        ov_read.DUMMYUNIONNAME.DUMMYSTRUCTNAME.OffsetHigh = @truncate(aligned_bytes >> 32);

        var n_read: u32 = 0;
        if (w.kernel32.ReadFile(src_handle, &tail_buf, @intCast(tail_len), &n_read, &ov_read) == 0 or
            n_read != tail_len) return error.UnexpectedReadShort;

        var ov_write = ov_read;
        var n_written: u32 = 0;
        if (w.kernel32.WriteFile(dst_handle, &tail_buf, @intCast(tail_len), &n_written, &ov_write) == 0 or
            n_written != tail_len) return error.UnexpectedWriteShort;
    }
    return true;
}

pub fn materializePosixAt(
    src_dir_fd: std.posix.fd_t,
    src_rel_z: [*:0]const u8,
    dst_dir_fd: std.posix.fd_t,
    tmp_rel_z: [*:0]const u8,
    dst_rel_z: [*:0]const u8,
    policy: MaterializePolicy,
) !MaterializeMethod {
    if (builtin.os.tag == .macos) {
        const darwin = struct {
            extern "c" fn clonefileat(s_fd: c_int, s: [*:0]const u8, d_fd: c_int, d: [*:0]const u8, flags: u32) c_int;
            extern "c" fn fcopyfile(from: c_int, to: c_int, state: ?*anyopaque, flags: u32) c_int;
        };
        if (darwin.clonefileat(src_dir_fd, src_rel_z, dst_dir_fd, tmp_rel_z, 0) == 0) {
            errdefer std.posix.unlinkatZ(dst_dir_fd, tmp_rel_z, 0) catch {};
            try std.posix.renameatZ(dst_dir_fd, tmp_rel_z, dst_dir_fd, dst_rel_z);
            return .reflinked;
        }
    }

    if (policy == .immutable_cas) {
        if (std.posix.linkatZ(src_dir_fd, src_rel_z, dst_dir_fd, tmp_rel_z, 0)) |_| {
            errdefer std.posix.unlinkatZ(dst_dir_fd, tmp_rel_z, 0) catch {};
            try std.posix.renameatZ(dst_dir_fd, tmp_rel_z, dst_dir_fd, dst_rel_z);
            return .hardlinked;
        } else |_| {}
    }

    const src_fd = try std.posix.openatZ(src_dir_fd, src_rel_z, .{ .ACCMODE = .RDONLY, .CLOEXEC = true }, 0);
    defer std.posix.close(src_fd);
    const st = try std.posix.fstat(src_fd);

    var tmp_fd_opt: ?std.posix.fd_t = try std.posix.openatZ(
        dst_dir_fd,
        tmp_rel_z,
        .{ .ACCMODE = .WRONLY, .CREAT = true, .EXCL = true, .CLOEXEC = true },
        0o600,
    );
    errdefer {
        if (tmp_fd_opt) |fd| std.posix.close(fd);
        std.posix.unlinkatZ(dst_dir_fd, tmp_rel_z, 0) catch {};
    }

    var method: MaterializeMethod = .copied;
    if (builtin.os.tag == .linux) {
        const rc = std.os.linux.ioctl(tmp_fd_opt.?, LINUX_FICLONE, @intCast(src_fd));
        if (std.os.linux.E.init(rc) == .SUCCESS) method = .reflinked;
    }

    if (method == .copied) {
        try copyFdContentsFast(src_fd, tmp_fd_opt.?, @intCast(st.size));
    }

    _ = std.c.fchmod(tmp_fd_opt.?, st.mode & 0o7777);
    std.posix.close(tmp_fd_opt.?);
    tmp_fd_opt = null;

    try std.posix.renameatZ(dst_dir_fd, tmp_rel_z, dst_dir_fd, dst_rel_z);
    return method;
}

fn copyFdContentsFast(src_fd: std.posix.fd_t, dst_fd: std.posix.fd_t, expected_len: u64) !void {
    var remaining = expected_len;
    if (builtin.os.tag == .linux) {
        while (remaining > 0) {
            const chunk: usize = @intCast(@min(remaining, 0x4000_0000));
            const rc = std.os.linux.copy_file_range(src_fd, null, dst_fd, null, chunk, 0);
            switch (std.os.linux.E.init(rc)) {
                .SUCCESS => {
                    if (rc == 0) break;
                    remaining -= rc;
                },
                .INTR => continue,
                else => break,
            }
        }
        if (remaining == 0) return;
    } else if (builtin.os.tag == .macos) {
        const darwin = struct {
            extern "c" fn fcopyfile(from: c_int, to: c_int, state: ?*anyopaque, flags: u32) c_int;
        };
        const COPYFILE_DATA: u32 = 1 << 3;
        if (darwin.fcopyfile(src_fd, dst_fd, null, COPYFILE_DATA) == 0) return;
        _ = std.posix.lseek_SET(src_fd, 0) catch {};
        _ = std.posix.lseek_SET(dst_fd, 0) catch {};
    }

    var buf: [65536]u8 = undefined;
    while (true) {
        const n = try std.posix.read(src_fd, &buf);
        if (n == 0) break;
        var off: usize = 0;
        while (off < n) {
            off += try std.posix.write(dst_fd, buf[off..n]);
        }
    }
}
```

#### B. Cross-OS Capability-Relative `open_file_beneath` (`openat2`, `NtCreateFile`, WASI `path_open`)

```zig
//! Reference Implementation: Sandboxed Relative Traversal (`Linux openat2`, `WinNT NtCreateFile`, `WASI path_open`)
const std = @import("std");
const w = std.os.windows;

// 1. Linux >= 5.6 `openat2` (syscall 437) with pre-5.6 per-segment `O_NOFOLLOW` fallback
const LinuxOpenHow = extern struct { flags: u64, mode: u64, resolve: u64 };
const RESOLVE_NO_MAGICLINKS: u64 = 0x02;
const RESOLVE_NO_SYMLINKS: u64 = 0x04;
const RESOLVE_BENEATH: u64 = 0x08;

pub fn openBeneathLinux(dir_fd: i32, rel_z: [*:0]const u8, flags: u32, mode: u32) !i32 {
    var how = LinuxOpenHow{
        .flags = @as(u64, flags) | std.os.linux.O.CLOEXEC | std.os.linux.O.NOFOLLOW,
        .mode = mode,
        .resolve = RESOLVE_BENEATH | RESOLVE_NO_SYMLINKS | RESOLVE_NO_MAGICLINKS,
    };
    const rc = std.os.linux.syscall4(
        .openat2,
        @bitCast(@as(isize, dir_fd)),
        @intFromPtr(rel_z),
        @intFromPtr(&how),
        @sizeOf(LinuxOpenHow),
    );
    switch (std.os.linux.E.init(rc)) {
        .SUCCESS => return @intCast(rc),
        .XDEV, .LOOP => return error.PathEscapesRootOrSymlink,
        else => |e| return std.posix.unexpectedErrno(e),
    }
}

// 2. Windows NT single-component `NtCreateFile` walk against `OBJECT_ATTRIBUTES.RootDirectory`
const FILE_AttributeTagInfo = 9;
const WinFileAttributeTagInfo = extern struct { FileAttributes: u32, ReparseTag: u32 };

pub fn openBeneathWinNt(root_dir: w.HANDLE, rel_wtf16: []const u16, desired_access: u32, disposition: u32) !w.HANDLE {
    if (rel_wtf16.len == 0 or rel_wtf16[0] == '\\' or rel_wtf16[0] == '/') return error.PathEscapesRootOrSymlink;

    var cur_dir: w.HANDLE = root_dir;
    errdefer if (cur_dir != root_dir) w.CloseHandle(cur_dir);

    var idx: usize = 0;
    while (idx < rel_wtf16.len) {
        var end = idx;
        while (end < rel_wtf16.len and rel_wtf16[end] != '\\' and rel_wtf16[end] != '/') : (end += 1) {}
        const seg = rel_wtf16[idx..end];
        idx = end + 1;

        if (seg.len == 0 or (seg.len == 1 and seg[0] == '.')) continue;
        if (seg.len == 2 and seg[0] == '.' and seg[1] == '.') return error.PathEscapesRootOrSymlink;
        if (std.mem.indexOfScalar(u16, seg, ':') != null) return error.PathEscapesRootOrSymlink;

        const is_leaf = (end >= rel_wtf16.len);
        var ustr = w.UNICODE_STRING{
            .Length = @intCast(seg.len * 2),
            .MaximumLength = @intCast(seg.len * 2),
            .Buffer = @constCast(seg.ptr),
        };
        var oa = w.OBJECT_ATTRIBUTES{
            .Length = @sizeOf(w.OBJECT_ATTRIBUTES),
            .RootDirectory = cur_dir,
            .Attributes = 0,
            .ObjectName = &ustr,
            .SecurityDescriptor = null,
            .SecurityQualityOfService = null,
        };
        var io_status: w.IO_STATUS_BLOCK = undefined;
        var next_h: w.HANDLE = undefined;

        const access = if (is_leaf) desired_access | w.SYNCHRONIZE | w.FILE_READ_ATTRIBUTES else w.FILE_TRAVERSE | w.SYNCHRONIZE | w.FILE_READ_ATTRIBUTES;
        const create_opts: u32 = w.FILE_SYNCHRONOUS_IO_NONALERT | w.FILE_OPEN_REPARSE_POINT |
            (if (is_leaf) w.FILE_NON_DIRECTORY_FILE else w.FILE_OPEN_FOR_BACKUP_INTENT);
        const create_disp: u32 = if (is_leaf) disposition else w.FILE_OPEN;

        const st = w.ntdll.NtCreateFile(
            &next_h,
            access,
            &oa,
            &io_status,
            null,
            w.FILE_ATTRIBUTE_NORMAL,
            w.FILE_SHARE_READ | w.FILE_SHARE_WRITE | w.FILE_SHARE_DELETE,
            create_disp,
            create_opts,
            null,
            0,
        );
        if (st != .SUCCESS) return error.NtOpenBeneathFailed;

        // Post-open reparse verification: fail closed if segment is a junction, symlink, or mount point!
        var tag_info: WinFileAttributeTagInfo = undefined;
        if (w.kernel32.GetFileInformationByHandleEx(
            next_h,
            FILE_AttributeTagInfo,
            &tag_info,
            @sizeOf(WinFileAttributeTagInfo),
        ) == 0 or (tag_info.FileAttributes & w.FILE_ATTRIBUTE_REPARSE_POINT) != 0 or
            (!is_leaf and (tag_info.FileAttributes & w.FILE_ATTRIBUTE_DIRECTORY) == 0))
        {
            w.CloseHandle(next_h);
            return error.PathEscapesRootOrSymlink;
        }

        if (cur_dir != root_dir) w.CloseHandle(cur_dir);
        if (is_leaf) return next_h;
        cur_dir = next_h;
    }
    return error.InvalidEmptyPath;
}

// 3. WASI Preview 1 `path_open` (`dirflags = 0` disables `LOOKUPFLAGS_SYMLINK_FOLLOW`)
pub fn openBeneathWasi(dir_fd: i32, rel_utf8: []const u8, oflags: u16, rights_base: u64) !i32 {
    if (rel_utf8.len == 0 or rel_utf8[0] == '/') return error.PathEscapesRootOrSymlink;
    var depth: usize = 0;
    var it = std.mem.splitScalar(u8, rel_utf8, '/');
    while (it.next()) |seg| {
        if (seg.len == 0 or std.mem.eql(u8, seg, ".")) continue;
        if (std.mem.eql(u8, seg, "..")) {
            if (depth == 0) return error.PathEscapesRootOrSymlink;
            depth -= 1;
        } else depth += 1;
    }
    var opened_fd: std.os.wasi.fd_t = undefined;
    const errno = std.os.wasi.path_open(
        dir_fd,
        .{}, // SYMLINK_FOLLOW = false!
        rel_utf8.ptr,
        rel_utf8.len,
        @bitCast(oflags),
        @bitCast(rights_base),
        @bitCast(@as(u64, 0)),
        .{},
        &opened_fd,
    );
    if (errno != .SUCCESS) return error.WasiOpenBeneathFailed;
    return opened_fd;
}
```

---

### 3.5 Overflow-Free `u128` Clocks & Injection-Safe Windows `CreateProcessW` Spawner

#### A. Overflow-Free `u128` Monotonic Clock Scaling in `.cx`

```rust
// File: stdlib/cx/time_scaling.cx (excerpt of stdlib/cx/time.cx)
mod time_scaling;

/// Scales `ticks` at `freq_hz` to nanoseconds with ZERO `u64` overflow across 584.5 years.
@inline @no_alloc @no_panic
pub(pkg) fn scale_ticks_to_nanos_hz(ticks: u64, freq_hz: u64, /) -> u64 {
    if freq_hz == 10_000_000_u64 {
        return ticks *| 100_u64;
    }
    if freq_hz == 24_000_000_u64 {
        return (((ticks as u128) * 125_u128) / 3_u128) as u64;
    }
    if freq_hz == 1_000_000_000_u64 {
        return ticks;
    }
    let whole_secs = ticks / freq_hz;
    let rem_ticks  = ticks % freq_hz;
    let rem_nanos  = (((rem_ticks as u128) * 1_000_000_000_u128) / (freq_hz as u128)) as u64;
    (whole_secs *| 1_000_000_000_u64) +| rem_nanos
}

@inline @no_alloc @no_panic
pub(pkg) fn scale_mach_ticks_to_nanos(ticks: u64, numer: u32, denom: u32, /) -> u64 {
    if numer == denom {
        return ticks;
    }
    (((ticks as u128) * (numer as u128)) / (denom as u128)) as u64
}
```

#### B. Injection-Safe Windows `CreateProcessW` Spawner (`BatBadBut` `CVE-2024-24576` Defense + Deduplicated `PROC_THREAD_ATTRIBUTE_HANDLE_LIST`)

```c
// Reference Implementation: Hardened Windows CreateProcessW Spawner (CVE-2024-24576 Immune)
#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdbool.h>
#include <stdint.h>
#include <wchar.h>

#ifndef PROC_THREAD_ATTRIBUTE_HANDLE_LIST
#define PROC_THREAD_ATTRIBUTE_HANDLE_LIST 0x00020002
#endif

typedef enum CxWinSpawnStatus {
    CX_SPAWN_OK                  = 0,
    CX_SPAWN_ERR_NUL_IN_ARG      = 1,
    CX_SPAWN_ERR_BATCH_REJECTED  = 2, // Blocks CVE-2024-24576 (.bat/.cmd rejected unless cmd_script)
    CX_SPAWN_ERR_CMD_UNESCAPABLE = 3,
    CX_SPAWN_ERR_NOT_FOUND       = 4,
    CX_SPAWN_ERR_WIN32           = 5,
} CxWinSpawnStatus;

static bool cx_is_batch_extension(const WCHAR *wpath) {
    size_t len = wcslen(wpath);
    while (len > 0 && (wpath[len - 1] == L' ' || wpath[len - 1] == L'.')) len--;
    if (len < 4) return false;
    const WCHAR *ext = wpath + (len - 4);
    if (ext[0] != L'.') return false;
    WCHAR c1 = ext[1] & ~0x20, c2 = ext[2] & ~0x20, c3 = ext[3] & ~0x20;
    return (c1 == L'B' && c2 == L'A' && c3 == L'T') ||
           (c1 == L'C' && c2 == L'M' && c3 == L'D');
}

// Appends exact MSVCRT / UCRT CommandLineToArgvW-quoted argument into `out` (or counts length if `out == NULL`).
static bool cx_append_msvcrt_quoted_arg(
    const WCHAR *arg,
    size_t arg_len,
    WCHAR *out,
    size_t *io_pos
) {
    for (size_t i = 0; i < arg_len; ++i) {
        if (arg[i] == L'\0') return false;
    }

    bool needs_quotes = (arg_len == 0);
    for (size_t i = 0; i < arg_len && !needs_quotes; ++i) {
        WCHAR ch = arg[i];
        if (ch == L' ' || ch == L'\t' || ch == L'\n' || ch == L'\v' || ch == L'"') {
            needs_quotes = true;
        }
    }

    size_t p = *io_pos;
    if (!needs_quotes) {
        if (out) memcpy(out + p, arg, arg_len * sizeof(WCHAR));
        *io_pos = p + arg_len;
        return true;
    }

    if (out) out[p] = L'"';
    p++;

    size_t backslashes = 0;
    for (size_t i = 0; i < arg_len; ++i) {
        WCHAR ch = arg[i];
        if (ch == L'\\') {
            backslashes++;
        } else if (ch == L'"') {
            size_t emit_bs = backslashes * 2 + 1;
            if (out) {
                for (size_t k = 0; k < emit_bs; ++k) out[p + k] = L'\\';
                out[p + emit_bs] = L'"';
            }
            p += emit_bs + 1;
            backslashes = 0;
        } else {
            if (backslashes > 0) {
                if (out) {
                    for (size_t k = 0; k < backslashes; ++k) out[p + k] = L'\\';
                }
                p += backslashes;
                backslashes = 0;
            }
            if (out) out[p] = ch;
            p++;
        }
    }

    if (backslashes > 0) {
        size_t emit_bs = backslashes * 2;
        if (out) {
            for (size_t k = 0; k < emit_bs; ++k) out[p + k] = L'\\';
        }
        p += emit_bs;
    }
    if (out) out[p] = L'"';
    *io_pos = p + 1;
    return true;
}

// Filters NULL, INVALID_HANDLE_VALUE, pre-Win8 console pseudohandles, and duplicates (prevents ERROR_INVALID_PARAMETER!)
static DWORD cx_collect_inheritable_stdio_handles(
    HANDLE h_in,
    HANDLE h_out,
    HANDLE h_err,
    HANDLE out_unique[3]
) {
    HANDLE candidates[3] = { h_in, h_out, h_err };
    DWORD count = 0;
    for (int i = 0; i < 3; ++i) {
        HANDLE h = candidates[i];
        if (h == NULL || h == INVALID_HANDLE_VALUE) continue;
        if ((((uintptr_t)h) & 3u) == 3u && GetFileType(h) == FILE_TYPE_CHAR) continue;

        DWORD flags = 0;
        if (!GetHandleInformation(h, &flags)) continue;
        if ((flags & HANDLE_FLAG_INHERIT) == 0) {
            SetHandleInformation(h, HANDLE_FLAG_INHERIT, HANDLE_FLAG_INHERIT);
        }

        bool duplicate = false;
        for (DWORD j = 0; j < count; ++j) {
            if (out_unique[j] == h) { duplicate = true; break; }
        }
        if (!duplicate) out_unique[count++] = h;
    }
    return count;
}

// Resolves `program` strictly to `.exe` (NEVER consulting PATHEXT for `.bat`/`.cmd`!).
static bool cx_resolve_exe_only(const WCHAR *program, const WCHAR *cwd_opt, WCHAR out_resolved[1024]) {
    if (cx_is_batch_extension(program)) return false;
    DWORD n = SearchPathW(cwd_opt, program, L".exe", 1024, out_resolved, NULL);
    if (n > 0 && n < 1024) return true;
    n = SearchPathW(NULL, program, L".exe", 1024, out_resolved, NULL);
    return (n > 0 && n < 1024);
}

CxWinSpawnStatus cx_win32_spawn_hardened(
    const WCHAR *program,
    const WCHAR *const *args,
    const size_t *arg_lens,
    size_t arg_count,
    const WCHAR *cwd_opt,
    void *env_block_utf16_opt,
    HANDLE h_stdin,
    HANDLE h_stdout,
    HANDLE h_stderr,
    PROCESS_INFORMATION *out_pi,
    DWORD *out_win32_err
) {
    *out_win32_err = ERROR_SUCCESS;
    if (cx_is_batch_extension(program)) return CX_SPAWN_ERR_BATCH_REJECTED;

    WCHAR resolved_app[1024];
    if (!cx_resolve_exe_only(program, cwd_opt, resolved_app)) {
        *out_win32_err = ERROR_FILE_NOT_FOUND;
        return CX_SPAWN_ERR_NOT_FOUND;
    }
    if (cx_is_batch_extension(resolved_app)) return CX_SPAWN_ERR_BATCH_REJECTED;

    size_t prog_len = wcslen(resolved_app);
    size_t cmd_len = 0;
    if (!cx_append_msvcrt_quoted_arg(resolved_app, prog_len, NULL, &cmd_len)) return CX_SPAWN_ERR_NUL_IN_ARG;
    for (size_t i = 0; i < arg_count; ++i) {
        cmd_len += 1;
        if (!cx_append_msvcrt_quoted_arg(args[i], arg_lens[i], NULL, &cmd_len)) return CX_SPAWN_ERR_NUL_IN_ARG;
    }

    WCHAR stack_cmd[2048];
    WCHAR *cmd_buf = (cmd_len + 1 <= 2048)
        ? stack_cmd
        : (WCHAR *)HeapAlloc(GetProcessHeap(), 0, (cmd_len + 1) * sizeof(WCHAR));
    if (!cmd_buf) {
        *out_win32_err = ERROR_NOT_ENOUGH_MEMORY;
        return CX_SPAWN_ERR_WIN32;
    }

    size_t write_pos = 0;
    cx_append_msvcrt_quoted_arg(resolved_app, prog_len, cmd_buf, &write_pos);
    for (size_t i = 0; i < arg_count; ++i) {
        cmd_buf[write_pos++] = L' ';
        cx_append_msvcrt_quoted_arg(args[i], arg_lens[i], cmd_buf, &write_pos);
    }
    cmd_buf[write_pos] = L'\0';

    HANDLE unique_handles[3];
    DWORD handle_count = cx_collect_inheritable_stdio_handles(h_stdin, h_stdout, h_stderr, unique_handles);

    STARTUPINFOEXW si_ex;
    ZeroMemory(&si_ex, sizeof(si_ex));
    si_ex.StartupInfo.cb = sizeof(STARTUPINFOEXW);
    si_ex.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    si_ex.StartupInfo.hStdInput  = h_stdin;
    si_ex.StartupInfo.hStdOutput = h_stdout;
    si_ex.StartupInfo.hStdError  = h_stderr;

    uint8_t attr_storage[128];
    bool has_attr_list = false;
    BOOL inherit_flag = FALSE;
    DWORD creation_flags = CREATE_UNICODE_ENVIRONMENT;

    if (handle_count > 0) {
        SIZE_T attr_size = 0;
        InitializeProcThreadAttributeList(NULL, 1, 0, &attr_size);
        LPPROC_THREAD_ATTRIBUTE_LIST attr_list = (attr_size <= sizeof(attr_storage))
            ? (LPPROC_THREAD_ATTRIBUTE_LIST)attr_storage
            : (LPPROC_THREAD_ATTRIBUTE_LIST)HeapAlloc(GetProcessHeap(), 0, attr_size);

        if (InitializeProcThreadAttributeList(attr_list, 1, 0, &attr_size) &&
            UpdateProcThreadAttribute(
                attr_list,
                0,
                PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
                unique_handles,
                handle_count * sizeof(HANDLE),
                NULL,
                NULL
            ))
        {
            si_ex.lpAttributeList = attr_list;
            has_attr_list = true;
            inherit_flag = TRUE;
            creation_flags |= EXTENDED_STARTUPINFO_PRESENT;
        }
    } else {
        si_ex.StartupInfo.cb = sizeof(STARTUPINFOW);
    }

    BOOL ok = CreateProcessW(
        resolved_app,
        cmd_buf,
        NULL,
        NULL,
        inherit_flag,
        creation_flags,
        env_block_utf16_opt,
        cwd_opt,
        &si_ex.StartupInfo,
        out_pi
    );
    if (!ok) *out_win32_err = GetLastError();

    if (has_attr_list) {
        DeleteProcThreadAttributeList(si_ex.lpAttributeList);
        if ((uint8_t *)si_ex.lpAttributeList != attr_storage) {
            HeapFree(GetProcessHeap(), 0, si_ex.lpAttributeList);
        }
    }
    if (cmd_buf != stack_cmd) HeapFree(GetProcessHeap(), 0, cmd_buf);

    return ok ? CX_SPAWN_OK : CX_SPAWN_ERR_WIN32;
}
#endif
```

---

## 4. Deliverable 3: `--sim` Virtualization & `DR-17` Capability Boundary Table

### 4.1 `Context.reactor` (`ReactorVTable`) Dispatch Seam (`DR-20` Seam #5)

In normal production and `--dev` builds, `context.reactor` points to the static `.rodata` `HOST_OS_REACTOR_VTABLE`, which dispatches directly to the native Linux, macOS, Windows, and WASI syscalls detailed in Sections 1–3 with a single predicted indirect branch. When invoked under **`corex test --sim [--seed=S]`** (`DR-18`, `DR-20` Seam #5 & `Fix-18A`), the test runner swaps `context.reactor` for an isolated per-test **`SimReactor`**. `SimReactor` maintains deterministic virtual clocks (`mono_ns: u64` and `wall_epoch_ns: i128` advancing with zero host sleep latency), an in-memory Merkle filesystem (`SimVfs` modeling POSIX/NTFS/WASI path rules, `FILE_SHARE_DELETE` open-handle tables, 1,024 hardlink limits, and crash-cut `DurabilityMode` buffers), and hermetic virtual `SimEnv` and `SimProcTable` maps that prevent host `$HOME` / `$PATH` leakage while deterministically injecting seeded `EINTR` short reads/writes, `ENOSPC`, `ERROR_SHARING_VIOLATION` antivirus locks, and `FsWatcher` queue-overflow rescans.

### 4.2 Complete Entry-Point to `EffectCapabilityMask` & `Context.reactor` Mapping Matrix

Every row below maps a Phase 11.2a public API entry point to its exact `DR-17` `@std_cap_boundary` `EffectCapabilityMask` bits (`fs = 0x0001`, `env = 0x0004`, `process = 0x0008`, `unsafe_op = 0x0020`, `alloc = 0x0040`, `clock = 0x0100`, `blocking_sync = 0x0400`; `ffi = 0x0010` cleared at audited `stdlib/cx` boundaries) and its `ReactorVTable` simulation hook:

| Module & Entry Point(s) | `EffectCapabilityMask` Bits Emitted | Hex Mask | `Context.reactor` (`ReactorVTable`) Hook | `--sim` Virtualization & Fault-Injection Behavior |
| :--- | :--- | :---: | :--- | :--- |
| **`cx.io` Pure Memory Streams**<br>`OutBuf.*`, `IoSlice.*`, `ByteReader`, `SliceWriter`, `LimitReader` | `PURE` *(inherits upstream `Reader`/`Writer` via vtable)* | `0x0000` | None *(in-memory slice math)* | 100% deterministic in-memory execution; zero host syscalls. |
| **`cx.io` Standard Streams**<br>`stdin_locked`, `stdout_locked`, `stderr_locked`, `print`, `println`, `eprint`, `eprintln` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.stdio_rw(ctx, stream_id, buf)` | Captures `stdout`/`stderr` into `SimReactor.captured_stdio` ring for golden assertions; feeds `stdin` from seeded fixture buffer. |
| **`cx.path` Lexical Operations**<br>`Path.*`, `PathBuf.new/from`, `ComponentsIter`, `normalize_lexical` | `PURE` *(+ `alloc` `0x0040` on heap-growing `PathBuf` methods)* | `0x0000` / `0x0040` | None *(pure lexical byte/WTF-8 state machine)* | Executes identically across host OSes; tests can toggle `SimPathFlavor` (POSIX vs. Win32 WTF-8). |
| **`cx.fs` File & Dir Open**<br>`File.open`, `File.create`, `File.open_with`, `Dir.open`, `Dir.cwd` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_open(ctx, dir_fd, path, opts)` | Resolves against `SimVfs` inode table; enforces simulated `FILE_SHARE_DELETE` & permission checks; injects seeded `ENOENT`/`EACCES`. |
| **`cx.fs` Sandboxed Traversal**<br>`Dir.open_file_beneath`, `open_dir_beneath`, `create_dir_beneath`, `unlink_file_beneath`, `metadata_beneath` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_op_beneath(ctx, dir_fd, rel, op)` | Simulates `RESOLVE_BENEATH \| RESOLVE_NO_SYMLINKS`: rejects `..` underflow, absolute paths, and `SimVfs` symlink/junction nodes with `.FilesystemLoop`. |
| **`cx.fs` File Data I/O**<br>`File.read_out`, `read`, `pread_out`, `write`, `write_all`, `pwrite_all`, `write_vectored`, `seek`, `set_len`, `close` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_rw(ctx, fd, iov, offset, op)` | Reads/writes `SimVfs` blocks; under `--sim` chaos mode, splits unguarded `read`/`write`/`write_vectored` calls into partial `1..len` transfers and `EINTR` to test retry loops. |
| **`cx.fs` Sync & Permissions**<br>`File.sync`, `Dir.sync`, `File.set_permissions` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_sync(ctx, fd, durability)` | Commits dirty `SimVfs` buffers at `.CrashSafe` / `.PowerSafe` barriers so simulated crash/power-cut tests catch un-synced writes. |
| **`cx.fs` Thresholded Load & Mmap**<br>`Mmap.open_read_only`, `Mmap.close`, `load_file_thresholded` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_mmap(ctx, fd, nul_guard)` | Allocates read-only pinned `SimVfs` snapshot (`+1` `\0` byte at `len()`) and tracks live `@linear Mmap` handles for leak checks. |
| **`cx.fs` Canonical Resolution**<br>`resolve_path`, `resolve_path_in`, `resolve_or_create_path` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_resolve(ctx, path, create_kind)` | Expands `SimVfs` symlinks (capping depth at `40` → `.FilesystemLoop`), creates missing dirs for `resolve_or_create_path`, and normalizes drive/UNC casing. |
| **`cx.fs` Atomic Publish**<br>`StagedAtomicFile.*`, `write_atomic`, `publish_staged_atomic` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_rename_atomic(ctx, tmp, dst, dur)` | Verifies same-mount invariant (`EXDEV`), injects transient `ERROR_SHARING_VIOLATION` on attempt `0..2` to exercise AV retry backoff, and swaps to a fresh virtual inode ID. |
| **`cx.fs` 3-Tier CoW & Dir Ops**<br>`materialize_file`, `metadata`, `symlink_metadata`, `create_dir_all`, `remove_file`, `remove_dir_all`, `Dir.entries` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_materialize(ctx, src, dst, pol)` | Simulates CoW block-refcounting (`Reflinked`), 1,024-hardlink cap (`Hardlinked` fallback to `Copied`), and `Context.rng`-shuffled `DirIter` order to catch order-dependent bugs. |
| **`cx.fs` File Locking**<br>`FileLock.acquire`, `FileLock.unlock_and_close` | `fs \| blocking_sync` | `0x0401` | `reactor.vtable.fs_lock(ctx, fd, mode, nonblock)` | Tracks shared/exclusive locks in `SimVfs`; parks tasks or returns `.FileLockConflict` deterministically under `TaskGroup` `--sim` schedules. |
| **`cx.fs` Change Watcher**<br>`FsWatcher.new`, `watch`, `unwatch`, `close` / `FsWatcher.poll_events` | `fs \| blocking_sync` *(+ `clock` on `poll_events`)* | `0x0401` / `0x0501` | `reactor.vtable.fs_watch_poll(ctx, w_id, timeout_ns)` | Delivers deterministic `WatchEvent`s on `SimVfs` mutations; advances virtual clock by `timeout` when idle; injects synthetic `rescan_required` overflow events. |
| **`cx.time` Pure Math**<br>`Duration.*`, `Instant.duration_since`, `checked_add`, `SystemTime.duration_since` | `PURE` (`@no_alloc @no_panic`) | `0x0000` | None *(pure `u64` / `i128` saturating/checked math)* | Bit-exact across all targets and `--sim`. |
| **`cx.time` Clock Reads**<br>`Instant.now`, `SystemTime.now` | `clock` (`@no_alloc @no_panic`) | `0x0100` | `reactor.vtable.monotonic_ns(ctx)` / `wall_epoch_ns(ctx)` | Returns `SimReactor.mono_ns` / `SimReactor.wall_epoch_ns` (supports synthetic backward/forward NTP jumps on `SystemTime` while keeping `Instant` strictly monotonic). |
| **`cx.time` Sleep**<br>`cx.time.sleep(dur)` | `clock \| blocking_sync` | `0x0500` | `reactor.vtable.sleep_ns(ctx, dur.as_nanos())` | Advances `SimReactor.mono_ns += dur.as_nanos()` and wakes due timers in 0 ns of real host CPU waiting. |
| **`cx.env` Args & Lookup**<br>`args_in`, `var_in`, `process_id` *(+ `alloc` on `args_os`, `var`, `var_os`, `vars`)* | `env` *(or `env \| alloc`)* | `0x0004` / `0x0044` | `reactor.vtable.env_query(ctx, key_opt)` | Reads strictly from hermetic `SimReactor.env_map` and `SimReactor.argv` (`process_id()` returns virtual PID `1000 + node_id`). |
| **`cx.env` Unsafe Mutation**<br>`unsafe fn set_var`, `unsafe fn remove_var` | `env \| unsafe_op \| blocking_sync` | `0x0424` | `reactor.vtable.env_mutate(ctx, key, val_opt)` | Mutates `SimReactor.env_map` without touching host OS `environ`. |
| **`cx.env` Directories & Exe**<br>`current_dir`, `set_current_dir`, `current_exe`, `home_dir`, `cache_dir`, `config_dir`, `data_local_dir`, `temp_dir` | `env \| fs` *(+ `blocking_sync` on `cwd`/`exe`)* | `0x0005` / `0x0405` | `reactor.vtable.env_std_dir(ctx, dir_kind)` | Maps to hermetic `SimVfs` paths (`/sim/home`, `/sim/home/.cache`, `/sim/tmp`, `/sim/bin/app`), preventing host filesystem pollution. |
| **`cx.process` Child Lifecycle**<br>`Command.spawn`, `status`, `output` | `process \| fs \| env \| blocking_sync` *(+ `alloc` on `output`)* | `0x040D` / `0x044D` | `reactor.vtable.proc_spawn(ctx, &cmd_spec)` | Runs full `BatBadBut` `.bat`/`.cmd` and NUL validation, then dispatches to registered `SimReactor.mock_procs` handler (failing closed with `.Unsupported` if unregistered). |
| **`cx.process` Wait / Kill / Exit**<br>`ChildProcess.wait`, `kill_and_wait` / `try_wait`, `detach`, `exit` | `process \| blocking_sync` / `process` | `0x0408` / `0x0008` | `reactor.vtable.proc_wait(ctx, pid, flags)` | Joins simulated child in `SimProcTable`, returns deterministic `ExitStatus`, and verifies zero un-reaped `@linear ChildProcess` handles on test completion. |

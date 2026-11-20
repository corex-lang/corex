# Architecture, Algorithms & Canonical v1.0 APIs for CoreX cx Prelude, cx.mem, cx.col, cx.str, and cx.math (STD-01)

Phase 11.1 of CoreX (`.cx`) defines the freestanding, zero-GC foundational kernel of the `cx.*` standard library across five strictly acyclic Tier-0 through Tier-2 modules: the universal **cx prelude**, **cx.mem**, **cx.col**, **cx.str**, and **cx.math**. All dynamic containers (`Vec[T]`, `#soa Vec[T]`, `Deque[T]`, `RawTableInner`, and `String`) standardize on **24-byte headers** on 64-bit targets (`16 bytes` on `wasm32`, or `24 bytes` for `String` across all targets to preserve 23-byte inline storage) paired with an 8-byte aligned, LSB-tagged **`AllocatorHandle`** (`0 = GeneralAllocator`, `1 = BumpArenaNoFree`, `2 = StaticRoData`). Containers default to the implicit `context.allocator` for everyday ergonomics while accepting explicit `&mut Arena` and 2-slot `context.scratch[0..2]` overrides (`E0328`) that allow `MIR` Pass 1 (`ElaborateDrops`) to elide `TrivialDrop` destructors down to **zero machine instructions** at compile time. Across all five packages, runtime pre-`main` static constructors are prohibited; every lookup table is evaluated deterministically inside `MirVm` at `comptime`, deduplicated by `Wyhash(0)`, and placed in its own `.rodata` linker section so unreferenced facilities add **zero cold-start latency and zero dead-code bytes**.

To meet CoreX's performance and footprint targets – matching C/Zig runtime speed while keeping the self-hosted `corex` binary under 1 MB and minimal freestanding `wasm32` binaries within `DR-15`'s **1.5–10 KB** envelope – each subsystem pairs SIMD/SWAR throughput with **Pointer-Shape Identical Code Folding (ICF)** and compact `.rodata` tables:

-   **cx.mem** eliminates mandatory `libc` `malloc` dependencies through a 4-instruction bump fast-path `@linear Arena` (`64 KiB` slabs plus dedicated `> 32 KiB` large-object bypass mappings), an `O(1)` intrusive `Pool[T]`, an in-place-resizable `FixedBuffer`, a direct OS/Wasm `System` allocator (`mmap` / `VirtualAlloc` on native OSes; power-of-two size-class freelists over `64 KiB` `memory.grow` bigpages on freestanding `wasm32`), and zero-`unsafe` `FromBytes` / `IntoBytes` (`@zero_pad`) byte transmutation.
-   **cx.col** builds `Context.rng`-seeded `Wyhash` SwissTables (`Map[K, V]` and `Set[T]`) atop a **type-erased `RawTableInner`** parameterized by `(elem_size, elem_align, hash_fn, eq_fn)` so instantiating `Map` across 50 nominal types compiles probing, adaptive tombstone deletion, in-place rehashing, and resizing **once**. Group probing dispatches at compile time to 16-byte `SSE2`, 16-byte `ARM64 NEON` nibble-packing (`vshrn_n_u16`), or an 8-byte branchless `u64` SWAR fallback on freestanding `wasm32`. Slice sorting pairs **`ipnsort`** for `sort_unstable` (`3,456 B` vs. `4,691 B` on `u64` in `sort-research-rs` benchmarks) with **Munro–Wild `Powersort` (`driftsort` core)** for stable `sort` (`<= N / 2` scratch memory).
-   **cx.str and cx.math** combine a Little-Endian **24-byte `SSO String`** storing up to **23 inline UTF-8 bytes** while preserving all 64 bits of `AllocatorHandle` on the heap branch (`sizeof(String?) == 24 B` via `byte[23] == 0x7F` niche); **Keiser–Lemire 3-table SIMD UTF-8 validation** (`48 B` `.rodata`); independently tree-shakeable 3-stage overlapped tries for **`wcwidth`** (`5,181 B`) and **`UAX #29` Extended Grapheme Clusters** (`4,939 B` + `234 B` 13-state DFA covering Unicode 17/18 `GB9c` Indic conjuncts and `GB11` ZWJ emoji = **`10,354 B` (`10.11 KiB`) combined**, or `9,838 B` unified); **`jeaiii` 2-digit integer formatting** (`200 B` table); and zero-`libc` **`Schubfach`/`Dragonbox` float formatting** + **`Eisel–Lemire` float parsing** sharing a **single `632 B` `POW5_SPLIT` `.rodata` table**.

> **Visual – Unified 24-Byte Container Headers Enable Zero-Instruction Arena Drop Elision:** Every heap-capable CoreX container occupies 3 machine words (24 bytes on 64-bit, 16 bytes on wasm32). Stealing bits 0..2 of 8-byte aligned allocator addresses distinguishes general heaps from **BumpArenaNoFree** slabs, while placing flagged_cap at bytes 20..23 of String leaves all 64 bits of AllocatorHandle intact and frees 23 inline UTF-8 bytes when bit 7 of byte 23 is zero.

Conventional Rust SSO crates such as `compact_str` (`CompactString`) store inline lengths as `0xC0 | len` in byte 23 and rely on the third 64-bit word holding an untagged `usize` capacity smaller than `2^56`. In CoreX, placing `AllocatorHandle` at bytes `16..23` of `String` would collide with byte 23 whenever an allocator resides at a high canonical virtual address (such as kernel space `0xFFFF_8000_...` or ARM64 Top-Byte-Ignore pointers). Reordering `String`'s non-inline fields to `{ ptr: *mut u8, alloc: AllocatorHandle, len: u32, flagged_cap: u32 }` places `flagged_cap = cap | 0x8000_0000_u32` at bytes `20..23` on Little-Endian architectures. Byte 23 is therefore guaranteed to have bit 7 set (`>= 0x80`) on every heap or `.rodata` string and bit 7 clear (`0x00..=0x17`) on every inline string of `0..=23` bytes – preserving all 64 bits of `AllocatorHandle` in bytes `8..15`, making zeroed memory `[0_u8; 24]` a valid empty `""` string, and leaving `0x18..=0x7F` (104 bit-patterns, with `0x7F` designated for `Option.None`) as niches so `sizeof(String?) == 24`.

---

## 1. Deliverable 1: Complete Canonical CoreX v1.0 Public API Catalog

All public signatures below strictly follow the finalized CoreX v1.0 specification in `PLAN.md`, `DR-04`, `DR-06`, `DR-15`, `DR-20`, `DR-21`, and `DR-22`: `cx.*` namespaces, unified `.` paths, `and`/`or`/`not` and `~x` operators, `let`/`var` bindings, MVS parameter modes (`[var] x: T`, `&T`, `&mut T`, `[var] x: own T`, `&out T`), `/` positional-only and `*` keyword-only parameter zones, payload-first `T!E` and `T?` types, `@attr(key: val)` annotations, omitted `-> unit` return types, and `@no_alloc` / `@no_panic` capability contracts.

### 1.1 Universal cx Prelude (core/prelude.cx Re-Exported via cx.*)

The universal prelude is implicitly in scope in every `.cx` module without `use` statements, while direct user `use core.*` imports are gated behind `--internal-core` (`E0218`). Alongside the 20 primitives (`i8`..`i128`, `u8`..`u128`, `isize`, `usize`, `f32`, `f64`, `bool`, `char`, `str`, `unit`, `never`, `opaque`) and the built-in Constrained Type Groups (`Signed`, `Unsigned`, `Integer`, `Float`, `Number`, `Scalar`, `Bytes`, `Comparable`, `Equatable`, `Copy`, `TrivialDrop`, `FromBytes`, `IntoBytes`), the prelude exposes core comparison, hashing, formatting, `SourceLoc`, and `Context` types.

```rust
// File: stdlib/cx/mod.cx (re-exporting core/prelude.cx + Phase 11.1 modules)
mod cx;

pub mod mem;
pub mod col;
pub mod str;
pub mod math;

@derive(Copy, Equatable)
pub enum Ordering: i8 {
    Less    = -1,
    Equal   = 0,
    Greater = 1,
}

pub trait Equatable {
    fn eq(&self, other: &Self, /) -> bool;
}

pub trait Comparable: Equatable {
    fn cmp(&self, other: &Self, /) -> Ordering;
}

pub trait Hasher {
    @no_alloc @no_panic
    fn write(&mut self, bytes: &[u8], /);

    @no_alloc @no_panic
    fn write_u64(&mut self, word: u64, /) {
        self.write(&word.to_le_bytes());
    }

    @no_alloc @no_panic
    fn finish(&self) -> u64;
}

pub trait Hash {
    @no_alloc @no_panic
    fn hash[H: Hasher](&self, state: &mut H, /);
}

pub trait Default {
    fn default() -> Self;
}

pub trait Clone {
    fn clone(&self) -> Self;
}

/// Deterministic scope destructor lowered by MIR Pass 1 (`ElaborateDrops`).
pub trait AutoDrop {
    fn drop(&mut self);
}

/// 8-byte `.rodata` call-site location handle (`sizeof(SourceLoc) == @size_of[*opaque]()`).
@repr(C)
@derive(Copy, Equatable)
pub struct SourceLoc {
    rodata_ptr: *SourceLocRecord,
}

@repr(C)
pub(pkg) struct SourceLocRecord {
    pub file:    str,
    pub fn_name: str,
    pub line:    u32,
    pub col:     u32,
}

impl SourceLoc {
    @inline @no_alloc @no_panic
    pub fn file(self) -> str = unsafe { self.rodata_ptr.*.file };
    @inline @no_alloc @no_panic
    pub fn fn_name(self) -> str = unsafe { self.rodata_ptr.*.fn_name };
    @inline @no_alloc @no_panic
    pub fn line(self) -> u32 = unsafe { self.rodata_ptr.*.line };
    @inline @no_alloc @no_panic
    pub fn col(self) -> u32 = unsafe { self.rodata_ptr.*.col };
}

/// Packed 8-byte compile-time validated format specification (`SE-12`).
@derive(Copy, Equatable)
pub bit_field FmtSpec: u64 {
    pub fill_utf32:   u32  | 21, // Unicode scalar fill character (default ' ' = 0x20)
    pub align_mode:   u8   | 2,  // 0 = Default, 1 = Left('<'), 2 = Center('^'), 3 = Right('>')
    pub sign_plus:    bool | 1,  // '+'
    pub alt_prefix:   bool | 1,  // '#' (0x, 0b, 0o, trailing decimal point)
    pub zero_pad:     bool | 1,  // '0'
    pub has_prec:     bool | 1,  // '.prec' present
    pub verb:         u8   | 4,  // 0=Display, 1=Debug('?'), 2='x', 3='X', 4='b', 5='o', 6='e', 7='E', 8='f', 9='p'
    pub _reserved:    u8   | 1,
    pub width:        u16  | 16,
    pub precision:    u16  | 16, // Exact sum = 64 bits (`ADR-22D` `E0423`)
}

@derive(Copy, Equatable)
pub enum FmtError: u8 {
    BufferFull = 1,
    IoFailure  = 2,
}

/// Direct function-pointer byte sink (`16 B` on 64-bit, `8 B` on `wasm32`; zero heap vtables).
@repr(C)
pub struct FmtWriter {
    pub ctx:      *mut opaque,
    pub write_fn: fn(*mut opaque, &[u8]) -> unit!FmtError,
}

impl FmtWriter {
    @inline @no_alloc
    pub fn write_bytes(&mut self, bytes: &[u8], /) -> unit!FmtError =
        (self.write_fn)(self.ctx, bytes);

    @inline @no_alloc
    pub fn write_str(&mut self, s: str, /) -> unit!FmtError =
        (self.write_fn)(self.ctx, s.as_bytes());

    @no_alloc
    pub fn write_padded(&mut self, raw: &[u8], spec: FmtSpec, /) -> unit!FmtError;
}

pub trait Display {
    fn fmt(&self, out: &mut FmtWriter, spec: FmtSpec, /) -> unit!FmtError;
}

pub trait Debug {
    fn fmt_debug(&self, out: &mut FmtWriter, spec: FmtSpec, /) -> unit!FmtError;
}

/// 24-byte stack-resident format argument (`Depth(rho_local)` escape-checked via `E0306`).
@repr(C)
@derive(Copy)
pub struct FmtArg {
    pub data:   *opaque,
    pub fmt_fn: fn(*opaque, &mut FmtWriter, FmtSpec) -> unit!FmtError,
    pub spec:   FmtSpec,
}

/// Zero-allocation stack-resident format bundle (`32 B` on 64-bit, legal inside `@no_alloc`).
@repr(C)
@derive(Copy)
pub struct FmtArgs {
    pub pieces: &[str],
    pub args:   &[FmtArg],
}

/// Implicit thread/task Context ABI table (`with context.allocator = &mut arena { … }`).
@repr(C)
pub struct Context {
    pub allocator:    mem.AllocatorHandle,
    pub scratch:      *mut [mem.Arena; 2], // 2-slot ping-pong scratch ring (`D-04`, `E0328`)
    pub rng_seed:     *mut u64,            // Deterministic PRNG state under `--sim --seed` (`Fix-18A`)
    pub logger:       *opaque,
    pub diagnostics:  *opaque,
    pub cancel_token: *opaque,
    pub reactor:      *opaque,             // Phase 8/13 `ReactorVTable` seam (`25 LOC`)
    pub trace_sink:   *mut opaque?,        // Phase 6/13.2 `FlightRing` seam (`15 LOC`)
}

@inline @no_alloc
pub fn assert(cond: bool, msg: FmtArgs = "", /, *, loc: SourceLoc = @caller_location());

@inline @no_alloc @no_panic
pub fn debug_assert(cond: bool, msg: FmtArgs = "", /, *, loc: SourceLoc = @caller_location());

@cold @no_alloc
pub fn panic(msg: FmtArgs, /, *, loc: SourceLoc = @caller_location()) -> never;

/// Zero-keyword debug inspector (`{val=}` + `@caller_location()`, `DR-22` §2.6).
pub fn dbg[T: Debug](val: own T, /, *, loc: SourceLoc = @caller_location()) -> T;
```

---

### 1.2 cx.mem: Allocators, Arenas, Pools, System Heap & Safe Byte Views

Every allocator state (`AllocatorHeader`, `Arena`, `FixedBuffer`, `System`) is aligned to at least 8 bytes so `AllocatorHandle` encodes `AllocTag` in bits `0..2` without pointer indirection.

| Type (`cx.mem.*`) | 64-Bit Size / Align | `wasm32` Size / Align | Ownership Tier | Architectural & Layout Contract |
| :--- | :---: | :---: | :---: | :--- |
| `Layout` | `16 B` / `8 B` | `8 B` / `4 B` | `Copy` | `alignment` is non-zero power of two; `size <= isize.MAX` |
| `AllocatorHandle` | `8 B` / `8 B` | `4 B` / `4 B` | `Copy` | `bits[2:0]`: `0=GeneralAllocator`, `1=BumpArenaNoFree`, `2=StaticRoData` |
| `Arena` (`BumpArena`) | `32 B` / `8 B` | `20 B` / `8 B` | `@linear` | `64 KiB` slabs + `> 32 KiB` bypass list; zero-filled on init & restore |
| `ArenaCheckpoint` | `24 B` / `8 B` | `12 B` / `4 B` | `Copy` | `(slab_ptr, bypass_head, used_offset)` for `O(1)` bulk restore |
| `Pool[T]` | `24 B` / `8 B` | `16 B` / `8 B` | `@linear` | Intrusive free-list over `64 KiB` slabs; `O(1)` alloc/free |
| `OwnPtr[T]` | `8 B` / `8 B` | `4 B` / `4 B` | `@linear` | Non-null unique pointer (`sizeof(OwnPtr[T]?) == @size_of[*mut T]()`) |
| `FixedBuffer` | `32 B` / `8 B` | `16 B` / `8 B` | `Copy` / Stack | `@no_alloc`-compatible bump allocator + last-alloc in-place `resize` |
| `Span16` | `4 B` / `2 B` | `4 B` / `2 B` | `Copy`, `FromBytes`, `IntoBytes` | Unboxed `{ off: u16, len: u16 }` `< 64 KiB` slice index |

```rust
// File: stdlib/cx/mem.cx
mod mem;

@repr(C)
@derive(Copy, Equatable)
pub struct Layout {
    pub size:      usize,
    pub alignment: usize,
}

impl Layout {
    @inline @no_alloc @no_panic
    pub comptime fn of[T]() -> Layout = Layout {
        size: @size_of[T](),
        alignment: @align_of[T](),
    };

    @inline @no_alloc @no_panic
    pub fn array[T](count: usize, /) -> Layout!AllocError {
        let elem_sz = @size_of[T]();
        if elem_sz != 0 and count > (isize.MAX as usize) / elem_sz {
            return .Err(.InvalidLayout);
        }
        .Ok(Layout { size: count * elem_sz, alignment: @align_of[T]() })
    }
}

@derive(Copy, Equatable)
pub enum AllocError: u8 {
    OutOfMemory   = 1,
    InvalidLayout = 2,
}

@derive(Copy, Equatable)
pub enum AllocTag: u8 {
    GeneralAllocator = 0, // Invokes `AllocatorHeader.dealloc_fn` on drop
    BumpArenaNoFree  = 1, // Elides `dealloc`; bulk-reclaimed by `Arena.restore` / `release`
    StaticRoData     = 2, // Immutable `.rodata` / `comptime`-promoted buffer; never freed
}

pub trait Allocator {
    fn alloc(&mut self, layout: Layout, /) -> *mut u8!AllocError;
    fn resize(&mut self, ptr: *mut u8, old_layout: Layout, new_size: usize, /) -> bool;
    fn realloc(&mut self, ptr: *mut u8, old_layout: Layout, new_size: usize, /) -> *mut u8!AllocError;
    fn dealloc(&mut self, ptr: *mut u8, layout: Layout, /);
}

/// Intrusive vtable placed at offset 0 of any `GeneralAllocator` instance (`align(8)`).
@repr(C, align(8))
pub struct AllocatorHeader {
    pub alloc_fn:   fn(*mut opaque, Layout) -> *mut u8!AllocError,
    pub resize_fn:  fn(*mut opaque, *mut u8, Layout, usize) -> bool,
    pub realloc_fn: fn(*mut opaque, *mut u8, Layout, usize) -> *mut u8!AllocError,
    pub dealloc_fn: fn(*mut opaque, *mut u8, Layout),
}

/// 8-byte aligned LSB-tagged allocator pointer (`sizeof(AllocatorHandle) == @size_of[usize]()`).
@repr(C)
@derive(Copy, Equatable)
pub struct AllocatorHandle {
    pub raw_tagged_ptr: usize,
}

impl AllocatorHandle {
    pub const STATIC_RODATA: AllocatorHandle = AllocatorHandle { raw_tagged_ptr: 0x2_usize };

    @inline @no_alloc @no_panic
    pub fn tag(self) -> AllocTag = (self.raw_tagged_ptr & 0x3_usize) as AllocTag;

    @inline @no_alloc @no_panic
    pub fn is_arena_or_static(self) -> bool = (self.raw_tagged_ptr & 0x3_usize) != 0;

    @no_alloc
    pub fn alloc(self, layout: Layout, /) -> *mut u8!AllocError;
    @no_alloc @no_panic
    pub fn resize_in_place(self, ptr: *mut u8, old_layout: Layout, new_size: usize, /) -> bool;
    @no_alloc
    pub fn realloc(self, ptr: *mut u8, old_layout: Layout, new_size: usize, /) -> *mut u8!AllocError;
    @no_alloc @no_panic
    pub fn dealloc(self, ptr: *mut u8, layout: Layout, /);
}

@repr(C)
@derive(Copy, Equatable)
pub struct ArenaCheckpoint {
    pub(pkg) slab_ptr:    *mut SlabHeader?,
    pub(pkg) bypass_head: *mut BypassHeader?,
    pub(pkg) used_offset: u32,
}

/// Tier-3 `@linear` 64 KiB page-slab bump arena (`align(8)` so `as_handle()` steals bit 0).
@repr(C, align(8))
@linear
pub struct Arena {
    pub(pkg) current_slab: *mut SlabHeader?,
    pub(pkg) first_slab:   *mut SlabHeader?,
    pub(pkg) bypass_head:  *mut BypassHeader?,
    pub(pkg) used_offset:  u32,
    pub(pkg) default_cap:  u32,
}

pub type BumpArena = Arena;

impl Arena {
    pub const DEFAULT_SLAB_BYTES: usize = 65_536;
    pub const BYPASS_THRESHOLD: usize   = 32_768;

    @no_panic
    pub fn new(*, slab_bytes: usize = Self.DEFAULT_SLAB_BYTES) -> Self;
    pub fn with_capacity(min_bytes: usize, /) -> Self!AllocError;

    @inline @no_alloc @no_panic
    pub fn as_handle(&mut self) -> AllocatorHandle =
        AllocatorHandle { raw_tagged_ptr: (&raw mut self.* as usize) | 0x1_usize };

    @inline @no_alloc @no_panic
    pub fn checkpoint(&self) -> ArenaCheckpoint;

    @no_alloc @no_panic
    pub fn restore(&mut self, cp: ArenaCheckpoint, /);

    @no_alloc @no_panic
    pub fn reset(&mut self);

    @no_panic
    pub fn release(var own self);

    pub fn create[T](&mut self, val: own T, /) -> &mut T;
    pub fn try_create[T](&mut self, val: own T, /) -> (&mut T)!AllocError;
    pub fn alloc_slice[T: Copy](&mut self, count: usize, /, *, zeroed: bool = true) -> &mut [T];
    pub fn try_alloc_slice[T: Copy](&mut self, count: usize, /, *, zeroed: bool = true) -> (&mut [T])!AllocError;
    pub fn dupe[T: Copy](&mut self, src: &[T], /) -> &mut [T];
    pub fn dupe_str(&mut self, s: str, /) -> str;
    pub fn fmt(&mut self, args: FmtArgs, /) -> str;
}

/// 2-slot ping-pong scratch helper (`DR-20` `D-04`; unguarded conflict rejected at compile time via `E0328`).
pub fn with_scratch[R](
    conflict: AllocatorHandle = AllocatorHandle.STATIC_RODATA,
    /,
    body: |&mut Arena| -> R,
) -> R;

/// `@linear` non-null unique pointer (`0x0` niche -> `sizeof(OwnPtr[T]?) == @size_of[*mut T]()`).
@repr(C)
@linear
pub struct OwnPtr[T] {
    ptr: *mut T is 1..=usize.MAX,
}

impl[T] OwnPtr[T] {
    pub fn new(val: own T, /) -> Self;
    pub fn try_new(val: own T, /) -> Self!AllocError;
    @inline @no_alloc @no_panic pub fn as_ref(&self) -> &T = unsafe { &self.ptr.* };
    @inline @no_alloc @no_panic pub fn as_mut(&mut self) -> &mut T = unsafe { &mut self.ptr.* };
    pub fn into_inner(own self) -> T;
    pub fn free(own self);
}

/// `@linear` typed slab pool (`O(1)` alloc/free; slot stride = `align_up(max(sizeof(T), sizeof(usize)), align_of(T))`).
@repr(C, align(8))
@linear
pub struct Pool[T] {
    slab_head:  *mut PoolSlabHeader?,
    free_head:  *mut PoolFreeNode?,
    slab_items: u32,
    live_count: u32,
}

impl[T] Pool[T] {
    @no_panic pub fn new(*, items_per_slab: u32 = 1024) -> Self;
    pub fn try_alloc(&mut self, val: own T, /) -> OwnPtr[T]!AllocError;
    pub fn alloc(&mut self, val: own T, /) -> OwnPtr[T];
    @no_alloc @no_panic pub fn free(&mut self, item: own OwnPtr[T], /);
    @inline @no_alloc @no_panic pub fn live_len(&self) -> usize = self.live_count as usize;
    @no_panic pub fn release(var own self);
}

/// Stack / static buffer bump allocator usable inside `@no_alloc` functions (`header` enables `as_handle()`).
@repr(C, align(8))
pub struct FixedBuffer {
    header: *AllocatorHeader,
    buf:    *mut u8,
    cap:    usize,
    used:   usize,
}

impl FixedBuffer {
    @inline @no_alloc @no_panic pub fn init(backing: &mut [u8], /) -> Self;
    @inline @no_alloc @no_panic pub fn as_handle(&mut self) -> AllocatorHandle;
    @inline @no_alloc @no_panic pub fn reset(&mut self) { self.used = 0; }
    @inline @no_alloc @no_panic pub fn remaining(&self) -> usize = self.cap - self.used;
}

impl Allocator for FixedBuffer {
    @no_alloc @no_panic fn alloc(&mut self, layout: Layout, /) -> *mut u8!AllocError;
    @no_alloc @no_panic fn resize(&mut self, ptr: *mut u8, old_layout: Layout, new_size: usize, /) -> bool;
    @no_alloc @no_panic fn realloc(&mut self, ptr: *mut u8, old_layout: Layout, new_size: usize, /) -> *mut u8!AllocError;
    @no_alloc @no_panic fn dealloc(&mut self, ptr: *mut u8, layout: Layout, /);
}

/// Zero-`libc` OS / freestanding WebAssembly allocator (`mmap` / `VirtualAlloc` / `memory.grow`).
pub struct System {}

impl System {
    @no_alloc @no_panic pub fn handle() -> AllocatorHandle;
    pub fn alloc_pages(byte_len: usize, /) -> *mut u8!AllocError;
    @no_panic pub fn free_pages(ptr: *mut u8, byte_len: usize, /);
}

/// Unboxed 4-byte buffer span (`FromBytes` + `IntoBytes` via `@zero_pad`).
@repr(C)
@zero_pad
@derive(Copy, Equatable, Comparable)
pub struct Span16 {
    pub off: u16 = 0,
    pub len: u16 = 0,
}

impl Span16 {
    pub const EMPTY: Span16 = Span16 { .. };

    @inline @no_alloc @no_panic
    pub fn slice(self, buf: &[u8], /) -> &[u8]? =
        if (end := (self.off as usize) + (self.len as usize)) <= buf.len() {
            .Some(buf[self.off as usize .. end])
        } else {
            .None
        };
}

// --- Zero-Unsafe Wire Transmutation (`DR-20` `D-01`) & Endian Byte Cursors ---

@derive(Copy, Equatable)
pub enum WireError: u8 {
    UnexpectedEof = 1,
    MisalignedPtr = 2,
    SizeMismatch  = 3,
}

@inline @no_alloc @no_panic
pub fn align_up(addr: usize, align: usize, /) -> usize? {
    let mask = align - 1;
    if addr > usize.MAX - mask { return .None; }
    .Some((addr + mask) & ~mask)
}

@inline @no_alloc @no_panic
pub fn swap[T](a: &mut T, b: &mut T, /) {
    (a.*, b.*) = (b.*, a.*);
}

@inline @no_alloc @no_panic
pub fn replace[T](dest: &mut T, src: own T, /) -> T {
    var tmp = src;
    (dest.*, tmp) = (own tmp, own dest.*);
    tmp
}

@inline @no_alloc @no_panic
pub fn view_bytes[T: FromBytes](buf: &[u8], /) -> (&T)!WireError {
    if buf.len() < @size_of[T]() { return .Err(.UnexpectedEof); }
    if (buf.as_ptr() as usize) & (@align_of[T]() - 1) != 0 { return .Err(.MisalignedPtr); }
    .Ok(unsafe { &(buf.as_ptr() as *T).* })
}

@inline @no_alloc @no_panic
pub fn view_slice_bytes[T: FromBytes](buf: &[u8], count: usize, /) -> (&[T])!WireError;

@inline @no_alloc @no_panic
pub fn as_bytes[T: IntoBytes](val: &T, /) -> &[u8] =
    unsafe { @slice_from_raw_parts(&raw val.* as *u8, @size_of[T]()) };

@inline @no_alloc @no_panic
pub fn as_bytes_mut[T: FromBytes + IntoBytes](val: &mut T, /) -> &mut [u8] =
    unsafe { @slice_from_raw_parts_mut(&raw mut val.* as *mut u8, @size_of[T]()) };

@inline @no_alloc @no_panic
pub fn read_le[T: Integer | Float](buf: &[u8], offset: usize = 0, /) -> T!WireError;
@inline @no_alloc @no_panic
pub fn read_be[T: Integer | Float](buf: &[u8], offset: usize = 0, /) -> T!WireError;
@inline @no_alloc @no_panic
pub fn write_le[T: Integer | Float](buf: &mut [u8], offset: usize, val: T, /) -> unit!WireError;
@inline @no_alloc @no_panic
pub fn write_be[T: Integer | Float](buf: &mut [u8], offset: usize, val: T, /) -> unit!WireError;

pub struct ByteCursor {
    pub buf: &[u8],
    pub pos: usize = 0,
}

impl ByteCursor {
    @inline @no_alloc @no_panic pub fn new(buf: &[u8], /) -> Self = Self { buf: buf, pos: 0 };
    @inline @no_alloc @no_panic pub fn remaining(&self) -> usize = self.buf.len() - self.pos;
    @no_alloc @no_panic pub fn take(&mut self, n: usize, /) -> (&[u8])!WireError;
    @no_alloc @no_panic pub fn read_le[T: Integer | Float](&mut self) -> T!WireError;
    @no_alloc @no_panic pub fn read_be[T: Integer | Float](&mut self) -> T!WireError;
    @no_alloc @no_panic pub fn view[T: FromBytes](&mut self) -> (&T)!WireError;
}
```

---

### 1.3 cx.col: Cache-Optimal Containers, Type-Erased SwissTable & Slice Algorithms

In `Deque[T]`, because ring capacity is always `0` or a power of two (`1 << k` for `k in 0..=27`, up to `134,217,728` elements), packing `exp_plus_1: u5` (`0` = empty, `1..=28` = `1 << (exp - 1)`) into bits `31..27` and `head: u27` into bits `26..0` of a single `u32` word keeps `Deque[T]` at **exact 24 bytes** on 64-bit targets (`16 bytes` on `wasm32`) alongside `Vec[T]`, `#soa Vec[T]`, and `RawTableInner`. Similarly, `SmallVec[T, N]` places `{ len_and_flag: u32, heap_cap: u32 }` (8 bytes) ahead of `union { heap: (ptr: *mut T, alloc: AllocatorHandle), inline_buf: [T; N] }` (16 bytes for `heap` on 64-bit), so `SmallVec[u8, 16]`, `SmallVec[u32, 4]`, and `SmallVec[u64, 2]` also occupy **exact 24 bytes** on the stack.

| Container (`cx.col.*`) | 64-Bit Size / Align | `wasm32` Size / Align | Ownership Tier | Backing Memory & Cache Layout |
| :--- | :---: | :---: | :---: | :--- |
| `Vec[T]` | `24 B` / `8 B` | `16 B` / `4 B` | `AutoDrop` | Contiguous `[T; cap]`; `1.5x`–`2x` growth; in-place Arena resize |
| `#soa Vec[T]` | `24 B` / `8 B` | `16 B` / `4 B` | `AutoDrop` | **Single** slab partitioned into aligned columns `[F_0; cap]..[F_m; cap]` |
| `SmallVec[T, N]` | `max(24, 8 + align8(N*sizeof(T)))` | `max(16, 8 + align4(N*sizeof(T)))` | `AutoDrop` | Inline `[T; N]` on stack; spills seamlessly to `(ptr, alloc, heap_cap)` |
| `Deque[T]` | `24 B` / `8 B` | `16 B` / `4 B` | `AutoDrop` | Power-of-two ring (`(head + i) & ((1 << exp) - 1)` wrap, 0 branches) |
| `SlotKey[V]` | `8 B` / `4 B` | `8 B` / `4 B` | `Copy` | `{ index: u32, generation: u32 is 1..=u32.MAX }` (`sizeof(SlotKey?) == 8 B`) |
| `SlotMap[K, V]` | `32 B` / `8 B` | `20 B` / `4 B` | `AutoDrop` | Single allocation `[generations: [u32; cap] \| slots: [SlotUnion[V]; cap]]` |
| `RawTableInner` | `24 B` / `8 B` | `16 B` / `4 B` | `AutoDrop` | ICF type-erased SwissTable core `[ctrl \| pad \| (K, V) buckets]` |
| `Map[K, V, H]` / `Set[T, H]` | `32 B` / `8 B` | `24 B` / `4 B` | `AutoDrop` | `RawTableInner` (`24 B`) + `u64` `Context.rng` Wyhash seed (`Fix-18A`) |

```rust
// File: stdlib/cx/col.cx
mod col;

use cx.mem.{AllocError, AllocatorHandle, Arena};

/// 24-byte contiguous dynamic array (`AutoDrop`; 0-instruction drop when `T: TrivialDrop` in `Arena`).
@repr(C)
pub struct Vec[T] {
    ptr:   *mut T,
    len:   u32,
    cap:   u32,
    alloc: AllocatorHandle,
}

impl[T] Vec[T] {
    @inline @no_alloc @no_panic pub fn new() -> Self;
    pub fn with_capacity(cap: usize, /) -> Self;
    pub fn try_with_capacity(cap: usize, /) -> Self!AllocError;
    pub fn in_arena(arena: &mut Arena, /, cap: usize = 0) -> Self;

    @inline @no_alloc @no_panic pub fn len(&self) -> usize = self.len as usize;
    @inline @no_alloc @no_panic pub fn capacity(&self) -> usize = self.cap as usize;
    @inline @no_alloc @no_panic pub fn is_empty(&self) -> bool = self.len == 0;
    @inline @no_alloc @no_panic pub fn as_slice(&self) -> &[T];
    @inline @no_alloc @no_panic pub fn as_mut_slice(&mut self) -> &mut [T];

    @inline @no_alloc
    pub subscript(idx: usize, /) -> T {
        let {
            assert(idx < (self.len as usize), "Vec index {idx=} out of bounds (len={self.len})");
            yield unsafe { (self.ptr + idx).* };
        }
        inout {
            assert(idx < (self.len as usize), "Vec index {idx=} out of bounds (len={self.len})");
            yield unsafe { &mut (self.ptr + idx).* };
        }
    }

    pub fn push(&mut self, item: own T, /);
    pub fn try_push(&mut self, item: own T, /) -> unit!AllocError;
    @no_alloc @no_panic pub fn pop(&mut self) -> T?;
    pub fn reserve(&mut self, additional: usize, /);
    pub fn try_reserve(&mut self, additional: usize, /) -> unit!AllocError;
    pub fn extend_from_slice(&mut self, src: &[T], /) where T: Copy;
    pub fn insert(&mut self, idx: usize, item: own T, /);
    pub fn remove(&mut self, idx: usize, /) -> T;
    @no_alloc pub fn swap_remove(&mut self, idx: usize, /) -> T;
    @no_alloc pub fn truncate(&mut self, new_len: usize, /);
    @no_alloc pub fn clear(&mut self);
    pub fn retain(&mut self, keep: |&T| -> bool, /);
}

/// Inline-storage SmallVec (`N` items on stack; `24 B` when `N * sizeof(T) <= 16` on 64-bit).
@repr(C)
pub struct SmallVec[T, const N: usize = 8] {
    len_and_flag: u32, // MSB 0 = inline (`len <= N`), MSB 1 = heap (`len = bits[30:0]`)
    heap_cap:     u32,
    storage:      SmallVecStorage[T, N],
}

impl[T, const N: usize] SmallVec[T, N] {
    @inline @no_alloc @no_panic pub fn new() -> Self;
    @inline @no_alloc @no_panic pub fn is_spilled(&self) -> bool = (self.len_and_flag & 0x8000_0000_u32) != 0;
    @inline @no_alloc @no_panic pub fn len(&self) -> usize = (self.len_and_flag & 0x7FFF_FFFF_u32) as usize;
    @inline @no_alloc @no_panic pub fn as_slice(&self) -> &[T];
    @inline @no_alloc @no_panic pub fn as_mut_slice(&mut self) -> &mut [T];
    pub fn push(&mut self, item: own T, /);
    pub fn try_push(&mut self, item: own T, /) -> unit!AllocError;
    @no_alloc @no_panic pub fn pop(&mut self) -> T?;
    @no_alloc pub fn clear(&mut self);
}

@derive(Copy, Equatable)
bit_field DequeHeadExp: u32 {
    pub head:       u32 | 27, // Ring start index `0 .. 2^27 - 1`
    pub exp_plus_1: u8  | 5,  // `0` = unallocated (`cap = 0`), `1..=28` = `cap = 1 << (exp_plus_1 - 1)`
}

/// Exact 24-byte power-of-two ring buffer (`16 B` on `wasm32`).
@repr(C)
pub struct Deque[T] {
    ptr:      *mut T,
    head_exp: DequeHeadExp,
    len:      u32,
    alloc:    AllocatorHandle,
}

impl[T] Deque[T] {
    @inline @no_alloc @no_panic pub fn new() -> Self;
    pub fn with_capacity(cap: usize, /) -> Self;
    pub fn in_arena(arena: &mut Arena, /, cap: usize = 0) -> Self;
    @inline @no_alloc @no_panic pub fn len(&self) -> usize = self.len as usize;
    @inline @no_alloc @no_panic pub fn capacity(&self) -> usize;
    @inline @no_alloc @no_panic pub fn is_empty(&self) -> bool = self.len == 0;
    @no_alloc @no_panic pub fn as_slices(&self) -> (&[T], &[T]);
    pub fn push_back(&mut self, item: own T, /);
    pub fn push_front(&mut self, item: own T, /);
    @no_alloc @no_panic pub fn pop_front(&mut self) -> T?;
    @no_alloc @no_panic pub fn pop_back(&mut self) -> T?;
    @no_alloc pub fn clear(&mut self);
}

/// 64-bit generational key (`generation` refined `1..=u32.MAX` -> `0` is `Option.None` niche!).
@repr(C)
@derive(Copy, Equatable, Comparable)
pub struct SlotKey[V] {
    pub index:      u32,
    pub generation: u32 is 1..=u32.MAX,
}

/// Generational arena (`O(1)` insert/lookup/remove; odd `gen` = live, even `gen` = free).
@repr(C)
pub struct SlotMap[K, V] {
    base_ptr:  *mut u8,
    len:       u32,
    cap:       u32,
    free_head: u32, // `0xFFFF_FFFF` sentinel when freelist is empty
    @cfg(target.ptr_width == 64) _pad: u32 = 0,
    alloc:     AllocatorHandle,
}

impl[K, V] SlotMap[K, V] {
    @inline @no_alloc @no_panic pub fn new() -> Self;
    pub fn with_capacity(cap: usize, /) -> Self;
    pub fn in_arena(arena: &mut Arena, /, cap: usize = 0) -> Self;
    @inline @no_alloc @no_panic pub fn len(&self) -> usize = self.len as usize;
    @inline @no_alloc @no_panic pub fn is_empty(&self) -> bool = self.len == 0;
    pub fn insert(&mut self, val: own V, /) -> K;
    pub fn try_insert(&mut self, val: own V, /) -> K!AllocError;
    @inline @no_alloc @no_panic pub fn contains(&self, key: K, /) -> bool;
    @inline @no_alloc @no_panic pub fn get(&self, key: K, /) -> (&V)?;
    @inline @no_alloc @no_panic pub fn get_mut(&mut self, key: K, /) -> (&mut V)?;
    @no_alloc @no_panic pub fn get_disjoint_mut(&mut self, k0: K, k1: K, /) -> (&mut V, &mut V)?;
    @no_alloc @no_panic pub fn remove(&mut self, key: K, /) -> V?;
}

/// Seeded 64-bit Wyhash / rapidhash state (`Context.rng`-seeded under `--sim` per `Fix-18A`).
@derive(Copy)
pub struct WyHasher {
    state: u64,
    seed:  u64,
}

impl WyHasher {
    @inline @no_alloc @no_panic pub fn with_seed(seed: u64, /) -> Self;
}

impl Hasher for WyHasher {
    @no_alloc @no_panic fn write(&mut self, bytes: &[u8], /);
    @no_alloc @no_panic fn finish(&self) -> u64;
}

/// 24-byte type-erased SwissTable core (`growth_left` stored at `(ctrl - 8) as *mut u32` when allocated).
@repr(C)
pub(pkg) struct RawTableInner {
    pub ctrl:        *mut u8, // Points to static `.rodata` `EMPTY_CTRL_GROUP` when `bucket_mask == 0`
    pub bucket_mask: u32,     // `buckets - 1` (`0` when empty)
    pub items:       u32,     // Live `FULL` entries
    pub alloc:       AllocatorHandle,
}

/// SIMD/SWAR SwissTable open-addressed hash map (`87.5%` max load factor, `32 B` total).
@repr(C)
pub struct Map[K: Equatable + Hash, V, H: Hasher = WyHasher] {
    raw:  RawTableInner,
    seed: u64,
}

impl[K: Equatable + Hash, V, H: Hasher] Map[K, V, H] {
    @no_alloc @no_panic pub fn new() -> Self;
    pub fn with_capacity(cap: usize, /) -> Self;
    pub fn in_arena(arena: &mut Arena, /, cap: usize = 0) -> Self;

    @inline @no_alloc @no_panic pub fn len(&self) -> usize = self.raw.items as usize;
    @inline @no_alloc @no_panic pub fn capacity(&self) -> usize;
    @inline @no_alloc @no_panic pub fn is_empty(&self) -> bool = self.raw.items == 0;

    @no_alloc @no_panic pub fn contains_key(&self, key: &K, /) -> bool;
    @no_alloc @no_panic pub fn get(&self, key: &K, /) -> (&V)?;
    @no_alloc @no_panic pub fn get_mut(&mut self, key: &K, /) -> (&mut V)?;
    @no_alloc @no_panic pub fn get_key_value(&self, key: &K, /) -> (&K, &V)?;

    pub fn insert(&mut self, key: own K, val: own V, /) -> V?;
    pub fn try_insert(&mut self, key: own K, val: own V, /) -> (V?)!AllocError;
    pub fn get_or_insert_with(&mut self, key: own K, default_fn: || -> V, /) -> &mut V;
    @no_alloc @no_panic pub fn remove(&mut self, key: &K, /) -> V?;
    @no_alloc @no_panic pub fn remove_entry(&mut self, key: &K, /) -> (K, V)?;
    @no_alloc pub fn clear(&mut self);
    pub fn reserve(&mut self, additional: usize, /);
    pub fn retain(&mut self, keep: |&K, &mut V| -> bool, /);
}

pub struct Set[T: Equatable + Hash, H: Hasher = WyHasher] {
    inner: Map[T, unit, H],
}

// --- Canonical In-Place & Scratch-Backed Slice Algorithms (`cx.col.*`) ---

@no_alloc pub fn sort_unstable[T: Comparable](slice: &mut [T], /);
@no_alloc pub fn sort_unstable_by[T](slice: &mut [T], less: |&T, &T| -> bool, /);

pub fn sort[T: Comparable](slice: &mut [T], /);
pub fn sort_by[T](slice: &mut [T], less: |&T, &T| -> bool, /);
pub fn sort_by_key[T, K: Comparable](slice: &mut [T], key_fn: |&T| -> K, /);

@no_alloc @no_panic pub fn binary_search[T: Comparable](slice: &[T], target: &T, /) -> usize!usize;
@no_alloc @no_panic pub fn binary_search_by[T](slice: &[T], cmp_fn: |&T| -> Ordering, /) -> usize!usize;
@no_alloc @no_panic pub fn partition_point[T](slice: &[T], pred: |&T| -> bool, /) -> usize;

@no_alloc pub fn dedup_slice[T: Equatable](slice: &mut [T], /) -> usize;
@no_alloc pub fn partition_in_place[T](slice: &mut [T], pred: |&T| -> bool, /) -> usize;
@no_alloc pub fn select_nth_unstable[T: Comparable](slice: &mut [T], nth: usize, /);
@no_alloc @no_panic pub fn rotate_left[T](slice: &mut [T], mid: usize, /);

@inline @no_alloc @no_panic pub fn windows[T](slice: &[T], width: usize is 1..=usize.MAX, /) -> WindowsIter[T];
@inline @no_alloc @no_panic pub fn chunks[T](slice: &[T], chunk_size: usize is 1..=usize.MAX, /) -> ChunksIter[T];
```

---

### 1.4 cx.str: 24-Byte SSO String, Zero-Alloc FmtArgs, Unicode & Ergonomic Slice APIs

`cx.str` separates zero-allocation `str` views and lazy iterators from owning 24-byte `String` values (inline SSO up to 23 bytes) and explicit `&mut Arena` slice builders (`replace_in`, `join_in`) so developers get Python/Swift expressiveness without hidden minor-heap churn.

```rust
// File: stdlib/cx/str.cx
mod str;

use cx.mem.{AllocError, AllocatorHandle, Arena};

/// 24-byte UTF-8 String with 23-byte Little-Endian Small String Optimization (`SSO`).
/// `sizeof(String) == 24`, `sizeof(String?) == 24` (`raw_bytes[23] == 0x7F` niche).
@repr(C, align(8))
pub struct String {
    raw_bytes: [u8; 24],
}

impl String {
    pub const INLINE_CAP: usize = 23;

    @inline @no_alloc @no_panic
    pub comptime fn new() -> Self = Self { raw_bytes: [0_u8; 24] };

    pub fn from_str(s: str, /) -> Self;

    @inline @no_alloc @no_panic
    pub comptime fn from_static(s: str, /) -> Self;

    pub fn in_arena(arena: &mut Arena, /, s: str = "") -> Self;
    pub fn with_capacity(cap: usize, /) -> Self;
    pub fn fmt(args: FmtArgs, /) -> Self;

    @inline @no_alloc @no_panic pub fn len(&self) -> usize;
    @inline @no_alloc @no_panic pub fn capacity(&self) -> usize;
    @inline @no_alloc @no_panic pub fn is_empty(&self) -> bool = self.len() == 0;
    @inline @no_alloc @no_panic pub fn is_inline(&self) -> bool = (self.raw_bytes[23] & 0x80_u8) == 0;
    @inline @no_alloc @no_panic pub fn as_str(&self) -> str;
    @inline @no_alloc @no_panic pub fn as_bytes(&self) -> &[u8] = self.as_str().as_bytes();

    pub fn push_str(&mut self, s: str, /);
    pub fn try_push_str(&mut self, s: str, /) -> unit!AllocError;
    pub fn push_char(&mut self, ch: char, /);
    pub fn write_fmt(&mut self, args: FmtArgs, /);
    @no_alloc @no_panic pub fn clear(&mut self);
    @no_alloc pub fn truncate(&mut self, new_byte_len: usize, /);
}

impl str {
    @inline @no_alloc @no_panic pub fn len(self) -> usize;
    @inline @no_alloc @no_panic pub fn is_empty(self) -> bool = self.len() == 0;
    @inline @no_alloc @no_panic pub fn as_bytes(self) -> &[u8];
    @inline @no_alloc @no_panic pub fn as_ptr(self) -> *u8;

    @inline @no_alloc @no_panic pub fn starts_with(self, prefix: str, /) -> bool;
    @inline @no_alloc @no_panic pub fn ends_with(self, suffix: str, /) -> bool;
    @inline @no_alloc @no_panic pub fn strip_prefix(self, prefix: str, /) -> str?;
    @inline @no_alloc @no_panic pub fn strip_suffix(self, suffix: str, /) -> str?;
    @no_alloc @no_panic pub fn contains(self, needle: str, /) -> bool;
    @no_alloc @no_panic pub fn find(self, needle: str, /) -> usize?;
    @no_alloc @no_panic pub fn rfind(self, needle: str, /) -> usize?;
    @no_alloc @no_panic pub fn eq_ascii_ignore_case(self, other: str, /) -> bool;

    @no_alloc @no_panic pub fn trim(self, *, chars: str = " \t\r\n") -> str;
    @no_alloc @no_panic pub fn trim_start(self, *, chars: str = " \t\r\n") -> str;
    @no_alloc @no_panic pub fn trim_end(self, *, chars: str = " \t\r\n") -> str;

    @inline @no_alloc @no_panic pub fn split(self, sep: str = " ", /, *, keep_empty: bool = true) -> SplitIter;
    @inline @no_alloc @no_panic pub fn split_whitespace(self) -> SplitWhitespaceIter;
    @no_alloc @no_panic pub fn split_once(self, sep: str, /) -> (str, str)?;
    @no_alloc @no_panic pub fn rsplit_once(self, sep: str, /) -> (str, str)?;
    @inline @no_alloc @no_panic pub fn lines(self) -> LinesIter;

    @inline @no_alloc @no_panic pub fn chars(self) -> CharsIter;
    @inline @no_alloc @no_panic pub fn char_indices(self) -> CharIndicesIter;
    @inline @no_alloc @no_panic pub fn graphemes(self) -> GraphemeIter;
    @no_alloc @no_panic pub fn display_width(self) -> usize;

    pub fn replace(self, from: str, to: str, /, *, max_count: usize = usize.MAX) -> String;
    pub fn replace_in(self, arena: &mut Arena, from: str, to: str, /, *, max_count: usize = usize.MAX) -> str;
}

pub fn join(parts: &[str], sep: str = "", /) -> String;
pub fn join_in(arena: &mut Arena, parts: &[str], sep: str = "", /) -> str;

@derive(Copy, Equatable)
pub struct Utf8Error {
    pub valid_up_to: usize,
    pub error_len:   u8?,
}

@no_alloc @no_panic pub fn validate_utf8(bytes: &[u8], /) -> bool;
@no_alloc @no_panic pub fn from_utf8(bytes: &[u8], /) -> str!Utf8Error;
@no_alloc @no_panic pub fn char_width(ch: char, /) -> i8;

@derive(Copy, Equatable)
pub enum ParseIntError: u8 { Empty = 1, InvalidDigit = 2, Overflow = 3 }

@derive(Copy, Equatable)
pub enum ParseFloatError: u8 { Empty = 1, InvalidSyntax = 2 }

@no_alloc @no_panic pub fn parse_int[T: Integer](s: str, /, *, radix: u8 is 2..=36 = 10) -> T!ParseIntError;
@no_alloc @no_panic pub fn parse_float[T: Float](s: str, /) -> T!ParseFloatError;

@no_alloc @no_panic pub fn format_int[T: Integer](buf: &mut [u8], val: T, /, *, radix: u8 is 2..=36 = 10, upper: bool = false) -> str!FmtError;
@no_alloc @no_panic pub fn format_float[T: Float](buf: &mut [u8], val: T, /) -> str!FmtError;
@no_alloc pub fn format_into(buf: &mut [u8], args: FmtArgs, /) -> str!FmtError;
```

#### Cross-Language API & Allocation-Contract Comparison for Everyday String Tasks

The matrix below compares API ergonomics and memory allocation contracts across Python, Rust, Swift, Zig, and CoreX (no independent cross-language runtime microbenchmark of these slice helpers is included in the reference material):

| Everyday String Operation | Python 3.13 | Rust (`std`) | Swift 6 | Zig (`std.mem`) | CoreX v1.0 (`cx.str`) & Allocation Contract |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Trim whitespace or custom set** | `s.strip()` / `s.strip("/")` *(allocates `str`)* | `s.trim()` / `s.trim_matches('/')` *(0 alloc)* | `s.trimmingCharacters(in: ...)` *(Foundation)* | `mem.trim(u8, s, " \t\r\n")` *(3-arg call)* | `s.trim()` or `s.trim(chars: "/")` **(0-alloc `str` view)** |
| **Strip prefix or suffix & branch** | `s.removeprefix("0x")` *(no match bool)* | `if let Some(r) = s.strip_prefix("0x")` | `if s.hasPrefix("0x") { s.dropFirst(2) }` | `if (mem.startsWith(u8, s, "0x")) s[2..]` | `if s.strip_prefix("0x") is .Some(r)` / `s.strip_suffix(".cx")` **(0 alloc, left-to-right `SE-01`)** |
| **Split key=value with fallback** | `k, _, v = s.partition("=")` *(3-tuple)* | `s.split_once('=').unwrap_or((s, ""))` | `s.split(separator: "=", maxSplits: 1)` *(Array)* | `var it = mem.splitScalar(u8, s, '=');` | `let (k, v) = s.split_once("=") orelse (s, "");` **(0 alloc)** |
| **Lazy `split` & CRLF/LF `lines`** | `s.split(",")` / `s.splitlines()` *(allocates `list`)* | `s.split(',')` / `s.lines()` *(0 alloc)* | `s.split(separator: ",")` *(allocates `Array`)* | `mem.splitSequence(u8, s, ",")` *(verbose)* | `for tok, i in s.split(",")` / `for ln in s.lines()` **(0 alloc, preserves blank lines)** |
| **Replace & join strings** | `s.replace(a, b)` / `",".join(xs)` *(heap)* | `s.replace(a, b)` / `xs.join(",")` *(always heap)* | `xs.joined(separator: ",")` *(SSO <= 15 B)* | `try mem.join(alloc, ",", xs)` *(manual free)* | `s.replace(a, b)` / `cx.str.join(xs, ",")` **(0 heap alloc if `<= 23 B` SSO; or `join_in(&mut arena, ...)` with 0-inst drop)** |

---

### 1.5 cx.math: Zero-libc Scalar, Bitwise, Overflow & IEEE-754 Transcendental APIs

All `cx.math` operations compile without linking system `libm` or `libc`, using Bind-Once Constrained Type Groups (`Float`, `Integer`, `Unsigned`, `Comparable`) for clean monomorphized signatures.

```rust
// File: stdlib/cx/math.cx
mod math;

pub const PI:        f64 = 3.14159265358979323846_f64;
pub const TAU:       f64 = 6.28318530717958647692_f64;
pub const FRAC_PI_2: f64 = 1.57079632679489661923_f64;
pub const FRAC_PI_4: f64 = 0.78539816339744830962_f64;
pub const E:         f64 = 2.71828182845904523536_f64;
pub const LN_2:      f64 = 0.69314718055994530942_f64;
pub const LN_10:     f64 = 2.30258509299404568402_f64;
pub const LOG2_E:    f64 = 1.44269504088896340736_f64;
pub const LOG10_2:   f64 = 0.30102999566398119521_f64;
pub const SQRT_2:    f64 = 1.41421356237309504880_f64;

@inline @no_alloc @no_panic pub fn min(a: Comparable, b: Comparable, /) -> Comparable = if b < a { b } else { a };
@inline @no_alloc @no_panic pub fn max(a: Comparable, b: Comparable, /) -> Comparable = if a < b { b } else { a };
@inline @no_alloc @no_panic pub fn clamp(val: Comparable, lo: Comparable, hi: Comparable, /) -> Comparable =
    if val < lo { lo } else if val > hi { hi } else { val };

@inline @no_alloc @no_panic pub fn div_ceil[T: Unsigned](a: T, b: T is 1..=T.MAX, /) -> T;
@inline @no_alloc @no_panic pub fn div_floor[T: Integer](a: T, b: T, /) -> T?;
@inline @no_alloc @no_panic pub fn is_power_of_two[T: Unsigned](x: T, /) -> bool = x != 0 and (x & (x -% 1)) == 0;
@inline @no_alloc @no_panic pub fn next_power_of_two[T: Unsigned](x: T, /) -> T?;
@inline @no_alloc @no_panic pub fn ilog2[T: Unsigned](x: T is 1..=T.MAX, /) -> u32;
@inline @no_alloc @no_panic pub fn ilog10[T: Unsigned](x: T is 1..=T.MAX, /) -> u32;

// Checked (`T?`), Wrapping (`+%` / `wrapping_*`), Saturating (`+|` / `saturating_*`), and Widening Ops:
@inline @no_alloc @no_panic pub fn checked_add(a: Integer, b: Integer, /) -> Integer?;
@inline @no_alloc @no_panic pub fn checked_sub(a: Integer, b: Integer, /) -> Integer?;
@inline @no_alloc @no_panic pub fn checked_mul(a: Integer, b: Integer, /) -> Integer?;
@inline @no_alloc @no_panic pub fn checked_div(a: Integer, b: Integer, /) -> Integer?;
@inline @no_alloc @no_panic pub fn checked_shl[T: Integer](a: T, shift: u32, /) -> T?;
@inline @no_alloc @no_panic pub fn checked_shr[T: Integer](a: T, shift: u32, /) -> T?;
@inline @no_alloc @no_panic pub fn wrapping_shl[T: Integer](a: T, shift: u32, /) -> T;
@inline @no_alloc @no_panic pub fn wrapping_shr[T: Integer](a: T, shift: u32, /) -> T;
@inline @no_alloc @no_panic pub fn saturating_add(a: Integer, b: Integer, /) -> Integer = a +| b;
@inline @no_alloc @no_panic pub fn saturating_sub(a: Integer, b: Integer, /) -> Integer = a -| b;
@inline @no_alloc @no_panic pub fn saturating_mul(a: Integer, b: Integer, /) -> Integer = a *| b;
@inline @no_alloc @no_panic pub fn widening_mul_u64(a: u64, b: u64, /) -> (u64, u64); // `(lo, hi)`
@inline @no_alloc @no_panic pub fn carrying_add_u64(a: u64, b: u64, carry_in: bool, /) -> (u64, bool);

// IEEE-754 Bit, ULP & Approximate Equality Helpers:
@inline @no_alloc @no_panic pub fn is_nan(x: Float, /) -> bool = x != x;
@inline @no_alloc @no_panic pub fn is_finite(x: Float, /) -> bool;
@inline @no_alloc @no_panic pub fn is_subnormal(x: Float, /) -> bool;
@inline @no_alloc @no_panic pub fn copysign(mag: Float, sgn: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn next_up(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn next_down(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn ulp(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn total_cmp(a: Float, b: Float, /) -> Ordering;
@inline @no_alloc @no_panic pub fn degrees_to_radians(deg: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn radians_to_degrees(rad: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn approx_eq_abs(a: Float, b: Float, /, *, tol: Float) -> bool;
@inline @no_alloc @no_panic pub fn approx_eq_rel(a: Float, b: Float, /, *, rel_tol: Float = 1.0e-12) -> bool;
@no_alloc @no_panic pub fn approx_eq_ulp(a: f64, b: f64, /, *, max_ulps: u64 = 4) -> bool;

// Hardware-Intrinsic Rounding, FMA & Zero-libc Minimax Elementary Transcendentals:
@inline @no_alloc @no_panic pub fn abs[T: Signed | Float](x: T, /) -> T;
@inline @no_alloc @no_panic pub fn floor(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn ceil(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn trunc(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn round_ties_even(x: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn mul_add(a: Float, b: Float, c: Float, /) -> Float;
@inline @no_alloc @no_panic pub fn sqrt(x: Float, /) -> Float;
@no_alloc @no_panic pub fn cbrt(x: Float, /) -> Float;
@no_alloc @no_panic pub fn hypot(x: Float, y: Float, /) -> Float;
@no_alloc @no_panic pub fn frexp(x: Float, /) -> (Float, i32);
@no_alloc @no_panic pub fn ldexp(x: Float, exp2: i32, /) -> Float;

@no_alloc @no_panic pub fn sin(x: Float, /) -> Float;
@no_alloc @no_panic pub fn cos(x: Float, /) -> Float;
@no_alloc @no_panic pub fn sin_cos(x: Float, /) -> (Float, Float);
@no_alloc @no_panic pub fn tan(x: Float, /) -> Float;
@no_alloc @no_panic pub fn asin(x: Float, /) -> Float;
@no_alloc @no_panic pub fn acos(x: Float, /) -> Float;
@no_alloc @no_panic pub fn atan(x: Float, /) -> Float;
@no_alloc @no_panic pub fn atan2(y: Float, x: Float, /) -> Float;

@no_alloc @no_panic pub fn exp(x: Float, /) -> Float;
@no_alloc @no_panic pub fn exp2(x: Float, /) -> Float;
@no_alloc @no_panic pub fn expm1(x: Float, /) -> Float;
@no_alloc @no_panic pub fn ln(x: Float, /) -> Float;
@no_alloc @no_panic pub fn log2(x: Float, /) -> Float;
@no_alloc @no_panic pub fn log10(x: Float, /) -> Float;
@no_alloc @no_panic pub fn ln_1p(x: Float, /) -> Float;
@no_alloc @no_panic pub fn powf(base: Float, exp: Float, /) -> Float;
@no_alloc @no_panic pub fn powi(base: Float, exp: i32, /) -> Float;
```

---

## 2. Deliverable 2: Concrete Algorithmic & SIMD/SWAR Reference Implementations

### 2.1 Zero-libc Memory Subsystem: Arena Slabs, Pool[T], FixedBuffer, System Heap & Endian Views

CoreX's `cx.mem.Arena` avoids stranding half-used `64 KiB` slabs on oversized allocations by splitting requests at `BYPASS_THRESHOLD = 32_768` (`default_cap / 2`). Requests up to `32 KiB` bump `used_offset` inside the active `64 KiB` slab (after a 32-byte `SlabHeader` aligned to 16 bytes, leaving `65,504 B` of usable payload) in four scalar instructions; if the slab overflows and a previously restored `next` slab is already linked on the spine, `Arena` zeroes and reuses it without an OS syscall, whereas `restore(cp)` rewinds `used_offset` and zeroes the dirtied tail so `MirVm` and `corex test --sim` never observe residual bytes. Requests exceeding `32 KiB` (or alignment `> 4096`) allocate a dedicated page-rounded `BypassHeader` block linked onto `self.bypass_head`, leaving `current_slab` untouched and unmapping cleanly on `restore(cp)` or `release()`.

Similarly, `Pool[T]` computes a compile-time slot stride `STRIDE = align_up(max(@size_of[T](), @size_of[*mut PoolFreeNode]()), @align_of[T]())` so freed slots store an intrusive `PoolFreeNode` pointer at offset 0 with zero per-object metadata overhead, while `FixedBuffer.resize` checks `(ptr as usize) + old_layout.size == (self.buf as usize) + self.used` to grow or shrink the most recent allocation in `O(1)` time. On native OSes, `System` maps anonymous virtual pages (`mmap` on Linux/macOS, `VirtualAlloc` on Windows) backing thread-local power-of-two size-class bins (`16 B..32 KiB`) whose `dealloc` pushes directly onto `bins[cls]` using `Layout.size` with zero `malloc` chunk headers. On freestanding `wasm32`, `System` adopts Zig's `WasmAllocator` layout: growing `64 KiB` bigpages via `@wasm_memory_grow(0, pow2_pages)` and storing each freed slot's next-pointer at `slot_addr + slot_size - 4` so base alignment up to `64 KiB` is preserved intact.

```rust
// Reference Implementation (CoreX v1.0): `Arena`, `FixedBuffer`, `Pool[T]`, `wasm32` Heap & Endian Helpers
// File: stdlib/cx/mem_impl.cx
mod mem_impl;

use cx.mem.{AllocError, AllocatorHandle, Arena, ArenaCheckpoint, FixedBuffer, Layout, OwnPtr, Pool, System, WireError, align_up};

@repr(C, align(16))
pub(pkg) struct SlabHeader {
    pub next: *mut SlabHeader?,
    pub prev: *mut SlabHeader?,
    pub cap:  u32,
    pub _pad: u32 = 0,
}

@repr(C, align(16))
pub(pkg) struct BypassHeader {
    pub prev:      *mut BypassHeader?,
    pub map_bytes: usize,
}

const SLAB_HDR_SIZE: usize   = @size_of[SlabHeader]();
const BYPASS_HDR_SIZE: usize = @size_of[BypassHeader]();

impl Arena {
    @inline @no_panic
    pub fn alloc_raw(&mut self, layout: Layout, /) -> *mut u8!AllocError {
        if layout.alignment == 0 or (layout.alignment & (layout.alignment - 1)) != 0 {
            return .Err(.InvalidLayout);
        }
        if self.current_slab is .Some(slab) and layout.size <= (self.default_cap as usize) / 2 {
            let base_addr = (slab as usize) + (self.used_offset as usize);
            if align_up(base_addr, layout.alignment) is .Some(aligned_addr) {
                let rel_off = aligned_addr - (slab as usize);
                if layout.size <= (unsafe { slab.*.cap } as usize) -| rel_off and rel_off + layout.size <= (unsafe { slab.*.cap } as usize) {
                    self.used_offset = (rel_off + layout.size) as u32;
                    return .Ok(aligned_addr as *mut u8);
                }
            }
        }
        self.alloc_slow(layout)
    }

    @cold @no_panic
    fn alloc_slow(&mut self, layout: Layout, /) -> *mut u8!AllocError {
        if layout.size > (self.default_cap as usize) / 2 or layout.alignment > 4096 {
            let hdr_aligned = align_up(BYPASS_HDR_SIZE, layout.alignment) orelse return .Err(.InvalidLayout);
            if layout.size > usize.MAX - hdr_aligned { return .Err(.OutOfMemory); }
            let total = align_up(hdr_aligned + layout.size, 65_536) orelse return .Err(.OutOfMemory);
            let raw_page = System.alloc_pages(total)?;
            let bypass = raw_page as *mut BypassHeader;
            unsafe { bypass.* = BypassHeader { prev: self.bypass_head, map_bytes: total }; }
            self.bypass_head = .Some(bypass);
            return .Ok(unsafe { raw_page + hdr_aligned });
        }

        if self.current_slab is .Some(curr) and unsafe { curr.*.next } is .Some(reused) {
            unsafe {
                @memset((reused as *mut u8) + SLAB_HDR_SIZE, 0, (reused.*.cap as usize) - SLAB_HDR_SIZE);
            }
            self.current_slab = .Some(reused);
            self.used_offset = SLAB_HDR_SIZE as u32;
            return self.alloc_raw(layout);
        }

        let slab_bytes = self.default_cap as usize;
        let raw_slab = System.alloc_pages(slab_bytes)?;
        let hdr = raw_slab as *mut SlabHeader;
        unsafe {
            hdr.* = SlabHeader { next: .None, prev: self.current_slab, cap: slab_bytes as u32 };
            if self.current_slab is .Some(prev) { prev.*.next = .Some(hdr); } else { self.first_slab = .Some(hdr); }
        }
        self.current_slab = .Some(hdr);
        self.used_offset = SLAB_HDR_SIZE as u32;
        self.alloc_raw(layout)
    }

    @no_alloc @no_panic
    pub fn restore(&mut self, cp: ArenaCheckpoint, /) {
        while self.bypass_head != cp.bypass_head {
            let b = self.bypass_head orelse unreachable;
            self.bypass_head = unsafe { b.*.prev };
            System.free_pages(b as *mut u8, unsafe { b.*.map_bytes });
        }
        self.current_slab = cp.slab_ptr;
        self.used_offset = cp.used_offset;
        if cp.slab_ptr is .Some(slab) {
            let wipe_start = cp.used_offset as usize;
            let wipe_len = (unsafe { slab.*.cap } as usize) - wipe_start;
            unsafe { @memset((slab as *mut u8) + wipe_start, 0, wipe_len); }
        }
    }
}

/// 2-slot ping-pong scratch selector (`DR-20` `D-04`, `E0328`): selects `scratch[1]` iff `conflict` aliases `scratch[0]`.
pub fn with_scratch[R](
    conflict: AllocatorHandle = AllocatorHandle.STATIC_RODATA,
    /,
    body: |&mut Arena| -> R,
) -> R {
    let pair = unsafe { &mut context.scratch.* };
    let slot0_raw = (&raw mut pair[0] as usize) | 0x1_usize;
    let idx: usize = if conflict.raw_tagged_ptr == slot0_raw { 1 } else { 0 };
    let cp = pair[idx].checkpoint();
    defer pair[idx].restore(cp);
    body(&mut pair[idx])
}

/// `FixedBuffer` in-place last-allocation resize (`@no_alloc @no_panic`).
@no_alloc @no_panic
pub(pkg) fn fixed_buffer_resize(fb: &mut FixedBuffer, ptr: *mut u8, old: Layout, new_size: usize, /) -> bool {
    let base = fb.buf as usize;
    let addr = ptr as usize;
    if addr + old.size != base + fb.used { return false; }
    let rel = addr - base;
    if new_size > fb.cap - rel { return false; }
    fb.used = rel + new_size;
    true
}

/// `Pool[T]` O(1) intrusive freelist pop/push (`STRIDE` >= `@size_of[*mut PoolFreeNode]()`).
@repr(C)
pub(pkg) struct PoolFreeNode { pub next: *mut PoolFreeNode? }

impl[T] Pool[T] {
    @no_alloc @no_panic
    pub fn free(&mut self, item: own OwnPtr[T], /) {
        let raw_ptr = item.as_mut() as *mut T;
        unsafe { @drop_in_place(raw_ptr); }
        @forget(own item);
        let node = raw_ptr as *mut PoolFreeNode;
        unsafe { node.* = PoolFreeNode { next: self.free_head }; }
        self.free_head = .Some(node);
        self.live_count -= 1;
    }
}

/// Unaligned-safe, bounds-verified Little-Endian reader (`cx.mem.read_le`).
@inline @no_alloc @no_panic
pub fn read_le[T: Integer | Float](buf: &[u8], offset: usize = 0, /) -> T!WireError {
    const N: usize = @size_of[T]();
    if offset > buf.len() or buf.len() - offset < N {
        return .Err(.UnexpectedEof);
    }
    var raw: [u8; N] = [0_u8; N];
    unsafe { @memcpy(&raw mut raw[0] as *mut opaque, (buf.as_ptr() + offset) as *opaque, N); }
    .Ok(@from_le_bytes[T](raw))
}

@inline @no_alloc @no_panic
pub fn write_le[T: Integer | Float](buf: &mut [u8], offset: usize, val: T, /) -> unit!WireError {
    const N: usize = @size_of[T]();
    if offset > buf.len() or buf.len() - offset < N {
        return .Err(.UnexpectedEof);
    }
    let raw = @to_le_bytes[T](val);
    unsafe { @memcpy((buf.as_mut_ptr() + offset) as *mut opaque, &raw raw[0] as *opaque, N); }
    .Ok(())
}

// --- Freestanding `wasm32` Zero-libc Size-Class Allocator (`WasmAllocator` Pattern) ---
@cfg(target.arch == .Wasm32 and target.os == .Freestanding)
mod wasm_heap {
    use cx.mem.{AllocError, Layout};

    const WASM_PAGE: usize     = 65_536;
    const MIN_CLASS_LOG2: u32  = 3;  // 8 B min slot (1 B payload + 4 B tail freelist link)
    const SMALL_CLASSES: usize = 13; // 8 B .. 32 KiB
    const BIG_CLASSES: usize   = 16; // 64 KiB .. 2 GiB

    var next_addrs: [usize; SMALL_CLASSES] = [0; SMALL_CLASSES];
    var small_frees: [usize; SMALL_CLASSES] = [0; SMALL_CLASSES];
    var big_frees: [usize; BIG_CLASSES] = [0; BIG_CLASSES];

    @no_panic
    fn alloc_big_pages(pages_needed: usize, /) -> usize {
        let pow2_pages = cx.math.next_power_of_two(pages_needed) orelse return 0;
        let big_cls = cx.math.ilog2(pow2_pages) as usize;
        let slot_bytes = pow2_pages * WASM_PAGE;
        if (head := big_frees[big_cls]) != 0 {
            let tail_link = (head + slot_bytes - 4) as *usize;
            big_frees[big_cls] = unsafe { tail_link.* };
            return head;
        }
        let prev_pages = @wasm_memory_grow(0, pow2_pages);
        if prev_pages == usize.MAX { return 0; }
        prev_pages * WASM_PAGE
    }

    @no_panic
    pub fn alloc(layout: Layout, /) -> *mut u8!AllocError {
        let needed = cx.math.max(layout.size +| 4, layout.alignment);
        let slot_size = cx.math.next_power_of_two(needed) orelse return .Err(.OutOfMemory);
        let cls = (cx.math.ilog2(cx.math.max(slot_size, 8)) - MIN_CLASS_LOG2) as usize;

        if cls < SMALL_CLASSES {
            let actual_slot = 1_usize << ((cls as u32) + MIN_CLASS_LOG2);
            if (free_addr := small_frees[cls]) != 0 {
                let tail_link = (free_addr + actual_slot - 4) as *usize;
                small_frees[cls] = unsafe { tail_link.* };
                return .Ok(free_addr as *mut u8);
            }
            if (next_addrs[cls] & (WASM_PAGE - 1)) == 0 {
                let page_addr = alloc_big_pages(1);
                if page_addr == 0 { return .Err(.OutOfMemory); }
                next_addrs[cls] = page_addr;
            }
            let out = next_addrs[cls];
            next_addrs[cls] = out + actual_slot;
            return .Ok(out as *mut u8);
        }

        let pages = (needed + WASM_PAGE - 1) / WASM_PAGE;
        let big_addr = alloc_big_pages(pages);
        if big_addr == 0 { .Err(.OutOfMemory) } else { .Ok(big_addr as *mut u8) }
    }

    @no_panic
    pub fn dealloc(ptr: *mut u8, layout: Layout, /) {
        let addr = ptr as usize;
        let needed = cx.math.max(layout.size +| 4, layout.alignment);
        let slot_size = cx.math.next_power_of_two(needed) orelse return;
        let cls = (cx.math.ilog2(cx.math.max(slot_size, 8)) - MIN_CLASS_LOG2) as usize;

        if cls < SMALL_CLASSES {
            let actual_slot = 1_usize << ((cls as u32) + MIN_CLASS_LOG2);
            let tail_link = (addr + actual_slot - 4) as *mut usize;
            unsafe { tail_link.* = small_frees[cls]; }
            small_frees[cls] = addr;
        } else {
            let pow2_pages = cx.math.next_power_of_two((needed + WASM_PAGE - 1) / WASM_PAGE) orelse return;
            let big_cls = cx.math.ilog2(pow2_pages) as usize;
            let tail_link = (addr + pow2_pages * WASM_PAGE - 4) as *mut usize;
            unsafe { tail_link.* = big_frees[big_cls]; }
            big_frees[big_cls] = addr;
        }
    }
}
```

---

### 2.2 Cache-Optimal #soa Vec[T] Projection & ICF-Factored SwissTable Probing (cx.col)

For `#soa Vec[T]`, `comptime` reflection (`@type_info[T]()`) orders columns by descending alignment (`align(F_0) >= align(F_1) >= ... >= align(F_m)`) inside a **single** allocation of `cap * sum_j sizeof(F_j)` bytes, keeping `#soa Vec[T]`'s header at **24 bytes** (`{ base_ptr: *mut u8, len: u32, cap: u32, alloc: AllocatorHandle }`) with zero inter-column alignment padding when `cap` is rounded to a multiple of `align(F_0)`. Column slices (`soa_vec.pos_x`) project `&[F_k]` directly at `base_ptr + cap * prefix_bytes[k]`, while element indexing `soa_vec[i].pos_x` rewrites in `Sema` (`DR-04` §4.3) to `(col_ptr_k + i).*`, and whole-element `subscript(idx: usize) -> T` gathers `T` on `let` and writes back fields via `Fix-06B` `defer` blocks on `inout`.

> **Visual – Type-Erased SwissTable Probing Unifies 16-Byte SIMD and 8-Byte Wasm32 SWAR:** Top: A 64-bit seeded Wyhash splits into a 57-bit triangular probe index (H1) and a 7-bit fingerprint (H2). Type-erased RawTableInner routines probe 16 control bytes at once on x86-64 and ARM64 – using **vshrn_n_u16** nibble packing on NEON – and fall back cleanly to an 8-byte branchless u64 SWAR kernel on freestanding wasm32. Bottom: Outlining the quicksort loop in **ipnsort** cuts u64 unstable-sort code size by 26% (to 3,456 B), while **driftsort** achieves adaptive stable sorting in 5,294 B versus 25,520 B for glidesort.

In `cx.col.Map[K, V]`, `Map.new()` draws its 64-bit `WyHasher` seed from `context.rng_seed` via a SplitMix/WyRand step (`0x2d358dccaa6c78a5`, `0x8bb84b93962eacc9`) without allocating heap memory, guaranteeing deterministic replay under `corex test --sim --seed` (`Fix-18A`) while thwarting HashDoS collisions in production. Each 64-bit hash splits into `h1 = h >> 7` and `h2 = (h & 0x7F) as u8`, using `CTRL_EMPTY = 0xFF` (`0b1111_1111`), `CTRL_DELETED = 0x80` (`0b1000_0000`), and `0b0xxx_xxxx` for `FULL` entries. Backshift deletion is intentionally rejected in favor of **adaptive tombstone elision**: backshifting requires linear probing (degrading cache clustering) and shifts multi-cache-line `(K, V)` values on every removal, whereas SwissTable probes quadratically by `Group.WIDTH` (`pos = (pos + stride) & mask; stride += WIDTH`) and marks a removed slot `CTRL_EMPTY` (preserving `growth_left`!) whenever `empty_before.leading_zeros() + empty_after.trailing_zeros() < WIDTH`, emitting `CTRL_DELETED` only inside dense packs of `>= WIDTH` non-empty slots. When tombstones exhaust `growth_left` at low occupancy (`items <= buckets / 2`), `rehash_in_place_raw` maps `EMPTY`/`DELETED` to `EMPTY` and `FULL` to `DELETED` in parallel via `((high -% (high >> 7)) | 0x8080...)` and re-clusters keys with zero allocation. Crucially, all probing, insertion-slot search, tombstone erasure, in-place compaction, and resizing live on **non-generic `RawTableInner` functions** parameterized by `(elem_size, elem_align, hash_fn, eq_fn)` so instantiating `Map` across 50 types compiles the engine once.

```rust
// Reference Implementation (CoreX v1.0): Seeded Wyhash + Multi-Arch SwissTable `Group` + ICF `RawTableInner`
// File: stdlib/cx/col_swisstable.cx
mod col_swisstable;

use cx.mem.{AllocError, AllocatorHandle, Layout, align_up};
use cx.math.widening_mul_u64;

pub(pkg) const CTRL_EMPTY:   u8 = 0xFF_u8; // 0b1111_1111
pub(pkg) const CTRL_DELETED: u8 = 0x80_u8; // 0b1000_0000

/// Draws a deterministic per-table seed from `context.rng_seed` (`Fix-18A`, 0 syscalls, 0 allocs).
@inline @no_alloc @no_panic
pub(pkg) fn next_table_seed() -> u64 {
    let state_ptr = context.rng_seed;
    let next = unsafe { state_ptr.* } +% 0x2d35_8dcc_aa6c_78a5_u64;
    unsafe { state_ptr.* = next; }
    let (lo, hi) = widening_mul_u64(next, next ^ 0x8bb8_4b93_962e_acc9_u64);
    lo ^ hi
}

// ============================================================================
// [A] PORTABLE 8-BYTE `u64` SWAR GROUP (`wasm32` & Freestanding Fallback)
// ============================================================================
@cfg(not (target.arch is (.X86_64 | .Aarch64)))
pub(pkg) mod group_impl {
    pub const WIDTH: usize = 8;
    const REP_01: u64 = 0x0101_0101_0101_0101_u64;
    const REP_7F: u64 = 0x7F7F_7F7F_7F7F_7F7F_u64;
    const REP_80: u64 = 0x8080_8080_8080_8080_u64;

    @derive(Copy)
    pub struct BitMask { pub bits: u64 }

    impl BitMask {
        @inline @no_alloc @no_panic pub fn any(self) -> bool = self.bits != 0;
        @inline @no_alloc @no_panic pub fn trailing_zeros(self) -> usize = (self.bits.trailing_zeros() >> 3) as usize;
        @inline @no_alloc @no_panic pub fn leading_zeros(self) -> usize = (self.bits.leading_zeros() >> 3) as usize;
        @inline @no_alloc @no_panic
        pub fn next_index(&mut self) -> usize? {
            if self.bits == 0 { return .None; }
            let idx = (self.bits.trailing_zeros() >> 3) as usize;
            self.bits &= self.bits -% 1;
            .Some(idx)
        }
    }

    @derive(Copy)
    pub struct Group { word: u64 }

    impl Group {
        @inline @no_alloc @no_panic
        pub unsafe fn load(ptr: *u8, /) -> Self {
            var w: u64 = 0;
            @memcpy(&raw mut w as *mut opaque, ptr as *opaque, 8);
            Self { word: w.to_le() }
        }

        /// Exact branchless 8-byte SWAR `h2` match (5 ALU ops, zero false positives or negatives).
        @inline @no_alloc @no_panic
        pub fn match_h2(self, h2: u8, /) -> BitMask {
            let cmp = self.word ^ ((h2 as u64) *% REP_01);
            let non_zero = (cmp & REP_7F) +% REP_7F;
            BitMask { bits: ~(non_zero | cmp) & REP_80 }
        }

        /// `EMPTY` (`0xFF`) is uniquely identified by bit 7 == 1 AND bit 6 == 1 (3 ALU ops).
        @inline @no_alloc @no_panic
        pub fn match_empty(self) -> BitMask =
            BitMask { bits: (self.word & (self.word << 1)) & REP_80 };

        @inline @no_alloc @no_panic
        pub fn match_empty_or_deleted(self) -> BitMask =
            BitMask { bits: self.word & REP_80 };

        @inline @no_alloc @no_panic
        pub fn convert_special_to_empty_and_full_to_deleted(self) -> u64 {
            let high = self.word & REP_80;
            ((high -% (high >> 7)) | REP_80).to_le()
        }
    }
}

// ============================================================================
// [B] 16-BYTE SIMD GROUP (`x86_64` SSE2 `pmovmskb` & `AArch64` NEON `vshrn_n_u16`)
// ============================================================================
@cfg(target.arch is (.X86_64 | .Aarch64))
pub(pkg) mod group_impl {
    pub const WIDTH: usize = 16;
    @cfg(target.arch == .X86_64)  type MaskWord = u16;
    @cfg(target.arch == .Aarch64) type MaskWord = u64;
    @cfg(target.arch == .X86_64)  const STRIDE_SHIFT: u32 = 0;
    @cfg(target.arch == .Aarch64) const STRIDE_SHIFT: u32 = 2;

    @derive(Copy)
    pub struct BitMask { pub bits: MaskWord }

    impl BitMask {
        @inline @no_alloc @no_panic pub fn any(self) -> bool = self.bits != 0;
        @inline @no_alloc @no_panic pub fn trailing_zeros(self) -> usize = (self.bits.trailing_zeros() >> STRIDE_SHIFT) as usize;
        @inline @no_alloc @no_panic pub fn leading_zeros(self) -> usize = (self.bits.leading_zeros() >> STRIDE_SHIFT) as usize;
        @inline @no_alloc @no_panic
        pub fn next_index(&mut self) -> usize? {
            if self.bits == 0 { return .None; }
            let idx = (self.bits.trailing_zeros() >> STRIDE_SHIFT) as usize;
            self.bits &= self.bits -% 1;
            .Some(idx)
        }
    }

    @derive(Copy)
    pub struct Group { vec: cx.simd.Simd[u8, 16] }

    impl Group {
        @inline @no_alloc @no_panic
        pub unsafe fn load(ptr: *u8, /) -> Self = Self { vec: @simd_load_unaligned[u8, 16](ptr) };

        @inline @no_alloc @no_panic
        fn pack_mask(cmp_bytes: cx.simd.Simd[u8, 16], /) -> BitMask {
            @cfg(target.arch == .X86_64) {
                return BitMask { bits: @x86_pmovmskb_128(cmp_bytes) };
            }
            @cfg(target.arch == .Aarch64) {
                let narrowed: u64 = @neon_vshrn_n_u16_to_u64(cmp_bytes, const 4);
                return BitMask { bits: narrowed & 0x1111_1111_1111_1111_u64 };
            }
        }

        @inline @no_alloc @no_panic
        pub fn match_h2(self, h2: u8, /) -> BitMask =
            Self.pack_mask(@simd_eq(self.vec, cx.simd.Simd[u8, 16].splat(h2)));

        @inline @no_alloc @no_panic
        pub fn match_empty(self) -> BitMask =
            Self.pack_mask(@simd_eq(self.vec, cx.simd.Simd[u8, 16].splat(0xFF_u8)));

        @inline @no_alloc @no_panic
        pub fn match_empty_or_deleted(self) -> BitMask =
            Self.pack_mask(@simd_lt_i8(self.vec, cx.simd.Simd[u8, 16].splat(0_u8)));
    }
}

// ============================================================================
// [C] TYPE-ERASED ICF CORE (`elem_size`, `elem_align`, `hash_fn`, `eq_fn`)
// ============================================================================
const EMPTY_CTRL_GROUP: [u8; 16] = [CTRL_EMPTY; 16];

impl cx.col.RawTableInner {
    @inline @no_alloc @no_panic
    pub fn empty(alloc: AllocatorHandle, /) -> Self = Self {
        ctrl: &raw EMPTY_CTRL_GROUP[0] as *mut u8,
        bucket_mask: 0,
        items: 0,
        alloc: alloc,
    };

    /// Allocation layout: `[growth_left: u32, _pad: u32 (8B) | ctrl: buckets + WIDTH | pad | entries: buckets * elem_size]`.
    @inline @no_alloc @no_panic
    pub fn bucket_ptr(&self, idx: usize, elem_size: usize, elem_align: usize, /) -> *mut u8 {
        let buckets = (self.bucket_mask as usize) + 1;
        let entries_off = align_up(buckets + group_impl.WIDTH, elem_align) orelse unreachable;
        unsafe { self.ctrl + entries_off + idx * elem_size }
    }

    @inline @no_alloc @no_panic
    fn growth_left_mut(&mut self) -> &mut u32 = unsafe { &mut ((self.ctrl - 8) as *mut u32).* };

    @inline @no_alloc @no_panic
    pub fn set_ctrl(&mut self, idx: usize, val: u8, /) {
        let mirror_idx = ((idx -% group_impl.WIDTH) & (self.bucket_mask as usize)) +% group_impl.WIDTH;
        unsafe {
            (self.ctrl + idx).* = val;
            (self.ctrl + mirror_idx).* = val;
        }
    }

    @no_alloc @no_panic
    pub fn find_raw(
        &self,
        hash: u64,
        elem_size: usize,
        elem_align: usize,
        eq_ctx: *opaque,
        eq_fn: fn(*opaque, *u8) -> bool,
        /,
    ) -> usize? {
        if self.items == 0 { return .None; }
        let h2 = (hash & 0x7F_u64) as u8;
        let mask = self.bucket_mask as usize;
        var pos = ((hash >> 7) as usize) & mask;
        var stride: usize = 0;

        loop {
            let grp = unsafe { group_impl.Group.load(self.ctrl + pos) };
            var matches = grp.match_h2(h2);
            while matches.next_index() is .Some(lane) {
                let idx = (pos + lane) & mask;
                if eq_fn(eq_ctx, self.bucket_ptr(idx, elem_size, elem_align) as *u8) {
                    return .Some(idx);
                }
            }
            if grp.match_empty().any() { return .None; }
            stride += group_impl.WIDTH;
            pos = (pos + stride) & mask;
        }
    }

    /// Type-erased insert-or-find core parameterized by `(elem_size, elem_align, hash_fn, eq_fn)`.
    pub fn find_or_prepare_insert_raw(
        &mut self,
        hash: u64,
        seed: u64,
        elem_size: usize,
        elem_align: usize,
        eq_ctx: *opaque,
        eq_fn: fn(*opaque, *u8) -> bool,
        hash_fn: fn(u64, *u8) -> u64,
        /,
    ) -> (usize, bool)!AllocError {
        if self.bucket_mask != 0 {
            let h2 = (hash & 0x7F_u64) as u8;
            let mask = self.bucket_mask as usize;
            var pos = ((hash >> 7) as usize) & mask;
            var stride: usize = 0;
            var first_avail: usize? = .None;

            loop {
                let grp = unsafe { group_impl.Group.load(self.ctrl + pos) };
                var matches = grp.match_h2(h2);
                while matches.next_index() is .Some(lane) {
                    let idx = (pos + lane) & mask;
                    if eq_fn(eq_ctx, self.bucket_ptr(idx, elem_size, elem_align) as *u8) {
                        return .Ok((idx, true)); // Found existing key
                    }
                }
                if first_avail is .None {
                    let avail = grp.match_empty_or_deleted();
                    if avail.any() { first_avail = .Some((pos + avail.trailing_zeros()) & mask); }
                }
                if grp.match_empty().any() {
                    let slot = first_avail orelse unreachable;
                    let was_empty = unsafe { (self.ctrl + slot).* } == CTRL_EMPTY;
                    if not (was_empty and self.growth_left_mut().* == 0) {
                        if was_empty { self.growth_left_mut().* -= 1; }
                        self.set_ctrl(slot, h2);
                        self.items += 1;
                        return .Ok((slot, false));
                    }
                    break;
                }
                stride += group_impl.WIDTH;
                pos = (pos + stride) & mask;
            }
        }
        self.rehash_or_grow_raw(seed, elem_size, elem_align, hash_fn)?;
        let slot = self.find_first_avail_slot(hash);
        if unsafe { (self.ctrl + slot).* } == CTRL_EMPTY { self.growth_left_mut().* -= 1; }
        self.set_ctrl(slot, (hash & 0x7F_u64) as u8);
        self.items += 1;
        .Ok((slot, false))
    }

    @no_alloc @no_panic
    pub fn erase_slot_ctrl(&mut self, idx: usize, /) {
        let mask = self.bucket_mask as usize;
        let idx_before = (idx -% group_impl.WIDTH) & mask;
        let empty_before = unsafe { group_impl.Group.load(self.ctrl + idx_before) }.match_empty();
        let empty_after  = unsafe { group_impl.Group.load(self.ctrl + idx) }.match_empty();
        let use_tombstone = (empty_before.leading_zeros() + empty_after.trailing_zeros()) >= group_impl.WIDTH;
        if use_tombstone {
            self.set_ctrl(idx, CTRL_DELETED);
        } else {
            self.set_ctrl(idx, CTRL_EMPTY);
            self.growth_left_mut().* += 1;
        }
        self.items -= 1;
    }
}
```

---

### 2.3 Canonical Slice Sorting (ipnsort & Powersort / driftsort) and Search/Dedup Kernels

In `sort-research-rs` benchmarks by Lukas Bergdoll and Orson Peters, **95%+ of slice sorts operate on `N <= 20` elements**, where instruction-cache footprint dominates. CoreX inlines **only** the `N <= 20` insertion sort and outlines (`@noinline`) the quicksort and merge engines:
-   **`sort_unstable` (`ipnsort`):** Cuts `u64` release code size from `4,691 B` to **`3,456 B`**. It runs a single-pass `N - 1` ascending/descending scan, selects pivots via Tukey's ninther (`N >= 50`), partitions small/medium elements via **branchless cyclic Lomuto permutation** (`partition_lomuto_branchless_cyclic`, performing 2 moves per item instead of 3 with a `defer` gap-restore guard for `Fix-06B` panic safety), filters equal keys in linear time via `ancestor_pivot`, and falls back to heapsort at `2 * ilog2(N)` recursion depth.
-   **`sort` (`Powersort` / `driftsort` core):** Cuts stable sort code size from `25,520 B` (`glidesort`) to **`5,294 B`** on `u64`. For `N > 20`, it borrows `<= (N + 1) / 2` elements from `with_scratch` (`context.scratch[0..2]` – avoiding general heap allocation whenever the half-buffer fits in the `64 KiB` scratch slab!) and merges natural runs using Munro & Wild's overflow-free **node power** separator policy.

```rust
// Reference Implementation (CoreX v1.0): `ipnsort`, `Powersort`, Branchless `partition_point` & `dedup_slice`
// File: stdlib/cx/col_sort.cx
mod col_sort;

use cx.mem.{swap, with_scratch};

const SMALL_SORT_THRESHOLD: usize = 20;

@inline @no_alloc
fn insertion_sort[T](v: &mut [T], less: |&T, &T| -> bool, /) {
    var i: usize = 1;
    while i < v.len() {
        var tmp = unsafe { @ptr_read(v.as_ptr() + i) };
        var j = i;
        while j > 0 and less(&tmp, &v[j - 1]) {
            unsafe { @ptr_copy_nonoverlapping(v.as_ptr() + (j - 1), v.as_mut_ptr() + j, 1); }
            j -= 1;
        }
        unsafe { @ptr_write(v.as_mut_ptr() + j, own tmp); }
        i += 1;
    }
}

@no_alloc
fn partition_lomuto_branchless_cyclic[T](
    v: &mut [T],
    pivot: &T,
    less: |&T, &T| -> bool,
    /,
) -> usize {
    let n = v.len();
    if n == 0 { return 0; }
    let base = v.as_mut_ptr();
    var gap_val = unsafe { @ptr_read(base) };
    var gap_pos: usize = 0;
    var num_lt: usize = 0;
    var committed = false;
    defer {
        if not committed {
            unsafe { @ptr_write(base + gap_pos, own gap_val); }
        }
    }

    var right: usize = 1;
    while right < n {
        let is_lt = less(unsafe { &(base + right).* }, pivot) as usize;
        unsafe {
            @ptr_copy(base + num_lt, base + gap_pos, 1);
            @ptr_copy_nonoverlapping(base + right, base + num_lt, 1);
        }
        gap_pos = right;
        num_lt += is_lt;
        right += 1;
    }

    let gap_is_lt = less(&gap_val, pivot) as usize;
    unsafe {
        @ptr_copy(base + num_lt, base + gap_pos, 1);
        committed = true;
        @ptr_write(base + num_lt, own gap_val);
    }
    num_lt + gap_is_lt
}

@no_alloc
fn choose_pivot_ninther[T](v: &[T], less: |&T, &T| -> bool, /) -> usize {
    let n = v.len();
    let sort3 = |var a: usize, var b: usize, var c: usize| -> usize {
        if less(&v[b], &v[a]) { (a, b) = (b, a); }
        if less(&v[c], &v[b]) {
            (b, c) = (c, b);
            if less(&v[b], &v[a]) { (a, b) = (b, a); }
        }
        b
    };
    let mid = n / 2;
    if n >= 50 {
        let s = n / 8;
        return sort3(sort3(0, s, 2 * s), sort3(mid - s, mid, mid + s), sort3(n - 1 - 2 * s, n - 1 - s, n - 1));
    }
    sort3(0, mid, n - 1)
}

@noinline @no_alloc
fn ipnsort_loop[T](
    var v: &mut [T],
    var ancestor_pivot: (*T)?,
    var limit: u32,
    less: |&T, &T| -> bool,
    /,
) {
    while v.len() > SMALL_SORT_THRESHOLD {
        if limit == 0 {
            heapsort_fallback(v, less);
            return;
        }
        limit -= 1;

        let piv_idx = choose_pivot_ninther(v, less);
        if ancestor_pivot is .Some(anc_ptr) and not less(unsafe { &anc_ptr.* }, &v[piv_idx]) {
            swap(&mut v[0], &mut v[piv_idx]);
            let (piv_head, tail) = v.split_at_mut(1);
            let eq_len = partition_lomuto_branchless_cyclic(tail, &piv_head[0], |a, p| not less(p, a));
            v = v[(eq_len + 1)..];
            ancestor_pivot = .None;
            continue;
        }

        swap(&mut v[0], &mut v[piv_idx]);
        let num_lt = {
            let (piv_head, tail) = v.split_at_mut(1);
            partition_lomuto_branchless_cyclic(tail, &piv_head[0], less)
        };
        swap(&mut v[0], &mut v[num_lt]);

        let (left, right_with_piv) = v.split_at_mut(num_lt);
        let (piv_slot, right) = right_with_piv.split_at_mut(1);
        ipnsort_loop(left, ancestor_pivot, limit, less);
        ancestor_pivot = .Some(&raw piv_slot[0]);
        v = right;
    }
    insertion_sort(v, less);
}

@inline @no_alloc
pub fn sort_unstable_by[T](slice: &mut [T], less: |&T, &T| -> bool, /) {
    let n = slice.len();
    if n <= SMALL_SORT_THRESHOLD {
        if n >= 2 { insertion_sort(slice, less); }
        return;
    }
    var asc = true;
    var desc = true;
    var i: usize = 1;
    while i < n and (asc or desc) {
        if less(&slice[i], &slice[i - 1]) { asc = false; }
        if not less(&slice[i], &slice[i - 1]) { desc = false; }
        i += 1;
    }
    if asc { return; }
    if desc { slice.reverse(); return; }

    let depth_limit = 2_u32 * (cx.math.ilog2(n) + 1);
    ipnsort_loop(slice, .None, depth_limit, less);
}

/// Munro & Wild (2018) overflow-free Powersort node power (`<= N / 2` scratch merge driver).
@inline @no_alloc @no_panic
pub(pkg) fn powersort_node_power(n: usize, s1: usize, e1: usize, e2: usize, /) -> u8 {
    let denom = 2_u64 * (n as u64);
    let a = (((s1 + e1) as u64) << 30) / denom;
    let b = (((e1 + e2) as u64) << 30) / denom;
    ((a ^ b).leading_zeros() - 33) as u8
}

/// Branchless-sharpened `partition_point` (`0` bounds checks under Pentagon `mid < size <= len`).
@no_alloc @no_panic
pub fn partition_point[T](slice: &[T], pred: |&T| -> bool, /) -> usize {
    var base: usize = 0;
    var size = slice.len();
    while size > 0 {
        let half = size / 2;
        let mid = base + half;
        let go_right = pred(&slice[mid]);
        base = if go_right { mid + 1 } else { base };
        size -= half + (go_right as usize) * (1 - (size & 1));
    }
    base
}

/// Single-pass in-place deduplication returning the unique prefix length (`AutoDrop`-safe via `swap`).
@no_alloc
pub fn dedup_slice[T: Equatable](slice: &mut [T], /) -> usize {
    let n = slice.len();
    if n <= 1 { return n; }
    var write_idx: usize = 1;
    var read_idx: usize = 1;
    while read_idx < n {
        if slice[read_idx] != slice[write_idx - 1] {
            if write_idx != read_idx {
                swap(&mut slice[write_idx], &mut slice[read_idx]);
            }
            write_idx += 1;
        }
        read_idx += 1;
    }
    write_idx
}
```

---

### 2.4 24-Byte SSO String, Zero-Alloc FmtArgs Renderer & Keiser–Lemire SIMD UTF-8 (cx.str)

In `String`, placing `flagged_cap = (cap as u32) | 0x8000_0000_u32` at bytes `20..23` ensures that `(raw_bytes[23] & 0x80) == 0` identifies up to 23 inline UTF-8 bytes on both 64-bit and 32-bit Little-Endian targets while keeping all 64 bits of `AllocatorHandle` intact in bytes `8..15`. Simultaneously, `format_into` renders `FmtArgs` (`SE-12`) into any fixed `&mut [u8]` slice – or directly through `cx.io.Write` – using a stack `FmtWriter` with **zero heap allocations**, making `{expr=:#06x}` formatting legal inside `@no_alloc` interrupt and kernel paths.

```rust
// Reference Implementation (CoreX v1.0): 24-Byte Little-Endian SSO `String` + `@no_alloc` `FmtArgs` Renderer
// File: stdlib/cx/str_sso.cx
mod str_sso;

use cx.mem.{AllocError, AllocatorHandle, Layout};
use cx.str.String;

@cfg(target.ptr_width == 64)
@repr(C, align(8))
@derive(Copy)
struct HeapRepr {
    ptr:         *mut u8,         // Bytes 0..7
    alloc:       AllocatorHandle, // Bytes 8..15 (full 64-bit pointer + LSB AllocTag preserved!)
    len:         u32,             // Bytes 16..19
    flagged_cap: u32,             // Bytes 20..23 (`cap | 0x8000_0000` -> byte[23] >= 0x80 on LE)
}

@cfg(target.ptr_width == 32)
@repr(C, align(8))
@derive(Copy)
struct HeapRepr {
    ptr:         *mut u8,         // Bytes 0..3
    _pad0:       u32 = 0,         // Bytes 4..7
    alloc:       AllocatorHandle, // Bytes 8..11
    _pad1:       u32 = 0,         // Bytes 12..15
    len:         u32,             // Bytes 16..19
    flagged_cap: u32,             // Bytes 20..23 (`cap | 0x8000_0000` -> byte[23] >= 0x80 on LE)
}

impl String {
    @inline @no_alloc @no_panic
    pub fn len(&self) -> usize {
        let b23 = self.raw_bytes[23];
        if (b23 & 0x80_u8) == 0 {
            b23 as usize
        } else {
            (unsafe { (&raw self.raw_bytes as *HeapRepr).* }).len as usize
        }
    }

    @inline @no_alloc @no_panic
    pub fn as_str(&self) -> str {
        let b23 = self.raw_bytes[23];
        if (b23 & 0x80_u8) == 0 {
            unsafe { @str_from_utf8_unchecked((&raw self.raw_bytes[0])[..(b23 as usize)]) }
        } else {
            let h = unsafe { (&raw self.raw_bytes as *HeapRepr).* };
            unsafe { @str_from_utf8_unchecked(@slice_from_raw_parts(h.ptr as *u8, h.len as usize)) }
        }
    }

    @inline @no_alloc @no_panic
    pub comptime fn from_static(s: str, /) -> Self {
        if s.len() <= Self.INLINE_CAP {
            var out = Self { raw_bytes: [0_u8; 24] };
            let b = s.as_bytes();
            var i: usize = 0;
            while i < b.len() { out.raw_bytes[i] = b[i]; i += 1; }
            out.raw_bytes[23] = b.len() as u8;
            return out;
        }
        var out = Self { raw_bytes: [0_u8; 24] };
        unsafe {
            (&raw mut out.raw_bytes as *mut HeapRepr).* = HeapRepr {
                ptr: s.as_ptr() as *mut u8,
                alloc: AllocatorHandle.STATIC_RODATA,
                len: s.len() as u32,
                flagged_cap: 0x8000_0000_u32,
                ..
            };
        }
        out
    }

    pub fn try_push_str(&mut self, extra: str, /) -> unit!AllocError {
        let add_len = extra.len();
        if add_len == 0 { return .Ok(()); }
        let cur_len = self.len();
        if add_len > 0x7FFF_FFFF_usize - cur_len { return .Err(.OutOfMemory); }
        let new_len = cur_len + add_len;

        if self.is_inline() and new_len <= Self.INLINE_CAP {
            unsafe {
                @memcpy(&raw mut self.raw_bytes[cur_len] as *mut opaque, extra.as_ptr() as *opaque, add_len);
            }
            self.raw_bytes[23] = new_len as u8;
            return .Ok(());
        }

        self.reserve_non_inline(new_len)?;
        let h = unsafe { &mut (&raw mut self.raw_bytes as *mut HeapRepr).* };
        unsafe { @memcpy((h.ptr + cur_len) as *mut opaque, extra.as_ptr() as *opaque, add_len); }
        h.len = new_len as u32;
        .Ok(())
    }
}

impl AutoDrop for String {
    @inline @no_alloc @no_panic
    fn drop(&mut self) {
        if (self.raw_bytes[23] & 0x80_u8) != 0 {
            let h = unsafe { (&raw self.raw_bytes as *HeapRepr).* };
            if not h.alloc.is_arena_or_static() {
                let cap = (h.flagged_cap & 0x7FFF_FFFF_u32) as usize;
                h.alloc.dealloc(h.ptr, Layout { size: cap, alignment: 1 });
            }
        }
    }
}

// --- Zero-Allocation `FmtArgs` / `FmtSpec` Stack Slice Renderer (`SE-12`) ---

struct SliceSink {
    ptr: *mut u8,
    cap: usize,
    pos: usize,
}

@no_alloc @no_panic
fn slice_sink_write(ctx: *mut opaque, chunk: &[u8], /) -> unit!FmtError {
    let s = unsafe { &mut (ctx as *mut SliceSink).* };
    if chunk.len() > s.cap - s.pos { return .Err(.BufferFull); }
    if not chunk.is_empty() {
        unsafe { @memcpy((s.ptr + s.pos) as *mut opaque, chunk.as_ptr() as *opaque, chunk.len()); }
        s.pos += chunk.len();
    }
    .Ok(())
}

@no_alloc
pub fn render_fmt_args(out: &mut FmtWriter, args: FmtArgs, /) -> unit!FmtError {
    for arg, i in args.args {
        if not args.pieces[i].is_empty() {
            out.write_str(args.pieces[i])?;
        }
        (arg.fmt_fn)(arg.data, out, arg.spec)?;
    }
    if args.pieces.len() > args.args.len() and not args.pieces[$-1].is_empty() {
        out.write_str(args.pieces[$-1])?;
    }
    .Ok(())
}

@no_alloc
pub fn format_into(buf: &mut [u8], args: FmtArgs, /) -> str!FmtError {
    var sink = SliceSink { ptr: buf.as_mut_ptr(), cap: buf.len(), pos: 0 };
    var writer = FmtWriter { ctx: &raw mut sink as *mut opaque, write_fn: slice_sink_write };
    render_fmt_args(&mut writer, args)?;
    .Ok(unsafe { @str_from_utf8_unchecked(buf[..sink.pos]) })
}
```

#### Keiser–Lemire 3-Table SIMD + SWAR UTF-8 Validator (`48 Bytes` `.rodata`)

John Keiser and Daniel Lemire's SIMD lookup algorithm validates arbitrary UTF-8 streams using three 16-byte nibble-indexed tables (`KL_BYTE_1_HIGH`, `KL_BYTE_1_LOW`, `KL_BYTE_2_HIGH` = `48 bytes` total `.rodata`). Bitwise `AND`-ing the three parallel table shuffles (`pshufb` on SSSE3/AVX2, `vtbl` on ARM64 NEON, `i8x16.swizzle` on Wasm SIMD128) flags all seven structural UTF-8 violations (`TOO_SHORT`, `TOO_LONG`, `OVERLONG_2`, `OVERLONG_3`, `SURROGATE`, `OVERLONG_4` / `TOO_LARGE_1000` sharing bit 6, and `TOO_LARGE`), while emitting `TWO_CONTS = 0x80` on consecutive continuation bytes (`0x80..=0xBF`). Unsigned saturating subtractions on `prev2` (`0xE0 - 1`) and `prev3` (`0xF0 - 1`) set `must23_80 = 0x80` on required 3rd and 4th continuation lanes so `special ^ must23_80` cancels `0x80` on valid 3/4-byte sequences and raises `0x80` on truncated multi-byte leads.

```c
// Reference Implementation (C / SIMD Intrinsics, 1-to-1 with `stdlib/cx/str_utf8.cx`):
// Keiser–Lemire 3-Table SIMD UTF-8 Validator (48B .rodata) + 8-Byte SWAR ASCII Fast-Path
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

enum {
    KL_TOO_SHORT      = 1 << 0, // 0x01: lead byte followed by non-continuation
    KL_TOO_LONG       = 1 << 1, // 0x02: ASCII followed by continuation
    KL_OVERLONG_3     = 1 << 2, // 0x04: 0xE0 followed by 0x80..0x9F
    KL_TOO_LARGE      = 1 << 3, // 0x08: 0xF4 0x90..0xBF or 0xF5..0xFF 0x90..0xBF
    KL_SURROGATE      = 1 << 4, // 0x10: 0xED followed by 0xA0..0xBF
    KL_OVERLONG_2     = 1 << 5, // 0x20: 0xC0..0xC1 followed by 0x80..0xBF
    KL_OVERLONG_4_BIG = 1 << 6, // 0x40: 0xF0 0x80..0x8F OR 0xF5..0xFF 0x80..0x8F
    KL_TWO_CONTS      = 1 << 7  // 0x80: continuation followed by continuation
};

static const uint8_t KL_BYTE_1_HIGH[16] = {
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49
};
static const uint8_t KL_BYTE_1_LOW[16] = {
    0xE7, 0xA3, 0x83, 0x83, 0x8B, 0xCB, 0xCB, 0xCB,
    0xCB, 0xCB, 0xCB, 0xCB, 0xCB, 0xDB, 0xCB, 0xCB
};
static const uint8_t KL_BYTE_2_HIGH[16] = {
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xE6, 0xAE, 0xBA, 0xBA, 0x01, 0x01, 0x01, 0x01
};

#if defined(__SSE4_1__) || defined(__SSSE3__)
#include <tmmintrin.h>
bool cx_validate_utf8_simd(const uint8_t *buf, size_t len) {
    __m128i prev_blk = _mm_setzero_si128();
    __m128i prev_inc = _mm_setzero_si128();
    __m128i err      = _mm_setzero_si128();
    const __m128i t1h = _mm_loadu_si128((const __m128i *)KL_BYTE_1_HIGH);
    const __m128i t1l = _mm_loadu_si128((const __m128i *)KL_BYTE_1_LOW);
    const __m128i t2h = _mm_loadu_si128((const __m128i *)KL_BYTE_2_HIGH);
    const __m128i low_mask = _mm_set1_epi8(0x0F);
    const __m128i m80      = _mm_set1_epi8((char)0x80);
    const __m128i inc_max  = _mm_setr_epi8(
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        (char)(0xF0 - 1), (char)(0xE0 - 1), (char)(0xC0 - 1)
    );

    size_t off = 0;
    while (off + 16 <= len) {
        __m128i curr = _mm_loadu_si128((const __m128i *)(buf + off));
        if (_mm_movemask_epi8(curr) == 0) {
            err = _mm_or_si128(err, prev_inc);
            prev_blk = curr;
            prev_inc = _mm_setzero_si128();
            off += 16;
            continue;
        }
        __m128i pb1 = _mm_alignr_epi8(curr, prev_blk, 15);
        __m128i pb2 = _mm_alignr_epi8(curr, prev_blk, 14);
        __m128i pb3 = _mm_alignr_epi8(curr, prev_blk, 13);

        __m128i s1h = _mm_shuffle_epi8(t1h, _mm_and_si128(_mm_srli_epi16(pb1, 4), low_mask));
        __m128i s1l = _mm_shuffle_epi8(t1l, _mm_and_si128(pb1, low_mask));
        __m128i s2h = _mm_shuffle_epi8(t2h, _mm_and_si128(_mm_srli_epi16(curr, 4), low_mask));
        __m128i special = _mm_and_si128(_mm_and_si128(s1h, s1l), s2h);

        __m128i is3 = _mm_subs_epu8(pb2, _mm_set1_epi8((char)(0xE0 - 1)));
        __m128i is4 = _mm_subs_epu8(pb3, _mm_set1_epi8((char)(0xF0 - 1)));
        __m128i must23 = _mm_and_si128(_mm_cmpgt_epi8(_mm_or_si128(is3, is4), _mm_setzero_si128()), m80);

        err = _mm_or_si128(err, _mm_xor_si128(special, must23));
        prev_inc = _mm_subs_epu8(curr, inc_max);
        prev_blk = curr;
        off += 16;
    }

    if (off < len) {
        uint8_t tail[16] = {0};
        for (size_t i = 0; off + i < len; ++i) tail[i] = buf[off + i];
        __m128i curr = _mm_loadu_si128((const __m128i *)tail);
        __m128i pb1  = _mm_alignr_epi8(curr, prev_blk, 15);
        __m128i pb2  = _mm_alignr_epi8(curr, prev_blk, 14);
        __m128i pb3  = _mm_alignr_epi8(curr, prev_blk, 13);
        __m128i s1h  = _mm_shuffle_epi8(t1h, _mm_and_si128(_mm_srli_epi16(pb1, 4), low_mask));
        __m128i s1l  = _mm_shuffle_epi8(t1l, _mm_and_si128(pb1, low_mask));
        __m128i s2h  = _mm_shuffle_epi8(t2h, _mm_and_si128(_mm_srli_epi16(curr, 4), low_mask));
        __m128i is3  = _mm_subs_epu8(pb2, _mm_set1_epi8((char)(0xE0 - 1)));
        __m128i is4  = _mm_subs_epu8(pb3, _mm_set1_epi8((char)(0xF0 - 1)));
        __m128i must23 = _mm_and_si128(_mm_cmpgt_epi8(_mm_or_si128(is3, is4), _mm_setzero_si128()), m80);
        err = _mm_or_si128(err, _mm_xor_si128(_mm_and_si128(_mm_and_si128(s1h, s1l), s2h), must23));
        prev_inc = _mm_subs_epu8(curr, inc_max);
    }
    err = _mm_or_si128(err, prev_inc);
    return _mm_movemask_epi8(_mm_cmpeq_epi8(err, _mm_setzero_si128())) == 0xFFFF;
}
#endif

// Portable 8-byte SWAR + scalar UTF-8 validator for non-SIMD freestanding targets:
bool cx_validate_utf8_swar(const uint8_t *buf, size_t len) {
    size_t i = 0;
    while (i + 8 <= len) {
        uint64_t w;
        __builtin_memcpy(&w, buf + i, 8);
        if ((w & 0x8080808080808080ULL) == 0) { i += 8; continue; }
        break;
    }
    while (i < len) {
        if (buf[i] < 0x80) {
            if (i + 8 <= len) {
                uint64_t w;
                __builtin_memcpy(&w, buf + i, 8);
                if ((w & 0x8080808080808080ULL) == 0) { i += 8; continue; }
            }
            ++i;
            continue;
        }
        uint8_t b0 = buf[i];
        if (b0 < 0xC2) return false;
        if (b0 < 0xE0) {
            if (i + 1 >= len || (buf[i + 1] & 0xC0) != 0x80) return false;
            i += 2;
        } else if (b0 < 0xF0) {
            if (i + 2 >= len || (buf[i + 1] & 0xC0) != 0x80 || (buf[i + 2] & 0xC0) != 0x80) return false;
            if ((b0 == 0xE0 && buf[i + 1] < 0xA0) || (b0 == 0xED && buf[i + 1] >= 0xA0)) return false;
            i += 3;
        } else if (b0 <= 0xF4) {
            if (i + 3 >= len || (buf[i + 1] & 0xC0) != 0x80 || (buf[i + 2] & 0xC0) != 0x80 || (buf[i + 3] & 0xC0) != 0x80) return false;
            if ((b0 == 0xF0 && buf[i + 1] < 0x90) || (b0 == 0xF4 && buf[i + 1] >= 0x90)) return false;
            i += 4;
        } else {
            return false;
        }
    }
    return true;
}
```

---

### 2.5 Comptime-Compressed Unicode Tables (10.11 KiB Split / 9.61 KiB Unified): UAX #29 & wcwidth

To keep total Unicode `.rodata` strictly inside the `< 8–12 KB` budget while supporting full `UAX #29` Extended Grapheme Clusters (`GB1`–`GB999`, including `GB9c` `Indic_Conjunct_Break` and `GB11` `Extended_Pictographic`) and Markus Kuhn `wcwidth` terminal column widths, CoreX combines arithmetic range pruning with 3-stage suffix–prefix overlapped tries generated inside `MirVm` at `comptime`:

-   **Arithmetic Fast-Path Pruning (`88.2%` of Unicode):** Above `0x1FFFF` (`Planes 2..16`), only `0x20000..=0x3FFFD` (`wcwidth = 2`, `GCB = Other`), `0xE0001` & `0xE0020..=0xE007F` (`wcwidth = 0`, `GCB = Control`), and `0xE0100..=0xE01EF` (`wcwidth = 0`, `GCB = Extend_InCB_Extend`) differ from `(Other, 1)`. Inside the BMP, ASCII (`< 0x80`), Hangul precomposed syllables (`0xAC00..=0xD7A3`, where `wcwidth = 2` and `GCB` is `LV = 16` iff `(cp - 0xAC00) % 28 == 0` else `LVT = 17`), and CJK Unified Ideographs (`0x3400..=0x4DBF`, `0x4E00..=0x9FFF`) resolve in 3 range checks, restricting table lookups to `0x0000..=0x1FFFF` (`131,072` scalars).
-   **Split Tree-Shakeable Tries (`10,354 B` = `10.11 KiB` Total):** Computing Hangul `LV`/`LVT` arithmetically leaves **16 stored `GraphemeClass` values (`0..15`, 4 bits = 2 scalars/byte)** and **3 stored `WidthClass` values (`0, 1, 2`, 2 bits = 4 scalars/byte)**. Deduping 8-byte leaf windows and greedily overlapping matching suffixes/prefixes into a byte pool yields **`5,181 B`** (`5.06 KiB`) for `WCWIDTH_TRIE`, **`4,939 B`** (`4.82 KiB`) for `GRAPHEME_TRIE`, and **`234 B`** (`13 states × 18 classes`) for `GRAPHEME_DFA` – so CLI diagnostics calling only `display_width()` link just `5.06 KiB` while `--gc-sections` drops `GRAPHEME_TRIE` completely (if unified into a single 6-bit trie, total size is `9,838 B` / `9.61 KiB`).

> **Visual – Comptime Table Compression Fits Float and Unicode Data Inside 11.2 KB of .rodata:** Top: Splitting powers of five by 27 shrinks float scaling data from 9,872 B (full Schubfach/Dragonbox) to a **632 B** table shared by both float formatting and Eisel–Lemire parsing, while 3-stage overlapped tries fit full Unicode 17/18 wcwidth and UAX #29 grapheme segmentation in 10,354 B. Bottom: Per-symbol dead-code elimination links only referenced tables, keeping freestanding wasm32 binaries well below the **10,240 B** target.

```rust
// Reference Implementation (CoreX v1.0): `comptime` Overlapped Trie Generator, O(1) Lookup & 13-State UAX #29 DFA
// File: stdlib/cx/str_unicode.cx
mod str_unicode;

// `comptime` builder invoked inside `MirVm` to freeze `.rodata` slices (`5,181 B` wcwidth + `4,939 B` GCB + `234 B` DFA):
// For each deduplicated 8-byte leaf block sorted lexicographically, `pack_overlapped_pool` finds the longest
// suffix `0..=8` of `pool` matching the prefix of `block`, recording `u16` byte offset `pool.len() - overlap`.

// 13 DFA States: 0=SOT, 1=Base, 2=CR, 3=Control/LF, 4=Prepend, 5=L, 6=LV/V, 7=LVT/T,
//                8=RI_Odd, 9=InCB_Consonant, 10=InCB_Linked, 11=ExtPict_Seq, 12=ExtPict_ZWJ.
// 18 Runtime Classes: 0=Other, 1=CR, 2=LF, 3=Control, 4=Extend_Plain, 5=Extend_InCB_Extend,
//                     6=Extend_InCB_Linker, 7=ZWJ, 8=RI, 9=Prepend, 10=SpacingMark,
//                     11=L, 12=V, 13=T, 14=InCB_Consonant, 15=ExtPict, 16=LV, 17=LVT.
const GRAPHEME_DFA: [u8; 234] = comptime build_uax29_dfa();

comptime fn build_uax29_dfa() -> [u8; 234] {
    var dfa = [0_u8; 234];
    let base_for = |cls: usize| -> u8 {
        match cls {
            1 => 2, 2 | 3 => 3, 9 => 4, 11 => 5, 12 | 16 => 6, 13 | 17 => 7,
            8 => 8, 14 => 9, 6 => 10, 15 => 11, _ => 1,
        }
    };
    var st: usize = 0;
    while st < 13 {
        var cls: usize = 0;
        while cls < 18 {
            let entry: u8 = if st == 0 {
                base_for(cls) // GB1: sot × Any
            } else if st == 2 {
                if cls == 2 { 3 } else { 0x80_u8 | base_for(cls) } // GB3: CR × LF; GB4: CR ÷
            } else if st == 3 or cls is (1..=3) {
                0x80_u8 | base_for(cls) // GB4 & GB5: Control/LF ÷ and ÷ Control/CR/LF
            } else if (st == 5 and cls is (11 | 12 | 16 | 17)) or (st == 6 and cls is (12 | 13)) {
                base_for(cls) // GB6 & GB7: Hangul L / LV / V
            } else if st == 7 and cls == 13 {
                7 // GB8: (LVT | T) × T
            } else if cls is (4..=7) {
                // GB9: × (Extend | ZWJ), advancing GB9c InCB & GB11 ExtPict state machines:
                match st {
                    9  => if cls == 6 { 10 } else if cls is (5 | 7) { 9 } else { 1 },
                    10 => if cls is (5..=7) { 10 } else { 1 },
                    11 => if cls == 7 { 12 } else { 11 },
                    _  => 1,
                }
            } else if cls == 10 {
                1 // GB9a: × SpacingMark
            } else if st == 4 {
                base_for(cls) // GB9b: Prepend ×
            } else if st == 10 and cls == 14 {
                9 // GB9c: InCB_Linked × InCB_Consonant
            } else if st == 12 and cls == 15 {
                11 // GB11: ExtPict Extend* ZWJ × ExtPict
            } else if st == 8 and cls == 8 {
                1 // GB12/GB13: RI_Odd × RI -> paired!
            } else {
                0x80_u8 | base_for(cls) // GB999: Any ÷ Any
            };
            dfa[st * 18 + cls] = entry;
            cls += 1;
        }
        st += 1;
    }
    dfa
}

@inline @no_alloc @no_panic
pub fn char_width(ch: char, /) -> i8 {
    let cp = ch as u32;
    if cp < 0xA0_u32 {
        if cp == 0 { return 0; }
        return if cp < 0x20_u32 or cp >= 0x7F_u32 { -1 } else { 1 };
    }
    if (cp >= 0x3400_u32 and cp <= 0x4DBF_u32)
        or (cp >= 0x4E00_u32 and cp <= 0x9FFF_u32)
        or (cp >= 0xAC00_u32 and cp <= 0xD7A3_u32)
    {
        return 2;
    }
    if cp >= 0x20000_u32 {
        if cp <= 0x3FFFD_u32 { return 2; }
        if cp == 0xE0001_u32 or (cp >= 0xE0020_u32 and cp <= 0xE01EF_u32) { return 0; }
        return 1;
    }
    let byte_idx = (cp >> 2) as usize;
    let s2_blk = WCWIDTH_S1[byte_idx >> 6] as usize;
    let pool_off = WCWIDTH_S2[(s2_blk << 3) | ((byte_idx >> 3) & 0x7)] as usize;
    let packed = WCWIDTH_POOL[pool_off + (byte_idx & 0x7)];
    ((packed >> ((cp & 3_u32) * 2)) & 0x3_u8) as i8
}

@inline @no_alloc @no_panic
pub(pkg) fn grapheme_class(ch: char, /) -> u8 {
    let cp = ch as u32;
    if cp < 0x80_u32 {
        if cp == 0x0D_u32 { return 1; }
        if cp == 0x0A_u32 { return 2; }
        return if cp < 0x20_u32 or cp == 0x7F_u32 { 3 } else { 0 };
    }
    if cp >= 0xAC00_u32 and cp <= 0xD7A3_u32 {
        return if (cp - 0xAC00_u32) % 28_u32 == 0 { 16 } else { 17 };
    }
    if cp >= 0x20000_u32 {
        if cp == 0xE0001_u32 or (cp >= 0xE0020_u32 and cp <= 0xE007F_u32) { return 3; }
        return if cp >= 0xE0100_u32 and cp <= 0xE01EF_u32 { 5 } else { 0 };
    }
    let byte_idx = (cp >> 1) as usize;
    let s2_blk = GCB_S1[byte_idx >> 6] as usize;
    let pool_off = GCB_S2[(s2_blk << 3) | ((byte_idx >> 3) & 0x7)] as usize;
    let packed = GCB_POOL[pool_off + (byte_idx & 0x7)];
    (packed >> ((cp & 1_u32) * 4)) & 0x0F_u8
}
```

---

### 2.6 Zero-libc Float & Integer Conversion: Shared 632B Pow5 Table, Schubfach, Eisel–Lemire & jeaiii

Full uncompressed `f64` power-of-10 tables consume `9,872 B` in `Schubfach` / `xjb` (`9,904 B` in `Dragonbox`), whereas Dragonbox's compact cache uses `584 B` and Russ Cox's 2026 `fp` converter splits `pow10[p] = pow10[p_0] * pow10[p_1]` into 27 fine + 26 coarse entries (`1,376 B` with stored exponents). Adapting this base-27 split to store normalized `5^r` (`27 × 8 B = 216 B`) and `5^(27c)` (`26 × 16 B = 416 B` for `c in -13..=12`, covering `q in -351..=350`) lets CoreX share **one `632 B` `POW5_SPLIT` `.rodata` table** across both `Schubfach` float-to-string (`-k in -292..=324`) and `Eisel–Lemire` string-to-float (`q in -342..=308`):

-   **Float-to-String (`Schubfach` + `jeaiii`):** Reconstructing the 128-bit significand of `10^(-k)` introduces `<= 1.0 ULP` error at bit 127 (`< 2^-126`), well inside Nadezhin's separation bound for IEEE-754 `binary64`. Logarithms use 32-bit fixed-point multiplies (`(e * 315653) >> 20`), candidate selection uses `zmij`-style branchless closedness tie-breaking, and decimal digits emit 2-at-a-time via James Anhalt's (`jeaiii`) division-free `200 B` `DEC_DIGITS_LUT` routine.
-   **String-to-Float (`Eisel–Lemire` + Stack Decimal Fallback):** While Mushtak & Lemire (2023) proved that a 19-digit `Eisel–Lemire` pass needs no fallback when backed by an exact uncompressed 128-bit table, sharing the `632 B` split table (`<= 1 ULP` in `pow_lo`) plus supporting arbitrary `> 19`-digit literals (`"0.000000000000000000000123..."`) triggers an exact stack-resident multiprecision decimal shift-and-round fallback (`[u32; 128]` limb ring = `512 B` stack, zero heap allocation) on `< 0.05%` of random/edge inputs (`29 / 63,385` in verification testing).
-   **Zero-`libc` `cx.math` Minimax Transcendentals:** For `sin`/`cos` on `f64`, splitting $\pi/2$ into exact 33+33+53-bit `PIO2_HI`, `PIO2_MI`, and `PIO2_LO` constants paired with a degree-13 minimax polynomial (`S1..S6`, `C1..C6`) achieves `< 1.0 ULP` on `[-\pi/4, \pi/4]` and **`<= 2.0 ULP`** across `|x| < 2^20` (including inputs adjacent to multiples of $\pi$), delegating `|x| >= 2^20` to Payne–Hanek reduction.

```rust
// Reference Implementation (CoreX v1.0): Shared 632B `POW5_SPLIT`, `Schubfach`, `Eisel–Lemire` + Stack Fallback & `jeaiii`
// File: stdlib/cx/num_conv.cx
mod num_conv;

use cx.math.{carrying_add_u64, widening_mul_u64};

const C_MIN: i32 = -13;
const POW5_FINE: [u64; 27]          = comptime build_pow5_fine();   // 216 B .rodata
const POW5_COARSE: [(u64, u64); 26] = comptime build_pow5_coarse(); // 416 B .rodata (Total = 632 B!)
const DEC_DIGITS_LUT: [u8; 200]     = b"00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899".*;

@inline @no_alloc @no_panic fn floor_log10_pow2(e: i32, /) -> i32 = (e * 315_653) >> 20;
@inline @no_alloc @no_panic fn floor_log10_pow2_minus_log10_4_over_3(e: i32, /) -> i32 = (e * 631_305 - 261_663) >> 21;
@inline @no_alloc @no_panic fn floor_log2_pow10(q: i32, /) -> i32 = (q * 1_741_647) >> 19;

@inline @no_alloc @no_panic
pub(pkg) fn pow10_sig128(q: i32, /) -> (u64, u64) {
    let c = (((q + 351) * 9710) >> 18) - 13;
    let r = (q - 27 * c) as usize;
    let (chi, clo) = POW5_COARSE[(c - C_MIN) as usize];
    let fine = POW5_FINE[r];

    let (_, mid_carry) = widening_mul_u64(clo, fine);
    let (p_lo, p_hi)   = widening_mul_u64(chi, fine);
    let (sum_lo, c_out) = carrying_add_u64(p_lo, mid_carry, false);
    let sum_hi = p_hi +% (c_out as u64);

    if (sum_hi >> 63) == 0 {
        ((sum_hi << 1) | (sum_lo >> 63), sum_lo << 1)
    } else {
        (sum_hi, sum_lo)
    }
}

@inline @no_alloc @no_panic
fn umul192_upper64_modified(pow_hi: u64, pow_lo: u64, y: u64, beta: u32, /) -> u64 {
    let y_sh = y << beta;
    let (glo, c0) = carrying_add_u64(pow_lo, 2, false);
    let ghi = pow_hi +% (c0 as u64);
    let (_, lo_hi) = widening_mul_u64(glo, y_sh);
    let (mid_lo, upper64) = widening_mul_u64(ghi, y_sh);
    let (mid64, c1) = carrying_add_u64(mid_lo, lo_hi, false);
    (upper64 +% (c1 as u64)) | ((mid64 > 1) as u64)
}

@no_alloc @no_panic
pub fn schubfach_to_decimal_f64(val: f64, /) -> (u64, i32) {
    let bits = val.to_bits();
    let bin_exp = ((bits >> 52) & 0x7FF_u64) as i32;
    var bin_sig = bits & ((1_u64 << 52) - 1);
    var regular = bin_sig != 0;
    let q: i32 = if bin_exp != 0 {
        bin_sig |= (1_u64 << 52);
        bin_exp - 1075
    } else {
        regular = true;
        1 - 1075
    };

    let c4 = bin_sig << 2;
    let u = c4 - (if regular { 2_u64 } else { 1_u64 });
    let v = c4;
    let w = c4 + 2_u64;

    let k = if regular { floor_log10_pow2(q) } else { floor_log10_pow2_minus_log10_4_over_3(q) };
    let beta = (q + floor_log2_pow10(-k) + 1) as u32;
    let (pow_hi, pow_lo) = pow10_sig128(-k);

    let u_b = umul192_upper64_modified(pow_hi, pow_lo, u, beta);
    let v_b = umul192_upper64_modified(pow_hi, pow_lo, v, beta);
    let w_b = umul192_upper64_modified(pow_hi, pow_lo, w, beta);
    let lsb = bin_sig & 1_u64;

    let s = w_b / 40_u64;
    if s >= 1 and (u_b + lsb <= s * 40_u64) and (s * 40_u64 + lsb <= w_b) {
        var d = s;
        var e10 = k + 1;
        while d % 10 == 0 { d /= 10; e10 += 1; }
        return (d, e10);
    }

    let t_under = v_b >> 2;
    let t_over  = t_under + 1;
    let under_in = (u_b + lsb) <= (t_under << 2);
    let over_in  = ((t_over << 2) + lsb) <= w_b;
    let rem = v_b & 3_u64;
    let under_closer = rem < 2 or (rem == 2 and (t_under & 1) == 0);

    var d = if under_in and (not over_in or under_closer) { t_under } else { t_over };
    var e10 = k;
    while d % 10 == 0 { d /= 10; e10 += 1; }
    (d, e10)
}

const EXACT_POW10_F64: [f64; 23] = [
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22,
];

@no_alloc @no_panic
pub(pkg) fn eisel_lemire_f64(man: u64, exp10: i32, /) -> f64? {
    if man == 0 or exp10 < -342 { return .Some(0.0_f64); }
    if exp10 > 308 { return .Some(f64.INFINITY); }
    if man < (1_u64 << 53) and exp10 >= -22 and exp10 <= 22 {
        let f = man as f64;
        return .Some(if exp10 >= 0 { f * EXACT_POW10_F64[exp10 as usize] } else { f / EXACT_POW10_F64[(-exp10) as usize] });
    }

    let clz = man.leading_zeros();
    let norm_man = man << clz;
    let e2_pow10 = floor_log2_pow10(exp10);
    let (pow_hi, pow_lo) = pow10_sig128(exp10);

    var (w_lo, w_hi) = widening_mul_u64(norm_man, pow_hi);
    if (w_hi & 0x1FF_u64) == 0x1FF_u64 or (w_hi & 0x1FF_u64) == 0 or w_lo >= (u64.MAX - norm_man) {
        let (_, second_hi) = widening_mul_u64(norm_man, pow_lo);
        let (n_lo, c_out) = carrying_add_u64(w_lo, second_hi, false);
        w_lo = n_lo;
        w_hi +%= c_out as u64;
    }

    let msb = (w_hi >> 63) as i32;
    var biased_exp = (63 - (clz as i32)) + e2_pow10 + msb + 1023;
    if biased_exp <= 0 {
        if biased_exp < -52 { return .Some(0.0_f64); }
        return eisel_lemire_subnormal(w_hi, w_lo, msb, biased_exp);
    }
    if biased_exp >= 0x7FF { return .Some(f64.INFINITY); }

    let sh = (9 + msb) as u32;
    let x54 = w_hi >> sh;
    let rem_mask = (1_u64 << sh) - 1;
    let rem_hi = w_hi & rem_mask;

    if (x54 & 1) == 1 {
        if (rem_hi == 0 and w_lo <= 8) or (rem_hi == rem_mask and w_lo >= u64.MAX - 7) {
            return .None; // Delegate exact halfway tie to `parse_f64_decimal_fallback` (`[u32; 128]` stack buffer)
        }
    }
    let sticky = rem_hi != 0 or w_lo > 8;
    let round_up = ((x54 & 1) == 1 and (sticky or (x54 & 2) != 0)) as u64;
    var x53 = (x54 >> 1) + round_up;
    if x53 >= (1_u64 << 53) {
        x53 >>= 1;
        biased_exp += 1;
        if biased_exp >= 0x7FF { return .Some(f64.INFINITY); }
    }
    .Some(f64.from_bits(((biased_exp as u64) << 52) | (x53 & ((1_u64 << 52) - 1))))
}

@inline @no_alloc @no_panic
fn write_2digits(out: *mut u8, idx: usize, /) {
    unsafe { @memcpy(out as *mut opaque, (&raw DEC_DIGITS_LUT[2 * idx]) as *opaque, 2); }
}

@no_alloc @no_panic
pub(pkg) fn format_u32_jeaiii(dst: *mut u8, u: u32, /) -> usize {
    let uu = u as u64;
    if u < 100 {
        if u < 10 { unsafe { dst.* = b'0' + (u as u8); } return 1; }
        write_2digits(dst, u as usize);
        return 2;
    }
    if u < 1_000_000 {
        if u < 10_000 {
            let y = uu * 42_949_673_u64;
            let n: usize = if u < 1_000 { unsafe { dst.* = b'0' + ((y >> 32) as u8); } 1 } else { write_2digits(dst, (y >> 32) as usize); 2 };
            write_2digits(unsafe { dst + n }, (((y & 0xFFFF_FFFF_u64) * 100) >> 32) as usize);
            return n + 2;
        }
        var y = uu * 429_497_u64;
        let n: usize = if u < 100_000 { unsafe { dst.* = b'0' + ((y >> 32) as u8); } 1 } else { write_2digits(dst, (y >> 32) as usize); 2 };
        y = (y & 0xFFFF_FFFF_u64) * 100; write_2digits(unsafe { dst + n }, (y >> 32) as usize);
        y = (y & 0xFFFF_FFFF_u64) * 100; write_2digits(unsafe { dst + n + 2 }, (y >> 32) as usize);
        return n + 4;
    }
    if u < 100_000_000 {
        const MASK47: u64 = (1_u64 << 47) - 1;
        var y = uu * 140_737_489_u64;
        let n: usize = if u < 10_000_000 { unsafe { dst.* = b'0' + ((y >> 47) as u8); } 1 } else { write_2digits(dst, (y >> 47) as usize); 2 };
        y = (y & MASK47) * 100; write_2digits(unsafe { dst + n }, (y >> 47) as usize);
        y = (y & MASK47) * 100; write_2digits(unsafe { dst + n + 2 }, (y >> 47) as usize);
        y = (y & MASK47) * 100; write_2digits(unsafe { dst + n + 4 }, (y >> 47) as usize);
        return n + 6;
    }
    var y = if u < 1_000_000_000 { (uu * 1_441_151_882_u64) >> 25 } else { (uu * 1_441_151_881_u64) >> 25 };
    let n: usize = if u < 1_000_000_000 { unsafe { dst.* = b'0' + ((y >> 32) as u8); } 1 } else { write_2digits(dst, (y >> 32) as usize); 2 };
    y = (y & 0xFFFF_FFFF_u64) * 100; write_2digits(unsafe { dst + n }, (y >> 32) as usize);
    y = (y & 0xFFFF_FFFF_u64) * 100; write_2digits(unsafe { dst + n + 2 }, (y >> 32) as usize);
    y = (y & 0xFFFF_FFFF_u64) * 100; write_2digits(unsafe { dst + n + 4 }, (y >> 32) as usize);
    y = (y & 0xFFFF_FFFF_u64) * 100; write_2digits(unsafe { dst + n + 6 }, (y >> 32) as usize);
    n + 8
}

@no_alloc @no_panic
fn fmt_u32_fixed8(dst: *mut u8, u: u32, /) {
    const MASK47: u64 = (1_u64 << 47) - 1;
    var y = (u as u64) * 140_737_489_u64;
    write_2digits(dst, (y >> 47) as usize);
    y = (y & MASK47) * 100; write_2digits(unsafe { dst + 2 }, (y >> 47) as usize);
    y = (y & MASK47) * 100; write_2digits(unsafe { dst + 4 }, (y >> 47) as usize);
    y = (y & MASK47) * 100; write_2digits(unsafe { dst + 6 }, (y >> 47) as usize);
}

@no_alloc @no_panic
pub(pkg) fn format_u64_jeaiii(dst: *mut u8, n: u64, /) -> usize {
    if n <= 0xFFFF_FFFF_u64 { return format_u32_jeaiii(dst, n as u32); }
    let hi = n / 100_000_000_u64;
    let lo = (n % 100_000_000_u64) as u32;
    if hi <= 0xFFFF_FFFF_u64 {
        let off = format_u32_jeaiii(dst, hi as u32);
        fmt_u32_fixed8(unsafe { dst + off }, lo);
        return off + 8;
    }
    let hi2 = (hi / 100_000_000_u64) as u32;
    let mid = (hi % 100_000_000_u64) as u32;
    let off = format_u32_jeaiii(dst, hi2);
    fmt_u32_fixed8(unsafe { dst + off }, mid);
    fmt_u32_fixed8(unsafe { dst + off + 8 }, lo);
    off + 16
}
```

---

## 3. Deliverable 3: Tree-Shaking, Binary-Size & Pentagon Bounds-Elimination Verification Checklist

### 3.1 Freestanding wasm32 Tree-Shaking & Modeled Binary-Size Budget (< 10 KB)

Because Phase 4's Signature Firewall never lowers unreferenced items to `HIR`/`MIR`, Phase 5 deduplicates monomorphizations via `LayoutShapeKey`, Phase 7/8 places every function and `.rodata` constant into its own section (`-ffunction-sections -fdata-sections` + `.llvm_addrsig`), and `wasm-ld` links with `--no-entry --gc-sections --icf=safe --strip-all -O3`, importing `cx.*` links solely the reachable symbol graph. Combining the exact `.rodata` table sizes above (`48 B`, `200 B`, `234 B`, `632 B`, `4,939 B`, `5,181 B`) with projected Wasm codegen budgets anchored to `DR-15`'s `1.5–10 KB` baseline yields three concrete verification profiles:

| Freestanding `wasm32` Verification Profile | Linked `.text` + `.rodata` Subsystems | Unreferenced `.rodata` Stripped by `--gc-sections` | Modeled `.wasm` Size | Gate Ceiling |
| :--- | :--- | :--- | :---: | :---: |
| **Profile A: Minimal Kernel** (`Arena` + `Span16` + `ByteCursor` + `cx.math.sin`) | Wasm section headers (`~140 B`), `Arena` (`~420 B`), `wasm_heap` (`~380 B`), minimax `sin_f64` (`~680 B`) | `POW5_SPLIT`, `DEC_DIGITS_LUT`, `KL_UTF8`, `WCWIDTH_TRIE`, `GRAPHEME_TRIE` (`0 B` linked) | **`~1,640 B` (`1.60 KiB`)** | `< 10,240 B` |
| **Profile B: Parser & Formatter** (Profile A + `Vec` + `SSO String` + `FmtArgs` + `jeaiii` + `validate_utf8_swar`) | Profile A + `Vec` (`~480 B`), `SSO String` (`~620 B`), `FmtArgs` (`~590 B`), `jeaiii` (`~450 B` + `200 B`), SWAR UTF-8 (`~400 B`) | `POW5_SPLIT` (`632 B`), `WCWIDTH_TRIE` (`5,181 B`), `GRAPHEME_TRIE` (`4,939 B`) (`0 B` linked) | **`~4,380 B` (`4.28 KiB`)** | `< 10,240 B` |
| **Profile C: Rich Containers & Float/Width** (Profile B + `Map` SWAR + `Schubfach` + `wcwidth`) | Profile B (`~4,380 B`) + ICF `RawTableInner` SWAR (`~940 B`) + `Schubfach` (`~820 B` + `632 B`) – *plus either `ipnsort` (`~1,150 B`) or `WCWIDTH_TRIE` (`5,181 B`)* | `GRAPHEME_TRIE` (`4,939 B` + `234 B` DFA) omitted unless `.graphemes()` is called | **`~7,920–8,920 B` (`7.7–8.7 KiB`)** | `< 10,240 B` |

---

### 3.2 Pentagon (Intv x Sub) Bounds-Elimination & SAST Verification Matrix

Every inner loop in `STD-01` is written so `Phase 6` `O(V)` interval filtering + Sparse ABCD demand-sliced Pentagon (`Intv × Sub`, capped at `MAX_SUB_VARS = 256` per `DR-20` `Fix-06A`) discharges 100% of slice bounds and unsigned-subtraction checks statically:

| Subsystem & Hot Inner Loop | Dominating Guard / Bitwise Invariant | Pentagon (`Intv × Sub`) Rule Discharging Check | Verified `MIR` / LLVM Output |
| :--- | :--- | :--- | :--- |
| **`Deque[T]` & `RawTableInner` Ring Wrap** | `buckets = (bucket_mask as usize) + 1`; index `pos = raw & mask` | Bitwise `AND` transfer: `sup(Intv(x & mask)) <= sup(Intv(mask)) < len` | **0 bounds checks** on ring and control-group wrap |
| **`cx.str.trim` / `SE-04` `$` End-Relative Slicing** | `if buf.len() < K { return .Err(...); }` before `buf[..$-K]` / `buf[$-K..]` | `DR-21` backward-offset rule: `inf(b*(%len)) >= K` implies `%len in s*(%idx)` and `inf(%idx) >= 0` | **0 underflow traps & 0 slice bounds traps** |
| **Unicode 3-Stage Tries & `jeaiii` `DEC_DIGITS_LUT`** | Bitwise shift + mask (`(byte_idx >> 3) & 0x7`, `y >> 47` where `y < 100 * 2^47`) | Constant interval `Intv(idx) subseteq [0, N - 1]` against fixed `[T; N]` `.rodata` arrays | **0 bounds checks** across all 3 trie stages & `DEC_DIGITS_LUT` |
| **`for item, i in slice` & `#soa Vec[T]` Loops** | Hardware counter `%i` over `0..%__len` (`DR-21` `SE-05`) | Loop header seeds `Intv(%i) >= 0` and `%__len in Sub(%i)` | **0 bounds checks**; LLVM `!range` + `#soa` `noalias` SIMD |
| **`partition_point` & `choose_pivot_ninther`** | `mid = base + size / 2` under loop guard `size > 0` and `base + size <= slice.len()` | Relational `Sub` propagation: `mid < base + size <= len` | **0 bounds checks** inside binary search & ninther `sort3` |
| **`Vec[T]`, `Map[K, V]`, `String` Arena Cleanup** | Constructed via `.in_arena(&mut arena)` (`AllocTag == 1`) with `T: TrivialDrop` | `MIR` Pass 1 (`ElaborateDrops`) + Pass 3 (`Depth(rho_arena)` `E0306` escape check) | **0 destructor instructions** emitted at scope exit |

---

### 3.3 Phase 11.1 Mandatory Verification Gate Checklist

1.  **Zero Pre-`main` Static Initializers Gate:** Inspect compiled ELF, Mach-O, PE32+, and `.wasm` binaries via `llvm-readobj --sections` and `wasm-objdump -h` to confirm **zero** `.init_array`, `__mod_init_func`, `.CRT$XCU`, or Wasm `start` sections are emitted across `cx.mem`, `cx.col`, `cx.str`, and `cx.math`.
2.  **Pointer-Shape ICF Deduplication Gate:** Instantiate `Map[K, V]` across 50 distinct nominal `(u64, *T)` key-value types in a test binary linked with `lld --icf=safe` / `wasm-ld --icf=safe`, and verify via `llvm-nm --size-sort` that `RawTableInner.find_raw`, `find_or_prepare_insert_raw`, `erase_slot_ctrl`, and `rehash_or_grow_raw` each appear **once** in `.text`.
3.  **Scratch-Arena Exclusivity (`E0328`) & `--sim` Determinism (`Fix-18A`) Gate:** Verify `compile_fail` tests trigger `E0328` on unguarded same-slot scratch rewinds, and run `corex test --sim --seed=0x5EED_CAFE stdlib/cx/` across randomized ASLR runs asserting bit-identical `Map`/`Set` iteration orders and `OOM` fault-injection cleanup.
4.  **Pentagon Zero-Trap Inner-Loop Gate:** Inspect post-SAST `MIR` (`corex check --sast-strict --emit-mir-post-sast`) across `Arena.alloc_raw`, `RawTableInner.find_raw`, `partition_lomuto_branchless_cyclic`, `partition_point`, `validate_utf8`, `char_width`, `grapheme_class`, `schubfach_to_decimal_f64`, `eisel_lemire_f64`, and `format_u32_jeaiii`, confirming **zero** residual bounds or checked-subtraction traps and `< 2 MB` Pentagon analyzer memory.
5.  **Four-Tier Differential & `< 10 KB` Freestanding Wasm Gate:** Assert 100% behavioral parity under `corex test --diff-backends` (`Pre-Opt MirVm`, `Post-Opt MirVm`, `-ofmt=c`, and `LLVM`) over the full Unicode `GraphemeBreakTest.txt` conformance corpus (`GB1`–`GB999` including `GB9c` and `GB11`) and 1,000,000 random/subnormal/boundary IEEE-754 float round-trips, while asserting freestanding `wasm32` Profiles A–C stay strictly `< 10,240 bytes`.

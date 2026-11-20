//! Virtual File System, `.cxtree` Binary Headers & Line/Column SourceMap
//!
//! Implements the content-addressable `VfsSourceMap` (`SourceMap`), dual-bounded two-queue LRU
//! `OverlayCache`, `.cxtree` binary manifest records, and $O(\log L)$ `LineIndex` bidirectional
//! byte/column resolver supporting `LF`/`CRLF` line endings and LSP `"utf-16"`/`"utf-8"` encodings.
//!
//! Files `< 16 KiB` (or exact 4096-byte page multiples) are loaded into `BumpArena` with an explicit
//! trailing NUL byte (`0x00`), larger non-page-multiple files use read-only OS memory mapping, and
//! editor/virtual overlays use heap-allocated `:0` buffers bounded by `256` entries and `64 MiB`.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");

const FileId = mem_foundation.FileId;
const StringId = mem_foundation.StringId;
const SymbolId = mem_foundation.SymbolId;
const Span = mem_foundation.Span;
const BumpArena = mem_foundation.BumpArena;
const StringInterner = mem_foundation.StringInterner;

// ---------------------------------------- TYPES ----------------------------------------

// ------------------ Package & CxTree Headers ------------------

/// Canonical 16-bit handle identifying a resolved package in `corex.lock`.
pub const PackageId = enum(u16) {
    /// Root workspace package being compiled (`0`).
    root = 0,
    /// CoreX standard library package (`1`).
    std_core = 1,
    /// Sentinel value representing no associated package.
    none = std.math.maxInt(u16),
    _,

    /// Alias for the root workspace package (`DR-11` §2.4).
    pub const root_workspace: PackageId = .root;
    /// Alias for the standard library package (`DR-11` §2.4).
    pub const std_lib: PackageId = .std_core;

    /// Converts a raw 16-bit integer index into a `PackageId`.
    pub inline fn fromInt(index: u16) PackageId {
        return @fromBackingInt(@intCast(index));
    }

    /// Returns the underlying 16-bit integer value of `self`.
    pub inline fn asInt(self: PackageId) u16 {
        return @backingInt(self);
    }

    /// Returns true if `self` is the `.none` sentinel.
    pub inline fn isNone(self: PackageId) bool {
        return self == .none;
    }
};

/// 32-byte binary header of a content-addressable `.cxtree` package manifest (`DR-11` §2.4, `align(8)`).
pub const CxTreeHeader = extern struct {
    /// Four-byte file magic signature (`"CXTR"`), aligned to 8 bytes for zero-copy `.cxtree` slicing.
    magic: [4]u8 align(8) = CXTREE_MAGIC,
    /// Format version number (`1`).
    version: u32 = CXTREE_VERSION,
    /// Number of `CxTreeEntry` records immediately following this header.
    entry_count: u32 = 0,
    /// Total byte length of the trailing UTF-8 relative-path string table.
    string_table_bytes: u32 = 0,
    /// Byte offset of the package name inside the string table.
    pkg_name_str_off: u32 = 0,
    /// Zero-initialized reserved padding to align `CxTreeHeader` to 32 bytes.
    reserved: [12]u8 = @splat(0),
};

/// 48-byte binary record describing a single file inside a `.cxtree` manifest (`DR-11` §2.4).
pub const CxTreeEntry = extern struct {
    /// Byte offset of the normalized POSIX relative path in the `.cxtree` string table.
    rel_path_off: u32,
    /// Byte length of the normalized POSIX relative path.
    rel_path_len: u16,
    /// File mode (`0x01` = regular file, `0x02` = executable file).
    file_mode: u16,
    /// Uncompressed file size in bytes.
    file_size: u64,
    /// 256-bit BLAKE3 content digest of the file.
    file_blake3: [32]u8,
};

/// Validation and integrity errors returned when mounting or faulting `.cxtree` manifests (`E0015`).
pub const CxTreeError = error{
    /// Buffer is shorter than `32` bytes (`@sizeOf(CxTreeHeader)`).
    TruncatedCxTree,
    /// Header magic bytes do not match `"CXTR"`.
    InvalidCxTreeMagic,
    /// Header `version` does not equal `1`.
    UnsupportedCxTreeVersion,
    /// Total buffer byte length does not equal `32 + entry_count * 48 + string_table_bytes`.
    CxTreeSizeMismatch,
    /// Relative path is empty, invalid UTF-8, or contains `..`, `.`, `\`, leading `/`, `:`, or control bytes.
    InvalidCxTreePath,
    /// Entries are not sorted in strict ascending bytewise UTF-8 relative-path order.
    UnsortedCxTreePaths,
    /// Two entries collide under exact or ASCII case-insensitive relative-path comparison.
    DuplicateOrCaseCollidingCxTreePath,
    /// Entry `file_mode` is outside `{ 0x01, 0x02 }` or `file_size` exceeds `MAX_SOURCE_FILE_BYTES`.
    InvalidCxTreeFileMode,
    /// Cached blob is missing, truncated, or fails `BLAKE3` verification against `CxTreeEntry.file_blake3`.
    CacheIntegrityMismatch,
};

/// Validated zero-copy view over an immutable `.cxtree` binary manifest buffer.
pub const CxTreeView = struct {
    /// Decoded 32-byte `.cxtree` header.
    header: CxTreeHeader,
    /// Sorted array of 48-byte `CxTreeEntry` records (`len == header.entry_count`).
    entries: []align(1) const CxTreeEntry,
    /// Trailing UTF-8 string table storing normalized POSIX relative paths.
    string_table: []const u8,

    /// Returns the normalized POSIX relative path slice for `entry`.
    pub inline fn asEntryPath(self: CxTreeView, entry: CxTreeEntry) []const u8 {
        const start: usize = entry.rel_path_off;
        return self.string_table[start .. start + entry.rel_path_len];
    }

    /// Extracts the NUL-terminated or prefix-bounded package name from `string_table`.
    pub fn extractPackageName(self: CxTreeView) []const u8 {
        const start: usize = @min(@as(usize, self.header.pkg_name_str_off), self.string_table.len);
        const limit: usize = if (self.entries.len > 0)
            @min(@as(usize, self.entries[0].rel_path_off), self.string_table.len)
        else
            self.string_table.len;
        if (start >= limit) return "";
        const candidate = self.string_table[start..limit];
        if (std.mem.indexOfScalar(u8, candidate, 0)) |nul_pos| {
            return candidate[0..nul_pos];
        }
        return candidate;
    }
};

// ------------------- Line & Column Indexing -------------------

/// Negotiated LSP 3.17 character offset encoding (`"utf-16"` default vs. `"utf-8"`).
pub const PositionEncoding = enum(u8) {
    /// UTF-16 code units (`2` units for astral scalars `>= U+10000`, `1` unit for BMP).
    utf16 = 0,
    /// UTF-8 code units (raw byte offsets clamped to scalar boundaries).
    utf8 = 1,
};

/// Half-open byte bounds `[start .. end)` of a single line (excluding `\r\n` or `\n`).
pub const LineBounds = struct {
    /// Inclusive starting byte offset of the line.
    start: u32,
    /// Exclusive ending byte offset of the line (with any trailing `\r` stripped).
    end: u32,
};

/// Resolved line and column coordinates for terminal diagnostics and LSP `Position` encoding.
pub const LineCol = struct {
    /// 1-based line number for CLI diagnostics.
    line: u32,
    /// 1-based UTF-8 codepoint column for CLI diagnostics.
    col_utf8: u32,
    /// 0-based UTF-16 code unit offset for LSP 3.17 compatibility.
    col_utf16_0: u32,
    /// 1-based byte column within the line.
    col_byte: u32,
    /// Inclusive starting byte offset of the enclosing line.
    line_start_byte: u32,
    /// Exclusive ending byte offset of the enclosing line (excluding `\r\n` or `\n`).
    line_end_byte: u32,
};

// ---------------- Virtual File System Entries -----------------

/// Backing storage strategy used for a `VfsFileEntry` source buffer.
pub const BackingKind = enum(u8) {
    /// Stored in `VfsSourceMap.small_file_arena` (`< 16 KiB` or page-aligned fallback).
    arena_small = 0,
    /// Mapped read-only from the OS page cache (`>= 16 KiB` with verified NUL tail).
    mmap_large = 1,
    /// In-memory virtual buffer or unsaved LSP editor overlay managed by `OverlayCache`.
    in_memory_overlay = 2,
    /// Mounted from an immutable `.cxtree` content-addressable archive.
    cxtree_archive = 3,
};

/// Metadata and buffer ownership record for a single loaded source file in `VfsSourceMap`.
pub const VfsFileEntry = struct {
    /// Unique 32-bit file handle in `VfsSourceMap`.
    file_id: FileId,
    /// Package owning this source file.
    package_id: PackageId,
    /// Interned normalized virtual path using forward slashes (`/`).
    virtual_path: StringId,
    /// Interned resolved OS path (or equal to `virtual_path` for virtual overlays).
    resolved_os_path: StringId,
    /// NUL-terminated UTF-8 source buffer (`content[content.len] == 0`).
    content: [:0]const u8,
    /// 256-bit BLAKE3 cryptographic hash of `content`.
    content_hash: [32]u8,
    /// Monotonic edit revision counter (`1` on first load, incremented on overlay updates).
    revision: u32,
    /// Storage mechanism backing `content`.
    backing_kind: BackingKind,
    /// Active OS memory mapping when `backing_kind == .mmap_large`.
    memory_map: ?std.Io.File.MemoryMap = null,
    /// Open OS file handle associated with `memory_map`.
    mapped_file: ?std.Io.File = null,
    /// Lazily constructed `LineIndex` for byte-to-line/column resolution.
    line_index: ?LineIndex = null,
    /// `true` when this file has an actively open editor buffer (`textDocument/didOpen`).
    is_open_in_editor: bool = false,
    /// `true` when this file is backed by a verified regular file on the host filesystem.
    has_disk_backing: bool = false,
    /// `true` once `content` holds verified file bytes (`false` for newly mounted lazy `.cxtree` entries).
    is_blob_loaded: bool = true,
    /// `true` if lazy blob faulting failed `BLAKE3` content verification (`E0015`).
    has_blob_integrity_error: bool = false,
    /// Uncompressed byte length expected when faulting an unloaded `.cxtree` blob.
    unloaded_blob_size: u32 = 0,
    /// Interned host `blobs/` directory path used strictly for internal lazy faulting (never exposed).
    blobs_dir_id: StringId = .empty,
    /// Original immutable `.cxtree` `file_blake3` digest preserved across temporary editor overlays.
    cxtree_blob_hash: [32]u8 = @splat(0),
};

/// Queue membership state of an `OverlaySlot` inside `OverlayCache`.
pub const OverlayQueueKind = enum(u8) {
    /// Detached or recycled on `OverlayCache.free_head`.
    detached = 0,
    /// Linked in the open-editor LRU queue (`open_head_mru` .. `open_tail_lru`).
    open_editor = 1,
    /// Linked in the closed virtual-buffer LRU queue (`closed_head_mru` .. `closed_tail_lru`).
    closed_virtual = 2,
};

/// Intrusive doubly-linked LRU slot owning a heap-allocated `:0` overlay buffer.
pub const OverlaySlot = struct {
    /// `FileId` currently backed by `owned_z` (`.none` when free-listed).
    file_id: FileId = .none,
    /// Heap-allocated NUL-terminated UTF-8 buffer owned by `VfsSourceMap.backing_allocator`.
    owned_z: ?[:0]u8 = null,
    /// Active LRU queue containing this slot.
    queue_kind: OverlayQueueKind = .detached,
    /// Index of the more-recently-used neighbor (`OVERLAY_SLOT_NONE` at queue head).
    prev_mru: u32 = OVERLAY_SLOT_NONE,
    /// Index of the less-recently-used neighbor (`OVERLAY_SLOT_NONE` at tail, or next free slot).
    next_lru: u32 = OVERLAY_SLOT_NONE,
};

/// Dual-bounded two-queue $O(1)$ intrusive LRU cache managing heap-allocated `:0` overlays.
pub const OverlayCache = struct {
    /// Contiguous pool of `OverlaySlot` records indexed by `u32` slot IDs.
    slots: std.ArrayList(OverlaySlot) = .empty,
    /// $O(1)$ lookup map from `FileId` to its active slot index in `slots`.
    file_to_slot: std.AutoHashMapUnmanaged(FileId, u32) = .empty,
    /// Head of the recycled slot free list (`OVERLAY_SLOT_NONE` when empty).
    free_head: u32 = OVERLAY_SLOT_NONE,
    /// Most-recently-used head of the open-editor queue (`is_open_in_editor == true`).
    open_head_mru: u32 = OVERLAY_SLOT_NONE,
    /// Least-recently-used tail of the open-editor queue (`is_open_in_editor == true`).
    open_tail_lru: u32 = OVERLAY_SLOT_NONE,
    /// Most-recently-used head of the closed virtual-buffer queue (`is_open_in_editor == false`).
    closed_head_mru: u32 = OVERLAY_SLOT_NONE,
    /// Least-recently-used tail of the closed virtual-buffer queue (`is_open_in_editor == false`).
    closed_tail_lru: u32 = OVERLAY_SLOT_NONE,
    /// Total number of active overlay slots across both queues.
    entry_count: usize = 0,
    /// Aggregate byte length (`owned_z.len`) across all active overlay slots.
    total_bytes: usize = 0,

    /// Unlinks `slot_idx` from its active open or closed LRU queue in $O(1)$ time.
    fn detachSlot(self: *OverlayCache, slot_idx: u32) void {
        const slot = &self.slots.items[slot_idx];
        const head_ptr: *u32, const tail_ptr: *u32 = switch (slot.queue_kind) {
            .detached => return,
            .open_editor => .{ &self.open_head_mru, &self.open_tail_lru },
            .closed_virtual => .{ &self.closed_head_mru, &self.closed_tail_lru },
        };
        if (slot.prev_mru != OVERLAY_SLOT_NONE) {
            self.slots.items[slot.prev_mru].next_lru = slot.next_lru;
        } else {
            head_ptr.* = slot.next_lru;
        }
        if (slot.next_lru != OVERLAY_SLOT_NONE) {
            self.slots.items[slot.next_lru].prev_mru = slot.prev_mru;
        } else {
            tail_ptr.* = slot.prev_mru;
        }
        slot.prev_mru = OVERLAY_SLOT_NONE;
        slot.next_lru = OVERLAY_SLOT_NONE;
        slot.queue_kind = .detached;
    }

    /// Inserts detached `slot_idx` at the MRU head of the open or closed LRU queue in $O(1)$ time.
    fn attachHeadMru(self: *OverlayCache, slot_idx: u32, is_open_in_editor: bool) void {
        std.debug.assert(self.slots.items[slot_idx].queue_kind == .detached);
        const head_ptr: *u32, const tail_ptr: *u32, const target_queue: OverlayQueueKind = if (is_open_in_editor)
            .{ &self.open_head_mru, &self.open_tail_lru, .open_editor }
        else
            .{ &self.closed_head_mru, &self.closed_tail_lru, .closed_virtual };

        const prev_head = head_ptr.*;
        const slot = &self.slots.items[slot_idx];
        slot.queue_kind = target_queue;
        slot.prev_mru = OVERLAY_SLOT_NONE;
        slot.next_lru = prev_head;
        if (prev_head != OVERLAY_SLOT_NONE) {
            self.slots.items[prev_head].prev_mru = slot_idx;
        } else {
            tail_ptr.* = slot_idx;
        }
        head_ptr.* = slot_idx;
    }

    /// Pops a recycled slot from `free_head` or appends a new slot assuming pre-reserved capacity.
    fn acquireSlotAssumeCapacity(self: *OverlayCache) u32 {
        if (self.free_head != OVERLAY_SLOT_NONE) {
            const recycled_idx = self.free_head;
            const slot = &self.slots.items[recycled_idx];
            self.free_head = slot.next_lru;
            slot.* = .{};
            return recycled_idx;
        }
        const fresh_idx: u32 = @intCast(self.slots.items.len);
        self.slots.appendAssumeCapacity(.{});
        return fresh_idx;
    }

    /// Detaches `slot_idx`, frees its `owned_z` buffer, removes `file_id` from `file_to_slot`, and recycles the slot.
    fn removeAndFreeSlot(self: *OverlayCache, allocator: std.mem.Allocator, slot_idx: u32) void {
        self.detachSlot(slot_idx);
        const slot = &self.slots.items[slot_idx];
        if (!slot.file_id.isNone()) {
            _ = self.file_to_slot.remove(slot.file_id);
            slot.file_id = .none;
            self.entry_count -= 1;
        }
        if (slot.owned_z) |owned_buf| {
            self.total_bytes -= owned_buf.len;
            allocator.free(owned_buf);
            slot.owned_z = null;
        }
        slot.next_lru = self.free_head;
        self.free_head = slot_idx;
    }

    /// Selects the least-recently-used unpinned victim slot (`closed_tail_lru` strictly before `open_tail_lru`).
    fn selectVictimSlot(self: *const OverlayCache, pinned_file_id: FileId) ?u32 {
        var cursor = self.closed_tail_lru;
        while (cursor != OVERLAY_SLOT_NONE) {
            if (self.slots.items[cursor].file_id != pinned_file_id) return cursor;
            cursor = self.slots.items[cursor].prev_mru;
        }
        cursor = self.open_tail_lru;
        while (cursor != OVERLAY_SLOT_NONE) {
            if (self.slots.items[cursor].file_id != pinned_file_id) return cursor;
            cursor = self.slots.items[cursor].prev_mru;
        }
        return null;
    }

    /// Releases all owned `:0` overlay buffers, slot storage, and lookup maps.
    fn deinit(self: *OverlayCache, allocator: std.mem.Allocator) void {
        for (self.slots.items) |*slot| {
            if (slot.owned_z) |owned_buf| {
                allocator.free(owned_buf);
                slot.owned_z = null;
            }
        }
        self.slots.deinit(allocator);
        self.file_to_slot.deinit(allocator);
        self.* = undefined;
    }
};

/// Loaded disk buffer result returned by `readOpenFileIntoBacking`.
const LoadedDiskBuffer = struct {
    /// NUL-terminated UTF-8 file contents (`mmap` view or `small_file_arena` slice).
    content: [:0]const u8,
    /// Storage strategy owning `content` (`.mmap_large` or `.arena_small`).
    backing_kind: BackingKind,
    /// Active OS memory mapping when `backing_kind == .mmap_large`.
    memory_map: ?std.Io.File.MemoryMap = null,
    /// Open OS file handle retained while `memory_map` is active.
    mapped_file: ?std.Io.File = null,
};

/// Heap-allocated demand pager backing lazy `.cxtree` blob reads across `*const VfsSourceMap` queries.
const LazyCxTreePager = struct {
    /// Active `std.Io` handle used to open/mmap immutable blobs on first access.
    io: std.Io,
    /// Backing allocator for temporary path formatting.
    backing_allocator: std.mem.Allocator,
    /// Shared interner resolving internal `blobs_dir_id` paths.
    interner: *const StringInterner,
    /// Dedicated 64 KiB slab arena owning `< 16 KiB` and page-aligned `.cxtree` blob buffers with `:0` sentinels.
    blob_arena: BumpArena,
    /// First `FileId` that failed `BLAKE3` verification during a `getFileEntry`/`getFileSource` fault.
    first_integrity_error_file: FileId = .none,
    /// Total count of blob integrity failures observed by this pager.
    integrity_error_count: u32 = 0,

    /// Releases `blob_arena` slabs owned by this pager.
    fn deinit(self: *LazyCxTreePager) void {
        self.blob_arena.deinit();
        self.* = undefined;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Canonical 4-byte magic signature at the start of every `.cxtree` manifest.
pub const CXTREE_MAGIC: [4]u8 = .{ 'C', 'X', 'T', 'R' };
/// Canonical `.cxtree` binary format version.
pub const CXTREE_VERSION: u32 = 1;
/// Size threshold (`16 KiB`) separating `BumpArena` reads from OS `mmap` mappings.
pub const SMALL_FILE_THRESHOLD: usize = 16 * 1024;
/// Hard maximum size (`64 MiB`) permitted for any single source file in `VfsSourceMap`.
pub const MAX_SOURCE_FILE_BYTES: usize = 64 * 1024 * 1024;
/// Hard maximum number of files (`65,536`) that may be loaded into `VfsSourceMap`.
pub const MAX_LOADED_FILES: usize = 65_536;
/// Maximum number of heap-allocated overlays retained simultaneously in `OverlayCache`.
pub const MAX_OPEN_OVERLAYS: usize = 256;
/// Maximum aggregate byte footprint (`64 MiB`) of heap-allocated overlays in `OverlayCache`.
pub const MAX_OPEN_OVERLAY_BYTES: usize = 64 * 1024 * 1024;
/// Sentinel `u32` slot index representing an empty link in `OverlayCache` LRU queues.
const OVERLAY_SLOT_NONE: u32 = std.math.maxInt(u32);
/// Standard OS virtual memory page granularity (`4096` bytes) used for `mmap` sentinel checks.
const OS_PAGE_SIZE: usize = 4096;

// -------------------------------------- INTERNALS --------------------------------------

/// Normalizes backslashes (`\`) to `/` and Windows drive letters (`D:` -> `d:`), then interns the path.
fn internNormalizedPath(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    raw_path: []const u8,
) !StringId {
    const has_drive_prefix = raw_path.len >= 2 and std.ascii.isAlphabetic(raw_path[0]) and raw_path[1] == ':';
    if (!(has_drive_prefix and std.ascii.isUpper(raw_path[0])) and
        std.mem.indexOfScalar(u8, raw_path, '\\') == null)
    {
        return interner.intern(raw_path);
    }
    const normalized_buf = try allocator.alloc(u8, raw_path.len);
    defer allocator.free(normalized_buf);
    for (raw_path, 0..) |path_byte, i| {
        normalized_buf[i] = if (path_byte == '\\') '/' else path_byte;
    }
    if (has_drive_prefix) {
        normalized_buf[0] = std.ascii.toLower(normalized_buf[0]);
    }
    return interner.intern(normalized_buf);
}

/// Computes the 256-bit BLAKE3 digest of `source_bytes`.
inline fn computeBlake3Hash(source_bytes: []const u8) [32]u8 {
    var digest: [32]u8 = undefined;
    std.crypto.hash.Blake3.hash(source_bytes, &digest, .{});
    return digest;
}

/// Returns `true` iff `rel_path` is a canonical, traversal-free POSIX relative `.cxtree` path.
fn isValidCxTreeRelativePathImpl(rel_path: []const u8) bool {
    if (rel_path.len == 0 or rel_path.len > 4096) return false;
    if (rel_path[0] == '/' or rel_path[rel_path.len - 1] == '/') return false;
    if (!std.unicode.utf8ValidateSlice(rel_path)) return false;

    for (rel_path) |ch_byte| {
        if (ch_byte < 0x20 or ch_byte == 0x7F or ch_byte == '\\' or ch_byte == ':') return false;
    }

    var seg_iter = std.mem.splitScalar(u8, rel_path, '/');
    while (seg_iter.next()) |seg| {
        if (seg.len == 0) return false;
        if (std.mem.eql(u8, seg, ".") or std.mem.eql(u8, seg, "..")) return false;
    }
    return true;
}

/// Marks `target_entry` as corrupted in `target_pager` and returns `error.CacheIntegrityMismatch`.
fn markLazyIntegrityFailure(
    target_pager: *LazyCxTreePager,
    target_entry: *VfsFileEntry,
) error{CacheIntegrityMismatch} {
    target_entry.has_blob_integrity_error = true;
    if (target_pager.first_integrity_error_file.isNone()) {
        target_pager.first_integrity_error_file = target_entry.file_id;
    }
    target_pager.integrity_error_count += 1;
    return error.CacheIntegrityMismatch;
}

/// Opens `<blobs_dir>/<2-hex>/<62-hex>` (falling back to `<2-hex>/<2-hex>/<64-hex>`) in read-only mode.
fn openCachedBlobFile(
    io: std.Io,
    allocator: std.mem.Allocator,
    blobs_dir: []const u8,
    digest: [32]u8,
) !std.Io.File {
    const hex = std.fmt.bytesToHex(digest, .lower);
    const trimmed_root = std.mem.trimEnd(u8, blobs_dir, "/\\");
    const primary_path = try std.fmt.allocPrint(
        allocator,
        "{s}/{s}/{s}",
        .{ trimmed_root, hex[0..2], hex[2..64] },
    );
    defer allocator.free(primary_path);

    if (std.Io.Dir.cwd().openFile(io, primary_path, .{
        .mode = .read_only,
        .allow_directory = false,
    })) |opened_primary| {
        return opened_primary;
    } else |open_err| {
        if (open_err != error.FileNotFound) return open_err;
    }

    const two_level_path = try std.fmt.allocPrint(
        allocator,
        "{s}/{s}/{s}/{s}",
        .{ trimmed_root, hex[0..2], hex[2..4], hex[0..64] },
    );
    defer allocator.free(two_level_path);
    return std.Io.Dir.cwd().openFile(io, two_level_path, .{
        .mode = .read_only,
        .allow_directory = false,
    });
}

/// Faults an unloaded `.cxtree` `entry` from `blobs/`, verifying `BLAKE3(bytes) == entry.content_hash`.
fn faultLazyEntryIfNeeded(pager: *LazyCxTreePager, entry: *VfsFileEntry) !void {
    if (entry.has_blob_integrity_error) return error.CacheIntegrityMismatch;
    if (entry.is_blob_loaded) return;

    const blobs_dir = pager.interner.get(entry.blobs_dir_id);
    if (blobs_dir.len == 0) return markLazyIntegrityFailure(pager, entry);

    const opened_file = openCachedBlobFile(
        pager.io,
        pager.backing_allocator,
        blobs_dir,
        entry.content_hash,
    ) catch {
        return markLazyIntegrityFailure(pager, entry);
    };
    errdefer opened_file.close(pager.io);

    const file_stat = opened_file.stat(pager.io) catch {
        return markLazyIntegrityFailure(pager, entry);
    };
    if (file_stat.kind == .directory or file_stat.size != entry.unloaded_blob_size) {
        return markLazyIntegrityFailure(pager, entry);
    }
    const file_size: usize = entry.unloaded_blob_size;

    // [1] Use read-only OS `mmap` for `>= 16 KiB` blobs not ending on a 4096-byte page boundary:
    if (file_size >= SMALL_FILE_THRESHOLD and (file_size % OS_PAGE_SIZE) != 0) {
        if (opened_file.createMemoryMap(pager.io, .{
            .len = file_size,
            .protection = .{ .read = true, .write = false },
            .populate = true,
            .offset = 0,
        })) |memory_map| {
            const raw_mapped_ptr: [*]const u8 = @ptrCast(memory_map.memory.ptr);
            if (memory_map.section != null and raw_mapped_ptr[file_size] == 0) {
                const mapped_content: [:0]const u8 = raw_mapped_ptr[0..file_size :0];
                if (!std.crypto.timing_safe.eql([32]u8, computeBlake3Hash(mapped_content), entry.content_hash)) {
                    var bad_map = memory_map;
                    bad_map.destroy(pager.io);
                    return markLazyIntegrityFailure(pager, entry);
                }
                entry.content = mapped_content;
                entry.memory_map = memory_map;
                entry.mapped_file = opened_file;
                entry.is_blob_loaded = true;
                return;
            }
            var cleanup_map = memory_map;
            cleanup_map.destroy(pager.io);
        } else |_| {}
    }

    // [2] Read `< 16 KiB`, page-multiple, or fallback blobs into `blob_arena` with explicit `:0` NUL sentinel:
    const arena_buf = try pager.blob_arena.allocSlice(u8, file_size + 1);
    if ((opened_file.readPositionalAll(pager.io, arena_buf[0..file_size], 0) catch {
        return markLazyIntegrityFailure(pager, entry);
    }) != file_size) {
        return markLazyIntegrityFailure(pager, entry);
    }
    arena_buf[file_size] = 0;
    opened_file.close(pager.io);

    const arena_content: [:0]const u8 = arena_buf[0..file_size :0];
    if (!std.crypto.timing_safe.eql([32]u8, computeBlake3Hash(arena_content), entry.content_hash)) {
        return markLazyIntegrityFailure(pager, entry);
    }
    entry.content = arena_content;
    entry.is_blob_loaded = true;
}

comptime {
    std.debug.assert(@sizeOf(PackageId) == 2);
    std.debug.assert(@sizeOf(PositionEncoding) == 1);
    std.debug.assert(@sizeOf(CxTreeHeader) == 32);
    std.debug.assert(@sizeOf(CxTreeEntry) == 48);
    std.debug.assert(@alignOf(CxTreeHeader) == 8);
    std.debug.assert(@alignOf(CxTreeEntry) == 8);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------- CxTree Validation & Lookup -----------------

/// Returns `true` iff `rel_path` is a canonical, traversal-free POSIX relative `.cxtree` path.
pub fn isValidCxTreeRelativePath(rel_path: []const u8) bool {
    return isValidCxTreeRelativePathImpl(rel_path);
}

/// Validates a binary `.cxtree` buffer (`CxTreeHeader`, sorted `CxTreeEntry` table, and case-collision set).
pub fn validateCxTreeBytes(
    allocator: std.mem.Allocator,
    bytes: []const u8,
) (CxTreeError || std.mem.Allocator.Error)!CxTreeView {
    if (bytes.len < @sizeOf(CxTreeHeader)) return error.TruncatedCxTree;
    var header: CxTreeHeader = undefined;
    @memcpy(std.mem.asBytes(&header), bytes[0..@sizeOf(CxTreeHeader)]);

    if (!std.mem.eql(u8, &header.magic, &CXTREE_MAGIC)) return error.InvalidCxTreeMagic;
    if (header.version != CXTREE_VERSION) return error.UnsupportedCxTreeVersion;

    const entries_byte_len = std.math.mul(usize, header.entry_count, @sizeOf(CxTreeEntry)) catch {
        return error.CxTreeSizeMismatch;
    };
    const body_byte_len = std.math.add(usize, entries_byte_len, header.string_table_bytes) catch {
        return error.CxTreeSizeMismatch;
    };
    const expected_total = std.math.add(usize, @sizeOf(CxTreeHeader), body_byte_len) catch {
        return error.CxTreeSizeMismatch;
    };
    if (bytes.len != expected_total or header.pkg_name_str_off > header.string_table_bytes) {
        return error.CxTreeSizeMismatch;
    }

    const entries = std.mem.bytesAsSlice(
        CxTreeEntry,
        bytes[@sizeOf(CxTreeHeader) .. @sizeOf(CxTreeHeader) + entries_byte_len],
    );
    const string_table = bytes[@sizeOf(CxTreeHeader) + entries_byte_len ..];

    // [1] Verify path validity, strict ascending bytewise order, and check for any ASCII uppercase byte:
    var has_ascii_upper = false;
    var prev_path: ?[]const u8 = null;
    for (entries) |entry| {
        if (entry.file_mode != 0x01 and entry.file_mode != 0x02) return error.InvalidCxTreeFileMode;
        if (entry.file_size > MAX_SOURCE_FILE_BYTES or entry.file_size > std.math.maxInt(u32)) {
            return error.InvalidCxTreeFileMode;
        }
        const path_end = std.math.add(usize, entry.rel_path_off, entry.rel_path_len) catch {
            return error.InvalidCxTreePath;
        };
        if (path_end > string_table.len) return error.InvalidCxTreePath;
        const rel_path = string_table[entry.rel_path_off..path_end];
        if (!isValidCxTreeRelativePath(rel_path)) return error.InvalidCxTreePath;

        if (prev_path) |prior_path| {
            switch (std.mem.order(u8, prior_path, rel_path)) {
                .lt => {},
                .eq => return error.DuplicateOrCaseCollidingCxTreePath,
                .gt => return error.UnsortedCxTreePaths,
            }
        }
        prev_path = rel_path;

        if (!has_ascii_upper) {
            for (rel_path) |path_byte| {
                if (path_byte >= 'A' and path_byte <= 'Z') {
                    has_ascii_upper = true;
                    break;
                }
            }
        }
    }

    // [2] Only allocate lowercase collision table when `entries.len > 1` and `'A'..'Z'` is present:
    if (entries.len > 1 and has_ascii_upper) {
        var lower_arena = BumpArena.init(allocator);
        defer lower_arena.deinit();
        var seen_lower_paths: std.StringHashMapUnmanaged(void) = .empty;
        defer seen_lower_paths.deinit(allocator);
        try seen_lower_paths.ensureTotalCapacity(allocator, @intCast(entries.len));

        for (entries) |entry| {
            const rel_path = string_table[entry.rel_path_off .. entry.rel_path_off + entry.rel_path_len];
            const lower_copy = try lower_arena.allocSlice(u8, rel_path.len);
            for (rel_path, 0..) |path_byte, i| {
                lower_copy[i] = std.ascii.toLower(path_byte);
            }
            if (seen_lower_paths.getOrPutAssumeCapacity(lower_copy).found_existing) {
                return error.DuplicateOrCaseCollidingCxTreePath;
            }
        }
    }

    return .{
        .header = header,
        .entries = entries,
        .string_table = string_table,
    };
}

/// Performs a zero-allocation $O(\log K)$ binary search for `rel_path` in `view`.
pub fn lookupCxTreeEntry(view: CxTreeView, rel_path: []const u8) ?CxTreeEntry {
    var low: usize = 0;
    var high: usize = view.entries.len;
    while (low < high) {
        const mid = low + (high - low) / 2;
        const candidate: CxTreeEntry = view.entries[mid];
        switch (std.mem.order(u8, view.asEntryPath(candidate), rel_path)) {
            .lt => low = mid + 1,
            .gt => high = mid,
            .eq => return candidate,
        }
    }
    return null;
}

// ----------------- Line Index Implementation ------------------

/// Binary-searchable line start table with an ASCII fast-path bitset for $O(\log L)$ column lookup.
pub const LineIndex = struct {
    /// Sorted byte offsets of the start of every line (`line_starts[0] == 0`).
    line_starts: []const u32,
    /// Bitset marking 0-based line indices that contain at least one non-ASCII byte (`>= 0x80`).
    non_ascii_lines: std.bit_set.Dynamic,
    /// Total byte length of the indexed source buffer.
    source_len: u32,

    /// Builds a `LineIndex` for `source` in a single non-backtracking $O(N)$ linear scan.
    pub fn build(allocator: std.mem.Allocator, source: []const u8) !LineIndex {
        if (source.len > std.math.maxInt(u32)) return error.SourceTooLarge;

        // [1] Collect line start offsets and track which lines contain non-ASCII bytes:
        var starts_list: std.ArrayList(u32) = .empty;
        errdefer starts_list.deinit(allocator);
        try starts_list.append(allocator, 0);

        var non_ascii_flags: std.ArrayList(bool) = .empty;
        errdefer non_ascii_flags.deinit(allocator);

        var has_non_ascii_in_line = false;
        for (source, 0..) |byte_val, i| {
            if (byte_val >= 0x80) {
                has_non_ascii_in_line = true;
            }
            if (byte_val == '\n') {
                try non_ascii_flags.append(allocator, has_non_ascii_in_line);
                has_non_ascii_in_line = false;
                try starts_list.append(allocator, @intCast(i + 1));
            }
        }
        try non_ascii_flags.append(allocator, has_non_ascii_in_line);

        // [2] Pack per-line non-ASCII booleans into a compact `std.bit_set.Dynamic`:
        var non_ascii_bitset = try std.bit_set.Dynamic.initEmpty(allocator, starts_list.items.len);
        errdefer non_ascii_bitset.deinit(allocator);
        for (non_ascii_flags.items, 0..) |is_non_ascii, i| {
            if (is_non_ascii) {
                non_ascii_bitset.set(i);
            }
        }
        non_ascii_flags.deinit(allocator);

        return .{
            .line_starts = try starts_list.toOwnedSlice(allocator),
            .non_ascii_lines = non_ascii_bitset,
            .source_len = @intCast(source.len),
        };
    }

    /// Releases the `line_starts` slice and `non_ascii_lines` bitset.
    pub fn deinit(self: *LineIndex, allocator: std.mem.Allocator) void {
        allocator.free(self.line_starts);
        self.non_ascii_lines.deinit(allocator);
        self.* = undefined;
    }

    /// Returns the total number of lines in the indexed file (`>= 1`).
    pub inline fn countLines(self: *const LineIndex) u32 {
        return @intCast(self.line_starts.len);
    }

    /// Returns the `[start .. end)` byte bounds of 0-based `line_index_0` (stripping `\r` and `\n`).
    pub fn getLineBounds(self: *const LineIndex, source: []const u8, line_index_0: u32) LineBounds {
        std.debug.assert(line_index_0 < self.line_starts.len);
        const start_byte = self.line_starts[line_index_0];
        const next_line_idx = @as(usize, line_index_0) + 1;
        var end_byte: u32 = if (next_line_idx < self.line_starts.len)
            self.line_starts[next_line_idx] - 1
        else
            self.source_len;

        if (end_byte > start_byte and end_byte <= source.len and source[end_byte - 1] == '\r') {
            end_byte -= 1;
        }
        return .{ .start = start_byte, .end = end_byte };
    }

    /// Returns the UTF-8 slice for 1-based line number `line_1_based` (excluding `\r\n` or `\n`).
    pub fn getLineSlice(self: *const LineIndex, source: []const u8, line_1_based: u32) []const u8 {
        if (line_1_based == 0 or line_1_based > self.countLines()) {
            return source[0..0];
        }
        const bounds = self.getLineBounds(source, line_1_based - 1);
        return source[bounds.start..bounds.end];
    }

    /// Resolves `byte_offset` in `source` to 1-based UTF-8/byte columns and 0-based UTF-16 column.
    pub fn resolveLineCol(self: *const LineIndex, source: []const u8, byte_offset: u32) LineCol {
        const clamped_offset = @min(byte_offset, self.source_len);

        // [1] Binary search `line_starts` in O(log L) time:
        var low: usize = 0;
        var high: usize = self.line_starts.len;
        while (low + 1 < high) {
            const mid = low + (high - low) / 2;
            if (self.line_starts[mid] <= clamped_offset) {
                low = mid;
            } else {
                high = mid;
            }
        }
        const line_index_0: u32 = @intCast(low);
        const bounds = self.getLineBounds(source, line_index_0);

        // [2] Clamp offset to `bounds.end` so `CRLF` `\r` is never counted on `\n` queries:
        const line_offset = @min(clamped_offset, bounds.end);
        const col_byte_0 = line_offset - bounds.start;

        // [3] Fast path; O(1) column arithmetic for pure-ASCII lines:
        if (!self.non_ascii_lines.isSet(line_index_0)) {
            return .{
                .line = line_index_0 + 1,
                .col_utf8 = col_byte_0 + 1,
                .col_utf16_0 = col_byte_0,
                .col_byte = col_byte_0 + 1,
                .line_start_byte = bounds.start,
                .line_end_byte = bounds.end,
            };
        }

        // [4] Slow path; fault-tolerant non-panicking UTF-8 and UTF-16 code-unit scan:
        var col_utf8: u32 = 1;
        var col_utf16_0: u32 = 0;
        var cursor: usize = bounds.start;
        const limit: usize = @min(@as(usize, line_offset), source.len);
        const line_end: usize = @min(@as(usize, bounds.end), source.len);
        while (cursor < limit) {
            const first_byte = source[cursor];
            if (first_byte < 0x80) {
                col_utf8 += 1;
                col_utf16_0 += 1;
                cursor += 1;
            } else {
                const seq_len = std.unicode.utf8ByteSequenceLength(first_byte) catch {
                    col_utf8 += 1;
                    col_utf16_0 += 1;
                    cursor += 1;
                    continue;
                };
                if (cursor + seq_len > line_end) {
                    col_utf8 += 1;
                    col_utf16_0 += 1;
                    cursor += 1;
                    continue;
                }
                const codepoint = std.unicode.utf8Decode(source[cursor .. cursor + seq_len]) catch {
                    col_utf8 += 1;
                    col_utf16_0 += 1;
                    cursor += 1;
                    continue;
                };
                if (cursor + seq_len > limit) break;
                col_utf8 += 1;
                col_utf16_0 += if (codepoint >= 0x10000) 2 else 1;
                cursor += seq_len;
            }
        }

        return .{
            .line = line_index_0 + 1,
            .col_utf8 = col_utf8,
            .col_utf16_0 = col_utf16_0,
            .col_byte = col_byte_0 + 1,
            .line_start_byte = bounds.start,
            .line_end_byte = bounds.end,
        };
    }

    /// Extracts the 0-based LSP `Position.character` offset from `line_col` for `encoding`.
    pub inline fn extractLspCharacter0(line_col: LineCol, encoding: PositionEncoding) u32 {
        return switch (encoding) {
            .utf16 => line_col.col_utf16_0,
            .utf8 => line_col.col_byte -| 1,
        };
    }

    /// Resolves 0-based LSP `(line_0, character_0)` in `encoding` to a clamped UTF-8 scalar byte offset.
    pub fn resolveByteOffset(
        self: *const LineIndex,
        source: []const u8,
        line_0: u32,
        character_0: u32,
        encoding: PositionEncoding,
    ) u32 {
        const effective_len: u32 = @min(
            self.source_len,
            @as(u32, @intCast(@min(source.len, std.math.maxInt(u32)))),
        );
        if (line_0 >= self.countLines()) return effective_len;

        const bounds = self.getLineBounds(source, line_0);
        if (bounds.start >= effective_len) return effective_len;
        const line_end: u32 = @min(bounds.end, effective_len);
        const line_byte_len: u32 = line_end - bounds.start;

        // [1] Fast path; O(1) overflow-safe byte offset arithmetic for pure-ASCII lines:
        if (!self.non_ascii_lines.isSet(line_0)) {
            return if (character_0 >= line_byte_len) line_end else bounds.start + character_0;
        }

        // [2] Non-ASCII `.utf8` and `.utf16` decoding with mid-scalar / mid-surrogate floor clamping:
        switch (encoding) {
            .utf8 => {
                if (character_0 >= line_byte_len) return line_end;
                const orig_target: u32 = bounds.start + character_0;
                if ((source[orig_target] & 0xC0) != 0x80) return orig_target;

                var candidate: u32 = orig_target;
                var back_steps: u8 = 0;
                while (back_steps < 3 and candidate > bounds.start and (source[candidate] & 0xC0) == 0x80) : (back_steps += 1) {
                    candidate -= 1;
                }
                const seq_len: u32 = std.unicode.utf8ByteSequenceLength(source[candidate]) catch 1;
                if (seq_len > 1 and
                    seq_len <= line_end - candidate and
                    candidate + seq_len > orig_target and
                    (std.unicode.utf8Decode(source[candidate .. candidate + seq_len]) catch null) != null)
                {
                    return candidate;
                }
                return orig_target;
            },
            .utf16 => {
                var cursor: usize = bounds.start;
                var utf16_acc: u32 = 0;
                const limit: usize = line_end;
                while (cursor < limit) {
                    if (utf16_acc >= character_0) return @intCast(cursor);
                    const first_byte = source[cursor];
                    if (first_byte < 0x80) {
                        utf16_acc += 1;
                        cursor += 1;
                        continue;
                    }
                    const seq_len = std.unicode.utf8ByteSequenceLength(first_byte) catch {
                        utf16_acc += 1;
                        cursor += 1;
                        continue;
                    };
                    if (cursor + seq_len > limit) {
                        utf16_acc += 1;
                        cursor += 1;
                        continue;
                    }
                    const codepoint = std.unicode.utf8Decode(source[cursor .. cursor + seq_len]) catch {
                        utf16_acc += 1;
                        cursor += 1;
                        continue;
                    };
                    const utf16_units: u32 = if (codepoint >= 0x10000) 2 else 1;
                    if (character_0 - utf16_acc < utf16_units) return @intCast(cursor);
                    utf16_acc += utf16_units;
                    cursor += seq_len;
                }
                return line_end;
            },
        }
    }
};

// ---------------- VFS SourceMap Implementation ----------------

/// Virtual File System and SourceMap managing `< 16 KiB` arena buffers, `>= 16 KiB` `mmap`s, and LRU overlays.
pub const VfsSourceMap = struct {
    /// Backing allocator for metadata arrays, `OverlayCache` buffers, `LineIndex` tables, and path normalization.
    backing_allocator: std.mem.Allocator,
    /// Shared string interner used to intern virtual and resolved OS file paths.
    interner: *StringInterner,
    /// Dedicated bump arena storing `< 16 KiB` disk file contents with `:0` NUL sentinels.
    small_file_arena: BumpArena,
    /// Contiguous table of loaded `VfsFileEntry` records indexed by `FileId.asInt()`.
    entries: std.ArrayList(VfsFileEntry) = .empty,
    /// $O(1)$ lookup map from interned normalized/resolved path `StringId` to `FileId`.
    path_to_file_id: std.AutoHashMapUnmanaged(StringId, FileId) = .empty,
    /// Dual-bounded two-queue $O(1)$ LRU cache owning heap-allocated `:0` editor and virtual overlays.
    overlay_cache: OverlayCache = .{},
    /// Optional heap-allocated demand pager for lazily mounted `.cxtree` package blobs.
    lazy_pager: ?*LazyCxTreePager = null,
    /// Most recent `std.Io` handle observed by `VfsSourceMap` for `mmap` teardown and disk reloads.
    last_io: ?std.Io = null,

    /// Initializes an empty `VfsSourceMap` bound to `backing_allocator` and `interner`.
    pub fn init(backing_allocator: std.mem.Allocator, interner: *StringInterner) VfsSourceMap {
        return .{
            .backing_allocator = backing_allocator,
            .interner = interner,
            .small_file_arena = BumpArena.init(backing_allocator),
        };
    }

    /// Updates the cached `std.Io` handle used by `setOverlay` and LRU eviction disk fallbacks.
    pub inline fn setIo(self: *VfsSourceMap, io: std.Io) void {
        self.last_io = io;
    }

    /// Releases all `LineIndex` instances, `OverlayCache` buffers, `MemoryMap` regions, files, and arenas.
    pub fn deinit(self: *VfsSourceMap, io: std.Io) void {
        self.last_io = io;
        for (self.entries.items) |*entry| {
            if (entry.line_index) |*line_idx| {
                line_idx.deinit(self.backing_allocator);
            }
            if (entry.memory_map) |*mem_map| {
                mem_map.destroy(io);
            }
            if (entry.mapped_file) |opened_file| {
                opened_file.close(io);
            }
        }
        self.overlay_cache.deinit(self.backing_allocator);
        if (self.lazy_pager) |pager| {
            pager.deinit();
            self.backing_allocator.destroy(pager);
            self.lazy_pager = null;
        }
        self.entries.deinit(self.backing_allocator);
        self.path_to_file_id.deinit(self.backing_allocator);
        self.small_file_arena.deinit();
        self.* = undefined;
    }

    /// Reads or maps an open regular file of `file_size` bytes, taking ownership of `opened_file`.
    fn readOpenFileIntoBacking(
        self: *VfsSourceMap,
        io: std.Io,
        opened_file: std.Io.File,
        file_size: usize,
    ) !LoadedDiskBuffer {
        var is_file_transferred = false;
        errdefer if (!is_file_transferred) opened_file.close(io);

        // [1] Attempt zero-copy OS `mmap` for `>= 16 KiB` files not landing on a 4096-byte page boundary:
        if (file_size >= SMALL_FILE_THRESHOLD and (file_size % OS_PAGE_SIZE) != 0) {
            if (opened_file.createMemoryMap(io, .{
                .len = file_size,
                .protection = .{ .read = true, .write = false },
                .populate = true,
                .offset = 0,
            })) |memory_map| {
                const raw_mapped_ptr: [*]const u8 = @ptrCast(memory_map.memory.ptr);
                if (memory_map.section != null and raw_mapped_ptr[file_size] == 0) {
                    is_file_transferred = true;
                    return .{
                        .content = raw_mapped_ptr[0..file_size :0],
                        .backing_kind = .mmap_large,
                        .memory_map = memory_map,
                        .mapped_file = opened_file,
                    };
                }
                var cleanup_map = memory_map;
                cleanup_map.destroy(io);
            } else |_| {}
        }

        // [2] Read `< 16 KiB`, page-boundary, or fallback files into `small_file_arena` with NUL sentinel:
        const arena_buf = try self.small_file_arena.allocSlice(u8, file_size + 1);
        if ((try opened_file.readPositionalAll(io, arena_buf[0..file_size], 0)) != file_size) {
            return error.UnexpectedEndOfFile;
        }
        arena_buf[file_size] = 0;
        opened_file.close(io);
        is_file_transferred = true;

        return .{
            .content = arena_buf[0..file_size :0],
            .backing_kind = .arena_small,
        };
    }

    /// Probes `resolved_os_path` (then `virtual_path`) on disk and reloads `entry` if a regular file exists.
    fn tryReloadEntryFromDisk(self: *VfsSourceMap, io: std.Io, entry: *VfsFileEntry) !bool {
        const opened_file = std.Io.Dir.cwd().openFile(io, self.interner.get(entry.resolved_os_path), .{
            .mode = .read_only,
            .allow_directory = false,
        }) catch blk: {
            if (entry.virtual_path == entry.resolved_os_path) return false;
            break :blk std.Io.Dir.cwd().openFile(io, self.interner.get(entry.virtual_path), .{
                .mode = .read_only,
                .allow_directory = false,
            }) catch return false;
        };

        const file_stat = opened_file.stat(io) catch {
            opened_file.close(io);
            return false;
        };
        if (file_stat.kind == .directory) {
            opened_file.close(io);
            return false;
        }
        if (file_stat.size > MAX_SOURCE_FILE_BYTES or file_stat.size > std.math.maxInt(u32)) {
            opened_file.close(io);
            return error.FileTooLarge;
        }

        const loaded = try self.readOpenFileIntoBacking(io, opened_file, @intCast(file_stat.size));
        if (entry.memory_map) |*existing_map| {
            existing_map.destroy(io);
            entry.memory_map = null;
        }
        if (entry.mapped_file) |existing_file| {
            existing_file.close(io);
            entry.mapped_file = null;
        }
        if (entry.resolved_os_path == entry.virtual_path) {
            if (self.resolvePath(io, self.interner.get(entry.virtual_path))) |canon_id| {
                entry.resolved_os_path = canon_id;
                self.path_to_file_id.put(self.backing_allocator, canon_id, entry.file_id) catch {};
            } else |_| {}
        }

        entry.content = loaded.content;
        entry.content_hash = computeBlake3Hash(loaded.content);
        entry.backing_kind = loaded.backing_kind;
        entry.memory_map = loaded.memory_map;
        entry.mapped_file = loaded.mapped_file;
        entry.has_disk_backing = true;
        entry.is_open_in_editor = false;
        entry.is_blob_loaded = true;
        entry.has_blob_integrity_error = false;
        entry.revision += 1;
        return true;
    }

    /// Evicts unpinned LRU overlay slots (`closed_*` before `open_*`) until count and byte bounds hold.
    fn evictLeastRecentlyUsed(
        self: *VfsSourceMap,
        optional_io: ?std.Io,
        pinned_file_id: FileId,
    ) void {
        while (self.overlay_cache.entry_count > MAX_OPEN_OVERLAYS or
            self.overlay_cache.total_bytes > MAX_OPEN_OVERLAY_BYTES)
        {
            const victim_slot_idx = self.overlay_cache.selectVictimSlot(pinned_file_id) orelse break;
            const victim_entry = &self.entries.items[
                self.overlay_cache.slots.items[victim_slot_idx].file_id.asInt()
            ];

            // [1] Reset `victim_entry` BEFORE freeing `victim.owned_z` to guarantee zero UAF on reads:
            if (victim_entry.line_index) |*existing_line_idx| {
                existing_line_idx.deinit(self.backing_allocator);
                victim_entry.line_index = null;
            }
            if (victim_entry.blobs_dir_id != .empty and !victim_entry.blobs_dir_id.isNone()) {
                victim_entry.backing_kind = .cxtree_archive;
                victim_entry.content = "";
                victim_entry.content_hash = victim_entry.cxtree_blob_hash;
                victim_entry.is_blob_loaded = false;
                victim_entry.has_blob_integrity_error = false;
                victim_entry.is_open_in_editor = false;
                victim_entry.revision += 1;
            } else {
                const has_reloaded_disk = if (optional_io) |io|
                    (self.tryReloadEntryFromDisk(io, victim_entry) catch false)
                else
                    false;
                if (!has_reloaded_disk) {
                    victim_entry.backing_kind = .in_memory_overlay;
                    victim_entry.content = "";
                    victim_entry.content_hash = computeBlake3Hash("");
                    victim_entry.is_open_in_editor = false;
                    victim_entry.is_blob_loaded = true;
                    victim_entry.has_blob_integrity_error = false;
                    victim_entry.revision += 1;
                }
            }

            // [2] Detach, free `victim.owned_z`, and recycle `victim_slot_idx`:
            self.overlay_cache.removeAndFreeSlot(self.backing_allocator, victim_slot_idx);
        }
    }

    /// Normalizes path separators to `/` and resolves the canonical OS path when present on disk.
    pub fn resolvePath(self: *VfsSourceMap, io: std.Io, raw_path: []const u8) !StringId {
        const normalized_id = try internNormalizedPath(self.backing_allocator, self.interner, raw_path);
        if (self.path_to_file_id.contains(normalized_id)) {
            return normalized_id;
        }

        const real_os_path = std.Io.Dir.cwd().realPathFileAlloc(
            io,
            self.interner.get(normalized_id),
            self.backing_allocator,
        ) catch {
            return normalized_id;
        };
        defer self.backing_allocator.free(real_os_path);
        return internNormalizedPath(self.backing_allocator, self.interner, real_os_path);
    }

    /// Resolves `raw_path`, returning its existing `FileId` or loading it from disk if not yet registered.
    pub fn resolveOrCreatePath(
        self: *VfsSourceMap,
        io: std.Io,
        raw_path: []const u8,
        package_id: PackageId,
    ) !FileId {
        self.last_io = io;

        // [1] Check $O(1)$ virtual and canonical path lookup caches first:
        const virtual_id = try internNormalizedPath(self.backing_allocator, self.interner, raw_path);
        if (self.path_to_file_id.get(virtual_id)) |existing_id| {
            return existing_id;
        }

        const resolved_id = try self.resolvePath(io, self.interner.get(virtual_id));
        if (self.path_to_file_id.get(resolved_id)) |existing_id| {
            try self.path_to_file_id.put(self.backing_allocator, virtual_id, existing_id);
            return existing_id;
        }

        if (self.entries.items.len >= MAX_LOADED_FILES) return error.TooManyLoadedFiles;
        try self.entries.ensureUnusedCapacity(self.backing_allocator, 1);
        try self.path_to_file_id.ensureUnusedCapacity(self.backing_allocator, 2);

        // [2] Open and stat file on disk using the normalized `/` path, enforcing `MAX_SOURCE_FILE_BYTES`:
        const opened_file = try std.Io.Dir.cwd().openFile(io, self.interner.get(virtual_id), .{
            .mode = .read_only,
            .allow_directory = false,
        });
        const file_stat = opened_file.stat(io) catch |stat_err| {
            opened_file.close(io);
            return stat_err;
        };
        if (file_stat.kind == .directory) {
            opened_file.close(io);
            return error.IsDir;
        }
        if (file_stat.size > MAX_SOURCE_FILE_BYTES or file_stat.size > std.math.maxInt(u32)) {
            opened_file.close(io);
            return error.FileTooLarge;
        }

        const new_file_id = FileId.fromInt(@intCast(self.entries.items.len));

        // [3] Load `< 16 KiB` into `small_file_arena` or map `>= 16 KiB` via OS `mmap`:
        const loaded = try self.readOpenFileIntoBacking(io, opened_file, @intCast(file_stat.size));
        self.entries.appendAssumeCapacity(.{
            .file_id = new_file_id,
            .package_id = package_id,
            .virtual_path = virtual_id,
            .resolved_os_path = resolved_id,
            .content = loaded.content,
            .content_hash = computeBlake3Hash(loaded.content),
            .revision = 1,
            .backing_kind = loaded.backing_kind,
            .memory_map = loaded.memory_map,
            .mapped_file = loaded.mapped_file,
            .has_disk_backing = true,
        });
        self.path_to_file_id.putAssumeCapacity(virtual_id, new_file_id);
        self.path_to_file_id.putAssumeCapacity(resolved_id, new_file_id);
        return new_file_id;
    }

    /// Inserts or updates an open editor / in-memory file overlay managed by `OverlayCache`.
    pub fn setOverlay(
        self: *VfsSourceMap,
        virtual_path: []const u8,
        content_bytes: []const u8,
        package_id: PackageId,
    ) !FileId {
        return self.setEditorOverlay(self.last_io, virtual_path, content_bytes, package_id, true);
    }

    /// Inserts or updates a heap-backed `:0` file overlay in `OverlayCache` with two-queue LRU eviction.
    pub fn setEditorOverlay(
        self: *VfsSourceMap,
        optional_io: ?std.Io,
        virtual_path: []const u8,
        content_bytes: []const u8,
        package_id: PackageId,
        is_open_in_editor: bool,
    ) !FileId {
        if (optional_io) |io| self.last_io = io;
        if (content_bytes.len > MAX_SOURCE_FILE_BYTES or content_bytes.len > std.math.maxInt(u32)) {
            return error.FileTooLarge;
        }
        const effective_io: ?std.Io = optional_io orelse
            self.last_io orelse
            if (self.lazy_pager) |pager| pager.io else null;

        const virtual_id = try internNormalizedPath(self.backing_allocator, self.interner, virtual_path);
        var resolved_id = virtual_id;
        var existing_file_id = self.path_to_file_id.get(virtual_id);
        if (existing_file_id == null) {
            if (effective_io) |io| {
                const normalized_slice = self.interner.get(virtual_id);
                if (!std.mem.startsWith(u8, normalized_slice, "/cx/")) {
                    resolved_id = try self.resolvePath(io, normalized_slice);
                    if (self.path_to_file_id.get(resolved_id)) |canon_existing_id| {
                        try self.path_to_file_id.put(self.backing_allocator, virtual_id, canon_existing_id);
                        existing_file_id = canon_existing_id;
                    }
                }
            }
        }

        const new_owned_z = try self.backing_allocator.allocSentinel(u8, content_bytes.len, 0);
        @memcpy(new_owned_z, content_bytes);
        var is_new_owned_transferred = false;
        errdefer if (!is_new_owned_transferred) self.backing_allocator.free(new_owned_z);
        const digest = computeBlake3Hash(new_owned_z);

        // [1] Update an already-registered `FileId` (freeing prior `slot.owned_z` immediately on overwrite):
        if (existing_file_id) |existing_id| {
            if (self.overlay_cache.file_to_slot.get(existing_id)) |existing_slot_idx| {
                const entry = &self.entries.items[existing_id.asInt()];
                if (entry.line_index) |*existing_line_idx| {
                    existing_line_idx.deinit(self.backing_allocator);
                    entry.line_index = null;
                }
                if (entry.memory_map) |*existing_map| {
                    if (effective_io) |io| existing_map.destroy(io);
                    entry.memory_map = null;
                }
                if (entry.mapped_file) |existing_file| {
                    if (effective_io) |io| existing_file.close(io);
                    entry.mapped_file = null;
                }

                self.overlay_cache.detachSlot(existing_slot_idx);
                const slot = &self.overlay_cache.slots.items[existing_slot_idx];
                if (slot.owned_z) |prev_buf| {
                    self.overlay_cache.total_bytes -= prev_buf.len;
                    self.backing_allocator.free(prev_buf);
                }
                slot.owned_z = new_owned_z;
                self.overlay_cache.total_bytes += new_owned_z.len;
                is_new_owned_transferred = true;
                self.overlay_cache.attachHeadMru(existing_slot_idx, is_open_in_editor);

                entry.package_id = package_id;
                entry.content = new_owned_z;
                entry.content_hash = digest;
                entry.revision += 1;
                entry.backing_kind = .in_memory_overlay;
                entry.is_open_in_editor = is_open_in_editor;
                entry.is_blob_loaded = true;
                entry.has_blob_integrity_error = false;

                self.evictLeastRecentlyUsed(effective_io, existing_id);
                return existing_id;
            }

            if (self.overlay_cache.free_head == OVERLAY_SLOT_NONE) {
                try self.overlay_cache.slots.ensureUnusedCapacity(self.backing_allocator, 1);
            }
            try self.overlay_cache.file_to_slot.ensureUnusedCapacity(self.backing_allocator, 1);

            const entry = &self.entries.items[existing_id.asInt()];
            if (entry.line_index) |*existing_line_idx| {
                existing_line_idx.deinit(self.backing_allocator);
                entry.line_index = null;
            }
            if (entry.memory_map) |*existing_map| {
                if (effective_io) |io| existing_map.destroy(io);
                entry.memory_map = null;
            }
            if (entry.mapped_file) |existing_file| {
                if (effective_io) |io| existing_file.close(io);
                entry.mapped_file = null;
            }

            const slot_idx = self.overlay_cache.acquireSlotAssumeCapacity();
            self.overlay_cache.slots.items[slot_idx].file_id = existing_id;
            self.overlay_cache.slots.items[slot_idx].owned_z = new_owned_z;
            self.overlay_cache.file_to_slot.putAssumeCapacity(existing_id, slot_idx);
            self.overlay_cache.entry_count += 1;
            self.overlay_cache.total_bytes += new_owned_z.len;
            is_new_owned_transferred = true;
            self.overlay_cache.attachHeadMru(slot_idx, is_open_in_editor);

            entry.package_id = package_id;
            entry.content = new_owned_z;
            entry.content_hash = digest;
            entry.revision += 1;
            entry.backing_kind = .in_memory_overlay;
            entry.is_open_in_editor = is_open_in_editor;
            entry.is_blob_loaded = true;
            entry.has_blob_integrity_error = false;

            self.evictLeastRecentlyUsed(effective_io, existing_id);
            return existing_id;
        }

        // [2] Register a new `FileId` backed by `OverlayCache`:
        if (self.entries.items.len >= MAX_LOADED_FILES) return error.TooManyLoadedFiles;
        try self.entries.ensureUnusedCapacity(self.backing_allocator, 1);
        try self.path_to_file_id.ensureUnusedCapacity(
            self.backing_allocator,
            if (resolved_id != virtual_id) 2 else 1,
        );
        if (self.overlay_cache.free_head == OVERLAY_SLOT_NONE) {
            try self.overlay_cache.slots.ensureUnusedCapacity(self.backing_allocator, 1);
        }
        try self.overlay_cache.file_to_slot.ensureUnusedCapacity(self.backing_allocator, 1);

        const new_file_id = FileId.fromInt(@intCast(self.entries.items.len));
        self.entries.appendAssumeCapacity(.{
            .file_id = new_file_id,
            .package_id = package_id,
            .virtual_path = virtual_id,
            .resolved_os_path = resolved_id,
            .content = new_owned_z,
            .content_hash = digest,
            .revision = 1,
            .backing_kind = .in_memory_overlay,
            .is_open_in_editor = is_open_in_editor,
            .has_disk_backing = false,
        });
        self.path_to_file_id.putAssumeCapacity(virtual_id, new_file_id);
        if (resolved_id != virtual_id) {
            self.path_to_file_id.putAssumeCapacity(resolved_id, new_file_id);
        }

        const slot_idx = self.overlay_cache.acquireSlotAssumeCapacity();
        self.overlay_cache.slots.items[slot_idx].file_id = new_file_id;
        self.overlay_cache.slots.items[slot_idx].owned_z = new_owned_z;
        self.overlay_cache.file_to_slot.putAssumeCapacity(new_file_id, slot_idx);
        self.overlay_cache.entry_count += 1;
        self.overlay_cache.total_bytes += new_owned_z.len;
        is_new_owned_transferred = true;
        self.overlay_cache.attachHeadMru(slot_idx, is_open_in_editor);

        self.evictLeastRecentlyUsed(effective_io, new_file_id);
        return new_file_id;
    }

    /// Closes an editor overlay (`textDocument/didClose`), reverting to `.cxtree`/disk or demoting virtual buffers.
    pub fn closeOverlay(self: *VfsSourceMap, io: std.Io, file_id: FileId) !bool {
        self.last_io = io;
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return error.InvalidFileId;
        const entry = &self.entries.items[file_id.asInt()];

        if (entry.line_index) |*existing_line_idx| {
            existing_line_idx.deinit(self.backing_allocator);
            entry.line_index = null;
        }

        // [1] Restore `.cxtree_archive` entries to lazy demand-paged state and free overlay buffer:
        if (entry.blobs_dir_id != .empty and !entry.blobs_dir_id.isNone()) {
            if (self.overlay_cache.file_to_slot.get(file_id)) |slot_idx| {
                self.overlay_cache.removeAndFreeSlot(self.backing_allocator, slot_idx);
            }
            if (entry.memory_map) |*existing_map| {
                existing_map.destroy(io);
                entry.memory_map = null;
            }
            if (entry.mapped_file) |existing_file| {
                existing_file.close(io);
                entry.mapped_file = null;
            }
            entry.backing_kind = .cxtree_archive;
            entry.content = "";
            entry.content_hash = entry.cxtree_blob_hash;
            entry.is_blob_loaded = false;
            entry.has_blob_integrity_error = false;
            entry.is_open_in_editor = false;
            entry.revision += 1;
            return true;
        }

        // [2] Reload from host disk (`small_file_arena` `< 16 KiB` or `mmap` `>= 16 KiB`) when present:
        if (try self.tryReloadEntryFromDisk(io, entry)) {
            if (self.overlay_cache.file_to_slot.get(file_id)) |slot_idx| {
                self.overlay_cache.removeAndFreeSlot(self.backing_allocator, slot_idx);
            }
            return true;
        }

        // [3] Virtual-only buffer; retain `slot.owned_z` and demote to `closed_head_mru`:
        entry.has_disk_backing = false;
        entry.is_open_in_editor = false;
        if (self.overlay_cache.file_to_slot.get(file_id)) |slot_idx| {
            self.overlay_cache.detachSlot(slot_idx);
            self.overlay_cache.attachHeadMru(slot_idx, false);
        }
        return false;
    }

    /// Lazily mounts all files in `cxtree_bytes` under `/cx/<pkg_name>@<pkg_version>/<rel_path>` without host path leakage.
    pub fn mountCxTreePackage(
        self: *VfsSourceMap,
        io: std.Io,
        package_id: PackageId,
        pkg_name: []const u8,
        pkg_version: []const u8,
        cxtree_bytes: []const u8,
        blobs_root_dir: []const u8,
    ) ![]FileId {
        self.last_io = io;
        const tree_view = try validateCxTreeBytes(self.backing_allocator, cxtree_bytes);

        // [1] Lazily initialize or refresh the demand-paging context for `.cxtree` blobs:
        if (self.lazy_pager) |existing_pager| {
            existing_pager.io = io;
        } else {
            const created = try self.backing_allocator.create(LazyCxTreePager);
            created.* = .{
                .io = io,
                .backing_allocator = self.backing_allocator,
                .interner = self.interner,
                .blob_arena = BumpArena.init(self.backing_allocator),
            };
            self.lazy_pager = created;
        }

        const blobs_dir_id = try internNormalizedPath(self.backing_allocator, self.interner, blobs_root_dir);
        const mounted_ids = try self.backing_allocator.alloc(FileId, tree_view.entries.len);
        errdefer self.backing_allocator.free(mounted_ids);

        try self.entries.ensureUnusedCapacity(self.backing_allocator, tree_view.entries.len);
        try self.path_to_file_id.ensureUnusedCapacity(self.backing_allocator, @intCast(tree_view.entries.len));

        var path_buf: std.ArrayList(u8) = .empty;
        defer path_buf.deinit(self.backing_allocator);

        // [2] Pre-allocate deterministic unloaded `FileId` handles with `resolved_os_path = virtual_id`:
        for (tree_view.entries, 0..) |tree_entry, i| {
            const rel_path = tree_view.asEntryPath(tree_entry);
            path_buf.clearRetainingCapacity();
            try path_buf.ensureUnusedCapacity(
                self.backing_allocator,
                5 + pkg_name.len + pkg_version.len + rel_path.len,
            );
            path_buf.appendSliceAssumeCapacity("/cx/");
            path_buf.appendSliceAssumeCapacity(pkg_name);
            path_buf.appendAssumeCapacity('@');
            path_buf.appendSliceAssumeCapacity(pkg_version);
            path_buf.appendAssumeCapacity('/');
            path_buf.appendSliceAssumeCapacity(rel_path);

            const virtual_id = try self.interner.intern(path_buf.items);
            if (self.path_to_file_id.get(virtual_id)) |existing_id| {
                mounted_ids[i] = existing_id;
                continue;
            }
            if (self.entries.items.len >= MAX_LOADED_FILES) return error.TooManyLoadedFiles;

            const new_file_id = FileId.fromInt(@intCast(self.entries.items.len));
            self.entries.appendAssumeCapacity(.{
                .file_id = new_file_id,
                .package_id = package_id,
                .virtual_path = virtual_id,
                .resolved_os_path = virtual_id,
                .content = "",
                .content_hash = tree_entry.file_blake3,
                .revision = 1,
                .backing_kind = .cxtree_archive,
                .is_blob_loaded = false,
                .unloaded_blob_size = @intCast(tree_entry.file_size),
                .blobs_dir_id = blobs_dir_id,
                .cxtree_blob_hash = tree_entry.file_blake3,
            });
            self.path_to_file_id.putAssumeCapacity(virtual_id, new_file_id);
            mounted_ids[i] = new_file_id;
        }
        return mounted_ids;
    }

    /// Explicitly faults `file_id` from `blobs/`, returning `error.CacheIntegrityMismatch` (`E0015`) on tampering.
    pub fn faultCxTreeFile(self: *const VfsSourceMap, file_id: FileId) ![:0]const u8 {
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return error.InvalidFileId;
        const entry = &self.entries.items[file_id.asInt()];
        if (!entry.is_blob_loaded) {
            const pager = self.lazy_pager orelse return error.CacheIntegrityMismatch;
            try faultLazyEntryIfNeeded(pager, entry);
        } else if (entry.has_blob_integrity_error) {
            return error.CacheIntegrityMismatch;
        }
        return entry.content;
    }

    /// Resolves a `.cxtree` or overlay asset by virtual path without touching the host workspace filesystem.
    pub fn lookupCxTreeAsset(self: *const VfsSourceMap, virtual_path: []const u8) !?[:0]const u8 {
        var stack_buf: [512]u8 = undefined;
        const has_drive_prefix = virtual_path.len >= 2 and
            std.ascii.isAlphabetic(virtual_path[0]) and
            virtual_path[1] == ':';
        const normalized_slice = if (!(has_drive_prefix and std.ascii.isUpper(virtual_path[0])) and
            std.mem.indexOfScalar(u8, virtual_path, '\\') == null)
            virtual_path
        else blk: {
            if (virtual_path.len > stack_buf.len) return null;
            for (virtual_path, 0..) |ch_byte, i| {
                stack_buf[i] = if (ch_byte == '\\') '/' else ch_byte;
            }
            if (has_drive_prefix) {
                stack_buf[0] = std.ascii.toLower(stack_buf[0]);
            }
            break :blk stack_buf[0..virtual_path.len];
        };
        const lookup_id = self.interner.lookup(normalized_slice) orelse return null;
        const file_id = self.path_to_file_id.get(lookup_id) orelse return null;
        const entry = &self.entries.items[file_id.asInt()];
        if (entry.backing_kind != .cxtree_archive and entry.backing_kind != .in_memory_overlay) {
            return null;
        }
        return try self.faultCxTreeFile(file_id);
    }

    /// Returns the first `FileId` that failed lazy `BLAKE3` blob verification, or `null` if all reads were clean.
    pub fn hasIntegrityErrorFile(self: *const VfsSourceMap) ?FileId {
        if (self.lazy_pager) |pager| {
            if (!pager.first_integrity_error_file.isNone()) return pager.first_integrity_error_file;
        }
        return null;
    }

    /// Returns a read-only pointer to the `VfsFileEntry` for `file_id`, faulting lazy `.cxtree` blobs on first access.
    pub fn getFileEntry(self: *const VfsSourceMap, file_id: FileId) ?*const VfsFileEntry {
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return null;
        const entry = &self.entries.items[file_id.asInt()];
        if (!entry.is_blob_loaded) {
            const pager = self.lazy_pager orelse return null;
            faultLazyEntryIfNeeded(pager, entry) catch return null;
        }
        if (entry.has_blob_integrity_error) return null;
        return entry;
    }

    /// Returns the normalized virtual path string for `file_id`, or `""` if `file_id` is invalid.
    pub fn getFilePath(self: *const VfsSourceMap, file_id: FileId) []const u8 {
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return "";
        return self.interner.get(self.entries.items[file_id.asInt()].virtual_path);
    }

    /// Returns the NUL-terminated UTF-8 source buffer for `file_id`, or `null` if invalid or corrupt.
    pub fn getFileSource(self: *const VfsSourceMap, file_id: FileId) ?[:0]const u8 {
        if (self.getFileEntry(file_id)) |entry| {
            return entry.content;
        }
        return null;
    }

    /// Returns the cached `LineIndex` for `file_id`, faulting any unloaded `.cxtree` blob and building lazily.
    pub fn getLineIndex(self: *VfsSourceMap, file_id: FileId) !*const LineIndex {
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return error.InvalidFileId;
        const entry = &self.entries.items[file_id.asInt()];
        if (!entry.is_blob_loaded) {
            const pager = self.lazy_pager orelse return error.CacheIntegrityMismatch;
            try faultLazyEntryIfNeeded(pager, entry);
        } else if (entry.has_blob_integrity_error) {
            return error.CacheIntegrityMismatch;
        }
        if (entry.line_index == null) {
            entry.line_index = try LineIndex.build(self.backing_allocator, entry.content);
        }
        return &entry.line_index.?;
    }

    /// Returns the total number of files currently registered in `VfsSourceMap`.
    pub inline fn countFiles(self: *const VfsSourceMap) usize {
        return self.entries.items.len;
    }
};

/// Canonical alias for `VfsSourceMap`.
pub const SourceMap = VfsSourceMap;

// ------------------------- Unit Tests -------------------------

test "test_line_index_lf_crlf_and_utf8_utf16_columns" {
    const source_text = "let a = 1;\r\nlet café = \"𐍈\";\nreturn a;";
    var line_index = try LineIndex.build(std.testing.allocator, source_text);
    defer line_index.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(u32, 3), line_index.countLines());
    try std.testing.expectEqualStrings("let a = 1;", line_index.getLineSlice(source_text, 1));
    try std.testing.expectEqualStrings("let café = \"𐍈\";", line_index.getLineSlice(source_text, 2));
    try std.testing.expectEqualStrings("return a;", line_index.getLineSlice(source_text, 3));

    // Querying on `\r` vs `\n` at the end of line 1 must yield identical column metrics:
    const col_at_cr = line_index.resolveLineCol(source_text, 10);
    const col_at_lf = line_index.resolveLineCol(source_text, 11);
    try std.testing.expectEqual(@as(u32, 1), col_at_cr.line);
    try std.testing.expectEqual(col_at_cr.col_utf8, col_at_lf.col_utf8);
    try std.testing.expectEqual(col_at_cr.col_utf16_0, col_at_lf.col_utf16_0);

    // Line 2: `"let café = \"𐍈\";"` -> `'é'` is 2 bytes (1 UTF-16 unit), `'𐍈'` is 4 bytes (2 UTF-16 units):
    const after_astral = line_index.resolveLineCol(source_text, 12 + 17);
    try std.testing.expectEqual(@as(u32, 2), after_astral.line);
    try std.testing.expectEqual(@as(u32, 14), after_astral.col_utf8);
    try std.testing.expectEqual(@as(u32, 14), after_astral.col_utf16_0);
}

test "test_vfs_sourcemap_overlay_revision_and_nul_sentinel" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var vfs = VfsSourceMap.init(std.testing.allocator, &interner);
    defer vfs.deinit(std.testing.io);

    const file_id = try vfs.setOverlay("src\\net\\socket.cx", "fn connect() {}\n", .root);
    try std.testing.expectEqual(@as(usize, 1), vfs.countFiles());
    try std.testing.expectEqualStrings("src/net/socket.cx", vfs.getFilePath(file_id));

    const source_slice = vfs.getFileSource(file_id).?;
    try std.testing.expectEqual(@as(u8, 0), source_slice[source_slice.len]);

    try std.testing.expectEqual(
        file_id,
        try vfs.setOverlay("src/net/socket.cx", "fn connect() {}\nfn close() {}\n", .root),
    );
    try std.testing.expectEqual(@as(u32, 2), vfs.getFileEntry(file_id).?.revision);
    try std.testing.expectEqual(@as(u32, 3), (try vfs.getLineIndex(file_id)).countLines());
}

test "test_line_index_resolve_byte_offset_ascii_utf8_utf16_and_malformed" {
    const source_text = "let a = 1;\r\nlet café = \"𐍈\";\nreturn a;";
    var line_index = try LineIndex.build(std.testing.allocator, source_text);
    defer line_index.deinit(std.testing.allocator);

    // [1] Pure-ASCII line 0 (`"let a = 1;"`, bytes `0..10` followed by `\r\n` at `10..12`):
    try std.testing.expectEqual(@as(u32, 0), line_index.resolveByteOffset(source_text, 0, 0, .utf16));
    try std.testing.expectEqual(@as(u32, 4), line_index.resolveByteOffset(source_text, 0, 4, .utf8));
    try std.testing.expectEqual(@as(u32, 10), line_index.resolveByteOffset(source_text, 0, 10, .utf16));
    try std.testing.expectEqual(@as(u32, 10), line_index.resolveByteOffset(source_text, 0, 99, .utf8));
    try std.testing.expectEqual(
        @as(u32, 10),
        line_index.resolveByteOffset(source_text, 0, std.math.maxInt(u32), .utf16),
    );
    try std.testing.expectEqual(
        @as(u32, 10),
        line_index.resolveByteOffset(source_text, 0, std.math.maxInt(u32), .utf8),
    );
    try std.testing.expectEqual(
        @as(u32, @intCast(source_text.len)),
        line_index.resolveByteOffset(source_text, 99, 0, .utf16),
    );

    // [2] Non-ASCII line 1 (`"let café = \"𐍈\";"`, starts at byte `12`):
    // `'é'` (`0xC3 0xA9`) spans line-local bytes `7..9`; `'𐍈'` (`4` bytes, `2` UTF-16 units) spans `13..17`:
    const post_astral_col = line_index.resolveLineCol(source_text, 12 + 17);
    try std.testing.expectEqual(@as(u32, 14), LineIndex.extractLspCharacter0(post_astral_col, .utf16));
    try std.testing.expectEqual(@as(u32, 17), LineIndex.extractLspCharacter0(post_astral_col, .utf8));

    // `.utf8` mid-scalar continuation bytes floor to the scalar's leading byte:
    try std.testing.expectEqual(@as(u32, 12 + 7), line_index.resolveByteOffset(source_text, 1, 7, .utf8));
    try std.testing.expectEqual(@as(u32, 12 + 7), line_index.resolveByteOffset(source_text, 1, 8, .utf8));
    try std.testing.expectEqual(@as(u32, 12 + 13), line_index.resolveByteOffset(source_text, 1, 13, .utf8));
    try std.testing.expectEqual(@as(u32, 12 + 13), line_index.resolveByteOffset(source_text, 1, 14, .utf8));
    try std.testing.expectEqual(@as(u32, 12 + 13), line_index.resolveByteOffset(source_text, 1, 15, .utf8));
    try std.testing.expectEqual(@as(u32, 12 + 13), line_index.resolveByteOffset(source_text, 1, 16, .utf8));
    try std.testing.expectEqual(@as(u32, 12 + 17), line_index.resolveByteOffset(source_text, 1, 17, .utf8));
    try std.testing.expectEqual(
        @as(u32, 12 + 19),
        line_index.resolveByteOffset(source_text, 1, std.math.maxInt(u32), .utf8),
    );

    // `.utf16` mid-surrogate offset (`character_0 == 13`, inside `'𐍈'` at UTF-16 `12..14`) floors to `12 + 13`:
    try std.testing.expectEqual(@as(u32, 12 + 13), line_index.resolveByteOffset(source_text, 1, 12, .utf16));
    try std.testing.expectEqual(@as(u32, 12 + 13), line_index.resolveByteOffset(source_text, 1, 13, .utf16));
    try std.testing.expectEqual(@as(u32, 12 + 17), line_index.resolveByteOffset(source_text, 1, 14, .utf16));
    try std.testing.expectEqual(
        @as(u32, 12 + 19),
        line_index.resolveByteOffset(source_text, 1, std.math.maxInt(u32), .utf16),
    );

    // [3] Malformed & truncated UTF-8 sequences round-trip 1-to-1 with `resolveLineCol`:
    const malformed = "a\x80\x80\xED\xA0\x80\xF0\x90\nb";
    var bad_index = try LineIndex.build(std.testing.allocator, malformed);
    defer bad_index.deinit(std.testing.allocator);

    var byte_i: u32 = 0;
    while (byte_i <= 8) : (byte_i += 1) {
        const resolved_col = bad_index.resolveLineCol(malformed, byte_i);
        try std.testing.expectEqual(
            byte_i,
            bad_index.resolveByteOffset(
                malformed,
                0,
                LineIndex.extractLspCharacter0(resolved_col, .utf8),
                .utf8,
            ),
        );
        try std.testing.expectEqual(
            byte_i,
            bad_index.resolveByteOffset(
                malformed,
                0,
                LineIndex.extractLspCharacter0(resolved_col, .utf16),
                .utf16,
            ),
        );
    }
}

test "test_vfs_drive_canonicalization_and_dual_bounded_overlay_cache" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var vfs = VfsSourceMap.init(std.testing.allocator, &interner);
    defer vfs.deinit(std.testing.io);
    vfs.setIo(std.testing.io);

    // [1] Windows drive-letter canonicalization (`"D:\\…"` vs `"d:/…"`):
    const win_id = try vfs.setOverlay("D:\\Repo\\src\\main.cx", "fn alpha() {}\n", .root);
    try std.testing.expectEqual(win_id, try vfs.setOverlay("d:/Repo/src/main.cx", "fn beta() {}\n", .root));
    try std.testing.expectEqualStrings("d:/Repo/src/main.cx", vfs.getFilePath(win_id));
    try std.testing.expectEqualStrings(
        "fn beta() {}\n",
        (try vfs.lookupCxTreeAsset("D:\\Repo\\src\\main.cx")).?,
    );

    // Virtual-only `closeOverlay` returns `false`, retains content, and demotes slot to `closed_*`:
    try std.testing.expect(!(try vfs.closeOverlay(std.testing.io, win_id)));
    try std.testing.expect(!vfs.getFileEntry(win_id).?.is_open_in_editor);
    try std.testing.expectEqualStrings("fn beta() {}\n", vfs.getFileSource(win_id).?);
    try std.testing.expectEqual(@as(usize, 1), vfs.overlay_cache.entry_count);

    // [2] Disk-backed files (`< 16 KiB` arena & `>= 16 KiB` mmap) revert on `closeOverlay` and free overlay slot:
    const small_disk_id = try vfs.resolveOrCreatePath(std.testing.io, ".agents/AGENTS.md", .root);
    const orig_small_hash = vfs.getFileEntry(small_disk_id).?.content_hash;
    _ = try vfs.setEditorOverlay(std.testing.io, ".agents/AGENTS.md", "// unsaved edit\n", .root, true);
    try std.testing.expectEqualStrings("// unsaved edit\n", vfs.getFileSource(small_disk_id).?);
    try std.testing.expect(try vfs.closeOverlay(std.testing.io, small_disk_id));
    try std.testing.expectEqual(orig_small_hash, vfs.getFileEntry(small_disk_id).?.content_hash);
    try std.testing.expect(!vfs.overlay_cache.file_to_slot.contains(small_disk_id));

    const large_disk_id = try vfs.resolveOrCreatePath(std.testing.io, "build.zig", .root);
    const orig_large_hash = vfs.getFileEntry(large_disk_id).?.content_hash;
    _ = try vfs.setEditorOverlay(std.testing.io, "build.zig", "// temporary build overlay\n", .root, true);
    try std.testing.expect(try vfs.closeOverlay(std.testing.io, large_disk_id));
    try std.testing.expectEqual(orig_large_hash, vfs.getFileEntry(large_disk_id).?.content_hash);

    // [3] `256`-entry LRU eviction (`closed_tail_lru` strictly before `open_tail_lru`) with zero-UAF reset:
    var open_ids: [MAX_OPEN_OVERLAYS + 2]FileId = undefined;
    var idx: usize = 0;
    while (idx < open_ids.len) : (idx += 1) {
        var path_buf: [64]u8 = undefined;
        const vpath = try std.fmt.bufPrint(&path_buf, "virtual/open_{d}.cx", .{idx});
        open_ids[idx] = try vfs.setEditorOverlay(null, vpath, "let val = 1;\n", .root, true);
    }
    try std.testing.expectEqual(MAX_OPEN_OVERLAYS, vfs.overlay_cache.entry_count);
    // `win_id` (closed virtual), `open_ids[0]`, and `open_ids[1]` (`259 - 256 = 3` oldest) must be evicted:
    try std.testing.expectEqualStrings("", vfs.getFileSource(win_id).?);
    try std.testing.expectEqualStrings("", vfs.getFileSource(open_ids[0]).?);
    try std.testing.expectEqualStrings("", vfs.getFileSource(open_ids[1]).?);
    try std.testing.expectEqualStrings("let val = 1;\n", vfs.getFileSource(open_ids[2]).?);
    try std.testing.expectEqualStrings("let val = 1;\n", vfs.getFileSource(open_ids[open_ids.len - 1]).?);

    // [4] `64 MiB` byte-cap eviction & Self-Overwrite UAF Guard (`24 MiB` -> `44 MiB` self-overwrite):
    var byte_vfs = VfsSourceMap.init(std.testing.allocator, &interner);
    defer byte_vfs.deinit(std.testing.io);

    const chunk_24m = try std.testing.allocator.alloc(u8, 24 * 1024 * 1024);
    defer std.testing.allocator.free(chunk_24m);
    @memset(chunk_24m, 'a');

    const chunk_44m = try std.testing.allocator.alloc(u8, 44 * 1024 * 1024);
    defer std.testing.allocator.free(chunk_44m);
    @memset(chunk_44m, 'b');

    const first_big_id = try byte_vfs.setEditorOverlay(null, "virtual/big_a.cx", chunk_24m, .root, true);
    const second_big_id = try byte_vfs.setEditorOverlay(null, "virtual/big_b.cx", chunk_24m, .root, true);
    try std.testing.expectEqual(@as(usize, 48 * 1024 * 1024), byte_vfs.overlay_cache.total_bytes);

    // Overwriting `second_big_id` from `24 MiB` to `44 MiB` (`68 MiB` combined) must evict `first_big_id`
    // while keeping `second_big_id` pinned and intact (`total_bytes == 44 MiB`):
    _ = try byte_vfs.setEditorOverlay(null, "virtual/big_b.cx", chunk_44m, .root, true);
    try std.testing.expectEqual(@as(usize, 1), byte_vfs.overlay_cache.entry_count);
    try std.testing.expectEqual(@as(usize, 44 * 1024 * 1024), byte_vfs.overlay_cache.total_bytes);
    try std.testing.expectEqualStrings("", byte_vfs.getFileSource(first_big_id).?);
    try std.testing.expectEqual(@as(usize, 44 * 1024 * 1024), byte_vfs.getFileSource(second_big_id).?.len);
    try std.testing.expectEqual(@as(u8, 'b'), byte_vfs.getFileSource(second_big_id).?[0]);
}

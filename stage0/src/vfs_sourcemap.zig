//! Virtual File System, `.cxtree` Binary Headers & Line/Column SourceMap
//!
//! Implements the content-addressable `VfsSourceMap` (`SourceMap`), `.cxtree` binary manifest records,
//! and $O(\log L)$ `LineIndex` resolver supporting `LF`/`CRLF` line endings and UTF-8/UTF-16 columns.
//!
//! Files `< 16 KiB` (or exact 4096-byte page multiples) are loaded into `BumpArena` with an explicit
//! trailing NUL byte (`0x00`), while larger non-page-multiple files use read-only OS memory mapping.

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
    /// In-memory virtual buffer or unsaved LSP editor overlay in `small_file_arena`.
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
    /// `true` once `content` holds verified file bytes (`false` for newly mounted lazy `.cxtree` entries).
    is_blob_loaded: bool = true,
    /// `true` if lazy blob faulting failed `BLAKE3` content verification (`E0015`).
    has_blob_integrity_error: bool = false,
    /// Uncompressed byte length expected when faulting an unloaded `.cxtree` blob.
    unloaded_blob_size: u32 = 0,
    /// Interned host `blobs/` directory path used strictly for internal lazy faulting (never exposed).
    blobs_dir_id: StringId = .empty,
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
/// Standard OS virtual memory page granularity (`4096` bytes) used for `mmap` sentinel checks.
const OS_PAGE_SIZE: usize = 4096;

// -------------------------------------- INTERNALS --------------------------------------

/// Normalizes backslashes (`\`) to forward slashes (`/`) and interns the resulting path.
fn internNormalizedPath(
    allocator: std.mem.Allocator,
    interner: *StringInterner,
    raw_path: []const u8,
) !StringId {
    if (std.mem.indexOfScalar(u8, raw_path, '\\') == null) {
        return interner.intern(raw_path);
    }
    const normalized_buf = try allocator.alloc(u8, raw_path.len);
    defer allocator.free(normalized_buf);
    for (raw_path, 0..) |path_byte, i| {
        normalized_buf[i] = if (path_byte == '\\') '/' else path_byte;
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
    const bytes_read = opened_file.readPositionalAll(pager.io, arena_buf[0..file_size], 0) catch {
        return markLazyIntegrityFailure(pager, entry);
    };
    if (bytes_read != file_size) {
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
            const gop = seen_lower_paths.getOrPutAssumeCapacity(lower_copy);
            if (gop.found_existing) return error.DuplicateOrCaseCollidingCxTreePath;
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
        const cand_path = view.asEntryPath(candidate);
        switch (std.mem.order(u8, cand_path, rel_path)) {
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
};

// ---------------- VFS SourceMap Implementation ----------------

/// Virtual File System and SourceMap managing `< 16 KiB` arena buffers, `>= 16 KiB` `mmap`s, and overlays.
pub const VfsSourceMap = struct {
    /// Backing allocator for metadata arrays, `LineIndex` tables, and path normalization.
    backing_allocator: std.mem.Allocator,
    /// Shared string interner used to intern virtual and resolved OS file paths.
    interner: *StringInterner,
    /// Dedicated bump arena storing `< 16 KiB` file contents and in-memory overlays with NUL sentinels.
    small_file_arena: BumpArena,
    /// Contiguous table of loaded `VfsFileEntry` records indexed by `FileId.asInt()`.
    entries: std.ArrayList(VfsFileEntry) = .empty,
    /// $O(1)$ lookup map from interned normalized/resolved path `StringId` to `FileId`.
    path_to_file_id: std.AutoHashMapUnmanaged(StringId, FileId) = .empty,
    /// Optional heap-allocated demand pager for lazily mounted `.cxtree` package blobs.
    lazy_pager: ?*LazyCxTreePager = null,

    /// Initializes an empty `VfsSourceMap` bound to `backing_allocator` and `interner`.
    pub fn init(backing_allocator: std.mem.Allocator, interner: *StringInterner) VfsSourceMap {
        return .{
            .backing_allocator = backing_allocator,
            .interner = interner,
            .small_file_arena = BumpArena.init(backing_allocator),
        };
    }

    /// Releases all `LineIndex` instances, unmaps any `MemoryMap` regions, closes files, and frees arenas.
    pub fn deinit(self: *VfsSourceMap, io: std.Io) void {
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

        // [2] Open and stat file on disk using the normalized `/` path, enforcing `MAX_SOURCE_FILE_BYTES`:
        const opened_file = try std.Io.Dir.cwd().openFile(io, self.interner.get(virtual_id), .{
            .mode = .read_only,
            .allow_directory = false,
        });
        errdefer opened_file.close(io);

        const file_stat = try opened_file.stat(io);
        if (file_stat.kind == .directory) return error.IsDir;
        if (file_stat.size > MAX_SOURCE_FILE_BYTES or file_stat.size > std.math.maxInt(u32)) {
            return error.FileTooLarge;
        }
        const file_size: usize = @intCast(file_stat.size);
        const new_file_id = FileId.fromInt(@intCast(self.entries.items.len));
        try self.entries.ensureUnusedCapacity(self.backing_allocator, 1);
        try self.path_to_file_id.ensureUnusedCapacity(self.backing_allocator, 2);

        // [3] Attempt zero-copy OS `mmap` for `>= 16 KiB` files not landing on a 4096-byte page boundary:
        if (file_size >= SMALL_FILE_THRESHOLD and (file_size % OS_PAGE_SIZE) != 0) {
            if (opened_file.createMemoryMap(io, .{
                .len = file_size,
                .protection = .{ .read = true, .write = false },
                .populate = true,
                .offset = 0,
            })) |memory_map| {
                const raw_mapped_ptr: [*]const u8 = @ptrCast(memory_map.memory.ptr);
                if (memory_map.section != null and raw_mapped_ptr[file_size] == 0) {
                    const mapped_content: [:0]const u8 = raw_mapped_ptr[0..file_size :0];
                    self.entries.appendAssumeCapacity(.{
                        .file_id = new_file_id,
                        .package_id = package_id,
                        .virtual_path = virtual_id,
                        .resolved_os_path = resolved_id,
                        .content = mapped_content,
                        .content_hash = computeBlake3Hash(mapped_content),
                        .revision = 1,
                        .backing_kind = .mmap_large,
                        .memory_map = memory_map,
                        .mapped_file = opened_file,
                    });
                    self.path_to_file_id.putAssumeCapacity(virtual_id, new_file_id);
                    self.path_to_file_id.putAssumeCapacity(resolved_id, new_file_id);
                    return new_file_id;
                }
                var cleanup_map = memory_map;
                cleanup_map.destroy(io);
            } else |_| {}
        }

        // [4] Read `< 16 KiB`, page-boundary, or fallback files into `small_file_arena` with NUL sentinel:
        const arena_buf = try self.small_file_arena.allocSlice(u8, file_size + 1);
        if ((try opened_file.readPositionalAll(io, arena_buf[0..file_size], 0)) != file_size) {
            return error.UnexpectedEndOfFile;
        }
        arena_buf[file_size] = 0;
        opened_file.close(io);

        const arena_content: [:0]const u8 = arena_buf[0..file_size :0];
        self.entries.appendAssumeCapacity(.{
            .file_id = new_file_id,
            .package_id = package_id,
            .virtual_path = virtual_id,
            .resolved_os_path = resolved_id,
            .content = arena_content,
            .content_hash = computeBlake3Hash(arena_content),
            .revision = 1,
            .backing_kind = .arena_small,
        });
        self.path_to_file_id.putAssumeCapacity(virtual_id, new_file_id);
        self.path_to_file_id.putAssumeCapacity(resolved_id, new_file_id);
        return new_file_id;
    }

    /// Inserts or updates an in-memory file overlay (`LSP` unsaved buffer or virtual test file).
    pub fn setOverlay(
        self: *VfsSourceMap,
        virtual_path: []const u8,
        content_bytes: []const u8,
        package_id: PackageId,
    ) !FileId {
        if (content_bytes.len > MAX_SOURCE_FILE_BYTES or content_bytes.len > std.math.maxInt(u32)) {
            return error.FileTooLarge;
        }

        const virtual_id = try internNormalizedPath(self.backing_allocator, self.interner, virtual_path);
        const owned_content = try self.small_file_arena.dupeZ(content_bytes);
        const digest = computeBlake3Hash(owned_content);

        if (self.path_to_file_id.get(virtual_id)) |existing_id| {
            const entry = &self.entries.items[existing_id.asInt()];
            if (entry.line_index) |*existing_line_idx| {
                existing_line_idx.deinit(self.backing_allocator);
                entry.line_index = null;
            }
            if (entry.memory_map) |*existing_map| {
                if (self.lazy_pager) |pager| existing_map.destroy(pager.io);
                entry.memory_map = null;
            }
            if (entry.mapped_file) |existing_file| {
                if (self.lazy_pager) |pager| existing_file.close(pager.io);
                entry.mapped_file = null;
            }
            entry.package_id = package_id;
            entry.content = owned_content;
            entry.content_hash = digest;
            entry.revision += 1;
            entry.backing_kind = .in_memory_overlay;
            entry.is_blob_loaded = true;
            entry.has_blob_integrity_error = false;
            return existing_id;
        }

        if (self.entries.items.len >= MAX_LOADED_FILES) return error.TooManyLoadedFiles;
        const new_file_id = FileId.fromInt(@intCast(self.entries.items.len));
        try self.entries.append(self.backing_allocator, .{
            .file_id = new_file_id,
            .package_id = package_id,
            .virtual_path = virtual_id,
            .resolved_os_path = virtual_id,
            .content = owned_content,
            .content_hash = digest,
            .revision = 1,
            .backing_kind = .in_memory_overlay,
        });
        try self.path_to_file_id.put(self.backing_allocator, virtual_id, new_file_id);
        return new_file_id;
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
        const normalized_slice = if (std.mem.indexOfScalar(u8, virtual_path, '\\') == null)
            virtual_path
        else blk: {
            if (virtual_path.len > stack_buf.len) return null;
            for (virtual_path, 0..) |ch_byte, i| {
                stack_buf[i] = if (ch_byte == '\\') '/' else ch_byte;
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

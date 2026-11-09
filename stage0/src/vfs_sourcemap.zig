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

/// 32-byte binary header of a content-addressable `.cxtree` package manifest (`DR-11` §2.4).
pub const CxTreeHeader = extern struct {
    /// Four-byte file magic signature (`"CXTR"`).
    magic: [4]u8 = CXTREE_MAGIC,
    /// Format version number (`1`).
    version: u32 = CXTREE_VERSION,
    /// Number of `CxTreeEntry` records immediately following this header.
    entry_count: u32,
    /// Total byte length of the trailing UTF-8 relative-path string table.
    string_table_bytes: u32,
    /// Byte offset of the package name inside the string table.
    pkg_name_str_off: u32,
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

comptime {
    std.debug.assert(@sizeOf(PackageId) == 2);
    std.debug.assert(@sizeOf(CxTreeHeader) == 32);
    std.debug.assert(@sizeOf(CxTreeEntry) == 48);
    std.debug.assert(@alignOf(CxTreeHeader) == 4);
    std.debug.assert(@alignOf(CxTreeEntry) == 8);
}

// ------------------------------------- PUBLIC API --------------------------------------

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

        const real_os_path = std.Io.Dir.cwd().realPathFileAlloc(io, raw_path, self.backing_allocator) catch {
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

        const resolved_id = try self.resolvePath(io, raw_path);
        if (self.path_to_file_id.get(resolved_id)) |existing_id| {
            try self.path_to_file_id.put(self.backing_allocator, virtual_id, existing_id);
            return existing_id;
        }

        if (self.entries.items.len >= MAX_LOADED_FILES) return error.TooManyLoadedFiles;

        // [2] Open and stat file on disk, enforcing `MAX_SOURCE_FILE_BYTES`:
        const opened_file = try std.Io.Dir.cwd().openFile(io, raw_path, .{
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
            entry.package_id = package_id;
            entry.content = owned_content;
            entry.content_hash = digest;
            entry.revision += 1;
            entry.backing_kind = .in_memory_overlay;
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

    /// Returns a read-only pointer to the `VfsFileEntry` for `file_id`, or `null` if invalid.
    pub fn getFileEntry(self: *const VfsSourceMap, file_id: FileId) ?*const VfsFileEntry {
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return null;
        return &self.entries.items[file_id.asInt()];
    }

    /// Returns the normalized virtual path string for `file_id`, or `""` if `file_id` is invalid.
    pub fn getFilePath(self: *const VfsSourceMap, file_id: FileId) []const u8 {
        if (self.getFileEntry(file_id)) |entry| {
            return self.interner.get(entry.virtual_path);
        }
        return "";
    }

    /// Returns the NUL-terminated UTF-8 source buffer for `file_id`, or `null` if invalid.
    pub fn getFileSource(self: *const VfsSourceMap, file_id: FileId) ?[:0]const u8 {
        if (self.getFileEntry(file_id)) |entry| {
            return entry.content;
        }
        return null;
    }

    /// Returns the cached `LineIndex` for `file_id`, building it lazily on first request.
    pub fn getLineIndex(self: *VfsSourceMap, file_id: FileId) !*const LineIndex {
        if (file_id.isNone() or file_id.asInt() >= self.entries.items.len) return error.InvalidFileId;
        const entry = &self.entries.items[file_id.asInt()];
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

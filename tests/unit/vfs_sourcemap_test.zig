//! Unit Tests for Virtual File System & SourceMap (`tests/unit/vfs_sourcemap_test.zig`)
//!
//! Verifies `PackageId`, `.cxtree` binary manifest headers, `LineIndex` $O(\log L)$ coordinate lookup
//! across `LF`/`CRLF` and UTF-8/UTF-16 encodings, and `VfsSourceMap` disk/overlay file management.
//!
//! Exercises both `< 16 KiB` arena-backed files and `>= 16 KiB` OS memory-mapped files with NUL sentinels.

const std = @import("std");
const corex = @import("corex");

const vfs = corex.vfs_sourcemap;
const FileId = corex.FileId;
const PackageId = corex.PackageId;
const LineIndex = corex.LineIndex;
const VfsSourceMap = corex.VfsSourceMap;
const StringInterner = corex.StringInterner;

// ------------------------------------- PUBLIC API --------------------------------------

// --------------- Package & CxTree Header Tests ----------------

test "test_package_id_and_cxtree_binary_header_layout" {
    try std.testing.expectEqual(@as(usize, 2), @sizeOf(PackageId));
    try std.testing.expectEqual(@as(usize, 32), @sizeOf(vfs.CxTreeHeader));
    try std.testing.expectEqual(@as(usize, 48), @sizeOf(vfs.CxTreeEntry));

    try std.testing.expectEqual(PackageId.root, PackageId.root_workspace);
    try std.testing.expectEqual(PackageId.std_core, PackageId.std_lib);
    try std.testing.expectEqual(@as(u16, 0), PackageId.root.asInt());
    try std.testing.expectEqual(@as(u16, 1), PackageId.std_core.asInt());
    try std.testing.expect(PackageId.none.isNone());
    try std.testing.expect(!PackageId.fromInt(5).isNone());
    try std.testing.expectEqual(@as(u16, 5), PackageId.fromInt(5).asInt());

    const header = vfs.CxTreeHeader{
        .entry_count = 4,
        .string_table_bytes = 64,
        .pkg_name_str_off = 0,
    };
    try std.testing.expectEqualSlices(u8, "CXTR", &header.magic);
    try std.testing.expectEqual(@as(u32, 1), header.version);
}

// ---------------------- LineIndex Tests -----------------------

test "test_line_index_empty_lf_crlf_and_out_of_bounds_queries" {
    // [1] Empty source buffer must have 1 empty line:
    var empty_index = try LineIndex.build(std.testing.allocator, "");
    defer empty_index.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(u32, 1), empty_index.countLines());
    try std.testing.expectEqualStrings("", empty_index.getLineSlice("", 1));
    try std.testing.expectEqualStrings("", empty_index.getLineSlice("", 0));
    try std.testing.expectEqualStrings("", empty_index.getLineSlice("", 2));

    const empty_loc = empty_index.resolveLineCol("", 99);
    try std.testing.expectEqual(@as(u32, 1), empty_loc.line);
    try std.testing.expectEqual(@as(u32, 1), empty_loc.col_utf8);
    try std.testing.expectEqual(@as(u32, 0), empty_loc.col_utf16_0);

    // [2] Mixed `CRLF` and `LF` line endings:
    const mixed_src = "first\r\nsecond\nthird\r\n";
    var mixed_index = try LineIndex.build(std.testing.allocator, mixed_src);
    defer mixed_index.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(u32, 4), mixed_index.countLines());
    try std.testing.expectEqualStrings("first", mixed_index.getLineSlice(mixed_src, 1));
    try std.testing.expectEqualStrings("second", mixed_index.getLineSlice(mixed_src, 2));
    try std.testing.expectEqualStrings("third", mixed_index.getLineSlice(mixed_src, 3));
    try std.testing.expectEqualStrings("", mixed_index.getLineSlice(mixed_src, 4));

    // Querying at `\r` (offset 5) and `\n` (offset 6) on line 1 must clamp to end of `"first"`:
    const loc_cr = mixed_index.resolveLineCol(mixed_src, 5);
    const loc_lf = mixed_index.resolveLineCol(mixed_src, 6);
    try std.testing.expectEqual(@as(u32, 1), loc_cr.line);
    try std.testing.expectEqual(@as(u32, 6), loc_cr.col_utf8);
    try std.testing.expectEqual(loc_cr.col_utf8, loc_lf.col_utf8);
    try std.testing.expectEqual(loc_cr.col_utf16_0, loc_lf.col_utf16_0);
}

test "test_line_index_utf8_astral_utf16_surrogates_and_malformed_bytes" {
    // Line 1 has 2-byte `é`, 3-byte `─`, and 4-byte `𐍈` (`U+10348`, 2 UTF-16 surrogate units):
    // Line 2 has invalid UTF-8 bytes (`0xFF`, `0xC3`) that must not panic during column resolution:
    const source_bytes = "aé─𐍈z\n" ++ [_]u8{ 'x', 0xFF, 0xC3, 'y', '\n' };
    var line_index = try LineIndex.build(std.testing.allocator, source_bytes);
    defer line_index.deinit(std.testing.allocator);

    try std.testing.expectEqual(@as(u32, 3), line_index.countLines());

    // Offset of `'z'` on line 1: `'a'` (1B) + `'é'` (2B) + `'─'` (3B) + `'𐍈'` (4B) = byte 10:
    const loc_at_z = line_index.resolveLineCol(source_bytes, 10);
    try std.testing.expectEqual(@as(u32, 1), loc_at_z.line);
    try std.testing.expectEqual(@as(u32, 5), loc_at_z.col_utf8);
    try std.testing.expectEqual(@as(u32, 5), loc_at_z.col_utf16_0);
    try std.testing.expectEqual(@as(u32, 11), loc_at_z.col_byte);

    // Offset of `'y'` on line 2 (after `'x'`, `0xFF`, `0xC3` -> byte 12 + 3 = 15):
    const loc_at_y = line_index.resolveLineCol(source_bytes, 15);
    try std.testing.expectEqual(@as(u32, 2), loc_at_y.line);
    try std.testing.expectEqual(@as(u32, 4), loc_at_y.col_utf8);
    try std.testing.expectEqual(@as(u32, 4), loc_at_y.col_byte);
}

// --------------------- VfsSourceMap Tests ---------------------

test "test_vfs_sourcemap_overlay_lifecycle_and_invalid_ids" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    // [1] Invalid `FileId` queries must fail gracefully without panicking:
    try std.testing.expect(source_map.getFileEntry(.none) == null);
    try std.testing.expect(source_map.getFileEntry(FileId.fromInt(42)) == null);
    try std.testing.expectEqualStrings("", source_map.getFilePath(.none));
    try std.testing.expect(source_map.getFileSource(.none) == null);
    try std.testing.expectError(error.InvalidFileId, source_map.getLineIndex(.none));

    // [2] Register overlay with Windows path separators and verify normalization + NUL sentinel:
    const file_id = try source_map.setOverlay("src\\core\\math.cx", "pub fn add(a: i32, b: i32) -> i32 { a + b }\n", .root);
    try std.testing.expectEqual(@as(usize, 1), source_map.countFiles());
    try std.testing.expectEqualStrings("src/core/math.cx", source_map.getFilePath(file_id));

    const first_entry = source_map.getFileEntry(file_id).?;
    try std.testing.expectEqual(@as(u32, 1), first_entry.revision);
    try std.testing.expectEqual(vfs.BackingKind.in_memory_overlay, first_entry.backing_kind);
    try std.testing.expectEqual(@as(u8, 0), first_entry.content[first_entry.content.len]);
    const first_hash = first_entry.content_hash;

    try std.testing.expectEqual(@as(u32, 2), (try source_map.getLineIndex(file_id)).countLines());

    // [3] Update overlay using POSIX path; verify same `FileId`, incremented revision, and rebuilt `LineIndex`:
    try std.testing.expectEqual(
        file_id,
        try source_map.setOverlay("src/core/math.cx", "pub fn add() {}\npub fn sub() {}\n", .root),
    );
    try std.testing.expectEqual(@as(usize, 1), source_map.countFiles());

    const updated_entry = source_map.getFileEntry(file_id).?;
    try std.testing.expectEqual(@as(u32, 2), updated_entry.revision);
    try std.testing.expect(!std.mem.eql(u8, &first_hash, &updated_entry.content_hash));

    try std.testing.expectEqual(@as(u32, 3), (try source_map.getLineIndex(file_id)).countLines());
}

test "test_vfs_sourcemap_disk_loading_small_and_large_files" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var source_map = VfsSourceMap.init(std.testing.allocator, &interner);
    defer source_map.deinit(std.testing.io);

    // [1] Load a small file (`< 16 KiB`) from disk and verify `.arena_small` backing + path deduplication:
    const small_id = try source_map.resolveOrCreatePath(std.testing.io, "build.zig", .root);
    try std.testing.expectEqual(small_id, try source_map.resolveOrCreatePath(std.testing.io, "./build.zig", .root));

    const small_entry = source_map.getFileEntry(small_id).?;
    try std.testing.expectEqual(vfs.BackingKind.arena_small, small_entry.backing_kind);
    try std.testing.expectEqual(@as(u8, 0), small_entry.content[small_entry.content.len]);

    // [2] Load a `>= 16 KiB` file from disk (`stage0/src/syntax_arenas.zig`) and verify NUL sentinel:
    const large_id = try source_map.resolveOrCreatePath(std.testing.io, "stage0\\src\\syntax_arenas.zig", .root);
    try std.testing.expectEqual(
        large_id,
        try source_map.resolveOrCreatePath(std.testing.io, "stage0/src/syntax_arenas.zig", .root),
    );

    const large_entry = source_map.getFileEntry(large_id).?;
    try std.testing.expect(large_entry.content.len >= vfs.SMALL_FILE_THRESHOLD);
    try std.testing.expectEqual(@as(u8, 0), large_entry.content[large_entry.content.len]);

    // [3] Verify exact 4096-byte page multiple (`16,384` bytes) uses `.arena_small` with safe NUL sentinel:
    const temp_page_path = ".zig-cache/test_page_boundary_16384.tmp";
    {
        const temp_file = try std.Io.Dir.cwd().createFile(std.testing.io, temp_page_path, .{});
        defer temp_file.close(std.testing.io);
        var page_buf: [16384]u8 = @splat('x');
        page_buf[16383] = '\n';
        try temp_file.writePositionalAll(std.testing.io, &page_buf, 0);
    }
    defer std.Io.Dir.cwd().deleteFile(std.testing.io, temp_page_path) catch {};

    const page_entry = source_map.getFileEntry(
        try source_map.resolveOrCreatePath(std.testing.io, temp_page_path, .root),
    ).?;
    try std.testing.expectEqual(@as(usize, 16384), page_entry.content.len);
    try std.testing.expectEqual(vfs.BackingKind.arena_small, page_entry.backing_kind);
    try std.testing.expectEqual(@as(u8, 0), page_entry.content[page_entry.content.len]);
}

test "test_line_index_mid_codepoint_monotonic_columns" {
    const source_text = "𐍈!";
    var line_index = try LineIndex.build(std.testing.allocator, source_text);
    defer line_index.deinit(std.testing.allocator);

    var prev_utf8: u32 = 0;
    var prev_utf16: u32 = 0;
    var offset: u32 = 0;
    while (offset <= source_text.len) : (offset += 1) {
        const resolved = line_index.resolveLineCol(source_text, offset);
        try std.testing.expect(resolved.col_utf8 >= prev_utf8);
        try std.testing.expect(resolved.col_utf16_0 >= prev_utf16);
        prev_utf8 = resolved.col_utf8;
        prev_utf16 = resolved.col_utf16_0;
    }
    try std.testing.expectEqual(@as(u32, 3), prev_utf8);
    try std.testing.expectEqual(@as(u32, 3), prev_utf16);
}

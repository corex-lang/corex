//! Phase 0 Deterministic PRNG Fuzzing Suite (`tests/fuzz/phase0_fuzz.zig`)
//!
//! Executes 1,000+ deterministic PRNG fuzz iterations per subsystem against `LineIndex` (compared
//! against a naive $O(N)$ reference scanner), `TransactionalPatcher`, and `BumpArena` + `StringInterner`.
//!
//! Asserts zero panics, zero out-of-bounds reads, zero memory leaks, and exact oracle equivalence.

const std = @import("std");
const corex = @import("corex");

const mem = corex.mem_foundation;
const FileId = corex.FileId;
const StringId = corex.StringId;
const BumpArena = corex.BumpArena;
const StringInterner = corex.StringInterner;
const LineCol = corex.LineCol;
const LineIndex = corex.LineIndex;
const SuggestedFix = corex.SuggestedFix;
const TextEdit = corex.TextEdit;
const TransactionalPatcher = corex.TransactionalPatcher;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of deterministic PRNG iterations executed per fuzz target (`>= 1,000`).
const FUZZ_ITERATIONS: usize = 1_024;

// -------------------------------------- INTERNALS --------------------------------------

/// Reference $O(N)$ linear scanner computing `LineCol` without binary search or `non_ascii_lines` bitsets.
fn naiveResolveLineCol(source: []const u8, byte_offset: u32) LineCol {
    const source_len: u32 = @intCast(source.len);
    const clamped_offset = @min(byte_offset, source_len);

    // [1] Linearly scan `source` to find the `[line_start .. line_end)` containing `clamped_offset`:
    var line_num: u32 = 1;
    var line_start: u32 = 0;
    var cursor: u32 = 0;
    while (cursor < clamped_offset) : (cursor += 1) {
        if (source[cursor] == '\n') {
            line_num += 1;
            line_start = cursor + 1;
        }
    }

    var line_end: u32 = line_start;
    while (line_end < source_len and source[line_end] != '\n') : (line_end += 1) {}
    if (line_end > line_start and source[line_end - 1] == '\r') {
        line_end -= 1;
    }

    const effective_offset = @min(clamped_offset, line_end);

    // [2] Decode UTF-8 and UTF-16 code units from `line_start` up to `effective_offset`:
    var col_utf8: u32 = 1;
    var col_utf16_0: u32 = 0;
    var scan_idx: usize = line_start;
    const scan_limit: usize = effective_offset;
    while (scan_idx < scan_limit) {
        const first_byte = source[scan_idx];
        if (first_byte < 0x80) {
            col_utf8 += 1;
            col_utf16_0 += 1;
            scan_idx += 1;
        } else {
            const seq_len = std.unicode.utf8ByteSequenceLength(first_byte) catch {
                col_utf8 += 1;
                col_utf16_0 += 1;
                scan_idx += 1;
                continue;
            };
            if (scan_idx + seq_len > @as(usize, line_end)) {
                col_utf8 += 1;
                col_utf16_0 += 1;
                scan_idx += 1;
                continue;
            }
            const codepoint = std.unicode.utf8Decode(source[scan_idx .. scan_idx + seq_len]) catch {
                col_utf8 += 1;
                col_utf16_0 += 1;
                scan_idx += 1;
                continue;
            };
            if (scan_idx + seq_len > scan_limit) break;
            col_utf8 += 1;
            col_utf16_0 += if (codepoint >= 0x10000) 2 else 1;
            scan_idx += seq_len;
        }
    }

    return .{
        .line = line_num,
        .col_utf8 = col_utf8,
        .col_utf16_0 = col_utf16_0,
        .col_byte = (effective_offset - line_start) + 1,
        .line_start_byte = line_start,
        .line_end_byte = line_end,
    };
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_line_index_matches_naive_scanner_across_1024_random_inputs" {
    var prng = std.Random.DefaultPrng.init(0xC0DEC0DE_20261109);
    const random = prng.random();

    const fragments = [_][]const u8{
        "a",    "bc",   " ", "\n", "\r\n", "\r",
        "é",
        "─",
        "𐍈",
        "\xff", "\xc3",
    };

    var source_buf: [256]u8 = undefined;
    var iter_idx: usize = 0;
    while (iter_idx < FUZZ_ITERATIONS) : (iter_idx += 1) {
        var byte_len: usize = 0;
        const fragment_count = random.intRangeAtMost(usize, 0, 32);
        var frag_idx: usize = 0;
        while (frag_idx < fragment_count) : (frag_idx += 1) {
            const piece = fragments[random.uintLessThan(usize, fragments.len)];
            if (byte_len + piece.len <= source_buf.len) {
                @memcpy(source_buf[byte_len .. byte_len + piece.len], piece);
                byte_len += piece.len;
            }
        }
        const source_slice = source_buf[0..byte_len];

        var line_index = try LineIndex.build(std.testing.allocator, source_slice);
        defer line_index.deinit(std.testing.allocator);

        var query_idx: usize = 0;
        while (query_idx < 8) : (query_idx += 1) {
            const offset = random.intRangeAtMost(u32, 0, @intCast(byte_len + 4));
            try std.testing.expectEqual(
                naiveResolveLineCol(source_slice, offset),
                line_index.resolveLineCol(source_slice, offset),
            );
        }
    }
}

test "test_fuzz_transactional_patcher_overlapping_and_out_of_bounds_edits" {
    var prng = std.Random.DefaultPrng.init(0x5AFEC0DE_12345678);
    const random = prng.random();

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    const rep_ids = [_]StringId{
        .empty,
        try interner.intern("x"),
        try interner.intern("mut_val"),
        try interner.intern("long_replacement_identifier"),
        .none,
    };
    const priorities = [_]corex.diagnostic.EditPriority{
        .memory_safety,
        .type_migration,
        .syntax_canonicalization,
        .lint_idiom,
        .formatting,
    };
    const applicabilities = [_]corex.diagnostic.FixApplicability{
        .machine_applicable,
        .machine_applicable,
        .has_placeholders,
        .maybe_incorrect,
    };

    var source_buf: [96]u8 = undefined;
    for (&source_buf, 0..) |*byte_ptr, i| {
        byte_ptr.* = 'a' + @as(u8, @intCast(i % 26));
    }

    var iter_idx: usize = 0;
    while (iter_idx < FUZZ_ITERATIONS) : (iter_idx += 1) {
        const src_len = random.intRangeAtMost(usize, 0, source_buf.len);
        const source_slice = source_buf[0..src_len];
        const target_file = FileId.fromInt(0);

        var edit_pool: [32]TextEdit = undefined;
        var fix_pool: [8]SuggestedFix = undefined;
        var edit_cursor: usize = 0;
        const fix_count = random.intRangeAtMost(usize, 1, fix_pool.len);

        var fix_idx: usize = 0;
        while (fix_idx < fix_count) : (fix_idx += 1) {
            const edit_count = random.intRangeAtMost(usize, 0, 4);
            const start_edit_idx = edit_cursor;
            var e_idx: usize = 0;
            while (e_idx < edit_count and edit_cursor < edit_pool.len) : (e_idx += 1) {
                edit_pool[edit_cursor] = .{
                    .file_id = if (random.uintLessThan(u8, 8) == 0) FileId.fromInt(1) else target_file,
                    .start_byte = random.intRangeAtMost(u32, 0, @intCast(src_len + 4)),
                    .end_byte = random.intRangeAtMost(u32, 0, @intCast(src_len + 4)),
                    .replacement_id = rep_ids[random.uintLessThan(usize, rep_ids.len)],
                };
                edit_cursor += 1;
            }
            fix_pool[fix_idx] = .{
                .message = "fuzz fix",
                .applicability = applicabilities[random.uintLessThan(usize, applicabilities.len)],
                .priority = priorities[random.uintLessThan(usize, priorities.len)],
                .edits = edit_pool[start_edit_idx..edit_cursor],
            };
        }

        const outcome = try TransactionalPatcher.apply(
            std.testing.allocator,
            source_slice,
            target_file,
            fix_pool[0..fix_count],
            &interner,
        );
        defer std.testing.allocator.free(outcome.patched_source);

        try std.testing.expect(outcome.applied_count + outcome.skipped_conflict_count <= fix_count);
        if (outcome.applied_count == 0) {
            try std.testing.expectEqualStrings(source_slice, outcome.patched_source);
        }
    }
}

test "test_fuzz_bump_arena_checkpoints_and_string_interner_consistency" {
    var prng = std.Random.DefaultPrng.init(0xA2E4A000_98765432);
    const random = prng.random();

    var arena = BumpArena.init(std.testing.allocator);
    defer arena.deinit();

    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var checkpoints: [16]mem.Checkpoint = undefined;
    var cp_depth: usize = 0;
    const alignments = [_]usize{ 1, 2, 4, 8, 16 };

    var sym_buf: [24]u8 = undefined;
    var iter_idx: usize = 0;
    while (iter_idx < FUZZ_ITERATIONS) : (iter_idx += 1) {
        const action = random.uintLessThan(u8, 4);
        if (action == 0 and cp_depth < checkpoints.len) {
            checkpoints[cp_depth] = arena.checkpoint();
            cp_depth += 1;
        } else if (action == 1 and cp_depth > 0) {
            cp_depth -= 1;
            arena.restore(checkpoints[cp_depth]);
            try std.testing.expectEqual(checkpoints[cp_depth].total_allocated, arena.total_allocated);
        } else if (action == 2) {
            const align_bytes = alignments[random.uintLessThan(usize, alignments.len)];
            const byte_count = if (random.uintLessThan(u8, 32) == 0)
                mem.DEFAULT_SLAB_SIZE + random.intRangeAtMost(usize, 1, 512)
            else
                random.intRangeAtMost(usize, 0, 256);

            const slice = try arena.allocAligned(byte_count, align_bytes);
            if (byte_count > 0) {
                try std.testing.expectEqual(@as(usize, 0), @intFromPtr(slice.ptr) % align_bytes);
                try std.testing.expectEqual(@as(u8, 0), slice[0]);
                try std.testing.expectEqual(@as(u8, 0), slice[slice.len - 1]);
                @memset(slice, 0xCC);
            }
        } else {
            var sym_writer = std.Io.Writer.fixed(&sym_buf);
            try sym_writer.print("fuzz_sym_{d}", .{random.uintLessThan(u32, 200)});
            const sym_text = sym_writer.buffered();
            const sym_id = try interner.intern(sym_text);
            try std.testing.expectEqual(sym_id, interner.lookup(sym_text).?);
            try std.testing.expectEqualStrings(sym_text, interner.get(sym_id));
        }
    }
}

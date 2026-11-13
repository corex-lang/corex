//! Phase 1 Deterministic Lexer & Lossless Trivia Fuzzing Suite (`tests/fuzz/phase1_lexer_fuzz.zig`)
//!
//! Executes 10,000,000+ deterministic PRNG random and mutated byte inputs through `Lexer.tokenize`,
//! plus 10,000 rich multi-token `.cx` grammar-mutated inputs with full `DiagnosticSink`,
//! `StringInterner`, and `LosslessCstArena.reconstructSource` verification.
//!
//! Asserts zero panics, zero hangs, zero out-of-bounds spans, final `.eof` sentinel presence, and
//! 100% lossless byte-for-bit source reconstruction across every single fuzz input.

const std = @import("std");
const corex = @import("corex");

const syntax = corex.syntax_arenas;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const StringInterner = corex.StringInterner;
const TokenKind = corex.TokenKind;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const Lexer = corex.Lexer;
const DiagnosticSink = corex.DiagnosticSink;

// --------------------------------------- CONSTS ----------------------------------------

/// Total number of high-speed random and mutated byte inputs executed in the primary fuzz gate.
const FAST_FUZZ_ITERATIONS: usize = 10_000_000;
/// Number of deterministic parallel worker shards dividing `FAST_FUZZ_ITERATIONS`.
const FAST_FUZZ_WORKER_COUNT: usize = 4;
/// Number of iterations executed by each deterministic worker shard (`2,500,000` x `4` = `10,000,000`).
const FAST_FUZZ_ITERS_PER_WORKER: usize = FAST_FUZZ_ITERATIONS / FAST_FUZZ_WORKER_COUNT;
/// Number of rich multi-token mutated `.cx` inputs verified with `LosslessCstArena.reconstructSource`.
const RICH_MUTATION_ITERATIONS: usize = 10_000;

/// Seed fragments covering all CoreX lexical categories, delimiters, escapes, and invalid UTF-8.
const LEXICAL_SEED_FRAGMENTS = [_][]const u8{
    "#!/usr/bin/env corex\n",
    "//! module doc\r\n",
    "/// item doc\n",
    "// line comment\n",
    "/* outer /* inner */ */",
    "/* unclosed",
    "pub ",
    "fn ",
    "struct ",
    "let ",
    "mut ",
    "comptime ",
    "bit_field ",
    "i32 ",
    "usize ",
    "snake_name ",
    "badCamel ",
    "PascalType ",
    "Bad_Type ",
    "MAX_CONST ",
    "BAD__CONST_ ",
    "_ ",
    "0 ",
    "42_000 ",
    "0xdead_beef ",
    "0x_bad ",
    "0b1010 ",
    "0b102 ",
    "0o755 ",
    "3.14e-2 ",
    "1.0e+ ",
    "0..10 ",
    "0..=10 ",
    "10.max(20) ",
    "\"hello \\n \\x7F \\u{1F600} \\'\"",
    "\"interp {if a { \"nested\" } else { r#\"raw\"# }}\"",
    "\"unterminated { 1 + 2",
    "\"\\xGG \\u{D800} \\u{}\"",
    "r\"raw string\"",
    "r#\"raw \"quoted\"\"#",
    "r#bad",
    "'a'",
    "'é'",
    "'𐍈'",
    "''",
    "'ab'",
    "#soa ",
    "#bad ",
    "+% -% *% +| -| *| |> -> => :: <<= >>= ",
    "\xEF\xBB\xBF",
    "\r\x0B\x0C",
    "\xFF\xFE\xC3\x28$",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Advances `state` using a branchless 64-bit `xorshift64*` PRNG step.
inline fn nextPrngU64(state: *u64) u64 {
    var val = state.*;
    val ^= val << 13;
    val ^= val >> 7;
    val ^= val << 17;
    state.* = val;
    return val *% 0x2545F4914F6CDD1D;
}

/// Verifies in $O(T)$ register checks that `token_buf` partitions `source[0..source.len]` losslessly.
inline fn verifyLosslessPartitionInline(source: []const u8, token_buf: *const TokenBuffer) !void {
    const token_count = token_buf.tokens.len;
    if (token_count == 0) return error.EmptyTokenStream;

    const kinds = token_buf.tokens.items(.kind);
    const flags = token_buf.tokens.items(.flags);
    const offsets = token_buf.tokens.items(.byte_offset);
    const lengths = token_buf.tokens.items(.byte_len);
    const trivia_spans = token_buf.tokens.items(.trivia_span);
    const trivia_items = token_buf.trivia.items;

    if (kinds[token_count - 1] != .eof) return error.MissingEofToken;

    var expected_offset: u32 = 0;
    var i: usize = 0;
    while (i < token_count) : (i += 1) {
        const span_meta = trivia_spans[i];
        const lead_start: usize = span_meta.start_index;
        const lead_end: usize = lead_start + span_meta.leading_count;
        var j: usize = lead_start;
        while (j < lead_end) : (j += 1) {
            const piece = trivia_items[j];
            if (piece.byte_offset != expected_offset) return error.NonContiguousLeadingTrivia;
            expected_offset += piece.byte_len;
        }

        if (!flags[i].is_synthesized) {
            if (offsets[i] != expected_offset) return error.NonContiguousTokenOffset;
            expected_offset += lengths[i];
        }

        const trail_end: usize = lead_end + span_meta.trailing_count;
        j = lead_end;
        while (j < trail_end) : (j += 1) {
            const piece = trivia_items[j];
            if (piece.byte_offset != expected_offset) return error.NonContiguousTrailingTrivia;
            expected_offset += piece.byte_len;
        }
    }

    if (expected_offset != @as(u32, @intCast(source.len))) {
        return error.LosslessByteLengthMismatch;
    }
}

/// Runs a deterministic shard of `iteration_count` random and mutated lexer inputs on a reusable `TokenBuffer`.
fn runFastFuzzWorkerShard(
    token_buf: *TokenBuffer,
    initial_seed: u64,
    iteration_count: usize,
    has_failed: *bool,
) void {
    var ring_buf: [256]u8 = undefined;
    const seed_pattern =
        "fn calc(x: i32) { let s = \"a{x}\\n\"; /* c */ 0x1F +% 1..10 'é' r#\"q\"# #soa }\r\n\xFF";
    for (&ring_buf, 0..) |*byte_ptr, i| {
        byte_ptr.* = seed_pattern[(i + @as(usize, @intCast(initial_seed & 0x3F))) % seed_pattern.len];
    }

    var prng_state: u64 = initial_seed;
    const file_id = FileId.fromInt(0);

    var iter_idx: usize = 0;
    while (iter_idx < iteration_count) : (iter_idx += 1) {
        const rand_val = nextPrngU64(&prng_state);
        const mutate_pos: usize = @intCast(rand_val & 0xFF);
        ring_buf[mutate_pos] = @truncate(rand_val >> 8);

        const base_len: usize = @intCast((rand_val >> 16) & 0x03);
        const extra_len: usize = if ((iter_idx & 15) == 0) @intCast((rand_val >> 20) & 0x07) else 0;
        const slice_len: usize = base_len + extra_len;
        const start_pos: usize = @intCast((rand_val >> 24) & 0xF0);
        const input_slice = ring_buf[start_pos .. start_pos + slice_len];

        token_buf.tokens.shrinkRetainingCapacity(0);
        token_buf.trivia.shrinkRetainingCapacity(0);

        var lexer_instance = Lexer.init(input_slice, file_id, token_buf, null, null);
        lexer_instance.tokenize() catch {
            has_failed.* = true;
            return;
        };
        verifyLosslessPartitionInline(input_slice, token_buf) catch {
            has_failed.* = true;
            return;
        };
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_lexer_10_million_random_and_mutated_inputs_lossless" {
    var worker_buffers: [FAST_FUZZ_WORKER_COUNT]TokenBuffer = undefined;
    var worker_failures: [FAST_FUZZ_WORKER_COUNT]bool = @splat(false);
    for (&worker_buffers) |*buf_item| {
        buf_item.* = TokenBuffer.init(std.testing.allocator);
        try buf_item.tokens.ensureTotalCapacity(std.testing.allocator, 64);
        try buf_item.trivia.ensureTotalCapacity(std.testing.allocator, 64);
    }
    defer for (&worker_buffers) |*buf_item| {
        buf_item.deinit();
    };

    var threads: [FAST_FUZZ_WORKER_COUNT - 1]?std.Thread = @splat(null);
    for (0..FAST_FUZZ_WORKER_COUNT - 1) |worker_idx| {
        const worker_seed: u64 = 0xC0DEC0DE_20261109 ^
            (@as(u64, @intCast(worker_idx + 1)) *% 0x9E37_79B9_7F4A_7C15);
        threads[worker_idx] = std.Thread.spawn(
            .{},
            runFastFuzzWorkerShard,
            .{
                &worker_buffers[worker_idx],
                worker_seed,
                FAST_FUZZ_ITERS_PER_WORKER,
                &worker_failures[worker_idx],
            },
        ) catch null;
        if (threads[worker_idx] == null) {
            runFastFuzzWorkerShard(
                &worker_buffers[worker_idx],
                worker_seed,
                FAST_FUZZ_ITERS_PER_WORKER,
                &worker_failures[worker_idx],
            );
        }
    }

    // Run final shard on the calling test thread:
    runFastFuzzWorkerShard(
        &worker_buffers[FAST_FUZZ_WORKER_COUNT - 1],
        0xC0DEC0DE_20261109,
        FAST_FUZZ_ITERS_PER_WORKER,
        &worker_failures[FAST_FUZZ_WORKER_COUNT - 1],
    );

    for (threads) |maybe_thread| {
        if (maybe_thread) |thread_handle| {
            thread_handle.join();
        }
    }
    for (worker_failures) |is_shard_failed| {
        try std.testing.expect(!is_shard_failed);
    }
}

test "test_fuzz_lexer_10k_rich_mutated_programs_with_diagnostics_and_reconstruct" {
    var prng = std.Random.DefaultPrng.init(0x5AFEC0DE_98765432);
    const random = prng.random();

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var source_buf: [512]u8 = undefined;
    var iter_idx: usize = 0;
    while (iter_idx < RICH_MUTATION_ITERATIONS) : (iter_idx += 1) {
        // [1] Assemble 1..12 random lexical fragments into `source_buf`:
        var byte_len: usize = 0;
        const frag_count = random.intRangeAtMost(usize, 0, 12);
        var frag_idx: usize = 0;
        while (frag_idx < frag_count) : (frag_idx += 1) {
            const frag = LEXICAL_SEED_FRAGMENTS[random.uintLessThan(usize, LEXICAL_SEED_FRAGMENTS.len)];
            if (byte_len + frag.len <= source_buf.len) {
                @memcpy(source_buf[byte_len .. byte_len + frag.len], frag);
                byte_len += frag.len;
            }
        }

        // [2] Apply 0..4 random byte mutations (bit flips, quote/brace injections, invalid UTF-8):
        const mutation_count = random.intRangeAtMost(usize, 0, 4);
        var mut_idx: usize = 0;
        while (mut_idx < mutation_count and byte_len > 0) : (mut_idx += 1) {
            source_buf[random.uintLessThan(usize, byte_len)] = random.int(u8);
        }

        const source_slice = source_buf[0..byte_len];
        token_buf.tokens.shrinkRetainingCapacity(0);
        token_buf.trivia.shrinkRetainingCapacity(0);

        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();

        const max_tok_cap: usize = if (iter_idx % 64 == 0)
            random.intRangeAtMost(usize, 1, 8)
        else
            syntax.MAX_TOKENS_PER_FILE;

        var lexer_instance = Lexer.initWithOptions(
            source_slice,
            FileId.fromInt(0),
            &token_buf,
            &sink,
            &interner,
            .{ .max_tokens = max_tok_cap },
        );
        try lexer_instance.tokenize();

        // [3] Verify both inline partition check and full `LosslessCstArena.reconstructSource`:
        try verifyLosslessPartitionInline(source_slice, &token_buf);
        const reconstructed = try cst_arena.reconstructSource(
            std.testing.allocator,
            source_slice,
            &token_buf,
        );
        defer std.testing.allocator.free(reconstructed);
        try std.testing.expectEqualSlices(u8, source_slice, reconstructed);

        try std.testing.expectEqual(
            TokenKind.eof,
            token_buf.getToken(TokenIndex.fromInt(@intCast(token_buf.countTokens() - 1))).kind,
        );
    }
}

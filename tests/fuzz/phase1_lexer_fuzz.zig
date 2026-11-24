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

/// Seed fragments covering all CoreX `DR-24` lexical categories, delimiters, escapes, recovery edges, and invalid UTF-8.
const LEXICAL_SEED_FRAGMENTS = [_][]const u8{
    "#!/usr/bin/env corex\n",
    "/# module doc\r\n",
    "/| item doc\n",
    "///| commented-out item doc\n",
    "///# commented-out module doc\n",
    "//// banner comment\n",
    "// line comment\n",
    "//! retired mod doc\r\n",
    "/// retired item doc\n",
    "/* outer /* inner */ */",
    "/* unclosed",
    "\tlet tab_indent = 1;\n",
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
    "\"hello \\n \\x7F \\u{1F600} \\' {literal_brace}\"",
    "f\"interp {if ok => f\\\"nested {r#\\\"raw\\\"#}\\\" else \\\"alt\\\":>8}\"",
    "f#\"{\"node\": \"{id}\", \"state\": \"{if ok => \"UP\" else \"DOWN\"}\"}\"#",
    "f\"zero_hole_warn\"",
    "f\"unmatched } brace\"",
    "f\"unterminated { 1 + 2",
    "\"\\xGG \\u{D800} \\u{}\"",
    "r\"raw string {literal}\"",
    "r#\"raw \"quoted\"\"#",
    "r#bad",
    "'a'",
    "'é'",
    "'𐍈'",
    "''",
    "'ab'",
    "#soa ",
    "#bad ",
    "subscript ",
    "yield ",
    "opaque ",
    "orelse ",
    "with ",
    "context ",
    "unreachable ",
    "b'x' ",
    "b'\\x7F' ",
    "b'é' ",
    "b\"HTTP/1.1\\r\\n\" ",
    "br#\"raw \"bytes\"\"# ",
    "42_u64 ",
    "0xFF_u8 ",
    "3.14_f32 ",
    "10_f64 ",
    "\"\n    plain multiline {literal}\n    \"",
    "f\"\n    multiline {val=} {{brace}} {if ok => \"inner\" else \"alt\"}\n    \"",
    "f#\"\n    {\"port\": {val:04}}\n    \"#",
    "r\"\n  raw multiline {ok}\n  \"",
    "r#\"\n  raw multiline \"ok\"\n  \"#",
    "b\"\n    raw byte lines\n    \"",
    "br#\"\n    raw \"byte\" lines\n    \"#",
    "\"\"\"bad_opening\"\"\"",
    "f\"\"\"\n    retired triple\n    \"\"\"",
    "r\"\"\"\n  retired raw triple\n  \"\"\"",
    "b\"\"\"retired_byte_triple\"\"\"",
    "\"\n  under_indented\n    \"",
    "\"\n    shared_close\"",
    "\"bad \\{ escape \\}\"",
    "@repr(C, packed: true, align: .CacheLine, zero_pad: true) ",
    "@link(name: \"sym\", section: \".text\") ",
    "if ok => 1 else 0 ",
    "&& ",
    "... ",
    "~ ",
    ":= ",
    "$ ",
    "[..$-1] ",
    "tup.0.1.2 ",
    "0..0.5 ",
    "+% -% *% +| -| *| |> -> => ... := $ ~ <<= >>= ",
    "\xEF\xBB\xBF",
    "\r\x0B\x0C",
    "\xFF\xFE\xC3\x28$`",
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
        "/# mod\n/| doc\nfn calc(x: i32) { let text = f\"a{x=} {{b}}\\n\"; " ++
        "0x1F_u64 +% if x > 0 => 1 else 0 b'x' b\"w\" r#\"q\"# f#\"z{x}\"# #soa }\r\n\xFF";
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

test "test_fuzz_lexer_dr24_comments_fmt_strings_and_multiline_dedent" {
    // [1] Enforce `DR-24` `TokenKind` (`121` variants, `fmt_string_lit = 60`) and `TriviaKind` (`9` variants):
    try std.testing.expectEqual(@as(usize, 121), std.enums.values(TokenKind).len);
    try std.testing.expectEqual(@as(u8, 60), @backingInt(TokenKind.fmt_string_lit));
    try std.testing.expectEqual(@as(usize, 9), std.enums.values(syntax.TriviaKind).len);

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    // [2] Verify clean `DR-24` positive lexemes (`/#`, `/|`, `///|`, `///#`, `f"…"`, `f#"…"#`, `"<newline> … "`):
    const canonical_dr24_source =
        "/# Canonical DR-24 lexer verification module.\n" ++
        "\n" ++
        "///# Commented-out module banner scanned as line_comment.\n" ++
        "///| Commented-out item docstring scanned as line_comment.\n" ++
        "/| Aligned packet header.\n" ++
        "@repr(C, align: .CacheLine, zero_pad: true)\n" ++
        "pub struct AlignedHeader {\n" ++
        "    /| Sequence counter.\n" ++
        "    pub seq_id: u64,\n" ++
        "}\n" ++
        "\n" ++
        "/| Formats plain and interpolated strings across all dedented multiline prefixes.\n" ++
        "@link(name: \"cx_format_probe\", section: \".text\")\n" ++
        "pub fn format_probe(port: u16, healthy: bool) -> str {\n" ++
        "    let plain_sql = \"SELECT id FROM nodes WHERE meta != '{}'\";\n" ++
        "    let fmt_line = f\"port={port:04} status={if healthy => \"UP\" else \"DOWN\":>6}\";\n" ++
        "    let fmt_guarded = f#\"{\"port\": {port}, \"state\": \"{if healthy => \"OK\" else \"WARN\"}\"}\"#;\n" ++
        "    let dedent_plain = \"\n" ++
        "        plain {literal} line\n" ++
        "        \";\n" ++
        "    let dedent_fmt = f\"\n" ++
        "        {{escaped}} port={port=}\n" ++
        "        \";\n" ++
        "    let dedent_fmt_guard = f#\"\n" ++
        "        {\"port\": {port:#06x}}\n" ++
        "        \"#;\n" ++
        "    let dedent_raw = r\"\n" ++
        "        raw {literal}\n" ++
        "        \";\n" ++
        "    let dedent_raw_guard = r#\"\n" ++
        "        raw \"quoted\" {literal}\n" ++
        "        \"#;\n" ++
        "    let dedent_bytes = b\"\n" ++
        "        HTTP/1.1 200 OK\n" ++
        "        \";\n" ++
        "    let dedent_raw_bytes = br#\"\n" ++
        "        raw \"bytes\"\n" ++
        "        \"#;\n" ++
        "    _ = (plain_sql, fmt_line, fmt_guarded, dedent_fmt, dedent_fmt_guard);\n" ++
        "    _ = (dedent_raw, dedent_raw_guard, dedent_bytes, dedent_raw_bytes);\n" ++
        "    return dedent_plain;\n" ++
        "}\n";

    {
        var clean_sink = DiagnosticSink.init(std.testing.allocator);
        defer clean_sink.deinit();
        var clean_lexer = Lexer.init(canonical_dr24_source, FileId.fromInt(0), &token_buf, &clean_sink, &interner);
        try clean_lexer.tokenize();
        try std.testing.expectEqual(@as(usize, 0), clean_sink.diagnostics.items.len);
        try verifyLosslessPartitionInline(canonical_dr24_source, &token_buf);

        var fmt_tok_count: usize = 0;
        for (token_buf.tokens.items(.kind)) |tok_kind| {
            if (tok_kind == .fmt_string_lit) fmt_tok_count += 1;
        }
        try std.testing.expectEqual(@as(usize, 4), fmt_tok_count);
    }

    // [3] Verify exact diagnostic codes & lossless recovery on retired/invalid `DR-24` lexical constructs:
    const diagnostic_cases = [_]struct {
        snippet: []const u8,
        expected_code: []const u8,
    }{
        .{ .snippet = "/* retired block comment */\n", .expected_code = "E0118" },
        .{ .snippet = "/// retired outer doc\npub const VAL: u32 = 1;\n", .expected_code = "E0118" },
        .{ .snippet = "//! retired mod doc\n", .expected_code = "E0118" },
        .{ .snippet = "const BAD_TRIPLE: str = \"\"\"\n    retired\n    \"\"\";\n", .expected_code = "E0115" },
        .{ .snippet = "const BAD_CLOSE: str = \"\n    shared_line\";\n", .expected_code = "E0115" },
        .{ .snippet = "const BAD_DEDENT: str = \"\n  under_indented\n    \";\n", .expected_code = "E0116" },
        .{ .snippet = "pub fn tab_fn() {\n\tlet val = 1;\n}\n", .expected_code = "E0116" },
        .{ .snippet = "const ZERO_HOLES: str = f\"plain literal\";\n", .expected_code = "W0119" },
    };

    for (diagnostic_cases) |diag_case| {
        token_buf.tokens.shrinkRetainingCapacity(0);
        token_buf.trivia.shrinkRetainingCapacity(0);
        var case_sink = DiagnosticSink.init(std.testing.allocator);
        defer case_sink.deinit();

        var case_lexer = Lexer.init(diag_case.snippet, FileId.fromInt(1), &token_buf, &case_sink, &interner);
        try case_lexer.tokenize();
        try verifyLosslessPartitionInline(diag_case.snippet, &token_buf);

        const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, diag_case.snippet, &token_buf);
        defer std.testing.allocator.free(reconstructed);
        try std.testing.expectEqualSlices(u8, diag_case.snippet, reconstructed);

        var has_expected_code = false;
        for (case_sink.diagnostics.items) |emitted_diag| {
            if (std.mem.eql(u8, emitted_diag.code.asCodeStr(), diag_case.expected_code)) {
                has_expected_code = true;
                break;
            }
        }
        try std.testing.expect(has_expected_code);
    }
}

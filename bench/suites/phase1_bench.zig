//! Phase 1 High-Speed Lexer & Lossless CST Benchmark Suite (`bench/suites/phase1_bench.zig`)
//!
//! Benchmarks deterministic UTF-8 lexing throughput across a 64 KiB (`2,048` LOC) synthetic `.cx`
//! module (reusing `TokenBuffer` capacity for zero-allocation hot-path scanning), $O(1)$ keyword
//! and disjoint identifier casing classification across 10,000 identifiers, literal-heavy scanning
//! (radix integers, floats, nested `{expr}` string interpolations, and `r#"…"#` raw strings), and
//! lossless byte-for-bit source reconstruction via `LosslessCstArena.reconstructSource`.
//!
//! Executed via `zig build bench`, enforcing 5 warmup iterations and 30 timed iterations per workload
//! and rendering the canonical monochrome Unicode report table.

const std = @import("std");
const corex = @import("corex");

const syntax = corex.syntax_arenas;
const FileId = corex.FileId;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const Lexer = corex.Lexer;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;

// --------------------------------------- CONSTS ----------------------------------------

/// Representative 16-line `.cx` code block (`512` bytes) repeated 128 times to form a 64 KiB (`2,048` LOC) module.
const SYNTHETIC_BLOCK_16_LOC =
    "/// Computes bounded checksum across a borrowed slice of packet frames.\n" ++
    "pub fn compute_frame_checksum(frames: &[PacketFrame], seed_val: u64) -> Result[u64, FrameError] {\n" ++
    "    const PRIME_MULT: u64 = 0x9E37_79B9_7F4A_7C15;\n" ++
    "    var acc_hash: u64 = seed_val +% 1_000_000;\n" ++
    "    for idx in 0..frames.len() {\n" ++
    "        let item = frames[idx];\n" ++
    "        if item.is_valid and not item.is_empty {\n" ++
    "            acc_hash = (acc_hash *% PRIME_MULT) ^ item.payload_len.max(1);\n" ++
    "        }\n" ++
    "    }\n" ++
    "    /* Verify non-zero state before returning to caller */\n" ++
    "    let status_msg = \"hash={acc_hash} count={frames.len()}\\n\";\n" ++
    "    let raw_tag = r#\"corex::net::frame_v1\"#;\n" ++
    "    let sep_char = ':';\n" ++
    "    return Ok(acc_hash);\n" ++
    "}\n";

/// Complete 64 KiB (`2,048` LOC) synthetic `.cx` module evaluated in `benchSyntheticModuleLex`.
const SYNTHETIC_MODULE_64K: [SYNTHETIC_BLOCK_16_LOC.len * 128]u8 = blk: {
    var buf: [SYNTHETIC_BLOCK_16_LOC.len * 128]u8 = undefined;
    var i: usize = 0;
    while (i < 128) : (i += 1) {
        const start = i * SYNTHETIC_BLOCK_16_LOC.len;
        @memcpy(buf[start .. start + SYNTHETIC_BLOCK_16_LOC.len], SYNTHETIC_BLOCK_16_LOC);
    }
    break :blk buf;
};

/// Literal-heavy `.cx` workload exercising radix integers, floats, nested `{expr}` strings, and raw strings.
const LITERAL_WORKLOAD_CHUNK =
    "const HEX_MASK: u64 = 0xDEAD_BEEF_CAFE_BABE;\n" ++
    "const BIN_FLAGS: u32 = 0b1010_0101_1111_0000;\n" ++
    "const OCT_PERMS: u16 = 0o755;\n" ++
    "const FLOAT_TOL: f64 = 3.141_592_653e-12;\n" ++
    "let msg = \"val={if x > 0 { \"inner {r#\"raw\"#}\" } else { \"zero\" }} \\x7F \\u{03B1}\\n\";\n" ++
    "let regex_pat = r##\"^[a-zA-Z_][a-zA-Z0-9_]*$\"##;\n" ++
    "let glyphs = ['a', 'é', '─', '𐍈', '\\n', '\\t', '\\''];\n";

/// Complete literal-scanning benchmark buffer (`~25` KiB).
const LITERAL_WORKLOAD_BUFFER: [LITERAL_WORKLOAD_CHUNK.len * 64]u8 = blk: {
    var buf: [LITERAL_WORKLOAD_CHUNK.len * 64]u8 = undefined;
    var i: usize = 0;
    while (i < 64) : (i += 1) {
        const start = i * LITERAL_WORKLOAD_CHUNK.len;
        @memcpy(buf[start .. start + LITERAL_WORKLOAD_CHUNK.len], LITERAL_WORKLOAD_CHUNK);
    }
    break :blk buf;
};

/// Representative mix of 32 keywords, primitive types, `snake_case`, `PascalCase`, and `SCREAMING_SNAKE_CASE` lexemes.
const IDENTIFIER_CLASSIFICATION_CORPUS = [_][]const u8{
    "pub",                "fn",                   "struct",              "enum",
    "trait",              "impl",                 "comptime",            "bit_field",
    "errdefer",           "catch",                "return",              "while",
    "i32",                "u64",                  "usize",               "f64",
    "bool",               "str",                  "never",               "unit",
    "_",                  "resolve_path",         "parse_expression",    "emit_diagnostic",
    "count_instructions", "has_side_effects",     "TokenBuffer",         "LosslessCstArena",
    "DiagnosticRenderer", "TransactionalPatcher", "MAX_TOKENS_PER_FILE", "DEFAULT_SLAB_SIZE",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Shared scratch `TokenBuffer` reused across benchmark iterations to measure zero-allocation lexing speed.
var shared_bench_token_buf: ?TokenBuffer = null;

/// Returns a pointer to the pre-warmed reusable `TokenBuffer`, initializing capacity on first use.
fn getOrInitReusableTokenBuffer(allocator: std.mem.Allocator) !*TokenBuffer {
    if (shared_bench_token_buf == null) {
        var fresh_buf = TokenBuffer.init(allocator);
        try fresh_buf.tokens.ensureTotalCapacity(allocator, 32_768);
        try fresh_buf.trivia.ensureTotalCapacity(allocator, 32_768);
        shared_bench_token_buf = fresh_buf;
    }
    const buf_ptr = &shared_bench_token_buf.?;
    buf_ptr.tokens.shrinkRetainingCapacity(0);
    buf_ptr.trivia.shrinkRetainingCapacity(0);
    return buf_ptr;
}

/// Benchmarks pure single-pass lexer throughput on a 64 KiB (`2,048` LOC) `.cx` module reusing `TokenBuffer`.
fn benchSyntheticModuleLex(allocator: std.mem.Allocator) !usize {
    const token_buf = try getOrInitReusableTokenBuffer(allocator);
    var lexer_instance = Lexer.init(&SYNTHETIC_MODULE_64K, FileId.fromInt(0), token_buf, null, null);
    try lexer_instance.tokenize();
    std.mem.doNotOptimizeAway(token_buf.countTokens());
    return token_buf.countTokens() * @sizeOf(syntax.TokenRecord) +
        token_buf.trivia.items.len * @sizeOf(syntax.TriviaPiece);
}

/// Benchmarks `classifyIdentifierOrKeyword` $O(1)$ classification across 10,000 identifiers.
fn benchClassifyIdentifiers10k(allocator: std.mem.Allocator) !usize {
    _ = allocator;
    var canonical_accum: usize = 0;
    var i: usize = 0;
    while (i < 10_000) : (i += 1) {
        const result = corex.classifyIdentifierOrKeyword(
            IDENTIFIER_CLASSIFICATION_CORPUS[i & (IDENTIFIER_CLASSIFICATION_CORPUS.len - 1)],
        );
        canonical_accum +%= @backingInt(result.kind) + @as(usize, @intFromBool(result.is_canonical));
    }
    std.mem.doNotOptimizeAway(canonical_accum);
    return IDENTIFIER_CLASSIFICATION_CORPUS.len * @sizeOf([]const u8);
}

/// Benchmarks numeric, interpolated string, raw string, and UTF-8 character literal scanning throughput.
fn benchLiteralScanningThroughput(allocator: std.mem.Allocator) !usize {
    const token_buf = try getOrInitReusableTokenBuffer(allocator);
    var lexer_instance = Lexer.init(&LITERAL_WORKLOAD_BUFFER, FileId.fromInt(0), token_buf, null, null);
    try lexer_instance.tokenize();
    std.mem.doNotOptimizeAway(token_buf.countTokens());
    return token_buf.countTokens() * @sizeOf(syntax.TokenRecord) +
        token_buf.trivia.items.len * @sizeOf(syntax.TriviaPiece);
}

/// Benchmarks lossless byte-for-bit source reconstruction via `LosslessCstArena.reconstructSource` on 64 KiB.
fn benchLosslessReconstruct64k(allocator: std.mem.Allocator) !usize {
    const token_buf = try getOrInitReusableTokenBuffer(allocator);
    var lexer_instance = Lexer.init(&SYNTHETIC_MODULE_64K, FileId.fromInt(0), token_buf, null, null);
    try lexer_instance.tokenize();

    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();

    const reconstructed = try cst_arena.reconstructSource(allocator, &SYNTHETIC_MODULE_64K, token_buf);
    defer allocator.free(reconstructed);
    std.mem.doNotOptimizeAway(reconstructed.ptr);
    return reconstructed.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 1 lexer benchmark suite and prints the monochrome Unicode table to `stdout`.
pub fn main(init: std.process.Init) !void {
    defer if (shared_bench_token_buf) |*buf_ref| {
        buf_ref.deinit();
        shared_bench_token_buf = null;
    };

    const results = try corex.bench_harness.runSuite(
        init.gpa,
        init.io,
        &[_]BenchCase{
            .{
                .name = "Lexer.tokenize (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchSyntheticModuleLex,
            },
            .{
                .name = "classifyIdentifierOrKeyword (10k idents)",
                .run_fn = benchClassifyIdentifiers10k,
            },
            .{
                .name = "Lexer literals (numbers + interp + raw)",
                .run_fn = benchLiteralScanningThroughput,
            },
            .{
                .name = "LosslessCstArena.reconstructSource (64 KiB)",
                .run_fn = benchLosslessReconstruct64k,
            },
        },
    );
    defer init.gpa.free(results);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_writer = std.Io.File.stdout().writerStreaming(init.io, &stdout_buf);
    const style_config: StyleConfig = .{
        .is_color_enabled = corex.style.isColorEnabled(.auto, init.io, std.Io.File.stdout(), init.environ_map),
    };

    try style_config.writeStatusHeader(
        &stdout_writer.interface,
        .success,
        corex.Glyphs.POINTER_SOLID,
        "corex bench",
        "Phase 1 Lexer & Lossless Trivia Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, results);
    try stdout_writer.interface.flush();
}

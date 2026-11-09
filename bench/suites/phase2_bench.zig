//! Phase 2 Resilient LL(k) + Pratt Parser & Incremental Splice Benchmark Suite (`bench/suites/phase2_bench.zig`)
//!
//! Benchmarks full CST + AST construction throughput across a pre-tokenized 64 KiB (`2,048` LOC)
//! `.cx` module (reusing `LosslessCstArena` and `AstArena` capacity), end-to-end `parseSource`
//! (lexing + CST + AST lowering on 64 KiB), dense 15-tier Pratt expression parsing across 4,096
//! complex expressions (`|>`, `catch`, `as`, generic calls, postfix chains, and view blocks), and
//! single-function incremental re-parsing (`reparseIncremental`) inside a 128-function module.
//!
//! Executed via `zig build bench` or `zig build bench-phase2`, enforcing 5 warmup iterations and
//! 30 timed iterations per workload and rendering the canonical monochrome Unicode report table.

const std = @import("std");
const corex = @import("corex");

const syntax = corex.syntax_arenas;
const FileId = corex.FileId;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const Lexer = corex.Lexer;
const Parser = corex.Parser;
const EditRange = corex.EditRange;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;

// ---------------------------------------- TYPES ----------------------------------------

/// Persistent state for the incremental re-parse benchmark workload.
const IncrementalBenchState = struct {
    /// Retained token and trivia buffer across incremental edits.
    token_buf: TokenBuffer,
    /// Retained lossless CST arena across incremental edits.
    cst_arena: LosslessCstArena,
    /// Retained AST arena across incremental edits.
    ast_arena: AstArena,
    /// `true` when `SYNTHETIC_MODULE_64K_EDITED` is currently active in `token_buf`.
    is_edited_active: bool,

    /// Releases all backing buffers owned by the incremental benchmark state.
    fn deinit(self: *IncrementalBenchState) void {
        self.token_buf.deinit();
        self.cst_arena.deinit();
        self.ast_arena.deinit();
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Representative 16-line `.cx` function block repeated 128 times to form a 64 KiB (`2,048` LOC) module.
const SYNTHETIC_BLOCK_16_LOC =
    "/// Computes bounded checksum across a borrowed slice of packet frames.\n" ++
    "pub fn compute_frame_checksum(frames: &[PacketFrame], seed_val: u64) -> Result[u64, FrameError] {\n" ++
    "    let prime_factor: u64 = 0x9E37_79B9_7F4A_7C15;\n" ++
    "    var acc_hash: u64 = seed_val +% 1_000_000;\n" ++
    "    for idx in 0..frames.len() {\n" ++
    "        let item = frames[idx];\n" ++
    "        if item.is_valid and not item.is_empty {\n" ++
    "            acc_hash = (acc_hash *% prime_factor) ^ item.payload_len.max(1);\n" ++
    "        }\n" ++
    "    }\n" ++
    "    /* Verify non-zero state before returning to caller */\n" ++
    "    let status_msg = \"hash={acc_hash} count={frames.len()}\\n\";\n" ++
    "    let raw_tag = r#\"corex::net::frame_v1\"#;\n" ++
    "    let sep_char = ':';\n" ++
    "    return Ok(acc_hash);\n" ++
    "}\n";
/// Complete 64 KiB (`2,048` LOC, `128` functions) synthetic `.cx` module.
const SYNTHETIC_MODULE_64K: [SYNTHETIC_BLOCK_16_LOC.len * 128]u8 = blk: {
    var buf: [SYNTHETIC_BLOCK_16_LOC.len * 128]u8 = undefined;
    var i: usize = 0;
    while (i < 128) : (i += 1) {
        const start = i * SYNTHETIC_BLOCK_16_LOC.len;
        @memcpy(buf[start .. start + SYNTHETIC_BLOCK_16_LOC.len], SYNTHETIC_BLOCK_16_LOC);
    }
    break :blk buf;
};
/// Byte offset of the `1_000_000` literal inside function #64 of `SYNTHETIC_MODULE_64K`.
const MID_FUNCTION_EDIT_START: u32 = @intCast(
    64 * SYNTHETIC_BLOCK_16_LOC.len +
        ("/// Computes bounded checksum across a borrowed slice of packet frames.\n" ++
            "pub fn compute_frame_checksum(frames: &[PacketFrame], seed_val: u64) -> Result[u64, FrameError] {\n" ++
            "    let prime_factor: u64 = 0x9E37_79B9_7F4A_7C15;\n" ++
            "    var acc_hash: u64 = seed_val +% ").len,
);
/// End byte offset of the `1_000_000` literal inside function #64 of `SYNTHETIC_MODULE_64K`.
const MID_FUNCTION_EDIT_END: u32 = MID_FUNCTION_EDIT_START + @as(u32, "1_000_000".len);
/// Edited 64 KiB module where function #64's seed offset literal is modified to `2_000_000`.
const SYNTHETIC_MODULE_64K_EDITED: [SYNTHETIC_MODULE_64K.len]u8 = blk: {
    var buf = SYNTHETIC_MODULE_64K;
    buf[MID_FUNCTION_EDIT_START] = '2';
    break :blk buf;
};
/// Function block containing 16 multi-tier Pratt expressions repeated 256 times (`4,096` expressions).
const PRATT_EXPR_CHUNK_16 =
    "pub fn eval_pratt_chunk(x: i64, y: i64, ptr: *i64) -> i64 {\n" ++
    "    let e01 = (x +% y *% 3) << 2 ^ (x -| y *| 5) & 0xFF;\n" ++
    "    let e02 = x |> transform(y) |> finalize[i64]() catch 0;\n" ++
    "    let e03 = not (x < y) and (y >= 0 or x != -1);\n" ++
    "    let e04 = -x + ~y - (*ptr as i64) + (&x).abs();\n" ++
    "    let e05 = alloc[u64](16)[0] as i64 +% (x / 2 % 7);\n" ++
    "    let e06 = try_fetch(x)? |> decode() catch |err| { 0 };\n" ++
    "    let e07 = Card(padding: 8) { Text(val: x); };\n" ++
    "    let e08 = ((x + 1) * (y - 2)) |> clamp(0, 100) catch 42;\n" ++
    "    let e09 = (x | y) & (x ^ 0xDEAD_BEEF) >> 4;\n" ++
    "    let e10 = state.metrics[0].count.max[i64](y) + 1;\n" ++
    "    let e11 = if x > 0 { x +% 10 } else { y -% 10 };\n" ++
    "    let e12 = future_val.await? |> normalize() catch -1;\n" ++
    "    let e13 = (x +| y) * (x -| 1) + (y *% 9);\n" ++
    "    let e14 = Row(gap: 4) { Badge(id: x); };\n" ++
    "    let e15 = (e01 + e02 + e04 + e05) |> sum_all(e08, e09);\n" ++
    "    return e15 + e10 + e11 + e13;\n" ++
    "}\n";
/// Complete Pratt expression benchmark source (`256` functions * `16` complex expressions = `4,096` expressions).
const PRATT_EXPR_MODULE_4096: [PRATT_EXPR_CHUNK_16.len * 256]u8 = blk: {
    @setEvalBranchQuota(500_000);
    var buf: [PRATT_EXPR_CHUNK_16.len * 256]u8 = undefined;
    var i: usize = 0;
    while (i < 256) : (i += 1) {
        const start = i * PRATT_EXPR_CHUNK_16.len;
        @memcpy(buf[start .. start + PRATT_EXPR_CHUNK_16.len], PRATT_EXPR_CHUNK_16);
    }
    break :blk buf;
};

// -------------------------------------- INTERNALS --------------------------------------

/// Shared scratch `TokenBuffer` reused across E2E benchmark iterations.
var shared_e2e_token_buf: ?TokenBuffer = null;
/// Pre-tokenized `TokenBuffer` for the 64 KiB synthetic module (`Parser.parse` benchmark).
var pretokenized_module_64k_buf: ?TokenBuffer = null;
/// Pre-tokenized `TokenBuffer` for the 4,096-expression Pratt benchmark module.
var pretokenized_pratt_4096_buf: ?TokenBuffer = null;
/// Shared scratch `LosslessCstArena` reused across non-incremental benchmark iterations.
var shared_cst_arena: ?LosslessCstArena = null;
/// Shared scratch `AstArena` reused across non-incremental benchmark iterations.
var shared_ast_arena: ?AstArena = null;
/// Persistent state for the incremental re-parse benchmark workload.
var shared_incremental_state: ?IncrementalBenchState = null;

/// Returns a pointer to the pre-tokenized 64 KiB `.cx` `TokenBuffer`, tokenizing once on first use.
fn getOrInitPreTokenizedModule64k(allocator: std.mem.Allocator) !*const TokenBuffer {
    if (pretokenized_module_64k_buf == null) {
        var fresh_buf = TokenBuffer.init(allocator);
        try fresh_buf.tokens.ensureTotalCapacity(allocator, 32_768);
        try fresh_buf.trivia.ensureTotalCapacity(allocator, 32_768);
        var lexer_instance = Lexer.init(&SYNTHETIC_MODULE_64K, FileId.fromInt(0), &fresh_buf, null, null);
        try lexer_instance.tokenize();
        pretokenized_module_64k_buf = fresh_buf;
    }
    return &pretokenized_module_64k_buf.?;
}

/// Returns a pointer to the pre-tokenized 4,096-expression `TokenBuffer`, tokenizing once on first use.
fn getOrInitPreTokenizedPratt4096(allocator: std.mem.Allocator) !*const TokenBuffer {
    if (pretokenized_pratt_4096_buf == null) {
        var fresh_buf = TokenBuffer.init(allocator);
        try fresh_buf.tokens.ensureTotalCapacity(allocator, 131_072);
        try fresh_buf.trivia.ensureTotalCapacity(allocator, 65_536);
        var lexer_instance = Lexer.init(&PRATT_EXPR_MODULE_4096, FileId.fromInt(0), &fresh_buf, null, null);
        try lexer_instance.tokenize();
        pretokenized_pratt_4096_buf = fresh_buf;
    }
    return &pretokenized_pratt_4096_buf.?;
}

/// Returns a pointer to the reusable scratch `TokenBuffer` for E2E `parseSource` benchmarks.
fn getOrInitReusableTokenBuffer(allocator: std.mem.Allocator) !*TokenBuffer {
    if (shared_e2e_token_buf == null) {
        var fresh_buf = TokenBuffer.init(allocator);
        try fresh_buf.tokens.ensureTotalCapacity(allocator, 32_768);
        try fresh_buf.trivia.ensureTotalCapacity(allocator, 32_768);
        shared_e2e_token_buf = fresh_buf;
    }
    const buf_ptr = &shared_e2e_token_buf.?;
    buf_ptr.tokens.shrinkRetainingCapacity(0);
    buf_ptr.trivia.shrinkRetainingCapacity(0);
    return buf_ptr;
}

/// Resets and returns the shared `LosslessCstArena` and `AstArena` with pre-warmed capacity.
fn getOrInitReusableSyntaxArenas(
    allocator: std.mem.Allocator,
) !struct { cst: *LosslessCstArena, ast: *AstArena } {
    if (shared_cst_arena == null) {
        var fresh_cst = LosslessCstArena.init(allocator);
        try fresh_cst.nodes.ensureTotalCapacity(allocator, 131_072);
        shared_cst_arena = fresh_cst;
    }
    if (shared_ast_arena == null) {
        var fresh_ast = AstArena.init(allocator);
        try fresh_ast.nodes.ensureTotalCapacity(allocator, 65_536);
        try fresh_ast.ast_to_cst.ensureTotalCapacity(allocator, 65_536);
        try fresh_ast.extra_data.ensureTotalCapacity(allocator, 65_536);
        shared_ast_arena = fresh_ast;
    }
    const cst_ptr = &shared_cst_arena.?;
    const ast_ptr = &shared_ast_arena.?;
    cst_ptr.nodes.shrinkRetainingCapacity(0);
    cst_ptr.parse_stack.shrinkRetainingCapacity(0);
    cst_ptr.has_parse_errors = false;
    ast_ptr.nodes.shrinkRetainingCapacity(0);
    ast_ptr.ast_to_cst.shrinkRetainingCapacity(0);
    ast_ptr.extra_data.shrinkRetainingCapacity(0);
    return .{ .cst = cst_ptr, .ast = ast_ptr };
}

/// Returns the pre-initialized `IncrementalBenchState`, running initial `parseSource` on first use.
fn getOrInitIncrementalState(allocator: std.mem.Allocator) !*IncrementalBenchState {
    if (shared_incremental_state == null) {
        var state = IncrementalBenchState{
            .token_buf = TokenBuffer.init(allocator),
            .cst_arena = LosslessCstArena.init(allocator),
            .ast_arena = AstArena.init(allocator),
            .is_edited_active = false,
        };
        _ = try corex.parseSource(
            &SYNTHETIC_MODULE_64K,
            FileId.fromInt(0),
            &state.token_buf,
            &state.cst_arena,
            &state.ast_arena,
            null,
            null,
        );
        shared_incremental_state = state;
    }
    return &shared_incremental_state.?;
}

/// Benchmarks pure `Parser.parse` (CST + AST construction) on a pre-tokenized 64 KiB (`2,048` LOC) `.cx` module.
fn benchParserParsePreTokenized64k(allocator: std.mem.Allocator) !usize {
    const arenas = try getOrInitReusableSyntaxArenas(allocator);

    var parser_instance = Parser.init(
        &SYNTHETIC_MODULE_64K,
        FileId.fromInt(0),
        try getOrInitPreTokenizedModule64k(allocator),
        arenas.cst,
        arenas.ast,
        null,
        null,
    );
    _ = try parser_instance.parse();
    std.mem.doNotOptimizeAway(arenas.cst.countNodes() + arenas.ast.countNodes());

    return arenas.cst.countNodes() * @sizeOf(syntax.CstNodeRecord) +
        arenas.ast.countNodes() * @sizeOf(syntax.AstNode) +
        arenas.ast.extra_data.items.len * @sizeOf(u32);
}

/// Benchmarks end-to-end `parseSource` (lexing + CST + AST lowering) on a 64 KiB (`2,048` LOC) `.cx` module.
fn benchParseSourceEndToEnd64k(allocator: std.mem.Allocator) !usize {
    const token_buf = try getOrInitReusableTokenBuffer(allocator);
    const arenas = try getOrInitReusableSyntaxArenas(allocator);

    _ = try corex.parseSource(
        &SYNTHETIC_MODULE_64K,
        FileId.fromInt(0),
        token_buf,
        arenas.cst,
        arenas.ast,
        null,
        null,
    );
    std.mem.doNotOptimizeAway(arenas.cst.countNodes() + arenas.ast.countNodes());

    return token_buf.countTokens() * @sizeOf(syntax.TokenRecord) +
        token_buf.trivia.items.len * @sizeOf(syntax.TriviaPiece) +
        arenas.cst.countNodes() * @sizeOf(syntax.CstNodeRecord) +
        arenas.ast.countNodes() * @sizeOf(syntax.AstNode);
}

/// Benchmarks 15-tier Pratt expression parsing across 4,096 complex expressions (`|>`, `catch`, generics, views).
fn benchPrattExpressions4096(allocator: std.mem.Allocator) !usize {
    const arenas = try getOrInitReusableSyntaxArenas(allocator);

    var parser_instance = Parser.init(
        &PRATT_EXPR_MODULE_4096,
        FileId.fromInt(0),
        try getOrInitPreTokenizedPratt4096(allocator),
        arenas.cst,
        arenas.ast,
        null,
        null,
    );
    _ = try parser_instance.parse();
    std.mem.doNotOptimizeAway(arenas.cst.countNodes() + arenas.ast.countNodes());

    return arenas.cst.countNodes() * @sizeOf(syntax.CstNodeRecord) +
        arenas.ast.countNodes() * @sizeOf(syntax.AstNode) +
        arenas.ast.extra_data.items.len * @sizeOf(u32);
}

/// Benchmarks `reparseIncremental` for a single-function edit inside a 128-function (`64` KiB) `.cx` module.
fn benchReparseIncrementalSingleFn64k(allocator: std.mem.Allocator) !usize {
    const state = try getOrInitIncrementalState(allocator);
    const new_source: []const u8 = if (state.is_edited_active)
        &SYNTHETIC_MODULE_64K
    else
        &SYNTHETIC_MODULE_64K_EDITED;
    state.is_edited_active = !state.is_edited_active;

    const stats = try corex.reparseIncremental(
        new_source,
        FileId.fromInt(0),
        .{
            .start_byte = MID_FUNCTION_EDIT_START,
            .old_end_byte = MID_FUNCTION_EDIT_END,
            .new_end_byte = MID_FUNCTION_EDIT_END,
        },
        &state.token_buf,
        &state.cst_arena,
        &state.ast_arena,
        null,
        null,
    );
    std.debug.assert(stats.is_fast_splice);
    std.mem.doNotOptimizeAway(stats.reused_prefix_items + stats.reused_suffix_items);

    return state.cst_arena.countNodes() * @sizeOf(syntax.CstNodeRecord) +
        state.ast_arena.countNodes() * @sizeOf(syntax.AstNode);
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 2 parser benchmark suite and prints the monochrome Unicode table to `stdout`.
pub fn main(init: std.process.Init) !void {
    defer {
        if (shared_e2e_token_buf) |*buf_ref| {
            buf_ref.deinit();
            shared_e2e_token_buf = null;
        }
        if (pretokenized_module_64k_buf) |*buf_ref| {
            buf_ref.deinit();
            pretokenized_module_64k_buf = null;
        }
        if (pretokenized_pratt_4096_buf) |*buf_ref| {
            buf_ref.deinit();
            pretokenized_pratt_4096_buf = null;
        }
        if (shared_cst_arena) |*cst_ref| {
            cst_ref.deinit();
            shared_cst_arena = null;
        }
        if (shared_ast_arena) |*ast_ref| {
            ast_ref.deinit();
            shared_ast_arena = null;
        }
        if (shared_incremental_state) |*inc_ref| {
            inc_ref.deinit();
            shared_incremental_state = null;
        }
    }

    const results = try corex.bench_harness.runSuite(
        init.gpa,
        init.io,
        &[_]BenchCase{
            .{
                .name = "Parser.parse (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchParserParsePreTokenized64k,
            },
            .{
                .name = "parseSource E2E (64 KiB lex + CST + AST)",
                .run_fn = benchParseSourceEndToEnd64k,
            },
            .{
                .name = "Pratt expression parser (4,096 complex exprs)",
                .run_fn = benchPrattExpressions4096,
            },
            .{
                .name = "reparseIncremental (1-fn edit in 64 KiB module)",
                .run_fn = benchReparseIncrementalSingleFn64k,
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
        "Phase 2 Resilient LL(k) + Pratt Parser Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, results);
    try stdout_writer.interface.flush();
}

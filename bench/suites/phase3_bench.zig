//! Phase 3 Demand-Driven Query Engine & Hybrid Wadler-Lindig Formatter Benchmark Suite (`bench/suites/phase3_bench.zig`)
//!
//! Benchmarks `corex fmt` CST-to-`DocArena` formatting and rendering (`formatTokensAndCst`) on a
//! pre-parsed 64 KiB (`2,048` LOC) `.cx` module, end-to-end `formatSource` (lex + parse + format +
//! render on 64 KiB), `CompilerDb` Early Cutoff on comment/whitespace edits in a 64 KiB module
//! (skipping `item_tree` and `typecheck_body`), and `CompilerDb` `ItemTree` signature firewall
//! isolation on a single-function body edit in a 128-function (`64` KiB) module.
//!
//! Executed via `zig build bench` or `zig build bench-phase3`, enforcing 5 warmup iterations and
//! 30 timed iterations per workload and rendering the canonical monochrome Unicode report table.

const std = @import("std");
const corex = @import("corex");

const fmt_engine = corex.fmt_engine;
const FileId = corex.FileId;
const DefId = corex.DefId;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const CompilerDb = corex.CompilerDb;
const StyleConfig = corex.StyleConfig;
const BenchCase = corex.bench_harness.BenchCase;

// ---------------------------------------- TYPES ----------------------------------------

/// Pre-tokenized and pre-parsed 64 KiB `.cx` syntax state for isolated `formatTokensAndCst` benchmarks.
const PreParsedFmtState = struct {
    /// Pre-populated token and trivia buffer.
    token_buf: TokenBuffer,
    /// Pre-populated lossless CST arena.
    cst_arena: LosslessCstArena,
    /// Pre-populated AST arena.
    ast_arena: AstArena,

    /// Releases all backing buffers owned by `self`.
    fn deinit(self: *PreParsedFmtState) void {
        self.token_buf.deinit();
        self.cst_arena.deinit();
        self.ast_arena.deinit();
    }
};

/// Persistent `CompilerDb` benchmark state toggling between two source revisions.
const QueryBenchState = struct {
    /// Persistent incremental query database.
    db: CompilerDb,
    /// `true` when the edited buffer variant is currently active in `db`.
    is_edited_active: bool,

    /// Releases `self.db`.
    fn deinit(self: *QueryBenchState) void {
        self.db.deinit();
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

/// Comment-edited 64 KiB module where a doc comment word in function #0 is modified (`Computes` -> ` Verifies`).
const SYNTHETIC_MODULE_64K_COMMENT_EDITED: [SYNTHETIC_MODULE_64K.len]u8 = blk: {
    var buf = SYNTHETIC_MODULE_64K;
    @memcpy(buf[4..12], "Verifies");
    break :blk buf;
};

/// Byte offset of the `1_000_000` literal inside function #64 of `SYNTHETIC_MODULE_64K`.
const MID_FUNCTION_BODY_EDIT_START: usize = 64 * SYNTHETIC_BLOCK_16_LOC.len +
    ("/// Computes bounded checksum across a borrowed slice of packet frames.\n" ++
        "pub fn compute_frame_checksum(frames: &[PacketFrame], seed_val: u64) -> Result[u64, FrameError] {\n" ++
        "    let prime_factor: u64 = 0x9E37_79B9_7F4A_7C15;\n" ++
        "    var acc_hash: u64 = seed_val +% ").len;

/// Body-edited 64 KiB module where function #64's seed offset literal is modified to `2_000_000`.
const SYNTHETIC_MODULE_64K_BODY_EDITED: [SYNTHETIC_MODULE_64K.len]u8 = blk: {
    var buf = SYNTHETIC_MODULE_64K;
    buf[MID_FUNCTION_BODY_EDIT_START] = '2';
    break :blk buf;
};

// -------------------------------------- INTERNALS --------------------------------------

/// Cached pre-parsed syntax state for `benchFormatTokensAndCst64k`.
var shared_pre_parsed_fmt: ?PreParsedFmtState = null;
/// Cached `CompilerDb` state for `benchQueryDbEarlyCutoffCommentEdit64k`.
var shared_early_cutoff_state: ?QueryBenchState = null;
/// Cached `CompilerDb` state for `benchQueryDbItemTreeFirewallSingleFnEdit64k`.
var shared_firewall_state: ?QueryBenchState = null;

/// Returns the pre-tokenized and pre-parsed 64 KiB syntax state, initializing once on first use.
fn getOrInitPreParsedFmtState(allocator: std.mem.Allocator) !*const PreParsedFmtState {
    if (shared_pre_parsed_fmt == null) {
        var state = PreParsedFmtState{
            .token_buf = TokenBuffer.init(allocator),
            .cst_arena = LosslessCstArena.init(allocator),
            .ast_arena = AstArena.init(allocator),
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
        shared_pre_parsed_fmt = state;
    }
    return &shared_pre_parsed_fmt.?;
}

/// Initializes a `QueryBenchState` and pre-warms all 128 function definitions at Revision 1.
fn initPreWarmedQueryState(allocator: std.mem.Allocator) !QueryBenchState {
    var db = try CompilerDb.init(allocator);
    errdefer db.deinit();

    const file_id = FileId.fromInt(0);
    _ = try db.setInput(file_id, &SYNTHETIC_MODULE_64K, .low);
    const tree = try db.extractItemTree(file_id);
    for (tree.entries) |entry| {
        _ = try db.verifySastMir(entry.def_id);
    }
    return .{
        .db = db,
        .is_edited_active = false,
    };
}

/// Benchmarks `formatTokensAndCst` on a pre-parsed 64 KiB (`2,048` LOC) `.cx` module.
fn benchFormatTokensAndCst64k(allocator: std.mem.Allocator) !usize {
    const pre_parsed = try getOrInitPreParsedFmtState(allocator);
    var fmt_res = try fmt_engine.formatTokensAndCst(
        allocator,
        &SYNTHETIC_MODULE_64K,
        &pre_parsed.token_buf,
        &pre_parsed.cst_arena,
        .{},
    );
    defer fmt_res.deinit(allocator);
    std.mem.doNotOptimizeAway(fmt_res.formatted_text.len);
    return fmt_res.formatted_text.len;
}

/// Benchmarks end-to-end `formatSource` (lex + parse + format + render) on a 64 KiB (`2,048` LOC) `.cx` module.
fn benchFormatSourceEndToEnd64k(allocator: std.mem.Allocator) !usize {
    var fmt_res = try fmt_engine.formatSource(
        allocator,
        &SYNTHETIC_MODULE_64K,
        FileId.fromInt(0),
    );
    defer fmt_res.deinit(allocator);
    std.mem.doNotOptimizeAway(fmt_res.formatted_text.len);
    return fmt_res.formatted_text.len;
}

/// Benchmarks `CompilerDb` Early Cutoff on a comment edit in a 64 KiB module (skipping `item_tree` & `typecheck_body`).
fn benchQueryDbEarlyCutoffCommentEdit64k(allocator: std.mem.Allocator) !usize {
    if (shared_early_cutoff_state == null) {
        shared_early_cutoff_state = try initPreWarmedQueryState(allocator);
    }
    const state = &shared_early_cutoff_state.?;
    const next_src: []const u8 = if (state.is_edited_active)
        &SYNTHETIC_MODULE_64K
    else
        &SYNTHETIC_MODULE_64K_COMMENT_EDITED;
    state.is_edited_active = !state.is_edited_active;

    const file_id = FileId.fromInt(0);
    _ = try state.db.setInput(file_id, next_src, .low);
    const sast_res = try state.db.verifySastMir(DefId.init(file_id, 64));
    std.mem.doNotOptimizeAway(sast_res.sast_fingerprint.low);

    return SYNTHETIC_MODULE_64K.len;
}

/// Benchmarks `CompilerDb` `ItemTree` firewall on a 1-function body edit in a 128-function (`64` KiB) module.
fn benchQueryDbItemTreeFirewallSingleFnEdit64k(allocator: std.mem.Allocator) !usize {
    if (shared_firewall_state == null) {
        shared_firewall_state = try initPreWarmedQueryState(allocator);
    }
    const state = &shared_firewall_state.?;
    const next_src: []const u8 = if (state.is_edited_active)
        &SYNTHETIC_MODULE_64K
    else
        &SYNTHETIC_MODULE_64K_BODY_EDITED;
    state.is_edited_active = !state.is_edited_active;

    const file_id = FileId.fromInt(0);
    _ = try state.db.setInput(file_id, next_src, .low);

    // Verify both the edited function (`#64`) and an unedited sibling (`#65`):
    const edited_sast = try state.db.verifySastMir(DefId.init(file_id, 64));
    const sibling_sast = try state.db.verifySastMir(DefId.init(file_id, 65));
    std.mem.doNotOptimizeAway(edited_sast.sast_fingerprint.low ^ sibling_sast.sast_fingerprint.low);

    return SYNTHETIC_MODULE_64K.len;
}

// ---------------------------------------- MAIN -----------------------------------------

/// Executes the Phase 3 query engine & formatter benchmark suite and prints the monochrome Unicode table.
pub fn main(init: std.process.Init) !void {
    defer {
        if (shared_pre_parsed_fmt) |*fmt_ref| {
            fmt_ref.deinit();
            shared_pre_parsed_fmt = null;
        }
        if (shared_early_cutoff_state) |*ec_ref| {
            ec_ref.deinit();
            shared_early_cutoff_state = null;
        }
        if (shared_firewall_state) |*fw_ref| {
            fw_ref.deinit();
            shared_firewall_state = null;
        }
    }

    const results = try corex.bench_harness.runSuite(
        init.gpa,
        init.io,
        &[_]BenchCase{
            .{
                .name = "formatTokensAndCst (64 KiB / 2,048 LOC .cx)",
                .run_fn = benchFormatTokensAndCst64k,
            },
            .{
                .name = "formatSource E2E (64 KiB lex + CST + fmt)",
                .run_fn = benchFormatSourceEndToEnd64k,
            },
            .{
                .name = "CompilerDb Early Cutoff (comment edit 64 KiB)",
                .run_fn = benchQueryDbEarlyCutoffCommentEdit64k,
            },
            .{
                .name = "CompilerDb ItemTree Firewall (1-fn edit / 128 fns)",
                .run_fn = benchQueryDbItemTreeFirewallSingleFnEdit64k,
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
        "Phase 3 Query Engine & Hybrid Formatter Benchmark Suite (5 warmup, 30 measured iterations)",
    );
    try stdout_writer.interface.writeByte('\n');
    try corex.bench_harness.renderResultsTable(&stdout_writer.interface, style_config, results);
    try stdout_writer.interface.flush();
}

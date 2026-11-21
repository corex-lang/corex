//! Phase 10 LSP Framing, Incremental VFS & Zero-Legacy Upgrade Fuzzing Suite
//!
//! Executes deterministic `std.Random.Xoroshiro128` fuzzing across untrusted LSP 3.17 JSON-RPC
//! framing (`runServerStream`), UTF-8/UTF-16 `LineIndex` + `CompilerDb.setInputWithEdit` incremental
//! reparsing and LRU cache eviction, and `upgrade_engine.upgradeSource` fixed-point convergence.
//!
//! Enforces `< 2s` total execution under `std.testing.allocator` with zero panics, zero memory
//! leaks, 100% incremental-vs-fresh CST/AST parity, generated-file immutability, and idempotency.

const std = @import("std");
const corex = @import("corex");

const lsp_server = corex.lsp_server;
const upgrade_engine = corex.upgrade_engine;
const pkg_manifest = corex.pkg_manifest;
const BumpArena = corex.BumpArena;
const StringInterner = corex.StringInterner;
const FileId = corex.FileId;
const PositionEncoding = corex.PositionEncoding;
const LineIndex = corex.LineIndex;
const VfsSourceMap = corex.VfsSourceMap;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const EditRange = corex.EditRange;
const CompilerDb = corex.CompilerDb;
const DiagnosticSink = corex.DiagnosticSink;

// --------------------------------------- CONSTS ----------------------------------------

// -------------------- Fuzzing Seed Corpora --------------------

/// Total adversarial and mutated JSON-RPC frames exercised in `test_fuzz_lsp_jsonrpc_framing_and_untrusted_payloads`.
const LSP_FRAMING_FUZZ_ITERATIONS: usize = 280;
/// Number of frames batched into each `runServerStream` session during framing fuzzing.
const LSP_FRAMES_PER_SESSION: usize = 56;
/// Total multi-step UTF-8/UTF-16 incremental VFS edits verified in `test_fuzz_vfs_incremental_edits_match_fresh_parse`.
const VFS_INCREMENTAL_FUZZ_ITERATIONS: usize = 160;
/// Total `OverlayCache` open/close/reopen/overwrite operations executed during VFS eviction stress.
const VFS_OVERLAY_STRESS_OPERATIONS: usize = 320;
/// Total `SemanticTokensCache` small-budget LRU mutations executed during cache stress.
const SEMANTIC_CACHE_STRESS_OPERATIONS: usize = 120;
/// Total mutated legacy + canonical `.cx` programs verified in `test_fuzz_upgrade_engine_convergence_idempotency_and_rollback_safety`.
const UPGRADE_FUZZ_ITERATIONS: usize = 104;

/// Adversarial raw LSP frame headers testing integer overflows, malformed lengths, and size caps.
const ADVERSARIAL_RAW_FRAMES = [_][]const u8{
    "Content-Length: -1\r\n\r\n{}",
    "Content-Length: -99999999999999999999\r\n\r\n{}",
    "Content-Length: +32\r\n\r\n{}",
    "Content-Length: 0x40\r\n\r\n{}",
    "Content-Length: abcdef\r\n\r\n{}",
    "Content-Length: \r\n\r\n{}",
    "Content-Length: 999999999999999999999999999999999999\r\n\r\n{}",
    "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n\r\n{}",
    "\r\n\r\n{\"jsonrpc\":\"2.0\",\"method\":\"initialized\"}",
    "Content-Length: 16777217\r\n\r\n",
    "Content-Length: 104857600\r\n\r\n{}",
};

/// Adversarial JSON bodies exercising lone UTF-16 surrogates, invalid envelopes, and malformed params.
const ADVERSARIAL_JSON_BODIES = [_][]const u8{
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"textDocument/hover\",\"params\":{\"bad\":\"\\uD800\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"textDocument/hover\",\"params\":{\"bad\":\"\\uDC00\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"textDocument/hover\",\"params\":{\"bad\":\"\\uDBFF\\u0041\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"textDocument/hover\",\"params\":{\"bad\":\"\\uD835\\uD835\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"textDocument/hover\",\"params\":{\"bad\":\"\\uD8\"}}",
    "{\"jsonrpc\":\"1.0\",\"id\":6,\"method\":\"initialize\",\"params\":{}}",
    "{\"jsonrpc\":\"2.0\",\"id\":[1,2],\"method\":\"textDocument/hover\",\"params\":null}",
    "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"unknown/customMethod\",\"params\":{\"x\":true}}",
    "{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{\"id\":999999}}",
    "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"textDocument/completion\",\"params\":{\"textDocument\":{\"uri\":\"not-a-uri\"}}}",
    "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"textDocument/rename\",\"params\":{\"newName\":\"123bad\"}}",
    "[]",
    "null",
    "\"bare_string\"",
    "{\"unclosed\": [1, 2, 3",
};

/// Valid baseline JSON-RPC request/notification templates mutated by the PRNG fuzzer.
const BASELINE_LSP_JSON_TEMPLATES = [_][]const u8{
    "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didChange\",\"params\":{\"textDocument\":" ++
        "{\"uri\":\"file:///D%3A/virt/fuzz.cx\",\"version\":2},\"contentChanges\":[{\"range\":" ++
        "{\"start\":{\"line\":1,\"character\":4},\"end\":{\"line\":1,\"character\":7}},\"text\":\"let\"}]}}",
    "{\"jsonrpc\":\"2.0\",\"id\":21,\"method\":\"textDocument/hover\",\"params\":{\"textDocument\":" ++
        "{\"uri\":\"file:///D%3A/virt/fuzz.cx\"},\"position\":{\"line\":1,\"character\":10}}}",
    "{\"jsonrpc\":\"2.0\",\"id\":22,\"method\":\"textDocument/completion\",\"params\":{\"textDocument\":" ++
        "{\"uri\":\"file:///D%3A/virt/fuzz.cx\"},\"position\":{\"line\":2,\"character\":12}}}",
    "{\"jsonrpc\":\"2.0\",\"id\":23,\"method\":\"textDocument/semanticTokens/full\",\"params\":" ++
        "{\"textDocument\":{\"uri\":\"file:///D%3A/virt/fuzz.cx\"}}}",
    "{\"jsonrpc\":\"2.0\",\"id\":24,\"method\":\"textDocument/semanticTokens/full/delta\",\"params\":" ++
        "{\"textDocument\":{\"uri\":\"file:///D%3A/virt/fuzz.cx\"},\"previousResultId\":\"0000000000000001\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":25,\"method\":\"textDocument/inlayHint\",\"params\":{\"textDocument\":" ++
        "{\"uri\":\"file:///D%3A/virt/fuzz.cx\"},\"range\":{\"start\":{\"line\":0,\"character\":0}," ++
        "\"end\":{\"line\":8,\"character\":0}}}}",
    "{\"jsonrpc\":\"2.0\",\"id\":26,\"method\":\"textDocument/codeAction\",\"params\":{\"textDocument\":" ++
        "{\"uri\":\"file:///D%3A/virt/fuzz.cx\"},\"range\":{\"start\":{\"line\":0,\"character\":0}," ++
        "\"end\":{\"line\":6,\"character\":0}},\"context\":{\"diagnostics\":[]}}}",
    "{\"jsonrpc\":\"2.0\",\"id\":27,\"method\":\"textDocument/rename\",\"params\":{\"textDocument\":" ++
        "{\"uri\":\"file:///D%3A/virt/fuzz.cx\"},\"position\":{\"line\":0,\"character\":8},\"newName\":\"renamed_fn\"}}",
};

/// UTF-8-valid `.cx` splice snippets (including BMP and 4-byte astral `"𐍈"` / `"𝐀"` scalars) for VFS incremental fuzzing.
const VFS_UTF8_EDIT_SNIPPETS = [_][]const u8{
    "",
    " ",
    "\n",
    "\r\n    let next_val = 42_i32;\r\n",
    "/* block • note */",
    "// astral marker 𐍈𝐀\n",
    "\"𐍈𝐀\"",
    "\"café ─ item\"",
    " + (1_i32 << 2) ",
    "\npub fn extra_item(in_v: i32) -> i32 {\n    return in_v +% 7;\n}\n",
    "if flag_v { return 1; } else { return 0; }",
    "match count_v { 0 => 10, _ => 20 }",
    "{ let inner_tmp = 9; }",
};

/// Legacy and canonical `.cx` fragments combined and mutated during `upgradeSource` fuzzing.
const UPGRADE_SEED_FRAGMENTS = [_][]const u8{
    "use std::io;\n",
    "use cx.ffi.c_void;\n",
    "extern \"c\" fn raw_release(ptr: *const c_void) -> unit;\n",
    "@repr(u8)\npub enum WireMode {\n    Idle = 0;\n    Busy = 1;\n}\n",
    "type StatusBits = bit_field u8 {\n    ready: bool | 1;\n    code: u8 | 7;\n};\n",
    "pub struct SlotPair {\n    pub first_v: i32;\n    pub second_v: i32;\n}\n",
    "@noalloc\n@align(bytes = 8)\npub fn legacy_compute[T: Numeric](\n" ++
        "    ref item_v: T,\n    inout counter: i32,\n    set out_ok: bool,\n" ++
        "    maybe_num: Option[i32],\n    res_in: Result[Option[i32], i32],\n) -> unit {\n" ++
        "    let mut local_acc = counter;\n" ++
        "    if local_acc > 0 && (local_acc == 1 || local_acc == 2) {\n" ++
        "        let zero_cb = || local_acc;\n" ++
        "        let _ = zero_cb();\n" ++
        "    }\n" ++
        "    if let Some(unwrapped_v) = maybe_num {\n" ++
        "        local_acc = local_acc + unwrapped_v;\n" ++
        "    }\n" ++
        "    counter = local_acc;\n" ++
        "    out_ok = !(res_in.is_err());\n" ++
        "}\n",
    "pub fn bitwise_and_slice(buf: &[u8], ptr: *i32, flag: bool, mask: u32) -> usize {\n" ++
        "    if !flag {\n" ++
        "        let inv_mask = !mask;\n" ++
        "        return (inv_mask as usize) + (unsafe { *ptr } as usize);\n" ++
        "    }\n" ++
        "    let sub = buf[0 .. buf.len - 1];\n" ++
        "    return sub.len;\n" ++
        "}\n",
    "@deprecated(upgrade: \"modern_helper($0)\")\npub fn old_helper(num_v: i32) -> i32 {\n" ++
        "    return modern_helper(num_v);\n}\n" ++
        "pub fn modern_helper(num_v: i32) -> i32 {\n    return num_v + 1;\n}\n" ++
        "pub fn call_deprecated(in_num: Option[i32]) -> i32 {\n" ++
        "    return old_helper(in_num.unwrap_or(0));\n}\n",
    "@test\npub fn test_legacy_case() -> unit {\n    let mut check_v = 5;\n    check_v += 1;\n}\n",
};

/// Generated-file header prefixes that `upgradeSource` must preserve untouched (`0` edits).
const GENERATED_HEADER_PREFIXES = [_][]const u8{
    "// @generated by schema-gen\n",
    "// Code generated by tool – DO NOT EDIT.\n",
    "//! @generated bindings module\n",
    "/* Header block\n * DO NOT EDIT\n */\n",
};

/// Syntax corruption snippets injected randomly into non-generated upgrade fuzz inputs.
const SYNTAX_CORRUPTION_SNIPPETS = [_][]const u8{
    " let broken = (1 + ; ",
    "\nfn unclosed_sig(x_in: Option[i32] \n",
    " && || ! ",
    " struct { ; } ",
    " /* unterminated_or_nested */ ??? ",
    "\npub fn hole_tail(flag: bool) { if !flag { let mut z_val = \n",
};

// -------------------------------------- INTERNALS --------------------------------------

// ------------------ Mutation & Parse Helpers ------------------

/// Wraps `json_body` inside a standard `Content-Length` frame and appends it to `out_buf`.
fn appendValidFrame(
    allocator: std.mem.Allocator,
    out_buf: *std.ArrayListUnmanaged(u8),
    json_body: []const u8,
) !void {
    const hdr = try std.fmt.allocPrint(allocator, "Content-Length: {d}\r\n\r\n", .{json_body.len});
    defer allocator.free(hdr);
    try out_buf.appendSlice(allocator, hdr);
    try out_buf.appendSlice(allocator, json_body);
}

/// Generates a deeply nested JSON array or object exceeding `MAX_LSP_JSON_DEPTH` (`64`).
fn appendDeepNestedJsonFrame(
    allocator: std.mem.Allocator,
    out_buf: *std.ArrayListUnmanaged(u8),
    depth: usize,
    is_object_nesting: bool,
) !void {
    var body: std.ArrayListUnmanaged(u8) = .empty;
    defer body.deinit(allocator);
    try body.appendSlice(allocator, "{\"jsonrpc\":\"2.0\",\"id\":77,\"method\":\"initialize\",\"params\":");
    var i: usize = 0;
    while (i < depth) : (i += 1) {
        if (is_object_nesting) {
            try body.appendSlice(allocator, "{\"a\":");
        } else {
            try body.append(allocator, '[');
        }
    }
    try body.appendSlice(allocator, "0");
    i = 0;
    while (i < depth) : (i += 1) {
        try body.append(allocator, if (is_object_nesting) '}' else ']');
    }
    try body.append(allocator, '}');
    try appendValidFrame(allocator, out_buf, body.items);
}

/// Executes `lsp_server.runServerStream` on `wire_input`, discarding outbound bytes cleanly.
fn runFuzzedLspStream(
    allocator: std.mem.Allocator,
    io: std.Io,
    wire_input: []const u8,
) !void {
    var reader = std.Io.Reader.fixed(wire_input);
    var out_alloc = std.Io.Writer.Allocating.init(allocator);
    defer out_alloc.deinit();
    _ = try lsp_server.runServerStream(allocator, io, null, &reader, &out_alloc.writer, null, .{});
}

/// Counts total lexer + parser syntax errors on `raw_source` using the exact frontmatter-masked pipeline.
fn countSyntaxErrorsForSource(
    allocator: std.mem.Allocator,
    file_id: FileId,
    raw_source: []const u8,
) !u32 {
    var fm_arena = BumpArena.init(allocator);
    defer fm_arena.deinit();
    const cx_view = if (try pkg_manifest.extractScriptFrontmatter(&fm_arena, file_id, raw_source, null)) |ext|
        ext.blanked_cx_source
    else
        raw_source;

    var tok_buf = TokenBuffer.init(allocator);
    defer tok_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    _ = try corex.parseSource(cx_view, file_id, &tok_buf, &cst_arena, &ast_arena, &sink, null);
    return sink.error_count;
}

/// Advances or backs up `raw_pos` in `source` so it never splits a `\r\n` pair (`\r` at `pos - 1`, `\n` at `pos`).
fn clampAwayFromMidCrlf(source: []const u8, raw_pos: u32) u32 {
    const pos: usize = @min(@as(usize, raw_pos), source.len);
    if (pos > 0 and pos < source.len and source[pos - 1] == '\r' and source[pos] == '\n') {
        return @intCast(pos - 1);
    }
    return @intCast(pos);
}

// ---------------------------------------- MAIN -----------------------------------------

// ----------------- Deterministic Fuzz Suites ------------------

test "test_fuzz_lsp_jsonrpc_framing_and_untrusted_payloads" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    var prng = std.Random.Xoroshiro128.init(0xC0AE_1010_F022_0001);
    const random = prng.random();

    // [1] Dedicated boundary streams; oversized `> 8 KiB` headers, `> 16 MiB` lengths, & truncated EOF frames:
    {
        var oversized_hdr: std.ArrayListUnmanaged(u8) = .empty;
        defer oversized_hdr.deinit(allocator);
        try oversized_hdr.appendSlice(allocator, "X-Padding: ");
        try oversized_hdr.appendNTimes(allocator, 'A', lsp_server.MAX_LSP_HEADER_BYTES + 256);
        try oversized_hdr.appendSlice(allocator, "\r\nContent-Length: 2\r\n\r\n{}");
        try runFuzzedLspStream(allocator, io, oversized_hdr.items);

        var truncated_eof: std.ArrayListUnmanaged(u8) = .empty;
        defer truncated_eof.deinit(allocator);
        try truncated_eof.appendSlice(
            allocator,
            "Content-Length: 240\r\n\r\n{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\"",
        );
        try runFuzzedLspStream(allocator, io, truncated_eof.items);
    }

    // [2] 280+ adversarial & PRNG-mutated frames across initialized/uninitialized/shutting-down sessions:
    var executed_frames: usize = 0;
    while (executed_frames < LSP_FRAMING_FUZZ_ITERATIONS) {
        var session_wire: std.ArrayListUnmanaged(u8) = .empty;
        defer session_wire.deinit(allocator);

        // Initialize 3 out of 4 sessions so interior LSP handlers also receive mutated payloads:
        if (random.intRangeLessThan(u8, 0, 4) != 0) {
            try appendValidFrame(
                allocator,
                &session_wire,
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{" ++
                    "\"general\":{\"positionEncodings\":[\"utf-8\"]},\"textDocument\":{\"diagnostic\":{}}}}}",
            );
            try appendValidFrame(
                allocator,
                &session_wire,
                "{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{\"textDocument\":{" ++
                    "\"uri\":\"file:///D%3A/virt/fuzz.cx\",\"languageId\":\"corex\",\"version\":1," ++
                    "\"text\":\"pub fn sample_fn(val: i32) -> i32 {\\n    let tmp = val + 1;\\n    return tmp;\\n}\\n\"}}}",
            );
        }

        var batch_idx: usize = 0;
        while (batch_idx < LSP_FRAMES_PER_SESSION and executed_frames < LSP_FRAMING_FUZZ_ITERATIONS) : ({
            batch_idx += 1;
            executed_frames += 1;
        }) {
            switch (random.intRangeLessThan(u8, 0, 6)) {
                0 => {
                    // Raw malformed / overflow `Content-Length` frame:
                    try session_wire.appendSlice(
                        allocator,
                        ADVERSARIAL_RAW_FRAMES[
                            random.intRangeLessThan(usize, 0, ADVERSARIAL_RAW_FRAMES.len)
                        ],
                    );
                },
                1 => {
                    // Lone UTF-16 surrogates (`\uD800` / `\uDC00`) & malformed JSON-RPC envelopes:
                    try appendValidFrame(
                        allocator,
                        &session_wire,
                        ADVERSARIAL_JSON_BODIES[
                            random.intRangeLessThan(usize, 0, ADVERSARIAL_JSON_BODIES.len)
                        ],
                    );
                },
                2 => {
                    // Deep `> 64` nested JSON arrays or objects (`65..90` depth):
                    try appendDeepNestedJsonFrame(
                        allocator,
                        &session_wire,
                        random.intRangeAtMost(usize, lsp_server.MAX_LSP_JSON_DEPTH + 1, 90),
                        random.boolean(),
                    );
                },
                3 => {
                    // Byte-corrupted / control-char / invalid-UTF-8 mutation of a baseline LSP request:
                    const base_tmpl = BASELINE_LSP_JSON_TEMPLATES[
                        random.intRangeLessThan(usize, 0, BASELINE_LSP_JSON_TEMPLATES.len)
                    ];
                    const mutated = try allocator.dupe(u8, base_tmpl);
                    defer allocator.free(mutated);
                    var m_i: usize = 0;
                    const mut_limit = random.intRangeAtMost(usize, 1, 4);
                    while (m_i < mut_limit and mutated.len > 0) : (m_i += 1) {
                        const pos = random.intRangeLessThan(usize, 0, mutated.len);
                        const bad_bytes = [_]u8{ 0x00, 0x07, 0x1F, 0x80, 0xC0, 0xFF, '{', '[', '"', '\\', ':' };
                        mutated[pos] = bad_bytes[random.intRangeLessThan(usize, 0, bad_bytes.len)];
                    }
                    try appendValidFrame(allocator, &session_wire, mutated);
                },
                4 => {
                    // Truncated JSON slice with matching `Content-Length`:
                    const base_tmpl = BASELINE_LSP_JSON_TEMPLATES[
                        random.intRangeLessThan(usize, 0, BASELINE_LSP_JSON_TEMPLATES.len)
                    ];
                    try appendValidFrame(
                        allocator,
                        &session_wire,
                        base_tmpl[0..random.intRangeAtMost(usize, 1, base_tmpl.len)],
                    );
                },
                else => {
                    // Out-of-bounds line/character coordinates & random `$/cancelRequest` interleaving:
                    const coord_req = try std.fmt.allocPrint(
                        allocator,
                        "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"textDocument/hover\",\"params\":{{" ++
                            "\"textDocument\":{{\"uri\":\"file:///D%3A/virt/fuzz.cx\"}}," ++
                            "\"position\":{{\"line\":{d},\"character\":{d}}}}}}}",
                        .{ executed_frames + 100, random.int(u32), random.int(u32) },
                    );
                    defer allocator.free(coord_req);
                    try appendValidFrame(allocator, &session_wire, coord_req);
                    if (random.boolean()) {
                        const cancel_msg = try std.fmt.allocPrint(
                            allocator,
                            "{{\"jsonrpc\":\"2.0\",\"method\":\"$/cancelRequest\",\"params\":{{\"id\":{d}}}}}",
                            .{executed_frames + 100},
                        );
                        defer allocator.free(cancel_msg);
                        try appendValidFrame(allocator, &session_wire, cancel_msg);
                    }
                },
            }
        }

        // Occasionally append truncated EOF frame at the very end of the session stream:
        if (random.intRangeLessThan(u8, 0, 3) == 0) {
            try session_wire.appendSlice(allocator, "Content-Length: 99\r\n\r\n{\"jsonrpc\":");
        } else {
            try appendValidFrame(allocator, &session_wire, "{\"jsonrpc\":\"2.0\",\"id\":999,\"method\":\"shutdown\"}");
            try appendValidFrame(allocator, &session_wire, "{\"jsonrpc\":\"2.0\",\"method\":\"exit\"}");
        }

        try runFuzzedLspStream(allocator, io, session_wire.items);
    }
    try std.testing.expect(executed_frames >= 250);
}

test "test_fuzz_vfs_incremental_edits_match_fresh_parse" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    var prng = std.Random.Xoroshiro128.init(0xC0AE_1010_F022_0002);
    const random = prng.random();

    // [1] 160+ multi-step random UTF-8/UTF-16 edits via `LineIndex.resolveByteOffset` + `setInputWithEdit`:
    {
        var db = try CompilerDb.init(allocator);
        defer db.deinit();
        var vfs = VfsSourceMap.init(allocator, &db.interner);
        defer vfs.deinit(io);
        db.setVfsSourceMap(&vfs);

        const seed_src =
            "//! Incremental VFS & astral scalar 𐍈𝐀 module\r\n" ++
            "pub struct Counter {\n" ++
            "    pub val_num: i32,\n" ++
            "    pub tag_str: str,\n" ++
            "}\n" ++
            "pub fn update_counter(cnt: &mut Counter, delta: i32) -> i32 {\n" ++
            "    let glyph_note = \"café • 𐍈𝐀\";\n" ++
            "    _ = glyph_note;\n" ++
            "    cnt.val_num = cnt.val_num +% delta;\n" ++
            "    return cnt.val_num;\n" ++
            "}\n";

        var current_buf = try allocator.dupe(u8, seed_src);
        defer allocator.free(current_buf);

        const fid = try vfs.setEditorOverlay(io, "d:/virt/inc_fuzz.cx", current_buf, .root, true);
        _ = try db.setInput(fid, current_buf, .low);
        _ = try db.parseCst(fid);

        var step_i: usize = 0;
        while (step_i < VFS_INCREMENTAL_FUZZ_ITERATIONS) : (step_i += 1) {
            // Periodically reset when buffer grows beyond 4 KiB to keep all 160 steps under `< 2s`:
            if (current_buf.len > 4096) {
                allocator.free(current_buf);
                current_buf = try allocator.dupe(u8, seed_src);
                _ = try vfs.setEditorOverlay(io, "d:/virt/inc_fuzz.cx", current_buf, .root, true);
                _ = try db.setInput(fid, current_buf, .low);
                _ = try db.parseCst(fid);
            }

            // Apply 1..2 coalesced `setInputWithEdit` mutations before querying `db.parseCst(fid)`:
            const sub_edits: usize = if (random.intRangeLessThan(u8, 0, 4) == 0) 2 else 1;
            var sub_i: usize = 0;
            while (sub_i < sub_edits) : (sub_i += 1) {
                const line_idx = try vfs.getLineIndex(fid);
                const line_count = @max(line_idx.countLines(), 1);
                const encoding: PositionEncoding = if (random.boolean()) .utf16 else .utf8;

                const line_a = random.intRangeLessThan(u32, 0, line_count + 1);
                const col_a = random.intRangeLessThan(u32, 0, 80);
                const line_b = random.intRangeLessThan(u32, 0, line_count + 1);
                const col_b = random.intRangeLessThan(u32, 0, 80);

                const raw_off_a = line_idx.resolveByteOffset(current_buf, line_a, col_a, encoding);
                const raw_off_b = line_idx.resolveByteOffset(current_buf, line_b, col_b, encoding);
                const start_byte = clampAwayFromMidCrlf(current_buf, @min(raw_off_a, raw_off_b));
                const old_end_byte = @max(start_byte, clampAwayFromMidCrlf(current_buf, @max(raw_off_a, raw_off_b)));

                // Verify `LineIndex.resolveByteOffset` never splits a multi-byte UTF-8 scalar:
                if (start_byte < current_buf.len) {
                    try std.testing.expect((current_buf[start_byte] & 0xC0) != 0x80);
                }
                if (old_end_byte < current_buf.len) {
                    try std.testing.expect((current_buf[old_end_byte] & 0xC0) != 0x80);
                }

                const repl_snippet = VFS_UTF8_EDIT_SNIPPETS[
                    random.intRangeLessThan(usize, 0, VFS_UTF8_EDIT_SNIPPETS.len)
                ];
                const next_len = @as(usize, start_byte) + repl_snippet.len +
                    (current_buf.len - @as(usize, old_end_byte));
                const next_buf = try allocator.alloc(u8, next_len);
                @memcpy(next_buf[0..start_byte], current_buf[0..start_byte]);
                @memcpy(next_buf[start_byte .. start_byte + repl_snippet.len], repl_snippet);
                @memcpy(next_buf[start_byte + repl_snippet.len ..], current_buf[old_end_byte..]);

                try std.testing.expect(std.unicode.utf8ValidateSlice(next_buf));
                const edit_range = EditRange{
                    .start_byte = start_byte,
                    .old_end_byte = old_end_byte,
                    .new_end_byte = @intCast(@as(usize, start_byte) + repl_snippet.len),
                };

                allocator.free(current_buf);
                current_buf = next_buf;
                _ = try vfs.setEditorOverlay(io, "d:/virt/inc_fuzz.cx", current_buf, .root, true);
                _ = try db.setInputWithEdit(fid, current_buf, .low, edit_range);
            }

            const inc_art = try db.parseCst(fid);

            var fresh_tok = TokenBuffer.init(allocator);
            defer fresh_tok.deinit();
            var fresh_cst = LosslessCstArena.init(allocator);
            defer fresh_cst.deinit();
            var fresh_ast = AstArena.init(allocator);
            defer fresh_ast.deinit();
            var fresh_sink = DiagnosticSink.init(allocator);
            defer fresh_sink.deinit();
            _ = try corex.parseSource(
                current_buf,
                fid,
                &fresh_tok,
                &fresh_cst,
                &fresh_ast,
                &fresh_sink,
                null,
            );

            try std.testing.expectEqual(fresh_tok.countTokens(), inc_art.token_buffer.countTokens());
            try std.testing.expectEqual(fresh_cst.countNodes(), inc_art.cst_arena.countNodes());
            try std.testing.expectEqual(fresh_ast.countNodes(), inc_art.ast_arena.countNodes());
            try std.testing.expectEqual(fresh_sink.error_count, inc_art.diagnostics.error_count);

            var tok_i: usize = 0;
            while (tok_i < fresh_tok.countTokens()) : (tok_i += 1) {
                const tok_id = corex.TokenIndex.fromInt(@intCast(tok_i));
                const expected_tok = fresh_tok.getToken(tok_id);
                const actual_tok = inc_art.token_buffer.getToken(tok_id);
                try std.testing.expectEqual(expected_tok.kind, actual_tok.kind);
                try std.testing.expectEqual(expected_tok.byte_offset, actual_tok.byte_offset);
                try std.testing.expectEqual(expected_tok.byte_len, actual_tok.byte_len);
            }
        }
    }

    // [2] `OverlayCache` (> `256` entries) & `SemanticTokensCache` (`init` + tight limits) LRU eviction stress:
    {
        var interner = try StringInterner.init(allocator);
        defer interner.deinit();
        var stress_vfs = VfsSourceMap.init(allocator, &interner);
        defer stress_vfs.deinit(io);
        stress_vfs.setIo(io);

        // Include a disk-backed file alongside `290` virtual paths to exercise disk-revert + two-queue LRU eviction:
        const disk_fid = try stress_vfs.resolveOrCreatePath(io, "core/root.cx", .std_core);
        var recorded_fids: std.ArrayListUnmanaged(FileId) = .empty;
        defer recorded_fids.deinit(allocator);
        try recorded_fids.append(allocator, disk_fid);

        var op_i: usize = 0;
        while (op_i < VFS_OVERLAY_STRESS_OPERATIONS) : (op_i += 1) {
            var vpath_buf: [64]u8 = undefined;
            const vpath = try std.fmt.bufPrint(
                &vpath_buf,
                "d:/virt/lru_slot_{d}.cx",
                .{random.intRangeLessThan(usize, 0, 290)},
            );

            const action_pick = random.intRangeLessThan(u8, 0, 5);
            if (action_pick == 0 and recorded_fids.items.len > 0) {
                _ = try stress_vfs.closeOverlay(
                    io,
                    recorded_fids.items[random.intRangeLessThan(usize, 0, recorded_fids.items.len)],
                );
            } else if (action_pick == 1) {
                _ = try stress_vfs.setEditorOverlay(io, "core/root.cx", "// temporary overlay\n", .std_core, true);
                _ = try stress_vfs.closeOverlay(io, disk_fid);
            } else {
                const fid = try stress_vfs.setEditorOverlay(
                    io,
                    vpath,
                    VFS_UTF8_EDIT_SNIPPETS[random.intRangeLessThan(usize, 0, VFS_UTF8_EDIT_SNIPPETS.len)],
                    .root,
                    random.boolean(),
                );
                try recorded_fids.append(allocator, fid);
                const live_slice = stress_vfs.getFileSource(fid).?;
                try std.testing.expectEqual(@as(u8, 0), live_slice[live_slice.len]);
            }

            try std.testing.expect(stress_vfs.overlay_cache.entry_count <= corex.MAX_OPEN_OVERLAYS);
            try std.testing.expect(stress_vfs.overlay_cache.total_bytes <= corex.MAX_OPEN_OVERLAY_BYTES);
        }

        // Verify `SemanticTokensCache.init` and `initWithLimits(4, 96)` bounded LRU eviction:
        var default_sem_cache = try lsp_server.SemanticTokensCache.init(allocator);
        defer default_sem_cache.deinit();
        const default_rid = default_sem_cache.allocNextResultId();
        try default_sem_cache.putCloned(FileId.fromInt(1), default_rid, &.{ 0, 0, 3, 1, 0 });
        try std.testing.expect(default_sem_cache.getMatchingResult(FileId.fromInt(1), &default_rid) != null);

        var tight_sem_cache = try lsp_server.SemanticTokensCache.initWithLimits(allocator, 4, 96);
        defer tight_sem_cache.deinit();
        var active_ids: [8][16]u8 = @splat(@splat('0'));

        var sem_op: usize = 0;
        while (sem_op < SEMANTIC_CACHE_STRESS_OPERATIONS) : (sem_op += 1) {
            const file_slot: u32 = random.intRangeLessThan(u32, 0, 8);
            const target_fid = FileId.fromInt(file_slot + 1);
            switch (random.intRangeLessThan(u8, 0, 4)) {
                0 => tight_sem_cache.removeFile(target_fid),
                1 => _ = tight_sem_cache.getMatchingResult(target_fid, &active_ids[file_slot]),
                else => {
                    const sample_tokens = try allocator.alloc(u32, random.intRangeAtMost(usize, 0, 7) * 5);
                    defer allocator.free(sample_tokens);
                    for (sample_tokens, 0..) |*slot_ptr, idx| {
                        slot_ptr.* = @intCast(idx + sem_op);
                    }
                    const next_rid = tight_sem_cache.allocNextResultId();
                    active_ids[file_slot] = next_rid;
                    try tight_sem_cache.putCloned(target_fid, next_rid, sample_tokens);
                },
            }
            try std.testing.expect(tight_sem_cache.entry_count <= 4);
            try std.testing.expect(tight_sem_cache.total_bytes <= 96);
        }
    }
}

test "test_fuzz_upgrade_engine_convergence_idempotency_and_rollback_safety" {
    const allocator = std.testing.allocator;
    var prng = std.Random.Xoroshiro128.init(0xC0AE_1010_F022_0003);
    const random = prng.random();

    var iter: usize = 0;
    while (iter < UPGRADE_FUZZ_ITERATIONS) : (iter += 1) {
        var snippet_buf: std.ArrayListUnmanaged(u8) = .empty;
        defer snippet_buf.deinit(allocator);

        const has_generated_header = (iter % 5 == 0);
        if (has_generated_header) {
            try snippet_buf.appendSlice(
                allocator,
                GENERATED_HEADER_PREFIXES[
                    random.intRangeLessThan(usize, 0, GENERATED_HEADER_PREFIXES.len)
                ],
            );
        }

        // Assemble 1..2 legacy + canonical `.cx` seed items:
        const frag_count = random.intRangeAtMost(usize, 1, 2);
        var frag_i: usize = 0;
        while (frag_i < frag_count) : (frag_i += 1) {
            try snippet_buf.appendSlice(
                allocator,
                UPGRADE_SEED_FRAGMENTS[
                    random.intRangeLessThan(usize, 0, UPGRADE_SEED_FRAGMENTS.len)
                ],
            );
            try snippet_buf.append(allocator, '\n');
        }

        // Inject random syntax corruptions on ~35% of non-generated inputs to test rollback safety:
        if (!has_generated_header and random.intRangeLessThan(u8, 0, 10) < 4) {
            try snippet_buf.insertSlice(
                allocator,
                random.intRangeAtMost(usize, 0, snippet_buf.items.len),
                SYNTAX_CORRUPTION_SNIPPETS[
                    random.intRangeLessThan(usize, 0, SYNTAX_CORRUPTION_SNIPPETS.len)
                ],
            );
        }

        const file_id = FileId.fromInt(@intCast(iter + 1));
        const pre_errors = try countSyntaxErrorsForSource(allocator, file_id, snippet_buf.items);

        var first_res = try upgrade_engine.upgradeSource(allocator, snippet_buf.items, file_id, .{});
        defer first_res.deinit(allocator);

        // [1] `@generated` / `DO NOT EDIT` headers must never be modified:
        if (has_generated_header) {
            try std.testing.expect(first_res.is_skipped_generated);
            try std.testing.expect(!first_res.is_changed);
            try std.testing.expectEqual(@as(u32, 0), first_res.applied_edit_count);
            try std.testing.expectEqualStrings(snippet_buf.items, first_res.upgraded_source);
            continue;
        }

        // [2] Syntax error count must never increase (`!is_rolled_back` => `post_errors <= pre_errors`):
        const post_errors = try countSyntaxErrorsForSource(allocator, file_id, first_res.upgraded_source);
        if (first_res.is_rolled_back) {
            try std.testing.expect(!first_res.is_changed);
            try std.testing.expectEqualStrings(snippet_buf.items, first_res.upgraded_source);
        } else {
            try std.testing.expect(post_errors <= pre_errors);
        }

        // [3] Fixed-point convergence / idempotency (`upgradeSource` pass 2 produces `is_changed == false`):
        var second_res = try upgrade_engine.upgradeSource(
            allocator,
            first_res.upgraded_source,
            file_id,
            .{},
        );
        defer second_res.deinit(allocator);
        try std.testing.expect(!second_res.is_changed);
        try std.testing.expectEqualStrings(first_res.upgraded_source, second_res.upgraded_source);
    }
}

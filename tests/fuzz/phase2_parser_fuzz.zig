//! Phase 2 Deterministic Parser, CST/AST Invariant & Incremental Reparse Fuzzing Suite (`tests/fuzz/phase2_parser_fuzz.zig`)
//!
//! Executes 2,500+ structure-aware and byte-mutated `.cx` programs through `Lexer` and `Parser`
//! (including periodic tight `max_depth` caps `8..32`), plus 1,000+ random single-item and
//! cross-boundary edit iterations through `reparseIncremental`.
//!
//! Asserts zero panics, zero hangs, empty `parse_stack` on exit, pre-order `subtree_size` partitioning,
//! monotonic token leaf coverage, valid `ast_to_cst` origins, 100% lossless `reconstructSource`, and
//! bit-for-bit incremental parity against a full scratch `parseSource`.

const std = @import("std");
const corex = @import("corex");

const syntax = corex.syntax_arenas;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const CstNodeIndex = corex.CstNodeIndex;
const NodeIndex = corex.NodeIndex;
const StringInterner = corex.StringInterner;
const TriviaPiece = syntax.TriviaPiece;
const TokenBuffer = corex.TokenBuffer;
const CstNodeKind = syntax.CstNodeKind;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const EditRange = corex.EditRange;
const Parser = corex.Parser;
const DiagnosticSink = corex.DiagnosticSink;

// --------------------------------------- CONSTS ----------------------------------------

/// Number of mutated `.cx` programs verified in `test_fuzz_parser_mutated_programs_lossless_and_preorder_invariants`.
const MUTATED_PROGRAM_ITERATIONS: usize = 2_500;
/// Number of random incremental edit iterations verified in `test_fuzz_parser_incremental_reparse_matches_full_scratch_parse`.
const INCREMENTAL_FUZZ_ITERATIONS: usize = 1_000;

/// Syntactic seed fragments covering `DR-24` items, types, patterns, expressions, view blocks, and recovery edges.
const SYNTACTIC_SEED_FRAGMENTS = [_][]const u8{
    "/# Module banner docstring.\n\n",
    "/| Outer item docstring.\n///| Commented-out item doc.\n///# Commented-out mod doc.\n",
    "mod net_core;\n",
    "pub(pkg) mod inner { pub(super) const LIMIT: u32 = 16_u32; }\n",
    "use cx.io.{File, BufReader as Br, *};\n",
    "const MAX_SIZE: usize = 0x1000_usize;\n",
    "pub type Port = u16 is 1..=65535;\n",
    "pub bit_field Flags: u32 { pub ready: bool | 1, mode: u8 | 3, _pad: u32 | 28 }\n",
    "@derive(Clone) pub struct Point[T: Copy = i32, const N: usize = 4] where T: Sized { pub x: T = 0, pub y: T }\n",
    "@repr(C, packed: true, align: .CacheLine, zero_pad: true) pub struct DmaSlot { /| Address.\n pub addr: u64 }\n",
    "@repr(C, packed: 4, align: 64) @derive(Copy, Equatable) pub struct XregsHdr { pub mask: u64 }\n",
    "@link(name: \"cx_rt_hook\", section: \".text.hot\") extern \"C\" fn rt_hook(code: i32) -> i32;\n",
    "@route(method: \"POST\", path: \"/v1\") pub enum Resp[T] { Ok(T), Err { code: u32, msg: str }, Empty }\n",
    "pub enum Order: u8 { Relaxed = 0, SeqCst = 5 }\n",
    "pub union Word { u_val: u64, f_val: f64 }\n",
    "pub trait Hasher { type Out; const SEED: u64 = 1; fn write(&mut self, buf: &[u8]) -> Self.Out; }\n",
    "impl[T: Copy] Point[T] { pub fn origin(&self) -> i32 = 0; }\n",
    "impl Grid { pub subscript(row_i: usize, col_i: usize, /) -> i32 { let { yield 0; } inout { yield &mut self.cell; } } }\n",
    "extern \"C\" fn c_printf(fmt: *u8, ...) -> i32;\n",
    "@cfg(target.os == .Linux and target.ptr_width == 64)\n",
    "pub fn strip[Data: str | &[u8]](data: Data, /, *, trim: bool = true) -> Data = data;\n",
    "pub async unsafe fn compute(\n" ++
        "    arr_in: &mut [i32; 8], out_v: &out i32, box_v: own Box[i32], soa_b: (#soa [u8])?,\n" ++
        ") -> i32!IoError {\n",
    "    let .Ok(val) = parse_in(arr_in) else { return .Err(io_err); };\n",
    "    out_v.* = ~0xFF_i32 + (raw_ptr.* as i32) + (&raw val as usize as i32);\n",
    "    _ = consume_box(own box_v);\n",
    "    let upd = Point { x: 10, ..base };\n",
    "    let moved_upd = Point { x: 20, ..own base };\n",
    "    (left_v, right_v) = (right_v, left_v);\n",
    "    let bytes_lit = b\"HTTP/1.1\\r\\n\"; let sep_b = b':';\n",
    "    let plain_sql = \"SELECT id FROM nodes WHERE meta != '{}'\";\n",
    "    let banner = f\"\n        hello {val=#010x} {{ok}}\n        \";\n",
    "    let json_frame = f#\"{\"id\": {val:04x}, \"mode\": \"{if val > 0 => \"FAST\" else \"IDLE\"}\"}\"#;\n",
    "    let inline_pt = if val > 10 => Point { x: 1, y: 2 } else if val > 0 => Point { x: 0, y: 1 } else Point { x: 0, y: 0 };\n",
    "    defer cleanup();\n",
    "    errdefer |err| { log(err); }\n",
    "    for idx in 0..10 { if idx == 2 { continue; } else { break; } }\n",
    "    while val < 100 |cap| { var tmp: i32 = cap +% 1; tmp <<= 2; }\n",
    "    while iter.next()? is .Some(&item) { _ = item |> step_a() |> step_b(); }\n",
    "    if (rem := arr_in[..$-1].len()) > 0 { _ = search: for elem, i in arr_in { break :search i; } orelse rem; }\n",
    "    with context.allocator = &mut scratch { _ = opt_v orelse unreachable; }\n",
    "    let fsm_out = fsm: match state { .Idle => continue :fsm .Done, .Done => grid[0, 1] };\n",
    "    let res = op_a() catch op_b() catch |err| { 0 };\n",
    "    let cmp = (1 == 2 == 3) + (0..5..10);\n",
    "    let clos = @cold own |x: i32, var y: i32| -> i32 { y += 1; x + y };\n",
    "    let view = Card(padding: if val > 0 => 8 else 16) { Row { Text(val: \"hi\"); } };\n",
    "    let missing_else = if val > 0 => 1;\n",
    "    let mixed_braces = if val > 0 => { 1 } else { 2 };\n",
    "    let inc = user.\n",
    "    let call_inc = connect(host, )\n",
    "    return match val { 0 | 1 => -1, -5..=5 => 2, .Some(var cur_v) if cur_v > 0 => cur_v, Point { x: px, .. } => px, _ => 0 };\n",
    "}\n",
    "test \"fuzz prose test\" (raw: &[u8]) -> unit!IoError { assert(raw.len() >= 0); }\n",
    "bench \"fuzz microbench\" (bencher: &mut Bencher) { _ = bencher; }\n",
    "((((((((((1 + 2))))))))))\n",
    "[[[[[[[[[[i32; 4]]]]]]]]]]\n",
    "{ { { { let x = 1; } } } }\n",
    "/# mid_file_mod_doc_e0229\n/| dangling_doc_e0230\n\n",
    "@packed @align(8) @cache_aligned @zero_pad @[inline] @(cold) pub struct RetiredAttrs { pub x: u32 }\n",
    "/* comment */ /// retired //! retired // line\r\n",
    "badCamel Bad_Type BAD__CONST ` $ := @ #bad && || !x *const\n",
};

/// Clean statement replacements used for fast-splice and cross-boundary incremental edit fuzzing.
const INCREMENTAL_EDIT_SNIPPETS = [_][]const u8{
    "return val + 1_u32;",
    "return (val * 3_u32) +% 42_000_u32;",
    "let step = val |> normalize() catch 0;\n    return step;",
    "let coal = opt_val orelse val;\n    return coal + (b'A' as u32);",
    "let msg = f\"\n        item={val=}\n        \";\n    _ = msg;\n    return val;",
    "let tag = f#\"{\"v\": {if val > 0 => val else 1_u32}}\"#;\n    _ = tag;\n    return if val > 5 => val - 1_u32 else val + 1_u32;",
    "var acc: u32 = val;\n    for i in 0..4 { acc += i; }\n    return acc;",
    "return fsm: match val { 0 => continue :fsm 1, 1..=9 => 20, _ => ~val };",
    "return val; }\npub fn injected_helper(val: u32, /) -> u32 {\n    return val ^ 0xFF_u32;",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Verifies pre-order CST structural invariants, monotonic leaf tokens, AST origins, and lossless reconstruction.
fn verifyAllParserInvariants(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buf: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
) !void {
    // [1] Parser state stack must be completely unwound (`parse_stack.items.len == 0`) on exit:
    try std.testing.expectEqual(@as(usize, 0), cst_arena.parse_stack.items.len);
    try std.testing.expect(cst_arena.countNodes() > 0);

    // [2] Root CST node `0` must be `.source_file` with `subtree_size == cst_arena.countNodes()`:
    const root_cst = cst_arena.getNode(CstNodeIndex.fromInt(0));
    try std.testing.expectEqual(CstNodeKind.source_file, root_cst.kind);
    try std.testing.expectEqual(@as(u32, @intCast(cst_arena.countNodes())), root_cst.subtree_size);

    // [3] Every CST node's `subtree_size` must partition its children and visit tokens monotonically:
    var prev_leaf_tok: ?u32 = null;
    var i: usize = 0;
    while (i < cst_arena.countNodes()) : (i += 1) {
        const rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(i)));
        try std.testing.expect(rec.subtree_size >= 1);
        try std.testing.expect(i + @as(usize, rec.subtree_size) <= cst_arena.countNodes());

        if (rec.subtree_size > 1) {
            var child_idx: usize = i + 1;
            const end_idx: usize = i + @as(usize, rec.subtree_size);
            while (child_idx < end_idx) {
                const child_rec = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(child_idx)));
                try std.testing.expect(child_rec.subtree_size >= 1);
                child_idx += @as(usize, child_rec.subtree_size);
            }
            try std.testing.expectEqual(end_idx, child_idx);
        } else if (!rec.flags.is_bracketed and !rec.flags.is_missing_or_injected) {
            try std.testing.expect(rec.token.asInt() < token_buf.countTokens());
            if (prev_leaf_tok) |prev_tok| {
                try std.testing.expectEqual(prev_tok + 1, rec.token.asInt());
            } else {
                try std.testing.expectEqual(@as(u32, 0), rec.token.asInt());
            }
            prev_leaf_tok = rec.token.asInt();
        }
    }
    if (token_buf.countTokens() > 0 and prev_leaf_tok != null) {
        try std.testing.expectEqual(@as(u32, @intCast(token_buf.countTokens() - 1)), prev_leaf_tok.?);
    }

    // [4] Every AST node must map to a valid `CstNodeIndex` (`< cst_arena.countNodes()`) and `TokenIndex`:
    try std.testing.expect(ast_arena.countNodes() > 0);
    try std.testing.expectEqual(ast_arena.countNodes(), ast_arena.ast_to_cst.items.len);
    i = 0;
    while (i < ast_arena.countNodes()) : (i += 1) {
        const ast_id = NodeIndex.fromInt(@intCast(i));
        const ast_rec = ast_arena.getNode(ast_id);
        if (!ast_rec.main_token.isNone() and token_buf.countTokens() > 0) {
            try std.testing.expect(ast_rec.main_token.asInt() < token_buf.countTokens());
        }
        const origin = ast_arena.getCstOrigin(ast_id);
        if (!origin.isNone()) {
            try std.testing.expect(origin.asInt() < cst_arena.countNodes());
        }
    }

    // [5] Lossless source reconstruction must match `source` byte-for-bit:
    const reconstructed = try cst_arena.reconstructSource(allocator, source, token_buf);
    defer allocator.free(reconstructed);
    try std.testing.expectEqualSlices(u8, source, reconstructed);
}

// ------------------------------------- PUBLIC API --------------------------------------

test "test_fuzz_parser_mutated_programs_lossless_and_preorder_invariants" {
    var prng = std.Random.DefaultPrng.init(0xC0DEC0DE_FA5E0002);
    const random = prng.random();

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    var source_buf: [1024]u8 = undefined;
    var iter_idx: usize = 0;
    while (iter_idx < MUTATED_PROGRAM_ITERATIONS) : (iter_idx += 1) {
        // [1] Assemble 1..8 syntactic seed fragments into `source_buf`:
        var byte_len: usize = 0;
        const frag_count = random.intRangeAtMost(usize, 0, 8);
        var frag_idx: usize = 0;
        while (frag_idx < frag_count) : (frag_idx += 1) {
            const frag = SYNTACTIC_SEED_FRAGMENTS[random.uintLessThan(usize, SYNTACTIC_SEED_FRAGMENTS.len)];
            if (byte_len + frag.len <= source_buf.len) {
                @memcpy(source_buf[byte_len .. byte_len + frag.len], frag);
                byte_len += frag.len;
            }
        }

        // [2] Apply 0..3 random byte mutations (delimiter deletions, operator swaps, arbitrary bytes):
        const mut_count = random.intRangeAtMost(usize, 0, 3);
        var mut_idx: usize = 0;
        while (mut_idx < mut_count and byte_len > 0) : (mut_idx += 1) {
            source_buf[random.uintLessThan(usize, byte_len)] = switch (random.uintLessThan(u8, 8)) {
                0 => '{',
                1 => '}',
                2 => '(',
                3 => '[',
                4 => ';',
                5 => '.',
                6 => '|',
                else => random.int(u8),
            };
        }

        const source_slice = source_buf[0..byte_len];
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();

        const file_id = FileId.fromInt(@intCast(iter_idx & 0xFF));

        // Periodically enforce a tight `max_depth` cap (`8..32`) to stress `E0203` recovery:
        if (iter_idx % 16 == 0) {
            token_buf.tokens.shrinkRetainingCapacity(0);
            token_buf.trivia.clearRetainingCapacity();
            cst_arena.nodes.shrinkRetainingCapacity(0);
            cst_arena.parse_stack.clearRetainingCapacity();
            cst_arena.has_parse_errors = false;
            ast_arena.nodes.shrinkRetainingCapacity(0);
            ast_arena.extra_data.clearRetainingCapacity();
            ast_arena.ast_to_cst.clearRetainingCapacity();

            try corex.tokenize(source_slice, file_id, &token_buf, &sink, &interner);
            var parser_instance = Parser.initWithOptions(
                source_slice,
                file_id,
                &token_buf,
                &cst_arena,
                &ast_arena,
                &sink,
                &interner,
                .{ .max_depth = random.intRangeAtMost(usize, 8, 32) },
            );
            _ = try parser_instance.parse();
        } else {
            _ = try corex.parseSource(
                source_slice,
                file_id,
                &token_buf,
                &cst_arena,
                &ast_arena,
                &sink,
                &interner,
            );
        }

        // [3] Verify all CST, AST, and lossless round-trip invariants:
        try verifyAllParserInvariants(
            std.testing.allocator,
            source_slice,
            &token_buf,
            &cst_arena,
            &ast_arena,
        );
    }
}

test "test_fuzz_parser_incremental_reparse_matches_full_scratch_parse" {
    var prng = std.Random.DefaultPrng.init(0x19C2_E5A1_2026_1109);
    const random = prng.random();

    const initial_module =
        \\/# Incremental reparse fuzz seed module.
        \\
        \\const MODULE_SEED: u32 = 100;
        \\
        \\/| Computes slot zero.
        \\pub fn item_zero(val: u32) -> u32 {
        \\    // [edit_0]
        \\    return val + 1;
        \\    // [end_0]
        \\}
        \\
        \\/| Computes slot one.
        \\pub fn item_one(val: u32) -> u32 {
        \\    // [edit_1]
        \\    return val + 2;
        \\    // [end_1]
        \\}
        \\
        \\/| Computes slot two.
        \\pub fn item_two(val: u32) -> u32 {
        \\    // [edit_2]
        \\    return val + 3;
        \\    // [end_2]
        \\}
        \\
        \\/| Computes slot three.
        \\pub fn item_three(val: u32) -> u32 {
        \\    // [edit_3]
        \\    return val + 4;
        \\    // [end_3]
        \\}
    ;

    var current_source = try std.testing.allocator.dupe(u8, initial_module);
    defer std.testing.allocator.free(current_source);

    var inc_tokens = TokenBuffer.init(std.testing.allocator);
    defer inc_tokens.deinit();
    var inc_cst = LosslessCstArena.init(std.testing.allocator);
    defer inc_cst.deinit();
    var inc_ast = AstArena.init(std.testing.allocator);
    defer inc_ast.deinit();

    var scratch_tokens = TokenBuffer.init(std.testing.allocator);
    defer scratch_tokens.deinit();
    var scratch_cst = LosslessCstArena.init(std.testing.allocator);
    defer scratch_cst.deinit();
    var scratch_ast = AstArena.init(std.testing.allocator);
    defer scratch_ast.deinit();

    const file_id = FileId.fromInt(0);
    _ = try corex.parseSource(
        current_source,
        file_id,
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );

    const start_markers = [_][]const u8{
        "// [edit_0]\n    ",
        "// [edit_1]\n    ",
        "// [edit_2]\n    ",
        "// [edit_3]\n    ",
    };
    const end_markers = [_][]const u8{
        "\n    // [end_0]",
        "\n    // [end_1]",
        "\n    // [end_2]",
        "\n    // [end_3]",
    };

    var fast_splice_count: usize = 0;
    var iter_idx: usize = 0;
    while (iter_idx < INCREMENTAL_FUZZ_ITERATIONS) : (iter_idx += 1) {
        const slot_idx = random.uintLessThan(usize, start_markers.len);
        const start_marker = start_markers[slot_idx];
        const edit_start = std.mem.indexOf(u8, current_source, start_marker).? + start_marker.len;
        const edit_old_end = std.mem.indexOfPos(u8, current_source, edit_start, end_markers[slot_idx]).?;

        const replacement = INCREMENTAL_EDIT_SNIPPETS[
            random.uintLessThan(usize, INCREMENTAL_EDIT_SNIPPETS.len)
        ];

        const new_len = current_source.len - (edit_old_end - edit_start) + replacement.len;
        var next_source = try std.testing.allocator.alloc(u8, new_len);
        errdefer std.testing.allocator.free(next_source);

        @memcpy(next_source[0..edit_start], current_source[0..edit_start]);
        @memcpy(next_source[edit_start .. edit_start + replacement.len], replacement);
        @memcpy(
            next_source[edit_start + replacement.len .. new_len],
            current_source[edit_old_end..],
        );

        const stats = try corex.reparseIncremental(
            next_source,
            file_id,
            EditRange{
                .start_byte = @intCast(edit_start),
                .old_end_byte = @intCast(edit_old_end),
                .new_end_byte = @intCast(edit_start + replacement.len),
            },
            &inc_tokens,
            &inc_cst,
            &inc_ast,
            null,
            null,
        );
        if (stats.is_fast_splice) {
            fast_splice_count += 1;
        }

        // Verify structural invariants and lossless source reconstruction:
        try verifyAllParserInvariants(
            std.testing.allocator,
            next_source,
            &inc_tokens,
            &inc_cst,
            &inc_ast,
        );

        // Verify 100% bit-for-bit equality against a fresh `parseSource(next_source)`:
        _ = try corex.parseSource(
            next_source,
            file_id,
            &scratch_tokens,
            &scratch_cst,
            &scratch_ast,
            null,
            null,
        );

        try std.testing.expectEqual(scratch_tokens.countTokens(), inc_tokens.countTokens());
        var i: usize = 0;
        while (i < scratch_tokens.countTokens()) : (i += 1) {
            const tok_id = TokenIndex.fromInt(@intCast(i));
            try std.testing.expectEqual(
                scratch_tokens.getToken(tok_id),
                inc_tokens.getToken(tok_id),
            );
        }
        try std.testing.expectEqualSlices(
            TriviaPiece,
            scratch_tokens.trivia.items,
            inc_tokens.trivia.items,
        );

        try std.testing.expectEqual(scratch_cst.countNodes(), inc_cst.countNodes());
        i = 0;
        while (i < scratch_cst.countNodes()) : (i += 1) {
            const cst_id = CstNodeIndex.fromInt(@intCast(i));
            try std.testing.expectEqual(scratch_cst.getNode(cst_id), inc_cst.getNode(cst_id));
        }

        try std.testing.expectEqual(scratch_ast.countNodes(), inc_ast.countNodes());
        i = 0;
        while (i < scratch_ast.countNodes()) : (i += 1) {
            const ast_id = NodeIndex.fromInt(@intCast(i));
            try std.testing.expectEqual(scratch_ast.getNode(ast_id), inc_ast.getNode(ast_id));
            try std.testing.expectEqual(
                scratch_ast.getCstOrigin(ast_id),
                inc_ast.getCstOrigin(ast_id),
            );
        }
        try std.testing.expectEqualSlices(
            u32,
            scratch_ast.extra_data.items,
            inc_ast.extra_data.items,
        );

        std.testing.allocator.free(current_source);
        current_source = next_source;
    }

    try std.testing.expect(fast_splice_count > 500);
}

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

/// Syntactic seed fragments covering items, types, patterns, expressions, view blocks, and recovery edges.
const SYNTACTIC_SEED_FRAGMENTS = [_][]const u8{
    "mod net_core;\n",
    "pub mod inner { const LIMIT: u32 = 16; }\n",
    "use std::io::{File, BufReader as Br, *};\n",
    "const MAX_SIZE: usize = 0x1000;\n",
    "pub type Port = u16 is 1..=65535;\n",
    "pub type Flags = bit_field u32 { pub ready: bool | 1, mode: u8 | 3 };\n",
    "@derive(Clone) pub struct Point[T: Copy] where T: Sized { pub x: T = 0, pub y: T }\n",
    "pub bit_field Reg: u16 { pub en: bool | 1, ch: u8 | 4 }\n",
    "pub enum Resp[T] { Ok(T), Err { code: u32, msg: str }, Empty = 0 }\n",
    "pub union Word { u_val: u64, f_val: f64 }\n",
    "pub trait Hasher { type Out; const SEED: u64 = 1; fn write(&mut self, buf: &[u8]) -> Self::Out; }\n",
    "impl[T: Copy] Point[T] { pub fn origin(&self) -> i32 { return 0; } }\n",
    "pub async unsafe fn compute(a: &mut [i32; 8], b: (#soa [u8])?) -> Result[i32, IoError] {\n",
    "    let .Ok(val) = parse_in(a) else { return .Err(io_err); };\n",
    "    defer cleanup();\n",
    "    errdefer |err| { log(err); }\n",
    "    for idx in 0..10 { if idx == 2 { continue; } else { break; } }\n",
    "    while val < 100 |cap| { var tmp: i32 = cap +% 1; tmp <<= 2; }\n",
    "    while let .Some(item) = iter.next()? { let _ = item |> step_a() |> step_b(); }\n",
    "    let res = op_a() catch op_b() catch |err| { 0 };\n",
    "    let cmp = (1 == 2 == 3) + (0..5..10);\n",
    "    let clos = |x: i32, mut y: i32| -> i32 { x + y };\n",
    "    let view = Card(padding: 8) { Row { Text(val: \"hi\"); } };\n",
    "    let inc = user.\n",
    "    let call_inc = connect(host, )\n",
    "    return match val { 0 | 1 => -1, -5..=5 => 2, .Some(v) if v > 0 => v, Point { x, .. } => x, _ => 0 };\n",
    "}\n",
    "((((((((((1 + 2))))))))))\n",
    "[[[[[[[[[[i32; 4]]]]]]]]]]\n",
    "{ { { { let x = 1; } } } }\n",
    "/* comment */ // line\r\n",
    "badCamel Bad_Type BAD__CONST $ @ #bad\n",
};

/// Clean statement replacements used for fast-splice and cross-boundary incremental edit fuzzing.
const INCREMENTAL_EDIT_SNIPPETS = [_][]const u8{
    "return val + 1;",
    "return (val * 3) +% 42_000;",
    "let step = val |> normalize() catch 0;\n    return step;",
    "var acc: u32 = val;\n    for i in 0..4 { acc += i; }\n    return acc;",
    "return match val { 0 => 10, 1..=9 => 20, _ => val };",
    "return val; }\npub fn injected_helper(val: u32) -> u32 {\n    return val ^ 0xFF;",
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
        \\const MODULE_SEED: u32 = 100;
        \\
        \\pub fn item_zero(val: u32) -> u32 {
        \\    /*edit_0*/return val + 1;/*end_0*/
        \\}
        \\
        \\pub fn item_one(val: u32) -> u32 {
        \\    /*edit_1*/return val + 2;/*end_1*/
        \\}
        \\
        \\pub fn item_two(val: u32) -> u32 {
        \\    /*edit_2*/return val + 3;/*end_2*/
        \\}
        \\
        \\pub fn item_three(val: u32) -> u32 {
        \\    /*edit_3*/return val + 4;/*end_3*/
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

    const start_markers = [_][]const u8{ "/*edit_0*/", "/*edit_1*/", "/*edit_2*/", "/*edit_3*/" };
    const end_markers = [_][]const u8{ "/*end_0*/", "/*end_1*/", "/*end_2*/", "/*end_3*/" };

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

//! Unit Tests for Lossless CST, TokenBuffer & AST Arenas (`tests/unit/syntax_arenas_test.zig`)
//!
//! Verifies the 112-variant `TokenKind` table, SoA `TokenBuffer` and `TriviaPiece` storage,
//! `LosslessCstArena` pre-order `subtree_size` skipping and source reconstruction, and `AstArena`.
//!
//! Enforces zero memory leaks and tests resource caps (`MAX_PARSE_DEPTH`) and semantic hole nodes.

const std = @import("std");
const corex = @import("corex");

const syntax = corex.syntax_arenas;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const CstNodeIndex = corex.CstNodeIndex;
const NodeIndex = corex.NodeIndex;
const PackedOperand = corex.PackedOperand;
const TokenKind = corex.TokenKind;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const AstArena = corex.AstArena;
const AstStore = corex.AstStore;

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------- TokenBuffer & Trivia Tests -----------------

test "test_token_kind_taxonomy_and_soa_token_buffer" {
    // [1] Verify 112-variant `TokenKind` taxonomy and canonical aliases:
    try std.testing.expectEqual(@as(usize, 112), @typeInfo(TokenKind).@"enum".field_names.len);
    try std.testing.expectEqual(TokenKind.lbrace, TokenKind.l_brace);
    try std.testing.expectEqual(TokenKind.rbrace, TokenKind.r_brace);
    try std.testing.expectEqual(TokenKind.lparen, TokenKind.l_paren);
    try std.testing.expectEqual(TokenKind.rparen, TokenKind.r_paren);
    try std.testing.expectEqual(TokenKind.coloncolon, TokenKind.colon_colon);
    try std.testing.expectEqual(TokenKind.invalid_token, TokenKind.invalid);

    var token_buffer = TokenBuffer.init(std.testing.allocator);
    defer token_buffer.deinit();

    const leading_pieces = [_]syntax.TriviaPiece{
        .{ .kind = .doc_comment, .byte_offset = 0, .byte_len = 18 },
        .{ .kind = .newline_lf, .byte_offset = 18, .byte_len = 1 },
    };
    const trailing_pieces = [_]syntax.TriviaPiece{
        .{ .kind = .spaces, .byte_offset = 22, .byte_len = 1 },
    };

    const tok_pub = try token_buffer.appendToken(
        .kw_pub,
        .{ .has_leading_newline = true },
        19,
        3,
        &leading_pieces,
        &trailing_pieces,
    );
    const fn_span = token_buffer.getTokenSpan(
        FileId.fromInt(1),
        try token_buffer.appendTokenRecord(.{
            .kind = .kw_fn,
            .byte_offset = 23,
            .byte_len = 2,
        }),
    );

    try std.testing.expectEqual(@as(usize, 2), token_buffer.countTokens());

    const pub_record = token_buffer.getToken(tok_pub);
    try std.testing.expectEqual(TokenKind.kw_pub, pub_record.kind);
    try std.testing.expect(pub_record.flags.has_leading_newline);
    try std.testing.expect(pub_record.flags.has_leading_trivia_pieces);
    try std.testing.expect(pub_record.flags.has_trailing_trivia);
    try std.testing.expectEqual(@as(usize, 2), token_buffer.getLeadingTrivia(tok_pub).len);
    try std.testing.expectEqual(@as(usize, 1), token_buffer.getTrailingTrivia(tok_pub).len);

    try std.testing.expectEqual(@as(u32, 23), fn_span.start_byte);
    try std.testing.expectEqual(@as(u32, 25), fn_span.end_byte);
}

// ------------------- LosslessCstArena Tests -------------------

test "test_lossless_cst_subtree_skipping_and_exact_source_reconstruction" {
    const raw_source = "/// Doc header\r\npub fn calc(val: i32) -> i32 {\n    val +% 1\n}\n";
    var token_buffer = TokenBuffer.init(std.testing.allocator);
    defer token_buffer.deinit();

    // Tokenize `raw_source` into two trivia-carrying tokens plus a synthesized recovery token:
    const first_tok = try token_buffer.appendToken(
        .kw_pub,
        .{},
        16,
        3,
        &.{
            .{ .kind = .doc_comment, .byte_offset = 0, .byte_len = 14 },
            .{ .kind = .newline_crlf, .byte_offset = 14, .byte_len = 2 },
        },
        &.{
            .{ .kind = .spaces, .byte_offset = 19, .byte_len = 1 },
        },
    );
    const rest_tok = try token_buffer.appendToken(
        .ident,
        .{},
        20,
        @intCast(raw_source.len - 20),
        &.{},
        &.{},
    );
    const synth_semi = try token_buffer.appendToken(
        .semi,
        .{ .is_synthesized = true },
        @intCast(raw_source.len),
        0,
        &.{},
        &.{},
    );

    var cst = LosslessCstArena.init(std.testing.allocator);
    defer cst.deinit();

    const file_node = try cst.startNode(.source_file, first_tok);
    const fn_node = try cst.startNode(.fn_decl, first_tok);
    _ = try cst.appendLeafNode(.visibility_modifier, first_tok, .{});
    _ = try cst.appendLeafNode(.token_leaf, rest_tok, .{});
    _ = try cst.appendLeafNode(.invalid_parse_leaf, synth_semi, .{
        .has_error = true,
        .is_missing_or_injected = true,
    });
    cst.finishNode(fn_node, .{ .has_error = true, .child_arity_small = 3 });
    cst.finishNode(file_node, .{ .has_error = true, .child_arity_small = 1 });

    try std.testing.expect(cst.has_parse_errors);
    try std.testing.expectEqual(@as(usize, 5), cst.countNodes());
    try std.testing.expectEqual(@as(u32, 5), cst.getNode(file_node).subtree_size);
    try std.testing.expectEqual(@as(u32, 4), cst.getNode(fn_node).subtree_size);

    const reconstructed = try cst.reconstructSource(std.testing.allocator, raw_source, &token_buffer);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(raw_source, reconstructed);

    // Verify out-of-bounds token span is rejected cleanly without panicking:
    _ = try token_buffer.appendToken(.ident, .{}, 100, 10, &.{}, &.{});
    try std.testing.expectError(
        error.OutOfBoundsTokenSpan,
        cst.reconstructSource(std.testing.allocator, raw_source, &token_buffer),
    );
}

test "test_cst_parse_state_stack_depth_bound" {
    var cst = LosslessCstArena.init(std.testing.allocator);
    defer cst.deinit();

    var depth_idx: usize = 0;
    while (depth_idx < syntax.MAX_PARSE_DEPTH) : (depth_idx += 1) {
        try cst.pushParseState(.{
            .kind = .expr_bp,
            .precedence_or_mode = @truncate(depth_idx),
            .subtree_start = @intCast(depth_idx),
        });
    }
    try std.testing.expectError(error.ParseDepthExceeded, cst.pushParseState(.{ .kind = .root }));

    var popped_count: usize = 0;
    while (cst.popParseState()) |_| {
        popped_count += 1;
    }
    try std.testing.expectEqual(syntax.MAX_PARSE_DEPTH, popped_count);
}

// ----------------------- AstArena Tests -----------------------

test "test_ast_arena_soa_nodes_extra_trail_and_semantic_holes" {
    var ast = AstStore.init(std.testing.allocator);
    defer ast.deinit();

    const root_id = try ast.appendNode(.{
        .tag = .root,
        .main_token = TokenIndex.fromInt(0),
    });
    try std.testing.expectEqual(NodeIndex.root, root_id);
    try std.testing.expect(ast.getCstOrigin(root_id).isNone());

    const extra_params = [_]u32{ 10, 20, 30, 40 };
    const extra_idx = try ast.appendExtraSlice(&extra_params);

    const hole_tags = [_]syntax.AstTag{
        .item_hole,
        .stmt_hole,
        .expr_hole,
        .type_hole,
        .pattern_hole,
        .incomplete_member_access,
        .incomplete_call,
    };
    for (hole_tags, 0..) |hole_tag, i| {
        const node_id = try ast.appendNodeWithCst(.{
            .tag = hole_tag,
            .main_token = TokenIndex.fromInt(@intCast(i + 1)),
            .lhs = PackedOperand.initExtra(extra_idx),
            .rhs = PackedOperand.initNode(root_id),
        }, CstNodeIndex.fromInt(@intCast(i + 10)));

        try std.testing.expectEqual(hole_tag, ast.getNode(node_id).tag);
        try std.testing.expectEqual(CstNodeIndex.fromInt(@intCast(i + 10)), ast.getCstOrigin(node_id));
    }

    try std.testing.expectEqual(@as(usize, 1 + hole_tags.len), ast.countNodes());
    try std.testing.expectEqualSlices(u32, &extra_params, ast.getExtraSlice(extra_idx, extra_params.len));
}

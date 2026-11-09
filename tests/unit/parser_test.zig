//! Unit Tests for Fault-Tolerant Parser, Lossless CST/AST & Incremental Reparse (`tests/unit/parser_test.zig`)
//!
//! Exercises `TokenSet128` bitset operations, canonical recovery anchor sets, all top-level `Item`
//! declarations, generics and `where` clauses, all 11 `PrimaryType` forms and postfix `?`, all
//! statement and pattern forms, all 15 Pratt expression precedence tiers and `LL(k)` disambiguations,
//! all 4 `DR-03` Showcase `.cx` programs, fault-tolerant recovery (`E0201`–`E0203`, `W0201`),
//! semantic holes, IDE completion nodes (`incomplete_member_access`, `incomplete_call`),
//! `reparseIncremental`, and Red-Team adversarial regressions (`RT-01`–`RT-07`).

const std = @import("std");
const corex = @import("corex");

const parser = corex.parser;
const syntax = corex.syntax_arenas;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const CstNodeIndex = corex.CstNodeIndex;
const NodeIndex = corex.NodeIndex;
const StringInterner = corex.StringInterner;
const TokenKind = corex.TokenKind;
const TriviaPiece = syntax.TriviaPiece;
const TokenBuffer = corex.TokenBuffer;
const CstNodeKind = syntax.CstNodeKind;
const LosslessCstArena = corex.LosslessCstArena;
const AstTag = syntax.AstTag;
const AstArena = corex.AstArena;
const TokenSet128 = corex.TokenSet128;
const EditRange = corex.EditRange;
const Parser = corex.Parser;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const SuggestedFix = corex.SuggestedFix;
const TransactionalPatcher = corex.TransactionalPatcher;

// -------------------------------------- INTERNALS --------------------------------------

/// Verifies pre-order CST subtree partitioning, monotonic token leaf coverage, and lossless source reconstruction.
fn expectValidCstAndAstInvariants(
    source: []const u8,
    token_buf: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
) !void {
    try std.testing.expectEqual(@as(usize, 0), cst_arena.parse_stack.items.len);
    try std.testing.expect(cst_arena.countNodes() >= 2);

    const root_cst = cst_arena.getNode(CstNodeIndex.fromInt(0));
    try std.testing.expectEqual(CstNodeKind.source_file, root_cst.kind);
    try std.testing.expectEqual(@as(u32, @intCast(cst_arena.countNodes())), root_cst.subtree_size);

    // [1] Verify that every composite CST node's children partition `[i + 1 .. i + subtree_size)`:
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

    // [2] Verify that every AST node maps to a valid `CstNodeIndex` and `TokenIndex`:
    try std.testing.expect(ast_arena.countNodes() >= 1);
    try std.testing.expectEqual(AstTag.root, ast_arena.getNode(NodeIndex.root).tag);
    try std.testing.expectEqual(ast_arena.countNodes(), ast_arena.ast_to_cst.items.len);
    i = 0;
    while (i < ast_arena.countNodes()) : (i += 1) {
        const ast_id = NodeIndex.fromInt(@intCast(i));
        const ast_rec = ast_arena.getNode(ast_id);
        if (!ast_rec.main_token.isNone()) {
            try std.testing.expect(ast_rec.main_token.asInt() <= token_buf.countTokens());
        }
        const cst_origin = ast_arena.getCstOrigin(ast_id);
        if (!cst_origin.isNone()) {
            try std.testing.expect(cst_origin.asInt() < cst_arena.countNodes());
        }
    }

    // [3] Verify 100% lossless byte-for-bit source reconstruction:
    const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, source, token_buf);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualSlices(u8, source, reconstructed);
}

/// Parses `source`, asserts zero errors and zero warnings, and verifies all CST/AST invariants.
fn expectCleanParse(source: []const u8, ast_arena: *AstArena, cst_arena: *LosslessCstArena) !void {
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    const root_id = try corex.parseFile(
        source,
        FileId.fromInt(0),
        &token_buf,
        cst_arena,
        ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(NodeIndex.root, root_id);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);
    try std.testing.expect(!cst_arena.has_parse_errors);
    try expectValidCstAndAstInvariants(source, &token_buf, cst_arena, ast_arena);
}

/// Returns `true` if `ast_arena` contains at least one node with `target_tag`.
fn hasAstTag(ast_arena: *const AstArena, target_tag: AstTag) bool {
    for (ast_arena.nodes.items(.tag)) |tag_val| {
        if (tag_val == target_tag) return true;
    }
    return false;
}

/// Returns `true` if `cst_arena` contains at least one node with `target_kind`.
fn hasCstKind(cst_arena: *const LosslessCstArena, target_kind: CstNodeKind) bool {
    for (cst_arena.nodes.items(.kind)) |kind_val| {
        if (kind_val == target_kind) return true;
    }
    return false;
}

/// Asserts that `inc_tokens`, `inc_cst`, and `inc_ast` match a fresh `parseSource(new_source)` bit-for-bit.
fn expectIncrementalMatchesFullParse(
    new_source: []const u8,
    inc_tokens: *const TokenBuffer,
    inc_cst: *const LosslessCstArena,
    inc_ast: *const AstArena,
) !void {
    try expectValidCstAndAstInvariants(new_source, inc_tokens, inc_cst, inc_ast);

    var full_tokens = TokenBuffer.init(std.testing.allocator);
    defer full_tokens.deinit();
    var full_cst = LosslessCstArena.init(std.testing.allocator);
    defer full_cst.deinit();
    var full_ast = AstArena.init(std.testing.allocator);
    defer full_ast.deinit();

    _ = try corex.parseSource(
        new_source,
        FileId.fromInt(0),
        &full_tokens,
        &full_cst,
        &full_ast,
        null,
        null,
    );

    try std.testing.expectEqual(full_tokens.countTokens(), inc_tokens.countTokens());
    var i: usize = 0;
    while (i < full_tokens.countTokens()) : (i += 1) {
        const tok_id = TokenIndex.fromInt(@intCast(i));
        try std.testing.expectEqual(full_tokens.getToken(tok_id), inc_tokens.getToken(tok_id));
    }
    try std.testing.expectEqualSlices(TriviaPiece, full_tokens.trivia.items, inc_tokens.trivia.items);

    try std.testing.expectEqual(full_cst.countNodes(), inc_cst.countNodes());
    i = 0;
    while (i < full_cst.countNodes()) : (i += 1) {
        const cst_id = CstNodeIndex.fromInt(@intCast(i));
        try std.testing.expectEqual(full_cst.getNode(cst_id), inc_cst.getNode(cst_id));
    }

    try std.testing.expectEqual(full_ast.countNodes(), inc_ast.countNodes());
    i = 0;
    while (i < full_ast.countNodes()) : (i += 1) {
        const ast_id = NodeIndex.fromInt(@intCast(i));
        try std.testing.expectEqual(full_ast.getNode(ast_id), inc_ast.getNode(ast_id));
        try std.testing.expectEqual(full_ast.getCstOrigin(ast_id), inc_ast.getCstOrigin(ast_id));
    }
    try std.testing.expectEqualSlices(u32, full_ast.extra_data.items, inc_ast.extra_data.items);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------- TokenSet128 & Anchor Sets ------------------

test "test_parser_token_set_128_operations_and_recovery_anchor_sets" {
    // [1] Verify `EMPTY`, `initOne`, `initMany`, `contains`, `unionWith`, and `without`:
    const empty_set = TokenSet128.EMPTY;
    try std.testing.expectEqual(@as(u128, 0), empty_set.mask);
    try std.testing.expect(!empty_set.contains(.kw_pub));
    try std.testing.expect(!empty_set.contains(.eof));

    const single_fn = TokenSet128.initOne(.kw_fn);
    try std.testing.expect(single_fn.contains(.kw_fn));
    try std.testing.expect(!single_fn.contains(.kw_struct));

    const multi_set = TokenSet128.initMany(&.{ .kw_pub, .kw_let, .semi, .eof });
    try std.testing.expect(multi_set.contains(.kw_pub));
    try std.testing.expect(multi_set.contains(.kw_let));
    try std.testing.expect(multi_set.contains(.semi));
    try std.testing.expect(multi_set.contains(.eof));
    try std.testing.expect(!multi_set.contains(.kw_fn));

    const combined_set = multi_set.unionWith(single_fn);
    try std.testing.expect(combined_set.contains(.kw_fn));
    try std.testing.expect(combined_set.contains(.kw_pub));

    const diff_set = combined_set.without(TokenSet128.initMany(&.{ .kw_pub, .eof }));
    try std.testing.expect(!diff_set.contains(.kw_pub));
    try std.testing.expect(!diff_set.contains(.eof));
    try std.testing.expect(diff_set.contains(.kw_fn));
    try std.testing.expect(diff_set.contains(.semi));

    // [2] Verify canonical synchronization sets and operator bitsets:
    try std.testing.expect(parser.ITEM_STARTER_SET.contains(.kw_fn));
    try std.testing.expect(parser.ITEM_STARTER_SET.contains(.kw_struct));
    try std.testing.expect(parser.ITEM_STARTER_SET.contains(.kw_bit_field));
    try std.testing.expect(parser.STMT_STARTER_SET.contains(.kw_let));
    try std.testing.expect(parser.STMT_STARTER_SET.contains(.kw_defer));
    try std.testing.expect(parser.TYPE_STARTER_SET.contains(.prim_type));
    try std.testing.expect(parser.TYPE_STARTER_SET.contains(.hash_soa));
    try std.testing.expect(parser.ITEM_CONSUME_SET.contains(.semi));
    try std.testing.expect(parser.ITEM_STOP_SET.contains(.rbrace));
    try std.testing.expect(parser.ITEM_STOP_SET.contains(.eof));
    try std.testing.expect(parser.STRUCT_FIELD_CONSUME_SET.contains(.comma));
    try std.testing.expect(parser.STRUCT_FIELD_STOP_SET.contains(.rbrace));
    try std.testing.expect(parser.ENUM_VARIANT_CONSUME_SET.contains(.comma));
    try std.testing.expect(parser.ENUM_VARIANT_STOP_SET.contains(.rbrace));
    try std.testing.expect(parser.MEMBER_STOP_SET.contains(.kw_fn));
    try std.testing.expect(parser.PARAM_CONSUME_SET.contains(.comma));
    try std.testing.expect(parser.PARAM_STOP_SET.contains(.rparen));
    try std.testing.expect(parser.TYPE_ARG_STOP_SET.contains(.rbracket));
    try std.testing.expect(parser.BLOCK_STMT_CONSUME_SET.contains(.semi));
    try std.testing.expect(parser.BLOCK_STMT_STOP_SET.contains(.rbrace));
    try std.testing.expect(parser.LOCAL_INIT_STOP_SET.contains(.kw_else));
    try std.testing.expect(parser.MATCH_ARM_CONSUME_SET.contains(.comma));
    try std.testing.expect(parser.MATCH_ARM_STOP_SET.contains(.fat_arrow));
    try std.testing.expect(parser.EXPR_SYNC_STOP_SET.contains(.semi));
    try std.testing.expect(parser.ASSIGN_OP_SET.contains(.eq));
    try std.testing.expect(parser.ASSIGN_OP_SET.contains(.shr_eq));
    try std.testing.expect(parser.RELATIONAL_OP_SET.contains(.eqeq));
    try std.testing.expect(parser.RANGE_OP_SET.contains(.dotdoteq));

    // [3] Verify `EditRange` byte count helpers:
    const edit = EditRange{ .start_byte = 10, .old_end_byte = 18, .new_end_byte = 25 };
    try std.testing.expectEqual(@as(u32, 8), edit.countOldBytes());
    try std.testing.expectEqual(@as(u32, 15), edit.countNewBytes());
}

// ---------------- Top-Level Item Declarations -----------------

test "test_parser_all_top_level_item_declarations_and_attributes" {
    const items_source =
        \\mod external_mod;
        \\pub mod inline_mod {
        \\    use self::inner;
        \\    use Self::Assoc;
        \\    use std::io::*;
        \\    use std::fs::{File, BufReader as Br};
        \\    use net::http as http_alias;
        \\    pub const LIMIT: usize = 256;
        \\    const UNTYPED_CONST = 42;
        \\}
        \\pub type ByteSlice = &[u8];
        \\pub type NonZeroPort = u16 is 1..=65535;
        \\pub type RegFlags = bit_field u32 {
        \\    pub enabled: bool | 1,
        \\    mode: u8 | 3;
        \\};
        \\@derive(Clone, Debug)
        \\@repr(C, align = 16)
        \\pub struct Packet[T: Copy, const CAP: usize = 64] where T: Sized {
        \\    @field_attr(id: 1)
        \\    pub header: u32 = 0,
        \\    payload: [T; CAP];
        \\}
        \\struct UnitMarker;
        \\pub bit_field StatusRegister: u32 {
        \\    @bit(0)
        \\    pub is_ready: bool | 1,
        \\    channel: u8 | 7,
        \\}
        \\pub enum FrameKind[T] where T: Copy {
        \\    @cold
        \\    Ping = 0,
        \\    Payload(T, u32),
        \\    Metadata { id: u64, flags: u8 = 1 };
        \\    Close = 255,
        \\}
        \\@repr(C)
        \\pub union RawValue {
        \\    pub int_bits: i64,
        \\    float_bits: f64,
        \\}
        \\pub trait Container[Elem]: Sized + Clone where Elem: Copy {
        \\    type Item: Copy = Elem;
        \\    const MAX_LEN: usize = 1024;
        \\    fn count(&self) -> usize;
        \\    pub async unsafe fn reset(&mut self) { }
        \\    subscript(&self, index: usize) -> &Elem;
        \\}
        \\impl[T: Copy, const CAP: usize] Packet[T, const CAP] {
        \\    pub const VERSION: u32 = 1;
        \\    pub type ElemType = T;
        \\    pub fn take_ownership(own self) -> Self { return self; }
        \\    pub fn borrow_ref(ref self) -> i32 { return 0; }
        \\    pub fn borrow_ref_mut(ref mut self, _: i32) -> i32 { return 1; }
        \\    pub fn mutate_self(mut self, self_typed: i32 = 10) -> i32 { return self_typed; }
        \\    pub fn explicit_self(self: &Self, val: inout i32, out: set i32, owned: sink i32) {}
        \\    pub subscript(&self, idx: usize): u32 { yield self.header; }
        \\}
        \\impl[T: Copy, const CAP: usize] Container[T] for Packet[T, const CAP] where T: Sized {
        \\    fn count(&self) -> usize { return CAP; }
        \\}
        \\extern "C" fn c_puts(msg: *u8) -> i32;
        \\comptime {
        \\    let check = 1 + 1;
        \\}
    ;

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    try expectCleanParse(items_source, &ast_arena, &cst_arena);

    try std.testing.expect(hasAstTag(&ast_arena, .mod_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .use_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .const_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .type_alias_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .struct_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .enum_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .union_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .trait_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .impl_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .fn_decl));
    try std.testing.expect(hasCstKind(&cst_arena, .attribute));
    try std.testing.expect(hasCstKind(&cst_arena, .where_clause));
}

// ------------------ Generics & Primary Types ------------------

test "test_parser_all_11_primary_types_and_postfix_optional_chains" {
    const types_source =
        \\pub struct TypeShowcase[T: Clone + Send = i32, const N: usize = 16] {
        \\    pub f_prim: i32,
        \\    pub f_self: Self,
        \\    pub f_ref: &T,
        \\    pub f_ref_mut: &mut T,
        \\    pub f_ref_inout: &inout T,
        \\    pub f_ref_let: &let T,
        \\    pub f_ptr: *u8,
        \\    pub f_ptr_mut: *mut u8,
        \\    pub f_own: own T,
        \\    pub f_own_mut: own mut T,
        \\    pub f_region_ref: ref T,
        \\    pub f_region_mut: ref mut T,
        \\    pub f_soa_slice: #soa [T],
        \\    pub f_soa_array: #soa [T; N],
        \\    pub f_slice: [u8],
        \\    pub f_array: [u64; 32],
        \\    pub f_unit_tuple: (),
        \\    pub f_single_tuple: (i32,),
        \\    pub f_pair_tuple: (i32, str),
        \\    pub f_fn_ptr: async unsafe fn(count: usize, &str) -> bool,
        \\    pub f_dyn_trait: dyn Printable,
        \\    pub f_qualified: std::collections::Map[str, T, const 8, 16, true, MAX_CAP],
        \\    pub f_assoc: Container::Item,
        \\    pub f_opt: T?,
        \\    pub f_nested_opt: (&mut [T; N])??,
        \\}
    ;

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    try expectCleanParse(types_source, &ast_arena, &cst_arena);

    try std.testing.expect(hasAstTag(&ast_arena, .prim_type));
    try std.testing.expect(hasAstTag(&ast_arena, .named_type));
    try std.testing.expect(hasAstTag(&ast_arena, .generic_type));
    try std.testing.expect(hasAstTag(&ast_arena, .ref_type));
    try std.testing.expect(hasAstTag(&ast_arena, .ptr_type));
    try std.testing.expect(hasAstTag(&ast_arena, .mode_type));
    try std.testing.expect(hasAstTag(&ast_arena, .array_type));
    try std.testing.expect(hasAstTag(&ast_arena, .slice_type));
    try std.testing.expect(hasAstTag(&ast_arena, .tuple_type));
    try std.testing.expect(hasAstTag(&ast_arena, .fn_type));
    try std.testing.expect(hasAstTag(&ast_arena, .optional_type));
}

// ------------------- Statements & Patterns --------------------

test "test_parser_all_statement_forms_and_all_11_assignment_operators" {
    const stmts_source =
        \\pub fn exercise_statements(input: i32) -> i32 {
        \\    ;
        \\    @state let immut_val: i32 = input;
        \\    var mut counter: i32 = 0;
        \\    let .Ok(extracted) = validate(immut_val) else {
        \\        return -1;
        \\    };
        \\    defer cleanup_fast();
        \\    defer {
        \\        release_handles();
        \\    };
        \\    errdefer rollback_fast();
        \\    errdefer |err_val| {
        \\        log_error(err_val);
        \\    }
        \\    for idx in 0..10 {
        \\        if idx == 5 {
        \\            continue;
        \\        }
        \\        counter += idx;
        \\    }
        \\    while counter < 100 |captured| {
        \\        counter += captured;
        \\    }
        \\    while let .Some(next_item) = poll_next() {
        \\        counter += next_item;
        \\    }
        \\    let loop_out = loop {
        \\        if counter > 50 {
        \\            break counter;
        \\        }
        \\        break;
        \\    };
        \\    const INNER_STEP: i32 = 2;
        \\    counter = 10;
        \\    counter += INNER_STEP;
        \\    counter -= 1;
        \\    counter *= 3;
        \\    counter /= 2;
        \\    counter %= 7;
        \\    counter &= 0xFF;
        \\    counter |= 0x01;
        \\    counter ^= 0x03;
        \\    counter <<= 1;
        \\    counter >>= 1;
        \\    return counter + extracted;
        \\}
    ;

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    try expectCleanParse(stmts_source, &ast_arena, &cst_arena);

    try std.testing.expect(hasAstTag(&ast_arena, .local_var_decl));
    try std.testing.expect(hasAstTag(&ast_arena, .defer_stmt));
    try std.testing.expect(hasAstTag(&ast_arena, .return_stmt));
    try std.testing.expect(hasAstTag(&ast_arena, .break_stmt));
    try std.testing.expect(hasAstTag(&ast_arena, .continue_stmt));
    try std.testing.expect(hasAstTag(&ast_arena, .for_stmt));
    try std.testing.expect(hasAstTag(&ast_arena, .while_stmt));
    try std.testing.expect(hasAstTag(&ast_arena, .loop_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .assign_stmt));
    try std.testing.expect(hasCstKind(&cst_arena, .empty_stmt));
    try std.testing.expect(hasCstKind(&cst_arena, .let_else_branch));

    var assign_count: usize = 0;
    for (ast_arena.nodes.items(.tag)) |tag_val| {
        if (tag_val == .assign_stmt) assign_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 14), assign_count);
}

test "test_parser_all_refutable_and_irrefutable_patterns" {
    const patterns_source =
        \\pub fn match_patterns(scrutinee: Event) -> i32 {
        \\    let (mut a_val, ref b_val, own c_val, &d_val, &mut e_val, _) = unpack();
        \\    return match scrutinee {
        \\        _ => 0,
        \\        0 | 1 | -42 => 1,
        \\        -10..=10 => 2,
        \\        'a'..='z' | '0'..'9' => 3,
        \\        0..MAX_LIMIT => 4,
        \\        MAX_LIMIT => 5,
        \\        "ping" | true | false | 3.14 => 6,
        \\        .Quit => 7,
        \\        .Resize(width, height) if width > 0 => width + height,
        \\        .Click { x_pos, mut y_pos: 0, .. } => x_pos,
        \\        Event::KeyPress(code) => code,
        \\        Point { x_coord, ref y_coord, z_coord: 10, .. } => x_coord + y_coord,
        \\        (first_item, (second_item, _)) => first_item + second_item,
        \\        fallback_bind => 99,
        \\    };
        \\}
    ;

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    try expectCleanParse(patterns_source, &ast_arena, &cst_arena);

    try std.testing.expect(hasAstTag(&ast_arena, .wildcard_pat));
    try std.testing.expect(hasAstTag(&ast_arena, .bind_pat));
    try std.testing.expect(hasAstTag(&ast_arena, .lit_pat));
    try std.testing.expect(hasAstTag(&ast_arena, .variant_pat));
    try std.testing.expect(hasAstTag(&ast_arena, .struct_pat));
    try std.testing.expect(hasAstTag(&ast_arena, .tuple_pat));
    try std.testing.expect(hasAstTag(&ast_arena, .or_pat));
    try std.testing.expect(hasCstKind(&cst_arena, .range_pat));
}

// ----------------- Pratt Expressions & LL(k) ------------------

test "test_parser_all_15_pratt_precedence_tiers_and_llk_disambiguations" {
    const expr_source =
        \\pub fn pratt_and_llk(vec: &[i32], point: Point) -> i32 {
        \\    let arith = -1 + 2 * 3 +% 4 *% 5 -% 6 +| 7 *| 8 -| 9 / 2 % 3;
        \\    let bits = (1 << 4 >> 1) & 0xFF ^ 0x0F | 0x01;
        \\    let logic = (arith == bits and not false) or (arith != 0 && bits >= 1 || ~bits == 0);
        \\    let casted = (arith as i64) as i32;
        \\    let piped = arith |> transform_a() |> transform_b(scale: 2);
        \\    let caught = fallible_a() catch fallible_b() catch |err| {
        \\        log_err(err);
        \\        0
        \\    };
        \\    let prefixes = !false and (not true) or *(&point.x) == *(&mut point.y);
        \\    let modes = borrow_check(&inout point, &let point, own point, ref point, ref mut point);
        \\    let tuple_and_arr = ((1), (1,), (1, 2), [0; 16], [1, 2, 3,]);
        \\    let generic_calls = alloc[u64](16) + alloc[(u64, i64)](4) + alloc[[u8]](2)
        \\        + alloc[std::io::File](1) + alloc[dyn Printable](1);
        \\    let indexing = vec[0] + matrix[1, 2] + table[EnumType::VariantKey] + EnumType::Make[i32](1);
        \\    let tuple_field = tuple_and_arr.0;
        \\    let closures = (|x: i32, mut y: i32| -> i32 { x + y })(1, 2) + (|_| 0)(1) + (|| 42)();
        \\    let blocks = (async { 1 }) + (unsafe { 2 }) + (comptime { 3 });
        \\    let variants = .UnitVar + .TupleVar(1, 2) + .StructVar { a: 1, b, ..base };
        \\    let struct_val = Point { x: 1, y, ..point };
        \\    if point == (Point { x: 1, y: 2 }) {
        \\        Card(padding: 16) {
        \\            Row {
        \\                Badge[u32](count: 1) {}
        \\            }
        \\        }
        \\    } else if let .Some(v) = opt_val {
        \\        return v;
        \\    } else if has_item |cap| {
        \\        return cap;
        \\    }
        \\    return casted + piped + caught + tuple_field;
        \\}
    ;

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    try expectCleanParse(expr_source, &ast_arena, &cst_arena);

    try std.testing.expect(hasAstTag(&ast_arena, .unary_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .binary_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .pipe_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .cast_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .field_access));
    try std.testing.expect(hasAstTag(&ast_arena, .generic_call));
    try std.testing.expect(hasAstTag(&ast_arena, .call_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .index_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .struct_lit));
    try std.testing.expect(hasAstTag(&ast_arena, .tuple_lit));
    try std.testing.expect(hasAstTag(&ast_arena, .array_lit));
    try std.testing.expect(hasAstTag(&ast_arena, .closure_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .if_expr));
    try std.testing.expect(hasAstTag(&ast_arena, .contextual_variant));
    try std.testing.expect(hasCstKind(&cst_arena, .view_block_expr));
}

test "test_parser_catch_right_associativity_vs_pipe_left_associativity" {
    // [1] `a |> b |> c` is left-associative `(a |> b) |> c`, so outer `pipe_expr.lhs` is inner `pipe_expr`:
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    try expectCleanParse("fn p() -> i32 { return a |> b |> c; }\n", &ast_arena, &cst_arena);

    var outer_pipe_id: ?NodeIndex = null;
    var i: usize = 0;
    while (i < ast_arena.countNodes()) : (i += 1) {
        const id = NodeIndex.fromInt(@intCast(i));
        if (ast_arena.getNode(id).tag == .pipe_expr) {
            outer_pipe_id = id;
        }
    }
    try std.testing.expect(outer_pipe_id != null);
    try std.testing.expectEqual(
        AstTag.pipe_expr,
        ast_arena.getNode(NodeIndex.fromInt(ast_arena.getNode(outer_pipe_id.?).lhs.payload)).tag,
    );

    // [2] `a catch b catch c` is right-associative `a catch (b catch c)`, so outer `rhs` is inner `binary_expr`:
    try expectCleanParse("fn c() -> i32 { return a catch b catch c; }\n", &ast_arena, &cst_arena);

    var outer_catch_id: ?NodeIndex = null;
    i = 0;
    while (i < ast_arena.countNodes()) : (i += 1) {
        const id = NodeIndex.fromInt(@intCast(i));
        if (ast_arena.getNode(id).tag == .binary_expr) {
            outer_catch_id = id;
        }
    }
    try std.testing.expect(outer_catch_id != null);
    try std.testing.expectEqual(
        AstTag.binary_expr,
        ast_arena.getNode(NodeIndex.fromInt(ast_arena.getNode(outer_catch_id.?).rhs.payload)).tag,
    );
}

// ------------------- DR-03 Domain Showcases -------------------

test "test_parser_all_four_dr03_showcase_programs_lossless_and_zero_diagnostics" {
    const showcase_1_cli =
        \\mod cli_scanner;
        \\use std::env;
        \\use std::fs::{File, BufReader};
        \\use std::io::{IoError, Stdout};
        \\use std::mem::Arena;
        \\const DEFAULT_BUF_CAP: usize = 65_536;
        \\@cli_command(name = "cx-scan", version = "1.0.0")
        \\pub struct ScanOptions {
        \\    @arg(short = 'p', long = "pattern")
        \\    pub pattern: str,
        \\    @arg(short = 'f', long = "file")
        \\    pub file_path: str,
        \\    @flag(short = 'i', long = "ignore-case")
        \\    pub ignore_case: bool = false,
        \\    @arg(short = 'm', long = "max-matches")
        \\    pub max_matches: usize = 1_000,
        \\}
        \\pub fn scan_file(arena: &mut Arena, opts: &ScanOptions, out: &mut Stdout) -> Result[u64, IoError] {
        \\    let file = File::open(opts.file_path)?;
        \\    defer file.close();
        \\    var reader = BufReader::with_capacity(arena, file, DEFAULT_BUF_CAP);
        \\    var matches_found: u64 = 0;
        \\    while let .Some(line) = reader.next_line()? {
        \\        if line.contains(opts.pattern) {
        \\            matches_found += 1;
        \\            out.write_fmt("{opts.file_path}: {line}\n")?;
        \\        }
        \\    }
        \\    .Ok(matches_found)
        \\}
    ;

    const showcase_2_http =
        \\mod user_api;
        \\use net::http::{Request, Response, StatusCode, Json};
        \\const MAX_BODY_BYTES: usize = 16_384;
        \\@derive(Deserialize)
        \\pub struct CreateUserReq {
        \\    pub username: str,
        \\    pub email: str,
        \\    pub role: UserRole?,
        \\}
        \\@route(method = "POST", path = "/v1/users")
        \\pub async fn create_user(req: &mut Request) -> Result[Json[CreateUserReq], ApiError] {
        \\    let body_bytes = req.read_body_bounded(MAX_BODY_BYTES).await?;
        \\    let payload = body_bytes
        \\        |> Json::parse[CreateUserReq]()
        \\        |> Result::map_err(|e| ApiError::InvalidJson(e.message()))?;
        \\    .Ok(Json::from(payload))
        \\}
    ;

    const showcase_3_avl =
        \\mod avl_tree;
        \\use std::cmp::Ord;
        \\use std::mem::OwnPtr;
        \\pub struct AvlNode[K: Ord, V] {
        \\    pub key: K,
        \\    pub value: V,
        \\    pub left: OwnPtr[AvlNode[K, V]]?,
        \\    pub right: OwnPtr[AvlNode[K, V]]?,
        \\}
        \\impl[K: Ord, V] AvlNode[K, V] {
        \\    fn rotate_right(mut y_node: OwnPtr[AvlNode[K, V]]) -> OwnPtr[AvlNode[K, V]] {
        \\        let .Some(mut x_node) = y_node.left.take() else {
        \\            return y_node;
        \\        };
        \\        y_node.left = x_node.right.take();
        \\        x_node.right = .Some(own y_node);
        \\        x_node
        \\    }
        \\}
    ;

    const showcase_4_ui =
        \\mod ui_telemetry;
        \\use ui::core::{View, Signal, Computed, Theme, Color};
        \\@component
        \\pub fn telemetry_dashboard(node_name: str, cpu_sig: &Signal[f32], theme: &Theme) -> View {
        \\    @state var is_paused: bool = false;
        \\    let is_critical = Computed::new(|| cpu_sig.get() >= 80.0);
        \\    Card(padding: 16, border_color: theme.border_subtle) {
        \\        Row(justify: .SpaceBetween, align: .Center) {
        \\            Text(value: "Node: {node_name}", weight: .Bold, size: 18);
        \\            Button(
        \\                label: if is_paused { "Resume" } else { "Pause" },
        \\                on_click: || { is_paused = not is_paused; },
        \\            );
        \\        }
        \\    }
        \\}
    ;

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    try expectCleanParse(showcase_1_cli, &ast_arena, &cst_arena);
    try expectCleanParse(showcase_2_http, &ast_arena, &cst_arena);
    try expectCleanParse(showcase_3_avl, &ast_arena, &cst_arena);
    try expectCleanParse(showcase_4_ui, &ast_arena, &cst_arena);
}

// ----------------- Error Recovery & Autofixes -----------------

test "test_parser_fault_tolerant_recovery_e0201_e0202_e0203_and_holes" {
    // [1] Exercise `E0201` recovery across item, struct, enum, trait, impl, param, type, pat, and expr holes:
    const recovery_src =
        \\123;
        \\struct BrokenStruct { 456, pub ok_field: + }
        \\enum BrokenEnum { 789, ValidVariant }
        \\trait BrokenTrait { 111; fn valid_fn(&self); }
        \\impl BrokenStruct { 222; fn ok_method(&self, +) {} }
        \\fn broken_body(val: i32) -> i32 {
        \\    let + = ;
        \\    let non_assoc = (1 == 2 == 3) + (0..5..10);
        \\    let nested_assign = (val = 10);
        \\    return match val {
        \\        + => 0,
        \\        _ => 1,
        \\    };
        \\}
    ;

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    _ = try corex.parseSource(
        recovery_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        null,
    );
    try std.testing.expect(sink.hasErrors());
    try std.testing.expect(cst_arena.has_parse_errors);
    try expectValidCstAndAstInvariants(recovery_src, &token_buf, &cst_arena, &ast_arena);

    try std.testing.expect(hasAstTag(&ast_arena, .item_hole));
    try std.testing.expect(hasAstTag(&ast_arena, .type_hole));
    try std.testing.expect(hasAstTag(&ast_arena, .pattern_hole));
    try std.testing.expect(hasAstTag(&ast_arena, .expr_hole));

    // [2] Verify `E0202` unclosed delimiter (`(`, `[`, `{`) includes secondary label at opening token:
    const unclosed_src = "fn unclosed_fn(a: [i32; 4 {\n    return 0;\n}\n";
    var unclosed_sink = DiagnosticSink.init(std.testing.allocator);
    defer unclosed_sink.deinit();
    _ = try corex.parseSource(
        unclosed_src,
        FileId.fromInt(1),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &unclosed_sink,
        null,
    );
    try std.testing.expect(unclosed_sink.error_count >= 1);
    var has_e0202_secondary = false;
    for (unclosed_sink.asSlice()) |diag_item| {
        if (diag_item.code == .e0202_unclosed_delimiter and diag_item.labels.len >= 2) {
            if (std.mem.eql(u8, diag_item.labels[1].label, "unclosed delimiter opened here")) {
                has_e0202_secondary = true;
            }
        }
    }
    try std.testing.expect(has_e0202_secondary);
    try expectValidCstAndAstInvariants(unclosed_src, &token_buf, &cst_arena, &ast_arena);

    // [3] Verify `E0203` recursion depth overflow across statement (`stmt_hole`) and expression (`expr_hole`):
    const deep_stmt_src = "fn deep_fn() { let x = 1; }\n";
    var depth_sink = DiagnosticSink.init(std.testing.allocator);
    defer depth_sink.deinit();
    token_buf.tokens.shrinkRetainingCapacity(0);
    token_buf.trivia.clearRetainingCapacity();
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();

    try corex.tokenize(deep_stmt_src, FileId.fromInt(2), &token_buf, &depth_sink, null);
    var capped_parser = Parser.initWithOptions(
        deep_stmt_src,
        FileId.fromInt(2),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &depth_sink,
        null,
        .{ .max_depth = 2 },
    );
    _ = try capped_parser.parse();
    try std.testing.expectEqual(@as(u32, 1), depth_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0203_parse_depth_exceeded, depth_sink.asSlice()[0].code);
    try std.testing.expect(hasAstTag(&ast_arena, .stmt_hole));
    try expectValidCstAndAstInvariants(deep_stmt_src, &token_buf, &cst_arena, &ast_arena);
}

test "test_parser_w0201_contextual_casing_recovery_and_transactional_patcher" {
    const bad_casing_source =
        "struct bad_struct_name {\n" ++
        "    pub BadFieldName: i32,\n" ++
        "}\n" ++
        "const badConstName: i32 = 10;\n" ++
        "fn BadFuncName(BadParam: bad_struct_name) -> i32 {\n" ++
        "    return bad_param.BadFieldName;\n" ++
        "}\n";

    const expected_patched_source =
        "struct BadStructName {\n" ++
        "    pub bad_field_name: i32,\n" ++
        "}\n" ++
        "const BAD_CONST_NAME: i32 = 10;\n" ++
        "fn bad_func_name(bad_param: BadStructName) -> i32 {\n" ++
        "    return bad_param.bad_field_name;\n" ++
        "}\n";

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    const file_id = FileId.fromInt(0);
    _ = try corex.parseSource(
        bad_casing_source,
        file_id,
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 7), sink.warning_count);
    try expectValidCstAndAstInvariants(bad_casing_source, &token_buf, &cst_arena, &ast_arena);

    var candidate_fixes: std.ArrayList(SuggestedFix) = .empty;
    defer candidate_fixes.deinit(std.testing.allocator);
    for (sink.asSlice()) |diag_item| {
        try std.testing.expectEqual(DiagnosticCode.w0201_non_canonical_identifier_case, diag_item.code);
        try candidate_fixes.appendSlice(std.testing.allocator, diag_item.suggestions);
    }

    const patch_outcome = try TransactionalPatcher.apply(
        std.testing.allocator,
        bad_casing_source,
        file_id,
        candidate_fixes.items,
        &interner,
    );
    defer std.testing.allocator.free(patch_outcome.patched_source);
    try std.testing.expectEqual(@as(u32, 7), patch_outcome.applied_count);
    try std.testing.expectEqual(@as(u32, 0), patch_outcome.skipped_conflict_count);
    try std.testing.expectEqualStrings(expected_patched_source, patch_outcome.patched_source);

    // Re-parse the patched source and verify zero errors and zero warnings:
    try expectCleanParse(patch_outcome.patched_source, &ast_arena, &cst_arena);
}

test "test_parser_ide_completion_nodes_and_carrier_token_flushing" {
    // [1] Verify `incomplete_member_access` (`user.`) and `incomplete_call` (`connect(host, `):
    const ide_src =
        \\fn ide_session() {
        \\    let member = client.
        \\    let call_a = connect(host, )
        \\    let call_b = client.send[u32](payload,
        \\}
    ;

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    _ = try corex.parseSource(ide_src, FileId.fromInt(0), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try expectValidCstAndAstInvariants(ide_src, &token_buf, &cst_arena, &ast_arena);
    try std.testing.expect(hasAstTag(&ast_arena, .incomplete_member_access));
    try std.testing.expect(hasAstTag(&ast_arena, .incomplete_call));

    // [2] Verify synthesized trivia carrier token (`is_synthesized = true, has_lexer_error = false`):
    var carrier_tokens = TokenBuffer.init(std.testing.allocator);
    defer carrier_tokens.deinit();
    _ = try carrier_tokens.appendToken(
        .invalid_token,
        .{ .is_synthesized = true, .has_lexer_error = false },
        0,
        0,
        &.{.{ .kind = .spaces, .byte_offset = 0, .byte_len = 2 }},
        &.{},
    );
    _ = try carrier_tokens.appendToken(.kw_mod, .{}, 2, 3, &.{}, &.{
        .{ .kind = .spaces, .byte_offset = 5, .byte_len = 1 },
    });
    _ = try carrier_tokens.appendToken(.ident, .{}, 6, 3, &.{}, &.{});
    _ = try carrier_tokens.appendToken(.semi, .{}, 9, 1, &.{}, &.{});
    _ = try carrier_tokens.appendToken(.eof, .{}, 10, 0, &.{}, &.{});

    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();

    const carrier_src = "  mod foo;";
    _ = try corex.parseTokens(
        carrier_src,
        FileId.fromInt(1),
        &carrier_tokens,
        &cst_arena,
        &ast_arena,
        null,
        null,
    );
    const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, carrier_src, &carrier_tokens);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(carrier_src, reconstructed);
}

// ---------------- Incremental & Red-Team Suite ----------------

test "test_parser_reparse_incremental_prefix_middle_suffix_and_fallback_edits" {
    const base_source =
        \\pub fn first_item(val: u32) -> u32 {
        \\    return val + 1;
        \\}
        \\
        \\pub fn second_item(val: u32) -> u32 {
        \\    return val + 2;
        \\}
        \\
        \\pub fn third_item(val: u32) -> u32 {
        \\    return val + 3;
        \\}
    ;

    var inc_tokens = TokenBuffer.init(std.testing.allocator);
    defer inc_tokens.deinit();
    var inc_cst = LosslessCstArena.init(std.testing.allocator);
    defer inc_cst.deinit();
    var inc_ast = AstArena.init(std.testing.allocator);
    defer inc_ast.deinit();

    _ = try corex.parseSource(base_source, FileId.fromInt(0), &inc_tokens, &inc_cst, &inc_ast, null, null);

    // [1] Middle-item growing edit (`val + 2` -> `val + 200_000`):
    const mid_source =
        \\pub fn first_item(val: u32) -> u32 {
        \\    return val + 1;
        \\}
        \\
        \\pub fn second_item(val: u32) -> u32 {
        \\    return val + 200_000;
        \\}
        \\
        \\pub fn third_item(val: u32) -> u32 {
        \\    return val + 3;
        \\}
    ;
    const mid_off: u32 = @intCast(std.mem.indexOf(u8, base_source, "val + 2").?);
    const mid_stats = try corex.reparseIncremental(
        mid_source,
        FileId.fromInt(0),
        .{ .start_byte = mid_off, .old_end_byte = mid_off + 7, .new_end_byte = mid_off + 13 },
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );
    try std.testing.expect(mid_stats.is_fast_splice);
    try std.testing.expectEqual(@as(u32, 1), mid_stats.reused_prefix_items);
    try std.testing.expectEqual(@as(u32, 1), mid_stats.reparsed_items);
    try std.testing.expectEqual(@as(u32, 1), mid_stats.reused_suffix_items);
    try expectIncrementalMatchesFullParse(mid_source, &inc_tokens, &inc_cst, &inc_ast);

    // [2] First-item shrinking edit (`val + 1` -> `val`):
    const first_source =
        \\pub fn first_item(val: u32) -> u32 {
        \\    return val;
        \\}
        \\
        \\pub fn second_item(val: u32) -> u32 {
        \\    return val + 200_000;
        \\}
        \\
        \\pub fn third_item(val: u32) -> u32 {
        \\    return val + 3;
        \\}
    ;
    const first_off: u32 = @intCast(std.mem.indexOf(u8, mid_source, "val + 1").?);
    const first_stats = try corex.reparseIncremental(
        first_source,
        FileId.fromInt(0),
        .{ .start_byte = first_off, .old_end_byte = first_off + 7, .new_end_byte = first_off + 3 },
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );
    try std.testing.expect(first_stats.is_fast_splice);
    try std.testing.expectEqual(@as(u32, 0), first_stats.reused_prefix_items);
    try std.testing.expectEqual(@as(u32, 1), first_stats.reparsed_items);
    try std.testing.expectEqual(@as(u32, 2), first_stats.reused_suffix_items);
    try expectIncrementalMatchesFullParse(first_source, &inc_tokens, &inc_cst, &inc_ast);

    // [3] Last-item edit (`val + 3` -> `val * 99`):
    const last_source =
        \\pub fn first_item(val: u32) -> u32 {
        \\    return val;
        \\}
        \\
        \\pub fn second_item(val: u32) -> u32 {
        \\    return val + 200_000;
        \\}
        \\
        \\pub fn third_item(val: u32) -> u32 {
        \\    return val * 99;
        \\}
    ;
    const last_off: u32 = @intCast(std.mem.indexOf(u8, first_source, "val + 3").?);
    const last_stats = try corex.reparseIncremental(
        last_source,
        FileId.fromInt(0),
        .{ .start_byte = last_off, .old_end_byte = last_off + 7, .new_end_byte = last_off + 8 },
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );
    try std.testing.expect(last_stats.is_fast_splice);
    try std.testing.expectEqual(@as(u32, 2), last_stats.reused_prefix_items);
    try std.testing.expectEqual(@as(u32, 1), last_stats.reparsed_items);
    try std.testing.expectEqual(@as(u32, 0), last_stats.reused_suffix_items);
    try expectIncrementalMatchesFullParse(last_source, &inc_tokens, &inc_cst, &inc_ast);

    // [4] Full-span fallback edit covering all items (`is_fast_splice == false`):
    const fallback_stats = try corex.reparseIncremental(
        base_source,
        FileId.fromInt(0),
        .{
            .start_byte = 0,
            .old_end_byte = @intCast(last_source.len),
            .new_end_byte = @intCast(base_source.len),
        },
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );
    try std.testing.expect(!fallback_stats.is_fast_splice);
    try expectIncrementalMatchesFullParse(base_source, &inc_tokens, &inc_cst, &inc_ast);
}

test "test_parser_red_team_adversarial_regressions_rt01_through_rt07" {
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    // [1] `RT-01` – Malformed path expressions (`foo::;` and `bar::123`) finish `.path_pat` CST subtree cleanly:
    const rt01_src = "fn rt01() { let a = foo::; let b = bar::123; }\n";
    _ = try corex.parseSource(rt01_src, FileId.fromInt(0), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expect(sink.error_count >= 2);
    try expectValidCstAndAstInvariants(rt01_src, &token_buf, &cst_arena, &ast_arena);

    // [2] `RT-02` – Empty `TokenBuffer` and non-`.eof`-terminated `TokenBuffer` terminate cleanly:
    var raw_tokens = TokenBuffer.init(std.testing.allocator);
    defer raw_tokens.deinit();
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();
    _ = try corex.parseTokens("", FileId.fromInt(1), &raw_tokens, &cst_arena, &ast_arena, null, null);
    try std.testing.expectEqual(@as(usize, 1), cst_arena.countNodes());

    _ = try raw_tokens.appendToken(.kw_fn, .{}, 0, 2, &.{}, &.{});
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();
    _ = try corex.parseTokens("fn", FileId.fromInt(1), &raw_tokens, &cst_arena, &ast_arena, null, null);
    try std.testing.expect(cst_arena.countNodes() >= 2);

    // [3] `RT-03` & `RT-04` – Bounded lookahead and `recoverDepthOverflow` when overflowing on `stop_set` token:
    const rt04_src = "mod outer { fn deep(val: ((((((((((i32))))))))))) -> i32 { return ((((((((((1)))))))))); } }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    token_buf.tokens.shrinkRetainingCapacity(0);
    token_buf.trivia.clearRetainingCapacity();
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();
    try corex.tokenize(rt04_src, FileId.fromInt(2), &token_buf, &sink, null);
    var capped_parser = Parser.initWithOptions(
        rt04_src,
        FileId.fromInt(2),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        null,
        .{ .max_depth = 5 },
    );
    _ = try capped_parser.parse();
    try std.testing.expect(sink.error_count >= 1);
    try expectValidCstAndAstInvariants(rt04_src, &token_buf, &cst_arena, &ast_arena);

    // [4] `RT-05` – `reparseIncremental` malformed `EditRange` guard falls back to full scratch parse:
    const rt05_stats = try corex.reparseIncremental(
        rt04_src,
        FileId.fromInt(2),
        .{ .start_byte = 12, .old_end_byte = 8, .new_end_byte = 6 },
        &token_buf,
        &cst_arena,
        &ast_arena,
        null,
        null,
    );
    try std.testing.expect(!rt05_stats.is_fast_splice);

    // [5] `RT-06` – Malformed patterns (`-true`, `1..`, `Foo::`) emit `E0201` without hanging:
    const rt06_src = "fn rt06(val: i32) -> i32 { return match val { -true => 1, 1.. => 2, Foo:: => 3 }; }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try corex.parseSource(rt06_src, FileId.fromInt(3), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expect(sink.error_count >= 3);
    try expectValidCstAndAstInvariants(rt06_src, &token_buf, &cst_arena, &ast_arena);

    // [6] `RT-07` – Generic & standard call with empty trailing view block `Card[u32](padding: 16) {}`:
    try expectCleanParse("fn rt07() { Card[u32](padding: 16) {} Row(gap: 8) {} }\n", &ast_arena, &cst_arena);
    try std.testing.expect(hasCstKind(&cst_arena, .view_block_expr));
}

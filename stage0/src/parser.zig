//! Fault-Tolerant Incremental Parser & Lossless CST-to-AST Lowerer
//!
//! Implements the explicit-stack `LL(k)` recursive-descent and 15-tier Pratt precedence-climbing
//! parser for the CoreX v1.0 surface grammar (`DR-03` Sections 5.3–5.5), producing a pre-order
//! `LosslessCstArena` and lowered Structure-of-Arrays `AstArena` in a single pass.
//!
//! Enforces `MAX_PARSE_DEPTH` (`512`, `E0203`), $O(1)$ 128-bit `TokenSet128` anchor synchronization
//! (`E0201`, `E0202`), cross-namespace casing recovery with in-place `W0201` autofixes, mid-keystroke
//! IDE completion nodes (`incomplete_member_access`, `incomplete_call`), and $O(K)$ top-level item
//! incremental re-parsing (`reparseIncremental`, `DR-12` Sections 1–2).

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const lexer = @import("lexer.zig");
const diagnostic = @import("diag/diagnostic.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const CstNodeIndex = mem_foundation.CstNodeIndex;
const NodeIndex = mem_foundation.NodeIndex;
const ExtraIndex = mem_foundation.ExtraIndex;
const PackedOperand = mem_foundation.PackedOperand;

const TokenKind = syntax_arenas.TokenKind;
const TokenFlags = syntax_arenas.TokenFlags;
const TokenRecord = syntax_arenas.TokenRecord;
const TriviaPiece = syntax_arenas.TriviaPiece;
const TokenBuffer = syntax_arenas.TokenBuffer;
const CstNodeKind = syntax_arenas.CstNodeKind;
const CstNodeFlags = syntax_arenas.CstNodeFlags;
const CstNodeRecord = syntax_arenas.CstNodeRecord;
const ParseStateKind = syntax_arenas.ParseStateKind;
const ParseState = syntax_arenas.ParseState;
const LosslessCstArena = syntax_arenas.LosslessCstArena;
const AstTag = syntax_arenas.AstTag;
const AstNode = syntax_arenas.AstNode;
const AstArena = syntax_arenas.AstArena;

const IdentifierCase = lexer.IdentifierCase;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const SuggestedFix = diagnostic.SuggestedFix;
const TextEdit = diagnostic.TextEdit;

// ---------------------------------------- TYPES ----------------------------------------

// --------------------- Token Sets & Edits ---------------------

/// 128-bit bitset indexing all 112 `TokenKind` variants (`0..111`) for $O(1)$ membership queries.
pub const TokenSet128 = struct {
    /// Underlying 128-bit bitmask where bit `@intFromEnum(kind)` encodes presence.
    mask: u128 = 0,

    /// Canonical empty token bitset constant.
    pub const EMPTY: TokenSet128 = .{ .mask = 0 };

    /// Constructs a `TokenSet128` containing a single `TokenKind`.
    pub inline fn initOne(kind: TokenKind) TokenSet128 {
        return .{ .mask = @as(u128, 1) << @intCast(@backingInt(kind)) };
    }

    /// Constructs a `TokenSet128` containing all token kinds in `kinds`.
    pub fn initMany(kinds: []const TokenKind) TokenSet128 {
        var combined_mask: u128 = 0;
        for (kinds) |kind_item| {
            combined_mask |= @as(u128, 1) << @intCast(@backingInt(kind_item));
        }
        return .{ .mask = combined_mask };
    }

    /// Returns `true` if `kind` is a member of `self` in $O(1)$ time.
    pub inline fn contains(self: TokenSet128, kind: TokenKind) bool {
        return ((self.mask >> @as(u7, @intCast(@backingInt(kind)))) & 1) != 0;
    }

    /// Returns the bitwise union (`self | other`) of two token sets.
    pub inline fn unionWith(self: TokenSet128, other: TokenSet128) TokenSet128 {
        return .{ .mask = self.mask | other.mask };
    }

    /// Returns the set difference (`self & ~other`) removing all tokens in `other`.
    pub inline fn without(self: TokenSet128, other: TokenSet128) TokenSet128 {
        return .{ .mask = self.mask & ~other.mask };
    }
};

/// 12-byte half-open source byte edit window describing a text modification for `reparseIncremental`.
pub const EditRange = extern struct {
    /// Inclusive starting byte offset of the edit in both the old and new source buffers.
    start_byte: u32,
    /// Exclusive ending byte offset of the replaced region in the old source buffer.
    old_end_byte: u32,
    /// Exclusive ending byte offset of the inserted region in the new source buffer.
    new_end_byte: u32,

    /// Returns the byte length removed from the old source buffer (`old_end_byte -| start_byte`).
    pub inline fn countOldBytes(self: EditRange) u32 {
        return self.old_end_byte -| self.start_byte;
    }

    /// Returns the byte length inserted into the new source buffer (`new_end_byte -| start_byte`).
    pub inline fn countNewBytes(self: EditRange) u32 {
        return self.new_end_byte -| self.start_byte;
    }
};

/// Telemetry and reuse metrics returned by `reparseIncremental` (`DR-12` Section 2).
pub const IncrementalReparseStats = struct {
    /// Number of untouched top-level prefix items `[0 .. p)` reused without re-lexing or re-parsing.
    reused_prefix_items: u32 = 0,
    /// Number of top-level items re-parsed within the modified window.
    reparsed_items: u32 = 0,
    /// Number of untouched top-level suffix items `[s .. K)` reused with shifted token/byte offsets.
    reused_suffix_items: u32 = 0,
    /// `true` if the incremental window splice succeeded without falling back to a full scratch parse.
    is_fast_splice: bool = false,
};

// ------------------- Parser State & Options -------------------

/// Configurable resource caps and lint toggles for `Parser`.
pub const ParserOptions = struct {
    /// Maximum explicit parser state stack depth before emitting `E0203` (`<= MAX_PARSE_DEPTH`).
    max_depth: usize = syntax_arenas.MAX_PARSE_DEPTH,
    /// When `true`, emits `W0201` warnings with `.machine_applicable` autofixes on casing mismatches.
    is_casing_warning_enabled: bool = true,
};

/// Pratt infix binding power pair `(left_bp, right_bp)` and non-associativity flag (`DR-03` Section 5.3).
const InfixBindingPower = struct {
    /// Left binding power checked against `min_bp` before consuming the operator.
    left_bp: u8,
    /// Right binding power passed as `min_bp` when parsing the right-hand operand.
    right_bp: u8,
    /// `true` for relational (`==`, `!=`, `<`, `<=`, `>`, `>=`) and range (`..`, `..=`) operators.
    is_non_associative: bool = false,
};

/// Top-level item CST and token boundary metadata used during `reparseIncremental` window discovery.
const TopLevelItemWindow = struct {
    /// Starting `CstNodeIndex` of this top-level item inside `LosslessCstArena.nodes`.
    cst_start: u32,
    /// Pre-order CST `subtree_size` of this top-level item.
    cst_len: u32,
    /// Inclusive first `TokenIndex` belonging to this item.
    first_token: u32,
    /// Exclusive ending `TokenIndex` (the `first_token` of the next sibling item or `.eof`).
    end_token: u32,
    /// Inclusive earliest byte offset of this item (including its first token's leading trivia).
    start_byte: u32,
    /// Exclusive ending byte offset of this item (where the next sibling's leading trivia begins).
    end_byte: u32,
};

// --------------------------------------- CONSTS ----------------------------------------

// -------------------- Synchronization Sets --------------------

/// Tokens that can legally begin a top-level `Item` after optional attributes and `pub`.
pub const ITEM_STARTER_SET: TokenSet128 = TokenSet128.initMany(&.{
    .at,
    .kw_pub,
    .kw_mod,
    .kw_use,
    .kw_const,
    .kw_type,
    .kw_struct,
    .kw_bit_field,
    .kw_enum,
    .kw_union,
    .kw_trait,
    .kw_impl,
    .kw_comptime,
    .kw_async,
    .kw_unsafe,
    .kw_extern,
    .kw_fn,
});
/// Tokens that can legally begin a statement inside a `Block`.
pub const STMT_STARTER_SET: TokenSet128 = TokenSet128.initMany(&.{
    .semi,
    .at,
    .kw_let,
    .kw_var,
    .kw_defer,
    .kw_errdefer,
    .kw_return,
    .kw_break,
    .kw_continue,
    .kw_for,
    .kw_while,
    .kw_loop,
    .kw_if,
    .kw_match,
    .kw_comptime,
});
/// Tokens that can legally begin a `PrimaryType` expression (`DR-03` Section 5.4 Part 5 & `DR-04`).
pub const TYPE_STARTER_SET: TokenSet128 = TokenSet128.initMany(&.{
    .prim_type,
    .kw_self_type,
    .amp,
    .star,
    .kw_own,
    .kw_ref,
    .hash_soa,
    .tilde,
    .lbracket,
    .lparen,
    .at,
    .kw_fn,
    .ident,
    .type_ident,
    .const_ident,
});
/// Consume-anchor set for top-level `Item` recovery (`DR-12` Section 2.2 Deliverable 2A).
pub const ITEM_CONSUME_SET: TokenSet128 = TokenSet128.initMany(&.{.semi});
/// Stop-before anchor set for top-level `Item` recovery (`DR-12` Section 2.2 Deliverable 2A).
pub const ITEM_STOP_SET: TokenSet128 = ITEM_STARTER_SET.unionWith(TokenSet128.initMany(&.{
    .rbrace,
    .eof,
}));
/// Consume-anchor set for `struct`, `union`, and `bit_field` member loops.
pub const STRUCT_FIELD_CONSUME_SET: TokenSet128 = TokenSet128.initMany(&.{ .comma, .semi });
/// Stop-before anchor set for `struct`, `union`, and `bit_field` member loops.
pub const STRUCT_FIELD_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rbrace,
    .at,
    .kw_pub,
    .ident,
    .type_ident,
    .const_ident,
    .eof,
}).unionWith(ITEM_STARTER_SET);
/// Consume-anchor set for `enum` variant declaration loops.
pub const ENUM_VARIANT_CONSUME_SET: TokenSet128 = TokenSet128.initMany(&.{ .comma, .semi });
/// Stop-before anchor set for `enum` variant declaration loops.
pub const ENUM_VARIANT_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rbrace,
    .at,
    .type_ident,
    .ident,
    .const_ident,
    .eof,
}).unionWith(ITEM_STARTER_SET);
/// Stop-before anchor set for `trait` and `impl` member declaration loops.
pub const MEMBER_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rbrace,
    .at,
    .kw_pub,
    .kw_type,
    .kw_const,
    .kw_comptime,
    .kw_async,
    .kw_unsafe,
    .kw_extern,
    .kw_fn,
    .eof,
});
/// Consume-anchor set for function parameter lists.
pub const PARAM_CONSUME_SET: TokenSet128 = TokenSet128.initMany(&.{.comma});
/// Stop-before anchor set for function parameter lists.
pub const PARAM_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rparen,
    .arrow,
    .kw_where,
    .lbrace,
    .semi,
    .kw_comptime,
    .kw_mut,
    .kw_own,
    .kw_ref,
    .amp,
    .kw_self_val,
    .ident,
    .underscore,
    .eof,
});
/// Stop-before anchor set for generic `[TypeParams]` and `[TypeArgs]` lists.
pub const TYPE_ARG_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rbracket,
    .lparen,
    .lbrace,
    .colon,
    .eq,
    .semi,
    .arrow,
    .kw_where,
    .rbrace,
    .rparen,
    .eof,
});
/// Consume-anchor set for `Block` statement loops.
pub const BLOCK_STMT_CONSUME_SET: TokenSet128 = TokenSet128.initMany(&.{.semi});
/// Stop-before anchor set for `Block` statement loops.
pub const BLOCK_STMT_STOP_SET: TokenSet128 = STMT_STARTER_SET.unionWith(TokenSet128.initMany(&.{
    .rbrace,
    .eof,
}));
/// Stop-before anchor set for local `let` / `var` initializer expressions.
pub const LOCAL_INIT_STOP_SET: TokenSet128 = STMT_STARTER_SET.unionWith(TokenSet128.initMany(&.{
    .kw_else,
    .rbrace,
    .eof,
}));
/// Consume-anchor set for `match` arm loops.
pub const MATCH_ARM_CONSUME_SET: TokenSet128 = TokenSet128.initMany(&.{.comma});
/// Stop-before anchor set for `match` arm loops.
pub const MATCH_ARM_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rbrace,
    .fat_arrow,
    .underscore,
    .dot,
    .type_ident,
    .const_ident,
    .ident,
    .int_lit,
    .float_lit,
    .string_lit,
    .char_lit,
    .kw_true,
    .kw_false,
    .lparen,
    .eof,
});
/// Stop-before anchor set for Pratt expressions and postfix call argument lists.
pub const EXPR_SYNC_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .comma,
    .rparen,
    .rbracket,
    .rbrace,
    .semi,
    .colon,
    .fat_arrow,
    .pipe_gt,
    .eof,
}).unionWith(STMT_STARTER_SET);
/// Bitset of all 11 statement-level assignment operators (`=`, `+=`, `-=`, `*=`, `/=`, `%=`, etc.).
pub const ASSIGN_OP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .eq,
    .plus_eq,
    .minus_eq,
    .star_eq,
    .slash_eq,
    .percent_eq,
    .amp_eq,
    .pipe_eq,
    .caret_eq,
    .shl_eq,
    .shr_eq,
});
/// Bitset of all 6 non-associative relational and equality operators (`==`, `!=`, `<`, `<=`, `>`, `>=`).
pub const RELATIONAL_OP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .eqeq,
    .bang_eq,
    .lt,
    .le,
    .gt,
    .ge,
});
/// Bitset of non-associative range operators (`..`, `..=`).
pub const RANGE_OP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .dotdot,
    .dotdoteq,
});

// -------------------------------------- INTERNALS --------------------------------------

// ------------------- Pratt & Token Helpers --------------------

/// Returns `true` if `record` is a zero-length synthesized trivia carrier token (`!has_lexer_error`).
inline fn isCarrierToken(record: TokenRecord) bool {
    return record.kind == .invalid_token and record.flags.is_synthesized and !record.flags.has_lexer_error;
}

/// Returns `true` if `kind` belongs to one of the three cased identifier categories.
inline fn isIdentifierKind(kind: TokenKind) bool {
    return kind == .ident or kind == .type_ident or kind == .const_ident;
}

/// Returns `true` if `kind` is one of the 45 language keywords (`0..44`).
inline fn isKeywordKind(kind: TokenKind) bool {
    return @backingInt(kind) <= @backingInt(TokenKind.kw_self_type);
}

/// Returns `true` if `kind` is one of the 11 assignment operators (`DR-03` Section 5.3 Tier 0).
inline fn isAssignOp(kind: TokenKind) bool {
    return ASSIGN_OP_SET.contains(kind);
}

/// Returns `true` if `kind` is a non-associative relational or equality operator (`DR-03` Tier 4).
inline fn isRelationalOp(kind: TokenKind) bool {
    return RELATIONAL_OP_SET.contains(kind);
}

/// Returns `true` if `kind` is a non-associative range constructor operator (`..` or `..=`, Tier 5).
inline fn isRangeOp(kind: TokenKind) bool {
    return RANGE_OP_SET.contains(kind);
}

/// Returns `true` if `kind` is a scalar value literal (`int`, `float`, `string`, `char`, `bool`).
inline fn isLiteralToken(kind: TokenKind) bool {
    return switch (kind) {
        .int_lit, .float_lit, .string_lit, .char_lit, .kw_true, .kw_false => true,
        else => false,
    };
}

/// Returns `true` if `kind` is a closing delimiter (`}`, `)`, `]`) or `.eof`.
inline fn isClosingDelimiter(kind: TokenKind) bool {
    return switch (kind) {
        .rbrace, .rparen, .rbracket, .eof => true,
        else => false,
    };
}

/// Returns `true` if `tag` is a block-bodied expression that may omit a trailing `;` in statement position.
inline fn isBlockBodiedAstTag(tag: AstTag) bool {
    return switch (tag) {
        .block, .if_expr, .match_expr, .loop_expr => true,
        else => false,
    };
}

/// Returns the right binding power (`26`) for unary prefix operators (`DR-03` Section 5.3 Tier 13).
inline fn getPrefixRightBindingPower(kind: TokenKind) ?u8 {
    return switch (kind) {
        .minus,
        .minus_percent,
        .bang,
        .kw_not,
        .tilde,
        .star,
        .amp,
        .kw_own,
        .kw_ref,
        => 26,
        else => null,
    };
}

/// Returns the Pratt `(left_bp, right_bp, is_non_associative)` descriptor for `kind` (`DR-03` Section 5.3).
fn getInfixBindingPower(kind: TokenKind) ?InfixBindingPower {
    return switch (kind) {
        // Tier 12 – Explicit Type Cast (`as Type`):
        .kw_as => .{ .left_bp = 24, .right_bp = 25 },
        // Tier 11 – Multiplicative (`*`, `/`, `%`, `*%`, `*|`):
        .star, .slash, .percent, .star_percent, .star_pipe => .{ .left_bp = 22, .right_bp = 23 },
        // Tier 10 – Additive (`+`, `-`, `+%`, `-%`, `+|`, `-|`):
        .plus, .minus, .plus_percent, .minus_percent, .plus_pipe, .minus_pipe => .{
            .left_bp = 20,
            .right_bp = 21,
        },
        // Tier 9 – Bitwise Shift (`<<`, `>>`):
        .shl, .shr => .{ .left_bp = 18, .right_bp = 19 },
        // Tier 8 – Bitwise AND (`&`):
        .amp => .{ .left_bp = 16, .right_bp = 17 },
        // Tier 7 – Bitwise XOR (`^`):
        .caret => .{ .left_bp = 14, .right_bp = 15 },
        // Tier 6 – Bitwise OR (`|`):
        .pipe => .{ .left_bp = 12, .right_bp = 13 },
        // Tier 5 – Range Constructors (`..`, `..=`), Non-Associative:
        .dotdot, .dotdoteq => .{ .left_bp = 10, .right_bp = 11, .is_non_associative = true },
        // Tier 4.5 – Inline Pattern Test (`is Pattern`), Non-Associative:
        .kw_is => .{ .left_bp = 9, .right_bp = 10, .is_non_associative = true },
        // Tier 4 – Relational & Equality (`==`, `!=`, `<`, `<=`, `>`, `>=`), Non-Associative:
        .eqeq, .bang_eq, .lt, .le, .gt, .ge => .{
            .left_bp = 8,
            .right_bp = 9,
            .is_non_associative = true,
        },
        // Tier 3 – Logical Short-Circuit AND (`&&`, `and`):
        .ampamp, .kw_and => .{ .left_bp = 6, .right_bp = 7 },
        // Tier 2 – Logical Short-Circuit OR (`||`, `or`):
        .pipepipe, .kw_or => .{ .left_bp = 4, .right_bp = 5 },
        // Tier 1.5 – Inline Error Fallback (`catch`), Right-to-Left:
        .kw_catch => .{ .left_bp = 3, .right_bp = 2 },
        // Tier 1 – Data Transformation Pipeline (`|>`):
        .pipe_gt => .{ .left_bp = 2, .right_bp = 3 },
        else => null,
    };
}

// -------------------- Incremental Helpers ---------------------

/// Returns the earliest source byte offset covered by `token_id`, including its leading trivia pieces.
fn getTokenEarliestByte(token_buffer: *const TokenBuffer, token_id: TokenIndex) u32 {
    const leading_pieces = token_buffer.getLeadingTrivia(token_id);
    if (leading_pieces.len > 0) {
        return leading_pieces[0].byte_offset;
    }
    return token_buffer.getToken(token_id).byte_offset;
}

/// Returns `true` if `token_buffer` and `cst_arena` contain zero lexical, synthesis, or syntax errors.
fn hasCleanTokensAndCst(
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) bool {
    if (cst_arena.has_parse_errors or cst_arena.countNodes() < 2) return false;
    if (token_buffer.countTokens() == 0) return false;

    const root_rec = cst_arena.getNode(CstNodeIndex.fromInt(0));
    if (root_rec.kind != .file_end or root_rec.subtree_size != cst_arena.countNodes()) {
        return false;
    }

    const token_count = token_buffer.countTokens();
    const flag_slice = token_buffer.tokens.items(.flags);
    const kind_slice = token_buffer.tokens.items(.kind);
    if (kind_slice[token_count - 1] != .eof) return false;

    var i: usize = 0;
    while (i < token_count) : (i += 1) {
        const flags = flag_slice[i];
        if (flags.has_lexer_error or flags.is_synthesized) return false;
    }
    return true;
}

/// Walks top-level CST children of `.source_file` in $O(K)$ steps using `subtree_size`.
fn extractTopLevelItemWindows(
    allocator: std.mem.Allocator,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) ![]TopLevelItemWindow {
    var windows: std.ArrayList(TopLevelItemWindow) = .empty;
    errdefer windows.deinit(allocator);

    const total_cst = cst_arena.countNodes();
    if (total_cst < 2) return windows.toOwnedSlice(allocator);

    const eof_cst_idx: u32 = @intCast(total_cst - 1);
    var cst_cursor: u32 = 1;
    while (cst_cursor < eof_cst_idx) {
        const node_rec = cst_arena.getNode(CstNodeIndex.fromInt(cst_cursor));
        if (node_rec.subtree_size == 0 or cst_cursor + node_rec.subtree_size > eof_cst_idx) {
            break;
        }
        const next_cst_idx = cst_cursor + node_rec.subtree_size;
        const next_node_rec = cst_arena.getNode(CstNodeIndex.fromInt(next_cst_idx));
        const first_tok = node_rec.token;
        const next_first_tok = next_node_rec.token;

        try windows.append(allocator, .{
            .cst_start = cst_cursor,
            .cst_len = node_rec.subtree_size,
            .first_token = first_tok.asInt(),
            .end_token = next_first_tok.asInt(),
            .start_byte = getTokenEarliestByte(token_buffer, first_tok),
            .end_byte = getTokenEarliestByte(token_buffer, next_first_tok),
        });
        cst_cursor = next_cst_idx;
    }
    return windows.toOwnedSlice(allocator);
}

/// Splices `window_tokens` (excluding its trailing `.eof` when `is_keeping_window_eof == false`) into `dest`.
fn spliceTokenBufferWindow(
    dest: *TokenBuffer,
    tok_start: usize,
    tok_old_end: usize,
    window_tokens: *const TokenBuffer,
    is_keeping_window_eof: bool,
    byte_delta: i64,
) !void {
    const win_tok_len = if (is_keeping_window_eof)
        window_tokens.countTokens()
    else
        window_tokens.countTokens() -| 1;

    // [1] Determine trivia slice range `[triv_start .. triv_old_end)` in `dest.trivia`:
    const old_tok_total = dest.countTokens();
    const triv_start: usize = if (tok_start < old_tok_total)
        dest.tokens.items(.trivia_span)[tok_start].start_index
    else
        dest.trivia.items.len;
    const triv_old_end: usize = if (tok_old_end < old_tok_total)
        dest.tokens.items(.trivia_span)[tok_old_end].start_index
    else
        dest.trivia.items.len;

    const win_triv_len: usize = if (is_keeping_window_eof)
        window_tokens.trivia.items.len
    else if (win_tok_len < window_tokens.countTokens())
        window_tokens.tokens.items(.trivia_span)[win_tok_len].start_index
    else
        window_tokens.trivia.items.len;

    // [2] Rebuild `dest.trivia` with prefix, window trivia, and byte-shifted suffix trivia:
    var new_trivia: std.ArrayList(TriviaPiece) = .empty;
    errdefer new_trivia.deinit(dest.allocator);
    try new_trivia.ensureTotalCapacity(
        dest.allocator,
        triv_start + win_triv_len + (dest.trivia.items.len - triv_old_end),
    );

    new_trivia.appendSliceAssumeCapacity(dest.trivia.items[0..triv_start]);
    new_trivia.appendSliceAssumeCapacity(window_tokens.trivia.items[0..win_triv_len]);
    for (dest.trivia.items[triv_old_end..]) |suffix_piece| {
        var shifted_piece = suffix_piece;
        shifted_piece.byte_offset = @intCast(@as(i64, suffix_piece.byte_offset) + byte_delta);
        new_trivia.appendAssumeCapacity(shifted_piece);
    }
    dest.trivia.deinit(dest.allocator);
    dest.trivia = new_trivia;

    // [3] Rebuild `dest.tokens` with prefix, trivia-shifted window tokens, and shifted suffix tokens:
    var new_tokens: std.MultiArrayList(TokenRecord) = .empty;
    errdefer new_tokens.deinit(dest.allocator);
    try new_tokens.ensureTotalCapacity(
        dest.allocator,
        tok_start + win_tok_len + (old_tok_total - tok_old_end),
    );

    var i: usize = 0;
    while (i < tok_start) : (i += 1) {
        new_tokens.appendAssumeCapacity(dest.tokens.get(i));
    }
    i = 0;
    while (i < win_tok_len) : (i += 1) {
        var win_rec = window_tokens.tokens.get(i);
        win_rec.trivia_span.start_index = @intCast(@as(usize, win_rec.trivia_span.start_index) + triv_start);
        new_tokens.appendAssumeCapacity(win_rec);
    }
    const trivia_delta: i64 = @as(i64, @intCast(win_triv_len)) - @as(i64, @intCast(triv_old_end - triv_start));
    i = tok_old_end;
    while (i < old_tok_total) : (i += 1) {
        var suffix_rec = dest.tokens.get(i);
        suffix_rec.byte_offset = @intCast(@as(i64, suffix_rec.byte_offset) + byte_delta);
        suffix_rec.trivia_span.start_index = @intCast(
            @as(i64, suffix_rec.trivia_span.start_index) + trivia_delta,
        );
        new_tokens.appendAssumeCapacity(suffix_rec);
    }
    dest.tokens.deinit(dest.allocator);
    dest.tokens = new_tokens;
}

/// Splices `window_cst` nodes into `dest.nodes[cst_start .. cst_old_end)` and shifts suffix token IDs.
fn spliceCstArenaWindow(
    dest: *LosslessCstArena,
    cst_start: usize,
    cst_old_end: usize,
    window_cst: *const LosslessCstArena,
    token_delta: i64,
) !void {
    const old_cst_total = dest.countNodes();
    const win_cst_len = window_cst.countNodes();

    var new_nodes: std.MultiArrayList(CstNodeRecord) = .empty;
    errdefer new_nodes.deinit(dest.allocator);
    try new_nodes.ensureTotalCapacity(
        dest.allocator,
        cst_start + win_cst_len + (old_cst_total - cst_old_end),
    );

    var i: usize = 0;
    while (i < cst_start) : (i += 1) {
        new_nodes.appendAssumeCapacity(dest.nodes.get(i));
    }
    i = 0;
    while (i < win_cst_len) : (i += 1) {
        new_nodes.appendAssumeCapacity(window_cst.nodes.get(i));
    }
    i = cst_old_end;
    while (i < old_cst_total) : (i += 1) {
        var suffix_node = dest.nodes.get(i);
        if (!suffix_node.token.isNone()) {
            suffix_node.token = TokenIndex.fromInt(
                @intCast(@as(i64, suffix_node.token.asInt()) + token_delta),
            );
        }
        new_nodes.appendAssumeCapacity(suffix_node);
    }

    dest.nodes.deinit(dest.allocator);
    dest.nodes = new_nodes;
    dest.has_parse_errors = dest.has_parse_errors or window_cst.has_parse_errors;
    if (dest.nodes.len > 0) {
        dest.nodes.items(.subtree_size)[0] = @intCast(dest.nodes.len);
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------------- Parser Implementation --------------------

/// Fault-tolerant `LL(k)` + Pratt precedence-climbing parser and lossless CST-to-AST lowerer.
pub const Parser = struct {
    /// Original UTF-8 source buffer corresponding to `token_buffer`.
    source: []const u8,
    /// Canonical `FileId` for diagnostic span and `TextEdit` generation.
    file_id: FileId,
    /// Read-only Structure-of-Arrays token and trivia buffer produced by `Lexer`.
    token_buffer: *const TokenBuffer,
    /// Target pre-order `LosslessCstArena` populated during parsing.
    cst: *LosslessCstArena,
    /// Target Structure-of-Arrays `AstArena` populated during parsing.
    ast: *AstArena,
    /// Optional diagnostic collector receiving `E0201`–`E0203` errors and `W0201` warnings.
    diagnostic_sink: ?*DiagnosticSink = null,
    /// Optional string interner used to intern `.machine_applicable` `W0201` replacement strings.
    interner: ?*StringInterner = null,
    /// Configurable recursion depth limit and warning flags.
    options: ParserOptions = .{},
    /// Current token index cursor into `token_buffer` (`0 .. token_buffer.countTokens()`).
    cursor: u32 = 0,
    /// `true` while unwinding an active `error.ParseDepthExceeded` recovery (`E0203`).
    is_recovering_depth_overflow: bool = false,
    /// `true` if the most recently completed expression in the current statement ended with a `{ … }` block.
    has_last_expr_block_body: bool = false,
    /// `true` while parsing the candidate LHS lvalue of a block expression/assignment statement.
    is_in_stmt_lhs: bool = false,

    /// Initializes a `Parser` with default `ParserOptions`.
    pub fn init(
        source: []const u8,
        file_id: FileId,
        token_buffer: *const TokenBuffer,
        cst_arena: *LosslessCstArena,
        ast_arena: *AstArena,
        diagnostic_sink: ?*DiagnosticSink,
        interner: ?*StringInterner,
    ) Parser {
        return initWithOptions(
            source,
            file_id,
            token_buffer,
            cst_arena,
            ast_arena,
            diagnostic_sink,
            interner,
            .{},
        );
    }

    /// Initializes a `Parser` with explicit `ParserOptions`.
    pub fn initWithOptions(
        source: []const u8,
        file_id: FileId,
        token_buffer: *const TokenBuffer,
        cst_arena: *LosslessCstArena,
        ast_arena: *AstArena,
        diagnostic_sink: ?*DiagnosticSink,
        interner: ?*StringInterner,
        options: ParserOptions,
    ) Parser {
        return .{
            .source = source,
            .file_id = file_id,
            .token_buffer = token_buffer,
            .cst = cst_arena,
            .ast = ast_arena,
            .diagnostic_sink = diagnostic_sink,
            .interner = interner,
            .options = options,
        };
    }

    /// Parses the entire `token_buffer` into `self.cst` and `self.ast`, returning `NodeIndex.root` (`0`).
    pub fn parse(self: *Parser) !NodeIndex {
        self.cst.parse_stack.clearRetainingCapacity();
        self.is_recovering_depth_overflow = false;

        try self.flushCarrierTokens();
        const first_tok = self.peekTokenIndexNth(0);
        const root_cst = try self.cst.startNode(.source_file, first_tok);
        const root_ast = try self.ast.appendNodeWithCst(.{
            .tag = .root,
            .main_token = first_tok,
        }, root_cst);

        var item_indices: std.ArrayList(u32) = .empty;
        defer item_indices.deinit(self.ast.allocator);

        while (self.peekKind() != .eof) {
            const cursor_before = self.cursor;
            self.is_recovering_depth_overflow = false;
            try item_indices.append(self.ast.allocator, (try self.parseItem()).asInt());

            // Guarantee strict monotonic forward progress at top level:
            if (self.cursor == cursor_before and self.peekKind() != .eof) {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }

        // Consume the final `.eof` token as a CST leaf so 100% of tokens are covered:
        try self.flushCarrierTokens();
        if (self.cursor < self.token_buffer.countTokens()) {
            const eof_tok = TokenIndex.fromInt(self.cursor);
            const eof_rec = self.token_buffer.getToken(eof_tok);
            _ = try self.cst.appendLeafNode(.token_leaf, eof_tok, .{
                .has_error = eof_rec.flags.has_lexer_error,
                .is_missing_or_injected = eof_rec.flags.is_synthesized,
            });
            self.cursor += 1;
        }

        self.cst.finishNode(root_cst, .{ .has_error = self.cst.has_parse_errors });

        if (item_indices.items.len > 0) {
            self.ast.nodes.items(.lhs)[root_ast.asInt()] = PackedOperand.initExtra(
                try self.ast.appendExtraSlice(item_indices.items),
            );
            self.ast.nodes.items(.rhs)[root_ast.asInt()] = .{
                .tag = .extra,
                .payload = @intCast(item_indices.items.len),
            };
        }
        return root_ast;
    }

    /// Flushes any pending pure trivia carrier tokens at `self.cursor` into `self.cst`.
    fn flushCarrierTokens(self: *Parser) !void {
        const total_tokens = self.token_buffer.countTokens();
        while (self.cursor < total_tokens) {
            const token_id = TokenIndex.fromInt(self.cursor);
            const record = self.token_buffer.getToken(token_id);
            if (!isCarrierToken(record)) break;
            _ = try self.cst.appendLeafNode(.token_leaf, token_id, .{
                .is_missing_or_injected = true,
            });
            self.cursor += 1;
        }
    }

    /// Returns the `TokenIndex` at `lookahead` non-carrier tokens ahead of `self.cursor`.
    fn peekTokenIndexNth(self: *const Parser, lookahead: usize) TokenIndex {
        const total_tokens = self.token_buffer.countTokens();
        if (total_tokens == 0 or self.cursor >= total_tokens) {
            return TokenIndex.fromInt(@intCast(total_tokens));
        }

        var scan_idx: usize = self.cursor;
        var remaining: usize = lookahead;
        while (scan_idx < total_tokens) : (scan_idx += 1) {
            const candidate_id = TokenIndex.fromInt(@intCast(scan_idx));
            if (isCarrierToken(self.token_buffer.getToken(candidate_id))) continue;
            if (remaining == 0 or scan_idx + 1 == total_tokens) {
                return candidate_id;
            }
            remaining -= 1;
        }
        return TokenIndex.fromInt(@intCast(total_tokens));
    }

    /// Returns the `TokenRecord` at `lookahead` non-carrier tokens ahead of `self.cursor`.
    fn peekNth(self: *const Parser, lookahead: usize) TokenRecord {
        const tok_idx = self.peekTokenIndexNth(lookahead);
        if (tok_idx.asInt() >= self.token_buffer.countTokens()) {
            return .{
                .kind = .eof,
                .flags = .{ .is_synthesized = true },
                .byte_offset = @intCast(self.source.len),
                .byte_len = 0,
                .trivia_span = .{},
            };
        }
        return self.token_buffer.getToken(tok_idx);
    }

    /// Returns the `TokenKind` of the current non-carrier token (`peekNth(0).kind`).
    inline fn peekKind(self: *const Parser) TokenKind {
        return self.peekNth(0).kind;
    }

    /// Returns the `TokenKind` at `lookahead` non-carrier tokens ahead of `self.cursor`.
    inline fn peekKindNth(self: *const Parser, lookahead: usize) TokenKind {
        return self.peekNth(lookahead).kind;
    }

    /// Returns the source `Span` for `token_id`, clamping out-of-bounds synthetic EOF indices.
    fn getTokenSpan(self: *const Parser, token_id: TokenIndex) Span {
        if (token_id.asInt() >= self.token_buffer.countTokens()) {
            const end_off: u32 = @intCast(self.source.len);
            return .{
                .file_id = self.file_id,
                .start_byte = end_off,
                .end_byte = end_off,
            };
        }
        return self.token_buffer.getTokenSpan(self.file_id, token_id);
    }

    /// Returns the UTF-8 source slice of `token_id`.
    fn getTokenLexeme(self: *const Parser, token_id: TokenIndex) []const u8 {
        if (token_id.asInt() >= self.token_buffer.countTokens()) return "";
        const record = self.token_buffer.getToken(token_id);
        const start_off: usize = record.byte_offset;
        const end_off: usize = @min(start_off + @as(usize, record.byte_len), self.source.len);
        return self.source[start_off..end_off];
    }

    /// Returns the UTF-8 source slice of the token at `lookahead` non-carrier tokens ahead.
    fn peekLexemeNth(self: *const Parser, lookahead: usize) []const u8 {
        return self.getTokenLexeme(self.peekTokenIndexNth(lookahead));
    }

    /// Consumes the current non-carrier token (after flushing carriers) and appends a CST leaf node.
    fn consumeLeaf(self: *Parser, cst_kind: CstNodeKind, extra_flags: CstNodeFlags) !TokenIndex {
        try self.flushCarrierTokens();
        const total_tokens = self.token_buffer.countTokens();
        if (self.cursor >= total_tokens) {
            const fallback_tok = TokenIndex.fromInt(@intCast(total_tokens -| 1));
            _ = try self.cst.appendLeafNode(cst_kind, fallback_tok, .{
                .has_error = extra_flags.has_error,
                .is_missing_or_injected = true,
                .is_bracketed = extra_flags.is_bracketed,
                .child_arity_small = extra_flags.child_arity_small,
            });
            return fallback_tok;
        }

        const token_id = TokenIndex.fromInt(self.cursor);
        const record = self.token_buffer.getToken(token_id);
        const is_lexer_non_case_err = record.flags.has_lexer_error and !isIdentifierKind(record.kind);
        _ = try self.cst.appendLeafNode(cst_kind, token_id, .{
            .has_error = extra_flags.has_error or is_lexer_non_case_err,
            .is_missing_or_injected = extra_flags.is_missing_or_injected or record.flags.is_synthesized,
            .is_bracketed = extra_flags.is_bracketed,
            .child_arity_small = extra_flags.child_arity_small,
        });

        // Advance `self.cursor` across non-EOF tokens (or when more tokens follow):
        if (record.kind != .eof or self.cursor + 1 < total_tokens) {
            self.cursor += 1;
        }
        return token_id;
    }

    /// Starts a pre-order composite CST node after flushing any pending trivia carrier tokens.
    fn startCstNode(self: *Parser, kind: CstNodeKind) !CstNodeIndex {
        try self.flushCarrierTokens();
        return self.cst.startNode(kind, self.peekTokenIndexNth(0));
    }

    /// Inserts a composite CST parent node at `lhs_cst_start` before an already-parsed left-hand child.
    pub fn precedeNode(
        self: *Parser,
        lhs_cst_start: CstNodeIndex,
        lhs_ast_start: usize,
        kind: CstNodeKind,
        token: TokenIndex,
    ) !CstNodeIndex {
        const insert_idx: usize = lhs_cst_start.asInt();
        const old_len: usize = self.cst.countNodes();
        std.debug.assert(insert_idx <= old_len);

        if (old_len >= syntax_arenas.MAX_CST_NODES) return error.CstNodeLimitExceeded;
        try self.cst.nodes.append(self.cst.allocator, .{
            .kind = kind,
            .flags = .{ .is_bracketed = true },
            .token = token,
            .subtree_size = 1,
        });

        if (insert_idx < old_len) {
            const kinds_slice = self.cst.nodes.items(.kind);
            const flags_slice = self.cst.nodes.items(.flags);
            const tokens_slice = self.cst.nodes.items(.token);
            const sizes_slice = self.cst.nodes.items(.subtree_size);

            std.mem.copyBackwards(
                CstNodeKind,
                kinds_slice[insert_idx + 1 .. old_len + 1],
                kinds_slice[insert_idx..old_len],
            );
            std.mem.copyBackwards(
                CstNodeFlags,
                flags_slice[insert_idx + 1 .. old_len + 1],
                flags_slice[insert_idx..old_len],
            );
            std.mem.copyBackwards(
                TokenIndex,
                tokens_slice[insert_idx + 1 .. old_len + 1],
                tokens_slice[insert_idx..old_len],
            );
            std.mem.copyBackwards(
                u32,
                sizes_slice[insert_idx + 1 .. old_len + 1],
                sizes_slice[insert_idx..old_len],
            );

            kinds_slice[insert_idx] = kind;
            flags_slice[insert_idx] = .{ .is_bracketed = true };
            tokens_slice[insert_idx] = token;
            sizes_slice[insert_idx] = 1;
        }

        // Shift `ast_to_cst` origins for AST nodes created inside the LHS subtree:
        var ast_idx: usize = lhs_ast_start;
        while (ast_idx < self.ast.ast_to_cst.items.len) : (ast_idx += 1) {
            const origin = self.ast.ast_to_cst.items[ast_idx];
            if (!origin.isNone() and origin.asInt() >= insert_idx) {
                self.ast.ast_to_cst.items[ast_idx] = CstNodeIndex.fromInt(origin.asInt() + 1);
            }
        }
        return lhs_cst_start;
    }

    /// Pushes `state` onto `self.cst.parse_stack`, enforcing `self.options.max_depth` (`E0203`).
    fn pushState(self: *Parser, kind: ParseStateKind, subtree_start: CstNodeIndex) !void {
        if (self.cst.parse_stack.items.len >= self.options.max_depth) {
            return error.ParseDepthExceeded;
        }
        try self.cst.pushParseState(.{
            .kind = kind,
            .subtree_start = subtree_start.asInt(),
        });
    }

    /// Pops `count` frames from `self.cst.parse_stack`.
    fn popStates(self: *Parser, count: usize) void {
        var i: usize = 0;
        while (i < count) : (i += 1) {
            _ = self.cst.popParseState();
        }
    }

    /// Emits `E0201` (`e0201_unexpected_token`) at `token_id` unless it is a pre-diagnosed lexer error.
    fn emitUnexpectedToken(
        self: *Parser,
        token_id: TokenIndex,
        message: []const u8,
        label_text: []const u8,
    ) !void {
        if (token_id.asInt() < self.token_buffer.countTokens()) {
            const record = self.token_buffer.getToken(token_id);
            if (record.kind == .invalid_token and record.flags.has_lexer_error) {
                return;
            }
        }
        const sink = self.diagnostic_sink orelse return;
        const token_span = self.getTokenSpan(token_id);
        const labels = [_]LabeledSpan{.{
            .span = token_span,
            .label = label_text,
            .style = .primary,
        }};
        try sink.emit(.{
            .code = .e0201_unexpected_token,
            .severity = .err,
            .primary_span = token_span,
            .labels = &labels,
            .message = message,
        });
    }

    /// Emits `E0202` (`e0202_unclosed_delimiter`) with primary span at cursor and secondary at `open_tok`.
    fn emitUnclosedDelimiter(
        self: *Parser,
        open_tok: TokenIndex,
        expected_close_desc: []const u8,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const current_tok = self.peekTokenIndexNth(0);
        const current_span = self.getTokenSpan(current_tok);
        const open_span = self.getTokenSpan(open_tok);
        const labels = [_]LabeledSpan{
            .{
                .span = current_span,
                .label = expected_close_desc,
                .style = .primary,
            },
            .{
                .span = open_span,
                .label = "unclosed delimiter opened here",
                .style = .secondary,
            },
        };
        try sink.emit(.{
            .code = .e0202_unclosed_delimiter,
            .severity = .err,
            .primary_span = current_span,
            .message = "unclosed block, group, or generic delimiter",
            .labels = &labels,
        });
    }

    /// Emits `E0203` (`e0203_parse_depth_exceeded`) once and non-recursively skips balanced tokens.
    fn recoverDepthOverflow(
        self: *Parser,
        cst_start: CstNodeIndex,
        stop_set: TokenSet128,
        hole_tag: AstTag,
    ) !NodeIndex {
        const err_tok = self.peekTokenIndexNth(0);
        if (!self.is_recovering_depth_overflow) {
            self.is_recovering_depth_overflow = true;
            if (self.diagnostic_sink) |sink| {
                const err_span = self.getTokenSpan(err_tok);
                const labels = [_]LabeledSpan{.{
                    .span = err_span,
                    .label = "maximum parser recursion depth exceeded here",
                    .style = .primary,
                }};
                try sink.emit(.{
                    .code = .e0203_parse_depth_exceeded,
                    .severity = .err,
                    .primary_span = err_span,
                    .message = "parser recursion depth limit exceeded",
                    .labels = &labels,
                });
            }
        }

        // Non-recursively consume balanced delimiter groups until reaching `stop_set` at depth 0:
        var delim_depth: u32 = 0;
        var has_consumed_any = false;
        while (self.peekKind() != .eof) {
            const cur_kind = self.peekKind();
            if (delim_depth == 0) {
                if (cur_kind == .rbrace or
                    cur_kind == .rparen or
                    cur_kind == .rbracket or
                    cur_kind == .semi or
                    cur_kind == .comma)
                {
                    break;
                }
                if (has_consumed_any and stop_set.contains(cur_kind)) {
                    break;
                }
            }
            if (cur_kind == .lbrace or cur_kind == .lparen or cur_kind == .lbracket) {
                delim_depth += 1;
            } else if (cur_kind == .rbrace or cur_kind == .rparen or cur_kind == .rbracket) {
                if (delim_depth == 0) break;
                delim_depth -= 1;
            }
            _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            has_consumed_any = true;
        }

        self.cst.nodes.items(.kind)[cst_start.asInt()] = .invalid_parse_subtree;
        self.cst.finishNode(cst_start, .{ .has_error = true });
        return self.ast.appendNodeWithCst(.{
            .tag = hole_tag,
            .main_token = err_tok,
        }, cst_start);
    }

    /// Emits or updates in-place `W0201` (`w0201_non_canonical_identifier_case`) for `token_id`.
    fn emitOrUpdateCasingWarning(
        self: *Parser,
        token_id: TokenIndex,
        expected_case: IdentifierCase,
    ) !void {
        if (!self.options.is_casing_warning_enabled) return;
        const sink = self.diagnostic_sink orelse return;
        const ident_span = self.getTokenSpan(token_id);
        const lexeme = self.getTokenLexeme(token_id);

        const label_msg = switch (expected_case) {
            .snake_case => "value/function/field/module identifiers must use `snake_case`",
            .pascal_case => "type/trait/variant identifiers must use `PascalCase` without underscores",
            .screaming_snake_case => "constant identifiers must use `SCREAMING_SNAKE_CASE`",
            .reserved_or_wildcard => "identifier does not follow canonical CoreX casing",
        };

        var fix_slice: []const SuggestedFix = &.{};
        var local_edit: [1]TextEdit = undefined;
        var local_fix: [1]SuggestedFix = undefined;
        if (self.interner) |str_interner| {
            const converted = switch (expected_case) {
                .snake_case => try lexer.toSnakeCase(sink.arena.asAllocator(), lexeme),
                .pascal_case => try lexer.toPascalCase(sink.arena.asAllocator(), lexeme),
                .screaming_snake_case => try lexer.toScreamingSnakeCase(sink.arena.asAllocator(), lexeme),
                .reserved_or_wildcard => lexeme,
            };
            local_edit[0] = .{
                .file_id = self.file_id,
                .start_byte = ident_span.start_byte,
                .end_byte = ident_span.end_byte,
                .replacement_id = try str_interner.intern(converted),
            };
            local_fix[0] = .{
                .message = "convert identifier to canonical CoreX casing",
                .applicability = .machine_applicable,
                .priority = .lint_idiom,
                .edits = &local_edit,
            };
            fix_slice = &local_fix;
        }

        // Update any existing `lexer` `W0201` at `ident_span` in-place with the slot-specific autofix:
        for (sink.diagnostics.items) |*existing_diag| {
            if (existing_diag.code == .w0201_non_canonical_identifier_case and
                existing_diag.primary_span.file_id == ident_span.file_id and
                existing_diag.primary_span.start_byte == ident_span.start_byte and
                existing_diag.primary_span.end_byte == ident_span.end_byte)
            {
                const cloned_labels = try sink.arena.allocSlice(LabeledSpan, 1);
                cloned_labels[0] = .{
                    .span = ident_span,
                    .label = try sink.arena.dupe(u8, label_msg),
                    .style = .primary,
                };
                existing_diag.labels = cloned_labels;

                if (fix_slice.len > 0) {
                    const cloned_fixes = try sink.arena.allocSlice(SuggestedFix, 1);
                    cloned_fixes[0] = .{
                        .message = try sink.arena.dupe(u8, fix_slice[0].message),
                        .applicability = fix_slice[0].applicability,
                        .priority = fix_slice[0].priority,
                        .edits = try sink.arena.dupe(TextEdit, fix_slice[0].edits),
                    };
                    existing_diag.suggestions = cloned_fixes;
                }
                return;
            }
        }

        const primary_labels = [_]LabeledSpan{.{
            .span = ident_span,
            .label = label_msg,
            .style = .primary,
        }};
        try sink.emit(.{
            .code = .w0201_non_canonical_identifier_case,
            .severity = .warning,
            .primary_span = ident_span,
            .message = "identifier does not follow canonical CoreX casing",
            .labels = &primary_labels,
            .suggestions = fix_slice,
        });
    }

    /// Consumes an identifier, recovering cross-namespace casing violations via `W0201`.
    fn expectIdentifierWithCasing(
        self: *Parser,
        expected_kind: TokenKind,
        expected_case: IdentifierCase,
        has_error: *bool,
        missing_msg: []const u8,
    ) !TokenIndex {
        const cur_kind = self.peekKind();
        if (cur_kind == expected_kind) {
            return self.consumeLeaf(.token_leaf, .{});
        }
        if (isIdentifierKind(cur_kind)) {
            const tok_id = try self.consumeLeaf(.token_leaf, .{});
            try self.emitOrUpdateCasingWarning(tok_id, expected_case);
            return tok_id;
        }
        has_error.* = true;
        const err_tok = self.peekTokenIndexNth(0);
        try self.emitUnexpectedToken(err_tok, missing_msg, "expected identifier here");
        return err_tok;
    }

    /// Consumes `expected_kind` if present; otherwise emits `E0201` and marks `has_error = true`.
    fn expectToken(
        self: *Parser,
        expected_kind: TokenKind,
        has_error: *bool,
        message: []const u8,
        label_text: []const u8,
    ) !TokenIndex {
        if (self.peekKind() == expected_kind) {
            return self.consumeLeaf(.token_leaf, .{});
        }
        has_error.* = true;
        const err_tok = self.peekTokenIndexNth(0);
        try self.emitUnexpectedToken(err_tok, message, label_text);
        return err_tok;
    }

    /// Consumes `close_kind` if present; otherwise emits `E0202` pointing back to `open_tok`.
    fn expectClosingDelimiter(
        self: *Parser,
        close_kind: TokenKind,
        open_tok: TokenIndex,
        has_error: *bool,
        expected_desc: []const u8,
    ) !void {
        if (self.peekKind() == close_kind) {
            const close_rec = self.peekNth(0);
            if (close_rec.flags.is_synthesized) {
                has_error.* = true;
                try self.emitUnclosedDelimiter(open_tok, expected_desc);
            }
            _ = try self.consumeLeaf(.token_leaf, .{});
            return;
        }
        has_error.* = true;
        try self.emitUnclosedDelimiter(open_tok, expected_desc);
    }

    /// Skips tokens into an `.invalid_parse_subtree` until reaching `consume_set` or `stop_set`.
    fn skipToRecoveryAnchor(
        self: *Parser,
        consume_set: TokenSet128,
        stop_set: TokenSet128,
        is_rbrace_consumable: bool,
    ) !void {
        const cur_kind = self.peekKind();
        if (cur_kind == .eof) return;
        if (consume_set.contains(cur_kind)) {
            _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            return;
        }
        if (stop_set.contains(cur_kind) and !(is_rbrace_consumable and cur_kind == .rbrace)) {
            return;
        }

        const err_cst = try self.startCstNode(.invalid_parse_subtree);
        var has_consumed_any = false;
        var nested_depth: u32 = 0;

        while (self.peekKind() != .eof) {
            const kind = self.peekKind();
            if (nested_depth == 0) {
                if (consume_set.contains(kind)) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                    break;
                }
                if (has_consumed_any and stop_set.contains(kind)) {
                    break;
                }
                if (!is_rbrace_consumable and (kind == .rbrace or kind == .rparen or kind == .rbracket)) {
                    if (!has_consumed_any and !stop_set.contains(kind)) {
                        _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                    }
                    break;
                }
            }

            if (kind == .lbrace or kind == .lparen or kind == .lbracket) {
                nested_depth += 1;
            } else if (kind == .rbrace or kind == .rparen or kind == .rbracket) {
                if (nested_depth > 0) nested_depth -= 1;
            }
            _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            has_consumed_any = true;
        }
        self.cst.finishNode(err_cst, .{ .has_error = true });
    }

    /// Parses a single `@attr(…)` annotation list into `self.cst`.
    fn parseAttributes(self: *Parser, has_error: *bool) anyerror!void {
        while (self.peekKind() == .at) {
            const attr_cst = try self.startCstNode(.attribute);
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (isIdentifierKind(self.peekKind()) or isKeywordKind(self.peekKind())) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected attribute identifier after `@`",
                    "missing attribute name",
                );
            }

            if (self.peekKind() == .lparen) {
                const open_paren = try self.consumeLeaf(.token_leaf, .{});
                while (self.peekKind() != .rparen and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    if (isIdentifierKind(self.peekKind()) and
                        (self.peekKindNth(1) == .eq or self.peekKindNth(1) == .colon))
                    {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                    _ = try self.parseExpr(true);
                    if (self.peekKind() == .comma) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else {
                        break;
                    }
                    if (self.cursor == loop_start) break;
                }
                try self.expectClosingDelimiter(
                    .rparen,
                    open_paren,
                    has_error,
                    "expected `)` to close attribute argument list",
                );
            }
            self.cst.finishNode(attr_cst, .{ .has_error = has_error.* });
        }
    }

    /// Parses a single top-level `Item` (`DR-03` Section 5.4 Part 1).
    pub fn parseItem(self: *Parser) anyerror!NodeIndex {
        const item_cst = try self.startCstNode(.placeholder);
        self.pushState(.item_dispatch, item_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(item_cst, ITEM_STOP_SET, .item_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_error = false;
        try self.parseAttributes(&has_error);

        if (self.peekKind() == .kw_pub) {
            _ = try self.consumeLeaf(.visibility_modifier, .{});
        }

        switch (self.peekKind()) {
            .kw_mod => return self.parseModItem(item_cst, &has_error),
            .kw_use => return self.parseUseItem(item_cst, &has_error),
            .kw_const => return self.parseConstItem(item_cst, &has_error),
            .kw_type => return self.parseTypeAliasItem(item_cst, &has_error),
            .kw_struct => return self.parseStructOrUnionItem(item_cst, false, &has_error),
            .kw_union => return self.parseStructOrUnionItem(item_cst, true, &has_error),
            .kw_bit_field => return self.parseBitFieldItem(item_cst, &has_error),
            .kw_enum => return self.parseEnumItem(item_cst, &has_error),
            .kw_trait => return self.parseTraitItem(item_cst, &has_error),
            .kw_impl => return self.parseImplItem(item_cst, &has_error),
            .kw_comptime => {
                if (self.peekKindNth(1) != .lbrace) {
                    return self.parseFunctionOrSubscriptItem(item_cst, &has_error);
                }
                self.cst.nodes.items(.kind)[item_cst.asInt()] = .block;
                _ = try self.consumeLeaf(.token_leaf, .{});
                const block_node = try self.parseBlock();
                self.cst.finishNode(item_cst, .{ .has_error = has_error });
                return block_node;
            },
            .kw_async, .kw_unsafe, .kw_extern, .kw_fn => {
                if (self.peekKind() == .kw_unsafe and self.peekKindNth(1) == .kw_impl) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    return self.parseImplItem(item_cst, &has_error);
                }
                if (self.peekKind() == .kw_unsafe and self.peekKindNth(1) == .kw_trait) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    return self.parseTraitItem(item_cst, &has_error);
                }
                return self.parseFunctionOrSubscriptItem(item_cst, &has_error);
            },
            .ident => {
                if (std.mem.eql(u8, self.peekLexemeNth(0), "subscript")) {
                    return self.parseFunctionOrSubscriptItem(item_cst, &has_error);
                }
            },
            else => {},
        }

        // Unexpected token at top-level item position; emit `E0201` and synchronize to next item:
        const err_tok = self.peekTokenIndexNth(0);
        try self.emitUnexpectedToken(
            err_tok,
            "unexpected token at top-level declaration",
            "expected an item declaration (`fn`, `struct`, `enum`, `type`, `const`, `use`, `mod`, `trait`, or `impl`)",
        );
        try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, ITEM_STOP_SET, true);
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .invalid_parse_subtree;
        self.cst.finishNode(item_cst, .{ .has_error = true });
        return self.ast.appendNodeWithCst(.{
            .tag = .item_hole,
            .main_token = err_tok,
        }, item_cst);
    }

    /// Parses `ModItem = "mod" IDENT ( ";" | "{" { Item } "}" ) ;`.
    fn parseModItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .mod_item;
        const mod_tok = try self.consumeLeaf(.mod_introducer, .{});
        const name_tok = try self.expectIdentifierWithCasing(
            .ident,
            .snake_case,
            has_error,
            "expected module name after `mod`",
        );

        var subitem_op: PackedOperand = .NONE;
        if (self.peekKind() == .lbrace) {
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            var inner_items: std.ArrayList(u32) = .empty;
            defer inner_items.deinit(self.ast.allocator);

            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const before_cur = self.cursor;
                try inner_items.append(self.ast.allocator, (try self.parseItem()).asInt());
                if (self.cursor == before_cur and self.peekKind() != .rbrace and self.peekKind() != .eof) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
            }
            try self.expectClosingDelimiter(
                .rbrace,
                open_brace,
                has_error,
                "expected `}` to close inline `mod` block",
            );
            if (inner_items.items.len > 0) {
                subitem_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(inner_items.items));
            }
        } else {
            _ = try self.expectToken(
                .semi,
                has_error,
                "expected `;` or `{` after module name",
                "expected `;` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .mod_decl,
            .main_token = mod_tok,
            .lhs = PackedOperand.initToken(name_tok),
            .rhs = subitem_op,
        }, item_cst);
    }

    /// Parses `UseItem = "use" UseTree ";" ;`.
    fn parseUseItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .use_item;
        const use_tok = try self.consumeLeaf(.use_introducer, .{});
        try self.parseUseTree(has_error);
        _ = try self.expectToken(
            .semi,
            has_error,
            "expected `;` after `use` declaration",
            "expected `;` here",
        );

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .use_decl,
            .main_token = use_tok,
        }, item_cst);
    }

    /// Parses `UseTree = ModuleSegment { "::" ModuleSegment } [ "::" ( "*" | "{" … "}" ) | "as" IDENT ]`.
    fn parseUseTree(self: *Parser, has_error: *bool) anyerror!void {
        const tree_cst = try self.startCstNode(.use_tree);
        self.pushState(.item_finish, tree_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                _ = try self.recoverDepthOverflow(tree_cst, ITEM_STOP_SET, .item_hole);
                has_error.* = true;
                return;
            },
            else => return err,
        };
        defer self.popStates(1);

        if (isIdentifierKind(self.peekKind()) or self.peekKind() == .kw_self_val or self.peekKind() == .kw_self_type) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected module or symbol identifier in `use` tree",
                "expected path segment here",
            );
        }

        while (self.peekKind() == .coloncolon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .star) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                break;
            }
            if (self.peekKind() == .lbrace) {
                const open_brace = try self.consumeLeaf(.token_leaf, .{});
                while (self.peekKind() != .rbrace and
                    self.peekKind() != .semi and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    try self.parseUseTree(has_error);
                    if (self.peekKind() == .comma) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else {
                        break;
                    }
                    if (self.cursor == loop_start) break;
                }
                try self.expectClosingDelimiter(
                    .rbrace,
                    open_brace,
                    has_error,
                    "expected `}` to close `use` group",
                );
                break;
            }
            if (isIdentifierKind(self.peekKind()) or self.peekKind() == .kw_self_val or self.peekKind() == .kw_self_type) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected identifier, `*`, or `{` after `::` in `use` path",
                    "incomplete `use` path",
                );
                break;
            }
        }

        if (self.peekKind() == .kw_as) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (isIdentifierKind(self.peekKind()) or self.peekKind() == .underscore) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected alias identifier after `as`",
                    "missing alias identifier",
                );
            }
        }
        self.cst.finishNode(tree_cst, .{ .has_error = has_error.* });
    }

    /// Parses `ConstItem = "const" CONST_IDENT [ ":" Type ] [ "=" Expr ] ";" ;`.
    fn parseConstItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .const_item;
        const const_tok = try self.consumeLeaf(.const_introducer, .{});
        _ = try self.expectIdentifierWithCasing(
            .const_ident,
            .screaming_snake_case,
            has_error,
            "expected constant identifier after `const`",
        );

        var type_op: PackedOperand = .NONE;
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            type_op = PackedOperand.initNode(try self.parseType());
        }

        var init_op: PackedOperand = .NONE;
        if (self.peekKind() == .eq) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            init_op = PackedOperand.initNode(try self.parseExpr(true));
        }

        if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `;` after `const` declaration",
                "expected `;` here",
            );
            try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, ITEM_STOP_SET, false);
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .const_decl,
            .main_token = const_tok,
            .lhs = type_op,
            .rhs = init_op,
        }, item_cst);
    }

    /// Parses `TypeAliasItem = "type" TYPE_IDENT [ TypeParams ] [ ":" TypeBounds ] [ "=" ( "bit_field" … | Type [ "is" Pattern ] ) ] ";" ;`.
    fn parseTypeAliasItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .type_alias_item;
        const type_tok = try self.consumeLeaf(.type_alias_introducer, .{});
        _ = try self.expectIdentifierWithCasing(
            .type_ident,
            .pascal_case,
            has_error,
            "expected `PascalCase` type identifier after `type`",
        );

        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            try self.parseTypeBounds(has_error);
        }

        var target_type_op: PackedOperand = .NONE;
        var refine_pat_op: PackedOperand = .NONE;

        if (self.peekKind() == .eq) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .kw_bit_field) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .lparen) {
                    const open_paren = try self.consumeLeaf(.token_leaf, .{});
                    target_type_op = PackedOperand.initNode(try self.parseType());
                    try self.expectClosingDelimiter(
                        .rparen,
                        open_paren,
                        has_error,
                        "expected `)` after `bit_field` backing integer type",
                    );
                } else {
                    target_type_op = PackedOperand.initNode(try self.parseType());
                }
                if (self.peekKind() == .lbrace) {
                    try self.parseBitFieldBody(has_error);
                }
                if (self.peekKind() == .semi) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
                return self.ast.appendNodeWithCst(.{
                    .tag = .type_alias_decl,
                    .main_token = type_tok,
                    .lhs = target_type_op,
                    .rhs = refine_pat_op,
                }, item_cst);
            }

            const first_target = try self.parseType();
            if (self.peekKind() == .pipe) {
                var union_members: std.ArrayList(u32) = .empty;
                defer union_members.deinit(self.ast.allocator);
                try union_members.append(self.ast.allocator, first_target.asInt());
                while (self.peekKind() == .pipe) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    try union_members.append(self.ast.allocator, (try self.parseType()).asInt());
                }
                target_type_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(union_members.items));
                refine_pat_op = .{ .tag = .extra, .payload = @intCast(union_members.items.len) };
            } else {
                target_type_op = PackedOperand.initNode(first_target);
                if (self.peekKind() == .kw_is) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    refine_pat_op = PackedOperand.initNode(try self.parsePattern(false));
                }
            }
        }

        if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `;` after `type` declaration",
                "expected `;` here",
            );
            try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, ITEM_STOP_SET, false);
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .type_alias_decl,
            .main_token = type_tok,
            .lhs = target_type_op,
            .rhs = refine_pat_op,
        }, item_cst);
    }

    /// Parses `StructItem` or `UnionItem` (`"struct" | "union" TYPE_IDENT [TypeParams] [WhereClause] "{" { StructField } "}"`).
    fn parseStructOrUnionItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        is_union: bool,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = if (is_union) .union_item else .struct_item;
        const kw_tok = try self.consumeLeaf(
            if (is_union) .union_introducer else .struct_introducer,
            .{},
        );
        _ = try self.expectIdentifierWithCasing(
            .type_ident,
            .pascal_case,
            has_error,
            if (is_union) "expected `PascalCase` union name" else "expected `PascalCase` struct name",
        );

        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }
        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }

        var field_nodes: std.ArrayList(u32) = .empty;
        defer field_nodes.deinit(self.ast.allocator);

        if (self.peekKind() == .lbrace) {
            try self.parseStructFieldsBlock(&field_nodes, has_error);
        } else if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to open field declaration block",
                "expected `{` here",
            );
            try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, ITEM_STOP_SET, false);
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        var lhs_op: PackedOperand = .NONE;
        var rhs_op: PackedOperand = .NONE;
        if (field_nodes.items.len > 0) {
            lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(field_nodes.items));
            rhs_op = .{ .tag = .extra, .payload = @intCast(field_nodes.items.len) };
        }
        return self.ast.appendNodeWithCst(.{
            .tag = if (is_union) .union_decl else .struct_decl,
            .main_token = kw_tok,
            .lhs = lhs_op,
            .rhs = rhs_op,
        }, item_cst);
    }

    /// Parses `"{ " { StructField } "}"` into `field_nodes` and `self.cst`.
    fn parseStructFieldsBlock(
        self: *Parser,
        field_nodes: *std.ArrayList(u32),
        has_error: *bool,
    ) anyerror!void {
        const open_brace = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
            const loop_start = self.cursor;
            const field_cst = try self.startCstNode(.struct_field);
            var has_field_err = false;

            try self.parseAttributes(&has_field_err);
            if (self.peekKind() == .kw_pub) {
                _ = try self.consumeLeaf(.visibility_modifier, .{});
            }

            if (isIdentifierKind(self.peekKind())) {
                _ = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_field_err,
                    "expected `snake_case` field name",
                );
                _ = try self.expectToken(
                    .colon,
                    &has_field_err,
                    "expected `:` after struct field name",
                    "expected `:` before field type",
                );
                try field_nodes.append(self.ast.allocator, (try self.parseType()).asInt());

                if (self.peekKind() == .eq) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.parseExpr(true);
                }
                if (self.peekKind() == .comma or self.peekKind() == .semi) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            } else {
                has_field_err = true;
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected field declaration inside `{ … }`",
                    "unexpected token in field list",
                );
                try self.skipToRecoveryAnchor(
                    STRUCT_FIELD_CONSUME_SET,
                    STRUCT_FIELD_STOP_SET,
                    false,
                );
            }

            if (has_field_err) has_error.* = true;
            self.cst.finishNode(field_cst, .{ .has_error = has_field_err });
            if (self.cursor == loop_start) {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }
        try self.expectClosingDelimiter(
            .rbrace,
            open_brace,
            has_error,
            "expected `}` to close struct or union body",
        );
    }

    /// Parses `BitFieldItem = "bit_field" TYPE_IDENT ":" Type "{" { BitFieldMember } "}" ;`.
    fn parseBitFieldItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .struct_item;
        const bf_tok = try self.consumeLeaf(.struct_introducer, .{});
        _ = try self.expectIdentifierWithCasing(
            .type_ident,
            .pascal_case,
            has_error,
            "expected `PascalCase` identifier after `bit_field`",
        );
        const backing_ty = if (self.peekKind() == .lparen) blk: {
            const open_paren = try self.consumeLeaf(.token_leaf, .{});
            const inner_ty = try self.parseType();
            try self.expectClosingDelimiter(
                .rparen,
                open_paren,
                has_error,
                "expected `)` after `bit_field` backing integer type",
            );
            break :blk inner_ty;
        } else blk: {
            _ = try self.expectToken(
                .colon,
                has_error,
                "expected `:` and backing integer type after `bit_field` name",
                "expected `:` here",
            );
            break :blk try self.parseType();
        };

        if (self.peekKind() == .lbrace) {
            try self.parseBitFieldBody(has_error);
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to open `bit_field` member block",
                "expected `{` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .struct_decl,
            .main_token = bf_tok,
            .lhs = PackedOperand.initNode(backing_ty),
        }, item_cst);
    }

    /// Parses `"{ " { BitFieldMember } "}"` where `BitFieldMember = { Attribute } [ "pub" ] IDENT ":" Type "|" INT_LIT [ "," | ";" ]`.
    fn parseBitFieldBody(self: *Parser, has_error: *bool) anyerror!void {
        const open_brace = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
            const loop_start = self.cursor;
            const member_cst = try self.startCstNode(.struct_field);
            var has_mem_err = false;

            try self.parseAttributes(&has_mem_err);
            if (self.peekKind() == .kw_pub) {
                _ = try self.consumeLeaf(.visibility_modifier, .{});
            }

            if (isIdentifierKind(self.peekKind())) {
                _ = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_mem_err,
                    "expected `snake_case` bit_field member name",
                );
                _ = try self.expectToken(
                    .colon,
                    &has_mem_err,
                    "expected `:` after `bit_field` member name",
                    "expected `:` here",
                );
                _ = try self.parseType();
                if (self.peekKind() == .pipe) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.expectToken(
                        .int_lit,
                        &has_mem_err,
                        "expected bit width integer literal after `|`",
                        "expected bit width here",
                    );
                }
                if (self.peekKind() == .comma or self.peekKind() == .semi) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            } else {
                has_mem_err = true;
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected `bit_field` member declaration",
                    "unexpected token in `bit_field` body",
                );
                try self.skipToRecoveryAnchor(
                    STRUCT_FIELD_CONSUME_SET,
                    STRUCT_FIELD_STOP_SET,
                    false,
                );
            }

            if (has_mem_err) has_error.* = true;
            self.cst.finishNode(member_cst, .{ .has_error = has_mem_err });
            if (self.cursor == loop_start) {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }
        try self.expectClosingDelimiter(
            .rbrace,
            open_brace,
            has_error,
            "expected `}` to close `bit_field` body",
        );
    }

    /// Parses `EnumItem = "enum" TYPE_IDENT [ TypeParams ] [ WhereClause ] "{" { EnumVariant } "}" ;`.
    fn parseEnumItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .enum_item;
        const enum_tok = try self.consumeLeaf(.enum_introducer, .{});
        _ = try self.expectIdentifierWithCasing(
            .type_ident,
            .pascal_case,
            has_error,
            "expected `PascalCase` enum name after `enum`",
        );

        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }
        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }

        if (self.peekKind() == .lbrace) {
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const loop_start = self.cursor;
                const var_cst = try self.startCstNode(.enum_variant);
                var has_var_err = false;

                try self.parseAttributes(&has_var_err);
                if (isIdentifierKind(self.peekKind())) {
                    _ = try self.expectIdentifierWithCasing(
                        .type_ident,
                        .pascal_case,
                        &has_var_err,
                        "expected `PascalCase` enum variant name",
                    );
                    if (self.peekKind() == .lparen) {
                        const open_paren = try self.consumeLeaf(.token_leaf, .{});
                        while (self.peekKind() != .rparen and
                            self.peekKind() != .rbrace and
                            self.peekKind() != .eof)
                        {
                            const inner_start = self.cursor;
                            _ = try self.parseType();
                            if (self.peekKind() == .comma) {
                                _ = try self.consumeLeaf(.token_leaf, .{});
                            } else {
                                break;
                            }
                            if (self.cursor == inner_start) break;
                        }
                        try self.expectClosingDelimiter(
                            .rparen,
                            open_paren,
                            &has_var_err,
                            "expected `)` to close tuple variant payload",
                        );
                    } else if (self.peekKind() == .lbrace) {
                        var dummy_fields: std.ArrayList(u32) = .empty;
                        defer dummy_fields.deinit(self.ast.allocator);
                        try self.parseStructFieldsBlock(&dummy_fields, &has_var_err);
                    }

                    if (self.peekKind() == .eq) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        _ = try self.parseExpr(true);
                    }
                    if (self.peekKind() == .comma or self.peekKind() == .semi) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                } else {
                    has_var_err = true;
                    has_error.* = true;
                    try self.emitUnexpectedToken(
                        self.peekTokenIndexNth(0),
                        "expected enum variant declaration",
                        "unexpected token in `enum` body",
                    );
                    try self.skipToRecoveryAnchor(
                        ENUM_VARIANT_CONSUME_SET,
                        ENUM_VARIANT_STOP_SET,
                        false,
                    );
                }

                if (has_var_err) has_error.* = true;
                self.cst.finishNode(var_cst, .{ .has_error = has_var_err });
                if (self.cursor == loop_start) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
            }
            try self.expectClosingDelimiter(
                .rbrace,
                open_brace,
                has_error,
                "expected `}` to close `enum` body",
            );
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to open `enum` variant list",
                "expected `{` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .enum_decl,
            .main_token = enum_tok,
        }, item_cst);
    }

    /// Parses `TraitItem = "trait" TYPE_IDENT [ TypeParams ] [ ":" TypeBounds ] [ WhereClause ] "{" { TraitMember } "}" ;`.
    fn parseTraitItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .trait_item;
        const trait_tok = try self.consumeLeaf(.trait_introducer, .{});
        _ = try self.expectIdentifierWithCasing(
            .type_ident,
            .pascal_case,
            has_error,
            "expected `PascalCase` trait name after `trait`",
        );

        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            try self.parseTypeBounds(has_error);
        }
        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }

        var member_indices: std.ArrayList(u32) = .empty;
        defer member_indices.deinit(self.ast.allocator);

        if (self.peekKind() == .lbrace) {
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const loop_start = self.cursor;
                const mem_cst = try self.startCstNode(.trait_member);
                var has_mem_err = false;

                try self.parseAttributes(&has_mem_err);
                if (self.peekKind() == .kw_pub) {
                    _ = try self.consumeLeaf(.visibility_modifier, .{});
                }

                const member_node = switch (self.peekKind()) {
                    .kw_type => try self.parseTypeAliasItem(mem_cst, &has_mem_err),
                    .kw_const => try self.parseConstItem(mem_cst, &has_mem_err),
                    .kw_async, .kw_unsafe, .kw_extern, .kw_comptime, .kw_fn => blk: {
                        const fn_node = try self.parseFunctionOrSubscriptItem(mem_cst, &has_mem_err);
                        self.cst.nodes.items(.kind)[mem_cst.asInt()] = .trait_member;
                        break :blk fn_node;
                    },
                    .ident => blk: {
                        if (std.mem.eql(u8, self.peekLexemeNth(0), "subscript")) {
                            const sub_node = try self.parseFunctionOrSubscriptItem(mem_cst, &has_mem_err);
                            self.cst.nodes.items(.kind)[mem_cst.asInt()] = .trait_member;
                            break :blk sub_node;
                        }
                        has_mem_err = true;
                        const err_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            err_tok,
                            "expected `fn`, `type`, `const`, or `subscript` inside `trait`",
                            "unexpected token in `trait` body",
                        );
                        try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, MEMBER_STOP_SET, false);
                        self.cst.finishNode(mem_cst, .{ .has_error = true });
                        break :blk try self.ast.appendNodeWithCst(.{
                            .tag = .item_hole,
                            .main_token = err_tok,
                        }, mem_cst);
                    },
                    else => blk: {
                        has_mem_err = true;
                        const err_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            err_tok,
                            "expected `fn`, `type`, or `const` member declaration in `trait`",
                            "unexpected token in `trait` body",
                        );
                        try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, MEMBER_STOP_SET, false);
                        self.cst.finishNode(mem_cst, .{ .has_error = true });
                        break :blk try self.ast.appendNodeWithCst(.{
                            .tag = .item_hole,
                            .main_token = err_tok,
                        }, mem_cst);
                    },
                };
                if (has_mem_err) has_error.* = true;
                try member_indices.append(self.ast.allocator, member_node.asInt());
                if (self.cursor == loop_start) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
            }
            try self.expectClosingDelimiter(
                .rbrace,
                open_brace,
                has_error,
                "expected `}` to close `trait` body",
            );
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to open `trait` body",
                "expected `{` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        var lhs_op: PackedOperand = .NONE;
        var rhs_op: PackedOperand = .NONE;
        if (member_indices.items.len > 0) {
            lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(member_indices.items));
            rhs_op = .{ .tag = .extra, .payload = @intCast(member_indices.items.len) };
        }
        return self.ast.appendNodeWithCst(.{
            .tag = .trait_decl,
            .main_token = trait_tok,
            .lhs = lhs_op,
            .rhs = rhs_op,
        }, item_cst);
    }

    /// Parses `ImplItem = "impl" [ TypeParams ] Type [ "for" Type ] [ WhereClause ] "{" { ImplMember } "}" ;`.
    fn parseImplItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .impl_item;
        const impl_tok = try self.consumeLeaf(.impl_introducer, .{});

        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }
        const first_ty = try self.parseType();
        if (self.peekKind() == .kw_for) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            _ = try self.parseType();
        }
        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }

        var member_indices: std.ArrayList(u32) = .empty;
        defer member_indices.deinit(self.ast.allocator);

        if (self.peekKind() == .lbrace) {
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const loop_start = self.cursor;
                const mem_cst = try self.startCstNode(.impl_member);
                var has_mem_err = false;

                try self.parseAttributes(&has_mem_err);
                if (self.peekKind() == .kw_pub) {
                    _ = try self.consumeLeaf(.visibility_modifier, .{});
                }

                const member_node = switch (self.peekKind()) {
                    .kw_type => try self.parseTypeAliasItem(mem_cst, &has_mem_err),
                    .kw_const => try self.parseConstItem(mem_cst, &has_mem_err),
                    .kw_async, .kw_unsafe, .kw_extern, .kw_comptime, .kw_fn => blk: {
                        const fn_node = try self.parseFunctionOrSubscriptItem(mem_cst, &has_mem_err);
                        self.cst.nodes.items(.kind)[mem_cst.asInt()] = .impl_member;
                        break :blk fn_node;
                    },
                    .ident => blk: {
                        if (std.mem.eql(u8, self.peekLexemeNth(0), "subscript")) {
                            const sub_node = try self.parseFunctionOrSubscriptItem(mem_cst, &has_mem_err);
                            self.cst.nodes.items(.kind)[mem_cst.asInt()] = .impl_member;
                            break :blk sub_node;
                        }
                        has_mem_err = true;
                        const err_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            err_tok,
                            "expected `fn`, `type`, `const`, or `subscript` inside `impl`",
                            "unexpected token in `impl` body",
                        );
                        try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, MEMBER_STOP_SET, false);
                        self.cst.finishNode(mem_cst, .{ .has_error = true });
                        break :blk try self.ast.appendNodeWithCst(.{
                            .tag = .item_hole,
                            .main_token = err_tok,
                        }, mem_cst);
                    },
                    else => blk: {
                        has_mem_err = true;
                        const err_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            err_tok,
                            "expected `fn`, `type`, or `const` member declaration in `impl`",
                            "unexpected token in `impl` body",
                        );
                        try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, MEMBER_STOP_SET, false);
                        self.cst.finishNode(mem_cst, .{ .has_error = true });
                        break :blk try self.ast.appendNodeWithCst(.{
                            .tag = .item_hole,
                            .main_token = err_tok,
                        }, mem_cst);
                    },
                };
                if (has_mem_err) has_error.* = true;
                try member_indices.append(self.ast.allocator, member_node.asInt());
                if (self.cursor == loop_start) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
            }
            try self.expectClosingDelimiter(
                .rbrace,
                open_brace,
                has_error,
                "expected `}` to close `impl` body",
            );
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to open `impl` body",
                "expected `{` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        var rhs_op: PackedOperand = .NONE;
        if (member_indices.items.len > 0) {
            rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(member_indices.items));
        }
        return self.ast.appendNodeWithCst(.{
            .tag = .impl_decl,
            .main_token = impl_tok,
            .lhs = PackedOperand.initNode(first_ty),
            .rhs = rhs_op,
        }, item_cst);
    }

    /// Parses `FunctionItem` (`[async] [unsafe] [extern] ("fn" | "subscript") FnSignature (Block | ";")`).
    fn parseFunctionOrSubscriptItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .fn_item;
        while (self.peekKind() == .kw_async or
            self.peekKind() == .kw_unsafe or
            self.peekKind() == .kw_extern or
            self.peekKind() == .kw_comptime)
        {
            const qual_kind = self.peekKind();
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (qual_kind == .kw_extern and self.peekKind() == .string_lit) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            }
        }

        const is_subscript = self.peekKind() == .ident and
            std.mem.eql(u8, self.peekLexemeNth(0), "subscript");
        const fn_tok = if (self.peekKind() == .kw_fn or is_subscript)
            try self.consumeLeaf(.fn_introducer, .{})
        else
            try self.expectToken(
                .kw_fn,
                has_error,
                "expected `fn` keyword in function declaration",
                "expected `fn` here",
            );

        const sig_cst = try self.startCstNode(.fn_sig);
        if (!is_subscript or self.peekKind() != .lparen) {
            _ = try self.expectIdentifierWithCasing(
                .ident,
                .snake_case,
                has_error,
                "expected `snake_case` function name",
            );
        }

        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }

        if (self.peekKind() == .lparen) {
            try self.parseParamList(has_error);
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `(` to start function parameter list",
                "expected `(` here",
            );
        }

        var ret_type_op: PackedOperand = .NONE;
        if (self.peekKind() == .arrow or (is_subscript and self.peekKind() == .colon)) {
            const ret_cst = try self.startCstNode(.return_type);
            _ = try self.consumeLeaf(.token_leaf, .{});
            ret_type_op = PackedOperand.initNode(try self.parseType());
            self.cst.finishNode(ret_cst, .{ .has_error = has_error.* });
        }

        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }
        self.cst.finishNode(sig_cst, .{ .has_error = has_error.* });

        var body_op: PackedOperand = .NONE;
        if (self.peekKind() == .lbrace) {
            body_op = PackedOperand.initNode(try self.parseBlock());
        } else if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` function body or `;` after function signature",
                "expected `{` or `;` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .fn_decl,
            .main_token = fn_tok,
            .lhs = ret_type_op,
            .rhs = body_op,
        }, item_cst);
    }

    /// Parses `ParamList = "(" [ (SelfParam | FnParam) { "," FnParam } [ "," ] ] ")" ;`.
    fn parseParamList(self: *Parser, has_error: *bool) anyerror!void {
        const list_cst = try self.startCstNode(.param_list);
        self.pushState(.fn_sig_after_params, list_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                _ = try self.recoverDepthOverflow(list_cst, PARAM_STOP_SET, .type_hole);
                has_error.* = true;
                return;
            },
            else => return err,
        };
        defer self.popStates(1);

        const open_paren = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rparen and
            self.peekKind() != .lbrace and
            self.peekKind() != .rbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const param_cst = try self.startCstNode(.fn_param);
            var has_param_err = false;

            try self.parseAttributes(&has_param_err);

            if (self.peekKind() == .kw_comptime) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            }

            // Check for `SelfParam` (`[ "&" ["mut"] | "mut" | "own" | "ref" ["mut"] ] "self"`):
            if (self.peekKind() == .amp) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            } else if (self.peekKind() == .kw_mut or
                self.peekKind() == .kw_own or
                self.peekKind() == .kw_ref)
            {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            }

            if (self.peekKind() == .kw_self_val) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .colon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    if (self.peekKind() == .kw_let or
                        (self.peekKind() == .ident and
                            (std.mem.eql(u8, self.peekLexemeNth(0), "inout") or
                                std.mem.eql(u8, self.peekLexemeNth(0), "sink") or
                                std.mem.eql(u8, self.peekLexemeNth(0), "set") or
                                std.mem.eql(u8, self.peekLexemeNth(0), "yielded"))))
                    {
                        if (self.peekKindNth(1) != .comma and self.peekKindNth(1) != .rparen) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        }
                    }
                    _ = try self.parseType();
                }
            } else if (isIdentifierKind(self.peekKind()) or self.peekKind() == .underscore) {
                if (self.peekKind() == .underscore) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else {
                    _ = try self.expectIdentifierWithCasing(
                        .ident,
                        .snake_case,
                        &has_param_err,
                        "expected `snake_case` parameter name",
                    );
                }
                _ = try self.expectToken(
                    .colon,
                    &has_param_err,
                    "expected `:` and parameter type after parameter name",
                    "expected `:` here",
                );
                // Support optional Hylo/DR-02 parameter convention keywords (`inout`, `sink`, `set`, `let`, `yielded`):
                if (self.peekKind() == .kw_let or
                    (self.peekKind() == .ident and
                        (std.mem.eql(u8, self.peekLexemeNth(0), "inout") or
                            std.mem.eql(u8, self.peekLexemeNth(0), "sink") or
                            std.mem.eql(u8, self.peekLexemeNth(0), "set") or
                            std.mem.eql(u8, self.peekLexemeNth(0), "yielded"))))
                {
                    if (self.peekKindNth(1) != .comma and self.peekKindNth(1) != .rparen) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                }
                _ = try self.parseType();
                if (self.peekKind() == .eq) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.parseExpr(true);
                }
            } else {
                has_param_err = true;
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected parameter declaration in parameter list",
                    "unexpected token in parameter list",
                );
                try self.skipToRecoveryAnchor(PARAM_CONSUME_SET, PARAM_STOP_SET, false);
            }

            if (has_param_err) has_error.* = true;
            self.cst.finishNode(param_cst, .{ .has_error = has_param_err });

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else if (self.peekKind() != .rparen and !has_param_err) {
                break;
            }
            if (self.cursor == loop_start) {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }
        try self.expectClosingDelimiter(
            .rparen,
            open_paren,
            has_error,
            "expected `)` to close parameter list",
        );
        self.cst.finishNode(list_cst, .{ .has_error = has_error.* });
    }

    /// Parses `TypeParams = "[" TypeParam { "," TypeParam } [ "," ] "]" ;`.
    fn parseTypeParams(self: *Parser, has_error: *bool) anyerror!void {
        const params_cst = try self.startCstNode(.type_params);
        self.pushState(.type_parse, params_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                _ = try self.recoverDepthOverflow(params_cst, TYPE_ARG_STOP_SET, .type_hole);
                has_error.* = true;
                return;
            },
            else => return err,
        };
        defer self.popStates(1);

        const open_bracket = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rbracket and
            self.peekKind() != .lbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const param_cst = try self.startCstNode(.type_param);
            var has_param_err = false;

            if (self.peekKind() == .kw_const) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .const_ident or self.peekKind() == .type_ident) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else {
                    _ = try self.expectIdentifierWithCasing(
                        .const_ident,
                        .screaming_snake_case,
                        &has_param_err,
                        "expected `SCREAMING_SNAKE_CASE` const generic identifier",
                    );
                }
                _ = try self.expectToken(
                    .colon,
                    &has_param_err,
                    "expected `:` and type after `const` generic parameter",
                    "expected `:` here",
                );
                _ = try self.parseType();
                if (self.peekKind() == .eq) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.parseExpr(false);
                }
            } else if (isIdentifierKind(self.peekKind())) {
                _ = try self.expectIdentifierWithCasing(
                    .type_ident,
                    .pascal_case,
                    &has_param_err,
                    "expected `PascalCase` type parameter name",
                );
                if (self.peekKind() == .colon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    try self.parseTypeBounds(&has_param_err);
                }
                if (self.peekKind() == .eq) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.parseType();
                }
            } else {
                has_param_err = true;
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected generic type or `const` parameter inside `[ … ]`",
                    "unexpected token in generic parameters",
                );
                try self.skipToRecoveryAnchor(PARAM_CONSUME_SET, TYPE_ARG_STOP_SET, false);
            }

            if (has_param_err) has_error.* = true;
            self.cst.finishNode(param_cst, .{ .has_error = has_param_err });

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }
        try self.expectClosingDelimiter(
            .rbracket,
            open_bracket,
            has_error,
            "expected `]` to close generic parameter list",
        );
        self.cst.finishNode(params_cst, .{ .has_error = has_error.* });
    }

    /// Parses `TypeBounds = Type { "+" Type } ;`.
    fn parseTypeBounds(self: *Parser, has_error: *bool) anyerror!void {
        _ = has_error;
        _ = try self.parseType();
        while (self.peekKind() == .plus) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            _ = try self.parseType();
        }
    }

    /// Parses `WhereClause = "where" WherePred { "," WherePred } [ "," ] ;`.
    fn parseWhereClause(self: *Parser, has_error: *bool) anyerror!void {
        const where_cst = try self.startCstNode(.where_clause);
        _ = try self.consumeLeaf(.where_clause_start, .{});

        while (self.peekKind() != .lbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const pred_cst = try self.startCstNode(.where_pred);
            _ = try self.parseType();
            _ = try self.expectToken(
                .colon,
                has_error,
                "expected `:` in `where` clause predicate",
                "expected `:` before trait bounds",
            );
            try self.parseTypeBounds(has_error);
            self.cst.finishNode(pred_cst, .{ .has_error = has_error.* });

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }
        self.cst.finishNode(where_cst, .{ .has_error = has_error.* });
    }

    /// Parses `Type = PrimaryType { "?" } ;` (`DR-03` Section 5.4 Part 5).
    pub fn parseType(self: *Parser) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const type_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const type_ast_start = self.ast.countNodes();

        self.pushState(.type_parse, type_cst_start) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                return self.recoverDepthOverflow(hole_cst, TYPE_ARG_STOP_SET, .type_hole);
            },
            else => return err,
        };
        var chain_pushes: usize = 0;
        defer self.popStates(1 + chain_pushes);

        var type_node = try self.parsePrimaryType();

        // Postfix `?` optional type sugar (`T?`, chainable and depth-bounded):
        while (!self.is_recovering_depth_overflow and self.peekKind() == .question) {
            self.pushState(.type_parse, type_cst_start) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    _ = try self.precedeNode(
                        type_cst_start,
                        type_ast_start,
                        .invalid_parse_subtree,
                        self.peekTokenIndexNth(0),
                    );
                    return self.recoverDepthOverflow(type_cst_start, TYPE_ARG_STOP_SET, .type_hole);
                },
                else => return err,
            };
            chain_pushes += 1;

            const q_tok = self.peekTokenIndexNth(0);
            _ = try self.precedeNode(type_cst_start, type_ast_start, .optional_type, q_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            self.cst.finishNode(type_cst_start, .{});
            type_node = try self.ast.appendNodeWithCst(.{
                .tag = .optional_type,
                .main_token = q_tok,
                .lhs = PackedOperand.initNode(type_node),
            }, type_cst_start);
        }
        return type_node;
    }

    /// Parses one of the 11 disjoint `PrimaryType` productions (`DR-03` Section 5.4 Part 5).
    fn parsePrimaryType(self: *Parser) anyerror!NodeIndex {
        switch (self.peekKind()) {
            .prim_type => {
                const tok = try self.consumeLeaf(.prim_type_node, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{
                    .tag = .prim_type,
                    .main_token = tok,
                }, leaf_cst);
            },
            .kw_self_type => {
                const tok = try self.consumeLeaf(.named_type, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{
                    .tag = .named_type,
                    .main_token = tok,
                }, leaf_cst);
            },
            .amp => {
                const ref_cst = try self.startCstNode(.ref_type);
                const amp_tok = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut or self.peekKind() == .kw_let or
                    (self.peekKind() == .ident and std.mem.eql(u8, self.peekLexemeNth(0), "inout")))
                {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                const inner_ty = try self.parseType();
                self.cst.finishNode(ref_cst, .{});
                return self.ast.appendNodeWithCst(.{
                    .tag = .ref_type,
                    .main_token = amp_tok,
                    .lhs = PackedOperand.initNode(inner_ty),
                }, ref_cst);
            },
            .star => {
                const ptr_cst = try self.startCstNode(.ptr_type);
                const star_tok = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                const inner_ty = try self.parseType();
                self.cst.finishNode(ptr_cst, .{});
                return self.ast.appendNodeWithCst(.{
                    .tag = .ptr_type,
                    .main_token = star_tok,
                    .lhs = PackedOperand.initNode(inner_ty),
                }, ptr_cst);
            },
            .kw_own, .kw_ref, .hash_soa, .tilde => {
                const mode_cst = try self.startCstNode(.mode_type);
                const mode_tok = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                const inner_ty = try self.parseType();
                self.cst.finishNode(mode_cst, .{});
                return self.ast.appendNodeWithCst(.{
                    .tag = .mode_type,
                    .main_token = mode_tok,
                    .lhs = PackedOperand.initNode(inner_ty),
                }, mode_cst);
            },
            .lbracket => {
                const arr_cst = try self.startCstNode(.slice_or_array_type);
                var has_err = false;
                const open_bracket = try self.consumeLeaf(.token_leaf, .{});
                const elem_ty = try self.parseType();
                var len_expr_op: PackedOperand = .NONE;
                var is_array = false;
                if (self.peekKind() == .semi) {
                    is_array = true;
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    len_expr_op = PackedOperand.initNode(try self.parseExpr(false));
                }
                try self.expectClosingDelimiter(
                    .rbracket,
                    open_bracket,
                    &has_err,
                    "expected `]` to close slice or array type",
                );
                self.cst.finishNode(arr_cst, .{ .has_error = has_err });
                return self.ast.appendNodeWithCst(.{
                    .tag = if (is_array) .array_type else .slice_type,
                    .main_token = open_bracket,
                    .lhs = PackedOperand.initNode(elem_ty),
                    .rhs = len_expr_op,
                }, arr_cst);
            },
            .lparen => {
                const tup_cst = try self.startCstNode(.tuple_type);
                var has_err = false;
                const open_paren = try self.consumeLeaf(.token_leaf, .{});
                var elem_types: std.ArrayList(u32) = .empty;
                defer elem_types.deinit(self.ast.allocator);
                var has_comma = false;

                while (self.peekKind() != .rparen and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .semi and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    try elem_types.append(self.ast.allocator, (try self.parseType()).asInt());
                    if (self.peekKind() == .comma) {
                        has_comma = true;
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else {
                        break;
                    }
                    if (self.cursor == loop_start) break;
                }
                try self.expectClosingDelimiter(
                    .rparen,
                    open_paren,
                    &has_err,
                    "expected `)` to close tuple type",
                );
                self.cst.finishNode(tup_cst, .{ .has_error = has_err });
                if (elem_types.items.len == 1 and !has_comma) {
                    return NodeIndex.fromInt(elem_types.items[0]);
                }

                var lhs_op: PackedOperand = .NONE;
                var rhs_op: PackedOperand = .NONE;
                if (elem_types.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(elem_types.items));
                    rhs_op = .{ .tag = .extra, .payload = @intCast(elem_types.items.len) };
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .tuple_type,
                    .main_token = open_paren,
                    .lhs = lhs_op,
                    .rhs = rhs_op,
                }, tup_cst);
            },
            .at, .kw_async, .kw_unsafe, .kw_fn => {
                const fn_cst = try self.startCstNode(.fn_type);
                var has_err = false;
                if (self.peekKind() == .at) {
                    try self.parseAttributes(&has_err);
                }
                while (self.peekKind() == .kw_async or self.peekKind() == .kw_unsafe) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                const fn_tok = try self.expectToken(
                    .kw_fn,
                    &has_err,
                    "expected `fn` in function type",
                    "expected `fn` here",
                );
                var param_types: std.ArrayList(u32) = .empty;
                defer param_types.deinit(self.ast.allocator);

                if (self.peekKind() == .lparen) {
                    const open_paren = try self.consumeLeaf(.token_leaf, .{});
                    while (self.peekKind() != .rparen and
                        self.peekKind() != .rbrace and
                        self.peekKind() != .semi and
                        self.peekKind() != .eof)
                    {
                        const loop_start = self.cursor;
                        if (isIdentifierKind(self.peekKind()) and self.peekKindNth(1) == .colon) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        }
                        try param_types.append(self.ast.allocator, (try self.parseType()).asInt());
                        if (self.peekKind() == .comma) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        } else {
                            break;
                        }
                        if (self.cursor == loop_start) break;
                    }
                    try self.expectClosingDelimiter(
                        .rparen,
                        open_paren,
                        &has_err,
                        "expected `)` to close function type parameters",
                    );
                }
                var ret_op: PackedOperand = .NONE;
                if (self.peekKind() == .arrow) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    ret_op = PackedOperand.initNode(try self.parseType());
                }
                self.cst.finishNode(fn_cst, .{ .has_error = has_err });
                var lhs_op: PackedOperand = .NONE;
                if (param_types.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(param_types.items));
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .fn_type,
                    .main_token = fn_tok,
                    .lhs = lhs_op,
                    .rhs = ret_op,
                }, fn_cst);
            },
            .ident, .type_ident, .const_ident => {
                // Handle `dyn Trait`, `any Group`, or `distinct BaseType` modifier prefixes:
                if (self.peekKind() == .ident and
                    (std.mem.eql(u8, self.peekLexemeNth(0), "dyn") or
                        std.mem.eql(u8, self.peekLexemeNth(0), "any") or
                        std.mem.eql(u8, self.peekLexemeNth(0), "distinct")) and
                    TYPE_STARTER_SET.contains(self.peekKindNth(1)))
                {
                    const mode_cst = try self.startCstNode(.mode_type);
                    const mode_tok = try self.consumeLeaf(.token_leaf, .{});
                    const inner_ty = try self.parseType();
                    self.cst.finishNode(mode_cst, .{});
                    return self.ast.appendNodeWithCst(.{
                        .tag = .mode_type,
                        .main_token = mode_tok,
                        .lhs = PackedOperand.initNode(inner_ty),
                    }, mode_cst);
                }

                const named_cst = try self.startCstNode(.named_type);
                var has_err = false;
                var first_tok = self.peekTokenIndexNth(0);

                // Consume optional leading `ident ::` module path segments:
                while (self.peekKind() == .ident and self.peekKindNth(1) == .coloncolon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }

                // Consume the type identifier segment (requiring `.type_ident` `PascalCase`):
                first_tok = try self.expectIdentifierWithCasing(
                    .type_ident,
                    .pascal_case,
                    &has_err,
                    "expected `PascalCase` type name",
                );
                while (self.peekKind() == .coloncolon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.expectIdentifierWithCasing(
                        .type_ident,
                        .pascal_case,
                        &has_err,
                        "expected `PascalCase` associated type name after `::`",
                    );
                }

                var arg_nodes: std.ArrayList(u32) = .empty;
                defer arg_nodes.deinit(self.ast.allocator);
                var has_generic_args = false;

                if (self.peekKind() == .lbracket) {
                    has_generic_args = true;
                    try self.parseTypeArgs(&arg_nodes, &has_err);
                }
                self.cst.finishNode(named_cst, .{ .has_error = has_err });

                if (has_generic_args) {
                    var lhs_op: PackedOperand = .NONE;
                    var rhs_op: PackedOperand = .NONE;
                    if (arg_nodes.items.len > 0) {
                        lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(arg_nodes.items));
                        rhs_op = .{ .tag = .extra, .payload = @intCast(arg_nodes.items.len) };
                    }
                    return self.ast.appendNodeWithCst(.{
                        .tag = .generic_type,
                        .main_token = first_tok,
                        .lhs = lhs_op,
                        .rhs = rhs_op,
                    }, named_cst);
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .named_type,
                    .main_token = first_tok,
                }, named_cst);
            },
            else => {
                const err_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    err_tok,
                    "expected type expression",
                    "unexpected token in type position",
                );
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                if (!TYPE_ARG_STOP_SET.contains(self.peekKind()) and !isClosingDelimiter(self.peekKind())) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
                self.cst.finishNode(hole_cst, .{ .has_error = true });
                return self.ast.appendNodeWithCst(.{
                    .tag = .type_hole,
                    .main_token = err_tok,
                }, hole_cst);
            },
        }
    }

    /// Parses `TypeArgs = "[" TypeOrConstArg { "," TypeOrConstArg } [ "," ] "]" ;`.
    fn parseTypeArgs(
        self: *Parser,
        arg_nodes: *std.ArrayList(u32),
        has_error: *bool,
    ) anyerror!void {
        const args_cst = try self.startCstNode(.type_args);
        self.pushState(.type_parse, args_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                _ = try self.recoverDepthOverflow(args_cst, TYPE_ARG_STOP_SET, .type_hole);
                has_error.* = true;
                return;
            },
            else => return err,
        };
        defer self.popStates(1);

        const open_bracket = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rbracket and
            self.peekKind() != .rbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            if (self.peekKind() == .kw_const) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                try arg_nodes.append(self.ast.allocator, (try self.parseExpr(false)).asInt());
            } else if (self.peekKind() == .int_lit or
                self.peekKind() == .const_ident or
                self.peekKind() == .kw_true or
                self.peekKind() == .kw_false)
            {
                try arg_nodes.append(
                    self.ast.allocator,
                    (try self.parsePrimaryExpr(false)).asInt(),
                );
            } else {
                try arg_nodes.append(self.ast.allocator, (try self.parseType()).asInt());
            }

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }
        try self.expectClosingDelimiter(
            .rbracket,
            open_bracket,
            has_error,
            "expected `]` to close generic type argument list",
        );
        self.cst.finishNode(args_cst, .{ .has_error = has_error.* });
    }

    /// Parses `Block = "{" { Stmt } [ TailExpr ] "}" ;` (`DR-03` Section 5.4 Part 6).
    pub fn parseBlock(self: *Parser) anyerror!NodeIndex {
        const block_cst = try self.startCstNode(.block);
        self.pushState(.block_stmt_loop, block_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(block_cst, BLOCK_STMT_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_error = false;
        const open_brace = if (self.peekKind() == .lbrace)
            try self.consumeLeaf(.token_leaf, .{})
        else
            try self.expectToken(
                .lbrace,
                &has_error,
                "expected `{` to start block",
                "expected `{` here",
            );

        var stmt_indices: std.ArrayList(u32) = .empty;
        defer stmt_indices.deinit(self.ast.allocator);
        var tail_expr_op: PackedOperand = .NONE;

        while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
            const loop_start = self.cursor;
            self.is_recovering_depth_overflow = false;
            if (self.peekKind() == .semi) {
                const empty_cst = try self.startCstNode(.empty_stmt);
                _ = try self.consumeLeaf(.token_leaf, .{});
                self.cst.finishNode(empty_cst, .{});
                continue;
            }

            var is_tail = false;
            const stmt_node = try self.parseStmt(&is_tail);
            if (is_tail) {
                tail_expr_op = PackedOperand.initNode(stmt_node);
                break;
            }
            try stmt_indices.append(self.ast.allocator, stmt_node.asInt());

            if (self.cursor == loop_start and self.peekKind() != .rbrace and self.peekKind() != .eof) {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }

        try self.expectClosingDelimiter(
            .rbrace,
            open_brace,
            &has_error,
            "expected `}` to close block",
        );
        self.cst.finishNode(block_cst, .{ .has_error = has_error });

        var lhs_op: PackedOperand = .NONE;
        if (stmt_indices.items.len > 0) {
            lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(stmt_indices.items));
        }
        self.has_last_expr_block_body = true;
        return self.ast.appendNodeWithCst(.{
            .tag = .block,
            .main_token = open_brace,
            .lhs = lhs_op,
            .rhs = tail_expr_op,
        }, block_cst);
    }

    /// Returns `true` if `@` at `peek(0)` starts an `@attribute` prefix on a local declaration/statement.
    fn isLeadingStmtAttribute(self: *const Parser) bool {
        var lookahead: usize = 0;
        var steps: usize = 0;
        while (steps < 256 and self.peekKindNth(lookahead) == .at) : (steps += 1) {
            lookahead += 1;
            const name_kind = self.peekKindNth(lookahead);
            if (!isIdentifierKind(name_kind) and !isKeywordKind(name_kind)) return false;
            lookahead += 1;
            if (self.peekKindNth(lookahead) == .lbracket) return false;
            if (self.peekKindNth(lookahead) == .lparen) {
                var paren_depth: u32 = 1;
                lookahead += 1;
                while (steps < 256 and paren_depth > 0) : (steps += 1) {
                    const inner_kind = self.peekKindNth(lookahead);
                    if (inner_kind == .eof) return false;
                    if (inner_kind == .lparen) {
                        paren_depth += 1;
                    } else if (inner_kind == .rparen) {
                        paren_depth -= 1;
                    }
                    lookahead += 1;
                }
                if (paren_depth != 0) return false;
            }
        }
        return switch (self.peekKindNth(lookahead)) {
            .kw_let,
            .kw_var,
            .kw_const,
            .kw_type,
            .kw_struct,
            .kw_enum,
            .kw_union,
            .kw_bit_field,
            .kw_fn,
            .kw_defer,
            .kw_errdefer,
            .kw_for,
            .kw_while,
            .kw_loop,
            .kw_comptime,
            => true,
            else => false,
        };
    }

    /// Returns `true` if `@` at `peek(0)` precedes a block-local `Item` declaration rather than a `Stmt`.
    fn isLeadingItemAttributeInBlock(self: *const Parser) bool {
        var lookahead: usize = 0;
        var steps: usize = 0;
        while (steps < 256 and self.peekKindNth(lookahead) == .at) : (steps += 1) {
            lookahead += 1;
            const name_kind = self.peekKindNth(lookahead);
            if (!isIdentifierKind(name_kind) and !isKeywordKind(name_kind)) return false;
            lookahead += 1;
            if (self.peekKindNth(lookahead) == .lbracket) return false;
            if (self.peekKindNth(lookahead) == .lparen) {
                var paren_depth: u32 = 1;
                lookahead += 1;
                while (steps < 256 and paren_depth > 0) : (steps += 1) {
                    const inner_kind = self.peekKindNth(lookahead);
                    if (inner_kind == .eof) return false;
                    if (inner_kind == .lparen) {
                        paren_depth += 1;
                    } else if (inner_kind == .rparen) {
                        paren_depth -= 1;
                    }
                    lookahead += 1;
                }
                if (paren_depth != 0) return false;
            }
        }
        return switch (self.peekKindNth(lookahead)) {
            .kw_const, .kw_type, .kw_struct, .kw_enum, .kw_union, .kw_bit_field, .kw_fn => true,
            .kw_comptime => self.peekKindNth(lookahead + 1) == .kw_fn,
            else => false,
        };
    }

    /// Parses a single `Stmt` or `TailExpr` inside a `Block`.
    fn parseStmt(self: *Parser, is_tail_out: *bool) anyerror!NodeIndex {
        is_tail_out.* = false;

        // Check for `@attr` annotations on a local declaration/statement (excluding `@intrinsic` calls):
        if (self.peekKind() == .at and self.isLeadingStmtAttribute()) {
            if (self.isLeadingItemAttributeInBlock()) {
                return self.parseItem();
            }
            const decl_cst = try self.startCstNode(.local_decl_stmt);
            var has_attr_err = false;
            try self.parseAttributes(&has_attr_err);
            if (self.peekKind() == .kw_let or self.peekKind() == .kw_var) {
                return self.parseLocalDeclStmtWithCst(decl_cst, has_attr_err);
            }
            const inner_stmt = try self.parseStmt(is_tail_out);
            self.cst.finishNode(decl_cst, .{ .has_error = has_attr_err });
            if (!inner_stmt.isNone() and inner_stmt.asInt() < self.ast.ast_to_cst.items.len) {
                self.ast.ast_to_cst.items[inner_stmt.asInt()] = decl_cst;
            }
            return inner_stmt;
        }

        switch (self.peekKind()) {
            .kw_let, .kw_var => {
                const decl_cst = try self.startCstNode(.local_decl_stmt);
                return self.parseLocalDeclStmtWithCst(decl_cst, false);
            },
            .kw_defer, .kw_errdefer => return self.parseDeferStmt(),
            .kw_return => return self.parseReturnStmt(),
            .kw_break => return self.parseBreakStmt(),
            .kw_continue => return self.parseContinueStmt(),
            .kw_for => return self.parseForStmt(),
            .kw_comptime => {
                if (self.peekKindNth(1) == .kw_for) {
                    return self.parseForStmt();
                }
                if (self.peekKindNth(1) == .kw_fn) {
                    return self.parseItem();
                }
            },
            .kw_while => return self.parseWhileStmt(),
            .kw_const, .kw_type, .kw_struct, .kw_enum, .kw_union, .kw_bit_field, .kw_fn => {
                return self.parseItem();
            },
            else => {},
        }

        // Expression, Assignment (`Expr AssignOp Expr ";"`), or `TailExpr`:
        try self.flushCarrierTokens();
        const stmt_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const stmt_ast_start = self.ast.countNodes();

        self.has_last_expr_block_body = false;
        const saved_stmt_lhs = self.is_in_stmt_lhs;
        self.is_in_stmt_lhs = true;
        const expr_node = blk_stmt_expr: {
            defer self.is_in_stmt_lhs = saved_stmt_lhs;
            break :blk_stmt_expr try self.parseExpr(true);
        };
        const expr_tag = self.ast.getNode(expr_node).tag;
        const is_block_bodied = self.has_last_expr_block_body or isBlockBodiedAstTag(expr_tag);

        if (isAssignOp(self.peekKind())) {
            const op_tok = self.peekTokenIndexNth(0);
            _ = try self.precedeNode(stmt_cst_start, stmt_ast_start, .assign_stmt, op_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const rhs_expr = try self.parseExpr(true);
            var has_assign_err = false;
            if (self.peekKind() == .semi) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                has_assign_err = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected `;` after assignment statement",
                    "expected `;` here",
                );
            }
            self.cst.finishNode(stmt_cst_start, .{ .has_error = has_assign_err });
            return self.ast.appendNodeWithCst(.{
                .tag = .assign_stmt,
                .main_token = op_tok,
                .lhs = PackedOperand.initNode(expr_node),
                .rhs = PackedOperand.initNode(rhs_expr),
            }, stmt_cst_start);
        }

        if (self.peekKind() == .semi) {
            const main_tok = self.ast.getNode(expr_node).main_token;
            _ = try self.precedeNode(stmt_cst_start, stmt_ast_start, .expr_stmt, main_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            self.cst.finishNode(stmt_cst_start, .{});
            return expr_node;
        }

        if (self.peekKind() == .rbrace or self.peekKind() == .eof) {
            is_tail_out.* = true;
            return expr_node;
        }

        if (is_block_bodied or expr_tag == .expr_hole or
            expr_tag == .incomplete_member_access or expr_tag == .incomplete_call)
        {
            return expr_node;
        }

        // Missing `;` after non-block expression statement:
        try self.emitUnexpectedToken(
            self.peekTokenIndexNth(0),
            "expected `;` after expression statement",
            "expected `;` here",
        );
        const main_tok = self.ast.getNode(expr_node).main_token;
        _ = try self.precedeNode(stmt_cst_start, stmt_ast_start, .expr_stmt, main_tok);
        try self.skipToRecoveryAnchor(BLOCK_STMT_CONSUME_SET, BLOCK_STMT_STOP_SET, false);
        self.cst.finishNode(stmt_cst_start, .{ .has_error = true });
        return expr_node;
    }

    /// Parses `LocalDeclStmt = ("let" | "var") ["mut"] Pattern [":" Type] ["=" Expr ["else" Block]] ";" ;`.
    fn parseLocalDeclStmtWithCst(
        self: *Parser,
        decl_cst: CstNodeIndex,
        has_initial_err: bool,
    ) anyerror!NodeIndex {
        self.pushState(.local_decl_init, decl_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(decl_cst, BLOCK_STMT_STOP_SET, .stmt_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_error = has_initial_err;
        const kw_tok = try self.consumeLeaf(.local_decl_introducer, .{});
        if (self.peekKind() == .kw_mut) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        }

        const pat_node = try self.parsePattern(true);

        var rhs_op: PackedOperand = .NONE;
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            rhs_op = PackedOperand.initNode(try self.parseType());
        }

        if (self.peekKind() == .eq) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            rhs_op = PackedOperand.initNode(try self.parseExpr(true));

            if (self.peekKind() == .kw_else) {
                const else_cst = try self.startCstNode(.let_else_branch);
                _ = try self.consumeLeaf(.token_leaf, .{});
                _ = try self.parseBlock();
                self.cst.finishNode(else_cst, .{});
            }
        }

        if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `;` after local variable declaration",
                "expected `;` here",
            );
            try self.skipToRecoveryAnchor(BLOCK_STMT_CONSUME_SET, LOCAL_INIT_STOP_SET, false);
        }

        self.cst.finishNode(decl_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .local_var_decl,
            .main_token = kw_tok,
            .lhs = PackedOperand.initNode(pat_node),
            .rhs = rhs_op,
        }, decl_cst);
    }

    /// Parses `DeferStmt = "defer" (Block | Expr ";") | "errdefer" ["|" IDENT "|"] (Block | Expr ";") ;`.
    fn parseDeferStmt(self: *Parser) anyerror!NodeIndex {
        const defer_cst = try self.startCstNode(.defer_stmt);
        var has_error = false;
        const is_errdefer = self.peekKind() == .kw_errdefer;
        const kw_tok = try self.consumeLeaf(.defer_introducer, .{});

        var capture_op: PackedOperand = .NONE;
        if (is_errdefer and self.peekKind() == .pipe) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            const cap_tok = try self.expectIdentifierWithCasing(
                .ident,
                .snake_case,
                &has_error,
                "expected `snake_case` error capture identifier inside `|…|`",
            );
            capture_op = PackedOperand.initToken(cap_tok);
            _ = try self.expectToken(
                .pipe,
                &has_error,
                "expected closing `|` after `errdefer` capture identifier",
                "expected `|` here",
            );
        }

        var body_node: NodeIndex = .none;
        if (self.peekKind() == .lbrace) {
            body_node = try self.parseBlock();
            if (self.peekKind() == .semi) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            }
        } else {
            body_node = try self.parseExpr(true);
            _ = try self.expectToken(
                .semi,
                &has_error,
                "expected `;` after `defer` expression",
                "expected `;` here",
            );
        }

        self.cst.finishNode(defer_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .defer_stmt,
            .main_token = kw_tok,
            .lhs = capture_op,
            .rhs = PackedOperand.initNode(body_node),
        }, defer_cst);
    }

    /// Parses `ReturnStmt = "return" [ Expr ] ";" ;`.
    fn parseReturnStmt(self: *Parser) anyerror!NodeIndex {
        const ret_cst = try self.startCstNode(.return_stmt);
        var has_error = false;
        const ret_tok = try self.consumeLeaf(.return_introducer, .{});

        var val_op: PackedOperand = .NONE;
        if (self.peekKind() != .semi and self.peekKind() != .rbrace and self.peekKind() != .eof) {
            val_op = PackedOperand.initNode(try self.parseExpr(true));
        }
        _ = try self.expectToken(
            .semi,
            &has_error,
            "expected `;` after `return` statement",
            "expected `;` here",
        );

        self.cst.finishNode(ret_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .return_stmt,
            .main_token = ret_tok,
            .lhs = val_op,
        }, ret_cst);
    }

    /// Parses `BreakStmt = "break" [ Expr ] ";" ;`.
    fn parseBreakStmt(self: *Parser) anyerror!NodeIndex {
        const brk_cst = try self.startCstNode(.break_stmt);
        var has_error = false;
        const brk_tok = try self.consumeLeaf(.break_introducer, .{});

        var val_op: PackedOperand = .NONE;
        if (self.peekKind() != .semi and self.peekKind() != .rbrace and self.peekKind() != .eof) {
            val_op = PackedOperand.initNode(try self.parseExpr(true));
        }
        _ = try self.expectToken(
            .semi,
            &has_error,
            "expected `;` after `break` statement",
            "expected `;` here",
        );

        self.cst.finishNode(brk_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .break_stmt,
            .main_token = brk_tok,
            .lhs = val_op,
        }, brk_cst);
    }

    /// Parses `ContinueStmt = "continue" ";" ;`.
    fn parseContinueStmt(self: *Parser) anyerror!NodeIndex {
        const cont_cst = try self.startCstNode(.continue_stmt);
        var has_error = false;
        const cont_tok = try self.consumeLeaf(.token_leaf, .{});
        _ = try self.expectToken(
            .semi,
            &has_error,
            "expected `;` after `continue` statement",
            "expected `;` here",
        );
        self.cst.finishNode(cont_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .continue_stmt,
            .main_token = cont_tok,
        }, cont_cst);
    }

    /// Parses `ForStmt = ["comptime"] "for" Pattern "in" ExprNoStruct Block ;`.
    fn parseForStmt(self: *Parser) anyerror!NodeIndex {
        const for_cst = try self.startCstNode(.for_stmt);
        var has_error = false;
        var comptime_tok: TokenIndex = .none;
        if (self.peekKind() == .kw_comptime) {
            comptime_tok = try self.consumeLeaf(.token_leaf, .{});
        }
        const for_tok = try self.consumeLeaf(.for_introducer, .{});

        const header_cst = try self.startCstNode(.for_header);
        const pat_node = try self.parsePattern(true);
        _ = try self.expectToken(
            .kw_in,
            &has_error,
            "expected `in` after `for` loop pattern",
            "expected `in` here",
        );
        const iter_expr = try self.parseExpr(false);
        self.cst.finishNode(header_cst, .{ .has_error = has_error });

        const body_block = try self.parseBlock();
        self.cst.finishNode(for_cst, .{ .has_error = has_error });

        const extra_pair = [_]u32{ pat_node.asInt(), iter_expr.asInt() };
        const extra_idx = try self.ast.appendExtraSlice(&extra_pair);
        return self.ast.appendNodeWithCst(.{
            .tag = .for_stmt,
            .main_token = if (!comptime_tok.isNone()) comptime_tok else for_tok,
            .lhs = PackedOperand.initExtra(extra_idx),
            .rhs = PackedOperand.initNode(body_block),
        }, for_cst);
    }

    /// Parses `WhileStmt = "while" ( "let" Pattern "=" ExprNoStruct | ExprNoStruct ) Block ;`.
    fn parseWhileStmt(self: *Parser) anyerror!NodeIndex {
        const while_cst = try self.startCstNode(.while_stmt);
        var has_error = false;
        const while_tok = try self.consumeLeaf(.while_introducer, .{});

        const header_cst = try self.startCstNode(.while_header);
        var cond_node: NodeIndex = .none;
        if (self.peekKind() == .kw_let) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            const pat_node = try self.parsePattern(false);
            _ = try self.expectToken(
                .eq,
                &has_error,
                "expected `=` after `while let` pattern",
                "expected `=` here",
            );
            const rhs_expr = try self.parseExpr(false);
            const extra_pair = [_]u32{ pat_node.asInt(), rhs_expr.asInt() };
            const extra_idx = try self.ast.appendExtraSlice(&extra_pair);
            cond_node = try self.ast.appendNodeWithCst(.{
                .tag = .binary_expr,
                .main_token = while_tok,
                .lhs = PackedOperand.initExtra(extra_idx),
                .rhs = PackedOperand.initNode(rhs_expr),
            }, header_cst);
        } else {
            cond_node = try self.parseExpr(false);
            // Support optional `|capture|` payload before `{` (`DR-02` Section 3.1):
            if (self.isPayloadCaptureBar()) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .amp) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                _ = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_error,
                    "expected `snake_case` payload capture identifier",
                );
                _ = try self.expectToken(
                    .pipe,
                    &has_error,
                    "expected closing `|` after payload capture",
                    "expected `|` here",
                );
            }
        }
        self.cst.finishNode(header_cst, .{ .has_error = has_error });

        const body_block = try self.parseBlock();
        self.cst.finishNode(while_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .while_stmt,
            .main_token = while_tok,
            .lhs = PackedOperand.initNode(cond_node),
            .rhs = PackedOperand.initNode(body_block),
        }, while_cst);
    }

    /// Parses `Pattern = SinglePattern { "|" SinglePattern } ;` (`DR-03` Section 5.4 Part 7).
    pub fn parsePattern(self: *Parser, is_binding_slot: bool) anyerror!NodeIndex {
        return self.parsePatternWithOptions(is_binding_slot, true);
    }

    /// Parses `Pattern` while optionally forbidding outer `{ … }` struct destructuring in `ExprNoStruct` headers.
    pub fn parsePatternWithOptions(
        self: *Parser,
        is_binding_slot: bool,
        is_struct_pat_allowed: bool,
    ) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const pat_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const pat_ast_start = self.ast.countNodes();

        self.pushState(.pattern_parse, pat_cst_start) catch |parse_err| switch (parse_err) {
            error.ParseDepthExceeded => {
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                return self.recoverDepthOverflow(hole_cst, MATCH_ARM_STOP_SET, .pattern_hole);
            },
            else => return parse_err,
        };
        var chain_pushes: usize = 0;
        defer self.popStates(1 + chain_pushes);

        var lhs_pat = try self.parseSinglePattern(is_binding_slot, is_struct_pat_allowed);

        while (!self.is_recovering_depth_overflow and
            self.peekKind() == .pipe and
            !(!is_struct_pat_allowed and self.isPayloadCaptureBar()))
        {
            self.pushState(.pattern_parse, pat_cst_start) catch |parse_err| switch (parse_err) {
                error.ParseDepthExceeded => {
                    _ = try self.precedeNode(
                        pat_cst_start,
                        pat_ast_start,
                        .invalid_parse_subtree,
                        self.peekTokenIndexNth(0),
                    );
                    return self.recoverDepthOverflow(pat_cst_start, MATCH_ARM_STOP_SET, .pattern_hole);
                },
                else => return parse_err,
            };
            chain_pushes += 1;

            const pipe_tok = self.peekTokenIndexNth(0);
            _ = try self.precedeNode(pat_cst_start, pat_ast_start, .or_pat, pipe_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const rhs_pat = try self.parseSinglePattern(is_binding_slot, is_struct_pat_allowed);
            self.cst.finishNode(pat_cst_start, .{});
            lhs_pat = try self.ast.appendNodeWithCst(.{
                .tag = .or_pat,
                .main_token = pipe_tok,
                .lhs = PackedOperand.initNode(lhs_pat),
                .rhs = PackedOperand.initNode(rhs_pat),
            }, pat_cst_start);
        }
        return lhs_pat;
    }

    /// Parses a single pattern (`_`, literal/range, tuple, binding, `.Variant`, or `PathPattern`).
    fn parseSinglePattern(
        self: *Parser,
        is_binding_slot: bool,
        is_struct_pat_allowed: bool,
    ) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const pat_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const pat_ast_start = self.ast.countNodes();

        switch (self.peekKind()) {
            .underscore => {
                const tok = try self.consumeLeaf(.wildcard_pat, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{
                    .tag = .wildcard_pat,
                    .main_token = tok,
                }, leaf_cst);
            },
            .minus, .int_lit, .float_lit, .string_lit, .char_lit, .kw_true, .kw_false => {
                var lit_tok = self.peekTokenIndexNth(0);
                if (self.peekKind() == .minus) {
                    const neg_cst = try self.startCstNode(.literal_pat);
                    var has_neg_err = false;
                    lit_tok = try self.consumeLeaf(.token_leaf, .{});
                    if (self.peekKind() == .int_lit or self.peekKind() == .float_lit) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else {
                        has_neg_err = true;
                        try self.emitUnexpectedToken(
                            self.peekTokenIndexNth(0),
                            "expected numeric literal after `-` in pattern",
                            "expected numeric literal here",
                        );
                    }
                    self.cst.finishNode(neg_cst, .{ .has_error = has_neg_err });
                } else {
                    lit_tok = try self.consumeLeaf(.literal_pat, .{});
                }
                var lit_node = try self.ast.appendNodeWithCst(.{
                    .tag = .lit_pat,
                    .main_token = lit_tok,
                }, pat_cst_start);

                if (self.peekKind() == .dotdoteq or self.peekKind() == .dotdot) {
                    const range_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(pat_cst_start, pat_ast_start, .range_pat, range_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    if (self.peekKind() == .minus) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                    if (isLiteralToken(self.peekKind()) or isIdentifierKind(self.peekKind())) {
                        const end_tok = try self.consumeLeaf(.literal_pat, .{});
                        self.cst.finishNode(pat_cst_start, .{});
                        lit_node = try self.ast.appendNodeWithCst(.{
                            .tag = .lit_pat,
                            .main_token = range_tok,
                            .lhs = PackedOperand.initNode(lit_node),
                            .rhs = PackedOperand.initToken(end_tok),
                        }, pat_cst_start);
                    } else {
                        try self.emitUnexpectedToken(
                            self.peekTokenIndexNth(0),
                            "expected upper-bound pattern after range operator",
                            "expected upper-bound literal or constant here",
                        );
                        self.cst.finishNode(pat_cst_start, .{ .has_error = true });
                    }
                }
                return lit_node;
            },
            .lparen => {
                const tup_cst = try self.startCstNode(.tuple_pat);
                var has_err = false;
                const open_paren = try self.consumeLeaf(.token_leaf, .{});
                var sub_pats: std.ArrayList(u32) = .empty;
                defer sub_pats.deinit(self.ast.allocator);

                while (self.peekKind() != .rparen and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .semi and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    try sub_pats.append(
                        self.ast.allocator,
                        (try self.parsePattern(is_binding_slot)).asInt(),
                    );
                    if (self.peekKind() == .comma) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else {
                        break;
                    }
                    if (self.cursor == loop_start) break;
                }
                try self.expectClosingDelimiter(
                    .rparen,
                    open_paren,
                    &has_err,
                    "expected `)` to close tuple pattern",
                );
                self.cst.finishNode(tup_cst, .{ .has_error = has_err });

                var lhs_op: PackedOperand = .NONE;
                var rhs_op: PackedOperand = .NONE;
                if (sub_pats.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(sub_pats.items));
                    rhs_op = .{ .tag = .extra, .payload = @intCast(sub_pats.items.len) };
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .tuple_pat,
                    .main_token = open_paren,
                    .lhs = lhs_op,
                    .rhs = rhs_op,
                }, tup_cst);
            },
            .dot => {
                const var_cst = try self.startCstNode(.variant_pat);
                var has_err = false;
                const dot_tok = try self.consumeLeaf(.token_leaf, .{});
                _ = try self.expectIdentifierWithCasing(
                    .type_ident,
                    .pascal_case,
                    &has_err,
                    "expected `PascalCase` variant identifier after `.`",
                );

                var payload_pats: std.ArrayList(u32) = .empty;
                defer payload_pats.deinit(self.ast.allocator);

                if (self.peekKind() == .lparen) {
                    try self.parseTuplePatPayload(&payload_pats, is_binding_slot, &has_err);
                } else if (is_struct_pat_allowed and self.peekKind() == .lbrace) {
                    try self.parseStructPatPayload(&payload_pats, is_binding_slot, &has_err);
                }
                self.cst.finishNode(var_cst, .{ .has_error = has_err });

                var lhs_op: PackedOperand = .NONE;
                var rhs_op: PackedOperand = .NONE;
                if (payload_pats.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(payload_pats.items));
                    rhs_op = .{ .tag = .extra, .payload = @intCast(payload_pats.items.len) };
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .variant_pat,
                    .main_token = dot_tok,
                    .lhs = lhs_op,
                    .rhs = rhs_op,
                }, var_cst);
            },
            .kw_mut, .kw_ref, .kw_own, .amp => {
                const bind_cst = try self.startCstNode(.ident_pat);
                var has_err = false;
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                const ident_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_err,
                    "expected `snake_case` binding identifier",
                );
                self.cst.finishNode(bind_cst, .{ .has_error = has_err });
                return self.ast.appendNodeWithCst(.{
                    .tag = .bind_pat,
                    .main_token = ident_tok,
                }, bind_cst);
            },
            .ident, .type_ident, .const_ident, .kw_self_type => {
                // Path, variant, or struct destructuring pattern (`Option::Some(x)`, `Ready`, or `Point { x, y }`):
                if (self.peekKindNth(1) == .coloncolon or
                    self.peekKindNth(1) == .lparen or
                    (is_struct_pat_allowed and self.peekKindNth(1) == .lbrace) or
                    (!is_binding_slot and self.peekKind() == .type_ident))
                {
                    const path_cst = try self.startCstNode(.path_pat);
                    var has_err = false;
                    const first_tok = try self.consumeLeaf(.token_leaf, .{});
                    while (self.peekKind() == .coloncolon) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        if (isIdentifierKind(self.peekKind())) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        } else {
                            has_err = true;
                            try self.emitUnexpectedToken(
                                self.peekTokenIndexNth(0),
                                "expected identifier after `::` in pattern",
                                "missing pattern path segment",
                            );
                            break;
                        }
                    }

                    var payload_pats: std.ArrayList(u32) = .empty;
                    defer payload_pats.deinit(self.ast.allocator);
                    var res_tag: AstTag = .variant_pat;

                    if (self.peekKind() == .lparen) {
                        self.cst.nodes.items(.kind)[path_cst.asInt()] = .variant_pat;
                        try self.parseTuplePatPayload(&payload_pats, is_binding_slot, &has_err);
                    } else if (is_struct_pat_allowed and self.peekKind() == .lbrace) {
                        self.cst.nodes.items(.kind)[path_cst.asInt()] = .struct_pat;
                        res_tag = .struct_pat;
                        try self.parseStructPatPayload(&payload_pats, is_binding_slot, &has_err);
                    }
                    self.cst.finishNode(path_cst, .{ .has_error = has_err });

                    var lhs_op: PackedOperand = .NONE;
                    var rhs_op: PackedOperand = .NONE;
                    if (payload_pats.items.len > 0) {
                        lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(payload_pats.items));
                        rhs_op = .{ .tag = .extra, .payload = @intCast(payload_pats.items.len) };
                    }
                    return self.ast.appendNodeWithCst(.{
                        .tag = res_tag,
                        .main_token = first_tok,
                        .lhs = lhs_op,
                        .rhs = rhs_op,
                    }, path_cst);
                }

                // Single identifier pattern (`x` binding or `CONST_IDENT` in match arm):
                if (!is_binding_slot and self.peekKind() == .const_ident) {
                    const tok = try self.consumeLeaf(.literal_pat, .{});
                    const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                    return self.ast.appendNodeWithCst(.{
                        .tag = .lit_pat,
                        .main_token = tok,
                    }, leaf_cst);
                }

                var has_err = false;
                const bind_cst = try self.startCstNode(.ident_pat);
                const ident_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_err,
                    "expected `snake_case` pattern binding identifier",
                );
                self.cst.finishNode(bind_cst, .{ .has_error = has_err });
                return self.ast.appendNodeWithCst(.{
                    .tag = .bind_pat,
                    .main_token = ident_tok,
                }, bind_cst);
            },
            else => {
                const err_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    err_tok,
                    "expected pattern",
                    "unexpected token in pattern position",
                );
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                if (!MATCH_ARM_STOP_SET.contains(self.peekKind()) and !isClosingDelimiter(self.peekKind())) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
                self.cst.finishNode(hole_cst, .{ .has_error = true });
                return self.ast.appendNodeWithCst(.{
                    .tag = .pattern_hole,
                    .main_token = err_tok,
                }, hole_cst);
            },
        }
    }

    /// Parses `TuplePatPayload = "(" [ Pattern { "," Pattern } [ "," ] ] ")" ;`.
    fn parseTuplePatPayload(
        self: *Parser,
        payload_pats: *std.ArrayList(u32),
        is_binding_slot: bool,
        has_error: *bool,
    ) anyerror!void {
        const open_paren = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rparen and
            self.peekKind() != .rbrace and
            self.peekKind() != .fat_arrow and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            try payload_pats.append(self.ast.allocator, (try self.parsePattern(is_binding_slot)).asInt());
            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }
        try self.expectClosingDelimiter(
            .rparen,
            open_paren,
            has_error,
            "expected `)` to close variant pattern payload",
        );
    }

    /// Parses `StructPatPayload = "{" [ FieldPat { "," FieldPat } [ "," ] ] "}" ;`.
    fn parseStructPatPayload(
        self: *Parser,
        payload_pats: *std.ArrayList(u32),
        is_binding_slot: bool,
        has_error: *bool,
    ) anyerror!void {
        const open_brace = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rbrace and
            self.peekKind() != .fat_arrow and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const field_cst = try self.startCstNode(.field_pat);
            var has_field_err = false;

            if (self.peekKind() == .dotdot) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                if (self.peekKind() == .kw_mut or
                    self.peekKind() == .kw_ref or
                    self.peekKind() == .kw_own)
                {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                const field_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_field_err,
                    "expected `snake_case` field name in struct pattern",
                );
                if (self.peekKind() == .colon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    try payload_pats.append(
                        self.ast.allocator,
                        (try self.parsePattern(is_binding_slot)).asInt(),
                    );
                } else {
                    const bind_node = try self.ast.appendNodeWithCst(.{
                        .tag = .bind_pat,
                        .main_token = field_tok,
                    }, field_cst);
                    try payload_pats.append(self.ast.allocator, bind_node.asInt());
                }
            }
            if (has_field_err) has_error.* = true;
            self.cst.finishNode(field_cst, .{ .has_error = has_field_err });

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }
        try self.expectClosingDelimiter(
            .rbrace,
            open_brace,
            has_error,
            "expected `}` to close struct pattern",
        );
    }

    /// Returns `true` if `[` at `peek(0)` starts generic `TypeArgs` (`[T]`, `[(u64, i64)]`, `[std::io::File]`).
    fn isTypeArgsAfterLBracket(self: *const Parser) bool {
        if (self.peekKind() != .lbracket) return false;
        return self.isTypeStarterAtLookahead(1);
    }

    /// Returns `true` if the token at `start_lookahead` begins a `TypeOrConstArg` inside `[…]`.
    fn isTypeStarterAtLookahead(self: *const Parser, start_lookahead: usize) bool {
        var lookahead: usize = start_lookahead;
        var steps: usize = 0;
        while (steps < 64 and lookahead < 64) : (steps += 1) {
            switch (self.peekKindNth(lookahead)) {
                .prim_type,
                .kw_self_type,
                .kw_const,
                .kw_own,
                .kw_ref,
                .hash_soa,
                .kw_fn,
                .star,
                => return true,
                .type_ident => {
                    // `TypeIdent` is a type argument unless it is `Enum::Variant` in an index without `(` after `]`:
                    if (self.peekKindNth(lookahead + 1) != .coloncolon) return true;
                    var scan_off: usize = lookahead;
                    var seg_steps: usize = 0;
                    while (seg_steps < 64 and
                        isIdentifierKind(self.peekKindNth(scan_off)) and
                        self.peekKindNth(scan_off + 1) == .coloncolon) : (seg_steps += 1)
                    {
                        scan_off += 2;
                    }
                    if (self.peekKindNth(scan_off) == .type_ident and
                        self.peekKindNth(scan_off + 1) == .rbracket and
                        self.peekKindNth(scan_off + 2) != .lparen)
                    {
                        return false;
                    }
                    return true;
                },
                .amp => {
                    lookahead = if (self.peekKindNth(lookahead + 1) == .kw_mut)
                        lookahead + 2
                    else
                        lookahead + 1;
                },
                .lparen => {
                    // Tuple type arg `[(u64, i64)]` or `[()]`:
                    if (self.peekKindNth(lookahead + 1) == .rparen) return true;
                    lookahead += 1;
                },
                .lbracket => {
                    // Nested slice or array type arg `[[u8]]` or `[[u8; 4]]`:
                    lookahead += 1;
                },
                .ident => {
                    // Module-qualified type path `[std::io::File]` or `[dyn Trait]`:
                    if (std.mem.eql(u8, self.peekLexemeNth(lookahead), "dyn")) {
                        lookahead += 1;
                        continue;
                    }
                    var scan_off: usize = lookahead;
                    var seg_steps: usize = 0;
                    while (seg_steps < 64 and
                        self.peekKindNth(scan_off) == .ident and
                        self.peekKindNth(scan_off + 1) == .coloncolon) : (seg_steps += 1)
                    {
                        scan_off += 2;
                    }
                    return scan_off > lookahead and self.peekKindNth(scan_off) == .type_ident;
                },
                else => return false,
            }
        }
        return false;
    }

    /// Returns `true` if `{` at `peek(0)` starts a `StructLiteral` (`{}`, `{ ..x }`, `{ a: 1 }`, `{ a, }`).
    fn isStructLiteralBrace(self: *const Parser) bool {
        if (self.peekKind() != .lbrace) return false;
        const first_inside = self.peekKindNth(1);
        if (first_inside == .rbrace or first_inside == .dotdot) return true;
        if (isIdentifierKind(first_inside)) {
            const second_inside = self.peekKindNth(2);
            return second_inside == .colon or second_inside == .comma or second_inside == .rbrace;
        }
        return false;
    }

    /// Returns `true` if `|` at `peek(0)` starts a Zig-style `|ident| {` payload capture before a block.
    fn isPayloadCaptureBar(self: *const Parser) bool {
        if (self.peekKind() != .pipe) return false;
        var scan_off: usize = 1;
        if (self.peekKindNth(scan_off) == .amp) {
            scan_off += 1;
        }
        if (!isIdentifierKind(self.peekKindNth(scan_off))) return false;
        return self.peekKindNth(scan_off + 1) == .pipe and self.peekKindNth(scan_off + 2) == .lbrace;
    }

    /// Parses an expression at minimum binding power `0` (`is_struct_lit_allowed = true` for `Expr`, `false` for `ExprNoStruct`).
    pub fn parseExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        return self.parseExprBp(0, is_struct_lit_allowed);
    }

    /// Parses a Pratt precedence-climbing expression with `min_bp` (`DR-03` Section 5.3).
    pub fn parseExprBp(self: *Parser, min_bp: u8, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const lhs_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const lhs_ast_start = self.ast.countNodes();

        self.pushState(.expr_pratt_loop, lhs_cst_start) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                return self.recoverDepthOverflow(hole_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        var chain_pushes: usize = 0;
        defer self.popStates(1 + chain_pushes);

        var lhs_node = try self.parsePrefixExpr(is_struct_lit_allowed);

        while (!self.is_recovering_depth_overflow) {
            const cur_kind = self.peekKind();

            // [1] Tier 14 Postfix Operators (`l_bp = 30`):
            if (30 >= min_bp) {
                if (cur_kind == .question) {
                    self.pushState(.expr_pratt_loop, lhs_cst_start) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            _ = try self.precedeNode(
                                lhs_cst_start,
                                lhs_ast_start,
                                .invalid_parse_subtree,
                                self.peekTokenIndexNth(0),
                            );
                            return self.recoverDepthOverflow(
                                lhs_cst_start,
                                EXPR_SYNC_STOP_SET,
                                .expr_hole,
                            );
                        },
                        else => return err,
                    };
                    chain_pushes += 1;

                    const q_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .postfix_try_expr, q_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    self.cst.finishNode(lhs_cst_start, .{});
                    self.has_last_expr_block_body = false;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .try_expr,
                        .main_token = q_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                    }, lhs_cst_start);
                    continue;
                }

                if (cur_kind == .dot) {
                    self.pushState(.expr_pratt_loop, lhs_cst_start) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            _ = try self.precedeNode(
                                lhs_cst_start,
                                lhs_ast_start,
                                .invalid_parse_subtree,
                                self.peekTokenIndexNth(0),
                            );
                            return self.recoverDepthOverflow(
                                lhs_cst_start,
                                EXPR_SYNC_STOP_SET,
                                .expr_hole,
                            );
                        },
                        else => return err,
                    };
                    chain_pushes += 1;

                    lhs_node = try self.parseDotPostfix(
                        lhs_node,
                        lhs_cst_start,
                        lhs_ast_start,
                        is_struct_lit_allowed,
                    );
                    continue;
                }

                if (cur_kind == .lbracket) {
                    self.pushState(.expr_pratt_loop, lhs_cst_start) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            _ = try self.precedeNode(
                                lhs_cst_start,
                                lhs_ast_start,
                                .invalid_parse_subtree,
                                self.peekTokenIndexNth(0),
                            );
                            return self.recoverDepthOverflow(
                                lhs_cst_start,
                                EXPR_SYNC_STOP_SET,
                                .expr_hole,
                            );
                        },
                        else => return err,
                    };
                    chain_pushes += 1;

                    lhs_node = try self.parseBracketPostfix(
                        lhs_node,
                        lhs_cst_start,
                        lhs_ast_start,
                        is_struct_lit_allowed,
                    );
                    continue;
                }

                if (cur_kind == .lparen) {
                    self.pushState(.expr_pratt_loop, lhs_cst_start) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            _ = try self.precedeNode(
                                lhs_cst_start,
                                lhs_ast_start,
                                .invalid_parse_subtree,
                                self.peekTokenIndexNth(0),
                            );
                            return self.recoverDepthOverflow(
                                lhs_cst_start,
                                EXPR_SYNC_STOP_SET,
                                .expr_hole,
                            );
                        },
                        else => return err,
                    };
                    chain_pushes += 1;

                    lhs_node = try self.parseCallPostfix(
                        lhs_node,
                        lhs_cst_start,
                        lhs_ast_start,
                        is_struct_lit_allowed,
                    );
                    continue;
                }
            }

            // [2] Stop before `|capture| {` payload bar inside `if` / `while` headers:
            if (!is_struct_lit_allowed and cur_kind == .pipe and self.isPayloadCaptureBar()) {
                break;
            }

            // [3] Break on outer statement-level assignment, or reject nested assignment inside expressions:
            if (isAssignOp(cur_kind)) {
                if (self.is_in_stmt_lhs) break;
                const assign_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    assign_tok,
                    "assignment is a statement in CoreX and cannot be nested inside an expression",
                    "unexpected assignment operator in expression",
                );
                _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, assign_tok);
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                const rhs_node = try self.parseExprBp(1, is_struct_lit_allowed);
                self.cst.finishNode(lhs_cst_start, .{ .has_error = true });
                lhs_node = try self.ast.appendNodeWithCst(.{
                    .tag = .expr_hole,
                    .main_token = assign_tok,
                    .lhs = PackedOperand.initNode(lhs_node),
                    .rhs = PackedOperand.initNode(rhs_node),
                }, lhs_cst_start);
                continue;
            }

            // [4] Infix Operators (Tiers 12 down to 1):
            if (getInfixBindingPower(cur_kind)) |bp_info| {
                if (bp_info.left_bp < min_bp) break;
                self.is_in_stmt_lhs = false;

                self.pushState(.expr_pratt_loop, lhs_cst_start) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        _ = try self.precedeNode(
                            lhs_cst_start,
                            lhs_ast_start,
                            .invalid_parse_subtree,
                            self.peekTokenIndexNth(0),
                        );
                        return self.recoverDepthOverflow(
                            lhs_cst_start,
                            EXPR_SYNC_STOP_SET,
                            .expr_hole,
                        );
                    },
                    else => return err,
                };
                chain_pushes += 1;

                if (cur_kind == .kw_as) {
                    const as_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .cast_expr, as_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    const target_ty = try self.parseType();
                    self.cst.finishNode(lhs_cst_start, .{});
                    self.has_last_expr_block_body = false;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .cast_expr,
                        .main_token = as_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = PackedOperand.initNode(target_ty),
                    }, lhs_cst_start);
                    continue;
                }

                if (cur_kind == .kw_catch) {
                    const catch_tok = self.peekTokenIndexNth(0);
                    var has_catch_err = false;
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, catch_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});

                    if (self.peekKind() == .pipe) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        _ = try self.expectIdentifierWithCasing(
                            .ident,
                            .snake_case,
                            &has_catch_err,
                            "expected `snake_case` error capture identifier after `catch |`",
                        );
                        _ = try self.expectToken(
                            .pipe,
                            &has_catch_err,
                            "expected closing `|` after `catch` identifier",
                            "expected `|` here",
                        );
                    }

                    const fallback_node = if (self.peekKind() == .lbrace)
                        try self.parseBlock()
                    else
                        try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);

                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_catch_err });
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .binary_expr,
                        .main_token = catch_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = PackedOperand.initNode(fallback_node),
                    }, lhs_cst_start);
                    continue;
                }

                if (cur_kind == .kw_is) {
                    const is_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, is_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    const rhs_pat = try self.parsePatternWithOptions(false, is_struct_lit_allowed);

                    var has_is_chain_err = false;
                    if (self.peekKind() == .kw_is) {
                        has_is_chain_err = true;
                        const chain_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            chain_tok,
                            "chained `is` pattern test operators are non-associative in CoreX",
                            "combine pattern tests with `and` or add explicit parentheses",
                        );
                        _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                        _ = try self.parsePatternWithOptions(false, is_struct_lit_allowed);
                    }

                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_is_chain_err });
                    self.has_last_expr_block_body = false;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .binary_expr,
                        .main_token = is_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = PackedOperand.initNode(rhs_pat),
                    }, lhs_cst_start);
                    continue;
                }

                const op_tok = self.peekTokenIndexNth(0);
                _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, op_tok);
                _ = try self.consumeLeaf(.token_leaf, .{});
                const rhs_node = try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);

                // Enforce non-associativity on relational (`<`, `==`, etc.) and range (`..`, `..=`) tiers:
                var has_non_assoc_err = false;
                if (bp_info.is_non_associative) {
                    const next_kind = self.peekKind();
                    if ((isRelationalOp(cur_kind) and isRelationalOp(next_kind)) or
                        (isRangeOp(cur_kind) and isRangeOp(next_kind)))
                    {
                        has_non_assoc_err = true;
                        const chain_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            chain_tok,
                            "chained relational or range operators are non-associative in CoreX",
                            "chain comparisons with `and` or add explicit parentheses",
                        );
                        _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                        _ = try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);
                    }
                }

                self.cst.finishNode(lhs_cst_start, .{ .has_error = has_non_assoc_err });
                self.has_last_expr_block_body = false;
                lhs_node = try self.ast.appendNodeWithCst(.{
                    .tag = if (cur_kind == .pipe_gt) .pipe_expr else .binary_expr,
                    .main_token = op_tok,
                    .lhs = PackedOperand.initNode(lhs_node),
                    .rhs = PackedOperand.initNode(rhs_node),
                }, lhs_cst_start);
                continue;
            }

            break;
        }
        return lhs_node;
    }

    /// Parses postfix `.await`, `.field`, `.0`, `.method[T](args)`, or mid-keystroke `expr.` (`incomplete_member_access`).
    fn parseDotPostfix(
        self: *Parser,
        lhs_node: NodeIndex,
        lhs_cst_start: CstNodeIndex,
        lhs_ast_start: usize,
        is_struct_lit_allowed: bool,
    ) anyerror!NodeIndex {
        const dot_tok = self.peekTokenIndexNth(0);
        if (self.peekKindNth(1) == .kw_await) {
            _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .postfix_await_expr, dot_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            _ = try self.consumeLeaf(.token_leaf, .{});
            self.cst.finishNode(lhs_cst_start, .{});
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .await_expr,
                .main_token = dot_tok,
                .lhs = PackedOperand.initNode(lhs_node),
            }, lhs_cst_start);
        }

        _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .field_or_method_expr, dot_tok);
        _ = try self.consumeLeaf(.token_leaf, .{});

        if (isIdentifierKind(self.peekKind()) or self.peekKind() == .int_lit) {
            var has_err = false;
            const member_tok = if (self.peekKind() == .int_lit)
                try self.consumeLeaf(.token_leaf, .{})
            else
                try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_err,
                    "expected `snake_case` field or method name after `.`",
                );

            var call_items: std.ArrayList(u32) = .empty;
            defer call_items.deinit(self.ast.allocator);
            try call_items.append(self.ast.allocator, member_tok.asInt());

            var has_type_args = false;
            if (self.isTypeArgsAfterLBracket()) {
                has_type_args = true;
                try self.parseTypeArgs(&call_items, &has_err);
            }

            if (self.peekKind() == .lparen or has_type_args) {
                var is_incomplete = false;
                if (self.peekKind() == .lparen) {
                    try self.parseCallArgs(&call_items, &has_err, &is_incomplete);
                }
                self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err or is_incomplete });
                self.has_last_expr_block_body = false;

                if (is_struct_lit_allowed and self.peekKind() == .lbrace) {
                    const vb_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .view_block_expr, vb_tok);
                    try call_items.append(self.ast.allocator, (try self.parseBlock()).asInt());
                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err or is_incomplete });
                    self.has_last_expr_block_body = true;
                }

                const extra_idx = try self.ast.appendExtraSlice(call_items.items);
                return self.ast.appendNodeWithCst(.{
                    .tag = if (is_incomplete) .incomplete_call else .method_call,
                    .main_token = dot_tok,
                    .lhs = PackedOperand.initNode(lhs_node),
                    .rhs = PackedOperand.initExtra(extra_idx),
                }, lhs_cst_start);
            }

            self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err });
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .field_access,
                .main_token = dot_tok,
                .lhs = PackedOperand.initNode(lhs_node),
                .rhs = PackedOperand.initToken(member_tok),
            }, lhs_cst_start);
        }

        // Mid-keystroke trailing `.`; synthesize missing leaf and lower to `.incomplete_member_access`:
        try self.emitUnexpectedToken(
            dot_tok,
            "expected field, method, or `await` after `.`",
            "incomplete member access after `.`",
        );
        _ = try self.cst.appendLeafNode(.invalid_parse_leaf, dot_tok, .{
            .has_error = true,
            .is_missing_or_injected = true,
        });
        self.cst.finishNode(lhs_cst_start, .{ .has_error = true });
        self.has_last_expr_block_body = false;
        return self.ast.appendNodeWithCst(.{
            .tag = .incomplete_member_access,
            .main_token = dot_tok,
            .lhs = PackedOperand.initNode(lhs_node),
            .rhs = PackedOperand.initToken(dot_tok),
        }, lhs_cst_start);
    }

    /// Parses postfix generic call `callee[T](args)` or index expression `base[index]`.
    fn parseBracketPostfix(
        self: *Parser,
        lhs_node: NodeIndex,
        lhs_cst_start: CstNodeIndex,
        lhs_ast_start: usize,
        is_struct_lit_allowed: bool,
    ) anyerror!NodeIndex {
        const saved_stmt_lhs = self.is_in_stmt_lhs;
        self.is_in_stmt_lhs = false;
        defer self.is_in_stmt_lhs = saved_stmt_lhs;
        const bracket_tok = self.peekTokenIndexNth(0);
        const lhs_ast = self.ast.getNode(lhs_node);
        const is_intrinsic_callee = lhs_ast.tag == .ident_expr and
            !lhs_ast.main_token.isNone() and
            self.token_buffer.getToken(lhs_ast.main_token).kind == .at;
        if (is_intrinsic_callee or self.isTypeArgsAfterLBracket()) {
            _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .call_expr, bracket_tok);
            var has_err = false;
            var call_items: std.ArrayList(u32) = .empty;
            defer call_items.deinit(self.ast.allocator);

            try self.parseTypeArgs(&call_items, &has_err);
            var has_call_parens = false;
            var is_incomplete = false;
            if (self.peekKind() == .lparen) {
                has_call_parens = true;
                try self.parseCallArgs(&call_items, &has_err, &is_incomplete);
            }
            self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err or is_incomplete });
            self.has_last_expr_block_body = false;

            if (is_struct_lit_allowed and self.peekKind() == .lbrace and
                (has_call_parens or !self.isStructLiteralBrace()))
            {
                const vb_tok = self.peekTokenIndexNth(0);
                _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .view_block_expr, vb_tok);
                try call_items.append(self.ast.allocator, (try self.parseBlock()).asInt());
                self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err or is_incomplete });
                self.has_last_expr_block_body = true;
            }

            var rhs_op: PackedOperand = .NONE;
            if (call_items.items.len > 0) {
                rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(call_items.items));
            }
            return self.ast.appendNodeWithCst(.{
                .tag = if (is_incomplete) .incomplete_call else .generic_call,
                .main_token = bracket_tok,
                .lhs = PackedOperand.initNode(lhs_node),
                .rhs = rhs_op,
            }, lhs_cst_start);
        }

        // Array, slice, or multi-index subscript expression (`base[index]`):
        _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .index_expr, bracket_tok);
        var has_err = false;
        const open_bracket = try self.consumeLeaf(.token_leaf, .{});
        const first_idx = try self.parseExpr(true);
        while (self.peekKind() == .comma) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .rbracket) break;
            _ = try self.parseExpr(true);
        }
        try self.expectClosingDelimiter(
            .rbracket,
            open_bracket,
            &has_err,
            "expected `]` to close index expression",
        );
        self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err });
        self.has_last_expr_block_body = false;
        return self.ast.appendNodeWithCst(.{
            .tag = .index_expr,
            .main_token = open_bracket,
            .lhs = PackedOperand.initNode(lhs_node),
            .rhs = PackedOperand.initNode(first_idx),
        }, lhs_cst_start);
    }

    /// Parses postfix function call `callee(args)` and optional trailing declarative view block `{ … }`.
    fn parseCallPostfix(
        self: *Parser,
        lhs_node: NodeIndex,
        lhs_cst_start: CstNodeIndex,
        lhs_ast_start: usize,
        is_struct_lit_allowed: bool,
    ) anyerror!NodeIndex {
        const lparen_tok = self.peekTokenIndexNth(0);
        _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .call_expr, lparen_tok);
        var has_err = false;
        var is_incomplete = false;
        var arg_nodes: std.ArrayList(u32) = .empty;
        defer arg_nodes.deinit(self.ast.allocator);

        try self.parseCallArgs(&arg_nodes, &has_err, &is_incomplete);
        self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err or is_incomplete });
        self.has_last_expr_block_body = false;

        if (is_struct_lit_allowed and self.peekKind() == .lbrace) {
            const vb_tok = self.peekTokenIndexNth(0);
            _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .view_block_expr, vb_tok);
            try arg_nodes.append(self.ast.allocator, (try self.parseBlock()).asInt());
            self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err or is_incomplete });
            self.has_last_expr_block_body = true;
        }

        var rhs_op: PackedOperand = .NONE;
        if (arg_nodes.items.len > 0) {
            rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(arg_nodes.items));
        }
        return self.ast.appendNodeWithCst(.{
            .tag = if (is_incomplete) .incomplete_call else .call_expr,
            .main_token = lparen_tok,
            .lhs = PackedOperand.initNode(lhs_node),
            .rhs = rhs_op,
        }, lhs_cst_start);
    }

    /// Parses `CallArgs = "(" [ CallArg { "," CallArg } [ "," ] ] ")"`, detecting `incomplete_call`.
    fn parseCallArgs(
        self: *Parser,
        arg_nodes: *std.ArrayList(u32),
        has_error: *bool,
        is_incomplete_out: *bool,
    ) anyerror!void {
        const saved_stmt_lhs = self.is_in_stmt_lhs;
        self.is_in_stmt_lhs = false;
        defer self.is_in_stmt_lhs = saved_stmt_lhs;
        const open_paren = try self.consumeLeaf(.token_leaf, .{});
        self.pushState(.call_args_loop, CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1))) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                const hole_node = try self.recoverDepthOverflow(
                    hole_cst,
                    EXPR_SYNC_STOP_SET,
                    .expr_hole,
                );
                try arg_nodes.append(self.ast.allocator, hole_node.asInt());
                has_error.* = true;
                is_incomplete_out.* = true;
                return;
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_trailing_comma = false;
        var trailing_comma_tok = open_paren;

        while (self.peekKind() != .rparen and
            self.peekKind() != .rbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const arg_cst = try self.startCstNode(.call_arg);
            var has_arg_err = false;
            has_trailing_comma = false;

            if (isIdentifierKind(self.peekKind()) and self.peekKindNth(1) == .colon) {
                _ = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_arg_err,
                    "expected `snake_case` named argument label",
                );
                _ = try self.consumeLeaf(.token_leaf, .{});
            }

            const arg_expr = try self.parseExpr(true);
            if (self.ast.getNode(arg_expr).tag == .expr_hole) {
                has_arg_err = true;
                is_incomplete_out.* = true;
            }
            try arg_nodes.append(self.ast.allocator, arg_expr.asInt());
            if (has_arg_err) has_error.* = true;
            self.cst.finishNode(arg_cst, .{ .has_error = has_arg_err });

            if (self.peekKind() == .comma) {
                trailing_comma_tok = try self.consumeLeaf(.token_leaf, .{});
                has_trailing_comma = true;
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }

        if (self.peekKind() == .rparen) {
            const rparen_rec = self.peekNth(0);
            if (has_trailing_comma and
                (rparen_rec.flags.is_synthesized or !rparen_rec.flags.has_leading_newline))
            {
                is_incomplete_out.* = true;
                const hole_cst = try self.cst.appendLeafNode(
                    .invalid_parse_leaf,
                    trailing_comma_tok,
                    .{ .has_error = true, .is_missing_or_injected = true },
                );
                const hole_node = try self.ast.appendNodeWithCst(.{
                    .tag = .expr_hole,
                    .main_token = trailing_comma_tok,
                }, hole_cst);
                try arg_nodes.append(self.ast.allocator, hole_node.asInt());
            }
            if (rparen_rec.flags.is_synthesized) {
                has_error.* = true;
                is_incomplete_out.* = true;
                try self.emitUnclosedDelimiter(
                    open_paren,
                    "expected `)` to close argument list",
                );
            }
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            is_incomplete_out.* = true;
            if (has_trailing_comma) {
                const hole_cst = try self.cst.appendLeafNode(
                    .invalid_parse_leaf,
                    trailing_comma_tok,
                    .{ .has_error = true, .is_missing_or_injected = true },
                );
                const hole_node = try self.ast.appendNodeWithCst(.{
                    .tag = .expr_hole,
                    .main_token = trailing_comma_tok,
                }, hole_cst);
                try arg_nodes.append(self.ast.allocator, hole_node.asInt());
            }
            try self.emitUnclosedDelimiter(
                open_paren,
                "expected `)` to close argument list",
            );
        }
    }

    /// Parses `PrefixExpr = [ UnaryOp ] PrimaryExpr` (`DR-03` Section 5.3 Tier 13, `r_bp = 26`).
    fn parsePrefixExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        if (getPrefixRightBindingPower(self.peekKind())) |right_bp| {
            const pref_cst = try self.startCstNode(.prefix_expr);
            self.pushState(.expr_prefix_finish, pref_cst) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    return self.recoverDepthOverflow(pref_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                },
                else => return err,
            };
            defer self.popStates(1);

            const op_kind = self.peekKind();
            const op_tok = try self.consumeLeaf(.token_leaf, .{});
            if ((op_kind == .amp or op_kind == .kw_own or op_kind == .kw_ref) and
                (self.peekKind() == .kw_mut or self.peekKind() == .kw_let or
                    (self.peekKind() == .ident and
                        (std.mem.eql(u8, self.peekLexemeNth(0), "inout") or
                            std.mem.eql(u8, self.peekLexemeNth(0), "sink") or
                            std.mem.eql(u8, self.peekLexemeNth(0), "set")))))
            {
                if (self.peekKind() == .kw_mut or self.peekKind() == .kw_let or
                    !EXPR_SYNC_STOP_SET.contains(self.peekKindNth(1)))
                {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            }

            const saved_stmt_lhs = self.is_in_stmt_lhs;
            self.is_in_stmt_lhs = saved_stmt_lhs and (op_kind == .star);
            const operand = blk_pref: {
                defer self.is_in_stmt_lhs = saved_stmt_lhs;
                break :blk_pref try self.parseExprBp(right_bp, is_struct_lit_allowed);
            };
            self.cst.finishNode(pref_cst, .{});
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .unary_expr,
                .main_token = op_tok,
                .lhs = PackedOperand.initNode(operand),
            }, pref_cst);
        }
        return self.parsePrimaryExpr(is_struct_lit_allowed);
    }

    /// Parses a `PrimaryExpr` (`DR-03` Section 5.4 Part 8).
    fn parsePrimaryExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        const saved_stmt_lhs = self.is_in_stmt_lhs;
        self.is_in_stmt_lhs = false;
        defer self.is_in_stmt_lhs = saved_stmt_lhs;
        self.has_last_expr_block_body = false;
        switch (self.peekKind()) {
            .int_lit => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .int_lit, .main_token = tok }, leaf_cst);
            },
            .float_lit => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .float_lit, .main_token = tok }, leaf_cst);
            },
            .string_lit => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .string_lit, .main_token = tok }, leaf_cst);
            },
            .char_lit => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .char_lit, .main_token = tok }, leaf_cst);
            },
            .kw_true, .kw_false => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .bool_lit, .main_token = tok }, leaf_cst);
            },
            .kw_self_val => {
                const tok = try self.consumeLeaf(.self_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .self_val, .main_token = tok }, leaf_cst);
            },
            .dot => {
                const var_cst = try self.startCstNode(.contextual_variant_expr);
                var has_err = false;
                const dot_tok = try self.consumeLeaf(.token_leaf, .{});
                const var_tok = try self.expectIdentifierWithCasing(
                    .type_ident,
                    .pascal_case,
                    &has_err,
                    "expected `PascalCase` variant identifier after `.`",
                );

                var arg_nodes: std.ArrayList(u32) = .empty;
                defer arg_nodes.deinit(self.ast.allocator);
                var is_incomplete = false;

                if (self.peekKind() == .lparen) {
                    try self.parseCallArgs(&arg_nodes, &has_err, &is_incomplete);
                } else if (is_struct_lit_allowed and self.isStructLiteralBrace()) {
                    try self.parseStructLiteralBody(&arg_nodes, &has_err);
                }
                self.cst.finishNode(var_cst, .{ .has_error = has_err or is_incomplete });

                var rhs_op: PackedOperand = .NONE;
                if (arg_nodes.items.len > 0) {
                    rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(arg_nodes.items));
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = if (is_incomplete) .incomplete_call else .contextual_variant,
                    .main_token = dot_tok,
                    .lhs = PackedOperand.initToken(var_tok),
                    .rhs = rhs_op,
                }, var_cst);
            },
            .lparen => {
                const grp_cst = try self.startCstNode(.tuple_or_paren_expr);
                self.pushState(.delimited_paren, grp_cst) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(grp_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                    },
                    else => return err,
                };
                defer self.popStates(1);

                var has_err = false;
                const open_paren = try self.consumeLeaf(.token_leaf, .{});
                var elem_nodes: std.ArrayList(u32) = .empty;
                defer elem_nodes.deinit(self.ast.allocator);
                var has_comma = false;

                while (self.peekKind() != .rparen and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .semi and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    try elem_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());
                    if (self.peekKind() == .comma) {
                        has_comma = true;
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else {
                        break;
                    }
                    if (self.cursor == loop_start) break;
                }
                try self.expectClosingDelimiter(
                    .rparen,
                    open_paren,
                    &has_err,
                    "expected `)` to close parenthesized or tuple expression",
                );
                self.cst.finishNode(grp_cst, .{ .has_error = has_err });
                self.has_last_expr_block_body = false;

                if (elem_nodes.items.len == 1 and !has_comma) {
                    return NodeIndex.fromInt(elem_nodes.items[0]);
                }
                var lhs_op: PackedOperand = .NONE;
                var rhs_op: PackedOperand = .NONE;
                if (elem_nodes.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(elem_nodes.items));
                    rhs_op = .{ .tag = .extra, .payload = @intCast(elem_nodes.items.len) };
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .tuple_lit,
                    .main_token = open_paren,
                    .lhs = lhs_op,
                    .rhs = rhs_op,
                }, grp_cst);
            },
            .lbracket => {
                const arr_cst = try self.startCstNode(.array_expr);
                self.pushState(.delimited_bracket, arr_cst) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(arr_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                    },
                    else => return err,
                };
                defer self.popStates(1);

                var has_err = false;
                const open_bracket = try self.consumeLeaf(.token_leaf, .{});
                var elem_nodes: std.ArrayList(u32) = .empty;
                defer elem_nodes.deinit(self.ast.allocator);

                if (self.peekKind() != .rbracket and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .eof)
                {
                    try elem_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());

                    if (self.peekKind() == .semi) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        try elem_nodes.append(
                            self.ast.allocator,
                            (try self.parseExpr(true)).asInt(),
                        );
                    } else {
                        while (self.peekKind() == .comma) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                            if (self.peekKind() == .rbracket or
                                self.peekKind() == .rbrace or
                                self.peekKind() == .eof)
                            {
                                break;
                            }
                            try elem_nodes.append(
                                self.ast.allocator,
                                (try self.parseExpr(true)).asInt(),
                            );
                        }
                    }
                }
                try self.expectClosingDelimiter(
                    .rbracket,
                    open_bracket,
                    &has_err,
                    "expected `]` to close array literal",
                );
                self.cst.finishNode(arr_cst, .{ .has_error = has_err });
                self.has_last_expr_block_body = false;

                var lhs_op: PackedOperand = .NONE;
                var rhs_op: PackedOperand = .NONE;
                if (elem_nodes.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(elem_nodes.items));
                    rhs_op = .{ .tag = .extra, .payload = @intCast(elem_nodes.items.len) };
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .array_lit,
                    .main_token = open_bracket,
                    .lhs = lhs_op,
                    .rhs = rhs_op,
                }, arr_cst);
            },
            .pipe, .pipepipe => return self.parseClosureExpr(is_struct_lit_allowed),
            .kw_if => return self.parseIfExpr(),
            .kw_match => return self.parseMatchExpr(),
            .kw_loop => {
                const loop_cst = try self.startCstNode(.loop_expr);
                const loop_tok = try self.consumeLeaf(.loop_introducer, .{});
                const body_node = try self.parseBlock();
                self.cst.finishNode(loop_cst, .{});
                self.has_last_expr_block_body = true;
                return self.ast.appendNodeWithCst(.{
                    .tag = .loop_expr,
                    .main_token = loop_tok,
                    .lhs = PackedOperand.initNode(body_node),
                }, loop_cst);
            },
            .at => {
                if ((isIdentifierKind(self.peekKindNth(1)) or isKeywordKind(self.peekKindNth(1))) and
                    (self.peekKindNth(2) == .pipe or self.peekKindNth(2) == .pipepipe))
                {
                    return self.parseClosureExpr(is_struct_lit_allowed);
                }
                const intr_cst = try self.startCstNode(.path_pat);
                var has_intr_err = false;
                const at_tok = try self.consumeLeaf(.token_leaf, .{});
                const ident_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_intr_err,
                    "expected `snake_case` intrinsic identifier after `@`",
                );
                self.cst.finishNode(intr_cst, .{ .has_error = has_intr_err });
                self.has_last_expr_block_body = false;
                return self.ast.appendNodeWithCst(.{
                    .tag = .ident_expr,
                    .main_token = at_tok,
                    .lhs = PackedOperand.initToken(ident_tok),
                }, intr_cst);
            },
            .kw_comptime => {
                const comp_cst = try self.startCstNode(.prefix_expr);
                self.pushState(.expr_prefix_finish, comp_cst) catch |parse_err| switch (parse_err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(comp_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                    },
                    else => return parse_err,
                };
                defer self.popStates(1);

                const comp_tok = try self.consumeLeaf(.token_leaf, .{});
                var has_inner_block = false;
                const inner_node = switch (self.peekKind()) {
                    .lbrace => blk: {
                        const parsed_blk = try self.parseBlock();
                        has_inner_block = true;
                        break :blk parsed_blk;
                    },
                    .kw_if => blk: {
                        const parsed_if = try self.parseIfExpr();
                        has_inner_block = true;
                        break :blk parsed_if;
                    },
                    .kw_match => blk: {
                        const parsed_match = try self.parseMatchExpr();
                        has_inner_block = true;
                        break :blk parsed_match;
                    },
                    else => blk: {
                        const parsed_expr = try self.parseExprBp(26, is_struct_lit_allowed);
                        has_inner_block = self.has_last_expr_block_body or
                            isBlockBodiedAstTag(self.ast.getNode(parsed_expr).tag);
                        break :blk parsed_expr;
                    },
                };
                self.cst.finishNode(comp_cst, .{});
                self.has_last_expr_block_body = has_inner_block;
                return self.ast.appendNodeWithCst(.{
                    .tag = .unary_expr,
                    .main_token = comp_tok,
                    .lhs = PackedOperand.initNode(inner_node),
                }, comp_cst);
            },
            .kw_unsafe, .kw_async => {
                const blk_cst = try self.startCstNode(.block);
                _ = try self.consumeLeaf(.token_leaf, .{});
                const inner_blk = try self.parseBlock();
                self.cst.finishNode(blk_cst, .{});
                self.has_last_expr_block_body = true;
                return inner_blk;
            },
            .lbrace => return self.parseBlock(),
            .ident, .type_ident, .const_ident, .kw_self_type, .prim_type => {
                return self.parsePathOrConstructExpr(is_struct_lit_allowed);
            },
            else => {
                const err_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    err_tok,
                    "expected expression",
                    "unexpected token in expression",
                );
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                if (!EXPR_SYNC_STOP_SET.contains(self.peekKind()) and !isClosingDelimiter(self.peekKind())) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
                self.cst.finishNode(hole_cst, .{ .has_error = true });
                return self.ast.appendNodeWithCst(.{
                    .tag = .expr_hole,
                    .main_token = err_tok,
                }, hole_cst);
            },
        }
    }

    /// Parses `PathOrConstructExpr = PathExpr [TypeArgs] [StructLiteral | CallArgs [Block] | Block]`.
    fn parsePathOrConstructExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const path_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const path_ast_start = self.ast.countNodes();

        // Support `yield expr` inside `subscript` blocks (`DR-02` Section 2.2):
        if (self.peekKind() == .ident and
            std.mem.eql(u8, self.peekLexemeNth(0), "yield") and
            !EXPR_SYNC_STOP_SET.contains(self.peekKindNth(1)) and
            self.peekKindNth(1) != .lparen and
            self.peekKindNth(1) != .coloncolon)
        {
            const yield_cst = try self.startCstNode(.return_stmt);
            const yield_tok = try self.consumeLeaf(.token_leaf, .{});
            const yielded_expr = try self.parseExpr(is_struct_lit_allowed);
            self.cst.finishNode(yield_cst, .{});
            return self.ast.appendNodeWithCst(.{
                .tag = .unary_expr,
                .main_token = yield_tok,
                .lhs = PackedOperand.initNode(yielded_expr),
            }, yield_cst);
        }

        var last_seg_kind = self.peekKind();
        const first_tok = try self.consumeLeaf(.ident_pat, .{});
        const first_leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));

        var seg_tokens: std.ArrayList(u32) = .empty;
        defer seg_tokens.deinit(self.ast.allocator);
        try seg_tokens.append(self.ast.allocator, first_tok.asInt());

        var has_err = false;
        var has_opened_path_cst = false;
        while (self.peekKind() == .coloncolon) {
            if (!has_opened_path_cst) {
                _ = try self.precedeNode(path_cst_start, path_ast_start, .path_pat, first_tok);
                has_opened_path_cst = true;
            }
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (isIdentifierKind(self.peekKind()) or self.peekKind() == .kw_self_type) {
                last_seg_kind = self.peekKind();
                try seg_tokens.append(
                    self.ast.allocator,
                    (try self.consumeLeaf(.token_leaf, .{})).asInt(),
                );
            } else {
                has_err = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected path segment identifier after `::`",
                    "missing path segment",
                );
                break;
            }
        }

        if (has_opened_path_cst) {
            self.cst.finishNode(path_cst_start, .{ .has_error = has_err });
        }

        var base_node: NodeIndex = if (!has_opened_path_cst)
            try self.ast.appendNodeWithCst(.{
                .tag = .ident_expr,
                .main_token = first_tok,
            }, first_leaf_cst)
        else blk: {
            const extra_idx = try self.ast.appendExtraSlice(seg_tokens.items);
            break :blk try self.ast.appendNodeWithCst(.{
                .tag = .path_expr,
                .main_token = first_tok,
                .lhs = PackedOperand.initExtra(extra_idx),
                .rhs = .{ .tag = .extra, .payload = @intCast(seg_tokens.items.len) },
            }, path_cst_start);
        };

        // Optional `[TypeArgs]` on path before `{` or `(`:
        var has_bracket_call = false;
        if (self.isTypeArgsAfterLBracket()) {
            base_node = try self.parseBracketPostfix(
                base_node,
                path_cst_start,
                path_ast_start,
                is_struct_lit_allowed,
            );
            has_bracket_call = self.has_last_expr_block_body;
        }

        // Optional `StructLiteral` `{ field: val, … }` or declarative `ViewBlock` `{ … }`:
        if (!has_bracket_call and is_struct_lit_allowed and self.peekKind() == .lbrace and
            (last_seg_kind == .type_ident or last_seg_kind == .kw_self_type))
        {
            const lbrace_tok = self.peekTokenIndexNth(0);
            if (self.isStructLiteralBrace()) {
                _ = try self.precedeNode(path_cst_start, path_ast_start, .struct_lit_expr, lbrace_tok);
                var field_nodes: std.ArrayList(u32) = .empty;
                defer field_nodes.deinit(self.ast.allocator);
                try self.parseStructLiteralBody(&field_nodes, &has_err);
                self.cst.finishNode(path_cst_start, .{ .has_error = has_err });
                self.has_last_expr_block_body = false;

                var rhs_op: PackedOperand = .NONE;
                if (field_nodes.items.len > 0) {
                    rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(field_nodes.items));
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .struct_lit,
                    .main_token = lbrace_tok,
                    .lhs = PackedOperand.initNode(base_node),
                    .rhs = rhs_op,
                }, path_cst_start);
            }

            // Declarative view block directly on a component type (`Card { … }`):
            _ = try self.precedeNode(path_cst_start, path_ast_start, .view_block_expr, lbrace_tok);
            const vb_node = try self.parseBlock();
            self.cst.finishNode(path_cst_start, .{ .has_error = has_err });
            self.has_last_expr_block_body = true;
            return self.ast.appendNodeWithCst(.{
                .tag = .call_expr,
                .main_token = lbrace_tok,
                .lhs = PackedOperand.initNode(base_node),
                .rhs = PackedOperand.initNode(vb_node),
            }, path_cst_start);
        }
        return base_node;
    }

    /// Parses `StructLiteral = "{" [ FieldInit { "," FieldInit } [ "," ] ] [ ".." Expr [ "," ] ] "}" ;`.
    fn parseStructLiteralBody(
        self: *Parser,
        field_nodes: *std.ArrayList(u32),
        has_error: *bool,
    ) anyerror!void {
        const open_brace = try self.consumeLeaf(.struct_lit_start, .{});
        self.pushState(.struct_lit_fields_loop, CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1))) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                _ = try self.recoverDepthOverflow(hole_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                has_error.* = true;
                return;
            },
            else => return err,
        };
        defer self.popStates(1);

        while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
            const loop_start = self.cursor;
            const field_cst = try self.startCstNode(.field_init);
            var has_field_err = false;

            if (self.peekKind() == .dotdot) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                try field_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());
                self.cst.finishNode(field_cst, .{});
                if (self.peekKind() == .comma) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                break;
            }

            if (isIdentifierKind(self.peekKind())) {
                const field_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_field_err,
                    "expected `snake_case` struct field initializer name",
                );
                if (self.peekKind() == .colon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    try field_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());
                } else {
                    const shorthand_node = try self.ast.appendNodeWithCst(.{
                        .tag = .ident_expr,
                        .main_token = field_tok,
                    }, field_cst);
                    try field_nodes.append(self.ast.allocator, shorthand_node.asInt());
                }
            } else {
                has_field_err = true;
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected field initializer inside struct literal",
                    "unexpected token in struct literal",
                );
                try self.skipToRecoveryAnchor(
                    STRUCT_FIELD_CONSUME_SET,
                    STRUCT_FIELD_STOP_SET,
                    false,
                );
            }

            if (has_field_err) has_error.* = true;
            self.cst.finishNode(field_cst, .{ .has_error = has_field_err });

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }
        try self.expectClosingDelimiter(
            .rbrace,
            open_brace,
            has_error,
            "expected `}` to close struct literal",
        );
    }

    /// Parses `ClosureExpr = { Attribute } ("||" | "|" [ClosureParam {"," ClosureParam} [","]] "|") ["->" Type] (Block | Expr)`.
    fn parseClosureExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        const clos_cst = try self.startCstNode(.closure_expr);
        var has_error = false;
        if (self.peekKind() == .at) {
            try self.parseAttributes(&has_error);
        }
        const open_tok = try self.consumeLeaf(.closure_start, .{});

        var param_tokens: std.ArrayList(u32) = .empty;
        defer param_tokens.deinit(self.ast.allocator);

        if (self.token_buffer.getToken(open_tok).kind == .pipe) {
            while (self.peekKind() != .pipe and
                self.peekKind() != .rbrace and
                self.peekKind() != .rparen and
                self.peekKind() != .semi and
                self.peekKind() != .eof)
            {
                const loop_start = self.cursor;
                const param_cst = try self.startCstNode(.closure_param);
                var has_param_err = false;

                if (self.peekKind() == .kw_mut or
                    self.peekKind() == .kw_own or
                    self.peekKind() == .kw_ref)
                {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                if (self.peekKind() == .underscore) {
                    try param_tokens.append(
                        self.ast.allocator,
                        (try self.consumeLeaf(.token_leaf, .{})).asInt(),
                    );
                } else {
                    const param_tok = try self.expectIdentifierWithCasing(
                        .ident,
                        .snake_case,
                        &has_param_err,
                        "expected `snake_case` closure parameter name",
                    );
                    try param_tokens.append(self.ast.allocator, param_tok.asInt());
                }

                if (self.peekKind() == .colon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.parseType();
                }
                if (has_param_err) has_error = true;
                self.cst.finishNode(param_cst, .{ .has_error = has_param_err });

                if (self.peekKind() == .comma) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else {
                    break;
                }
                if (self.cursor == loop_start) break;
            }
            _ = try self.expectToken(
                .pipe,
                &has_error,
                "expected closing `|` after closure parameters",
                "expected `|` here",
            );
        }

        if (self.peekKind() == .arrow) {
            const ret_cst = try self.startCstNode(.return_type);
            _ = try self.consumeLeaf(.token_leaf, .{});
            _ = try self.parseType();
            self.cst.finishNode(ret_cst, .{ .has_error = has_error });
        }

        const body_node = if (self.peekKind() == .lbrace)
            try self.parseBlock()
        else
            try self.parseExpr(is_struct_lit_allowed);

        self.cst.finishNode(clos_cst, .{ .has_error = has_error });
        var lhs_op: PackedOperand = .NONE;
        if (param_tokens.items.len > 0) {
            lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(param_tokens.items));
        }
        return self.ast.appendNodeWithCst(.{
            .tag = .closure_expr,
            .main_token = open_tok,
            .lhs = lhs_op,
            .rhs = PackedOperand.initNode(body_node),
        }, clos_cst);
    }

    /// Parses `IfExpr = "if" ("let" Pattern "=" ExprNoStruct | ExprNoStruct) Block ["else" (IfExpr | Block)]`.
    fn parseIfExpr(self: *Parser) anyerror!NodeIndex {
        const if_cst = try self.startCstNode(.if_expr);
        self.pushState(.if_after_cond, if_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(if_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_error = false;
        const if_tok = try self.consumeLeaf(.if_introducer, .{});

        const cond_cst = try self.startCstNode(.if_cond);
        var cond_node: NodeIndex = .none;
        if (self.peekKind() == .kw_let) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            const pat_node = try self.parsePattern(false);
            _ = try self.expectToken(
                .eq,
                &has_error,
                "expected `=` after `if let` pattern",
                "expected `=` here",
            );
            const scrutinee = try self.parseExpr(false);
            const extra_pair = [_]u32{ pat_node.asInt(), scrutinee.asInt() };
            const extra_idx = try self.ast.appendExtraSlice(&extra_pair);
            cond_node = try self.ast.appendNodeWithCst(.{
                .tag = .binary_expr,
                .main_token = if_tok,
                .lhs = PackedOperand.initExtra(extra_idx),
                .rhs = PackedOperand.initNode(scrutinee),
            }, cond_cst);
        } else {
            cond_node = try self.parseExpr(false);
            // Support optional `|capture|` payload before `{` (`DR-02` Section 3.1):
            if (self.isPayloadCaptureBar()) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .amp) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                _ = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_error,
                    "expected `snake_case` payload capture identifier",
                );
                _ = try self.expectToken(
                    .pipe,
                    &has_error,
                    "expected closing `|` after payload capture",
                    "expected `|` here",
                );
            }
        }
        self.cst.finishNode(cond_cst, .{ .has_error = has_error });

        const then_block = try self.parseBlock();
        var rhs_op = PackedOperand.initNode(then_block);

        if (self.peekKind() == .kw_else) {
            const else_cst = try self.startCstNode(.else_branch);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const else_node = if (self.peekKind() == .kw_if)
                try self.parseIfExpr()
            else
                try self.parseBlock();
            self.cst.finishNode(else_cst, .{});

            const branches = [_]u32{ then_block.asInt(), else_node.asInt() };
            rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(&branches));
        }

        self.cst.finishNode(if_cst, .{ .has_error = has_error });
        self.has_last_expr_block_body = true;
        return self.ast.appendNodeWithCst(.{
            .tag = .if_expr,
            .main_token = if_tok,
            .lhs = PackedOperand.initNode(cond_node),
            .rhs = rhs_op,
        }, if_cst);
    }

    /// Parses `MatchExpr = "match" ExprNoStruct "{" { MatchArm } "}" ;`.
    fn parseMatchExpr(self: *Parser) anyerror!NodeIndex {
        const match_cst = try self.startCstNode(.match_expr);
        self.pushState(.match_arms_loop, match_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(match_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_error = false;
        const match_tok = try self.consumeLeaf(.match_introducer, .{});
        const scrutinee = try self.parseExpr(false);

        var arm_entries: std.ArrayList(u32) = .empty;
        defer arm_entries.deinit(self.ast.allocator);

        if (self.peekKind() == .lbrace) {
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const loop_start = self.cursor;
                const arm_cst = try self.startCstNode(.match_arm);
                var has_arm_err = false;

                const pat_node = try self.parsePattern(false);
                if (self.peekKind() == .kw_if) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    _ = try self.parseExpr(false);
                }

                if (self.peekKind() == .fat_arrow) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else {
                    has_arm_err = true;
                    has_error = true;
                    try self.emitUnexpectedToken(
                        self.peekTokenIndexNth(0),
                        "expected `=>` after `match` arm pattern",
                        "expected `=>` here",
                    );
                    try self.skipToRecoveryAnchor(
                        MATCH_ARM_CONSUME_SET,
                        MATCH_ARM_STOP_SET,
                        false,
                    );
                    if (self.peekKind() == .fat_arrow) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                }

                const body_node = if (self.peekKind() == .lbrace)
                    try self.parseBlock()
                else
                    try self.parseExpr(true);

                try arm_entries.append(self.ast.allocator, pat_node.asInt());
                try arm_entries.append(self.ast.allocator, body_node.asInt());

                if (self.peekKind() == .comma) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                if (has_arm_err) has_error = true;
                self.cst.finishNode(arm_cst, .{ .has_error = has_arm_err });

                if (self.cursor == loop_start) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
            }
            try self.expectClosingDelimiter(
                .rbrace,
                open_brace,
                &has_error,
                "expected `}` to close `match` expression",
            );
        } else {
            has_error = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to open `match` arms",
                "expected `{` here",
            );
        }

        self.cst.finishNode(match_cst, .{ .has_error = has_error });
        self.has_last_expr_block_body = true;

        var rhs_op: PackedOperand = .NONE;
        if (arm_entries.items.len > 0) {
            rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(arm_entries.items));
        }
        return self.ast.appendNodeWithCst(.{
            .tag = .match_expr,
            .main_token = match_tok,
            .lhs = PackedOperand.initNode(scrutinee),
            .rhs = rhs_op,
        }, match_cst);
    }
};

// ------------------ Standalone Entry Points -------------------

/// Parses an already-tokenized `token_buffer` into `cst_arena` and `ast_arena`, returning `NodeIndex.root`.
pub fn parseTokens(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *LosslessCstArena,
    ast_arena: *AstArena,
    diagnostic_sink: ?*DiagnosticSink,
    interner: ?*StringInterner,
) !NodeIndex {
    var parser_instance = Parser.init(
        source,
        file_id,
        token_buffer,
        cst_arena,
        ast_arena,
        diagnostic_sink,
        interner,
    );
    return parser_instance.parse();
}

/// Tokenizes `source` into `token_buffer` and parses into `cst_arena` and `ast_arena`.
pub fn parseSource(
    source: []const u8,
    file_id: FileId,
    token_buffer: *TokenBuffer,
    cst_arena: *LosslessCstArena,
    ast_arena: *AstArena,
    diagnostic_sink: ?*DiagnosticSink,
    interner: ?*StringInterner,
) !NodeIndex {
    token_buffer.tokens.shrinkRetainingCapacity(0);
    token_buffer.trivia.clearRetainingCapacity();
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();

    try lexer.tokenize(source, file_id, token_buffer, diagnostic_sink, interner);
    return parseTokens(
        source,
        file_id,
        token_buffer,
        cst_arena,
        ast_arena,
        diagnostic_sink,
        interner,
    );
}

/// Canonical alias for `parseSource` matching `lexFile`.
pub const parseFile = parseSource;

/// Incrementally re-lexes and re-parses `new_source` across `edit` in $O(K + \text{window})$ time.
pub fn reparseIncremental(
    new_source: []const u8,
    file_id: FileId,
    edit: EditRange,
    token_buffer: *TokenBuffer,
    cst_arena: *LosslessCstArena,
    ast_arena: *AstArena,
    diagnostic_sink: ?*DiagnosticSink,
    interner: ?*StringInterner,
) !IncrementalReparseStats {
    // [1] Verify that the prior token buffer and CST are error-free and structurally eligible:
    if (edit.start_byte <= edit.old_end_byte and
        edit.start_byte <= edit.new_end_byte and
        edit.new_end_byte <= new_source.len and
        hasCleanTokensAndCst(token_buffer, cst_arena))
    {
        var has_potential_lexer_warn_in_reused = false;
        if (diagnostic_sink != null) {
            for (token_buffer.tokens.items(.kind)) |tok_kind| {
                if (tok_kind == .string_lit or tok_kind == .char_lit) {
                    has_potential_lexer_warn_in_reused = true;
                    break;
                }
            }
        }
        const old_eof_tok = TokenIndex.fromInt(@intCast(token_buffer.countTokens() - 1));
        const old_eof_offset = token_buffer.getToken(old_eof_tok).byte_offset;
        const byte_delta: i64 = @as(i64, edit.new_end_byte) - @as(i64, edit.old_end_byte);

        if (!has_potential_lexer_warn_in_reused and
            @as(i64, old_eof_offset) + byte_delta == @as(i64, @intCast(new_source.len)))
        {
            const windows = try extractTopLevelItemWindows(
                cst_arena.allocator,
                token_buffer,
                cst_arena,
            );
            defer cst_arena.allocator.free(windows);

            const total_items: u32 = @intCast(windows.len);
            // Identify untouched prefix items `[0 .. prefix_count)` where `end_byte(m) < edit.start_byte`:
            var prefix_count: u32 = 0;
            while (prefix_count < total_items and
                windows[prefix_count].end_byte < edit.start_byte) : (prefix_count += 1)
            {}

            // Identify untouched suffix items `[suffix_start .. total_items)` where `start_byte(m) > edit.old_end_byte`:
            var suffix_start: u32 = total_items;
            while (suffix_start > prefix_count and
                windows[suffix_start - 1].start_byte > edit.old_end_byte) : (suffix_start -= 1)
            {}

            if (prefix_count > 0 or suffix_start < total_items) {
                const reparse_start_byte: u32 = if (prefix_count < total_items)
                    windows[prefix_count].start_byte
                else
                    getTokenEarliestByte(token_buffer, old_eof_tok);

                const reparse_old_end_byte: u32 = if (suffix_start < total_items)
                    windows[suffix_start].start_byte
                else
                    old_eof_offset;

                const reparse_new_end_byte: u32 = @intCast(
                    @as(i64, reparse_old_end_byte) + byte_delta,
                );

                // [2] Re-lex the modified byte window `[reparse_start_byte .. reparse_new_end_byte]`:
                var window_tokens = TokenBuffer.init(token_buffer.allocator);
                defer window_tokens.deinit();
                var window_sink = DiagnosticSink.init(token_buffer.allocator);
                defer window_sink.deinit();

                var win_lexer = lexer.Lexer.init(
                    new_source[0..reparse_new_end_byte],
                    file_id,
                    &window_tokens,
                    &window_sink,
                    interner,
                );
                win_lexer.cursor = reparse_start_byte;
                try win_lexer.tokenize();

                const win_eof_tok = TokenIndex.fromInt(@intCast(window_tokens.countTokens() - 1));
                const is_suffix_reused = suffix_start < total_items;
                const has_stray_eof_trivia = is_suffix_reused and
                    window_tokens.getLeadingTrivia(win_eof_tok).len > 0;

                var has_win_lex_err = window_sink.countDiagnostics() > 0 or has_stray_eof_trivia;
                if (!has_win_lex_err) {
                    for (window_tokens.tokens.items(.flags)) |flag_item| {
                        if (flag_item.has_lexer_error or flag_item.is_synthesized) {
                            has_win_lex_err = true;
                            break;
                        }
                    }
                }

                if (!has_win_lex_err) {
                    const tok_start: usize = if (prefix_count < total_items)
                        windows[prefix_count].first_token
                    else
                        old_eof_tok.asInt();
                    const tok_old_end: usize = if (is_suffix_reused)
                        windows[suffix_start].first_token
                    else
                        token_buffer.countTokens();

                    const win_tok_count: usize = if (is_suffix_reused)
                        window_tokens.countTokens() - 1
                    else
                        window_tokens.countTokens();

                    // Save a backup of `token_buffer` in case window parsing fails:
                    var saved_tokens = try token_buffer.tokens.clone(token_buffer.allocator);
                    defer saved_tokens.deinit(token_buffer.allocator);
                    var saved_trivia = try token_buffer.trivia.clone(token_buffer.allocator);
                    defer saved_trivia.deinit(token_buffer.allocator);

                    try spliceTokenBufferWindow(
                        token_buffer,
                        tok_start,
                        tok_old_end,
                        &window_tokens,
                        !is_suffix_reused,
                        byte_delta,
                    );

                    // [3] Parse the spliced token window `[tok_start .. tok_new_end)`:
                    const tok_new_end: u32 = @intCast(
                        tok_start + (if (is_suffix_reused) win_tok_count else win_tok_count - 1),
                    );
                    var window_cst = LosslessCstArena.init(cst_arena.allocator);
                    defer window_cst.deinit();
                    var dummy_ast = AstArena.init(ast_arena.allocator);
                    defer dummy_ast.deinit();

                    var win_parser = Parser.init(
                        new_source,
                        file_id,
                        token_buffer,
                        &window_cst,
                        &dummy_ast,
                        &window_sink,
                        interner,
                    );
                    win_parser.cursor = @intCast(tok_start);

                    var reparsed_items: u32 = 0;
                    while (win_parser.cursor < tok_new_end and win_parser.peekKind() != .eof) {
                        const before_cur = win_parser.cursor;
                        _ = try win_parser.parseItem();
                        reparsed_items += 1;
                        if (win_parser.cursor == before_cur) break;
                    }

                    if (!is_suffix_reused and win_parser.cursor < token_buffer.countTokens()) {
                        const final_eof_tok = TokenIndex.fromInt(win_parser.cursor);
                        _ = try window_cst.appendLeafNode(.token_leaf, final_eof_tok, .{});
                        win_parser.cursor += 1;
                    }

                    const expected_end_cursor: u32 = if (is_suffix_reused)
                        tok_new_end
                    else
                        @intCast(token_buffer.countTokens());

                    if (!window_cst.has_parse_errors and
                        window_sink.countDiagnostics() == 0 and
                        win_parser.cursor == expected_end_cursor)
                    {
                        const cst_start: usize = if (prefix_count < total_items)
                            windows[prefix_count].cst_start
                        else
                            cst_arena.countNodes() - 1;
                        const cst_old_end: usize = if (is_suffix_reused)
                            windows[suffix_start].cst_start
                        else
                            cst_arena.countNodes();

                        const token_delta: i64 = @as(i64, @intCast(win_tok_count)) -
                            @as(i64, @intCast(tok_old_end - tok_start));

                        try spliceCstArenaWindow(
                            cst_arena,
                            cst_start,
                            cst_old_end,
                            &window_cst,
                            token_delta,
                        );

                        // [4] Rebuild `ast_arena` from spliced `token_buffer` for bit-for-bit parity with scratch parse:
                        ast_arena.nodes.shrinkRetainingCapacity(0);
                        ast_arena.extra_data.clearRetainingCapacity();
                        ast_arena.ast_to_cst.clearRetainingCapacity();

                        var verify_cst = LosslessCstArena.init(cst_arena.allocator);
                        defer verify_cst.deinit();
                        _ = try parseTokens(
                            new_source,
                            file_id,
                            token_buffer,
                            &verify_cst,
                            ast_arena,
                            diagnostic_sink,
                            interner,
                        );

                        return .{
                            .reused_prefix_items = prefix_count,
                            .reparsed_items = reparsed_items,
                            .reused_suffix_items = total_items - suffix_start,
                            .is_fast_splice = true,
                        };
                    }

                    // Restore `token_buffer` before falling back to full scratch parse:
                    token_buffer.tokens.deinit(token_buffer.allocator);
                    token_buffer.tokens = try saved_tokens.clone(token_buffer.allocator);
                    token_buffer.trivia.deinit(token_buffer.allocator);
                    token_buffer.trivia = try saved_trivia.clone(token_buffer.allocator);
                }
            }
        }
    }

    // Fallback to full scratch tokenize and parse:
    const root_id = try parseSource(
        new_source,
        file_id,
        token_buffer,
        cst_arena,
        ast_arena,
        diagnostic_sink,
        interner,
    );
    const root_node = ast_arena.getNode(root_id);
    const total_reparsed: u32 = if (root_node.rhs.tag == .extra) root_node.rhs.payload else 0;
    return .{
        .reused_prefix_items = 0,
        .reparsed_items = total_reparsed,
        .reused_suffix_items = 0,
        .is_fast_splice = false,
    };
}

// ------------------------- Unit Tests -------------------------

/// Verifies pre-order CST subtree partitioning, monotonic token coverage, and lossless round-tripping.
fn verifyCstAndAstInvariants(
    allocator: std.mem.Allocator,
    source: []const u8,
    token_buf: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    ast_arena: *const AstArena,
) !void {
    try std.testing.expect(cst_arena.countNodes() >= 2);
    const root_cst = cst_arena.getNode(CstNodeIndex.fromInt(0));
    try std.testing.expectEqual(CstNodeKind.source_file, root_cst.kind);
    try std.testing.expectEqual(@as(u32, @intCast(cst_arena.countNodes())), root_cst.subtree_size);

    // [1] Every composite CST node's children must partition `[idx + 1 .. idx + subtree_size)`:
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
        }
    }

    // [2] Every `ast_to_cst` origin must point to a valid CST node index:
    try std.testing.expectEqual(ast_arena.countNodes(), ast_arena.ast_to_cst.items.len);
    for (ast_arena.ast_to_cst.items) |origin| {
        if (!origin.isNone()) {
            try std.testing.expect(origin.asInt() < cst_arena.countNodes());
        }
    }

    // [3] Lossless source reconstruction must be 100% byte-for-byte identical to `source`:
    const reconstructed = try cst_arena.reconstructSource(allocator, source, token_buf);
    defer allocator.free(reconstructed);
    try std.testing.expectEqualSlices(u8, source, reconstructed);
}

test "test_parser_all_four_dr03_domain_showcases_zero_errors" {
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
        \\pub struct ScanStats {
        \\    pub lines_scanned: u64,
        \\    pub matches_found: u64,
        \\    pub bytes_processed: u64,
        \\}
        \\pub fn scan_file(arena: &mut Arena, opts: &ScanOptions, out: &mut Stdout) -> Result[ScanStats, IoError] {
        \\    let file = File::open(opts.file_path)?;
        \\    defer file.close();
        \\    var reader = BufReader::with_capacity(arena, file, DEFAULT_BUF_CAP);
        \\    var stats = ScanStats { lines_scanned: 0, matches_found: 0, bytes_processed: 0 };
        \\    while let .Some(line) = reader.next_line()? {
        \\        stats.lines_scanned += 1;
        \\        stats.bytes_processed += line.len() as u64;
        \\        let matched = if opts.ignore_case {
        \\            line.contains_ascii_ignore_case(opts.pattern)
        \\        } else {
        \\            line.contains(opts.pattern)
        \\        };
        \\        if matched {
        \\            stats.matches_found += 1;
        \\            out.write_fmt("{opts.file_path}:{stats.lines_scanned}: {line}\n")?;
        \\            if stats.matches_found >= (opts.max_matches as u64) {
        \\                break;
        \\            }
        \\        }
        \\    }
        \\    .Ok(stats)
        \\}
        \\pub fn main() -> i32 {
        \\    var arena = Arena::with_capacity(1_048_576);
        \\    defer arena.release();
        \\    let opts = match env::parse_args[ScanOptions](&mut arena) {
        \\        .Ok(parsed) => parsed,
        \\        .Err(err) => {
        \\            std::io::stderr().write_fmt("argument error: {err}\n");
        \\            return 2;
        \\        }
        \\    };
        \\    var stdout = Stdout::locked();
        \\    match scan_file(&mut arena, &opts, &mut stdout) {
        \\        .Ok(stats) => {
        \\            stdout.write_fmt("Scanned {stats.lines_scanned} lines\n");
        \\            0
        \\        }
        \\        .Err(err) => {
        \\            std::io::stderr().write_fmt("I/O failure: {err}\n");
        \\            1
        \\        }
        \\    }
        \\}
    ;

    const showcase_2_api =
        \\mod user_api;
        \\use net::http::{Request, Response, StatusCode, Json};
        \\use db::pg::{PgPool, TxIsolation};
        \\use crypto::argon2;
        \\use serde::{Serialize, Deserialize};
        \\const MAX_BODY_BYTES: usize = 16_384;
        \\@derive(Deserialize)
        \\pub struct CreateUserReq {
        \\    pub username: str,
        \\    pub email: str,
        \\    pub password_raw: str,
        \\    pub role: UserRole?,
        \\}
        \\@derive(Serialize, Deserialize)
        \\pub enum UserRole {
        \\    Admin,
        \\    Member,
        \\    Auditor { department_id: u32 },
        \\}
        \\@derive(Serialize)
        \\pub struct CreateUserResp {
        \\    pub user_id: u64,
        \\    pub username: str,
        \\    pub created_at_unix: i64,
        \\}
        \\pub enum ApiError {
        \\    PayloadTooLarge,
        \\    InvalidJson(str),
        \\    ValidationFailed(str),
        \\    ConflictEmail(str),
        \\    DatabaseError(str),
        \\}
        \\impl ApiError {
        \\    pub fn into_response(self) -> Response {
        \\        match self {
        \\            .PayloadTooLarge => Response::status(StatusCode::PayloadTooLarge),
        \\            .InvalidJson(msg) => Response::json(StatusCode::BadRequest, msg),
        \\            .ValidationFailed(reason) => Response::json(StatusCode::UnprocessableEntity, reason),
        \\            .ConflictEmail(email) => Response::json(StatusCode::Conflict, "Email: {email}"),
        \\            .DatabaseError(_) => Response::status(StatusCode::InternalServerError),
        \\        }
        \\    }
        \\}
        \\@route(method = "POST", path = "/v1/users")
        \\pub async fn create_user(req: &mut Request, pool: &PgPool) -> Result[Json[CreateUserResp], ApiError] {
        \\    let body_bytes = req.read_body_bounded(MAX_BODY_BYTES).await?;
        \\    let payload = body_bytes
        \\        |> Json::parse[CreateUserReq]()
        \\        |> Result::map_err(|e| ApiError::InvalidJson(e.message()))?;
        \\    if payload.username.len() < 3 or not payload.email.contains("@") {
        \\        return .Err(ApiError::ValidationFailed("invalid username or email"));
        \\    }
        \\    let password_hash = argon2::hash_password(payload.password_raw).await?;
        \\    let assigned_role = payload.role.unwrap_or(.Member);
        \\    var tx = pool.begin_tx(TxIsolation::Serializable).await?;
        \\    defer tx.rollback_if_uncommitted();
        \\    let exists = tx.query_scalar[bool](
        \\        "SELECT EXISTS(SELECT 1 FROM users WHERE email = $1)",
        \\        [payload.email],
        \\    ).await?;
        \\    if exists {
        \\        return .Err(ApiError::ConflictEmail(payload.email));
        \\    }
        \\    let (user_id, created_at_unix) = tx.query_one[(u64, i64)](
        \\        "INSERT INTO users VALUES ($1, $2, $3, $4) RETURNING id, created_at",
        \\        [payload.username, payload.email, password_hash, assigned_role.as_str()],
        \\    ).await?;
        \\    tx.commit().await?;
        \\    .Ok(Json::from(CreateUserResp {
        \\        user_id,
        \\        username: payload.username,
        \\        created_at_unix,
        \\    }))
        \\}
    ;

    const showcase_3_avl =
        \\mod avl_tree;
        \\use std::cmp::{Ord, Ordering};
        \\use std::mem::{PoolAllocator, OwnPtr};
        \\pub struct AvlNode[K: Ord, V] {
        \\    pub key: K,
        \\    pub value: V,
        \\    pub height: i32,
        \\    pub left: OwnPtr[AvlNode[K, V]]?,
        \\    pub right: OwnPtr[AvlNode[K, V]]?,
        \\}
        \\pub struct AvlTree[K: Ord, V] {
        \\    root: OwnPtr[AvlNode[K, V]]?,
        \\    pool: PoolAllocator[AvlNode[K, V]],
        \\    len: usize,
        \\}
        \\impl[K: Ord, V] AvlTree[K, V] {
        \\    pub fn with_capacity(cap: usize) -> Self {
        \\        Self {
        \\            root: .None,
        \\            pool: PoolAllocator::new[AvlNode[K, V]](cap),
        \\            len: 0,
        \\        }
        \\    }
        \\    fn rotate_right(mut y: OwnPtr[AvlNode[K, V]]) -> OwnPtr[AvlNode[K, V]] {
        \\        let .Some(mut x) = y.left.take() else {
        \\            return y;
        \\        };
        \\        y.left = x.right.take();
        \\        Self::update_height(&mut y);
        \\        x.right = .Some(own y);
        \\        Self::update_height(&mut x);
        \\        x
        \\    }
        \\    fn rebalance(mut node: OwnPtr[AvlNode[K, V]]) -> OwnPtr[AvlNode[K, V]] {
        \\        let bf = Self::balance_factor(&node);
        \\        if bf > 1 {
        \\            if let .Some(ref left_child) = node.left {
        \\                if Self::balance_factor(left_child) < 0 {
        \\                    let left_owned = node.left.take().unwrap();
        \\                    node.left = .Some(Self::rotate_left(own left_owned));
        \\                }
        \\            }
        \\            return Self::rotate_right(own node);
        \\        }
        \\        node
        \\    }
        \\}
    ;

    const showcase_4_ui =
        \\mod ui_telemetry;
        \\use ui::core::{View, Signal, Computed, Theme, Color};
        \\use ui::widgets::{Column, Row, Card, Text, Button, ProgressBar, Badge};
        \\pub struct MetricSample {
        \\    pub timestamp_ms: u64,
        \\    pub cpu_load: f32,
        \\    pub mem_used_mb: u32,
        \\}
        \\@component
        \\pub fn telemetry_dashboard(node_name: str, samples: &Signal[Vec[MetricSample]], theme: &Theme) -> View {
        \\    @state var is_paused: bool = false;
        \\    @state var threshold_pct: f32 = 80.0;
        \\    let latest_cpu = Computed::new(|| -> f32 {
        \\        match samples.get().last() {
        \\            .Some(sample) => sample.cpu_load,
        \\            .None => 0.0,
        \\        }
        \\    });
        \\    let is_critical = Computed::new(|| latest_cpu.get() >= threshold_pct);
        \\    Card(padding: 16, border_color: theme.border_subtle) {
        \\        Row(justify: .SpaceBetween, align: .Center) {
        \\            Text(value: "Node: {node_name}", weight: .Bold, size: 18);
        \\            if is_critical.get() {
        \\                Badge(label: "CRITICAL", color: Color::Red);
        \\            } else {
        \\                Badge(label: "HEALTHY", color: Color::Emerald);
        \\            }
        \\        }
        \\        Column(gap: 12) {
        \\            ProgressBar(
        \\                value: latest_cpu.get(),
        \\                max: 100.0,
        \\                tint: if is_critical.get() { Color::Red } else { Color::Cyan },
        \\            );
        \\            Row(gap: 8) {
        \\                Button(
        \\                    label: if is_paused { "Resume Stream" } else { "Pause Stream" },
        \\                    on_click: || { is_paused = not is_paused; },
        \\                );
        \\                Button(
        \\                    label: "Reset Alert (+5%)",
        \\                    on_click: || { threshold_pct += 5.0; },
        \\                );
        \\            }
        \\        }
        \\    }
        \\}
    ;

    const showcases = [_][]const u8{
        showcase_1_cli,
        showcase_2_api,
        showcase_3_avl,
        showcase_4_ui,
    };

    for (showcases, 0..) |showcase_src, idx| {
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

        const root_id = try parseSource(
            showcase_src,
            FileId.fromInt(@intCast(idx)),
            &token_buf,
            &cst_arena,
            &ast_arena,
            &sink,
            &interner,
        );
        try std.testing.expectEqual(NodeIndex.root, root_id);
        try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
        try std.testing.expect(!cst_arena.has_parse_errors);
        try verifyCstAndAstInvariants(
            std.testing.allocator,
            showcase_src,
            &token_buf,
            &cst_arena,
            &ast_arena,
        );
    }
}

test "test_parser_mid_keystroke_ide_recovery_and_casing_autofix_dedup" {
    // [1] `user.` trailing dot -> `incomplete_member_access`, `repo.find(id, ` -> `incomplete_call`:
    const incomplete_src =
        \\fn test_ide() {
        \\    let name = user.
        \\    let rec = repo.find(user_id, )
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

    _ = try parseSource(
        incomplete_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        null,
    );
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        incomplete_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    var has_incomplete_member = false;
    var has_incomplete_call = false;
    for (ast_arena.nodes.items(.tag)) |tag_val| {
        if (tag_val == .incomplete_member_access) has_incomplete_member = true;
        if (tag_val == .incomplete_call) has_incomplete_call = true;
    }
    try std.testing.expect(has_incomplete_member);
    try std.testing.expect(has_incomplete_call);

    // [2] Hybrid typo `struct bad_Camel {}` must emit exactly ONE `W0201` with `BadCamel` autofix:
    const casing_src = "struct bad_Camel { pub BadField: i32 }\n";
    var case_sink = DiagnosticSink.init(std.testing.allocator);
    defer case_sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    _ = try parseSource(
        casing_src,
        FileId.fromInt(1),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &case_sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 0), case_sink.error_count);
    try std.testing.expectEqual(@as(u32, 2), case_sink.warning_count);
    const diags = case_sink.asSlice();
    try std.testing.expectEqualStrings(
        "BadCamel",
        interner.get(diags[0].suggestions[0].edits[0].replacement_id),
    );
    try std.testing.expectEqualStrings(
        "bad_field",
        interner.get(diags[1].suggestions[0].edits[0].replacement_id),
    );
}

test "test_parser_non_associative_ops_unclosed_delimiters_and_depth_cap" {
    // [1] Non-associative relational (`a < b < c`) and range (`1..2..3`) operators emit `E0201`:
    const non_assoc_src = "fn check() { let a = 1 < 2 < 3; let r = 1..2..3; }\n";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    _ = try parseSource(
        non_assoc_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        null,
    );
    try std.testing.expect(sink.error_count >= 2);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        non_assoc_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [2] Unclosed delimiter (`E0202`) carries secondary label `"unclosed delimiter opened here"`:
    const unclosed_src = "fn broken(a: i32 {\n    return a;\n}\n";
    var unclosed_sink = DiagnosticSink.init(std.testing.allocator);
    defer unclosed_sink.deinit();
    _ = try parseSource(
        unclosed_src,
        FileId.fromInt(1),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &unclosed_sink,
        null,
    );
    try std.testing.expect(unclosed_sink.error_count >= 1);
    try std.testing.expectEqual(
        DiagnosticCode.e0202_unclosed_delimiter,
        unclosed_sink.asSlice()[0].code,
    );
    try std.testing.expectEqual(@as(usize, 2), unclosed_sink.asSlice()[0].labels.len);
    try std.testing.expectEqualStrings(
        "unclosed delimiter opened here",
        unclosed_sink.asSlice()[0].labels[1].label,
    );

    // [3] Left-associative chaining (`1 + 1 + 1 + …`) exceeding `max_depth` emits `E0203`:
    const chain_src = "fn deep() -> i32 { return 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1; }\n";
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

    try lexer.tokenize(chain_src, FileId.fromInt(2), &token_buf, &depth_sink, null);
    var capped_parser = Parser.initWithOptions(
        chain_src,
        FileId.fromInt(2),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &depth_sink,
        null,
        .{ .max_depth = 8 },
    );
    _ = try capped_parser.parse();
    try std.testing.expectEqual(@as(u32, 1), depth_sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0203_parse_depth_exceeded,
        depth_sink.asSlice()[0].code,
    );
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        chain_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
}

test "test_parser_incremental_reparse_matches_scratch_parse_bit_for_bit" {
    const old_source =
        \\const FIRST_CONST: u32 = 10;
        \\
        \\pub fn middle_fn(val: u32) -> u32 {
        \\    return val + 1;
        \\}
        \\
        \\pub fn suffix_fn(other: u32) -> u32 {
        \\    return other * 2;
        \\}
    ;
    const new_source =
        \\const FIRST_CONST: u32 = 10;
        \\
        \\pub fn middle_fn(val: u32) -> u32 {
        \\    return val + 42_000;
        \\}
        \\
        \\pub fn suffix_fn(other: u32) -> u32 {
        \\    return other * 2;
        \\}
    ;

    const edit_pos: u32 = @intCast(std.mem.indexOf(u8, old_source, "val + 1").?);
    const edit = EditRange{
        .start_byte = edit_pos,
        .old_end_byte = edit_pos + 7,
        .new_end_byte = edit_pos + 12,
    };

    var inc_tokens = TokenBuffer.init(std.testing.allocator);
    defer inc_tokens.deinit();
    var inc_cst = LosslessCstArena.init(std.testing.allocator);
    defer inc_cst.deinit();
    var inc_ast = AstArena.init(std.testing.allocator);
    defer inc_ast.deinit();

    _ = try parseSource(
        old_source,
        FileId.fromInt(0),
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );

    const stats = try reparseIncremental(
        new_source,
        FileId.fromInt(0),
        edit,
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        null,
        null,
    );
    try std.testing.expect(stats.is_fast_splice);
    try std.testing.expectEqual(@as(u32, 1), stats.reused_prefix_items);
    try std.testing.expectEqual(@as(u32, 1), stats.reparsed_items);
    try std.testing.expectEqual(@as(u32, 1), stats.reused_suffix_items);

    // Compare against a fresh full scratch parse of `new_source`:
    var scratch_tokens = TokenBuffer.init(std.testing.allocator);
    defer scratch_tokens.deinit();
    var scratch_cst = LosslessCstArena.init(std.testing.allocator);
    defer scratch_cst.deinit();
    var scratch_ast = AstArena.init(std.testing.allocator);
    defer scratch_ast.deinit();

    _ = try parseSource(
        new_source,
        FileId.fromInt(0),
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
        try std.testing.expectEqual(scratch_ast.getCstOrigin(ast_id), inc_ast.getCstOrigin(ast_id));
    }
    try std.testing.expectEqualSlices(
        u32,
        scratch_ast.extra_data.items,
        inc_ast.extra_data.items,
    );
}

test "test_parser_red_team_adversarial_regressions_rt01_to_rt07" {
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    // [1] `RT-01` – Malformed path expression (`foo::;` and `foo::123`) finishes `.path_pat` CST subtree:
    const rt01_src = "fn test_rt01() { let first = foo::; let second = bar::123; }\n";
    _ = try parseSource(rt01_src, FileId.fromInt(0), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expect(sink.error_count >= 2);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        rt01_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [2] `RT-02` – Empty `TokenBuffer` and non-`.eof`-terminated `TokenBuffer` terminate cleanly:
    var empty_tokens = TokenBuffer.init(std.testing.allocator);
    defer empty_tokens.deinit();
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();
    _ = try parseTokens("", FileId.fromInt(1), &empty_tokens, &cst_arena, &ast_arena, null, null);
    try std.testing.expectEqual(@as(usize, 1), cst_arena.countNodes());

    _ = try empty_tokens.appendToken(.kw_fn, .{}, 0, 2, &.{}, &.{});
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();
    _ = try parseTokens("fn", FileId.fromInt(1), &empty_tokens, &cst_arena, &ast_arena, null, null);
    try std.testing.expect(cst_arena.countNodes() >= 2);

    // [3] `RT-03` & `RT-04` – Bounded lookahead and `recoverDepthOverflow` on `stop_set` token:
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

    try lexer.tokenize(rt04_src, FileId.fromInt(2), &token_buf, &sink, null);
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
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        rt04_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [4] `RT-05` – `reparseIncremental` malformed `EditRange` guard:
    const fallback_stats = try reparseIncremental(
        rt04_src,
        FileId.fromInt(2),
        .{ .start_byte = 10, .old_end_byte = 12, .new_end_byte = 5 },
        &token_buf,
        &cst_arena,
        &ast_arena,
        null,
        null,
    );
    try std.testing.expect(!fallback_stats.is_fast_splice);

    // [5] `RT-06` – Malformed patterns (`-true`, `1..`, `Foo::`) emit `E0201`:
    const rt06_src = "fn pat_err(val: i32) -> i32 { return match val { -true => 1, 1.. => 2, Foo:: => 3 }; }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(rt06_src, FileId.fromInt(3), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expect(sink.error_count >= 3);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        rt06_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [6] `RT-07` – Generic & standard call with empty trailing view block `Card[u32](padding: 16) {}`:
    const rt07_src = "fn render() { Card[u32](padding: 16) {} Row(gap: 8) {} }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(rt07_src, FileId.fromInt(4), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        rt07_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
    var view_block_count: usize = 0;
    for (cst_arena.nodes.items(.kind)) |cst_kind| {
        if (cst_kind == .view_block_expr) view_block_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), view_block_count);
}

test "test_parse_phase5_intrinsics_comptime_and_is_pattern" {
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = diagnostic.DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    const valid_src =
        "fn check_phase5[T](comptime msg: str, status: Status) -> usize {\n" ++
        "    @allow_unused let local_val = @size_of[T]();\n" ++
        "    @compile_assert(local_val > 0, msg);\n" ++
        "    comptime {\n" ++
        "        @compile_assert(@implements[T, Eq](), msg);\n" ++
        "    }\n" ++
        "    comptime for idx in 0..2 {\n" ++
        "        let step = idx;\n" ++
        "    }\n" ++
        "    if status is Ready {\n" ++
        "        return comptime @align_of[T]();\n" ++
        "    }\n" ++
        "    if status is .Pending(code) {\n" ++
        "        return code;\n" ++
        "    }\n" ++
        "    return local_val;\n" ++
        "}\n";

    _ = try parseSource(valid_src, FileId.fromInt(0), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        valid_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // Chained `a is B is C` is non-associative and must emit `E0201`:
    const non_assoc_src = "fn chained_is(val: Status) -> bool { return val is Ready is Ready; }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(non_assoc_src, FileId.fromInt(1), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expect(sink.error_count >= 1);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        non_assoc_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
}

test "test_parse_leading_stmt_attribute_before_comptime_constructs" {
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();
    var sink = diagnostic.DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    const source =
        "fn annotated_comptime_stmts(slot: &mut i32) -> i32 {\n" ++
        "    @must_use comptime fn helper() -> i32 { return 7; }\n" ++
        "    @unroll comptime for idx in 0..2 {\n" ++
        "        let step = idx;\n" ++
        "    }\n" ++
        "    @check_block comptime {\n" ++
        "        @compile_assert(helper() == 7, \"ok\");\n" ++
        "    };\n" ++
        "    *slot = 20;\n" ++
        "    let local_cb = @local |delta: i32| delta + *slot;\n" ++
        "    return local_cb(helper());\n" ++
        "}\n";

    _ = try parseSource(source, FileId.fromInt(2), &token_buf, &cst_arena, &ast_arena, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        source,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
}

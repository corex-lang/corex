//! Fault-Tolerant Incremental Parser & Lossless CST-to-AST Lowerer
//!
//! Implements the explicit-stack `LL(k)` recursive-descent and 15-tier Pratt precedence-climbing
//! parser for the CoreX v1.0 surface grammar (`DR-03` Sections 5.3–5.5, `DR-21` Section 3.2 & `DR-22`
//! Sections 3.2–3.3), producing a pre-order `LosslessCstArena` and lowered Structure-of-Arrays
//! `AstArena` in a single pass.
//!
//! Enforces `MAX_PARSE_DEPTH` (`512`, `E0203`), $O(1)$ 128-bit `TokenSet128` anchor synchronization
//! (`E0201`, `E0202`), cross-namespace casing recovery with in-place `W0201` autofixes, `DR-22`
//! syntax canonicalization diagnostics (`E0219`–`E0228`), mid-keystroke IDE completion nodes
//! (`incomplete_member_access`, `incomplete_call`), and $O(K)$ top-level item incremental re-parsing
//! (`reparseIncremental`, `DR-12` Sections 1–2).

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
const ExternVisibility = syntax_arenas.ExternVisibility;
const ExternBlockFlags = syntax_arenas.ExternBlockFlags;
const ExternStaticFlags = syntax_arenas.ExternStaticFlags;
const MAX_PARSE_DEPTH: u32 = @intCast(syntax_arenas.MAX_PARSE_DEPTH);

const IdentifierCase = lexer.IdentifierCase;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const SuggestedFix = diagnostic.SuggestedFix;
const TextEdit = diagnostic.TextEdit;

// ---------------------------------------- TYPES ----------------------------------------

// --------------------- Token Sets & Edits ---------------------

/// 128-bit bitset indexing all 120 `TokenKind` variants (`0..119`) for $O(1)$ membership queries.
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
    /// When `true`, includes top-level `test` and `bench` declarations in `root`'s AST item slice.
    is_including_tests: bool = true,
};

/// Pratt infix binding power pair `(left_bp, right_bp)` and non-associativity flag (`DR-03` Section 5.3).
const InfixBindingPower = struct {
    /// Left binding power checked against `min_bp` before consuming the operator.
    left_bp: u8,
    /// Right binding power passed as `min_bp` when parsing the right-hand operand.
    right_bp: u8,
    /// `true` for relational (`==`, `!=`, `<`, `<=`, `>`, `>=`), `is`, and range (`..`, `..=`) operators.
    is_non_associative: bool = false,
};

/// Controls whether `parseTypeWithMode` consumes trailing `is Pattern` / `where Expr` refinements.
const TypeRefinementMode = enum(u8) {
    /// Do not consume trailing `is` or `where` (used after `as` and inside `type` / `where` headers).
    none = 0,
    /// Consume trailing `is Pattern` only, leaving `where` for item-level `WhereClause`s.
    is_only = 1,
    /// Consume trailing `is Pattern` or `where Expr` into a `.refined_type` CST node.
    all = 2,
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

/// Contiguous outer `.attribute` CST range attached to a parsed declaration header.
const ParsedAttrSlice = struct {
    /// Starting `CstNodeIndex` of the first `.attribute` CST node (`CstNodeIndex.none.asInt()` when `attr_len == 0`).
    attr_start: u32 = std.math.maxInt(u32),
    /// Total number of `.attribute` CST subtrees parsed on the declaration header.
    attr_len: u32 = 0,
};

/// Borrowed structural view over an inline package `use "<spec>" as <alias>;` item (`DR-11` §2.1).
pub const InlineUseDeclView = struct {
    /// AST `.use_decl` node index (`NodeIndex.none` when extracted directly from CST).
    ast_node: NodeIndex = .none,
    /// Enclosing `.use_item` CST node index.
    item_cst: CstNodeIndex = .none,
    /// `.string_lit` token carrying the quoted package specifier.
    spec_token: TokenIndex,
    /// Unquoted dependency specifier slice (`<pkg>@<req>`, `https://…`, `git+…`, `./…`).
    unquoted_spec: []const u8,
    /// Identifier token carrying the `<snake_alias>` package binding (`TokenIndex.none` on missing alias).
    alias_token: TokenIndex,
    /// Borrowed `<snake_alias>` identifier slice (`""` when `alias_token` is missing).
    alias_slice: []const u8,
    /// Byte span of `spec_token`.
    spec_span: Span,
    /// Byte span of `alias_token` (or `spec_span` when `alias_token` is missing).
    alias_span: Span,
    /// Byte span covering the full `.use_item` declaration.
    decl_span: Span,
    /// `true` when the `.use_item` carries a `pub` visibility modifier.
    is_pub: bool = false,
};

/// Retired `DR-22` parameter or call-site mode identifier classified via $O(1)$ static lookup (`E0221`).
const RetiredParamModeKind = enum(u8) {
    /// Retired `inout` exclusive borrow convention (`&mut`).
    inout,
    /// Retired leading `out` out-parameter convention (`&out`).
    out,
    /// Retired `ref` / `ref mut` borrow convention (`&` / `&mut`).
    ref,
    /// Retired `set` out-parameter convention (`&out`).
    set,
    /// Retired `sink` ownership transfer convention (`own`).
    sink,
    /// Retired post-colon `yielded` convention (`&mut`).
    yielded,
};

// --------------------------------------- CONSTS ----------------------------------------

/// Hard upper bound on non-mutating `LL(k)` token lookahead steps (`DR-21` Section 1.5).
pub const MAX_TYPE_LOOKAHEAD: usize = 64;

/// Maximum byte length of an unquoted inline `use "<spec>" as <alias>;` package specifier.
pub const MAX_INLINE_USE_SPEC_BYTES: usize = 512;

/// Reserved identifiers forbidden as inline package import aliases (`E0013`, `DR-11` §2.1).
pub const RESERVED_INLINE_USE_ALIAS_MAP = std.StaticStringMap(void).initComptime(.{
    .{ "Self", {} },
    .{ "_", {} },
    .{ "core", {} },
    .{ "cx", {} },
    .{ "pkg", {} },
    .{ "self", {} },
    .{ "std", {} },
    .{ "super", {} },
});

/// Canonical C ABI primitive type alias identifiers exempted from `W0201` `PascalCase` checks (`DR-10` §2.1).
pub const CANONICAL_C_TYPE_ALIASES = std.StaticStringMap(void).initComptime(.{
    .{ "c_char", {} },
    .{ "c_int", {} },
    .{ "c_long", {} },
    .{ "c_longdouble", {} },
    .{ "c_longlong", {} },
    .{ "c_schar", {} },
    .{ "c_short", {} },
    .{ "c_uchar", {} },
    .{ "c_uint", {} },
    .{ "c_ulong", {} },
    .{ "c_ulonglong", {} },
    .{ "c_ushort", {} },
    .{ "c_void", {} },
});

/// $O(1)$ static lookup map of retired `DR-22` parameter and call-site mode identifiers (`E0221`).
const RETIRED_PARAM_MODE_MAP = std.StaticStringMap(RetiredParamModeKind).initComptime(.{
    .{ "inout", .inout },
    .{ "out", .out },
    .{ "ref", .ref },
    .{ "set", .set },
    .{ "sink", .sink },
    .{ "yielded", .yielded },
});

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
    .kw_subscript,
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
    .kw_yield,
    .kw_unreachable,
    .kw_for,
    .kw_while,
    .kw_loop,
    .kw_with,
    .kw_if,
    .kw_match,
    .kw_comptime,
});
/// Tokens that can legally begin a `Type` expression (`DR-22` Section 3.3).
pub const TYPE_STARTER_SET: TokenSet128 = TokenSet128.initMany(&.{
    .prim_type,
    .kw_self_type,
    .amp,
    .star,
    .kw_own,
    .hash_soa,
    .tilde,
    .lbracket,
    .lparen,
    .pipe,
    .pipepipe,
    .at,
    .kw_async,
    .kw_unsafe,
    .kw_extern,
    .kw_fn,
    .ident,
    .type_ident,
    .const_ident,
});
/// Tokens (excluding `.lbrace`) that can begin a prefix or primary expression (`DR-22` Section 3.2).
pub const EXPR_STARTER_NO_LBRACE_SET: TokenSet128 = TokenSet128.initMany(&.{
    .minus,
    .minus_percent,
    .bang,
    .kw_not,
    .tilde,
    .star,
    .amp,
    .kw_own,
    .dotdot,
    .dotdoteq,
    .int_lit,
    .float_lit,
    .string_lit,
    .char_lit,
    .byte_lit,
    .byte_string_lit,
    .kw_true,
    .kw_false,
    .dollar,
    .underscore,
    .ident,
    .type_ident,
    .const_ident,
    .kw_self_val,
    .kw_self_type,
    .kw_context,
    .prim_type,
    .at,
    .dot,
    .lparen,
    .lbracket,
    .pipe,
    .pipepipe,
    .kw_if,
    .kw_match,
    .kw_for,
    .kw_while,
    .kw_loop,
    .kw_with,
    .kw_return,
    .kw_break,
    .kw_continue,
    .kw_unreachable,
    .kw_comptime,
    .kw_unsafe,
    .kw_async,
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
    .kw_subscript,
    .kw_async,
    .kw_unsafe,
    .kw_extern,
    .kw_fn,
    .eof,
});
/// Stop-before anchor set for `extern` block member declaration loops.
pub const EXTERN_MEMBER_STOP_SET: TokenSet128 = TokenSet128.initMany(&.{
    .rbrace,
    .at,
    .kw_pub,
    .kw_const,
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
    .eq,
    .lbrace,
    .semi,
    .slash,
    .star,
    .dotdotdot,
    .kw_var,
    .kw_comptime,
    .kw_mut,
    .kw_own,
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
    .dotdot,
    .dotdoteq,
    .minus,
    .amp,
    .kw_var,
    .kw_mut,
    .kw_own,
    .type_ident,
    .const_ident,
    .ident,
    .int_lit,
    .float_lit,
    .string_lit,
    .char_lit,
    .byte_lit,
    .byte_string_lit,
    .kw_true,
    .kw_false,
    .lparen,
    .lbracket,
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
    .kw_orelse,
    .kw_catch,
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

/// Returns `true` if `kind` is a `snake_case` identifier or `.kw_async` module path segment.
inline fn isIdentOrModuleSegment(kind: TokenKind) bool {
    return kind == .ident or kind == .kw_async;
}

/// Returns `true` if `kind` is one of the 50 language keywords (`0..49`).
inline fn isKeywordKind(kind: TokenKind) bool {
    return @backingInt(kind) <= @backingInt(TokenKind.kw_self_type);
}

/// Returns `true` if `kind` can begin an expression under the active `is_struct_lit_allowed` guard.
inline fn isExprStart(kind: TokenKind, is_struct_lit_allowed: bool) bool {
    if (kind == .lbrace) return is_struct_lit_allowed;
    return EXPR_STARTER_NO_LBRACE_SET.contains(kind);
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

/// Returns `true` if `kind` is a scalar or byte literal (`int`, `float`, `string`, `char`, `byte`, `bool`).
inline fn isLiteralToken(kind: TokenKind) bool {
    return switch (kind) {
        .int_lit,
        .float_lit,
        .string_lit,
        .char_lit,
        .byte_lit,
        .byte_string_lit,
        .kw_true,
        .kw_false,
        => true,
        else => false,
    };
}

/// Returns `true` if `byte_val` can continue an ASCII identifier (`[A-Za-z0-9_]`).
inline fn isAsciiIdentContinue(byte_val: u8) bool {
    return std.ascii.isAlphanumeric(byte_val) or byte_val == '_';
}

/// Extracts the inner unquoted slice of a plain single-line `.string_lit` lexeme (`null` on multiline or interpolated).
fn extractSingleLineUnquotedSpec(lexeme: []const u8) ?[]const u8 {
    if (lexeme.len < 2) return null;
    if (std.mem.startsWith(u8, lexeme, "\"\"\"")) return null;
    if (lexeme[0] == 'r') {
        var hash_count: usize = 0;
        var idx: usize = 1;
        while (idx < lexeme.len and lexeme[idx] == '#') : (idx += 1) {
            hash_count += 1;
        }
        if (idx >= lexeme.len or lexeme[idx] != '"') return null;
        if (std.mem.startsWith(u8, lexeme[idx..], "\"\"\"")) return null;
        const suffix_len = 1 + hash_count;
        if (lexeme.len < idx + 1 + suffix_len) return null;
        const close_pos = lexeme.len - suffix_len;
        if (lexeme[close_pos] != '"') return null;
        const inner_raw = lexeme[idx + 1 .. close_pos];
        if (std.mem.indexOfAny(u8, inner_raw, "\r\n") != null) return null;
        return inner_raw;
    }
    if (lexeme[0] != '"' or lexeme[lexeme.len - 1] != '"') return null;
    const inner_slice = lexeme[1 .. lexeme.len - 1];
    var i: usize = 0;
    while (i < inner_slice.len) : (i += 1) {
        const byte_val = inner_slice[i];
        if (byte_val == '\n' or byte_val == '\r' or byte_val == 0) return null;
        if (byte_val == '\\') {
            if (i + 1 >= inner_slice.len) return null;
            i += 1;
            continue;
        }
        if (byte_val == '{' or byte_val == '}') return null;
    }
    return inner_slice;
}

/// Validates syntactic well-formedness of an unquoted inline `use "<spec>"` package specifier (`DR-11` §1.2).
pub fn isValidInlineUseSpec(raw_spec: []const u8) bool {
    if (raw_spec.len == 0 or raw_spec.len > MAX_INLINE_USE_SPEC_BYTES) return false;
    if (raw_spec[0] == ' ' or raw_spec[raw_spec.len - 1] == ' ') return false;
    for (raw_spec) |byte_val| {
        if (byte_val < 0x20 or byte_val == 0x7F or byte_val == '\\') return false;
    }

    // [1] Local relative directory paths (`./…` or `../…`):
    if (std.mem.startsWith(u8, raw_spec, "./") or std.mem.startsWith(u8, raw_spec, "../")) {
        if (std.mem.indexOfScalar(u8, raw_spec, ' ') != null) return false;
        return (if (std.mem.startsWith(u8, raw_spec, "./")) raw_spec[2..] else raw_spec[3..]).len > 0;
    }

    // [2] Shorthand GitHub / GitLab repository specifiers (`github.com/<org>/<repo>[@<rev>]`):
    if (std.mem.startsWith(u8, raw_spec, "github.com/") or std.mem.startsWith(u8, raw_spec, "gitlab.com/")) {
        if (std.mem.indexOfScalar(u8, raw_spec, ' ') != null) return false;
        const after_host = raw_spec["github.com/".len..];
        const repo_path = if (std.mem.lastIndexOfAny(u8, after_host, "@#")) |sep_pos| blk: {
            if (sep_pos == 0 or sep_pos + 1 >= after_host.len) return false;
            break :blk after_host[0..sep_pos];
        } else after_host;
        const slash_pos = std.mem.indexOfScalar(u8, repo_path, '/') orelse return false;
        if (slash_pos == 0 or slash_pos + 1 >= repo_path.len) return false;
        return repo_path[repo_path.len - 1] != '/' and std.mem.indexOf(u8, repo_path, "//") == null;
    }

    // [3] Explicit Git / HTTPS URLs (`https://…`, `git+https://…`, `git+ssh://…`, `git+file://…`):
    const url_schemes = [_][]const u8{
        "https://",
        "git+https://",
        "git+ssh://",
        "git+file://",
    };
    for (url_schemes) |scheme| {
        if (std.mem.startsWith(u8, raw_spec, scheme)) {
            if (std.mem.indexOfScalar(u8, raw_spec, ' ') != null or raw_spec[scheme.len..].len == 0) return false;
            if (std.mem.lastIndexOfAny(u8, raw_spec, "@#")) |sep_idx| {
                if (!(std.mem.startsWith(u8, raw_spec, "git+ssh://git@") and sep_idx < 16) and sep_idx >= scheme.len) {
                    if (sep_idx == scheme.len or sep_idx + 1 >= raw_spec.len) return false;
                }
            }
            return true;
        }
    }

    // [4] Registry specifier (`[registry:]<kebab>@<non_empty_ver>`):
    const stripped = if (std.mem.startsWith(u8, raw_spec, "registry:")) raw_spec[9..] else raw_spec;
    const at_pos = std.mem.indexOfScalar(u8, stripped, '@') orelse return false;
    const pkg_part = stripped[0..at_pos];
    if (std.mem.trim(u8, stripped[at_pos + 1 ..], " ").len == 0) return false;
    if (pkg_part.len == 0 or pkg_part.len > 64) return false;
    if (RESERVED_INLINE_USE_ALIAS_MAP.has(pkg_part) or lexer.KEYWORD_OR_PRIM_MAP.has(pkg_part)) return false;
    if (!std.ascii.isLower(pkg_part[0]) or pkg_part[pkg_part.len - 1] == '-') return false;

    var snake_buf: [64]u8 = undefined;
    var has_prev_dash = false;
    for (pkg_part, 0..) |pkg_ch, i| {
        if (pkg_ch == '-') {
            if (has_prev_dash) return false;
            has_prev_dash = true;
            snake_buf[i] = '_';
        } else if (std.ascii.isLower(pkg_ch) or std.ascii.isDigit(pkg_ch)) {
            has_prev_dash = false;
            snake_buf[i] = pkg_ch;
        } else {
            return false;
        }
    }
    const snake_view = snake_buf[0..pkg_part.len];
    return !RESERVED_INLINE_USE_ALIAS_MAP.has(snake_view) and !lexer.KEYWORD_OR_PRIM_MAP.has(snake_view);
}

/// Returns `true` if `kind` is an unambiguous place/value starter after contextual `&out` or `&raw`.
inline fn isUnambiguousAddrOperandStart(kind: TokenKind, next_after_lparen: TokenKind) bool {
    return switch (kind) {
        .ident, .type_ident, .kw_self_val, .star => true,
        .lparen => next_after_lparen != .rparen,
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
        .block,
        .if_expr,
        .match_expr,
        .for_stmt,
        .while_stmt,
        .loop_expr,
        .with_expr,
        => true,
        else => false,
    };
}

/// Returns the right binding power (`28`) for unary prefix operators (`DR-22` Section 3.2 Tier 14).
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
        => 28,
        else => null,
    };
}

/// Returns the Pratt `(left_bp, right_bp, is_non_associative)` descriptor for `kind` (`DR-22` Section 3.2).
fn getInfixBindingPower(kind: TokenKind) ?InfixBindingPower {
    return switch (kind) {
        // Tier 13 – Explicit Type Cast (`as Type`):
        .kw_as => .{ .left_bp = 26, .right_bp = 27 },
        // Tier 12 – Multiplicative (`*`, `/`, `%`, `*%`, `*|`):
        .star, .slash, .percent, .star_percent, .star_pipe => .{ .left_bp = 24, .right_bp = 25 },
        // Tier 11 – Additive (`+`, `-`, `+%`, `-%`, `+|`, `-|`):
        .plus, .minus, .plus_percent, .minus_percent, .plus_pipe, .minus_pipe => .{
            .left_bp = 22,
            .right_bp = 23,
        },
        // Tier 10 – Bitwise Shift (`<<`, `>>`):
        .shl, .shr => .{ .left_bp = 20, .right_bp = 21 },
        // Tier 9 – Bitwise AND (`&`):
        .amp => .{ .left_bp = 18, .right_bp = 19 },
        // Tier 8 – Bitwise XOR (`^`):
        .caret => .{ .left_bp = 16, .right_bp = 17 },
        // Tier 7 – Bitwise OR (`|`):
        .pipe => .{ .left_bp = 14, .right_bp = 15 },
        // Tier 6 – Range Constructors (`..`, `..=`), Non-Associative:
        .dotdot, .dotdoteq => .{ .left_bp = 12, .right_bp = 13, .is_non_associative = true },
        // Tier 5 – Data Transformation Pipeline (`|>`, Left-to-Right):
        .pipe_gt => .{ .left_bp = 10, .right_bp = 11 },
        // Tier 4 – Inline Option / Error Fallback (`orelse`, `catch`, Right-to-Left):
        .kw_orelse, .kw_catch => .{ .left_bp = 9, .right_bp = 8 },
        // Tier 3 – Relational, Equality & Pattern Test (`==`..`>=`, `is`, `is not`), Non-Associative:
        .eqeq, .bang_eq, .lt, .le, .gt, .ge, .kw_is => .{
            .left_bp = 6,
            .right_bp = 7,
            .is_non_associative = true,
        },
        // Tier 2 – Logical Short-Circuit AND (`and`):
        .kw_and => .{ .left_bp = 4, .right_bp = 5 },
        // Tier 1 – Logical Short-Circuit OR (`or`):
        .kw_or => .{ .left_bp = 2, .right_bp = 3 },
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
        if ((flags.has_lexer_error and !isIdentifierKind(kind_slice[i])) or flags.is_synthesized) {
            return false;
        }
    }
    return true;
}

/// Re-emits lexer-originated `W0201` warnings for spliced identifier tokens carrying `has_lexer_error`.
fn replayLexerCasingWarnings(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    diagnostic_sink: ?*DiagnosticSink,
    interner: ?*StringInterner,
) !void {
    const sink = diagnostic_sink orelse return;
    const total_tokens = token_buffer.countTokens();
    const kind_slice = token_buffer.tokens.items(.kind);
    const flag_slice = token_buffer.tokens.items(.flags);

    var tok_i: usize = 0;
    while (tok_i < total_tokens) : (tok_i += 1) {
        if (!flag_slice[tok_i].has_lexer_error or !isIdentifierKind(kind_slice[tok_i])) continue;
        const tok_id = TokenIndex.fromInt(@intCast(tok_i));
        const record = token_buffer.getToken(tok_id);
        const start_off: usize = record.byte_offset;
        const end_off: usize = @min(start_off + @as(usize, record.byte_len), source.len);
        const lexeme = source[start_off..end_off];
        const classification = lexer.classifyIdentifierOrKeyword(lexeme);
        if (!classification.has_case_violation) continue;

        const ident_span = Span.init(file_id, @intCast(start_off), @intCast(end_off));
        const label_msg = switch (classification.expected_case) {
            .snake_case => "value/function identifiers must use `snake_case`",
            .pascal_case => "type/variant identifiers must use `PascalCase` without underscores",
            .screaming_snake_case => "constant identifiers must use `SCREAMING_SNAKE_CASE`",
            .reserved_or_wildcard => "identifier does not follow canonical CoreX casing",
        };
        const primary_labels = [_]LabeledSpan{.{
            .span = ident_span,
            .label = label_msg,
            .style = .primary,
        }};

        if (interner) |str_interner| {
            const converted = switch (classification.expected_case) {
                .snake_case => try lexer.toSnakeCase(sink.arena.asAllocator(), lexeme),
                .pascal_case => try lexer.toPascalCase(sink.arena.asAllocator(), lexeme),
                .screaming_snake_case => try lexer.toScreamingSnakeCase(sink.arena.asAllocator(), lexeme),
                .reserved_or_wildcard => lexeme,
            };
            const fix_edits = [_]TextEdit{.{
                .file_id = file_id,
                .start_byte = ident_span.start_byte,
                .end_byte = ident_span.end_byte,
                .replacement_id = try str_interner.intern(converted),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "convert identifier to canonical CoreX casing",
                .applicability = .machine_applicable,
                .priority = .lint_idiom,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .w0201_non_canonical_identifier_case,
                .severity = .warning,
                .primary_span = ident_span,
                .message = "identifier does not follow canonical CoreX casing",
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
        } else {
            try sink.emit(.{
                .code = .w0201_non_canonical_identifier_case,
                .severity = .warning,
                .primary_span = ident_span,
                .message = "identifier does not follow canonical CoreX casing",
                .labels = &primary_labels,
            });
        }
    }
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
    /// `true` while parsing destructuring place targets (`_ = …`, `(a, _) = …`, `Point { x: _ } = …`).
    is_in_lhs_place: bool = false,
    /// `true` while parsing the top-level condition header of an `if` or `while` expression.
    is_in_cond_header: bool = false,
    /// `true` while parsing inside a declaration or member annotated with `@allow(non_canonical_case)`.
    is_allowing_non_canonical_case: bool = false,
    /// `true` while executing `Parser.parse()`, gating scratch casing-exemption sets freed on exit.
    is_in_full_parse: bool = false,
    /// Nominal type identifiers declared under `@allow(non_canonical_case)` in the active `parse()` pass.
    allowed_non_canonical_types: std.StringHashMapUnmanaged(void) = .empty,
    /// Member, symbol, and foreign `extern` identifiers exempted from `W0201` in the active `parse()` pass.
    allowed_non_canonical_members: std.StringHashMapUnmanaged(void) = .empty,

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
        self.is_in_full_parse = true;
        defer self.clearAllowedNonCanonicalNames();
        try self.precollectAllowedNonCanonicalNames();

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
            const parsed_item = try self.parseItem();
            const parsed_tag = self.ast.getNode(parsed_item).tag;
            if (self.options.is_including_tests or (parsed_tag != .test_decl and parsed_tag != .bench_decl)) {
                try item_indices.append(self.ast.allocator, parsed_item.asInt());
            }

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

    /// Advances `start_raw` past any carrier tokens, returning the index of the next non-carrier token.
    inline fn skipCarrierRawIndex(self: *const Parser, start_raw: usize) usize {
        const total_tokens = self.token_buffer.countTokens();
        var scan_idx = start_raw;
        while (scan_idx < total_tokens) : (scan_idx += 1) {
            if (!isCarrierToken(self.token_buffer.getToken(TokenIndex.fromInt(@intCast(scan_idx))))) {
                return scan_idx;
            }
        }
        return total_tokens;
    }

    /// Advances `start_raw` by `count` non-carrier tokens in $O(\text{count})$ raw steps.
    inline fn advanceNonCarrierRawIndex(self: *const Parser, start_raw: usize, count: usize) usize {
        const total_tokens = self.token_buffer.countTokens();
        var cur_raw = self.skipCarrierRawIndex(start_raw);
        var rem = count;
        while (rem > 0 and cur_raw < total_tokens) : (rem -= 1) {
            cur_raw = self.skipCarrierRawIndex(cur_raw + 1);
        }
        return cur_raw;
    }

    /// Returns the non-carrier `TokenKind` at `raw_idx` (`.eof` when out of bounds).
    inline fn rawTokenKindAt(self: *const Parser, raw_idx: usize) TokenKind {
        const cur_raw = self.skipCarrierRawIndex(raw_idx);
        if (cur_raw >= self.token_buffer.countTokens()) return .eof;
        return self.token_buffer.getToken(TokenIndex.fromInt(@intCast(cur_raw))).kind;
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
        if (record.flags.has_lexer_error and isIdentifierKind(record.kind)) {
            const lexeme = self.getTokenLexeme(token_id);
            if (self.is_allowing_non_canonical_case or
                self.allowed_non_canonical_types.contains(lexeme) or
                self.allowed_non_canonical_members.contains(lexeme))
            {
                self.suppressCasingWarningAtToken(token_id);
            }
        }
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

        // Shift `ast_to_cst` origins and CST-indexed `attr_start` fields inside the LHS subtree:
        var ast_idx: usize = lhs_ast_start;
        while (ast_idx < self.ast.ast_to_cst.items.len) : (ast_idx += 1) {
            const origin = self.ast.ast_to_cst.items[ast_idx];
            if (!origin.isNone() and origin.asInt() >= insert_idx) {
                self.ast.ast_to_cst.items[ast_idx] = CstNodeIndex.fromInt(origin.asInt() + 1);
            }
            const node = self.ast.nodes.get(ast_idx);
            if (node.tag == .extern_block_decl and node.lhs.tag == .extra) {
                const base: usize = node.lhs.payload;
                if (base + 3 < self.ast.extra_data.items.len and
                    self.ast.extra_data.items[base + 3] > 0 and
                    self.ast.extra_data.items[base + 2] >= insert_idx)
                {
                    self.ast.extra_data.items[base + 2] += 1;
                }
            } else if (node.tag == .extern_static_decl and node.rhs.tag == .extra) {
                const base: usize = node.rhs.payload;
                if (base + 4 < self.ast.extra_data.items.len and
                    self.ast.extra_data.items[base + 4] > 0 and
                    self.ast.extra_data.items[base + 3] >= insert_idx)
                {
                    self.ast.extra_data.items[base + 3] += 1;
                }
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

    /// Emits a parser diagnostic at `primary_span` with an optional `.machine_applicable` `TextEdit`.
    fn emitDiagnosticWithFix(
        self: *Parser,
        code: DiagnosticCode,
        primary_span: Span,
        message: []const u8,
        label_text: []const u8,
        opt_fix_span: ?Span,
        opt_replacement: ?[]const u8,
        opt_fix_message: ?[]const u8,
    ) !void {
        self.cst.has_parse_errors = true;
        const sink = self.diagnostic_sink orelse return;
        const labels = [_]LabeledSpan{.{
            .span = primary_span,
            .label = label_text,
            .style = .primary,
        }};
        var fix_slice: []const SuggestedFix = &.{};
        var local_edit: [1]TextEdit = undefined;
        var local_fix: [1]SuggestedFix = undefined;
        if (opt_fix_span != null and opt_replacement != null and self.interner != null) {
            const fix_span = opt_fix_span.?;
            local_edit[0] = .{
                .file_id = self.file_id,
                .start_byte = fix_span.start_byte,
                .end_byte = fix_span.end_byte,
                .replacement_id = try self.interner.?.intern(opt_replacement.?),
            };
            local_fix[0] = .{
                .message = opt_fix_message orelse "replace with canonical CoreX syntax",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &local_edit,
            };
            fix_slice = &local_fix;
        }
        try sink.emit(.{
            .code = code,
            .severity = .err,
            .primary_span = primary_span,
            .message = message,
            .labels = &labels,
            .suggestions = fix_slice,
        });
    }

    /// Emits `E0219` (`e0219_retired_logical_or`) for an infix `||` token with a spacing-safe `or` autofix.
    fn emitRetiredLogicalOr(self: *Parser, op_tok: TokenIndex) !void {
        const op_span = self.getTokenSpan(op_tok);
        const needs_left_space = op_span.start_byte > 0 and
            op_span.start_byte <= self.source.len and
            isAsciiIdentContinue(self.source[op_span.start_byte - 1]);
        const needs_right_space = op_span.end_byte < self.source.len and
            isAsciiIdentContinue(self.source[op_span.end_byte]);
        const replacement: []const u8 = if (needs_left_space and needs_right_space)
            " or "
        else if (needs_left_space)
            " or"
        else if (needs_right_space)
            "or "
        else
            "or";
        try self.emitDiagnosticWithFix(
            .e0219_retired_logical_or,
            op_span,
            "infix `||` logical OR operator has been retired; use `or` instead (`||` is reserved for 0-argument closures)",
            "retired logical `||`; write `or` here",
            op_span,
            replacement,
            "replace `||` with `or`",
        );
    }

    /// Emits `E0215` (`e0215_invalid_walrus_position`) for an unparenthesized or non-header `:=` binding.
    fn emitWalrusPositionError(
        self: *Parser,
        err_span: Span,
        label_text: []const u8,
        help_note: []const u8,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const labels = [_]LabeledSpan{.{
            .span = err_span,
            .label = label_text,
            .style = .primary,
        }};
        const notes = [_][]const u8{help_note};
        try sink.emit(.{
            .code = .e0215_invalid_walrus_position,
            .severity = .err,
            .primary_span = err_span,
            .message = "condition `:=` binding is only valid inside a parenthesized positive `if` or `while` header",
            .labels = &labels,
            .notes = &notes,
        });
    }

    /// Parses retired `if let` / `while let`, emitting `E0216` with a `.machine_applicable` `is` rewrite.
    fn parseRetiredIfWhileLet(
        self: *Parser,
        cond_cst: CstNodeIndex,
        keyword_label: []const u8,
        has_error: *bool,
    ) anyerror!NodeIndex {
        const let_tok = try self.consumeLeaf(.token_leaf, .{});
        const let_span = self.getTokenSpan(let_tok);

        const pat_start_tok = self.peekTokenIndexNth(0);
        const saved_cond_header = self.is_in_cond_header;
        self.is_in_cond_header = false;
        const pat_node = blk_pat: {
            defer self.is_in_cond_header = saved_cond_header;
            break :blk_pat try self.parsePatternWithOptions(false, true);
        };
        const pat_end_tok = if (self.cursor > 0)
            TokenIndex.fromInt(self.cursor - 1)
        else
            pat_start_tok;

        var has_inner_err = false;
        _ = try self.expectToken(
            .eq,
            &has_inner_err,
            "expected `=` after retired `let` condition pattern",
            "expected `=` here",
        );

        const rhs_start_tok = self.peekTokenIndexNth(0);
        const rhs_expr = blk_rhs: {
            self.is_in_cond_header = false;
            defer self.is_in_cond_header = saved_cond_header;
            break :blk_rhs try self.parseExprBp(6, false);
        };
        const rhs_end_tok = if (self.cursor > 0)
            TokenIndex.fromInt(self.cursor - 1)
        else
            rhs_start_tok;

        const pat_start_span = self.getTokenSpan(pat_start_tok);
        const pat_end_span = self.getTokenSpan(pat_end_tok);
        const rhs_start_span = self.getTokenSpan(rhs_start_tok);
        const rhs_end_span = self.getTokenSpan(rhs_end_tok);
        const replace_end = @max(let_span.end_byte, rhs_end_span.end_byte);
        const replace_span = Span.init(self.file_id, let_span.start_byte, replace_end);

        if (self.diagnostic_sink) |sink| {
            var fix_slice: []const SuggestedFix = &.{};
            var local_edit: [1]TextEdit = undefined;
            var local_fix: [1]SuggestedFix = undefined;

            if (!has_inner_err and
                self.interner != null and
                pat_start_span.start_byte <= pat_end_span.end_byte and
                pat_end_span.end_byte <= self.source.len and
                rhs_start_span.start_byte <= rhs_end_span.end_byte and
                rhs_end_span.end_byte <= self.source.len)
            {
                const str_interner = self.interner.?;
                const pat_raw = self.source[pat_start_span.start_byte..pat_end_span.end_byte];
                const rhs_raw = self.source[rhs_start_span.start_byte..rhs_end_span.end_byte];
                const pat_text = std.mem.trim(u8, pat_raw, " \t\r\n");
                const rhs_text = std.mem.trim(u8, rhs_raw, " \t\r\n");
                if (pat_text.len > 0 and rhs_text.len > 0) {
                    const needs_pat_parens = std.mem.indexOfScalar(u8, pat_text, '{') != null or
                        std.mem.indexOfScalar(u8, pat_text, '|') != null;
                    const rhs_tag = self.ast.getNode(rhs_expr).tag;
                    const needs_rhs_parens = rhs_tag == .binary_expr or rhs_tag == .is_expr;
                    const arena_alloc = sink.arena.asAllocator();
                    const rewritten = if (needs_rhs_parens and needs_pat_parens)
                        try std.fmt.allocPrint(arena_alloc, "({s}) is ({s})", .{ rhs_text, pat_text })
                    else if (needs_rhs_parens)
                        try std.fmt.allocPrint(arena_alloc, "({s}) is {s}", .{ rhs_text, pat_text })
                    else if (needs_pat_parens)
                        try std.fmt.allocPrint(arena_alloc, "{s} is ({s})", .{ rhs_text, pat_text })
                    else
                        try std.fmt.allocPrint(arena_alloc, "{s} is {s}", .{ rhs_text, pat_text });

                    local_edit[0] = .{
                        .file_id = self.file_id,
                        .start_byte = replace_span.start_byte,
                        .end_byte = replace_span.end_byte,
                        .replacement_id = try str_interner.intern(rewritten),
                    };
                    local_fix[0] = .{
                        .message = "rewrite retired `let` condition using `is` pattern matching",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = &local_edit,
                    };
                    fix_slice = &local_fix;
                }
            }

            const labels = [_]LabeledSpan{.{
                .span = replace_span,
                .label = "retired conditional `let` syntax; write `<scrutinee> is <pattern>` instead",
                .style = .primary,
            }};
            const headline = if (std.mem.eql(u8, keyword_label, "while"))
                "`while let` has been retired; use `while expr is Pattern` instead"
            else
                "`if let` has been retired; use `if expr is Pattern` instead";
            try sink.emit(.{
                .code = .e0216_retired_if_while_let,
                .severity = .err,
                .primary_span = replace_span,
                .message = headline,
                .labels = &labels,
                .suggestions = fix_slice,
            });
        }

        has_error.* = true;
        var cond_expr = try self.ast.appendNodeWithCst(.{
            .tag = .is_expr,
            .main_token = let_tok,
            .lhs = PackedOperand.initNode(rhs_expr),
            .rhs = PackedOperand.initNode(pat_node),
        }, cond_cst);

        // Consume any trailing `and` / `or` guard conjuncts in the `if`/`while` condition header:
        self.is_in_cond_header = true;
        defer self.is_in_cond_header = saved_cond_header;
        while (self.peekKind() == .kw_and or
            self.peekKind() == .kw_or or
            self.peekKind() == .pipepipe)
        {
            const logic_tok = try self.consumeLeaf(.token_leaf, .{});
            const logic_kind = self.token_buffer.getToken(logic_tok).kind;
            if (logic_kind == .pipepipe) {
                try self.emitRetiredLogicalOr(logic_tok);
            }
            const right_bp: u8 = if (logic_kind == .kw_and) 6 else 4;
            const guard_rhs = try self.parseExprBp(right_bp, false);
            cond_expr = try self.ast.appendNodeWithCst(.{
                .tag = .binary_expr,
                .main_token = logic_tok,
                .lhs = PackedOperand.initNode(cond_expr),
                .rhs = PackedOperand.initNode(guard_rhs),
            }, cond_cst);
        }
        return cond_expr;
    }

    /// Consumes an identifier, recovering cross-namespace and hybrid casing violations via `W0201`.
    fn expectIdentifierWithCasing(
        self: *Parser,
        expected_kind: TokenKind,
        expected_case: IdentifierCase,
        has_error: *bool,
        missing_msg: []const u8,
    ) !TokenIndex {
        const cur_rec = self.peekNth(0);
        if (isIdentifierKind(cur_rec.kind)) {
            const preview_lexeme = self.peekLexemeNth(0);
            const is_exempt_type = expected_case == .pascal_case and
                (CANONICAL_C_TYPE_ALIASES.has(preview_lexeme) or
                    self.allowed_non_canonical_types.contains(preview_lexeme));
            const is_exempt_member = expected_case == .snake_case and
                self.allowed_non_canonical_members.contains(preview_lexeme);
            if (self.is_allowing_non_canonical_case or is_exempt_type or is_exempt_member) {
                const tok_id = try self.consumeLeaf(.token_leaf, .{});
                self.suppressCasingWarningAtToken(tok_id);
                if (self.is_allowing_non_canonical_case and self.is_in_full_parse and preview_lexeme.len > 0) {
                    if (expected_case == .pascal_case) {
                        try self.allowed_non_canonical_types.put(self.ast.allocator, preview_lexeme, {});
                    } else {
                        try self.allowed_non_canonical_members.put(self.ast.allocator, preview_lexeme, {});
                    }
                }
                return tok_id;
            }
        }
        if (cur_rec.kind == expected_kind) {
            const tok_id = try self.consumeLeaf(.token_leaf, .{});
            if (cur_rec.flags.has_lexer_error) {
                try self.emitOrUpdateCasingWarning(tok_id, expected_case);
            }
            return tok_id;
        }
        if (isIdentifierKind(cur_rec.kind)) {
            const tok_id = try self.consumeLeaf(.token_leaf, .{});
            try self.emitOrUpdateCasingWarning(tok_id, expected_case);
            return tok_id;
        }
        has_error.* = true;
        const err_tok = self.peekTokenIndexNth(0);
        try self.emitUnexpectedToken(err_tok, missing_msg, "expected identifier here");
        return err_tok;
    }

    /// Removes any pre-emitted lexer `W0201` casing warning at `token_id` for foreign `extern` or `@allow` symbols.
    fn suppressCasingWarningAtToken(self: *Parser, token_id: TokenIndex) void {
        const sink = self.diagnostic_sink orelse return;
        const ident_span = self.getTokenSpan(token_id);
        var diag_idx: usize = 0;
        while (diag_idx < sink.diagnostics.items.len) {
            const existing_diag = sink.diagnostics.items[diag_idx];
            if (existing_diag.code == .w0201_non_canonical_identifier_case and
                existing_diag.primary_span.file_id == ident_span.file_id and
                existing_diag.primary_span.start_byte == ident_span.start_byte and
                existing_diag.primary_span.end_byte == ident_span.end_byte)
            {
                _ = sink.diagnostics.orderedRemove(diag_idx);
                sink.warning_count -|= 1;
            } else {
                diag_idx += 1;
            }
        }
    }

    /// Consumes a foreign `extern` symbol identifier (`CreateFileW`, `sqlite3_open_v2`, `_errno`) without `W0201`.
    fn expectExternSymbolIdentifier(
        self: *Parser,
        has_error: *bool,
        missing_msg: []const u8,
    ) !TokenIndex {
        if (isIdentifierKind(self.peekKind())) {
            const tok_id = try self.consumeLeaf(.token_leaf, .{});
            self.suppressCasingWarningAtToken(tok_id);
            if (self.is_in_full_parse) {
                const sym_lexeme = self.getTokenLexeme(tok_id);
                if (sym_lexeme.len > 0) {
                    try self.allowed_non_canonical_members.put(self.ast.allocator, sym_lexeme, {});
                }
            }
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

    /// Parses a sequence of `@attr(key: val)` annotations into `self.cst` (`ADR-22E`).
    fn parseAttributes(self: *Parser, has_error: *bool) anyerror!void {
        _ = try self.parseAttributesWithSlice(has_error);
    }

    /// Parses a sequence of `@attr(key: val)` annotations and returns their CST slice descriptor.
    fn parseAttributesWithSlice(self: *Parser, has_error: *bool) anyerror!ParsedAttrSlice {
        var result: ParsedAttrSlice = .{};
        while (self.peekKind() == .at) {
            const attr_cst = try self.startCstNode(.attribute);
            if (result.attr_len == 0) {
                result.attr_start = attr_cst.asInt();
            }
            result.attr_len += 1;
            var has_attr_err = false;
            const at_tok = try self.consumeLeaf(.token_leaf, .{});
            if (isIdentifierKind(self.peekKind()) or isKeywordKind(self.peekKind())) {
                const name_tok = try self.consumeLeaf(.token_leaf, .{});
                if (std.mem.eql(u8, self.getTokenLexeme(name_tok), "noalloc")) {
                    has_attr_err = true;
                    has_error.* = true;
                    const at_span = self.getTokenSpan(at_tok);
                    const name_span = self.getTokenSpan(name_tok);
                    const full_span = Span.init(self.file_id, at_span.start_byte, name_span.end_byte);
                    try self.emitDiagnosticWithFix(
                        .e0225_retired_noalloc_attribute,
                        full_span,
                        "`@noalloc` attribute spelling has been retired; use `@no_alloc` instead",
                        "retired `@noalloc`; write `@no_alloc`",
                        full_span,
                        "@no_alloc",
                        "replace `@noalloc` with `@no_alloc`",
                    );
                }
            } else {
                has_attr_err = true;
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
                        const sep_tok = try self.consumeLeaf(.token_leaf, .{});
                        if (self.token_buffer.getToken(sep_tok).kind == .eq) {
                            has_attr_err = true;
                            has_error.* = true;
                            const eq_span = self.getTokenSpan(sep_tok);
                            try self.emitDiagnosticWithFix(
                                .e0223_retired_attribute_eq,
                                eq_span,
                                "`=` key-value separator inside `@attr(…)` has been retired; use `:` instead",
                                "retired `=` in attribute argument; write `:`",
                                eq_span,
                                ":",
                                "replace `=` with `:`",
                            );
                        }
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
                    &has_attr_err,
                    "expected `)` to close attribute argument list",
                );
                if (has_attr_err) has_error.* = true;
            }
            self.cst.finishNode(attr_cst, .{ .has_error = has_attr_err });
        }
        return result;
    }

    /// Parses optional `Vis = "pub" [ "(" ( "pkg" | "super" ) ")" ]` into `.visibility_modifier` CST (`ADR-22E`).
    fn parseVisibility(self: *Parser, has_error: *bool) anyerror!void {
        _ = try self.parseVisibilityWithLevel(has_error);
    }

    /// Parses optional `Vis` into `.visibility_modifier` CST and returns its decoded `ExternVisibility`.
    fn parseVisibilityWithLevel(self: *Parser, has_error: *bool) anyerror!ExternVisibility {
        if (self.peekKind() != .kw_pub) return .private;
        if (self.peekKindNth(1) != .lparen) {
            _ = try self.consumeLeaf(.visibility_modifier, .{});
            return .public;
        }

        const vis_cst = try self.startCstNode(.visibility_modifier);
        var has_vis_err = false;
        var parsed_vis: ExternVisibility = .public;
        _ = try self.consumeLeaf(.token_leaf, .{});
        const open_paren = try self.consumeLeaf(.token_leaf, .{});
        if (self.peekKind() == .ident and std.mem.eql(u8, self.peekLexemeNth(0), "pkg")) {
            parsed_vis = .pub_pkg;
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else if (self.peekKind() == .ident and std.mem.eql(u8, self.peekLexemeNth(0), "super")) {
            parsed_vis = .pub_super;
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_vis_err = true;
            has_error.* = true;
            const err_tok = self.peekTokenIndexNth(0);
            try self.emitUnexpectedToken(
                err_tok,
                "expected `pkg` or `super` inside `pub(…)` visibility modifier",
                "expected `pkg` or `super` here",
            );
            if (self.peekKind() != .rparen and
                self.peekKind() != .rbrace and
                self.peekKind() != .semi and
                self.peekKind() != .eof)
            {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }
        try self.expectClosingDelimiter(
            .rparen,
            open_paren,
            &has_vis_err,
            "expected `)` to close `pub(…)` visibility modifier",
        );
        if (has_vis_err) has_error.* = true;
        self.cst.finishNode(vis_cst, .{ .has_error = has_vis_err });
        return parsed_vis;
    }

    /// Consumes a `,` or retired `;` member separator, emitting `E0224` when `;` is used (`ADR-22D`).
    fn consumeMemberSeparator(self: *Parser, has_member_err: *bool) !void {
        if (self.peekKind() == .comma) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else if (self.peekKind() == .semi) {
            const semi_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            has_member_err.* = true;
            const semi_span = self.getTokenSpan(semi_tok);
            try self.emitDiagnosticWithFix(
                .e0224_retired_semicolon_member_sep,
                semi_span,
                "`;` member separator has been retired; separate `struct`, `union`, `enum`, and `bit_field` members with `,`",
                "retired `;` separator; write `,` here",
                semi_span,
                ",",
                "replace `;` with `,`",
            );
        }
    }

    /// Parses a single top-level `Item` (`DR-22` Section 3.3).
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
        const outer_attrs = try self.parseAttributesWithSlice(&has_error);
        const saved_allow_case = self.is_allowing_non_canonical_case;
        if (self.hasAllowNonCanonicalCaseAttr(item_cst)) {
            self.is_allowing_non_canonical_case = true;
        }
        defer self.is_allowing_non_canonical_case = saved_allow_case;
        const outer_vis = try self.parseVisibilityWithLevel(&has_error);

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
            .kw_subscript => return self.parseSubscriptItem(item_cst, &has_error),
            .kw_comptime => {
                if (self.peekKindNth(1) != .lbrace) {
                    return self.parseFunctionItem(item_cst, &has_error);
                }
                self.cst.nodes.items(.kind)[item_cst.asInt()] = .block;
                _ = try self.consumeLeaf(.token_leaf, .{});
                const block_node = try self.parseBlock();
                self.cst.finishNode(item_cst, .{ .has_error = has_error });
                return block_node;
            },
            .kw_async, .kw_unsafe, .kw_extern, .kw_fn => {
                if (self.peekKind() == .kw_async and
                    self.peekKindNth(1) == .ident and
                    std.mem.eql(u8, self.peekLexemeNth(1), "test") and
                    self.peekKindNth(2) == .string_lit)
                {
                    return self.parseTestItem(item_cst, &has_error);
                }
                if (self.peekKind() == .kw_unsafe and self.peekKindNth(1) == .kw_impl) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    return self.parseImplItem(item_cst, &has_error);
                }
                if (self.peekKind() == .kw_unsafe and self.peekKindNth(1) == .kw_trait) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    return self.parseTraitItem(item_cst, &has_error);
                }
                if (self.peekKind() == .kw_extern or
                    (self.peekKind() == .kw_unsafe and self.peekKindNth(1) == .kw_extern))
                {
                    const is_unsafe_extern = self.peekKind() == .kw_unsafe;
                    const ext_idx: usize = if (is_unsafe_extern) 1 else 0;
                    const after_abi_idx: usize = if (self.peekKindNth(ext_idx + 1) == .string_lit)
                        ext_idx + 2
                    else
                        ext_idx + 1;
                    const after_abi_kind = self.peekKindNth(after_abi_idx);
                    if (after_abi_kind == .lbrace) {
                        if (is_unsafe_extern) _ = try self.consumeLeaf(.token_leaf, .{});
                        return self.parseExternBlockItem(
                            item_cst,
                            outer_vis,
                            is_unsafe_extern,
                            outer_attrs,
                            &has_error,
                        );
                    }
                    if (after_abi_kind == .ident and
                        std.mem.eql(u8, self.peekLexemeNth(after_abi_idx), "static"))
                    {
                        if (is_unsafe_extern) _ = try self.consumeLeaf(.token_leaf, .{});
                        return self.parseExternStaticItem(
                            item_cst,
                            .none,
                            outer_vis,
                            is_unsafe_extern,
                            outer_attrs,
                            &has_error,
                        );
                    }
                }
                return self.parseFunctionItem(item_cst, &has_error);
            },
            .ident => {
                if (self.peekKindNth(1) == .string_lit) {
                    const kw_lexeme = self.peekLexemeNth(0);
                    if (std.mem.eql(u8, kw_lexeme, "test")) {
                        return self.parseTestItem(item_cst, &has_error);
                    } else if (std.mem.eql(u8, kw_lexeme, "bench")) {
                        return self.parseBenchItem(item_cst, &has_error);
                    }
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

    /// Parses `ModItem = "mod" ( IDENT | "async" ) ( ";" | "{" { Item } "}" ) ;`.
    fn parseModItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .mod_item;
        const mod_tok = try self.consumeLeaf(.mod_introducer, .{});
        const name_tok = if (self.peekKind() == .kw_async)
            try self.consumeLeaf(.token_leaf, .{})
        else
            try self.expectIdentifierWithCasing(
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
                const inner_item = try self.parseItem();
                const inner_tag = self.ast.getNode(inner_item).tag;
                if (self.options.is_including_tests or (inner_tag != .test_decl and inner_tag != .bench_decl)) {
                    try inner_items.append(self.ast.allocator, inner_item.asInt());
                }
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

    /// Parses `UseTree = ( StringLit "as" IDENT ) | ( ModuleSegment { "." ModuleSegment } [ "." ( "*" | "{" … "}" ) | "as" IDENT ] )`.
    fn parseUseTree(self: *Parser, has_error: *bool) anyerror!void {
        return self.parseUseTreeWithContext(has_error, true);
    }

    /// Parses a root or nested `.use_tree` CST subtree (`is_top_level` gates inline `"<spec>" as <alias>`).
    fn parseUseTreeWithContext(
        self: *Parser,
        has_error: *bool,
        is_top_level: bool,
    ) anyerror!void {
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

        if (self.peekKind() == .string_lit or self.peekKind() == .byte_string_lit) {
            const is_byte_str = self.peekKind() == .byte_string_lit;
            const spec_tok = try self.consumeLeaf(.token_leaf, .{});
            const spec_span = self.getTokenSpan(spec_tok);
            const opt_unquoted = if (is_byte_str) null else extractSingleLineUnquotedSpec(self.getTokenLexeme(spec_tok));

            if (!is_top_level) {
                has_error.* = true;
                try self.emitDiagnosticWithFix(
                    .e0013_invalid_manifest_or_pkg_name,
                    spec_span,
                    "inline package import cannot be nested inside a `{ … }` group",
                    "write a standalone `use \"<spec>\" as <snake_alias>;` item",
                    null,
                    null,
                    null,
                );
            } else if (opt_unquoted == null) {
                has_error.* = true;
                try self.emitDiagnosticWithFix(
                    .e0013_invalid_manifest_or_pkg_name,
                    spec_span,
                    "inline package import specifier must be a plain single-line string literal",
                    "expected single-line `\"<pkg>@<version>\"` or URL string literal",
                    null,
                    null,
                    null,
                );
            } else if (!isValidInlineUseSpec(opt_unquoted.?)) {
                has_error.* = true;
                try self.emitDiagnosticWithFix(
                    .e0013_invalid_manifest_or_pkg_name,
                    spec_span,
                    "malformed inline package import specifier",
                    "expected `<pkg>@<semver_req>`, `https://…`, `git+https://…`, or `./…`",
                    null,
                    null,
                    null,
                );
            }

            if (self.peekKind() == .dot or self.peekKind() == .lbrace or self.peekKind() == .star) {
                has_error.* = true;
                try self.emitDiagnosticWithFix(
                    .e0013_invalid_manifest_or_pkg_name,
                    self.getTokenSpan(self.peekTokenIndexNth(0)),
                    "inline package import cannot chain `.item` or `.{…}`; bind the package root with `as <snake_alias>` first",
                    "replace chained path with `as <snake_alias>`",
                    null,
                    null,
                    null,
                );
                while (self.peekKind() != .semi and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .eof)
                {
                    _ = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                }
                self.cst.finishNode(tree_cst, .{ .has_error = true });
                return;
            }

            _ = try self.expectToken(
                .kw_as,
                has_error,
                "inline package import requires an explicit `as <snake_alias>` binding",
                "expected `as <snake_alias>` after package specifier",
            );

            const next_kind = self.peekKind();
            if (next_kind == .underscore or next_kind == .kw_self_val or next_kind == .kw_self_type) {
                const bad_alias_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                has_error.* = true;
                try self.emitDiagnosticWithFix(
                    .e0013_invalid_manifest_or_pkg_name,
                    self.getTokenSpan(bad_alias_tok),
                    "inline package alias must be a non-reserved `snake_case` identifier",
                    "reserved keyword or `_` cannot be used as a package alias",
                    null,
                    null,
                    null,
                );
            } else {
                const alias_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    has_error,
                    "expected `snake_case` package alias identifier after `as`",
                );
                if (RESERVED_INLINE_USE_ALIAS_MAP.has(self.getTokenLexeme(alias_tok))) {
                    has_error.* = true;
                    try self.emitDiagnosticWithFix(
                        .e0013_invalid_manifest_or_pkg_name,
                        self.getTokenSpan(alias_tok),
                        "inline package alias must not shadow reserved root namespace identifiers",
                        "choose a non-reserved `snake_case` package alias",
                        null,
                        null,
                        null,
                    );
                }
            }
            self.cst.finishNode(tree_cst, .{ .has_error = has_error.* });
            return;
        }

        if (self.peekKind() == .lbrace) {
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            while (self.peekKind() != .rbrace and
                self.peekKind() != .semi and
                self.peekKind() != .eof)
            {
                const loop_start = self.cursor;
                try self.parseUseTreeWithContext(has_error, false);
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
            self.cst.finishNode(tree_cst, .{ .has_error = has_error.* });
            return;
        }

        if (isIdentifierKind(self.peekKind()) or
            self.peekKind() == .kw_async or
            self.peekKind() == .kw_self_val or
            self.peekKind() == .kw_self_type)
        {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected module or symbol identifier in `use` tree",
                "expected path segment here",
            );
        }

        while (self.peekKind() == .dot) {
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
                    try self.parseUseTreeWithContext(has_error, false);
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
            if (isIdentifierKind(self.peekKind()) or
                self.peekKind() == .kw_async or
                self.peekKind() == .kw_self_val or
                self.peekKind() == .kw_self_type)
            {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected identifier, `*`, or `{` after `.` in `use` path",
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

    /// Parses `TypeAliasItem = "type" TYPE_IDENT [ TypeParams ] [ ":" ConstraintExpr ] [ "=" ( Type | ConstraintExpr ) ] ";" ;`.
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
            _ = try self.parseConstraintExpr(has_error);
        }

        var target_type_op: PackedOperand = .NONE;
        var refine_pat_op: PackedOperand = .NONE;

        if (self.peekKind() == .eq) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .kw_bit_field) {
                has_error.* = true;
                const bf_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                try self.emitUnexpectedToken(
                    bf_tok,
                    "`type Name = bit_field …` has been retired; declare `bit_field Name: BackingInt { … }` directly",
                    "retired `type … = bit_field`; use top-level `bit_field Name: Type { … }`",
                );
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
                    if (self.peekKind() == .colon) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                    target_type_op = PackedOperand.initNode(try self.parseType());
                }
                if (self.peekKind() == .lbrace) {
                    try self.parseBitFieldBody(has_error);
                }
                if (self.peekKind() == .semi) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                self.cst.finishNode(item_cst, .{ .has_error = true });
                return self.ast.appendNodeWithCst(.{
                    .tag = .type_alias_decl,
                    .main_token = type_tok,
                    .lhs = target_type_op,
                    .rhs = refine_pat_op,
                }, item_cst);
            }

            const first_target = try self.parseIntersectBound(.none);
            if (self.peekKind() == .pipe) {
                var union_members: std.ArrayList(u32) = .empty;
                defer union_members.deinit(self.ast.allocator);
                try union_members.append(self.ast.allocator, first_target.asInt());
                while (self.peekKind() == .pipe) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    try union_members.append(
                        self.ast.allocator,
                        (try self.parseIntersectBound(.none)).asInt(),
                    );
                }
                target_type_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(union_members.items));
                refine_pat_op = .{ .tag = .extra, .payload = @intCast(union_members.items.len) };
            } else {
                target_type_op = PackedOperand.initNode(first_target);
                if (self.peekKind() == .kw_is) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    refine_pat_op = PackedOperand.initNode(try self.parsePatternWithOptions(false, false));
                } else if (self.peekKind() == .kw_where) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    refine_pat_op = PackedOperand.initNode(try self.parseExpr(false));
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
            const saved_allow_field = self.is_allowing_non_canonical_case;
            if (self.hasAllowNonCanonicalCaseAttr(field_cst)) {
                self.is_allowing_non_canonical_case = true;
            }
            defer self.is_allowing_non_canonical_case = saved_allow_field;
            try self.parseVisibility(&has_field_err);

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
                try self.consumeMemberSeparator(&has_field_err);
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

    /// Parses `BitFieldItem = "bit_field" TYPE_IDENT ":" Type "{" { BitFieldMember } "}" ;` (`ADR-22D`).
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
            has_error.* = true;
            const open_paren = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            const ty_start_tok = self.peekTokenIndexNth(0);
            const inner_ty = try self.parseType();
            const ty_end_tok = if (self.cursor > 0)
                TokenIndex.fromInt(self.cursor - 1)
            else
                ty_start_tok;
            try self.expectClosingDelimiter(
                .rparen,
                open_paren,
                has_error,
                "expected `)` after `bit_field` backing integer type",
            );
            const close_end_tok = if (self.cursor > 0)
                TokenIndex.fromInt(self.cursor - 1)
            else
                open_paren;
            const paren_span = Span.init(
                self.file_id,
                self.getTokenSpan(open_paren).start_byte,
                self.getTokenSpan(close_end_tok).end_byte,
            );
            if (self.diagnostic_sink) |sink| {
                const ty_start_span = self.getTokenSpan(ty_start_tok);
                const ty_end_span = self.getTokenSpan(ty_end_tok);
                var opt_rep: ?[]const u8 = null;
                if (ty_start_span.start_byte <= ty_end_span.end_byte and ty_end_span.end_byte <= self.source.len) {
                    const ty_slice = std.mem.trim(u8, self.source[ty_start_span.start_byte..ty_end_span.end_byte], " \t\r\n");
                    if (ty_slice.len > 0) {
                        opt_rep = try std.fmt.allocPrint(sink.arena.asAllocator(), ": {s}", .{ty_slice});
                    }
                }
                try self.emitDiagnosticWithFix(
                    .e0201_unexpected_token,
                    paren_span,
                    "parenthesized `bit_field Name(Type)` syntax has been retired; write `bit_field Name: Type` instead",
                    "retired `(Type)` backing syntax; use `: Type`",
                    paren_span,
                    opt_rep,
                    "replace `(Type)` with `: Type`",
                );
            }
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

    /// Parses `"{ " { BitFieldMember } "}"` where `BitFieldMember = { Attribute } [ Vis ] IDENT ":" Type "|" INT_LIT [ "," ]`.
    fn parseBitFieldBody(self: *Parser, has_error: *bool) anyerror!void {
        const open_brace = try self.consumeLeaf(.token_leaf, .{});
        while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
            const loop_start = self.cursor;
            const member_cst = try self.startCstNode(.struct_field);
            var has_mem_err = false;

            try self.parseAttributes(&has_mem_err);
            const saved_allow_mem = self.is_allowing_non_canonical_case;
            if (self.hasAllowNonCanonicalCaseAttr(member_cst)) {
                self.is_allowing_non_canonical_case = true;
            }
            defer self.is_allowing_non_canonical_case = saved_allow_mem;
            try self.parseVisibility(&has_mem_err);

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
                try self.consumeMemberSeparator(&has_mem_err);
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

    /// Parses `EnumItem = "enum" TYPE_IDENT [ TypeParams ] [ ":" Type ] [ WhereClause ] "{" { EnumVariant } "}" ;` (`ADR-22D`).
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
        var backing_type_op: PackedOperand = .NONE;
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            backing_type_op = PackedOperand.initNode(try self.parseTypeWithMode(.none));
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
                const saved_allow_var = self.is_allowing_non_canonical_case;
                if (self.hasAllowNonCanonicalCaseAttr(var_cst)) {
                    self.is_allowing_non_canonical_case = true;
                }
                defer self.is_allowing_non_canonical_case = saved_allow_var;
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
                    try self.consumeMemberSeparator(&has_var_err);
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
            .lhs = backing_type_op,
        }, item_cst);
    }

    /// Parses `TraitItem = "trait" TYPE_IDENT [ TypeParams ] [ ":" ConstraintExpr ] [ WhereClause ] "{" { TraitMember } "}" ;`.
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
            _ = try self.parseConstraintExpr(has_error);
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
                const saved_allow_mem = self.is_allowing_non_canonical_case;
                if (self.hasAllowNonCanonicalCaseAttr(mem_cst)) {
                    self.is_allowing_non_canonical_case = true;
                }
                defer self.is_allowing_non_canonical_case = saved_allow_mem;
                try self.parseVisibility(&has_mem_err);

                const member_node = switch (self.peekKind()) {
                    .kw_type => try self.parseTypeAliasItem(mem_cst, &has_mem_err),
                    .kw_const => try self.parseConstItem(mem_cst, &has_mem_err),
                    .kw_subscript => try self.parseSubscriptItem(mem_cst, &has_mem_err),
                    .kw_async, .kw_unsafe, .kw_extern, .kw_comptime, .kw_fn => blk: {
                        const fn_node = try self.parseFunctionItem(mem_cst, &has_mem_err);
                        self.cst.nodes.items(.kind)[mem_cst.asInt()] = .trait_member;
                        break :blk fn_node;
                    },
                    else => blk: {
                        has_mem_err = true;
                        const err_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            err_tok,
                            "expected `fn`, `subscript`, `type`, or `const` member declaration in `trait`",
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
        const first_ty = try self.parseTypeWithMode(.is_only);
        if (self.peekKind() == .kw_for) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            _ = try self.parseTypeWithMode(.is_only);
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
                const saved_allow_mem = self.is_allowing_non_canonical_case;
                if (self.hasAllowNonCanonicalCaseAttr(mem_cst)) {
                    self.is_allowing_non_canonical_case = true;
                }
                defer self.is_allowing_non_canonical_case = saved_allow_mem;
                try self.parseVisibility(&has_mem_err);

                const member_node = switch (self.peekKind()) {
                    .kw_type => try self.parseTypeAliasItem(mem_cst, &has_mem_err),
                    .kw_const => try self.parseConstItem(mem_cst, &has_mem_err),
                    .kw_subscript => try self.parseSubscriptItem(mem_cst, &has_mem_err),
                    .kw_async, .kw_unsafe, .kw_extern, .kw_comptime, .kw_fn => blk: {
                        const fn_node = try self.parseFunctionItem(mem_cst, &has_mem_err);
                        self.cst.nodes.items(.kind)[mem_cst.asInt()] = .impl_member;
                        break :blk fn_node;
                    },
                    else => blk: {
                        has_mem_err = true;
                        const err_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            err_tok,
                            "expected `fn`, `subscript`, `type`, or `const` member declaration in `impl`",
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

    /// Parses `ExternBlockItem = [unsafe] "extern" [STRING_LIT] "{" { ExternMember } "}" ;`.
    fn parseExternBlockItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        outer_vis: ExternVisibility,
        is_unsafe_block: bool,
        outer_attrs: ParsedAttrSlice,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .extern_block_item;
        const extern_tok = try self.consumeLeaf(.token_leaf, .{});
        const block_abi_tok: TokenIndex = if (self.peekKind() == .string_lit)
            try self.consumeLeaf(.token_leaf, .{})
        else
            .none;
        const open_brace = try self.consumeLeaf(.token_leaf, .{});

        var member_indices: std.ArrayList(u32) = .empty;
        defer member_indices.deinit(self.ast.allocator);

        while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
            const loop_start = self.cursor;
            const mem_cst = try self.startCstNode(.placeholder);
            const member_node = blk_mem: {
                self.pushState(.item_dispatch, mem_cst) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        has_error.* = true;
                        break :blk_mem try self.recoverDepthOverflow(
                            mem_cst,
                            EXTERN_MEMBER_STOP_SET,
                            .item_hole,
                        );
                    },
                    else => return err,
                };
                defer self.popStates(1);

                var has_mem_err = false;
                const mem_attrs = try self.parseAttributesWithSlice(&has_mem_err);
                const saved_allow_mem = self.is_allowing_non_canonical_case;
                if (self.hasAllowNonCanonicalCaseAttr(mem_cst)) {
                    self.is_allowing_non_canonical_case = true;
                }
                defer self.is_allowing_non_canonical_case = saved_allow_mem;
                const mem_vis = try self.parseVisibilityWithLevel(&has_mem_err);

                const parsed_mem = switch (self.peekKind()) {
                    .kw_const => try self.parseConstItem(mem_cst, &has_mem_err),
                    .kw_fn, .kw_unsafe, .kw_extern, .kw_async, .kw_comptime => blk_fn_or_static: {
                        if (self.peekKind() == .kw_unsafe and
                            self.peekKindNth(1) == .ident and
                            std.mem.eql(u8, self.peekLexemeNth(1), "static"))
                        {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                            break :blk_fn_or_static try self.parseExternStaticItem(
                                mem_cst,
                                block_abi_tok,
                                mem_vis,
                                true,
                                mem_attrs,
                                &has_mem_err,
                            );
                        }
                        break :blk_fn_or_static try self.parseFunctionItemWithExtern(
                            mem_cst,
                            extern_tok,
                            block_abi_tok,
                            true,
                            &has_mem_err,
                        );
                    },
                    .ident => blk_ident: {
                        if (std.mem.eql(u8, self.peekLexemeNth(0), "static")) {
                            break :blk_ident try self.parseExternStaticItem(
                                mem_cst,
                                block_abi_tok,
                                mem_vis,
                                is_unsafe_block,
                                mem_attrs,
                                &has_mem_err,
                            );
                        }
                        break :blk_ident try self.recoverInvalidExternMember(mem_cst, &has_mem_err);
                    },
                    else => try self.recoverInvalidExternMember(mem_cst, &has_mem_err),
                };
                if (has_mem_err) has_error.* = true;
                break :blk_mem parsed_mem;
            };

            try member_indices.append(self.ast.allocator, member_node.asInt());
            if (self.cursor == loop_start and self.peekKind() != .rbrace and self.peekKind() != .eof) {
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            }
        }

        try self.expectClosingDelimiter(
            .rbrace,
            open_brace,
            has_error,
            "expected `}` to close `extern` block",
        );
        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });

        var payload_words: std.ArrayList(u32) = .empty;
        defer payload_words.deinit(self.ast.allocator);
        try payload_words.ensureTotalCapacity(
            self.ast.allocator,
            syntax_arenas.EXTERN_BLOCK_HEADER_WORDS + member_indices.items.len,
        );
        payload_words.appendAssumeCapacity(block_abi_tok.asInt());
        payload_words.appendAssumeCapacity(@bitCast(ExternBlockFlags{
            .visibility = outer_vis,
            .is_unsafe = is_unsafe_block,
        }));
        payload_words.appendAssumeCapacity(outer_attrs.attr_start);
        payload_words.appendAssumeCapacity(outer_attrs.attr_len);
        payload_words.appendSliceAssumeCapacity(member_indices.items);

        const extra_start = try self.ast.appendExtraSlice(payload_words.items);
        return self.ast.appendNodeWithCst(.{
            .tag = .extern_block_decl,
            .main_token = extern_tok,
            .lhs = PackedOperand.initExtra(extra_start),
            .rhs = .{ .tag = .extra, .payload = @intCast(payload_words.items.len) },
        }, item_cst);
    }

    /// Emits `E0201`, synchronizes to `;`, `}`, or the next `extern` member, and returns an `.item_hole`.
    fn recoverInvalidExternMember(
        self: *Parser,
        mem_cst: CstNodeIndex,
        has_mem_err: *bool,
    ) anyerror!NodeIndex {
        has_mem_err.* = true;
        const err_tok = self.peekTokenIndexNth(0);
        try self.emitUnexpectedToken(
            err_tok,
            "expected `fn`, `static`, or `const` declaration inside `extern` block",
            "unexpected token in `extern` block",
        );
        var has_consumed_any = false;
        var nested_depth: u32 = 0;
        while (self.peekKind() != .eof) {
            const cur_kind = self.peekKind();
            if (nested_depth == 0) {
                if (cur_kind == .semi) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                    break;
                }
                if (cur_kind == .rbrace) break;
                const is_contextual_static = cur_kind == .ident and
                    std.mem.eql(u8, self.peekLexemeNth(0), "static");
                if (has_consumed_any and
                    (EXTERN_MEMBER_STOP_SET.contains(cur_kind) or is_contextual_static))
                {
                    break;
                }
            }
            if (cur_kind == .lbrace or cur_kind == .lparen or cur_kind == .lbracket) {
                nested_depth += 1;
            } else if (cur_kind == .rbrace or cur_kind == .rparen or cur_kind == .rbracket) {
                if (nested_depth > 0) nested_depth -= 1;
            }
            _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
            has_consumed_any = true;
        }
        self.cst.nodes.items(.kind)[mem_cst.asInt()] = .invalid_parse_subtree;
        self.cst.finishNode(mem_cst, .{ .has_error = true });
        return self.ast.appendNodeWithCst(.{
            .tag = .item_hole,
            .main_token = err_tok,
        }, mem_cst);
    }

    /// Parses `ExternStaticItem = [extern [STRING_LIT]] "static" ["mut"] IDENT ":" Type ";" ;`.
    fn parseExternStaticItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        inherited_abi_tok: TokenIndex,
        item_vis: ExternVisibility,
        is_unsafe_item: bool,
        item_attrs: ParsedAttrSlice,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .extern_static_item;
        var effective_abi_tok = inherited_abi_tok;
        if (self.peekKind() == .kw_extern) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .string_lit) {
                effective_abi_tok = try self.consumeLeaf(.token_leaf, .{});
            }
        }

        const static_tok = try self.consumeLeaf(.token_leaf, .{});
        var is_mut = false;
        if (self.peekKind() == .kw_mut) {
            is_mut = true;
            _ = try self.consumeLeaf(.token_leaf, .{});
        }

        const name_tok = try self.expectExternSymbolIdentifier(
            has_error,
            "expected foreign symbol identifier after `static`",
        );

        const type_node: NodeIndex = if (self.peekKind() == .colon) blk_ty: {
            _ = try self.consumeLeaf(.token_leaf, .{});
            break :blk_ty try self.parseType();
        } else blk_hole: {
            has_error.* = true;
            const err_tok = self.peekTokenIndexNth(0);
            try self.emitUnexpectedToken(
                err_tok,
                "expected `:` and type annotation in `extern static` declaration",
                "expected `: Type` here",
            );
            const hole_cst = try self.startCstNode(.invalid_parse_subtree);
            self.cst.finishNode(hole_cst, .{ .has_error = true });
            break :blk_hole try self.ast.appendNodeWithCst(.{
                .tag = .type_hole,
                .main_token = err_tok,
            }, hole_cst);
        };

        if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `;` after `extern static` declaration",
                "expected `;` here",
            );
            try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, EXTERN_MEMBER_STOP_SET, false);
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        const extra_words = [syntax_arenas.EXTERN_STATIC_EXTRA_WORDS]u32{
            static_tok.asInt(),
            effective_abi_tok.asInt(),
            @bitCast(ExternStaticFlags{
                .visibility = item_vis,
                .is_mut = is_mut,
                .has_extern = true,
                .is_unsafe = is_unsafe_item,
            }),
            item_attrs.attr_start,
            item_attrs.attr_len,
        };
        const extra_idx = try self.ast.appendExtraSlice(&extra_words);
        return self.ast.appendNodeWithCst(.{
            .tag = .extern_static_decl,
            .main_token = name_tok,
            .lhs = PackedOperand.initNode(type_node),
            .rhs = PackedOperand.initExtra(extra_idx),
        }, item_cst);
    }

    /// Parses `FunctionItem = [comptime] [async] [unsafe] [extern [STRING_LIT]] "fn" FnSignature (Block | "=" Expr ";" | ";")`.
    fn parseFunctionItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        return self.parseFunctionItemWithExtern(item_cst, .none, .none, false, has_error);
    }

    /// Parses a `FunctionItem`, propagating enclosing `extern` block linkage and `W0201` foreign symbol exemptions.
    fn parseFunctionItemWithExtern(
        self: *Parser,
        item_cst: CstNodeIndex,
        enclosing_extern_tok: TokenIndex,
        enclosing_abi_tok: TokenIndex,
        is_in_extern_block: bool,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .fn_item;
        var has_explicit_extern = false;
        while (self.peekKind() == .kw_async or
            self.peekKind() == .kw_unsafe or
            self.peekKind() == .kw_extern or
            self.peekKind() == .kw_comptime)
        {
            const qual_kind = self.peekKind();
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (qual_kind == .kw_extern) {
                has_explicit_extern = true;
                if (self.peekKind() == .string_lit) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            }
        }

        if (is_in_extern_block and !has_explicit_extern and !enclosing_extern_tok.isNone()) {
            _ = try self.cst.appendLeafNode(
                .token_leaf,
                enclosing_extern_tok,
                .{ .is_missing_or_injected = true },
            );
            if (!enclosing_abi_tok.isNone()) {
                _ = try self.cst.appendLeafNode(
                    .token_leaf,
                    enclosing_abi_tok,
                    .{ .is_missing_or_injected = true },
                );
            }
        }

        const fn_tok = if (self.peekKind() == .kw_fn)
            try self.consumeLeaf(.fn_introducer, .{})
        else
            try self.expectToken(
                .kw_fn,
                has_error,
                "expected `fn` keyword in function declaration",
                "expected `fn` here",
            );

        const is_extern_fn = has_explicit_extern or is_in_extern_block;
        const sig_cst = try self.startCstNode(.fn_sig);
        if (is_extern_fn) {
            _ = try self.expectExternSymbolIdentifier(
                has_error,
                "expected foreign function name",
            );
        } else if (self.hasPascalExemptFnAttr(item_cst) and self.peekKind() == .type_ident) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
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
        if (self.peekKind() == .arrow) {
            const ret_cst = try self.startCstNode(.return_type);
            _ = try self.consumeLeaf(.token_leaf, .{});
            ret_type_op = PackedOperand.initNode(try self.parseTypeWithMode(.is_only));
            self.cst.finishNode(ret_cst, .{ .has_error = has_error.* });
        }

        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }
        self.cst.finishNode(sig_cst, .{ .has_error = has_error.* });

        var body_op: PackedOperand = .NONE;
        if (is_in_extern_block) {
            if (self.peekKind() == .semi) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else if (self.peekKind() == .lbrace) {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "foreign function declaration inside `extern` block cannot have a body; expected `;`",
                    "unexpected `{ … }` body on `extern` prototype",
                );
                _ = try self.parseBlock();
                if (self.peekKind() == .semi) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            } else {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected `;` after foreign function signature inside `extern` block",
                    "expected `;` here",
                );
                try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, EXTERN_MEMBER_STOP_SET, false);
            }
        } else if (self.peekKind() == .lbrace) {
            body_op = PackedOperand.initNode(try self.parseBlock());
        } else if (self.peekKind() == .eq) {
            const body_cst = try self.startCstNode(.fn_expr_body);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const saved_cond_header = self.is_in_cond_header;
            self.is_in_cond_header = false;
            const body_expr = try self.parseExpr(true);
            self.is_in_cond_header = saved_cond_header;
            if (self.peekKind() == .semi) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "expected `;` after `=` function body expression",
                    "expected `;` here",
                );
                try self.skipToRecoveryAnchor(ITEM_CONSUME_SET, ITEM_STOP_SET, false);
            }
            self.cst.finishNode(body_cst, .{ .has_error = has_error.* });
            body_op = PackedOperand.initNode(body_expr);
        } else if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` function body, `= expr;`, or `;` after function signature",
                "expected `{`, `=`, or `;` here",
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

    /// Parses `SubscriptItem = [Vis] "subscript" [TypeParams] "(" [ParamList] ")" "->" Type [WhereClause] ("{" SubscriptArm+ "}" | ";")` (`SE-21`).
    fn parseSubscriptItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .subscript_item;
        const subscript_tok = try self.consumeLeaf(.subscript_introducer, .{});

        const sig_cst = try self.startCstNode(.fn_sig);
        if (self.peekKind() == .lbracket) {
            try self.parseTypeParams(has_error);
        }

        if (self.peekKind() == .lparen) {
            try self.parseParamList(has_error);
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `(` to start `subscript` parameter list",
                "expected `(` here",
            );
        }

        var ret_type_op: PackedOperand = .NONE;
        if (self.peekKind() == .arrow or self.peekKind() == .colon) {
            const ret_cst = try self.startCstNode(.return_type);
            var has_ret_err = false;
            if (self.peekKind() == .colon) {
                has_ret_err = true;
                has_error.* = true;
                const colon_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                const colon_span = self.getTokenSpan(colon_tok);
                try self.emitDiagnosticWithFix(
                    .e0201_unexpected_token,
                    colon_span,
                    "`subscript` return type uses `-> Type` instead of `: Type`",
                    "expected `->` before `subscript` element type",
                    colon_span,
                    " ->",
                    "replace `:` with ` ->`",
                );
            } else {
                _ = try self.consumeLeaf(.token_leaf, .{});
            }
            ret_type_op = PackedOperand.initNode(try self.parseTypeWithMode(.is_only));
            self.cst.finishNode(ret_cst, .{ .has_error = has_ret_err });
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `->` and element type in `subscript` declaration",
                "expected `-> Type` here",
            );
        }

        if (self.peekKind() == .kw_where) {
            try self.parseWhereClause(has_error);
        }
        self.cst.finishNode(sig_cst, .{ .has_error = has_error.* });

        var rhs_op: PackedOperand = .NONE;
        if (self.peekKind() == .semi) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        } else if (self.peekKind() == .lbrace) {
            const body_cst = try self.startCstNode(.block);
            const open_brace = try self.consumeLeaf(.token_leaf, .{});
            var arm_words: std.ArrayList(u32) = .empty;
            defer arm_words.deinit(self.ast.allocator);
            try arm_words.append(self.ast.allocator, 0);
            var arm_count: u32 = 0;

            while (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                const loop_start = self.cursor;
                const arm_cst = try self.startCstNode(.subscript_arm);
                var has_arm_err = false;
                var arm_mode: u32 = 0;

                if (self.peekKind() == .kw_let) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    arm_mode = 0;
                } else if (self.peekKind() == .ident and std.mem.eql(u8, self.peekLexemeNth(0), "inout")) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    arm_mode = 1;
                } else {
                    has_arm_err = true;
                    has_error.* = true;
                    try self.emitUnexpectedToken(
                        self.peekTokenIndexNth(0),
                        "expected `let` or `inout` accessor arm inside `subscript` body",
                        "expected `let { … }` or `inout { … }` here",
                    );
                    if (self.peekKind() != .lbrace and self.peekKind() != .rbrace and self.peekKind() != .eof) {
                        _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                    }
                }

                if (self.peekKind() == .lbrace) {
                    const arm_blk = try self.parseBlock();
                    try arm_words.append(self.ast.allocator, arm_mode);
                    try arm_words.append(self.ast.allocator, arm_blk.asInt());
                    arm_count += 1;
                } else {
                    has_arm_err = true;
                    has_error.* = true;
                    try self.emitUnexpectedToken(
                        self.peekTokenIndexNth(0),
                        "expected `{` block after `subscript` accessor arm introducer",
                        "expected `{` here",
                    );
                    try self.skipToRecoveryAnchor(BLOCK_STMT_CONSUME_SET, BLOCK_STMT_STOP_SET, false);
                }

                self.cst.finishNode(arm_cst, .{ .has_error = has_arm_err });
                if (self.cursor == loop_start) {
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                }
            }

            if (arm_count == 0) {
                has_error.* = true;
                try self.emitUnexpectedToken(
                    self.peekTokenIndexNth(0),
                    "`subscript` body must declare at least one `let` or `inout` accessor arm",
                    "empty `subscript` body",
                );
            }
            arm_words.items[0] = arm_count;

            try self.expectClosingDelimiter(
                .rbrace,
                open_brace,
                has_error,
                "expected `}` to close `subscript` body",
            );
            self.cst.finishNode(body_cst, .{ .has_error = has_error.* });
            rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(arm_words.items));
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` accessor body or `;` after `subscript` signature",
                "expected `{` or `;` here",
            );
        }

        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .subscript_decl,
            .main_token = subscript_tok,
            .lhs = ret_type_op,
            .rhs = rhs_op,
        }, item_cst);
    }

    /// Parses `TestItem = [ "async" ] "test" STRING_LIT [ "(" FnParam { "," FnParam } [ "," ] ")" ] [ "->" Type ] Block` (`SE-16`).
    fn parseTestItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .test_item;
        if (self.peekKind() == .kw_async) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        }
        _ = try self.consumeLeaf(.test_introducer, .{});
        const name_str_tok = try self.expectToken(
            .string_lit,
            has_error,
            "expected string literal test name after `test`",
            "expected test name string literal here",
        );

        if (self.peekKind() == .lparen) {
            try self.parseParamList(has_error);
        }

        var ret_type_op: PackedOperand = .NONE;
        if (self.peekKind() == .arrow) {
            const ret_cst = try self.startCstNode(.return_type);
            _ = try self.consumeLeaf(.token_leaf, .{});
            ret_type_op = PackedOperand.initNode(try self.parseTypeWithMode(.is_only));
            self.cst.finishNode(ret_cst, .{ .has_error = has_error.* });
        }

        const body_op: PackedOperand = if (self.options.is_including_tests)
            PackedOperand.initNode(try self.parseBlock())
        else blk_skip: {
            try self.skipTestOrBenchBlockCst(has_error);
            break :blk_skip .NONE;
        };
        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .test_decl,
            .main_token = name_str_tok,
            .lhs = ret_type_op,
            .rhs = body_op,
        }, item_cst);
    }

    /// Parses `BenchItem = "bench" STRING_LIT "(" FnParam ")" [ "->" Type ] Block` (`SE-16`).
    fn parseBenchItem(
        self: *Parser,
        item_cst: CstNodeIndex,
        has_error: *bool,
    ) anyerror!NodeIndex {
        self.cst.nodes.items(.kind)[item_cst.asInt()] = .bench_item;
        _ = try self.consumeLeaf(.bench_introducer, .{});
        const name_str_tok = try self.expectToken(
            .string_lit,
            has_error,
            "expected string literal benchmark name after `bench`",
            "expected benchmark name string literal here",
        );

        if (self.peekKind() == .lparen) {
            try self.parseParamList(has_error);
        } else {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `(` and `&mut Bencher` parameter after `bench` name",
                "expected `(b: &mut Bencher)` here",
            );
        }

        var ret_type_op: PackedOperand = .NONE;
        if (self.peekKind() == .arrow) {
            const ret_cst = try self.startCstNode(.return_type);
            _ = try self.consumeLeaf(.token_leaf, .{});
            ret_type_op = PackedOperand.initNode(try self.parseTypeWithMode(.is_only));
            self.cst.finishNode(ret_cst, .{ .has_error = has_error.* });
        }

        const body_op: PackedOperand = if (self.options.is_including_tests)
            PackedOperand.initNode(try self.parseBlock())
        else blk_skip: {
            try self.skipTestOrBenchBlockCst(has_error);
            break :blk_skip .NONE;
        };
        self.cst.finishNode(item_cst, .{ .has_error = has_error.* });
        return self.ast.appendNodeWithCst(.{
            .tag = .bench_decl,
            .main_token = name_str_tok,
            .lhs = ret_type_op,
            .rhs = body_op,
        }, item_cst);
    }

    /// Releases scratch `@allow(non_canonical_case)` casing-exemption sets at the end of a parse pass.
    fn clearAllowedNonCanonicalNames(self: *Parser) void {
        self.is_in_full_parse = false;
        self.allowed_non_canonical_types.deinit(self.ast.allocator);
        self.allowed_non_canonical_types = .empty;
        self.allowed_non_canonical_members.deinit(self.ast.allocator);
        self.allowed_non_canonical_members = .empty;
    }

    /// Pre-scans `@allow(… non_canonical_case …)` declarations in `token_buffer` for forward-ref and incremental parity.
    fn precollectAllowedNonCanonicalNames(self: *Parser) !void {
        const kind_slice = self.token_buffer.tokens.items(.kind);
        const total = kind_slice.len;
        var scan_pos: usize = 0;
        while (std.mem.indexOfScalarPos(TokenKind, kind_slice, scan_pos, .at)) |at_idx| {
            scan_pos = at_idx + 1;
            const name_idx = self.skipCarrierRawIndex(at_idx + 1);
            if (name_idx >= total) break;
            const name_lex = self.getTokenLexeme(TokenIndex.fromInt(@intCast(name_idx)));
            if (!std.mem.eql(u8, name_lex, "allow")) continue;

            var cur_idx = self.skipCarrierRawIndex(name_idx + 1);
            if (cur_idx >= total or kind_slice[cur_idx] != .lparen) continue;
            cur_idx = self.skipCarrierRawIndex(cur_idx + 1);

            var paren_depth: u32 = 1;
            var has_non_canonical = false;
            while (cur_idx < total and paren_depth > 0) {
                const cur_kind = kind_slice[cur_idx];
                if (cur_kind == .eof) break;
                if (cur_kind == .lparen) {
                    paren_depth += 1;
                } else if (cur_kind == .rparen) {
                    paren_depth -= 1;
                } else if (isIdentifierKind(cur_kind)) {
                    const arg_lex = self.getTokenLexeme(TokenIndex.fromInt(@intCast(cur_idx)));
                    if (std.mem.eql(u8, arg_lex, "non_canonical_case") or
                        std.mem.eql(u8, arg_lex, "W0201"))
                    {
                        has_non_canonical = true;
                    }
                }
                cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
            }
            if (!has_non_canonical or paren_depth != 0) continue;

            // Skip any stacked attributes, visibility `pub(…)`, and item/function qualifiers:
            while (cur_idx < total) {
                const cur_kind = kind_slice[cur_idx];
                if (cur_kind == .at) {
                    const next_attr = self.skipCarrierRawIndex(cur_idx + 1);
                    if (next_attr >= total) break;
                    cur_idx = self.skipCarrierRawIndex(next_attr + 1);
                    if (cur_idx < total and kind_slice[cur_idx] == .lparen) {
                        var sub_depth: u32 = 1;
                        cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                        while (cur_idx < total and sub_depth > 0) {
                            if (kind_slice[cur_idx] == .eof) break;
                            if (kind_slice[cur_idx] == .lparen) {
                                sub_depth += 1;
                            } else if (kind_slice[cur_idx] == .rparen) {
                                sub_depth -= 1;
                            }
                            cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                        }
                    }
                    continue;
                }
                if (cur_kind == .kw_pub) {
                    cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                    if (cur_idx < total and kind_slice[cur_idx] == .lparen) {
                        var vis_depth: u32 = 1;
                        cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                        while (cur_idx < total and vis_depth > 0) {
                            if (kind_slice[cur_idx] == .eof) break;
                            if (kind_slice[cur_idx] == .lparen) {
                                vis_depth += 1;
                            } else if (kind_slice[cur_idx] == .rparen) {
                                vis_depth -= 1;
                            }
                            cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                        }
                    }
                    continue;
                }
                if (cur_kind == .kw_async or
                    cur_kind == .kw_unsafe or
                    cur_kind == .kw_comptime or
                    cur_kind == .kw_var or
                    cur_kind == .kw_let)
                {
                    cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                    continue;
                }
                if (cur_kind == .kw_extern) {
                    cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                    if (cur_idx < total and kind_slice[cur_idx] == .string_lit) {
                        cur_idx = self.skipCarrierRawIndex(cur_idx + 1);
                    }
                    continue;
                }
                break;
            }
            if (cur_idx >= total) continue;

            const decl_kind = kind_slice[cur_idx];
            if (decl_kind == .kw_type or
                decl_kind == .kw_struct or
                decl_kind == .kw_union or
                decl_kind == .kw_bit_field or
                decl_kind == .kw_enum or
                decl_kind == .kw_trait)
            {
                const ident_idx = self.skipCarrierRawIndex(cur_idx + 1);
                if (ident_idx < total and isIdentifierKind(kind_slice[ident_idx])) {
                    const ty_lex = self.getTokenLexeme(TokenIndex.fromInt(@intCast(ident_idx)));
                    if (ty_lex.len > 0) {
                        try self.allowed_non_canonical_types.put(self.ast.allocator, ty_lex, {});
                    }
                    if (decl_kind == .kw_struct or decl_kind == .kw_union or decl_kind == .kw_bit_field) {
                        var body_scan = self.skipCarrierRawIndex(ident_idx + 1);
                        while (body_scan < total and
                            kind_slice[body_scan] != .lbrace and
                            kind_slice[body_scan] != .semi and
                            kind_slice[body_scan] != .eof)
                        {
                            body_scan = self.skipCarrierRawIndex(body_scan + 1);
                        }
                        if (body_scan < total and kind_slice[body_scan] == .lbrace) {
                            var brace_depth: u32 = 1;
                            body_scan = self.skipCarrierRawIndex(body_scan + 1);
                            while (body_scan < total and brace_depth > 0) {
                                const bk = kind_slice[body_scan];
                                if (bk == .eof) break;
                                if (bk == .lbrace) {
                                    brace_depth += 1;
                                } else if (bk == .rbrace) {
                                    brace_depth -= 1;
                                } else if (brace_depth == 1 and isIdentifierKind(bk)) {
                                    const after_fld = self.skipCarrierRawIndex(body_scan + 1);
                                    if (after_fld < total and kind_slice[after_fld] == .colon) {
                                        const fld_lex = self.getTokenLexeme(TokenIndex.fromInt(@intCast(body_scan)));
                                        if (fld_lex.len > 0) {
                                            try self.allowed_non_canonical_members.put(self.ast.allocator, fld_lex, {});
                                        }
                                    }
                                }
                                body_scan = self.skipCarrierRawIndex(body_scan + 1);
                            }
                        }
                    }
                }
            } else if (decl_kind == .kw_fn or decl_kind == .kw_const or decl_kind == .kw_mod) {
                const ident_idx = self.skipCarrierRawIndex(cur_idx + 1);
                if (ident_idx < total and isIdentifierKind(kind_slice[ident_idx])) {
                    const mem_lex = self.getTokenLexeme(TokenIndex.fromInt(@intCast(ident_idx)));
                    if (mem_lex.len > 0) {
                        try self.allowed_non_canonical_members.put(self.ast.allocator, mem_lex, {});
                    }
                }
            } else if (isIdentifierKind(decl_kind)) {
                const mem_lex = self.getTokenLexeme(TokenIndex.fromInt(@intCast(cur_idx)));
                if (mem_lex.len > 0) {
                    try self.allowed_non_canonical_members.put(self.ast.allocator, mem_lex, {});
                }
            }
        }
    }

    /// Returns `true` if `item_cst` carries a leading `@allow(… non_canonical_case …)` attribute (`DR-10`).
    fn hasAllowNonCanonicalCaseAttr(self: *const Parser, item_cst: CstNodeIndex) bool {
        if (item_cst.isNone()) return false;
        const total = self.cst.countNodes();
        var cursor: usize = item_cst.asInt() + 1;
        while (cursor < total) {
            const child = self.cst.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if (child.kind == .attribute) {
                const attr_end = @min(cursor + @max(@as(usize, child.subtree_size), 1), total);
                var is_allow_attr = false;
                var has_seen_attr_name = false;
                var tok_cur = cursor + 1;
                while (tok_cur < attr_end) : (tok_cur += 1) {
                    const leaf = self.cst.getNode(CstNodeIndex.fromInt(@intCast(tok_cur)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < self.token_buffer.countTokens())
                    {
                        const tok_rec = self.token_buffer.getToken(leaf.token);
                        if (tok_rec.kind == .at) continue;
                        const lex = self.getTokenLexeme(leaf.token);
                        if (!has_seen_attr_name) {
                            has_seen_attr_name = true;
                            if (!std.mem.eql(u8, lex, "allow")) break;
                            is_allow_attr = true;
                        } else if (is_allow_attr and isIdentifierKind(tok_rec.kind) and
                            (std.mem.eql(u8, lex, "non_canonical_case") or
                                std.mem.eql(u8, lex, "W0201")))
                        {
                            return true;
                        }
                    }
                }
                cursor = attr_end;
                continue;
            }
            cursor += @max(@as(usize, child.subtree_size), 1);
        }
        return false;
    }

    /// Returns `true` if `item_cst` carries a leading `@constructor` or `@builder_item` attribute (`SE-22`).
    fn hasPascalExemptFnAttr(self: *const Parser, item_cst: CstNodeIndex) bool {
        if (item_cst.isNone()) return false;
        const total = self.cst.countNodes();
        var cursor: usize = item_cst.asInt() + 1;
        while (cursor < total) {
            const child = self.cst.getNode(CstNodeIndex.fromInt(@intCast(cursor)));
            if (child.kind == .attribute) {
                const attr_end = @min(cursor + @max(@as(usize, child.subtree_size), 1), total);
                var tok_cur = cursor + 1;
                while (tok_cur < attr_end) : (tok_cur += 1) {
                    const leaf = self.cst.getNode(CstNodeIndex.fromInt(@intCast(tok_cur)));
                    if (leaf.subtree_size <= 1 and !leaf.token.isNone() and
                        leaf.token.asInt() < self.token_buffer.countTokens())
                    {
                        const tok_rec = self.token_buffer.getToken(leaf.token);
                        if (tok_rec.kind == .at) continue;
                        const start_b: usize = tok_rec.byte_offset;
                        const end_b: usize = @min(start_b + @as(usize, tok_rec.byte_len), self.source.len);
                        const lex = self.source[start_b..end_b];
                        if (std.mem.eql(u8, lex, "constructor") or std.mem.eql(u8, lex, "builder_item")) {
                            return true;
                        }
                        break;
                    }
                }
                cursor = attr_end;
                continue;
            }
            cursor += @max(@as(usize, child.subtree_size), 1);
        }
        return false;
    }

    /// Consumes a balanced `{ … }` block strictly into `LosslessCstArena` with zero body `AstNode` work (`SE-16`).
    fn skipTestOrBenchBlockCst(self: *Parser, has_error: *bool) anyerror!void {
        const blk_cst = try self.startCstNode(.block);
        if (self.peekKind() != .lbrace) {
            has_error.* = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `{` to start block body",
                "expected `{` here",
            );
            self.cst.finishNode(blk_cst, .{ .has_error = true });
            return;
        }
        const open_brace = try self.consumeLeaf(.token_leaf, .{});
        var brace_depth: u32 = 1;
        while (brace_depth > 0 and self.peekKind() != .eof) {
            const cur_kind = self.peekKind();
            if (cur_kind == .lbrace) {
                brace_depth += 1;
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else if (cur_kind == .rbrace) {
                brace_depth -= 1;
                if (brace_depth == 0) {
                    try self.expectClosingDelimiter(.rbrace, open_brace, has_error, "expected `}` to close block");
                    break;
                }
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                _ = try self.consumeLeaf(.token_leaf, .{});
            }
        }
        if (brace_depth > 0) {
            try self.expectClosingDelimiter(.rbrace, open_brace, has_error, "expected `}` to close block");
        }
        self.cst.finishNode(blk_cst, .{ .has_error = has_error.* });
    }

    /// Parses `ParamList` with `/` positional-only and `*` keyword-only zone separators and `...` variadics (`ADR-22B`, `SE-11`).
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
        var has_seen_slash = false;
        var has_seen_star = false;
        var has_seen_variadic = false;
        var non_self_before_slash: u32 = 0;
        var params_after_star: u32 = 0;
        var last_star_span: Span = self.getTokenSpan(open_paren);

        while (self.peekKind() != .rparen and
            self.peekKind() != .lbrace and
            self.peekKind() != .rbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;

            // [1] Parameter zone separators `/` (positional-only) and `*` (keyword-only) (`SE-11`):
            if (self.peekKind() == .slash or
                (self.peekKind() == .star and
                    (self.peekKindNth(1) == .comma or
                        self.peekKindNth(1) == .rparen or
                        self.peekKindNth(1) == .slash or
                        self.peekKindNth(1) == .star)))
            {
                const sep_cst = try self.startCstNode(.param_zone_sep);
                const is_slash = self.peekKind() == .slash;
                const sep_tok = try self.consumeLeaf(.token_leaf, .{});
                const sep_span = self.getTokenSpan(sep_tok);
                var has_sep_err = false;

                if (is_slash) {
                    if (has_seen_slash) {
                        has_sep_err = true;
                        try self.emitDiagnosticWithFix(
                            .e0228_invalid_param_zone_separator,
                            sep_span,
                            "duplicate `/` positional-only parameter zone separator",
                            "duplicate `/` separator here",
                            null,
                            null,
                            null,
                        );
                    } else if (has_seen_star) {
                        has_sep_err = true;
                        try self.emitDiagnosticWithFix(
                            .e0228_invalid_param_zone_separator,
                            sep_span,
                            "`/` positional-only parameter separator must appear before `*` keyword-only separator",
                            "`/` cannot appear after `*`",
                            null,
                            null,
                            null,
                        );
                    } else if (non_self_before_slash == 0) {
                        has_sep_err = true;
                        try self.emitDiagnosticWithFix(
                            .e0228_invalid_param_zone_separator,
                            sep_span,
                            "`/` positional-only separator requires at least one preceding non-receiver parameter",
                            "empty positional-only parameter zone before `/`",
                            null,
                            null,
                            null,
                        );
                    }
                    has_seen_slash = true;
                } else {
                    if (has_seen_star) {
                        has_sep_err = true;
                        try self.emitDiagnosticWithFix(
                            .e0228_invalid_param_zone_separator,
                            sep_span,
                            "duplicate `*` keyword-only parameter zone separator",
                            "duplicate `*` separator here",
                            null,
                            null,
                            null,
                        );
                    }
                    has_seen_star = true;
                    last_star_span = sep_span;
                }

                if (has_sep_err) has_error.* = true;
                self.cst.finishNode(sep_cst, .{ .has_error = has_sep_err });
                if (self.peekKind() == .comma) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else if (self.peekKind() != .rparen and !has_sep_err) {
                    break;
                }
                continue;
            }

            // [2] Trailing C variadic parameter `...` (`ADR-22F`):
            if (self.peekKind() == .dotdotdot) {
                const var_cst = try self.startCstNode(.variadic_param);
                const dots_tok = try self.consumeLeaf(.token_leaf, .{});
                var has_var_err = false;
                if (has_seen_variadic) {
                    has_var_err = true;
                    try self.emitUnexpectedToken(
                        dots_tok,
                        "duplicate `...` variadic parameter in parameter list",
                        "duplicate `...` here",
                    );
                }
                has_seen_variadic = true;
                if (self.peekKind() == .comma and self.peekKindNth(1) != .rparen) {
                    has_var_err = true;
                    try self.emitUnexpectedToken(
                        dots_tok,
                        "`...` variadic parameter must be the final parameter in the parameter list",
                        "`...` must appear last",
                    );
                }
                if (has_var_err) has_error.* = true;
                self.cst.finishNode(var_cst, .{ .has_error = has_var_err });
                if (self.peekKind() == .comma) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else if (self.peekKind() != .rparen and !has_var_err) {
                    break;
                }
                continue;
            }

            // [3] Receiver `SelfParam` or regular `FnParam`:
            const param_cst = try self.startCstNode(.fn_param);
            var has_param_err = false;

            try self.parseAttributes(&has_param_err);
            const saved_allow_param = self.is_allowing_non_canonical_case;
            if (self.hasAllowNonCanonicalCaseAttr(param_cst)) {
                self.is_allowing_non_canonical_case = true;
            }
            defer self.is_allowing_non_canonical_case = saved_allow_param;

            var has_leading_var = false;
            if (self.peekKind() == .kw_var) {
                has_leading_var = true;
                _ = try self.consumeLeaf(.token_leaf, .{});
            }

            if (self.peekKind() == .kw_comptime) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (!has_leading_var and self.peekKind() == .kw_var) {
                    has_leading_var = true;
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
            }

            // Check for `SelfParam` (`&self`, `&mut self`, `[var] [own] self`, `self: Type`, or retired `mut`/`ref`/`inout`/`sink`/`&inout self`):
            const peek0_retired_mode = if (self.peekKind() == .ident)
                RETIRED_PARAM_MODE_MAP.get(self.peekLexemeNth(0))
            else
                null;
            const is_amp_self = self.peekKind() == .amp;
            const is_own_self = self.peekKind() == .kw_own and self.peekKindNth(1) == .kw_self_val;
            const is_mut_self = self.peekKind() == .kw_mut and self.peekKindNth(1) == .kw_self_val;
            const is_ref_self = peek0_retired_mode == .ref and
                (self.peekKindNth(1) == .kw_self_val or
                    (self.peekKindNth(1) == .kw_mut and self.peekKindNth(2) == .kw_self_val));
            const is_inout_or_sink_self = (peek0_retired_mode == .inout or peek0_retired_mode == .sink) and
                self.peekKindNth(1) == .kw_self_val;

            if (is_amp_self or is_own_self or is_mut_self or is_ref_self or
                is_inout_or_sink_self or self.peekKind() == .kw_self_val)
            {
                if (is_amp_self) {
                    const amp_tok = try self.consumeLeaf(.token_leaf, .{});
                    if (self.peekKind() == .kw_mut) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else if (self.peekKind() == .ident and
                        std.mem.eql(u8, self.peekLexemeNth(0), "inout") and
                        self.peekKindNth(1) == .kw_self_val)
                    {
                        has_param_err = true;
                        const inout_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                        const fix_span = Span.init(
                            self.file_id,
                            self.getTokenSpan(amp_tok).start_byte,
                            self.getTokenSpan(inout_tok).end_byte,
                        );
                        try self.emitDiagnosticWithFix(
                            .e0221_retired_mutability_or_param_mode,
                            fix_span,
                            "`&inout self` receiver syntax has been retired; use `&mut self` instead",
                            "retired `&inout`; write `&mut`",
                            fix_span,
                            "&mut",
                            "replace `&inout` with `&mut`",
                        );
                    }
                } else if (is_own_self) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else if (is_mut_self) {
                    has_param_err = true;
                    const mut_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    const self_tok = try self.consumeLeaf(.token_leaf, .{});
                    const fix_span = Span.init(
                        self.file_id,
                        self.getTokenSpan(mut_tok).start_byte,
                        self.getTokenSpan(self_tok).end_byte,
                    );
                    try self.emitDiagnosticWithFix(
                        .e0221_retired_mutability_or_param_mode,
                        fix_span,
                        "`mut self` receiver syntax has been retired; use `&mut self` for mutable borrow or `var self` for mutable value copy",
                        "retired `mut self`; write `&mut self`",
                        fix_span,
                        "&mut self",
                        "replace `mut self` with `&mut self`",
                    );
                    if (self.peekKind() == .colon) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        try self.consumeRetiredPostColonParamMode(&has_param_err);
                        _ = try self.parseType();
                    }
                    self.cst.finishNode(param_cst, .{ .has_error = true });
                    has_error.* = true;
                    if (self.peekKind() == .comma) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else if (self.peekKind() != .rparen) {
                        break;
                    }
                    continue;
                } else if (is_ref_self) {
                    has_param_err = true;
                    const ref_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    var is_ref_mut = false;
                    if (self.peekKind() == .kw_mut) {
                        is_ref_mut = true;
                        _ = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    }
                    const self_tok = try self.consumeLeaf(.token_leaf, .{});
                    const fix_span = Span.init(
                        self.file_id,
                        self.getTokenSpan(ref_tok).start_byte,
                        self.getTokenSpan(self_tok).end_byte,
                    );
                    try self.emitDiagnosticWithFix(
                        .e0221_retired_mutability_or_param_mode,
                        fix_span,
                        "`ref self` receiver syntax has been retired; use `&self` or `&mut self` instead",
                        "retired `ref` receiver; use `&`",
                        fix_span,
                        if (is_ref_mut) "&mut self" else "&self",
                        if (is_ref_mut) "replace `ref mut self` with `&mut self`" else "replace `ref self` with `&self`",
                    );
                    if (self.peekKind() == .colon) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        try self.consumeRetiredPostColonParamMode(&has_param_err);
                        _ = try self.parseType();
                    }
                    self.cst.finishNode(param_cst, .{ .has_error = true });
                    has_error.* = true;
                    if (self.peekKind() == .comma) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else if (self.peekKind() != .rparen) {
                        break;
                    }
                    continue;
                } else if (is_inout_or_sink_self) {
                    has_param_err = true;
                    const is_inout_kw = peek0_retired_mode == .inout;
                    const mode_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    const self_tok = try self.consumeLeaf(.token_leaf, .{});
                    const fix_span = Span.init(
                        self.file_id,
                        self.getTokenSpan(mode_tok).start_byte,
                        self.getTokenSpan(self_tok).end_byte,
                    );
                    try self.emitDiagnosticWithFix(
                        .e0221_retired_mutability_or_param_mode,
                        fix_span,
                        if (is_inout_kw)
                            "`inout self` receiver syntax has been retired; use `&mut self` instead"
                        else
                            "`sink self` receiver syntax has been retired; use `own self` instead",
                        if (is_inout_kw) "retired `inout` receiver; use `&mut`" else "retired `sink` receiver; use `own`",
                        fix_span,
                        if (is_inout_kw) "&mut self" else "own self",
                        if (is_inout_kw) "replace `inout self` with `&mut self`" else "replace `sink self` with `own self`",
                    );
                    if (self.peekKind() == .colon) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        try self.consumeRetiredPostColonParamMode(&has_param_err);
                        _ = try self.parseType();
                    }
                    self.cst.finishNode(param_cst, .{ .has_error = true });
                    has_error.* = true;
                    if (self.peekKind() == .comma) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else if (self.peekKind() != .rparen) {
                        break;
                    }
                    continue;
                }

                _ = try self.expectToken(
                    .kw_self_val,
                    &has_param_err,
                    "expected `self` in receiver parameter",
                    "expected `self` here",
                );
                if (self.peekKind() == .colon) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    try self.consumeRetiredPostColonParamMode(&has_param_err);
                    _ = try self.parseType();
                }
            } else {
                // Handle retired leading parameter modifiers (`mut`/`own`/`ref`/`inout`/`set`/`out`/`sink x: T`) -> `E0221`:
                var opt_retired_own_tok: ?TokenIndex = null;
                var opt_retired_ref_tok: ?TokenIndex = null;
                var opt_retired_mode_kind: ?RetiredParamModeKind = null;
                var is_retired_ref_mut = false;

                if (self.peekKind() == .kw_mut) {
                    has_param_err = true;
                    const mut_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    const mut_span = self.getTokenSpan(mut_tok);
                    try self.emitDiagnosticWithFix(
                        .e0221_retired_mutability_or_param_mode,
                        mut_span,
                        "`mut` parameter binding modifier has been retired; use `var` for local rebinding or `&mut T` for mutable reference",
                        "retired `mut` before parameter name; write `var`",
                        mut_span,
                        "var",
                        "replace `mut` with `var`",
                    );
                } else if (self.peekKind() == .kw_own) {
                    has_param_err = true;
                    opt_retired_own_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    if (self.peekKind() == .kw_mut) {
                        has_leading_var = true;
                        _ = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    }
                } else if (peek0_retired_mode) |retired_kind| {
                    const is_leading_retired_mode = switch (retired_kind) {
                        .ref => self.peekKindNth(1) == .kw_mut or
                            isIdentifierKind(self.peekKindNth(1)) or
                            self.peekKindNth(1) == .underscore,
                        .inout, .out, .set, .sink => (isIdentifierKind(self.peekKindNth(1)) or
                            self.peekKindNth(1) == .underscore) and
                            self.peekKindNth(2) == .colon,
                        .yielded => false,
                    };
                    if (is_leading_retired_mode) {
                        has_param_err = true;
                        opt_retired_mode_kind = retired_kind;
                        opt_retired_ref_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                        if (retired_kind == .ref and self.peekKind() == .kw_mut) {
                            is_retired_ref_mut = true;
                            _ = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                        }
                    }
                }

                if (isIdentifierKind(self.peekKind()) or self.peekKind() == .underscore) {
                    const name_tok = if (self.peekKind() == .underscore)
                        try self.consumeLeaf(.token_leaf, .{})
                    else
                        try self.expectIdentifierWithCasing(
                            .ident,
                            .snake_case,
                            &has_param_err,
                            "expected `snake_case` parameter name",
                        );
                    _ = try self.expectToken(
                        .colon,
                        &has_param_err,
                        "expected `:` and parameter type after parameter name",
                        "expected `:` here",
                    );
                    try self.consumeRetiredPostColonParamMode(&has_param_err);
                    const ty_start_tok = self.peekTokenIndexNth(0);
                    _ = try self.parseType();
                    const ty_end_tok = if (self.cursor > 0)
                        TokenIndex.fromInt(self.cursor - 1)
                    else
                        ty_start_tok;

                    if (opt_retired_own_tok) |own_tok| {
                        const own_span = self.getTokenSpan(own_tok);
                        const ty_end_span = self.getTokenSpan(ty_end_tok);
                        const full_span = Span.init(self.file_id, own_span.start_byte, ty_end_span.end_byte);
                        var opt_rep: ?[]const u8 = null;
                        if (self.diagnostic_sink) |sink| {
                            const name_lex = self.getTokenLexeme(name_tok);
                            const ty_start_span = self.getTokenSpan(ty_start_tok);
                            if (ty_start_span.start_byte <= ty_end_span.end_byte and ty_end_span.end_byte <= self.source.len) {
                                const ty_lex = std.mem.trim(
                                    u8,
                                    self.source[ty_start_span.start_byte..ty_end_span.end_byte],
                                    " \t\r\n",
                                );
                                if (name_lex.len > 0 and ty_lex.len > 0) {
                                    opt_rep = if (has_leading_var)
                                        try std.fmt.allocPrint(sink.arena.asAllocator(), "var {s}: own {s}", .{ name_lex, ty_lex })
                                    else
                                        try std.fmt.allocPrint(sink.arena.asAllocator(), "{s}: own {s}", .{ name_lex, ty_lex });
                                }
                            }
                        }
                        try self.emitDiagnosticWithFix(
                            .e0221_retired_mutability_or_param_mode,
                            full_span,
                            "`own x: T` parameter syntax has been retired; place `own` on the type as `x: own T` (`[var] x: own T` if rebound)",
                            "retired leading `own`; write `x: own T`",
                            full_span,
                            opt_rep,
                            "move `own` to the parameter type",
                        );
                    } else if (opt_retired_ref_tok) |ref_tok| {
                        const ref_span = self.getTokenSpan(ref_tok);
                        const ty_end_span = self.getTokenSpan(ty_end_tok);
                        const full_span = Span.init(self.file_id, ref_span.start_byte, ty_end_span.end_byte);
                        var opt_rep: ?[]const u8 = null;
                        if (self.diagnostic_sink) |sink| {
                            const name_lex = self.getTokenLexeme(name_tok);
                            const ty_start_span = self.getTokenSpan(ty_start_tok);
                            if (ty_start_span.start_byte <= ty_end_span.end_byte and ty_end_span.end_byte <= self.source.len) {
                                const ty_lex = std.mem.trim(
                                    u8,
                                    self.source[ty_start_span.start_byte..ty_end_span.end_byte],
                                    " \t\r\n",
                                );
                                if (name_lex.len > 0 and ty_lex.len > 0) {
                                    const sink_alloc = sink.arena.asAllocator();
                                    opt_rep = switch (opt_retired_mode_kind orelse .ref) {
                                        .inout, .yielded => try std.fmt.allocPrint(
                                            sink_alloc,
                                            "{s}: &mut {s}",
                                            .{ name_lex, ty_lex },
                                        ),
                                        .out, .set => try std.fmt.allocPrint(
                                            sink_alloc,
                                            "{s}: &out {s}",
                                            .{ name_lex, ty_lex },
                                        ),
                                        .sink => if (has_leading_var)
                                            try std.fmt.allocPrint(
                                                sink_alloc,
                                                "var {s}: own {s}",
                                                .{ name_lex, ty_lex },
                                            )
                                        else
                                            try std.fmt.allocPrint(
                                                sink_alloc,
                                                "{s}: own {s}",
                                                .{ name_lex, ty_lex },
                                            ),
                                        .ref => if (is_retired_ref_mut)
                                            try std.fmt.allocPrint(
                                                sink_alloc,
                                                "{s}: &mut {s}",
                                                .{ name_lex, ty_lex },
                                            )
                                        else
                                            try std.fmt.allocPrint(
                                                sink_alloc,
                                                "{s}: &{s}",
                                                .{ name_lex, ty_lex },
                                            ),
                                    };
                                }
                            }
                        }
                        try self.emitDiagnosticWithFix(
                            .e0221_retired_mutability_or_param_mode,
                            full_span,
                            "leading parameter mode modifier has been retired; place `&`, `&mut`, `&out`, or `own` on the parameter type",
                            "retired leading parameter mode modifier",
                            full_span,
                            opt_rep,
                            "move parameter mode onto the parameter type",
                        );
                    }

                    if (!has_seen_slash) non_self_before_slash += 1;
                    if (has_seen_star) params_after_star += 1;

                    if (self.peekKind() == .eq) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        const saved_cond_header = self.is_in_cond_header;
                        self.is_in_cond_header = false;
                        _ = try self.parseExpr(true);
                        self.is_in_cond_header = saved_cond_header;
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

        if (has_seen_star and params_after_star == 0) {
            has_error.* = true;
            try self.emitDiagnosticWithFix(
                .e0228_invalid_param_zone_separator,
                last_star_span,
                "`*` keyword-only parameter separator must be followed by at least one keyword-only parameter",
                "empty keyword-only parameter zone after `*`",
                null,
                null,
                null,
            );
        }

        try self.expectClosingDelimiter(
            .rparen,
            open_paren,
            has_error,
            "expected `)` to close parameter list",
        );
        self.cst.finishNode(list_cst, .{ .has_error = has_error.* });
    }

    /// Diagnoses and recovers from retired post-`:` parameter modes (`inout`, `sink`, `set`, `let`, `yielded`).
    fn consumeRetiredPostColonParamMode(self: *Parser, has_param_err: *bool) !void {
        if (self.peekKind() == .kw_let) {
            has_param_err.* = true;
            const let_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            const next_span = self.getTokenSpan(self.peekTokenIndexNth(0));
            const let_span = self.getTokenSpan(let_tok);
            const fix_span = Span.init(self.file_id, let_span.start_byte, @max(let_span.end_byte, next_span.start_byte));
            try self.emitDiagnosticWithFix(
                .e0221_retired_mutability_or_param_mode,
                let_span,
                "explicit `let` parameter convention keyword has been retired; bare `x: T` is immutable by default",
                "retired `let` parameter mode",
                fix_span,
                "",
                "remove retired `let` mode keyword",
            );
            return;
        }
        if (self.peekKind() != .ident) return;
        const next_kind = self.peekKindNth(1);
        if (next_kind == .dot or next_kind == .comma or next_kind == .rparen or next_kind == .eq) return;
        if (!TYPE_STARTER_SET.contains(next_kind)) return;

        var opt_replacement: ?[]const u8 = null;
        var opt_msg: ?[]const u8 = null;
        if (RETIRED_PARAM_MODE_MAP.get(self.peekLexemeNth(0))) |retired_kind| {
            switch (retired_kind) {
                .inout => {
                    opt_replacement = "&mut ";
                    opt_msg = "`inout` parameter mode has been retired; write `&mut T` instead";
                },
                .sink => {
                    opt_replacement = "own ";
                    opt_msg = "`sink` parameter mode has been retired; write `own T` instead";
                },
                .set => {
                    opt_replacement = "&out ";
                    opt_msg = "`set` parameter mode has been retired; write `&out T` instead";
                },
                .yielded => {
                    opt_replacement = "&mut ";
                    opt_msg = "`yielded` parameter mode has been retired; write `&mut T` instead";
                },
                .out, .ref => {},
            }
        }

        if (opt_replacement) |rep_text| {
            has_param_err.* = true;
            const mode_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            const mode_span = self.getTokenSpan(mode_tok);
            const next_span = self.getTokenSpan(self.peekTokenIndexNth(0));
            const fix_span = Span.init(
                self.file_id,
                mode_span.start_byte,
                @max(mode_span.end_byte, next_span.start_byte),
            );
            try self.emitDiagnosticWithFix(
                .e0221_retired_mutability_or_param_mode,
                mode_span,
                opt_msg.?,
                "retired parameter convention keyword",
                fix_span,
                rep_text,
                "replace retired parameter mode with canonical `DR-22` type",
            );
        }
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
                    _ = try self.parseConstraintExpr(&has_param_err);
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

    /// Parses `IntersectBound = Type { "+" Type }` (`SE-09`).
    fn parseIntersectBound(self: *Parser, mode: TypeRefinementMode) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const ast_start = self.ast.countNodes();

        const first_ty = try self.parseTypeWithMode(mode);
        if (self.peekKind() != .plus) return first_ty;

        const first_plus_tok = self.peekTokenIndexNth(0);
        _ = try self.precedeNode(cst_start, ast_start, .intersect_bound_type, first_plus_tok);

        var members: std.ArrayList(u32) = .empty;
        defer members.deinit(self.ast.allocator);
        try members.append(self.ast.allocator, first_ty.asInt());

        while (self.peekKind() == .plus) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            try members.append(self.ast.allocator, (try self.parseTypeWithMode(mode)).asInt());
        }
        self.cst.finishNode(cst_start, .{});

        const extra_start = try self.ast.appendExtraSlice(members.items);
        return self.ast.appendNodeWithCst(.{
            .tag = .intersect_bound_type,
            .main_token = first_plus_tok,
            .lhs = PackedOperand.initExtra(extra_start),
            .rhs = .{ .tag = .extra, .payload = @intCast(members.items.len) },
        }, cst_start);
    }

    /// Parses `ConstraintExpr = IntersectBound { "|" IntersectBound }` (`SE-09`).
    fn parseConstraintExpr(self: *Parser, has_error: *bool) anyerror!NodeIndex {
        _ = has_error;
        try self.flushCarrierTokens();
        const cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const ast_start = self.ast.countNodes();

        const first_bound = try self.parseIntersectBound(.is_only);
        if (self.peekKind() != .pipe) return first_bound;

        const first_pipe_tok = self.peekTokenIndexNth(0);
        _ = try self.precedeNode(cst_start, ast_start, .union_bound_type, first_pipe_tok);

        var members: std.ArrayList(u32) = .empty;
        defer members.deinit(self.ast.allocator);
        try members.append(self.ast.allocator, first_bound.asInt());

        while (self.peekKind() == .pipe) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            try members.append(self.ast.allocator, (try self.parseIntersectBound(.is_only)).asInt());
        }
        self.cst.finishNode(cst_start, .{});

        const extra_start = try self.ast.appendExtraSlice(members.items);
        return self.ast.appendNodeWithCst(.{
            .tag = .union_bound_type,
            .main_token = first_pipe_tok,
            .lhs = PackedOperand.initExtra(extra_start),
            .rhs = .{ .tag = .extra, .payload = @intCast(members.items.len) },
        }, cst_start);
    }

    /// Parses `WhereClause = "where" WherePred { "," WherePred } [ "," ] ;`.
    fn parseWhereClause(self: *Parser, has_error: *bool) anyerror!void {
        const where_cst = try self.startCstNode(.where_clause);
        _ = try self.consumeLeaf(.where_clause_start, .{});

        while (self.peekKind() != .lbrace and
            self.peekKind() != .eq and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const pred_cst = try self.startCstNode(.where_pred);
            _ = try self.parseTypeWithMode(.none);
            _ = try self.expectToken(
                .colon,
                has_error,
                "expected `:` in `where` clause predicate",
                "expected `:` before trait bounds",
            );
            _ = try self.parseConstraintExpr(has_error);
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

    /// Returns `true` if `peek(start_lookahead)` starts a `SliceRefType` (`&[T]` or `&mut [T]`, excluding `&[T; N]`).
    fn isSliceRefTypeAt(self: *const Parser, start_lookahead: usize) bool {
        if (self.peekKindNth(start_lookahead) != .amp) return false;
        const bracket_off: usize = if (self.peekKindNth(start_lookahead + 1) == .kw_mut)
            start_lookahead + 2
        else
            start_lookahead + 1;
        if (self.peekKindNth(bracket_off) != .lbracket) return false;

        var scan_off: usize = bracket_off + 1;
        var steps: usize = 0;
        var bracket_depth: u32 = 1;
        var paren_depth: u32 = 0;
        while (steps < MAX_TYPE_LOOKAHEAD) : (steps += 1) {
            const cur_kind = self.peekKindNth(scan_off);
            if (cur_kind == .eof) return false;
            if (bracket_depth == 1 and paren_depth == 0) {
                if (cur_kind == .semi) return false;
                if (cur_kind == .rbracket) return true;
            }
            if (cur_kind == .lbracket) {
                bracket_depth += 1;
            } else if (cur_kind == .rbracket) {
                if (bracket_depth == 0) return false;
                bracket_depth -= 1;
            } else if (cur_kind == .lparen) {
                paren_depth += 1;
            } else if (cur_kind == .rparen) {
                if (paren_depth > 0) paren_depth -= 1;
            }
            scan_off += 1;
        }
        return true;
    }

    /// Returns `true` if `peek(start_lookahead)` starts an `own` closure type (`own [async] |…|`).
    fn isOwnClosureTypeAt(self: *const Parser, start_lookahead: usize) bool {
        if (self.peekKindNth(start_lookahead) != .kw_own) return false;
        const next_kind = self.peekKindNth(start_lookahead + 1);
        if (next_kind == .pipe or next_kind == .pipepipe) return true;
        if (next_kind == .kw_async) {
            const after_async = self.peekKindNth(start_lookahead + 2);
            return after_async == .pipe or after_async == .pipepipe;
        }
        return false;
    }

    /// Parses a unified 4-tier `Type` expression (`DR-22` Sections 1.3 & 3.3).
    pub fn parseType(self: *Parser) anyerror!NodeIndex {
        return self.parseTypeWithMode(.all);
    }

    /// Parses Tier 1 (`T ! E` + optional `is`/`where` refinement) over Tier 2–4 types (`ADR-22C`).
    fn parseTypeWithMode(self: *Parser, refinement_mode: TypeRefinementMode) anyerror!NodeIndex {
        const saved_cond_header = self.is_in_cond_header;
        self.is_in_cond_header = false;
        defer self.is_in_cond_header = saved_cond_header;

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
        defer self.popStates(1);

        var type_node = try self.parsePrefixOrPostfixType();

        // Tier 1 non-associative result type sugar (`Ok ! Err`, emitting `E0222` on `A ! B ! C`):
        if (!self.is_recovering_depth_overflow and self.peekKind() == .bang) {
            const bang_tok = self.peekTokenIndexNth(0);
            _ = try self.precedeNode(type_cst_start, type_ast_start, .result_type, bang_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const err_ty = try self.parsePrefixOrPostfixType();

            var has_chain_err = false;
            while (!self.is_recovering_depth_overflow and self.peekKind() == .bang) {
                has_chain_err = true;
                const extra_bang = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                const extra_span = self.getTokenSpan(extra_bang);
                try self.emitDiagnosticWithFix(
                    .e0222_chained_result_type,
                    extra_span,
                    "result type operator `!` is non-associative; parenthesize nested result types explicitly as `(A ! B) ! C` or `A ! (B ! C)`",
                    "chained `!` in result type requires explicit parentheses",
                    null,
                    null,
                    null,
                );
                _ = try self.parsePrefixOrPostfixType();
            }

            self.cst.finishNode(type_cst_start, .{ .has_error = has_chain_err });
            type_node = try self.ast.appendNodeWithCst(.{
                .tag = .result_type,
                .main_token = bang_tok,
                .lhs = PackedOperand.initNode(type_node),
                .rhs = PackedOperand.initNode(err_ty),
            }, type_cst_start);
        }

        // Optional refinement clause (`Type is SinglePatternNoStruct` or `Type where Expr`):
        const has_consumable_is = refinement_mode != .none and self.peekKind() == .kw_is;
        const has_consumable_where = refinement_mode == .all and self.peekKind() == .kw_where;
        if (!self.is_recovering_depth_overflow and (has_consumable_is or has_consumable_where)) {
            const ref_tok = self.peekTokenIndexNth(0);
            _ = try self.precedeNode(type_cst_start, type_ast_start, .refined_type, ref_tok);
            const ref_kind = self.peekKind();
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (ref_kind == .kw_is) {
                _ = try self.parsePatternWithOptions(false, false);
            } else {
                _ = try self.parseExpr(false);
            }
            self.cst.finishNode(type_cst_start, .{});
        }
        return type_node;
    }

    /// Parses Tier 2 (`&PostfixType`, `&mut PostfixType`, `&out PostfixType`, `own PostfixType`) or Tier 3.
    fn parsePrefixOrPostfixType(self: *Parser) anyerror!NodeIndex {
        if (self.peekKind() == .amp and !self.isSliceRefTypeAt(0)) {
            const ref_cst = try self.startCstNode(.ref_type);
            self.pushState(.type_parse, ref_cst) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    return self.recoverDepthOverflow(ref_cst, TYPE_ARG_STOP_SET, .type_hole);
                },
                else => return err,
            };
            defer self.popStates(1);

            var has_ref_err = false;
            const amp_tok = try self.consumeLeaf(.token_leaf, .{});
            var main_tok = amp_tok;

            if (self.peekKind() == .kw_mut) {
                main_tok = try self.consumeLeaf(.token_leaf, .{});
            } else if (self.peekKind() == .ident and
                std.mem.eql(u8, self.peekLexemeNth(0), "out") and
                self.peekKindNth(1) != .dot and
                TYPE_STARTER_SET.contains(self.peekKindNth(1)))
            {
                main_tok = try self.consumeLeaf(.token_leaf, .{});
            } else if (self.peekKind() == .ident and
                std.mem.eql(u8, self.peekLexemeNth(0), "inout") and
                self.peekKindNth(1) != .dot and
                TYPE_STARTER_SET.contains(self.peekKindNth(1)))
            {
                has_ref_err = true;
                const inout_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                main_tok = inout_tok;
                const fix_span = Span.init(
                    self.file_id,
                    self.getTokenSpan(amp_tok).start_byte,
                    self.getTokenSpan(inout_tok).end_byte,
                );
                try self.emitDiagnosticWithFix(
                    .e0221_retired_mutability_or_param_mode,
                    fix_span,
                    "`&inout T` type syntax has been retired; write `&mut T` instead",
                    "retired `&inout`; write `&mut`",
                    fix_span,
                    "&mut",
                    "replace `&inout` with `&mut`",
                );
            } else if (self.peekKind() == .kw_let) {
                has_ref_err = true;
                const let_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                const next_span = self.getTokenSpan(self.peekTokenIndexNth(0));
                const fix_span = Span.init(
                    self.file_id,
                    self.getTokenSpan(amp_tok).start_byte,
                    @max(self.getTokenSpan(let_tok).end_byte, next_span.start_byte),
                );
                try self.emitDiagnosticWithFix(
                    .e0221_retired_mutability_or_param_mode,
                    fix_span,
                    "`&let T` type syntax has been retired; write `&T` instead",
                    "retired `&let`; write `&`",
                    fix_span,
                    "&",
                    "replace `&let ` with `&`",
                );
            }

            const inner_ty = try self.parsePrefixOrPostfixType();
            self.cst.finishNode(ref_cst, .{ .has_error = has_ref_err });
            return self.ast.appendNodeWithCst(.{
                .tag = .ref_type,
                .main_token = main_tok,
                .lhs = PackedOperand.initNode(inner_ty),
            }, ref_cst);
        }

        if (self.peekKind() == .kw_own and !self.isOwnClosureTypeAt(0)) {
            const mode_cst = try self.startCstNode(.mode_type);
            self.pushState(.type_parse, mode_cst) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    return self.recoverDepthOverflow(mode_cst, TYPE_ARG_STOP_SET, .type_hole);
                },
                else => return err,
            };
            defer self.popStates(1);

            const own_tok = try self.consumeLeaf(.token_leaf, .{});
            const inner_ty = try self.parsePrefixOrPostfixType();
            self.cst.finishNode(mode_cst, .{});
            return self.ast.appendNodeWithCst(.{
                .tag = .mode_type,
                .main_token = own_tok,
                .lhs = PackedOperand.initNode(inner_ty),
            }, mode_cst);
        }

        // Recover retired `ref T` / `ref mut T` in type position with `E0221`:
        if (self.peekKind() == .ident and
            std.mem.eql(u8, self.peekLexemeNth(0), "ref") and
            (self.peekKindNth(1) == .kw_mut or
                (self.peekKindNth(1) != .dot and TYPE_STARTER_SET.contains(self.peekKindNth(1)))))
        {
            const ref_cst = try self.startCstNode(.ref_type);
            self.pushState(.type_parse, ref_cst) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    return self.recoverDepthOverflow(ref_cst, TYPE_ARG_STOP_SET, .type_hole);
                },
                else => return err,
            };
            defer self.popStates(1);
            const ref_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            var main_tok = ref_tok;
            var is_mut = false;
            if (self.peekKind() == .kw_mut) {
                is_mut = true;
                main_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            }
            const next_span = self.getTokenSpan(self.peekTokenIndexNth(0));
            const ref_span = self.getTokenSpan(ref_tok);
            const end_span = self.getTokenSpan(main_tok);
            const fix_span = Span.init(
                self.file_id,
                ref_span.start_byte,
                @max(end_span.end_byte, next_span.start_byte),
            );
            try self.emitDiagnosticWithFix(
                .e0221_retired_mutability_or_param_mode,
                Span.init(self.file_id, ref_span.start_byte, end_span.end_byte),
                "`ref` reference type keyword has been retired; write `&T` or `&mut T` instead",
                "retired `ref` type syntax",
                fix_span,
                if (is_mut) "&mut " else "&",
                if (is_mut) "replace `ref mut ` with `&mut `" else "replace `ref ` with `&`",
            );
            const inner_ty = try self.parsePrefixOrPostfixType();
            self.cst.finishNode(ref_cst, .{ .has_error = true });
            return self.ast.appendNodeWithCst(.{
                .tag = .ref_type,
                .main_token = main_tok,
                .lhs = PackedOperand.initNode(inner_ty),
            }, ref_cst);
        }

        return self.parsePostfixType();
    }

    /// Parses Tier 3 (`PostfixType = PrimaryType { "?" } ;`, binding tighter than `&`, `own`, and `!`).
    fn parsePostfixType(self: *Parser) anyerror!NodeIndex {
        try self.flushCarrierTokens();
        const type_cst_start = CstNodeIndex.fromInt(@intCast(self.cst.countNodes()));
        const type_ast_start = self.ast.countNodes();

        var chain_pushes: usize = 0;
        defer self.popStates(chain_pushes);

        var type_node = try self.parsePrimaryType();

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

    /// Parses Tier 4 `PrimaryType` (`DR-22` Section 3.3, including `&[T]`, `*T`, `*mut T`, `FnType`, `ClosureType`).
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
            .amp => {
                const ref_cst = try self.startCstNode(.ref_type);
                self.pushState(.type_parse, ref_cst) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(ref_cst, TYPE_ARG_STOP_SET, .type_hole);
                    },
                    else => return err,
                };
                defer self.popStates(1);
                const amp_tok = try self.consumeLeaf(.token_leaf, .{});
                const main_tok = if (self.peekKind() == .kw_mut)
                    try self.consumeLeaf(.token_leaf, .{})
                else
                    amp_tok;
                const inner_ty = if (self.peekKind() == .lbracket)
                    try self.parsePrimaryType()
                else
                    try self.parsePrefixOrPostfixType();
                self.cst.finishNode(ref_cst, .{});
                return self.ast.appendNodeWithCst(.{
                    .tag = .ref_type,
                    .main_token = main_tok,
                    .lhs = PackedOperand.initNode(inner_ty),
                }, ref_cst);
            },
            .star => {
                const ptr_cst = try self.startCstNode(.ptr_type);
                self.pushState(.type_parse, ptr_cst) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(ptr_cst, TYPE_ARG_STOP_SET, .type_hole);
                    },
                    else => return err,
                };
                defer self.popStates(1);

                var has_ptr_err = false;
                const star_tok = try self.consumeLeaf(.token_leaf, .{});
                var main_tok = star_tok;
                if (self.peekKind() == .kw_mut) {
                    main_tok = try self.consumeLeaf(.token_leaf, .{});
                } else if (self.peekKind() == .kw_const) {
                    has_ptr_err = true;
                    const const_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    const star_span = self.getTokenSpan(star_tok);
                    const const_span = self.getTokenSpan(const_tok);
                    const next_span = self.getTokenSpan(self.peekTokenIndexNth(0));
                    const diag_span = Span.init(self.file_id, star_span.start_byte, const_span.end_byte);
                    const fix_span = Span.init(
                        self.file_id,
                        star_span.start_byte,
                        @max(const_span.end_byte, next_span.start_byte),
                    );
                    try self.emitDiagnosticWithFix(
                        .e0226_retired_const_raw_ptr,
                        diag_span,
                        "`*const T` raw pointer spelling has been retired; bare `*T` is const by default (`*mut T` for mutable)",
                        "retired `*const T`; write `*T`",
                        fix_span,
                        "*",
                        "replace `*const ` with `*`",
                    );
                }
                const inner_ty = try self.parsePrimaryType();
                self.cst.finishNode(ptr_cst, .{ .has_error = has_ptr_err });
                return self.ast.appendNodeWithCst(.{
                    .tag = .ptr_type,
                    .main_token = main_tok,
                    .lhs = PackedOperand.initNode(inner_ty),
                }, ptr_cst);
            },
            .hash_soa, .tilde => {
                const mode_cst = try self.startCstNode(.mode_type);
                self.pushState(.type_parse, mode_cst) catch |err| switch (err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(mode_cst, TYPE_ARG_STOP_SET, .type_hole);
                    },
                    else => return err,
                };
                defer self.popStates(1);
                const mode_kind = self.peekKind();
                const mode_tok = try self.consumeLeaf(.token_leaf, .{});
                const inner_ty = if (mode_kind == .hash_soa)
                    try self.parsePrimaryType()
                else
                    try self.parsePrefixOrPostfixType();
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
            .at, .pipe, .pipepipe, .kw_own, .kw_async, .kw_unsafe, .kw_extern, .kw_fn => {
                if (self.peekKind() == .kw_async and self.peekKindNth(1) == .dot) {
                    return self.parseNamedOrGenericType();
                }
                if (self.peekKind() == .kw_own and !self.isOwnClosureTypeAt(0)) {
                    const mode_cst = try self.startCstNode(.mode_type);
                    self.pushState(.type_parse, mode_cst) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            return self.recoverDepthOverflow(mode_cst, TYPE_ARG_STOP_SET, .type_hole);
                        },
                        else => return err,
                    };
                    defer self.popStates(1);
                    const own_tok = try self.consumeLeaf(.token_leaf, .{});
                    const inner_ty = try self.parsePrefixOrPostfixType();
                    self.cst.finishNode(mode_cst, .{});
                    return self.ast.appendNodeWithCst(.{
                        .tag = .mode_type,
                        .main_token = own_tok,
                        .lhs = PackedOperand.initNode(inner_ty),
                    }, mode_cst);
                }

                const callable_cst = try self.startCstNode(.fn_type);
                var has_err = false;
                if (self.peekKind() == .at) {
                    try self.parseAttributes(&has_err);
                }

                // Check for `ClosureType = { Attribute } [ "own" ] [ "async" ] ( "||" | "|" … "|" ) [ "->" Type ]`:
                const is_closure_after_attrs = self.peekKind() == .pipe or
                    self.peekKind() == .pipepipe or
                    self.isOwnClosureTypeAt(0) or
                    (self.peekKind() == .kw_async and
                        (self.peekKindNth(1) == .pipe or self.peekKindNth(1) == .pipepipe));

                if (is_closure_after_attrs) {
                    self.cst.nodes.items(.kind)[callable_cst.asInt()] = .closure_type;
                    if (self.peekKind() == .kw_own) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                    if (self.peekKind() == .kw_async) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                    const open_tok = try self.consumeLeaf(.token_leaf, .{});
                    var param_types: std.ArrayList(u32) = .empty;
                    defer param_types.deinit(self.ast.allocator);

                    if (self.token_buffer.getToken(open_tok).kind == .pipe) {
                        while (self.peekKind() != .pipe and
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
                            .pipe,
                            open_tok,
                            &has_err,
                            "expected `|` to close closure type parameters",
                        );
                    }

                    var ret_op: PackedOperand = .NONE;
                    if (self.peekKind() == .arrow) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        ret_op = PackedOperand.initNode(try self.parseType());
                    }
                    self.cst.finishNode(callable_cst, .{ .has_error = has_err });
                    var rhs_op: PackedOperand = .NONE;
                    if (param_types.items.len > 0) {
                        rhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(param_types.items));
                    }
                    return self.ast.appendNodeWithCst(.{
                        .tag = .closure_type,
                        .main_token = open_tok,
                        .lhs = ret_op,
                        .rhs = rhs_op,
                    }, callable_cst);
                }

                // Otherwise `FnType = { Attribute } [ "async" ] [ "unsafe" ] [ "extern" [ STRING_LIT ] ] "fn" "(" … ")" [ "->" Type ]`:
                while (self.peekKind() == .kw_async or
                    self.peekKind() == .kw_unsafe or
                    self.peekKind() == .kw_extern)
                {
                    const qual_kind = self.peekKind();
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    if (qual_kind == .kw_extern and self.peekKind() == .string_lit) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    }
                }
                const fn_tok = try self.expectToken(
                    .kw_fn,
                    &has_err,
                    "expected `fn` or `|…|` in callable type",
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
                        if (self.peekKind() == .dotdotdot) {
                            const var_cst = try self.startCstNode(.variadic_param);
                            _ = try self.consumeLeaf(.token_leaf, .{});
                            self.cst.finishNode(var_cst, .{});
                            if (self.peekKind() == .comma) {
                                _ = try self.consumeLeaf(.token_leaf, .{});
                            }
                            break;
                        }
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
                self.cst.finishNode(callable_cst, .{ .has_error = has_err });
                var lhs_op: PackedOperand = .NONE;
                if (param_types.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(param_types.items));
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .fn_type,
                    .main_token = fn_tok,
                    .lhs = lhs_op,
                    .rhs = ret_op,
                }, callable_cst);
            },
            .kw_self_type, .ident, .type_ident, .const_ident => {
                if (self.peekKind() == .kw_self_type and
                    self.peekKindNth(1) != .dot and
                    self.peekKindNth(1) != .lbracket)
                {
                    const tok = try self.consumeLeaf(.named_type, .{});
                    const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                    return self.ast.appendNodeWithCst(.{
                        .tag = .named_type,
                        .main_token = tok,
                    }, leaf_cst);
                }

                // Handle `dyn Trait`, `any Group`, or `distinct BaseType` modifier prefixes:
                if (self.peekKind() == .ident and
                    (std.mem.eql(u8, self.peekLexemeNth(0), "dyn") or
                        std.mem.eql(u8, self.peekLexemeNth(0), "any") or
                        std.mem.eql(u8, self.peekLexemeNth(0), "distinct")) and
                    TYPE_STARTER_SET.contains(self.peekKindNth(1)))
                {
                    const is_distinct = std.mem.eql(u8, self.peekLexemeNth(0), "distinct");
                    const mode_cst = try self.startCstNode(.mode_type);
                    self.pushState(.type_parse, mode_cst) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            return self.recoverDepthOverflow(mode_cst, TYPE_ARG_STOP_SET, .type_hole);
                        },
                        else => return err,
                    };
                    defer self.popStates(1);
                    const mode_tok = try self.consumeLeaf(.token_leaf, .{});
                    const inner_ty = if (is_distinct)
                        try self.parseType()
                    else
                        try self.parsePrimaryType();
                    self.cst.finishNode(mode_cst, .{});
                    return self.ast.appendNodeWithCst(.{
                        .tag = .mode_type,
                        .main_token = mode_tok,
                        .lhs = PackedOperand.initNode(inner_ty),
                    }, mode_cst);
                }

                return self.parseNamedOrGenericType();
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

    /// Parses a qualified/generic nominal `Type` (`{ (IDENT | "async") "." } TYPE_IDENT [TypeArgs] {"." TYPE_IDENT}`).
    fn parseNamedOrGenericType(self: *Parser) anyerror!NodeIndex {
        const named_cst = try self.startCstNode(.named_type);
        var has_err = false;
        var first_tok = self.peekTokenIndexNth(0);

        if (self.peekKind() == .kw_self_type) {
            first_tok = try self.consumeLeaf(.token_leaf, .{});
        } else {
            // Consume optional leading `(ident | "async") .` module path segments:
            while (isIdentOrModuleSegment(self.peekKind()) and self.peekKindNth(1) == .dot) {
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
        }

        var arg_nodes: std.ArrayList(u32) = .empty;
        defer arg_nodes.deinit(self.ast.allocator);
        var has_generic_args = false;

        while (true) {
            if (self.peekKind() == .lbracket) {
                has_generic_args = true;
                try self.parseTypeArgs(&arg_nodes, &has_err);
            }
            if (self.peekKind() == .dot and isIdentifierKind(self.peekKindNth(1))) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                _ = try self.expectIdentifierWithCasing(
                    .type_ident,
                    .pascal_case,
                    &has_err,
                    "expected `PascalCase` associated type name after `.`",
                );
                continue;
            }
            break;
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

        const saved_cond_header = self.is_in_cond_header;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_cond_header = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_cond_header = saved_cond_header;
            self.is_in_lhs_place = saved_lhs_place;
        }

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
            } else if (self.isTypeStart(0)) {
                try arg_nodes.append(self.ast.allocator, (try self.parseType()).asInt());
            } else {
                try arg_nodes.append(self.ast.allocator, (try self.parseExpr(false)).asInt());
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
        const saved_cond_header = self.is_in_cond_header;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_cond_header = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_cond_header = saved_cond_header;
            self.is_in_lhs_place = saved_lhs_place;
        }

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
            .kw_extern,
            .kw_use,
            .kw_defer,
            .kw_errdefer,
            .kw_yield,
            .kw_for,
            .kw_while,
            .kw_loop,
            .kw_match,
            .kw_with,
            .kw_comptime,
            => true,
            .ident => self.peekKindNth(lookahead + 1) == .colon,
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
            .kw_const, .kw_type, .kw_struct, .kw_enum, .kw_union, .kw_bit_field, .kw_fn, .kw_extern, .kw_use => true,
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
            const saved_allow_stmt = self.is_allowing_non_canonical_case;
            if (self.hasAllowNonCanonicalCaseAttr(decl_cst)) {
                self.is_allowing_non_canonical_case = true;
            }
            defer self.is_allowing_non_canonical_case = saved_allow_stmt;
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
            .kw_yield => return self.parseYieldStmt(),
            .kw_break => return self.parseBreakStmt(),
            .kw_continue => return self.parseContinueStmt(),
            .kw_comptime => {
                if (self.peekKindNth(1) == .kw_fn) {
                    return self.parseItem();
                }
            },
            .kw_const,
            .kw_type,
            .kw_struct,
            .kw_enum,
            .kw_union,
            .kw_bit_field,
            .kw_fn,
            .kw_extern,
            .kw_use,
            => {
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
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_stmt_lhs = true;
        self.is_in_lhs_place = true;
        const expr_node = blk_stmt_expr: {
            defer {
                self.is_in_stmt_lhs = saved_stmt_lhs;
                self.is_in_lhs_place = saved_lhs_place;
            }
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

    /// Parses `LocalDeclStmt = ("let" | "var") Pattern [":" Type] ["=" Expr ["else" Block]] ";" ;` (`ADR-22B`).
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
            has_error = true;
            const mut_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            const intro_span = Span.init(
                self.file_id,
                self.getTokenSpan(kw_tok).start_byte,
                self.getTokenSpan(mut_tok).end_byte,
            );
            try self.emitDiagnosticWithFix(
                .e0221_retired_mutability_or_param_mode,
                intro_span,
                "`let mut` / `var mut` has been retired (`ADR-22B`); write `var` for mutable local bindings",
                "retired `mut` local binding introducer",
                intro_span,
                "var",
                "replace with `var`",
            );
        }

        const pat_node = try self.parsePattern(true);

        var rhs_op: PackedOperand = .NONE;
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            rhs_op = PackedOperand.initNode(try self.parseType());
        }

        if (self.peekKind() == .colon_eq) {
            const walrus_tok = try self.consumeLeaf(.token_leaf, .{});
            try self.emitWalrusPositionError(
                self.getTokenSpan(walrus_tok),
                "`:=` is reserved for parenthesized `(x := expr)` condition bindings",
                "use `=` for local `let` / `var` declarations, or wrap `(x := expr)` inside an `if` or `while` header",
            );
            _ = try self.parseExpr(true);
            if (self.peekKind() == .semi) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                try self.skipToRecoveryAnchor(BLOCK_STMT_CONSUME_SET, LOCAL_INIT_STOP_SET, false);
            }
            self.cst.finishNode(decl_cst, .{ .has_error = true });
            return self.ast.appendNodeWithCst(.{
                .tag = .stmt_hole,
                .main_token = walrus_tok,
            }, decl_cst);
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
        if (isExprStart(self.peekKind(), true)) {
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

    /// Parses `YieldStmt = "yield" Expr ";" ;` (`SE-21`).
    fn parseYieldStmt(self: *Parser) anyerror!NodeIndex {
        const yield_cst = try self.startCstNode(.yield_stmt);
        var has_error = false;
        const yield_tok = try self.consumeLeaf(.token_leaf, .{});
        const val_expr = try self.parseExpr(true);
        _ = try self.expectToken(
            .semi,
            &has_error,
            "expected `;` after `yield` statement",
            "expected `;` here",
        );

        self.cst.finishNode(yield_cst, .{ .has_error = has_error });
        return self.ast.appendNodeWithCst(.{
            .tag = .yield_stmt,
            .main_token = yield_tok,
            .lhs = PackedOperand.initNode(val_expr),
        }, yield_cst);
    }

    /// Parses `BreakStmt = "break" [ ":" IDENT ] [ Expr ] ";" ;`.
    fn parseBreakStmt(self: *Parser) anyerror!NodeIndex {
        const brk_cst = try self.startCstNode(.break_stmt);
        var has_error = false;
        const brk_tok = try self.consumeLeaf(.break_introducer, .{});

        var label_op: PackedOperand = .NONE;
        if (self.peekKind() == .colon) {
            const label_cst = try self.startCstNode(.loop_label);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const label_tok = try self.expectIdentifierWithCasing(
                .ident,
                .snake_case,
                &has_error,
                "expected `snake_case` loop label after `:`",
            );
            self.cst.finishNode(label_cst, .{ .has_error = has_error });
            label_op = PackedOperand.initToken(label_tok);
        }

        var val_op: PackedOperand = .NONE;
        if (isExprStart(self.peekKind(), true)) {
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
            .rhs = label_op,
        }, brk_cst);
    }

    /// Parses `ContinueStmt = "continue" [ ":" IDENT ] [ Expr ] ";" ;` (`SE-23`).
    fn parseContinueStmt(self: *Parser) anyerror!NodeIndex {
        const cont_cst = try self.startCstNode(.continue_stmt);
        var has_error = false;
        const cont_tok = try self.consumeLeaf(.token_leaf, .{});

        var label_op: PackedOperand = .NONE;
        if (self.peekKind() == .colon) {
            const label_cst = try self.startCstNode(.loop_label);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const label_tok = try self.expectIdentifierWithCasing(
                .ident,
                .snake_case,
                &has_error,
                "expected `snake_case` loop or `match` label after `:`",
            );
            self.cst.finishNode(label_cst, .{ .has_error = has_error });
            label_op = PackedOperand.initToken(label_tok);
        }

        var val_op: PackedOperand = .NONE;
        if (isExprStart(self.peekKind(), true)) {
            val_op = PackedOperand.initNode(try self.parseExpr(true));
        }

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
            .lhs = label_op,
            .rhs = val_op,
        }, cont_cst);
    }

    /// Parses an expression-position diverging `return`, `break`, or `continue` without a trailing `;`.
    fn parseDivergingJumpExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        const div_cst = try self.startCstNode(.diverging_expr);
        var has_error = false;
        const saved_cond_header = self.is_in_cond_header;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_cond_header = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_cond_header = saved_cond_header;
            self.is_in_lhs_place = saved_lhs_place;
        }

        switch (self.peekKind()) {
            .kw_return => {
                const ret_tok = try self.consumeLeaf(.return_introducer, .{});
                var val_op: PackedOperand = .NONE;
                if (isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                    val_op = PackedOperand.initNode(try self.parseExpr(is_struct_lit_allowed));
                }
                self.cst.finishNode(div_cst, .{ .has_error = has_error });
                return self.ast.appendNodeWithCst(.{
                    .tag = .return_stmt,
                    .main_token = ret_tok,
                    .lhs = val_op,
                }, div_cst);
            },
            .kw_break => {
                const brk_tok = try self.consumeLeaf(.break_introducer, .{});
                var label_op: PackedOperand = .NONE;
                if (self.peekKind() == .colon) {
                    const label_cst = try self.startCstNode(.loop_label);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    const label_tok = try self.expectIdentifierWithCasing(
                        .ident,
                        .snake_case,
                        &has_error,
                        "expected `snake_case` loop label after `:`",
                    );
                    self.cst.finishNode(label_cst, .{ .has_error = has_error });
                    label_op = PackedOperand.initToken(label_tok);
                }
                var val_op: PackedOperand = .NONE;
                if (isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                    val_op = PackedOperand.initNode(try self.parseExpr(is_struct_lit_allowed));
                }
                self.cst.finishNode(div_cst, .{ .has_error = has_error });
                return self.ast.appendNodeWithCst(.{
                    .tag = .break_stmt,
                    .main_token = brk_tok,
                    .lhs = val_op,
                    .rhs = label_op,
                }, div_cst);
            },
            else => {
                const cont_tok = try self.consumeLeaf(.token_leaf, .{});
                var label_op: PackedOperand = .NONE;
                if (self.peekKind() == .colon) {
                    const label_cst = try self.startCstNode(.loop_label);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    const label_tok = try self.expectIdentifierWithCasing(
                        .ident,
                        .snake_case,
                        &has_error,
                        "expected `snake_case` loop or `match` label after `:`",
                    );
                    self.cst.finishNode(label_cst, .{ .has_error = has_error });
                    label_op = PackedOperand.initToken(label_tok);
                }
                var val_op: PackedOperand = .NONE;
                if (isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                    val_op = PackedOperand.initNode(try self.parseExpr(is_struct_lit_allowed));
                }
                self.cst.finishNode(div_cst, .{ .has_error = has_error });
                return self.ast.appendNodeWithCst(.{
                    .tag = .continue_stmt,
                    .main_token = cont_tok,
                    .lhs = label_op,
                    .rhs = val_op,
                }, div_cst);
            },
        }
    }

    /// Parses `ForExpr = [label ":"] ["comptime"] "for" ["&" ["mut"]] Pattern ["," IDENT] "in" ExprNoStruct Block`.
    fn parseForExpr(
        self: *Parser,
        opt_existing_cst: ?CstNodeIndex,
        label_tok: TokenIndex,
    ) anyerror!NodeIndex {
        const for_cst = opt_existing_cst orelse try self.startCstNode(.for_stmt);
        var has_error = false;
        var comptime_tok: TokenIndex = .none;
        if (self.peekKind() == .kw_comptime) {
            comptime_tok = try self.consumeLeaf(.token_leaf, .{});
        }
        const for_tok = try self.consumeLeaf(.for_introducer, .{});

        const header_cst = try self.startCstNode(.for_header);
        const saved_cond_header = self.is_in_cond_header;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_cond_header = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_cond_header = saved_cond_header;
            self.is_in_lhs_place = saved_lhs_place;
        }

        var ref_mode: u32 = 0;
        if (self.peekKind() == .amp) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .kw_mut) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                ref_mode = 2;
            } else {
                ref_mode = 1;
            }
        } else if (self.peekKind() == .ident and
            std.mem.eql(u8, self.peekLexemeNth(0), "ref") and
            (self.peekKindNth(1) == .kw_mut or
                self.peekKindNth(1) == .underscore or
                self.peekKindNth(1) == .lparen or
                self.peekKindNth(1) == .lbracket or
                isIdentifierKind(self.peekKindNth(1))))
        {
            has_error = true;
            const ref_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
            var end_mod_tok = ref_tok;
            if (self.peekKind() == .kw_mut) {
                end_mod_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                ref_mode = 2;
            } else {
                ref_mode = 1;
            }
            const ref_span = self.getTokenSpan(ref_tok);
            const end_span = self.getTokenSpan(end_mod_tok);
            const next_tok = self.peekTokenIndexNth(0);
            const next_span = self.getTokenSpan(next_tok);
            const has_only_spaces = blk_spaces: {
                for (self.token_buffer.getLeadingTrivia(next_tok)) |piece| {
                    if (piece.kind != .spaces) break :blk_spaces false;
                }
                break :blk_spaces !self.peekNth(0).flags.has_leading_newline;
            };
            const diag_span = Span.init(self.file_id, ref_span.start_byte, end_span.end_byte);
            const fix_end = if (has_only_spaces and next_span.start_byte >= end_span.end_byte)
                next_span.start_byte
            else
                end_span.end_byte;
            const replacement = if (ref_mode == 2)
                (if (fix_end > end_span.end_byte) "&mut " else "&mut")
            else
                "&";
            try self.emitDiagnosticWithFix(
                .e0221_retired_mutability_or_param_mode,
                diag_span,
                "`for ref` loop header modifier has been retired (`ADR-22B`); write `for &` or `for &mut` instead",
                "retired `ref` loop binding modifier",
                Span.init(self.file_id, ref_span.start_byte, fix_end),
                replacement,
                if (ref_mode == 2) "replace `ref mut` with `&mut`" else "replace `ref` with `&`",
            );
        }

        const pat_node = try self.parsePatternWithOptions(true, false);
        var index_tok: TokenIndex = .none;
        if (self.peekKind() == .comma) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .underscore) {
                index_tok = try self.consumeLeaf(.wildcard_pat, .{});
            } else {
                index_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_error,
                    "expected `snake_case` loop index identifier after `,`",
                );
            }
        }

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
        self.has_last_expr_block_body = true;

        const extra_words = [_]u32{
            pat_node.asInt(),
            iter_expr.asInt(),
            index_tok.asInt(),
            label_tok.asInt(),
            ref_mode,
        };
        const extra_idx = try self.ast.appendExtraSlice(&extra_words);
        return self.ast.appendNodeWithCst(.{
            .tag = .for_stmt,
            .main_token = if (!comptime_tok.isNone()) comptime_tok else for_tok,
            .lhs = PackedOperand.initExtra(extra_idx),
            .rhs = PackedOperand.initNode(body_block),
        }, for_cst);
    }

    /// Parses `WhileExpr = [label ":"] "while" CondExprNoStruct Block`.
    fn parseWhileExpr(
        self: *Parser,
        opt_existing_cst: ?CstNodeIndex,
        label_tok: TokenIndex,
    ) anyerror!NodeIndex {
        const while_cst = opt_existing_cst orelse try self.startCstNode(.while_stmt);
        var has_error = false;
        const while_tok = try self.consumeLeaf(.while_introducer, .{});

        const header_cst = try self.startCstNode(.while_header);
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_lhs_place = false;
        defer self.is_in_lhs_place = saved_lhs_place;
        var cond_node: NodeIndex = .none;
        if (self.peekKind() == .kw_let) {
            cond_node = try self.parseRetiredIfWhileLet(header_cst, "while", &has_error);
        } else {
            const saved_cond_header = self.is_in_cond_header;
            self.is_in_cond_header = true;
            cond_node = blk_cond: {
                defer self.is_in_cond_header = saved_cond_header;
                break :blk_cond try self.parseExpr(false);
            };
        }
        self.cst.finishNode(header_cst, .{ .has_error = has_error });

        const body_block = try self.parseBlock();
        self.cst.finishNode(while_cst, .{ .has_error = has_error });
        self.has_last_expr_block_body = true;

        const extra_words = [_]u32{ cond_node.asInt(), label_tok.asInt() };
        const extra_idx = try self.ast.appendExtraSlice(&extra_words);
        return self.ast.appendNodeWithCst(.{
            .tag = .while_stmt,
            .main_token = while_tok,
            .lhs = PackedOperand.initExtra(extra_idx),
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

        while (!self.is_recovering_depth_overflow and self.peekKind() == .pipe) {
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

    /// Consumes a mandatory upper-bound literal or qualified constant after `..` or `..=` in a pattern.
    fn consumePatternRangeEnd(self: *Parser, has_err: *bool) !TokenIndex {
        if (self.peekKind() == .minus) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .int_lit or self.peekKind() == .float_lit) {
                return self.consumeLeaf(.literal_pat, .{});
            }
            has_err.* = true;
            const err_tok = self.peekTokenIndexNth(0);
            try self.emitUnexpectedToken(
                err_tok,
                "expected numeric literal after `-` in range pattern",
                "expected numeric literal here",
            );
            return err_tok;
        }
        if (isLiteralToken(self.peekKind())) {
            return self.consumeLeaf(.literal_pat, .{});
        }
        if (isIdentifierKind(self.peekKind()) or self.peekKind() == .prim_type or self.peekKind() == .kw_self_type) {
            var end_tok = try self.consumeLeaf(.literal_pat, .{});
            while (self.peekKind() == .dot) {
                _ = try self.consumeLeaf(.token_leaf, .{});
                if (isIdentifierKind(self.peekKind())) {
                    end_tok = try self.consumeLeaf(.literal_pat, .{});
                } else {
                    has_err.* = true;
                    try self.emitUnexpectedToken(
                        self.peekTokenIndexNth(0),
                        "expected constant identifier after `.` in range pattern",
                        "missing range bound segment",
                    );
                    break;
                }
            }
            return end_tok;
        }
        has_err.* = true;
        const err_tok = self.peekTokenIndexNth(0);
        try self.emitUnexpectedToken(
            err_tok,
            "expected upper-bound pattern after range operator",
            "expected upper-bound literal or constant here",
        );
        return err_tok;
    }

    /// Returns `true` if `peek(lookahead)` starts a retired `ref [mut] ident` binding modifier (`ADR-22B`).
    fn isRetiredRefPatAt(self: *const Parser, lookahead: usize) bool {
        if (self.peekKindNth(lookahead) != .ident or
            !std.mem.eql(u8, self.peekLexemeNth(lookahead), "ref"))
        {
            return false;
        }
        const after_ref = self.peekKindNth(lookahead + 1);
        return after_ref == .kw_mut or after_ref == .underscore or isIdentifierKind(after_ref);
    }

    /// Consumes a canonical (`var`, `&`, `&mut`) or retired (`mut`, `own`, `ref [mut]`) pattern modifier (`ADR-22B`).
    fn consumePatternBindingModifier(self: *Parser, has_err: *bool) !TokenIndex {
        switch (self.peekKind()) {
            .kw_var => return self.consumeLeaf(.token_leaf, .{}),
            .amp => {
                const amp_tok = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                return amp_tok;
            },
            .kw_mut => {
                has_err.* = true;
                const mut_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                const mut_span = self.getTokenSpan(mut_tok);
                try self.emitDiagnosticWithFix(
                    .e0221_retired_mutability_or_param_mode,
                    mut_span,
                    "`mut` pattern binding modifier has been retired (`ADR-22B`); write `var` instead",
                    "retired `mut` pattern modifier; write `var`",
                    mut_span,
                    "var",
                    "replace `mut` with `var`",
                );
                return mut_tok;
            },
            .kw_own => {
                has_err.* = true;
                const own_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                const own_span = self.getTokenSpan(own_tok);
                const next_tok = self.peekTokenIndexNth(0);
                const next_span = self.getTokenSpan(next_tok);
                const has_only_spaces = blk_spaces: {
                    for (self.token_buffer.getLeadingTrivia(next_tok)) |piece| {
                        if (piece.kind != .spaces) break :blk_spaces false;
                    }
                    break :blk_spaces !self.peekNth(0).flags.has_leading_newline;
                };
                const fix_end = if (has_only_spaces and next_span.start_byte >= own_span.end_byte)
                    next_span.start_byte
                else
                    own_span.end_byte;
                try self.emitDiagnosticWithFix(
                    .e0221_retired_mutability_or_param_mode,
                    own_span,
                    "`own` pattern binding modifier has been retired (`ADR-22B`); bare pattern bindings move by default",
                    "retired `own` pattern modifier",
                    Span.init(self.file_id, own_span.start_byte, fix_end),
                    "",
                    "remove redundant `own` modifier",
                );
                return own_tok;
            },
            else => {
                has_err.* = true;
                const ref_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                var end_mod_tok = ref_tok;
                var is_mut = false;
                if (self.peekKind() == .kw_mut) {
                    is_mut = true;
                    end_mod_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                }
                const ref_span = self.getTokenSpan(ref_tok);
                const end_span = self.getTokenSpan(end_mod_tok);
                const next_tok = self.peekTokenIndexNth(0);
                const next_span = self.getTokenSpan(next_tok);
                const has_only_spaces = blk_spaces: {
                    for (self.token_buffer.getLeadingTrivia(next_tok)) |piece| {
                        if (piece.kind != .spaces) break :blk_spaces false;
                    }
                    break :blk_spaces !self.peekNth(0).flags.has_leading_newline;
                };
                const diag_span = Span.init(self.file_id, ref_span.start_byte, end_span.end_byte);
                const fix_end = if (has_only_spaces and next_span.start_byte >= end_span.end_byte)
                    next_span.start_byte
                else
                    end_span.end_byte;
                const replacement = if (is_mut)
                    (if (fix_end > end_span.end_byte) "&mut " else "&mut")
                else
                    "&";
                try self.emitDiagnosticWithFix(
                    .e0221_retired_mutability_or_param_mode,
                    diag_span,
                    "`ref` pattern binding modifier has been retired (`ADR-22B`); write `&` or `&mut` instead",
                    "retired `ref` pattern modifier",
                    Span.init(self.file_id, ref_span.start_byte, fix_end),
                    replacement,
                    if (is_mut) "replace `ref mut` with `&mut`" else "replace `ref` with `&`",
                );
                return ref_tok;
            },
        }
    }

    /// Parses a single pattern (`_`, literal/range, tuple, slice, `@`, binding, `.Variant`, or `PathPattern`).
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
            .dotdot, .dotdoteq => {
                const range_cst = try self.startCstNode(.range_pat);
                var has_err = false;
                const range_tok = try self.consumeLeaf(.token_leaf, .{});
                const end_tok = try self.consumePatternRangeEnd(&has_err);
                self.cst.finishNode(range_cst, .{ .has_error = has_err });
                return self.ast.appendNodeWithCst(.{
                    .tag = .lit_pat,
                    .main_token = range_tok,
                    .rhs = if (has_err) .NONE else PackedOperand.initToken(end_tok),
                }, range_cst);
            },
            .minus, .int_lit, .float_lit, .string_lit, .char_lit, .byte_lit, .byte_string_lit, .kw_true, .kw_false => {
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
                    var has_range_err = false;
                    const end_tok = try self.consumePatternRangeEnd(&has_range_err);
                    self.cst.finishNode(pat_cst_start, .{ .has_error = has_range_err });
                    if (!has_range_err) {
                        lit_node = try self.ast.appendNodeWithCst(.{
                            .tag = .lit_pat,
                            .main_token = range_tok,
                            .lhs = PackedOperand.initNode(lit_node),
                            .rhs = PackedOperand.initToken(end_tok),
                        }, pat_cst_start);
                    }
                }
                return lit_node;
            },
            .lparen => {
                const tup_cst = try self.startCstNode(.tuple_pat);
                var has_err = false;
                var has_comma = false;
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
                        (try self.parsePatternWithOptions(is_binding_slot, true)).asInt(),
                    );
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
                    "expected `)` to close tuple pattern",
                );
                self.cst.finishNode(tup_cst, .{ .has_error = has_err });
                if (sub_pats.items.len == 1 and !has_comma) {
                    return NodeIndex.fromInt(sub_pats.items[0]);
                }

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
            .lbracket => {
                const slice_cst = try self.startCstNode(.slice_pat);
                var has_err = false;
                const open_bracket = try self.consumeLeaf(.token_leaf, .{});
                var elem_pats: std.ArrayList(u32) = .empty;
                defer elem_pats.deinit(self.ast.allocator);

                while (self.peekKind() != .rbracket and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .semi and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    if (self.peekKind() == .dotdot) {
                        const next_kind = self.peekKindNth(1);
                        const has_rest_binding = next_kind == .kw_var or
                            next_kind == .amp or
                            next_kind == .kw_mut or
                            next_kind == .kw_own or
                            isIdentifierKind(next_kind);
                        if (has_rest_binding) {
                            const rest_cst = try self.startCstNode(.ident_pat);
                            var has_rest_err = false;
                            const dotdot_tok = try self.consumeLeaf(.token_leaf, .{});
                            if (self.peekKind() == .kw_var or
                                self.peekKind() == .amp or
                                self.peekKind() == .kw_mut or
                                self.peekKind() == .kw_own or
                                self.isRetiredRefPatAt(0))
                            {
                                _ = try self.consumePatternBindingModifier(&has_rest_err);
                            }
                            const ident_tok = try self.expectIdentifierWithCasing(
                                .ident,
                                .snake_case,
                                &has_rest_err,
                                "expected `snake_case` rest binding identifier after `..`",
                            );
                            if (has_rest_err) has_err = true;
                            self.cst.finishNode(rest_cst, .{ .has_error = has_rest_err });
                            const rest_node = try self.ast.appendNodeWithCst(.{
                                .tag = .bind_pat,
                                .main_token = ident_tok,
                                .lhs = PackedOperand.initToken(dotdot_tok),
                            }, rest_cst);
                            try elem_pats.append(self.ast.allocator, rest_node.asInt());
                        } else {
                            const dotdot_tok = try self.consumeLeaf(.wildcard_pat, .{});
                            const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                            const rest_node = try self.ast.appendNodeWithCst(.{
                                .tag = .wildcard_pat,
                                .main_token = dotdot_tok,
                            }, leaf_cst);
                            try elem_pats.append(self.ast.allocator, rest_node.asInt());
                        }
                    } else {
                        try elem_pats.append(
                            self.ast.allocator,
                            (try self.parsePatternWithOptions(is_binding_slot, true)).asInt(),
                        );
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
                    &has_err,
                    "expected `]` to close slice pattern",
                );
                self.cst.finishNode(slice_cst, .{ .has_error = has_err });

                var lhs_op: PackedOperand = .NONE;
                var rhs_op: PackedOperand = .NONE;
                if (elem_pats.items.len > 0) {
                    lhs_op = PackedOperand.initExtra(try self.ast.appendExtraSlice(elem_pats.items));
                    rhs_op = .{ .tag = .extra, .payload = @intCast(elem_pats.items.len) };
                }
                return self.ast.appendNodeWithCst(.{
                    .tag = .slice_pat,
                    .main_token = open_bracket,
                    .lhs = lhs_op,
                    .rhs = rhs_op,
                }, slice_cst);
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
            .kw_var, .amp, .kw_mut, .kw_own => {
                const bind_cst = try self.startCstNode(.ident_pat);
                var has_err = false;
                const first_mod_tok = try self.consumePatternBindingModifier(&has_err);
                const ident_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_err,
                    "expected `snake_case` binding identifier",
                );
                if (self.peekKind() == .at) {
                    self.cst.nodes.items(.kind)[bind_cst.asInt()] = .at_pat;
                    self.pushState(.pattern_parse, bind_cst) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            return self.recoverDepthOverflow(bind_cst, MATCH_ARM_STOP_SET, .pattern_hole);
                        },
                        else => return err,
                    };
                    defer self.popStates(1);
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    const subpat_node = try self.parseSinglePattern(
                        is_binding_slot,
                        is_struct_pat_allowed,
                    );
                    self.cst.finishNode(bind_cst, .{ .has_error = has_err });
                    return self.ast.appendNodeWithCst(.{
                        .tag = .at_pat,
                        .main_token = ident_tok,
                        .lhs = PackedOperand.initToken(first_mod_tok),
                        .rhs = PackedOperand.initNode(subpat_node),
                    }, bind_cst);
                }
                self.cst.finishNode(bind_cst, .{ .has_error = has_err });
                return self.ast.appendNodeWithCst(.{
                    .tag = .bind_pat,
                    .main_token = ident_tok,
                }, bind_cst);
            },
            .prim_type => {
                if (self.peekKindNth(1) == .dot) {
                    const path_cst = try self.startCstNode(.path_pat);
                    var has_err = false;
                    const first_tok = try self.consumeLeaf(.token_leaf, .{});
                    while (self.peekKind() == .dot) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        if (isIdentifierKind(self.peekKind()) or self.peekKind() == .kw_async) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        } else {
                            has_err = true;
                            try self.emitUnexpectedToken(
                                self.peekTokenIndexNth(0),
                                "expected associated constant identifier after `.` in pattern",
                                "missing pattern path segment",
                            );
                            break;
                        }
                    }
                    self.cst.finishNode(path_cst, .{ .has_error = has_err });
                    var pat_node = try self.ast.appendNodeWithCst(.{
                        .tag = .variant_pat,
                        .main_token = first_tok,
                    }, path_cst);
                    if (self.peekKind() == .dotdoteq or self.peekKind() == .dotdot) {
                        const range_tok = self.peekTokenIndexNth(0);
                        _ = try self.precedeNode(pat_cst_start, pat_ast_start, .range_pat, range_tok);
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        var has_range_err = false;
                        const end_tok = try self.consumePatternRangeEnd(&has_range_err);
                        self.cst.finishNode(pat_cst_start, .{ .has_error = has_range_err });
                        if (!has_range_err) {
                            pat_node = try self.ast.appendNodeWithCst(.{
                                .tag = .lit_pat,
                                .main_token = range_tok,
                                .lhs = PackedOperand.initNode(pat_node),
                                .rhs = PackedOperand.initToken(end_tok),
                            }, pat_cst_start);
                        }
                    }
                    return pat_node;
                }
                const err_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    err_tok,
                    "expected pattern",
                    "unexpected primitive type in pattern position",
                );
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                self.cst.finishNode(hole_cst, .{ .has_error = true });
                return self.ast.appendNodeWithCst(.{
                    .tag = .pattern_hole,
                    .main_token = err_tok,
                }, hole_cst);
            },
            .ident, .type_ident, .const_ident, .kw_self_type, .kw_async => {
                if (self.peekKind() == .kw_async and self.peekKindNth(1) != .dot) {
                    const err_tok = self.peekTokenIndexNth(0);
                    try self.emitUnexpectedToken(
                        err_tok,
                        "expected pattern",
                        "unexpected `async` keyword in pattern position",
                    );
                    const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                    _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                    self.cst.finishNode(hole_cst, .{ .has_error = true });
                    return self.ast.appendNodeWithCst(.{
                        .tag = .pattern_hole,
                        .main_token = err_tok,
                    }, hole_cst);
                }
                if (self.isRetiredRefPatAt(0)) {
                    const bind_cst = try self.startCstNode(.ident_pat);
                    var has_err = false;
                    const first_mod_tok = try self.consumePatternBindingModifier(&has_err);
                    const ident_tok = try self.expectIdentifierWithCasing(
                        .ident,
                        .snake_case,
                        &has_err,
                        "expected `snake_case` binding identifier",
                    );
                    if (self.peekKind() == .at) {
                        self.cst.nodes.items(.kind)[bind_cst.asInt()] = .at_pat;
                        self.pushState(.pattern_parse, bind_cst) catch |err| switch (err) {
                            error.ParseDepthExceeded => {
                                return self.recoverDepthOverflow(bind_cst, MATCH_ARM_STOP_SET, .pattern_hole);
                            },
                            else => return err,
                        };
                        defer self.popStates(1);
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        const subpat_node = try self.parseSinglePattern(
                            is_binding_slot,
                            is_struct_pat_allowed,
                        );
                        self.cst.finishNode(bind_cst, .{ .has_error = has_err });
                        return self.ast.appendNodeWithCst(.{
                            .tag = .at_pat,
                            .main_token = ident_tok,
                            .lhs = PackedOperand.initToken(first_mod_tok),
                            .rhs = PackedOperand.initNode(subpat_node),
                        }, bind_cst);
                    }
                    self.cst.finishNode(bind_cst, .{ .has_error = has_err });
                    return self.ast.appendNodeWithCst(.{
                        .tag = .bind_pat,
                        .main_token = ident_tok,
                    }, bind_cst);
                }

                // Subpattern `@` binding (`ident @ SinglePattern`):
                if (self.peekKindNth(1) == .at) {
                    const at_cst = try self.startCstNode(.at_pat);
                    self.pushState(.pattern_parse, at_cst) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            return self.recoverDepthOverflow(at_cst, MATCH_ARM_STOP_SET, .pattern_hole);
                        },
                        else => return err,
                    };
                    defer self.popStates(1);
                    var has_err = false;
                    const ident_tok = try self.expectIdentifierWithCasing(
                        .ident,
                        .snake_case,
                        &has_err,
                        "expected `snake_case` pattern binding identifier before `@`",
                    );
                    _ = try self.consumeLeaf(.token_leaf, .{});
                    const subpat_node = try self.parseSinglePattern(
                        is_binding_slot,
                        is_struct_pat_allowed,
                    );
                    self.cst.finishNode(at_cst, .{ .has_error = has_err });
                    return self.ast.appendNodeWithCst(.{
                        .tag = .at_pat,
                        .main_token = ident_tok,
                        .rhs = PackedOperand.initNode(subpat_node),
                    }, at_cst);
                }

                // Qualified `.` path, variant, constant, or struct destructuring pattern
                // (`Option.Some(x)`, `Ready`, `MAX_RETRIES`, `Point { x, y }`):
                if (self.peekKindNth(1) == .dot or
                    self.peekKindNth(1) == .lparen or
                    (is_struct_pat_allowed and self.peekKindNth(1) == .lbrace) or
                    (!is_binding_slot and (self.peekKind() == .type_ident or self.peekKind() == .const_ident)))
                {
                    const path_cst = try self.startCstNode(.path_pat);
                    var has_err = false;
                    const first_tok = try self.consumeLeaf(.token_leaf, .{});
                    while (self.peekKind() == .dot) {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        if (isIdentifierKind(self.peekKind()) or self.peekKind() == .kw_async) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        } else {
                            has_err = true;
                            try self.emitUnexpectedToken(
                                self.peekTokenIndexNth(0),
                                "expected identifier after `.` in pattern",
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
                    var path_node = try self.ast.appendNodeWithCst(.{
                        .tag = res_tag,
                        .main_token = first_tok,
                        .lhs = lhs_op,
                        .rhs = rhs_op,
                    }, path_cst);

                    if (payload_pats.items.len == 0 and
                        res_tag == .variant_pat and
                        (self.peekKind() == .dotdoteq or self.peekKind() == .dotdot))
                    {
                        const range_tok = self.peekTokenIndexNth(0);
                        _ = try self.precedeNode(pat_cst_start, pat_ast_start, .range_pat, range_tok);
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        var has_range_err = false;
                        const end_tok = try self.consumePatternRangeEnd(&has_range_err);
                        self.cst.finishNode(pat_cst_start, .{ .has_error = has_range_err });
                        if (!has_range_err) {
                            path_node = try self.ast.appendNodeWithCst(.{
                                .tag = .lit_pat,
                                .main_token = range_tok,
                                .lhs = PackedOperand.initNode(path_node),
                                .rhs = PackedOperand.initToken(end_tok),
                            }, pat_cst_start);
                        }
                    }
                    return path_node;
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
                var has_shorthand_mod = false;
                if (self.peekKind() == .kw_var or
                    self.peekKind() == .amp or
                    self.peekKind() == .kw_mut or
                    self.peekKind() == .kw_own or
                    self.isRetiredRefPatAt(0))
                {
                    has_shorthand_mod = true;
                    _ = try self.consumePatternBindingModifier(&has_field_err);
                }
                const field_tok = try self.expectIdentifierWithCasing(
                    .ident,
                    .snake_case,
                    &has_field_err,
                    "expected `snake_case` field name in struct pattern",
                );
                if (self.peekKind() == .colon) {
                    const colon_tok = try self.consumeLeaf(.token_leaf, .{});
                    if (has_shorthand_mod) {
                        has_field_err = true;
                        try self.emitUnexpectedToken(
                            colon_tok,
                            "shorthand binding modifier cannot precede `field: pattern` renaming",
                            "move `var` or `&` into the renamed sub-pattern",
                        );
                    }
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

    /// Returns `true` if `[` at `peek(0)` starts generic `TypeArgs` under `DR-21` Section 1.3 Rules 1A–1B.
    fn isTypeArgsAfterLBracket(self: *const Parser, opt_lhs_node: ?NodeIndex) bool {
        if (self.peekKind() != .lbracket) return false;
        if (opt_lhs_node) |lhs_id| {
            if (self.hasTrailingTypeLhs(lhs_id)) return true;
        }
        return self.isTypeStart(1);
    }

    /// Returns `true` if the token at `start_lookahead` begins a `Type` (`DR-22` Section 3.3).
    fn isTypeStart(self: *const Parser, start_lookahead: usize) bool {
        var raw_idx: usize = self.peekTokenIndexNth(start_lookahead).asInt();
        var steps: usize = 0;
        while (steps < MAX_TYPE_LOOKAHEAD) : (steps += 1) {
            switch (self.rawTokenKindAt(raw_idx)) {
                .prim_type => {
                    return self.rawTokenKindAt(self.advanceNonCarrierRawIndex(raw_idx, 1)) != .dot;
                },
                .kw_self_type => {
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    if (self.rawTokenKindAt(next_raw) == .dot) {
                        return self.rawTokenKindAt(self.advanceNonCarrierRawIndex(next_raw, 1)) == .type_ident;
                    }
                    return true;
                },
                .kw_const,
                .kw_own,
                .hash_soa,
                .tilde,
                .kw_fn,
                .kw_unsafe,
                .kw_extern,
                .pipepipe,
                => return true,
                .kw_async => {
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    if (self.rawTokenKindAt(next_raw) != .dot) return true;
                    var scan_raw: usize = raw_idx;
                    var seg_steps: usize = 0;
                    while (seg_steps < MAX_TYPE_LOOKAHEAD and
                        isIdentOrModuleSegment(self.rawTokenKindAt(scan_raw)) and
                        self.rawTokenKindAt(self.advanceNonCarrierRawIndex(scan_raw, 1)) == .dot) : (seg_steps += 1)
                    {
                        scan_raw = self.advanceNonCarrierRawIndex(scan_raw, 2);
                    }
                    if (scan_raw > raw_idx and self.rawTokenKindAt(scan_raw) == .type_ident) {
                        raw_idx = scan_raw;
                        continue;
                    }
                    if (self.rawTokenKindAt(scan_raw) == .ident) {
                        const tail_tok = TokenIndex.fromInt(@intCast(self.skipCarrierRawIndex(scan_raw)));
                        const tail_lexeme = self.getTokenLexeme(tail_tok);
                        if (CANONICAL_C_TYPE_ALIASES.has(tail_lexeme) or
                            self.allowed_non_canonical_types.contains(tail_lexeme))
                        {
                            const after_tail = self.rawTokenKindAt(
                                self.advanceNonCarrierRawIndex(scan_raw, 1),
                            );
                            return after_tail != .dot and
                                after_tail != .lparen and
                                after_tail != .lbrace;
                        }
                    }
                    return false;
                },
                .at => {
                    const name_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    const name_kind = self.rawTokenKindAt(name_raw);
                    if (!isIdentifierKind(name_kind) and !isKeywordKind(name_kind)) return false;
                    var after_attr = self.advanceNonCarrierRawIndex(name_raw, 1);
                    if (self.rawTokenKindAt(after_attr) == .lbracket) return false;
                    if (self.rawTokenKindAt(after_attr) == .lparen) {
                        var paren_depth: u32 = 1;
                        after_attr = self.advanceNonCarrierRawIndex(after_attr, 1);
                        while (steps < MAX_TYPE_LOOKAHEAD and paren_depth > 0) : (steps += 1) {
                            const inner_kind = self.rawTokenKindAt(after_attr);
                            if (inner_kind == .eof) return false;
                            if (inner_kind == .lparen) {
                                paren_depth += 1;
                            } else if (inner_kind == .rparen) {
                                paren_depth -= 1;
                            }
                            after_attr = self.advanceNonCarrierRawIndex(after_attr, 1);
                        }
                        if (paren_depth != 0) return false;
                    }
                    raw_idx = after_attr;
                },
                .star => {
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    const next_kind = self.rawTokenKindAt(next_raw);
                    raw_idx = if (next_kind == .kw_mut or next_kind == .kw_const)
                        self.advanceNonCarrierRawIndex(next_raw, 1)
                    else
                        next_raw;
                },
                .pipe => {
                    var scan_raw: usize = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    var pipe_steps: usize = 0;
                    var nested_depth: u32 = 0;
                    while (pipe_steps < MAX_TYPE_LOOKAHEAD) : (pipe_steps += 1) {
                        const tok_kind = self.rawTokenKindAt(scan_raw);
                        if (tok_kind == .eof or tok_kind == .semi or tok_kind == .rbrace) return false;
                        if (nested_depth == 0 and tok_kind == .pipe) {
                            const after_pipe = self.rawTokenKindAt(self.advanceNonCarrierRawIndex(scan_raw, 1));
                            return after_pipe == .arrow or
                                after_pipe == .rbracket or
                                after_pipe == .rparen or
                                after_pipe == .comma or
                                after_pipe == .question or
                                after_pipe == .bang;
                        }
                        if (tok_kind == .lparen or tok_kind == .lbracket) {
                            nested_depth += 1;
                        } else if (tok_kind == .rparen or tok_kind == .rbracket) {
                            if (nested_depth == 0) return false;
                            nested_depth -= 1;
                        }
                        scan_raw = self.advanceNonCarrierRawIndex(scan_raw, 1);
                    }
                    return false;
                },
                .type_ident => {
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    const next_kind = self.rawTokenKindAt(next_raw);
                    if (next_kind == .dot or next_kind == .lparen or next_kind == .lbrace) {
                        return false;
                    }
                    if (next_kind == .lbracket) {
                        var scan_raw: usize = self.advanceNonCarrierRawIndex(next_raw, 1);
                        var scan_steps: usize = 0;
                        var bracket_depth: u32 = 1;
                        while (scan_steps < MAX_TYPE_LOOKAHEAD) : (scan_steps += 1) {
                            const tok_kind = self.rawTokenKindAt(scan_raw);
                            if (tok_kind == .eof or tok_kind == .semi or tok_kind == .rbrace) break;
                            if (tok_kind == .lbracket) {
                                bracket_depth += 1;
                            } else if (tok_kind == .rbracket) {
                                bracket_depth -= 1;
                                if (bracket_depth == 0) {
                                    const after_close = self.rawTokenKindAt(
                                        self.advanceNonCarrierRawIndex(scan_raw, 1),
                                    );
                                    if (after_close == .dot or
                                        after_close == .lparen or
                                        after_close == .lbrace)
                                    {
                                        return false;
                                    }
                                    break;
                                }
                            }
                            scan_raw = self.advanceNonCarrierRawIndex(scan_raw, 1);
                        }
                    }
                    return true;
                },
                .amp => {
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    const next_kind = self.rawTokenKindAt(next_raw);
                    if (next_kind == .kw_mut) {
                        raw_idx = self.advanceNonCarrierRawIndex(next_raw, 1);
                    } else if (next_kind == .ident) {
                        const next_tok_id = TokenIndex.fromInt(@intCast(self.skipCarrierRawIndex(next_raw)));
                        const after_out = self.advanceNonCarrierRawIndex(next_raw, 1);
                        if (std.mem.eql(u8, self.getTokenLexeme(next_tok_id), "out") and
                            self.rawTokenKindAt(after_out) != .dot)
                        {
                            raw_idx = after_out;
                        } else {
                            raw_idx = next_raw;
                        }
                    } else {
                        raw_idx = next_raw;
                    }
                },
                .lparen => {
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    if (self.rawTokenKindAt(next_raw) == .rparen) return true;
                    raw_idx = next_raw;
                },
                .lbracket => {
                    raw_idx = self.advanceNonCarrierRawIndex(raw_idx, 1);
                },
                .ident => {
                    const cur_tok_id = TokenIndex.fromInt(@intCast(self.skipCarrierRawIndex(raw_idx)));
                    const lexeme = self.getTokenLexeme(cur_tok_id);
                    const next_raw = self.advanceNonCarrierRawIndex(raw_idx, 1);
                    const next_kind = self.rawTokenKindAt(next_raw);
                    if ((std.mem.eql(u8, lexeme, "dyn") or std.mem.eql(u8, lexeme, "any")) and
                        (next_kind == .type_ident or next_kind == .kw_self_type or
                            (isIdentOrModuleSegment(next_kind) and
                                self.rawTokenKindAt(self.advanceNonCarrierRawIndex(next_raw, 1)) == .dot)))
                    {
                        raw_idx = next_raw;
                        continue;
                    }
                    var scan_raw: usize = raw_idx;
                    var seg_steps: usize = 0;
                    while (seg_steps < MAX_TYPE_LOOKAHEAD and
                        isIdentOrModuleSegment(self.rawTokenKindAt(scan_raw)) and
                        self.rawTokenKindAt(self.advanceNonCarrierRawIndex(scan_raw, 1)) == .dot) : (seg_steps += 1)
                    {
                        scan_raw = self.advanceNonCarrierRawIndex(scan_raw, 2);
                    }
                    if (scan_raw > raw_idx and self.rawTokenKindAt(scan_raw) == .type_ident) {
                        raw_idx = scan_raw;
                        continue;
                    }
                    if (self.rawTokenKindAt(scan_raw) == .ident) {
                        const tail_tok = TokenIndex.fromInt(@intCast(self.skipCarrierRawIndex(scan_raw)));
                        const tail_lexeme = self.getTokenLexeme(tail_tok);
                        if (CANONICAL_C_TYPE_ALIASES.has(tail_lexeme) or
                            self.allowed_non_canonical_types.contains(tail_lexeme))
                        {
                            const after_tail = self.rawTokenKindAt(
                                self.advanceNonCarrierRawIndex(scan_raw, 1),
                            );
                            return after_tail != .dot and
                                after_tail != .lparen and
                                after_tail != .lbrace;
                        }
                    }
                    return false;
                },
                else => return false,
            }
        }
        return false;
    }

    /// Returns `true` if `lhs_node` is a static path or instantiated type (`DR-21` Section 1.3).
    fn isStaticPathExpr(self: *const Parser, lhs_node: NodeIndex) bool {
        if (lhs_node.isNone() or self.has_last_expr_block_body) return false;
        var cur_node_id = lhs_node;
        var is_type_tail_required = false;
        const max_steps: usize = @min(self.ast.countNodes(), self.options.max_depth);
        var step_count: usize = 0;
        while (step_count <= max_steps) : (step_count += 1) {
            if (cur_node_id.isNone()) return false;
            const node = self.ast.getNode(cur_node_id);
            if (isBlockBodiedAstTag(node.tag)) return false;
            switch (node.tag) {
                .ident_expr => {
                    if (node.main_token.isNone()) return false;
                    const kind = self.token_buffer.getToken(node.main_token).kind;
                    return if (is_type_tail_required)
                        kind == .type_ident or kind == .kw_self_type
                    else
                        isIdentifierKind(kind) or kind == .kw_async or
                            kind == .kw_self_type or kind == .prim_type;
                },
                .path_expr => return !is_type_tail_required,
                .field_access => {
                    if (node.lhs.tag != .node or node.rhs.tag != .token) return false;
                    const rhs_kind = self.token_buffer.getToken(TokenIndex.fromInt(node.rhs.payload)).kind;
                    if (is_type_tail_required) {
                        if (rhs_kind != .type_ident) return false;
                        is_type_tail_required = false;
                    } else if (!isIdentifierKind(rhs_kind) and rhs_kind != .kw_async) {
                        return false;
                    }
                    cur_node_id = NodeIndex.fromInt(node.lhs.payload);
                },
                .generic_call => {
                    if (!self.isBracketOnlyGenericCallCst(cur_node_id)) return false;
                    is_type_tail_required = true;
                    cur_node_id = NodeIndex.fromInt(node.lhs.payload);
                },
                else => return false,
            }
        }
        return false;
    }

    /// Returns `true` if `lhs_node` syntactically ends in a nominal type or `Self` (`DR-21` Rule 1A).
    fn hasTrailingTypeLhs(self: *const Parser, lhs_node: NodeIndex) bool {
        if (lhs_node.isNone() or self.has_last_expr_block_body) return false;
        var cur_node_id = lhs_node;
        const max_steps: usize = @min(self.ast.countNodes(), self.options.max_depth);
        var step_count: usize = 0;
        while (step_count <= max_steps) : (step_count += 1) {
            if (cur_node_id.isNone()) return false;
            const node = self.ast.getNode(cur_node_id);
            switch (node.tag) {
                .ident_expr => {
                    if (node.main_token.isNone()) return false;
                    const kind = self.token_buffer.getToken(node.main_token).kind;
                    return kind == .type_ident or kind == .kw_self_type;
                },
                .field_access => {
                    if (node.lhs.tag != .node or node.rhs.tag != .token) return false;
                    const rhs_kind = self.token_buffer.getToken(TokenIndex.fromInt(node.rhs.payload)).kind;
                    return rhs_kind == .type_ident and
                        self.isStaticPathExpr(NodeIndex.fromInt(node.lhs.payload));
                },
                .generic_call => {
                    if (!self.isBracketOnlyGenericCallCst(cur_node_id)) return false;
                    cur_node_id = NodeIndex.fromInt(node.lhs.payload);
                },
                else => return false,
            }
        }
        return false;
    }

    /// Returns `true` if `node_id` is a `.generic_call` whose CST subtree ends directly at `]` without `(…)`.
    fn isBracketOnlyGenericCallCst(self: *const Parser, node_id: NodeIndex) bool {
        const node = self.ast.getNode(node_id);
        if (node.tag != .generic_call or node.lhs.tag != .node) return false;
        if (node_id.asInt() >= self.ast.ast_to_cst.items.len) return false;
        const cst_idx = self.ast.ast_to_cst.items[node_id.asInt()];
        if (cst_idx.isNone() or cst_idx.asInt() >= self.cst.countNodes()) return false;
        const cst_rec = self.cst.getNode(cst_idx);
        if (cst_rec.kind != .call_expr or cst_rec.subtree_size == 0) return false;
        const last_cst_idx = CstNodeIndex.fromInt(cst_idx.asInt() + cst_rec.subtree_size - 1);
        if (last_cst_idx.asInt() >= self.cst.countNodes()) return false;
        const last_leaf = self.cst.getNode(last_cst_idx);
        if (last_leaf.token.isNone()) return false;
        return self.token_buffer.getToken(last_leaf.token).kind == .rbracket;
    }

    /// Returns `true` if `(` at `peek(0)` starts a `WalrusCondExpr` (`([var] x [: T] := expr)`).
    fn isWalrusAfterLParen(self: *const Parser) bool {
        if (self.peekKind() != .lparen) return false;
        const first_kind = self.peekKindNth(1);
        if (first_kind == .kw_var) return true;
        if (!isIdentifierKind(first_kind)) return false;
        const second_kind = self.peekKindNth(2);
        if (second_kind == .colon_eq) return true;
        if (second_kind != .colon) return false;

        const third_kind = self.peekKindNth(3);
        if (third_kind == .kw_for or
            third_kind == .kw_while or
            third_kind == .kw_loop or
            third_kind == .kw_match or
            (third_kind == .kw_comptime and self.peekKindNth(4) == .kw_for))
        {
            return false;
        }

        var scan_off: usize = 3;
        var steps: usize = 0;
        var delim_depth: u32 = 0;
        while (steps < MAX_TYPE_LOOKAHEAD) : (steps += 1) {
            const cur_kind = self.peekKindNth(scan_off);
            if (delim_depth == 0) {
                if (cur_kind == .colon_eq) return true;
                if (cur_kind == .rparen or
                    cur_kind == .comma or
                    cur_kind == .semi or
                    cur_kind == .lbrace or
                    cur_kind == .rbrace or
                    cur_kind == .eof)
                {
                    return false;
                }
            }
            if (cur_kind == .lparen or cur_kind == .lbracket or cur_kind == .lbrace) {
                delim_depth += 1;
            } else if (cur_kind == .rparen or cur_kind == .rbracket or cur_kind == .rbrace) {
                if (delim_depth == 0) return false;
                delim_depth -= 1;
            }
            scan_off += 1;
        }
        return false;
    }

    /// Returns `true` if `peek(0)` starts a labeled loop or `match` (`label: for`, `label: while`, `label: loop`, `label: match`).
    fn isLabeledLoopStart(self: *const Parser) bool {
        if (self.peekKind() != .ident or self.peekKindNth(1) != .colon) return false;
        return switch (self.peekKindNth(2)) {
            .kw_for, .kw_while, .kw_loop, .kw_match => true,
            .kw_comptime => self.peekKindNth(3) == .kw_for,
            else => false,
        };
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
                    const after_dot = self.peekKindNth(1);
                    if ((self.has_last_expr_block_body or
                        isBlockBodiedAstTag(self.ast.getNode(lhs_node).tag)) and
                        (after_dot == .type_ident or after_dot == .const_ident))
                    {
                        break;
                    }

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

                if (cur_kind == .lbrace and
                    is_struct_lit_allowed and
                    !self.has_last_expr_block_body and
                    self.hasTrailingTypeLhs(lhs_node))
                {
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

                    const lbrace_tok = self.peekTokenIndexNth(0);
                    var has_lit_err = false;
                    if (self.isStructLiteralBrace()) {
                        _ = try self.precedeNode(
                            lhs_cst_start,
                            lhs_ast_start,
                            .struct_lit_expr,
                            lbrace_tok,
                        );
                        var field_nodes: std.ArrayList(u32) = .empty;
                        defer field_nodes.deinit(self.ast.allocator);
                        const saved_cond_header = self.is_in_cond_header;
                        self.is_in_cond_header = false;
                        try self.parseStructLiteralBody(&field_nodes, &has_lit_err);
                        self.is_in_cond_header = saved_cond_header;
                        self.cst.finishNode(lhs_cst_start, .{ .has_error = has_lit_err });
                        self.has_last_expr_block_body = false;

                        var rhs_op: PackedOperand = .NONE;
                        if (field_nodes.items.len > 0) {
                            rhs_op = PackedOperand.initExtra(
                                try self.ast.appendExtraSlice(field_nodes.items),
                            );
                        }
                        lhs_node = try self.ast.appendNodeWithCst(.{
                            .tag = .struct_lit,
                            .main_token = lbrace_tok,
                            .lhs = PackedOperand.initNode(lhs_node),
                            .rhs = rhs_op,
                        }, lhs_cst_start);
                        continue;
                    }

                    _ = try self.precedeNode(
                        lhs_cst_start,
                        lhs_ast_start,
                        .view_block_expr,
                        lbrace_tok,
                    );
                    const vb_node = try self.parseBlock();
                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_lit_err });
                    self.has_last_expr_block_body = true;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .call_expr,
                        .main_token = lbrace_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = PackedOperand.initNode(vb_node),
                    }, lhs_cst_start);
                    continue;
                }
            }

            // [2] Reject bare unparenthesized `:=` bindings (`E0215`) cleanly without cascading:
            if (cur_kind == .colon_eq) {
                self.is_in_stmt_lhs = false;
                self.is_in_lhs_place = false;
                const walrus_tok = self.peekTokenIndexNth(0);
                try self.emitWalrusPositionError(
                    self.getTokenSpan(walrus_tok),
                    "unparenthesized `:=` binding is not allowed here",
                    "wrap condition binding in parentheses: `(x := expr)` inside `if`/`while`, or use `let`/`var` with `=` for a statement",
                );
                _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .invalid_parse_subtree, walrus_tok);
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                const saved_cond_header = self.is_in_cond_header;
                self.is_in_cond_header = false;
                _ = try self.parseExprBp(1, is_struct_lit_allowed);
                self.is_in_cond_header = saved_cond_header;
                self.cst.finishNode(lhs_cst_start, .{ .has_error = true });
                self.has_last_expr_block_body = false;
                lhs_node = try self.ast.appendNodeWithCst(.{
                    .tag = .expr_hole,
                    .main_token = walrus_tok,
                }, lhs_cst_start);
                continue;
            }

            // [3] Break on outer statement-level assignment, or reject nested assignment inside expressions:
            if (isAssignOp(cur_kind)) {
                if (self.is_in_stmt_lhs) break;
                self.is_in_lhs_place = false;
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

            // [3b] Retired infix `||` (`ADR-22A`, `E0219`); preserve newline 0-arg closure after block expr:
            if (cur_kind == .pipepipe and 2 >= min_bp) {
                if ((self.has_last_expr_block_body or
                    isBlockBodiedAstTag(self.ast.getNode(lhs_node).tag)) and
                    self.peekNth(0).flags.has_leading_newline)
                {
                    break;
                }
                self.is_in_stmt_lhs = false;
                self.is_in_lhs_place = false;

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

                const op_tok = self.peekTokenIndexNth(0);
                _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, op_tok);
                _ = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                try self.emitRetiredLogicalOr(op_tok);
                const rhs_node = try self.parseExprBp(3, is_struct_lit_allowed);
                self.cst.finishNode(lhs_cst_start, .{ .has_error = true });
                self.has_last_expr_block_body = false;
                lhs_node = try self.ast.appendNodeWithCst(.{
                    .tag = .binary_expr,
                    .main_token = op_tok,
                    .lhs = PackedOperand.initNode(lhs_node),
                    .rhs = PackedOperand.initNode(rhs_node),
                }, lhs_cst_start);
                continue;
            }

            // [4] Infix Operators (Tiers 13 down to 1):
            if (getInfixBindingPower(cur_kind)) |bp_info| {
                if (bp_info.left_bp < min_bp) break;
                self.is_in_stmt_lhs = false;
                self.is_in_lhs_place = false;

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
                    const target_ty = try self.parseTypeWithMode(.none);
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

                if (cur_kind == .kw_orelse) {
                    const orelse_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, orelse_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});

                    var is_rhs_block = false;
                    const fallback_node = if (self.peekKind() == .lbrace) blk: {
                        is_rhs_block = true;
                        break :blk try self.parseBlock();
                    } else blk: {
                        const rhs_expr = try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);
                        is_rhs_block = self.has_last_expr_block_body;
                        break :blk rhs_expr;
                    };

                    self.cst.finishNode(lhs_cst_start, .{});
                    self.has_last_expr_block_body = is_rhs_block;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .binary_expr,
                        .main_token = orelse_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = PackedOperand.initNode(fallback_node),
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

                    var is_rhs_block = false;
                    const fallback_node = if (self.peekKind() == .lbrace) blk: {
                        is_rhs_block = true;
                        break :blk try self.parseBlock();
                    } else blk: {
                        const rhs_expr = try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);
                        is_rhs_block = self.has_last_expr_block_body;
                        break :blk rhs_expr;
                    };

                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_catch_err });
                    self.has_last_expr_block_body = is_rhs_block;
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
                    const op_tok = if (self.peekKind() == .kw_not)
                        try self.consumeLeaf(.token_leaf, .{})
                    else
                        is_tok;
                    const rhs_pat = try self.parsePatternWithOptions(false, is_struct_lit_allowed);

                    var has_is_chain_err = false;
                    if (self.peekKind() == .kw_is or isRelationalOp(self.peekKind())) {
                        has_is_chain_err = true;
                        const chain_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            chain_tok,
                            "chained `is` or relational operators are non-associative in CoreX",
                            "combine predicates with `and` or add explicit parentheses",
                        );
                        _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                        if (self.peekKind() == .kw_not) {
                            _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                        }
                        _ = try self.parsePatternWithOptions(false, is_struct_lit_allowed);
                    }

                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_is_chain_err });
                    self.has_last_expr_block_body = false;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .is_expr,
                        .main_token = op_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = PackedOperand.initNode(rhs_pat),
                    }, lhs_cst_start);
                    continue;
                }

                if (cur_kind == .dotdot or cur_kind == .dotdoteq) {
                    const range_tok = self.peekTokenIndexNth(0);
                    _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, range_tok);
                    _ = try self.consumeLeaf(.token_leaf, .{});

                    var rhs_op: PackedOperand = .NONE;
                    if (cur_kind == .dotdoteq or isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                        rhs_op = PackedOperand.initNode(
                            try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed),
                        );
                    }

                    var has_range_chain_err = false;
                    if (isRangeOp(self.peekKind())) {
                        has_range_chain_err = true;
                        const chain_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            chain_tok,
                            "chained range operators are non-associative in CoreX",
                            "add explicit parentheses around the range operand",
                        );
                        _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                        if (isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                            _ = try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);
                        }
                    }

                    self.cst.finishNode(lhs_cst_start, .{ .has_error = has_range_chain_err });
                    self.has_last_expr_block_body = false;
                    lhs_node = try self.ast.appendNodeWithCst(.{
                        .tag = .range_expr,
                        .main_token = range_tok,
                        .lhs = PackedOperand.initNode(lhs_node),
                        .rhs = rhs_op,
                    }, lhs_cst_start);
                    continue;
                }

                const op_tok = self.peekTokenIndexNth(0);
                _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .infix_expr, op_tok);
                _ = try self.consumeLeaf(.token_leaf, .{});
                const rhs_node = try self.parseExprBp(bp_info.right_bp, is_struct_lit_allowed);

                // Enforce non-associativity on relational (`<`, `==`, etc.) and `is` tiers:
                var has_non_assoc_err = false;
                if (bp_info.is_non_associative) {
                    const next_kind = self.peekKind();
                    if (isRelationalOp(cur_kind) and (isRelationalOp(next_kind) or next_kind == .kw_is)) {
                        has_non_assoc_err = true;
                        const chain_tok = self.peekTokenIndexNth(0);
                        try self.emitUnexpectedToken(
                            chain_tok,
                            "chained relational operators are non-associative in CoreX",
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

    /// Parses postfix `.*`, `.await`, `.field`, `.0`, `.method[T](args)`, or mid-keystroke `expr.`.
    fn parseDotPostfix(
        self: *Parser,
        lhs_node: NodeIndex,
        lhs_cst_start: CstNodeIndex,
        lhs_ast_start: usize,
        is_struct_lit_allowed: bool,
    ) anyerror!NodeIndex {
        const dot_tok = self.peekTokenIndexNth(0);
        if (self.peekKindNth(1) == .star) {
            _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .postfix_deref_expr, dot_tok);
            _ = try self.consumeLeaf(.token_leaf, .{});
            const star_tok = try self.consumeLeaf(.token_leaf, .{});
            self.cst.finishNode(lhs_cst_start, .{});
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .deref_expr,
                .main_token = star_tok,
                .lhs = PackedOperand.initNode(lhs_node),
            }, lhs_cst_start);
        }

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

        if ((self.peekKind() == .type_ident or self.peekKind() == .const_ident) and
            self.isStaticPathExpr(lhs_node))
        {
            const member_tok = try self.consumeLeaf(.token_leaf, .{});
            self.cst.finishNode(lhs_cst_start, .{});
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .field_access,
                .main_token = dot_tok,
                .lhs = PackedOperand.initNode(lhs_node),
                .rhs = PackedOperand.initToken(member_tok),
            }, lhs_cst_start);
        }

        if (isIdentifierKind(self.peekKind()) or self.peekKind() == .kw_async or self.peekKind() == .int_lit) {
            var has_err = false;
            const member_tok = if (self.peekKind() == .int_lit or self.peekKind() == .kw_async)
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
            if (self.isTypeArgsAfterLBracket(null)) {
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
            "expected field, method, `*`, or `await` after `.`",
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

    /// Parses postfix generic call `callee[T](args)` or index expression `base[i]` / `base[i, j]` (`SE-21`).
    fn parseBracketPostfix(
        self: *Parser,
        lhs_node: NodeIndex,
        lhs_cst_start: CstNodeIndex,
        lhs_ast_start: usize,
        is_struct_lit_allowed: bool,
    ) anyerror!NodeIndex {
        const saved_stmt_lhs = self.is_in_stmt_lhs;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_stmt_lhs = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_stmt_lhs = saved_stmt_lhs;
            self.is_in_lhs_place = saved_lhs_place;
        }
        const bracket_tok = self.peekTokenIndexNth(0);
        const lhs_ast = self.ast.getNode(lhs_node);
        const is_intrinsic_callee = lhs_ast.tag == .ident_expr and
            !lhs_ast.main_token.isNone() and
            self.token_buffer.getToken(lhs_ast.main_token).kind == .at;
        if (is_intrinsic_callee or self.isTypeArgsAfterLBracket(lhs_node)) {
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

        // Array, slice, or multi-index subscript expression (`base[i]` or `base[i, j]`):
        _ = try self.precedeNode(lhs_cst_start, lhs_ast_start, .index_expr, bracket_tok);
        var has_err = false;
        const open_bracket = try self.consumeLeaf(.token_leaf, .{});
        const saved_cond_header = self.is_in_cond_header;
        self.is_in_cond_header = false;
        defer self.is_in_cond_header = saved_cond_header;

        var idx_nodes: std.ArrayList(u32) = .empty;
        defer idx_nodes.deinit(self.ast.allocator);
        const first_idx = try self.parseExpr(true);
        try idx_nodes.append(self.ast.allocator, first_idx.asInt());
        while (self.peekKind() == .comma) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            if (self.peekKind() == .rbracket) break;
            try idx_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());
        }
        try self.expectClosingDelimiter(
            .rbracket,
            open_bracket,
            &has_err,
            "expected `]` to close index expression",
        );
        self.cst.finishNode(lhs_cst_start, .{ .has_error = has_err });
        self.has_last_expr_block_body = false;
        const rhs_op: PackedOperand = if (idx_nodes.items.len <= 1)
            PackedOperand.initNode(first_idx)
        else
            PackedOperand.initExtra(try self.ast.appendExtraSlice(idx_nodes.items));
        return self.ast.appendNodeWithCst(.{
            .tag = .index_expr,
            .main_token = open_bracket,
            .lhs = PackedOperand.initNode(lhs_node),
            .rhs = rhs_op,
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
        const saved_lhs_place = self.is_in_lhs_place;
        const saved_cond_header = self.is_in_cond_header;
        self.is_in_stmt_lhs = false;
        self.is_in_lhs_place = false;
        self.is_in_cond_header = false;
        defer {
            self.is_in_stmt_lhs = saved_stmt_lhs;
            self.is_in_lhs_place = saved_lhs_place;
            self.is_in_cond_header = saved_cond_header;
        }
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

            var opt_label_tok: TokenIndex = .none;
            if (isIdentifierKind(self.peekKind()) and self.peekKindNth(1) == .colon) {
                opt_label_tok = try self.expectIdentifierWithCasing(
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
            if (has_arg_err) has_error.* = true;
            self.cst.finishNode(arg_cst, .{ .has_error = has_arg_err });

            if (!opt_label_tok.isNone()) {
                const named_node = try self.ast.appendNodeWithCst(.{
                    .tag = .named_arg,
                    .main_token = opt_label_tok,
                    .lhs = PackedOperand.initNode(arg_expr),
                }, arg_cst);
                try arg_nodes.append(self.ast.allocator, named_node.asInt());
            } else {
                try arg_nodes.append(self.ast.allocator, arg_expr.asInt());
            }

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

    /// Parses `PrefixExpr = [ UnaryOp | RangePrefix ] PrimaryExpr` (`DR-22` Section 3.2 Tier 14, `r_bp = 28`).
    fn parsePrefixExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        const cur_kind = self.peekKind();
        if (cur_kind == .kw_own and
            (self.peekKindNth(1) == .pipe or
                self.peekKindNth(1) == .pipepipe or
                (self.peekKindNth(1) == .kw_async and
                    (self.peekKindNth(2) == .pipe or self.peekKindNth(2) == .pipepipe))))
        {
            return self.parseClosureExpr(is_struct_lit_allowed);
        }

        if (cur_kind == .dotdot or cur_kind == .dotdoteq) {
            const pref_cst = try self.startCstNode(.prefix_expr);
            self.pushState(.expr_prefix_finish, pref_cst) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    return self.recoverDepthOverflow(pref_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                },
                else => return err,
            };
            defer self.popStates(1);

            const saved_stmt_lhs = self.is_in_stmt_lhs;
            const saved_lhs_place = self.is_in_lhs_place;
            self.is_in_stmt_lhs = false;
            self.is_in_lhs_place = false;
            defer {
                self.is_in_stmt_lhs = saved_stmt_lhs;
                self.is_in_lhs_place = saved_lhs_place;
            }

            const range_tok = try self.consumeLeaf(.token_leaf, .{});
            var end_op: PackedOperand = .NONE;
            if (cur_kind == .dotdoteq or isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                end_op = PackedOperand.initNode(try self.parseExprBp(13, is_struct_lit_allowed));
            }

            var has_range_err = false;
            if (isRangeOp(self.peekKind())) {
                has_range_err = true;
                const chain_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    chain_tok,
                    "chained range operators are non-associative in CoreX",
                    "add explicit parentheses around the range operand",
                );
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                if (isExprStart(self.peekKind(), is_struct_lit_allowed)) {
                    _ = try self.parseExprBp(13, is_struct_lit_allowed);
                }
            }

            self.cst.finishNode(pref_cst, .{ .has_error = has_range_err });
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .range_expr,
                .main_token = range_tok,
                .rhs = end_op,
            }, pref_cst);
        }

        // Retired standalone call-site / borrow prefix (`ref [mut] place`, `inout place`, `sink expr`, `set place`):
        if (cur_kind == .ident) {
            if (RETIRED_PARAM_MODE_MAP.get(self.peekLexemeNth(0))) |retired_kind| {
                const next_kind = self.peekKindNth(1);
                const is_retired_ref = retired_kind == .ref and
                    (next_kind == .kw_mut or next_kind == .ident or next_kind == .kw_self_val);
                const is_retired_mode = (retired_kind == .inout or retired_kind == .sink or retired_kind == .set) and
                    (next_kind == .ident or next_kind == .kw_self_val);
                if (is_retired_ref or is_retired_mode) {
                    const pref_cst = try self.startCstNode(.prefix_expr);
                    self.pushState(.expr_prefix_finish, pref_cst) catch |err| switch (err) {
                        error.ParseDepthExceeded => {
                            return self.recoverDepthOverflow(pref_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                        },
                        else => return err,
                    };
                    defer self.popStates(1);

                    const first_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    var end_tok = first_tok;
                    var is_ref_mut = false;
                    if (is_retired_ref and self.peekKind() == .kw_mut) {
                        is_ref_mut = true;
                        end_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    }
                    const first_span = self.getTokenSpan(first_tok);
                    const end_span = self.getTokenSpan(end_tok);
                    const next_tok = self.peekTokenIndexNth(0);
                    const next_span = self.getTokenSpan(next_tok);
                    const has_only_spaces = blk_spaces: {
                        for (self.token_buffer.getLeadingTrivia(next_tok)) |piece| {
                            if (piece.kind != .spaces) break :blk_spaces false;
                        }
                        break :blk_spaces !self.peekNth(0).flags.has_leading_newline;
                    };
                    const diag_span = Span.init(self.file_id, first_span.start_byte, end_span.end_byte);
                    const fix_end = if (has_only_spaces and next_span.start_byte >= end_span.end_byte)
                        next_span.start_byte
                    else
                        end_span.end_byte;
                    const is_with_space = fix_end > end_span.end_byte;
                    const replacement = switch (retired_kind) {
                        .ref => if (is_ref_mut) (if (is_with_space) "&mut " else "&mut") else "&",
                        .inout, .yielded => if (is_with_space) "&mut " else "&mut",
                        .sink => if (is_with_space) "own " else "own",
                        .out, .set => if (is_with_space) "&out " else "&out",
                    };

                    try self.emitDiagnosticWithFix(
                        .e0221_retired_mutability_or_param_mode,
                        diag_span,
                        "retired call-site / borrow prefix (`ADR-22B`); use `&`, `&mut`, `&out`, or `own`",
                        "retired call-site or borrow prefix",
                        Span.init(self.file_id, first_span.start_byte, fix_end),
                        replacement,
                        "replace with canonical CoreX borrow/ownership prefix",
                    );

                    const saved_stmt_lhs = self.is_in_stmt_lhs;
                    const saved_lhs_place = self.is_in_lhs_place;
                    self.is_in_stmt_lhs = false;
                    self.is_in_lhs_place = false;
                    const operand = blk_ret_pref: {
                        defer {
                            self.is_in_stmt_lhs = saved_stmt_lhs;
                            self.is_in_lhs_place = saved_lhs_place;
                        }
                        break :blk_ret_pref try self.parseExprBp(28, is_struct_lit_allowed);
                    };
                    self.cst.finishNode(pref_cst, .{ .has_error = true });
                    self.has_last_expr_block_body = false;
                    return self.ast.appendNodeWithCst(.{
                        .tag = .unary_expr,
                        .main_token = first_tok,
                        .lhs = PackedOperand.initNode(operand),
                    }, pref_cst);
                }
            }
        }

        if (getPrefixRightBindingPower(cur_kind)) |right_bp| {
            const pref_cst = try self.startCstNode(.prefix_expr);
            self.pushState(.expr_prefix_finish, pref_cst) catch |err| switch (err) {
                error.ParseDepthExceeded => {
                    return self.recoverDepthOverflow(pref_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                },
                else => return err,
            };
            defer self.popStates(1);

            var has_pref_err = false;
            const op_kind = self.peekKind();
            const op_tok = try self.consumeLeaf(.token_leaf, .{});

            if (op_kind == .amp) {
                if (self.peekKind() == .kw_mut) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                } else if (self.peekKind() == .ident) {
                    const mod_lexeme = self.peekLexemeNth(0);
                    const after_mod = self.peekKindNth(1);
                    const after_lparen = self.peekKindNth(2);
                    if (std.mem.eql(u8, mod_lexeme, "out") and
                        isUnambiguousAddrOperandStart(after_mod, after_lparen))
                    {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                    } else if (std.mem.eql(u8, mod_lexeme, "raw") and
                        (after_mod == .kw_mut or
                            isUnambiguousAddrOperandStart(after_mod, after_lparen)))
                    {
                        _ = try self.consumeLeaf(.token_leaf, .{});
                        if (self.peekKind() == .kw_mut) {
                            _ = try self.consumeLeaf(.token_leaf, .{});
                        }
                    } else if (RETIRED_PARAM_MODE_MAP.get(mod_lexeme)) |retired_amp_kind| {
                        if ((retired_amp_kind == .inout or retired_amp_kind == .sink or retired_amp_kind == .set) and
                            isUnambiguousAddrOperandStart(after_mod, after_lparen))
                        {
                            has_pref_err = true;
                            const mod_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                            const amp_span = self.getTokenSpan(op_tok);
                            const mod_span = self.getTokenSpan(mod_tok);
                            const diag_span = Span.init(self.file_id, amp_span.start_byte, mod_span.end_byte);
                            const replacement = switch (retired_amp_kind) {
                                .inout, .yielded, .ref => "&mut",
                                .sink => "own",
                                .out, .set => "&out",
                            };
                            try self.emitDiagnosticWithFix(
                                .e0221_retired_mutability_or_param_mode,
                                diag_span,
                                "retired `&inout` / `&sink` / `&set` spelling (`ADR-22B`); write `&mut`, `own`, or `&out`",
                                "retired borrow/projection modifier",
                                diag_span,
                                replacement,
                                "replace with canonical CoreX prefix",
                            );
                        }
                    }
                } else if (self.peekKind() == .kw_let and
                    isUnambiguousAddrOperandStart(self.peekKindNth(1), self.peekKindNth(2)))
                {
                    has_pref_err = true;
                    const let_tok = try self.consumeLeaf(.token_leaf, .{ .has_error = true });
                    const amp_span = self.getTokenSpan(op_tok);
                    const let_span = self.getTokenSpan(let_tok);
                    const next_span = self.getTokenSpan(self.peekTokenIndexNth(0));
                    const diag_span = Span.init(self.file_id, amp_span.start_byte, let_span.end_byte);
                    const fix_span = Span.init(
                        self.file_id,
                        amp_span.start_byte,
                        @max(let_span.end_byte, next_span.start_byte),
                    );
                    try self.emitDiagnosticWithFix(
                        .e0221_retired_mutability_or_param_mode,
                        diag_span,
                        "`&let` borrow spelling has been retired (`ADR-22B`); write `&` instead",
                        "retired `&let`; write `&`",
                        fix_span,
                        "&",
                        "replace `&let ` with `&`",
                    );
                }
            }

            const first_operand_tok = self.peekTokenIndexNth(0);
            const saved_stmt_lhs = self.is_in_stmt_lhs;
            const saved_lhs_place = self.is_in_lhs_place;
            self.is_in_stmt_lhs = saved_stmt_lhs and (op_kind == .star);
            self.is_in_lhs_place = saved_lhs_place and (op_kind == .star);
            const operand_cst_start = self.cst.countNodes();
            const operand = blk_pref: {
                defer {
                    self.is_in_stmt_lhs = saved_stmt_lhs;
                    self.is_in_lhs_place = saved_lhs_place;
                }
                break :blk_pref try self.parseExprBp(right_bp, is_struct_lit_allowed);
            };

            if (op_kind == .bang) {
                has_pref_err = true;
                const bang_span = self.getTokenSpan(op_tok);
                try self.emitDiagnosticWithFix(
                    .e0220_retired_bang_prefix,
                    bang_span,
                    "prefix `!` has been retired (`ADR-22A`); write `not expr` for boolean negation or `~expr` for bitwise NOT",
                    "retired `!` prefix operator",
                    null,
                    null,
                    null,
                );
            } else if (op_kind == .star) {
                has_pref_err = true;
                const star_span = self.getTokenSpan(op_tok);
                var full_span = star_span;
                var opt_fix_text: ?[]u8 = null;
                defer if (opt_fix_text) |allocated| self.ast.allocator.free(allocated);

                if (!first_operand_tok.isNone() and self.cursor > first_operand_tok.asInt()) {
                    const last_operand_tok = TokenIndex.fromInt(self.cursor - 1);
                    const op_start = self.getTokenSpan(first_operand_tok).start_byte;
                    const op_end = self.getTokenSpan(last_operand_tok).end_byte;
                    if (op_end >= op_start and op_end <= self.source.len) {
                        full_span = Span.init(self.file_id, star_span.start_byte, op_end);
                        const op_slice = self.source[op_start..op_end];
                        const is_paren_wrapped = blk_paren: {
                            if (operand_cst_start >= self.cst.countNodes()) break :blk_paren false;
                            const op_cst = self.cst.getNode(CstNodeIndex.fromInt(@intCast(operand_cst_start)));
                            break :blk_paren op_cst.kind == .tuple_or_paren_expr and
                                operand_cst_start + @as(usize, op_cst.subtree_size) == self.cst.countNodes();
                        };
                        const operand_node = self.ast.getNode(operand);
                        const is_postfix_tight = is_paren_wrapped or switch (operand_node.tag) {
                            .ident_expr,
                            .self_val,
                            .field_access,
                            .method_call,
                            .call_expr,
                            .generic_call,
                            .index_expr,
                            .try_expr,
                            .await_expr,
                            => true,
                            .deref_expr => !operand_node.main_token.isNone() and
                                self.token_buffer.getToken(operand_node.main_token).kind != .star,
                            else => false,
                        };
                        opt_fix_text = if (is_postfix_tight)
                            try std.fmt.allocPrint(self.ast.allocator, "{s}.*", .{op_slice})
                        else
                            try std.fmt.allocPrint(self.ast.allocator, "({s}).*", .{op_slice});
                    }
                }
                try self.emitDiagnosticWithFix(
                    .e0227_retired_prefix_deref,
                    full_span,
                    "prefix `*ptr` dereference has been retired (`ADR-22F`); write postfix `ptr.*` instead",
                    "retired prefix `*` dereference; write `.*`",
                    if (opt_fix_text != null) full_span else null,
                    opt_fix_text,
                    "rewrite as postfix `.*` dereference",
                );
                self.cst.finishNode(pref_cst, .{ .has_error = true });
                self.has_last_expr_block_body = false;
                return self.ast.appendNodeWithCst(.{
                    .tag = .deref_expr,
                    .main_token = op_tok,
                    .lhs = PackedOperand.initNode(operand),
                }, pref_cst);
            }

            self.cst.finishNode(pref_cst, .{ .has_error = has_pref_err });
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .unary_expr,
                .main_token = op_tok,
                .lhs = PackedOperand.initNode(operand),
            }, pref_cst);
        }
        return self.parsePrimaryExpr(is_struct_lit_allowed);
    }

    /// Returns `true` if `@` at `peek(0)` begins an attributed closure expression (`@attr [own] [async] |…|`).
    fn isAttributedClosureExpr(self: *const Parser) bool {
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
        if (lookahead == 0) return false;
        if (self.peekKindNth(lookahead) == .kw_own) lookahead += 1;
        if (self.peekKindNth(lookahead) == .kw_async) lookahead += 1;
        const open_kind = self.peekKindNth(lookahead);
        return open_kind == .pipe or open_kind == .pipepipe;
    }

    /// Parses a `PrimaryExpr` (`DR-03` Section 5.4 Part 8 & `DR-22` Section 3.3).
    fn parsePrimaryExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        const saved_stmt_lhs = self.is_in_stmt_lhs;
        const saved_lhs_place = self.is_in_lhs_place;
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
            .byte_lit => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .byte_lit, .main_token = tok }, leaf_cst);
            },
            .byte_string_lit => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .byte_string_lit, .main_token = tok }, leaf_cst);
            },
            .kw_true, .kw_false => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .bool_lit, .main_token = tok }, leaf_cst);
            },
            .underscore => {
                if (saved_lhs_place and (!saved_stmt_lhs or isAssignOp(self.peekKindNth(1)))) {
                    const tok = try self.consumeLeaf(.wildcard_pat, .{});
                    const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                    return self.ast.appendNodeWithCst(.{
                        .tag = .wildcard_pat,
                        .main_token = tok,
                    }, leaf_cst);
                }
                const err_tok = self.peekTokenIndexNth(0);
                try self.emitUnexpectedToken(
                    err_tok,
                    "`_` discard placeholder is only valid on the left-hand side of an assignment or in a pattern",
                    "unexpected `_` in expression",
                );
                const hole_cst = try self.startCstNode(.invalid_parse_subtree);
                _ = try self.consumeLeaf(.invalid_parse_leaf, .{ .has_error = true });
                self.cst.finishNode(hole_cst, .{ .has_error = true });
                return self.ast.appendNodeWithCst(.{
                    .tag = .expr_hole,
                    .main_token = err_tok,
                }, hole_cst);
            },
            .kw_self_val => {
                const tok = try self.consumeLeaf(.self_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .self_val, .main_token = tok }, leaf_cst);
            },
            .dollar => {
                const tok = try self.consumeLeaf(.literal_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .dollar_expr, .main_token = tok }, leaf_cst);
            },
            .kw_context => {
                const tok = try self.consumeLeaf(.self_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(.{ .tag = .context_expr, .main_token = tok }, leaf_cst);
            },
            .kw_unreachable => {
                const tok = try self.consumeLeaf(.diverging_expr, .{});
                const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                return self.ast.appendNodeWithCst(
                    .{ .tag = .unreachable_expr, .main_token = tok },
                    leaf_cst,
                );
            },
            .kw_return, .kw_break, .kw_continue => {
                return self.parseDivergingJumpExpr(is_struct_lit_allowed);
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
                if (self.isWalrusAfterLParen()) {
                    return self.parseWalrusCondExpr();
                }

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
                const saved_cond_header = self.is_in_cond_header;
                defer self.is_in_cond_header = saved_cond_header;

                while (self.peekKind() != .rparen and
                    self.peekKind() != .rbrace and
                    self.peekKind() != .semi and
                    self.peekKind() != .eof)
                {
                    const loop_start = self.cursor;
                    try elem_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());
                    if (self.peekKind() == .comma) {
                        has_comma = true;
                        self.is_in_cond_header = false;
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
                const saved_cond_header = self.is_in_cond_header;
                self.is_in_cond_header = false;
                defer self.is_in_cond_header = saved_cond_header;

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
            .kw_match => return self.parseMatchExpr(null),
            .kw_for => return self.parseForExpr(null, .none),
            .kw_while => return self.parseWhileExpr(null, .none),
            .kw_loop => return self.parseLoopExpr(null, .none),
            .kw_with => return self.parseWithExpr(),
            .at => {
                if (self.isAttributedClosureExpr()) {
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
                if (self.peekKindNth(1) == .kw_for) {
                    return self.parseForExpr(null, .none);
                }

                const comp_cst = try self.startCstNode(.prefix_expr);
                self.pushState(.expr_prefix_finish, comp_cst) catch |parse_err| switch (parse_err) {
                    error.ParseDepthExceeded => {
                        return self.recoverDepthOverflow(comp_cst, EXPR_SYNC_STOP_SET, .expr_hole);
                    },
                    else => return parse_err,
                };
                defer self.popStates(1);

                const saved_place = self.is_in_lhs_place;
                self.is_in_lhs_place = false;
                defer self.is_in_lhs_place = saved_place;

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
                        const parsed_match = try self.parseMatchExpr(null);
                        has_inner_block = true;
                        break :blk parsed_match;
                    },
                    else => blk: {
                        const parsed_expr = try self.parseExprBp(28, is_struct_lit_allowed);
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
                if (self.peekKind() == .kw_async) {
                    if (self.peekKindNth(1) == .dot) {
                        const async_tok = try self.consumeLeaf(.ident_pat, .{});
                        const leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
                        return self.ast.appendNodeWithCst(.{
                            .tag = .ident_expr,
                            .main_token = async_tok,
                        }, leaf_cst);
                    }
                    if (self.peekKindNth(1) == .pipe or self.peekKindNth(1) == .pipepipe) {
                        return self.parseClosureExpr(is_struct_lit_allowed);
                    }
                }
                const blk_cst = try self.startCstNode(.block);
                _ = try self.consumeLeaf(.token_leaf, .{});
                const inner_blk = try self.parseBlock();
                self.cst.finishNode(blk_cst, .{});
                if (!inner_blk.isNone() and inner_blk.asInt() < self.ast.ast_to_cst.items.len) {
                    self.ast.ast_to_cst.items[inner_blk.asInt()] = blk_cst;
                }
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

    /// Parses a parenthesized `WalrusCondExpr = "(" ["var"] IDENT [":" Type] ":=" Expr ")"`.
    fn parseWalrusCondExpr(self: *Parser) anyerror!NodeIndex {
        const walrus_cst = try self.startCstNode(.walrus_cond_expr);
        self.pushState(.delimited_paren, walrus_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(walrus_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        var has_err = false;
        const open_paren = try self.consumeLeaf(.token_leaf, .{});
        var is_var = false;
        if (self.peekKind() == .kw_var) {
            is_var = true;
            _ = try self.consumeLeaf(.token_leaf, .{});
        }
        const ident_tok = try self.expectIdentifierWithCasing(
            .ident,
            .snake_case,
            &has_err,
            "expected `snake_case` binding identifier in `(… := …)`",
        );

        var type_node: NodeIndex = .none;
        if (self.peekKind() == .colon) {
            _ = try self.consumeLeaf(.token_leaf, .{});
            type_node = try self.parseType();
        }

        const colon_eq_tok = try self.expectToken(
            .colon_eq,
            &has_err,
            "expected `:=` in parenthesized condition binding",
            "expected `:=` here",
        );

        const is_valid_header = self.is_in_cond_header;
        self.is_in_cond_header = false;
        const init_expr = blk_init: {
            defer self.is_in_cond_header = is_valid_header;
            break :blk_init try self.parseExpr(true);
        };

        try self.expectClosingDelimiter(
            .rparen,
            open_paren,
            &has_err,
            "expected `)` to close `:=` condition binding",
        );

        if (!is_valid_header) {
            try self.emitWalrusPositionError(
                self.getTokenSpan(colon_eq_tok),
                "`:=` condition binding is not allowed outside an `if` or `while` header",
                "use `let` or `var` for a local binding statement, or move `(… := …)` into an `if` or `while` condition",
            );
            self.cst.finishNode(walrus_cst, .{ .has_error = true });
            self.has_last_expr_block_body = false;
            return self.ast.appendNodeWithCst(.{
                .tag = .expr_hole,
                .main_token = colon_eq_tok,
            }, walrus_cst);
        }

        self.cst.finishNode(walrus_cst, .{ .has_error = has_err });
        self.has_last_expr_block_body = false;
        const extra_words = [_]u32{
            @intFromBool(is_var),
            type_node.asInt(),
            init_expr.asInt(),
        };
        const extra_idx = try self.ast.appendExtraSlice(&extra_words);
        return self.ast.appendNodeWithCst(.{
            .tag = .walrus_expr,
            .main_token = colon_eq_tok,
            .lhs = PackedOperand.initToken(ident_tok),
            .rhs = PackedOperand.initExtra(extra_idx),
        }, walrus_cst);
    }

    /// Parses `LoopExpr = [label ":"] "loop" Block`.
    fn parseLoopExpr(
        self: *Parser,
        opt_existing_cst: ?CstNodeIndex,
        label_tok: TokenIndex,
    ) anyerror!NodeIndex {
        const loop_cst = opt_existing_cst orelse try self.startCstNode(.loop_expr);
        const loop_tok = try self.consumeLeaf(.loop_introducer, .{});
        const body_node = try self.parseBlock();
        self.cst.finishNode(loop_cst, .{});
        self.has_last_expr_block_body = true;
        return self.ast.appendNodeWithCst(.{
            .tag = .loop_expr,
            .main_token = loop_tok,
            .lhs = PackedOperand.initNode(body_node),
            .rhs = if (!label_tok.isNone()) PackedOperand.initToken(label_tok) else .NONE,
        }, loop_cst);
    }

    /// Parses `WithExpr = "with" ContextBinding { "," ContextBinding } [","] Block` (`SE-08`).
    fn parseWithExpr(self: *Parser) anyerror!NodeIndex {
        const with_cst = try self.startCstNode(.with_expr);
        self.pushState(.block_stmt_loop, with_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(with_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        const saved_cond_header = self.is_in_cond_header;
        self.is_in_cond_header = false;
        defer self.is_in_cond_header = saved_cond_header;

        var has_error = false;
        const with_tok = try self.consumeLeaf(.token_leaf, .{});

        var binding_words: std.ArrayList(u32) = .empty;
        defer binding_words.deinit(self.ast.allocator);
        try binding_words.append(self.ast.allocator, 0);
        var binding_count: u32 = 0;

        while (self.peekKind() != .lbrace and
            self.peekKind() != .rbrace and
            self.peekKind() != .semi and
            self.peekKind() != .eof)
        {
            const loop_start = self.cursor;
            const bind_cst = try self.startCstNode(.context_binding);
            var has_bind_err = false;

            _ = try self.expectToken(
                .kw_context,
                &has_bind_err,
                "expected `context.<slot> = expr` binding after `with`",
                "expected `context` here",
            );
            _ = try self.expectToken(
                .dot,
                &has_bind_err,
                "expected `.` after `context` in `with` binding",
                "expected `.` here",
            );
            const slot_tok = try self.expectIdentifierWithCasing(
                .ident,
                .snake_case,
                &has_bind_err,
                "expected `snake_case` context slot identifier after `context.`",
            );
            _ = try self.expectToken(
                .eq,
                &has_bind_err,
                "expected `=` after `context.<slot>`",
                "expected `=` here",
            );
            const val_expr = try self.parseExpr(false);

            if (has_bind_err) has_error = true;
            self.cst.finishNode(bind_cst, .{ .has_error = has_bind_err });

            try binding_words.append(self.ast.allocator, slot_tok.asInt());
            try binding_words.append(self.ast.allocator, val_expr.asInt());
            binding_count += 1;

            if (self.peekKind() == .comma) {
                _ = try self.consumeLeaf(.token_leaf, .{});
            } else {
                break;
            }
            if (self.cursor == loop_start) break;
        }

        if (binding_count == 0) {
            has_error = true;
            try self.emitUnexpectedToken(
                self.peekTokenIndexNth(0),
                "expected `context.<slot> = expr` binding after `with`",
                "missing context binding",
            );
        }
        binding_words.items[0] = binding_count;

        const body_block = try self.parseBlock();
        self.cst.finishNode(with_cst, .{ .has_error = has_error });
        self.has_last_expr_block_body = true;

        const extra_idx = try self.ast.appendExtraSlice(binding_words.items);
        return self.ast.appendNodeWithCst(.{
            .tag = .with_expr,
            .main_token = with_tok,
            .lhs = PackedOperand.initExtra(extra_idx),
            .rhs = PackedOperand.initNode(body_block),
        }, with_cst);
    }

    /// Parses an identifier, type, primitive type, or labeled loop/`match` primary expression.
    fn parsePathOrConstructExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        _ = is_struct_lit_allowed;
        try self.flushCarrierTokens();

        // Labeled loop or `match` (`label: for …`, `label: while …`, `label: loop …`, `label: match …`):
        if (self.isLabeledLoopStart()) {
            const loop_kind = switch (self.peekKindNth(2)) {
                .kw_while => CstNodeKind.while_stmt,
                .kw_loop => CstNodeKind.loop_expr,
                .kw_match => CstNodeKind.match_expr,
                else => CstNodeKind.for_stmt,
            };
            const outer_cst = try self.startCstNode(loop_kind);
            const label_cst = try self.startCstNode(.loop_label);
            var has_label_err = false;
            const label_tok = try self.expectIdentifierWithCasing(
                .ident,
                .snake_case,
                &has_label_err,
                "expected `snake_case` loop or `match` label",
            );
            _ = try self.consumeLeaf(.token_leaf, .{});
            self.cst.finishNode(label_cst, .{ .has_error = has_label_err });

            return switch (loop_kind) {
                .while_stmt => self.parseWhileExpr(outer_cst, label_tok),
                .loop_expr => self.parseLoopExpr(outer_cst, label_tok),
                .match_expr => self.parseMatchExpr(outer_cst),
                else => self.parseForExpr(outer_cst, label_tok),
            };
        }

        const first_tok = try self.consumeLeaf(.ident_pat, .{});
        const first_leaf_cst = CstNodeIndex.fromInt(@intCast(self.cst.countNodes() - 1));
        return self.ast.appendNodeWithCst(.{
            .tag = .ident_expr,
            .main_token = first_tok,
        }, first_leaf_cst);
    }

    /// Parses `StructLiteral = "{" [ FieldInit { "," FieldInit } [ "," ] ] [ ".." [ ["own"] Expr ] [ "," ] ] "}" ;` (`SE-14`).
    fn parseStructLiteralBody(
        self: *Parser,
        field_nodes: *std.ArrayList(u32),
        has_error: *bool,
    ) anyerror!void {
        const saved_cond_header = self.is_in_cond_header;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_cond_header = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_cond_header = saved_cond_header;
            self.is_in_lhs_place = saved_lhs_place;
        }
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
                const dotdot_tok = try self.consumeLeaf(.token_leaf, .{});
                if (self.peekKind() != .rbrace and
                    self.peekKind() != .comma and
                    self.peekKind() != .eof)
                {
                    try field_nodes.append(self.ast.allocator, (try self.parseExpr(true)).asInt());
                }
                self.cst.finishNode(field_cst, .{});
                if (self.peekKind() == .comma) {
                    _ = try self.consumeLeaf(.token_leaf, .{});
                }
                if (self.peekKind() != .rbrace and self.peekKind() != .eof) {
                    has_error.* = true;
                    try self.emitUnexpectedToken(
                        dotdot_tok,
                        "`..` struct spread/default rest must be the final entry in a struct literal",
                        "move `..` to the end of the struct literal",
                    );
                    continue;
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

    /// Parses `ClosureExpr = { Attribute } ["own"] ["async"] ("||" | "|" … "|") ["->" Type] (Block | Expr)` (`SE-19`, `SE-20`).
    fn parseClosureExpr(self: *Parser, is_struct_lit_allowed: bool) anyerror!NodeIndex {
        const saved_cond_header = self.is_in_cond_header;
        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_cond_header = false;
        self.is_in_lhs_place = false;
        defer {
            self.is_in_cond_header = saved_cond_header;
            self.is_in_lhs_place = saved_lhs_place;
        }

        const clos_cst = try self.startCstNode(.closure_expr);
        var has_error = false;
        if (self.peekKind() == .at) {
            try self.parseAttributes(&has_error);
        }
        if (self.peekKind() == .kw_own) {
            _ = try self.consumeLeaf(.token_leaf, .{});
        }
        if (self.peekKind() == .kw_async) {
            _ = try self.consumeLeaf(.token_leaf, .{});
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

                if (self.peekKind() == .kw_var or
                    self.peekKind() == .amp or
                    self.peekKind() == .kw_mut or
                    self.peekKind() == .kw_own or
                    self.isRetiredRefPatAt(0))
                {
                    _ = try self.consumePatternBindingModifier(&has_param_err);
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

    /// Parses `IfExpr = "if" CondExprNoStruct Block ["else" (IfExpr | Block)]` (`DR-21` `SE-01` & `SE-02`).
    fn parseIfExpr(self: *Parser) anyerror!NodeIndex {
        const if_cst = try self.startCstNode(.if_expr);
        self.pushState(.if_after_cond, if_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(if_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_lhs_place = false;
        defer self.is_in_lhs_place = saved_lhs_place;

        var has_error = false;
        const if_tok = try self.consumeLeaf(.if_introducer, .{});

        const cond_cst = try self.startCstNode(.if_cond);
        var cond_node: NodeIndex = .none;
        if (self.peekKind() == .kw_let) {
            cond_node = try self.parseRetiredIfWhileLet(cond_cst, "if", &has_error);
        } else {
            const saved_cond_header = self.is_in_cond_header;
            self.is_in_cond_header = true;
            cond_node = blk_cond: {
                defer self.is_in_cond_header = saved_cond_header;
                break :blk_cond try self.parseExpr(false);
            };
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

    /// Parses `MatchExpr = [IDENT ":"] "match" ExprNoStruct "{" { MatchArm } "}" ;` (`SE-23`).
    fn parseMatchExpr(self: *Parser, opt_existing_cst: ?CstNodeIndex) anyerror!NodeIndex {
        const match_cst = opt_existing_cst orelse try self.startCstNode(.match_expr);
        self.pushState(.match_arms_loop, match_cst) catch |err| switch (err) {
            error.ParseDepthExceeded => {
                return self.recoverDepthOverflow(match_cst, EXPR_SYNC_STOP_SET, .expr_hole);
            },
            else => return err,
        };
        defer self.popStates(1);

        const saved_lhs_place = self.is_in_lhs_place;
        self.is_in_lhs_place = false;
        defer self.is_in_lhs_place = saved_lhs_place;

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
        const old_eof_tok = TokenIndex.fromInt(@intCast(token_buffer.countTokens() - 1));
        const old_eof_offset = token_buffer.getToken(old_eof_tok).byte_offset;
        const byte_delta: i64 = @as(i64, edit.new_end_byte) - @as(i64, edit.old_end_byte);

        if (@as(i64, old_eof_offset) + byte_delta == @as(i64, @intCast(new_source.len))) {
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

            var has_potential_lexer_warn_in_reused = false;
            if (diagnostic_sink != null and (prefix_count > 0 or suffix_start < total_items)) {
                const prefix_tok_limit: usize = if (prefix_count < total_items)
                    windows[prefix_count].first_token
                else
                    old_eof_tok.asInt();
                const suffix_tok_begin: usize = if (suffix_start < total_items)
                    windows[suffix_start].first_token
                else
                    old_eof_tok.asInt();
                const tok_kinds = token_buffer.tokens.items(.kind);
                const tok_offsets = token_buffer.tokens.items(.byte_offset);
                const tok_lens = token_buffer.tokens.items(.byte_len);
                var tok_idx: usize = 0;
                while (tok_idx < old_eof_tok.asInt()) : (tok_idx += 1) {
                    if (tok_idx >= prefix_tok_limit and tok_idx < suffix_tok_begin) {
                        tok_idx = suffix_tok_begin - 1;
                        continue;
                    }
                    const tok_kind = tok_kinds[tok_idx];
                    if (tok_kind == .string_lit or tok_kind == .char_lit or
                        tok_kind == .byte_lit or tok_kind == .byte_string_lit)
                    {
                        const new_off_i64: i64 = if (tok_idx < prefix_tok_limit)
                            @as(i64, tok_offsets[tok_idx])
                        else
                            @as(i64, tok_offsets[tok_idx]) + byte_delta;
                        if (new_off_i64 >= 0) {
                            const new_off: usize = @intCast(new_off_i64);
                            const lit_slice = new_source[new_off..@min(new_off + tok_lens[tok_idx], new_source.len)];
                            if (std.mem.indexOfScalar(u8, lit_slice, '\\') != null and
                                (std.mem.indexOf(u8, lit_slice, "\\'") != null or
                                    std.mem.indexOf(u8, lit_slice, "\\\"") != null or
                                    std.mem.indexOf(u8, lit_slice, "\\{") != null or
                                    std.mem.indexOf(u8, lit_slice, "\\}") != null))
                            {
                                has_potential_lexer_warn_in_reused = true;
                                break;
                            }
                        }
                    }
                }
            }

            if (!has_potential_lexer_warn_in_reused and (prefix_count > 0 or suffix_start < total_items)) {
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

                var has_win_lex_err = has_stray_eof_trivia;
                if (!has_win_lex_err) {
                    for (window_sink.asSlice()) |diag_item| {
                        if (diag_item.code != .w0201_non_canonical_identifier_case) {
                            has_win_lex_err = true;
                            break;
                        }
                    }
                }
                if (!has_win_lex_err) {
                    const win_kinds = window_tokens.tokens.items(.kind);
                    for (window_tokens.tokens.items(.flags), 0..) |flag_item, win_i| {
                        if ((flag_item.has_lexer_error and !isIdentifierKind(win_kinds[win_i])) or
                            flag_item.is_synthesized)
                        {
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
                    defer win_parser.clearAllowedNonCanonicalNames();
                    try win_parser.precollectAllowedNonCanonicalNames();
                    win_parser.cursor = @intCast(tok_start);

                    var reparsed_items: u32 = 0;
                    while (win_parser.cursor < tok_new_end and win_parser.peekKind() != .eof) {
                        const before_cur = win_parser.cursor;
                        _ = try win_parser.parseItem();
                        reparsed_items += 1;
                        if (win_parser.cursor == before_cur) break;
                    }

                    if (!is_suffix_reused and win_parser.cursor < token_buffer.countTokens()) {
                        _ = try window_cst.appendLeafNode(.token_leaf, TokenIndex.fromInt(win_parser.cursor), .{});
                        win_parser.cursor += 1;
                    }

                    const expected_end_cursor: u32 = if (is_suffix_reused)
                        tok_new_end
                    else
                        @intCast(token_buffer.countTokens());

                    if (!window_cst.has_parse_errors and
                        window_sink.error_count == 0 and
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

                        try replayLexerCasingWarnings(
                            new_source,
                            file_id,
                            token_buffer,
                            diagnostic_sink,
                            interner,
                        );

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

/// Extracts an `InlineUseDeclView` from a `.use_item` CST subtree when its `.use_tree` begins with `.string_lit`.
pub fn extractInlineUseDeclView(
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
    item_cst: CstNodeIndex,
    ast_node: NodeIndex,
) ?InlineUseDeclView {
    if (item_cst.isNone() or item_cst.asInt() >= cst_arena.countNodes()) return null;
    const item_rec = cst_arena.getNode(item_cst);
    if (item_rec.kind != .use_item) return null;

    const item_start: usize = item_cst.asInt();
    const item_end: usize = @min(item_start + @max(@as(usize, item_rec.subtree_size), 1), cst_arena.countNodes());
    var is_pub = false;
    var tree_cst: CstNodeIndex = .none;
    var first_tok: TokenIndex = .none;
    var last_tok: TokenIndex = .none;

    var cursor: usize = item_start + 1;
    while (cursor < item_end) {
        const child_idx = CstNodeIndex.fromInt(@intCast(cursor));
        const child = cst_arena.getNode(child_idx);
        if (!child.token.isNone() and child.token.asInt() < token_buffer.countTokens()) {
            const tok_rec = token_buffer.getToken(child.token);
            if (!tok_rec.flags.is_synthesized) {
                if (first_tok.isNone()) first_tok = child.token;
                last_tok = child.token;
            }
        }
        if (child.kind == .attribute) {
            cursor += @max(@as(usize, child.subtree_size), 1);
            continue;
        }
        if (child.kind == .visibility_modifier) {
            is_pub = true;
            cursor += @max(@as(usize, child.subtree_size), 1);
            continue;
        }
        if (child.subtree_size <= 1 and !child.flags.is_bracketed and !child.token.isNone() and
            child.token.asInt() < token_buffer.countTokens())
        {
            if (token_buffer.getToken(child.token).kind == .kw_pub) is_pub = true;
        }
        if (child.kind == .use_tree and tree_cst.isNone()) {
            tree_cst = child_idx;
        }
        cursor += @max(@as(usize, child.subtree_size), 1);
    }

    if (tree_cst.isNone()) return null;
    const tree_rec = cst_arena.getNode(tree_cst);
    const tree_start: usize = tree_cst.asInt();
    const tree_end: usize = @min(tree_start + @max(@as(usize, tree_rec.subtree_size), 1), cst_arena.countNodes());

    var spec_tok: TokenIndex = .none;
    var alias_tok: TokenIndex = .none;
    var has_seen_as = false;
    var tree_cur: usize = tree_start + 1;
    while (tree_cur < tree_end) : (tree_cur += 1) {
        const leaf = cst_arena.getNode(CstNodeIndex.fromInt(@intCast(tree_cur)));
        if (leaf.kind == .use_tree and leaf.subtree_size > 1) return null;
        if (leaf.subtree_size <= 1 and !leaf.flags.is_bracketed and !leaf.token.isNone() and
            leaf.token.asInt() < token_buffer.countTokens())
        {
            const tok_rec = token_buffer.getToken(leaf.token);
            if (tok_rec.flags.is_synthesized) continue;
            if (spec_tok.isNone()) {
                if (tok_rec.kind != .string_lit and tok_rec.kind != .byte_string_lit) return null;
                spec_tok = leaf.token;
                continue;
            }
            if (tok_rec.kind == .kw_as) {
                has_seen_as = true;
                continue;
            }
            if (has_seen_as and alias_tok.isNone()) {
                alias_tok = leaf.token;
                last_tok = leaf.token;
            }
        }
    }
    if (spec_tok.isNone()) return null;

    const spec_rec = token_buffer.getToken(spec_tok);
    const spec_start: usize = spec_rec.byte_offset;
    const spec_end: usize = @min(spec_start + @as(usize, spec_rec.byte_len), source.len);
    const spec_lexeme = if (spec_start < spec_end) source[spec_start..spec_end] else "";
    const unquoted_spec = if (spec_rec.kind == .string_lit)
        (extractSingleLineUnquotedSpec(spec_lexeme) orelse "")
    else
        "";
    const spec_span = Span.init(file_id, @intCast(spec_start), @intCast(spec_end));

    var alias_slice: []const u8 = "";
    var alias_span = spec_span;
    if (!alias_tok.isNone() and alias_tok.asInt() < token_buffer.countTokens()) {
        const alias_rec = token_buffer.getToken(alias_tok);
        const alias_start: usize = alias_rec.byte_offset;
        const alias_end: usize = @min(alias_start + @as(usize, alias_rec.byte_len), source.len);
        if (alias_start < alias_end) alias_slice = source[alias_start..alias_end];
        alias_span = Span.init(file_id, @intCast(alias_start), @intCast(alias_end));
    }

    const decl_start: u32 = if (!first_tok.isNone()) token_buffer.getToken(first_tok).byte_offset else spec_span.start_byte;
    const decl_end: u32 = if (!last_tok.isNone()) blk: {
        const end_rec = token_buffer.getToken(last_tok);
        break :blk end_rec.byte_offset + end_rec.byte_len;
    } else alias_span.end_byte;

    return .{
        .ast_node = ast_node,
        .item_cst = item_cst,
        .spec_token = spec_tok,
        .unquoted_spec = unquoted_spec,
        .alias_token = alias_tok,
        .alias_slice = alias_slice,
        .spec_span = spec_span,
        .alias_span = alias_span,
        .decl_span = Span.init(file_id, decl_start, decl_end),
        .is_pub = is_pub,
    };
}

/// Scans `cst_arena` in source order and collects all inline string `use "<spec>" as <alias>;` views.
pub fn extractInlineStringUseSpecs(
    allocator: std.mem.Allocator,
    source: []const u8,
    file_id: FileId,
    token_buffer: *const TokenBuffer,
    cst_arena: *const LosslessCstArena,
) ![]InlineUseDeclView {
    var results: std.ArrayListUnmanaged(InlineUseDeclView) = .empty;
    errdefer results.deinit(allocator);

    const total_nodes = cst_arena.countNodes();
    var cursor: usize = 0;
    while (cursor < total_nodes) : (cursor += 1) {
        const node_idx = CstNodeIndex.fromInt(@intCast(cursor));
        if (cst_arena.getNode(node_idx).kind == .use_item) {
            if (extractInlineUseDeclView(source, file_id, token_buffer, cst_arena, node_idx, .none)) |view| {
                try results.append(allocator, view);
            }
        }
    }
    return results.toOwnedSlice(allocator);
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

    // [3] Every `extra_data` slice boundary must resolve cleanly via `computeAstNodeExtraEnds`:
    const extra_ends = try syntax_arenas.computeAstNodeExtraEnds(allocator, ast_arena);
    defer allocator.free(extra_ends);
    try std.testing.expectEqual(ast_arena.countNodes(), extra_ends.len);

    // [4] Lossless source reconstruction must be 100% byte-for-byte identical to `source`:
    const reconstructed = try cst_arena.reconstructSource(allocator, source, token_buf);
    defer allocator.free(reconstructed);
    try std.testing.expectEqualSlices(u8, source, reconstructed);
}

test "test_parser_all_four_dr21_domain_showcases_zero_errors" {
    const showcase_1_cli =
        \\mod cli_scanner;
        \\use cx.env;
        \\use cx.fs.{BufReader, File};
        \\use cx.io.{IoError, Stdout};
        \\use cx.mem.Arena;
        \\const DEFAULT_BUF_CAP: usize = 65_536;
        \\@cli_command(name: "cx-scan", version: "1.0.0")
        \\pub struct ScanOptions {
        \\    @arg(short: 'p', long: "pattern")
        \\    pub pattern: str,
        \\    @arg(short: 'f', long: "file")
        \\    pub file_path: str,
        \\    @flag(short: 'i', long: "ignore-case")
        \\    pub ignore_case: bool = false,
        \\    @arg(short: 'm', long: "max-matches")
        \\    pub max_matches: usize = 1_000,
        \\}
        \\pub struct ScanStats {
        \\    pub lines_scanned: u64,
        \\    pub matches_found: u64,
        \\    pub bytes_processed: u64,
        \\}
        \\pub fn scan_file(arena: &mut Arena, opts: &ScanOptions, out: &mut Stdout) -> ScanStats ! IoError {
        \\    let file = File.open(opts.file_path)?;
        \\    defer file.close();
        \\    var reader = BufReader.with_capacity(arena, file, DEFAULT_BUF_CAP);
        \\    var stats = ScanStats { lines_scanned: 0, matches_found: 0, bytes_processed: 0 };
        \\    while reader.next_line()? is .Some(line) {
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
        \\    var arena = Arena.with_capacity(1_048_576);
        \\    defer arena.release();
        \\    let opts = env.parse_args[ScanOptions](&mut arena) catch |err| {
        \\        cx.io.stderr().write_fmt("argument error: {err}\n");
        \\        return 2;
        \\    };
        \\    var stdout = Stdout.locked();
        \\    match scan_file(&mut arena, &opts, &mut stdout) {
        \\        .Ok(stats) => {
        \\            stdout.write_fmt("Scanned {stats.lines_scanned} lines\n");
        \\            0
        \\        }
        \\        .Err(err) => {
        \\            cx.io.stderr().write_fmt("I/O failure: {err}\n");
        \\            1
        \\        }
        \\    }
        \\}
    ;

    const showcase_2_api =
        \\mod user_api;
        \\use net.http.{Json, Request, Response, StatusCode};
        \\use db.pg.{PgPool, TxIsolation};
        \\use crypto.argon2;
        \\use serde.{Deserialize, Serialize};
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
        \\    pub fn into_response(self) -> Response = match self {
        \\        .PayloadTooLarge => Response.status(StatusCode.PayloadTooLarge),
        \\        .InvalidJson(msg) => Response.json(StatusCode.BadRequest, msg),
        \\        .ValidationFailed(reason) => Response.json(StatusCode.UnprocessableEntity, reason),
        \\        .ConflictEmail(email) => Response.json(StatusCode.Conflict, "Email: {email}"),
        \\        .DatabaseError(_) => Response.status(StatusCode.InternalServerError),
        \\    };
        \\}
        \\@route(method: "POST", path: "/v1/users")
        \\pub async fn create_user(req: &mut Request, pool: &PgPool) -> Json[CreateUserResp] ! ApiError {
        \\    let body_bytes = req.read_body_bounded(MAX_BODY_BYTES).await?;
        \\    let payload = body_bytes
        \\        |> Json.parse[CreateUserReq]()
        \\        catch |err| return .Err(ApiError.InvalidJson(err.message()));
        \\    if payload.username.len() < 3 or not payload.email.contains("@") {
        \\        return .Err(ApiError.ValidationFailed("invalid username or email"));
        \\    }
        \\    let password_hash = argon2.hash_password(payload.password_raw).await?;
        \\    let assigned_role = payload.role orelse .Member;
        \\    var tx = pool.begin_tx(TxIsolation.Serializable).await?;
        \\    defer tx.rollback_if_uncommitted();
        \\    let exists = tx.query_scalar[bool](
        \\        "SELECT EXISTS(SELECT 1 FROM users WHERE email = $1)",
        \\        [payload.email],
        \\    ).await?;
        \\    if exists {
        \\        return .Err(ApiError.ConflictEmail(payload.email));
        \\    }
        \\    let (user_id, created_at_unix) = tx.query_one[(u64, i64)](
        \\        "INSERT INTO users VALUES ($1, $2, $3, $4) RETURNING id, created_at",
        \\        [payload.username, payload.email, password_hash, assigned_role.as_str()],
        \\    ).await?;
        \\    tx.commit().await?;
        \\    .Ok(Json.from(CreateUserResp {
        \\        user_id,
        \\        username: payload.username,
        \\        created_at_unix,
        \\    }))
        \\}
    ;

    const showcase_3_avl =
        \\mod avl_tree;
        \\use cx.cmp.{Ord, Ordering};
        \\use cx.mem.{OwnPtr, PoolAllocator};
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
        \\    pub fn with_capacity(cap: usize) -> Self = Self {
        \\        root: .None,
        \\        pool: PoolAllocator.new[AvlNode[K, V]](cap),
        \\        len: 0,
        \\    };
        \\    fn rotate_right(var right_root: own OwnPtr[AvlNode[K, V]]) -> OwnPtr[AvlNode[K, V]] {
        \\        var pivot = right_root.left.take() orelse return right_root;
        \\        right_root.left = pivot.right.take();
        \\        Self.update_height(&mut right_root);
        \\        pivot.right = .Some(own right_root);
        \\        Self.update_height(&mut pivot);
        \\        pivot
        \\    }
        \\    fn rebalance(var node: own OwnPtr[AvlNode[K, V]]) -> OwnPtr[AvlNode[K, V]] {
        \\        let bf = Self.balance_factor(&node);
        \\        if bf > 1 {
        \\            if node.left is .Some(&left_child) and Self.balance_factor(left_child) < 0 {
        \\                let left_owned = node.left.take() orelse unreachable;
        \\                node.left = .Some(Self.rotate_left(own left_owned));
        \\            }
        \\            return Self.rotate_right(own node);
        \\        }
        \\        node
        \\    }
        \\}
    ;

    const showcase_4_ui =
        \\mod ui_telemetry;
        \\use cx.ui.core.{Color, Computed, Signal, Theme, View};
        \\use cx.ui.widgets.{Badge, Button, Card, Column, ProgressBar, Row, Text};
        \\pub struct MetricSample {
        \\    pub timestamp_ms: u64,
        \\    pub cpu_load: f32,
        \\    pub mem_used_mb: u32,
        \\}
        \\@component
        \\pub fn telemetry_dashboard(node_name: str, samples: &Signal[Vec[MetricSample]], theme: &Theme) -> View {
        \\    @state var is_paused: bool = false;
        \\    @state var threshold_pct: f32 = 80.0;
        \\    let latest_cpu = Computed.new(|| -> f32 {
        \\        match samples.get().last() {
        \\            .Some(sample) => sample.cpu_load,
        \\            .None => 0.0,
        \\        }
        \\    });
        \\    let is_critical = Computed.new(|| latest_cpu.get() >= threshold_pct);
        \\    Card(padding: 16, border_color: theme.border_subtle) {
        \\        Row(justify: .SpaceBetween, align: .Center) {
        \\            Text(value: "Node: {node_name}", weight: .Bold, size: 18);
        \\            if is_critical.get() {
        \\                Badge(label: "CRITICAL", color: Color.Red);
        \\            } else {
        \\                Badge(label: "HEALTHY", color: Color.Emerald);
        \\            }
        \\        }
        \\        Column(gap: 12) {
        \\            ProgressBar(
        \\                value: latest_cpu.get(),
        \\                max: 100.0,
        \\                tint: if is_critical.get() { Color.Red } else { Color.Cyan },
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

    // [1] `RT-01` – Malformed member projections (`foo.;` and `bar.;`) recover cleanly:
    const rt01_src = "fn test_rt01() { let first = foo.; let second = bar.; }\n";
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

    // [5] `RT-06` – Malformed patterns (`-true`, `1..`, `Foo.`) emit `E0201`:
    const rt06_src = "fn pat_err(val: i32) -> i32 { return match val { -true => 1, 1.. => 2, Foo. => 3 }; }\n";
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
        "    slot.* = 20;\n" ++
        "    let local_cb = @local |delta: i32| delta + slot.*;\n" ++
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

test "test_parser_dr21_surface_elevations_contracts_and_diagnostics" {
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

    // [1] Valid `DR-21` surface elevations (`SE-01`–`SE-08`, `.` paths, ranges, `$`, `with`):
    const valid_dr21_src =
        \\use cx.io.{self, self as io_mod, BufReader as Br, Read, Write};
        \\use cx.prelude.*;
        \\fn add_scaled(val: i32, scale: i32 = 2, pred: |i32| -> bool) -> i32 = val * scale;
        \\fn exercise_dr21(items: &[i32], opt: i32?, table: &[fn(i32) -> i32; 4]) -> i32 {
        \\    if (count: usize := items.len) > 0 and opt is not .None {
        \\        let tail = items[1..$-1];
        \\        let head = items[..2];
        \\        let incl = items[..=1];
        \\        let rest = items[1..];
        \\        let full = items[..];
        \\        let dyn_call = table[ColumnKey.Primary](tail[$-1]);
        \\        let piped = items[0] |> add_scaled(scale: 3, pred: |val| val > 0) orelse return 0;
        \\        let found = search: for &item, idx in items {
        \\            if item.* == piped {
        \\                break :search idx as i32;
        \\            }
        \\            continue :search;
        \\        } orelse -1;
        \\        with context.allocator = cx.mem.default_allocator() {
        \\            let alloc_ref = context.allocator;
        \\            match items {
        \\                [first, ..middle, last] => {
        \\                    if opt is wrapped @ .Some(inner) {
        \\                        return first + last + inner + found + dyn_call + (alloc_ref.id as i32);
        \\                    }
        \\                }
        \\                _ => unreachable,
        \\            }
        \\        }
        \\    }
        \\    return 0;
        \\}
    ;

    _ = try parseSource(
        valid_dr21_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        valid_dr21_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [2] `E0215` outside `if`/`while` condition header and bare `:=` statement:
    const invalid_walrus_src =
        \\fn bad_walrus() {
        \\    let bad_a = (val := 10);
        \\    bare := 20;
        \\}
    ;
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(
        invalid_walrus_src,
        FileId.fromInt(1),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 2), sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0215_invalid_walrus_position,
        sink.asSlice()[0].code,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0215_invalid_walrus_position,
        sink.asSlice()[1].code,
    );
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        invalid_walrus_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [3] `E0216` retired `if let` emits `.machine_applicable` `SuggestedFix` + `.is_expr` recovery:
    const retired_if_let_src =
        "fn old_style(opt: i32?) -> i32 { if let .Some(val) = opt { return val; } return 0; }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(
        retired_if_let_src,
        FileId.fromInt(2),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 1), sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0216_retired_if_while_let,
        sink.asSlice()[0].code,
    );
    try std.testing.expectEqual(@as(usize, 1), sink.asSlice()[0].suggestions.len);
    try std.testing.expectEqualStrings(
        "opt is .Some(val)",
        interner.get(sink.asSlice()[0].suggestions[0].edits[0].replacement_id),
    );
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        retired_if_let_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
}

test "test_parser_dr22_canonical_showcases_types_elevations_and_autofixes" {
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

    // [1] Valid `DR-22` canonical constructs (`ADR-22A`–`ADR-22F` & `SE-09`–`SE-23`):
    const valid_dr22_src =
        \\mod dr22_showcase;
        \\pub(pkg) use cx.mem.{Bencher, UiScope};
        \\
        \\@derive(Copy, Equatable)
        \\pub enum MemoryOrder: u8 {
        \\    Relaxed = 0,
        \\    Consume = 1,
        \\    Acquire = 2,
        \\    Release = 3,
        \\    AcqRel = 4,
        \\    SeqCst = 5,
        \\}
        \\
        \\pub(super) bit_field ControlReg: u32 {
        \\    pub(pkg) is_enabled: bool | 1,
        \\    mode_bits: u8 | 3,
        \\}
        \\
        \\pub type NumericOrOrd = Copy + Send | Ord;
        \\
        \\pub struct Matrix[T: Copy | Send + Sync = f32, const N: usize = 4] {
        \\    pub(pkg) cells: [T; N],
        \\    pub(super) raw_ptr: *mut u8?,
        \\    pub slice_opt: &[u8]?,
        \\    pub borrowed_opt: &MemoryOrder?,
        \\}
        \\
        \\extern "C" fn printf(fmt: *u8, ...) -> i32;
        \\
        \\impl[T: Copy, const N: usize] Matrix[T, N] {
        \\    @inline @no_alloc @no_panic
        \\    pub fn swap_ptrs(left: *mut T, right: *mut T, /, *, var count: usize = 1, dst: &out T) {
        \\        (left.*, right.*, _) = (right.*, left.*, count);
        \\        let raw_addr = &raw left.*;
        \\        let raw_mut_addr = &raw mut right.*;
        \\        unsafe {
        \\            dst.* = left.*;
        \\        }
        \\        _ = (raw_addr, raw_mut_addr);
        \\    }
        \\
        \\    pub subscript(row: usize, col: usize) -> &T {
        \\        let {
        \\            yield &self.cells[row + col];
        \\        }
        \\        inout {
        \\            yield &mut self.cells[row + col];
        \\        }
        \\    }
        \\}
        \\
        \\pub fn check_contextual_out_raw(
        \\    out: &mut ControlReg,
        \\    raw: &[u8],
        \\    mod_buf: &out_mod.Buffer,
        \\    ui_children: @builder |&mut UiScope|,
        \\    escaping_cb: own |i32| -> i32 ! MemoryOrder,
        \\) -> i32 ! MemoryOrder {
        \\    let borrow_out = &out;
        \\    let borrow_field = &out.is_enabled;
        \\    let borrow_raw_elem = &raw[0];
        \\    let header_byte = b'\n';
        \\    let magic_bytes = b"CX22";
        \\    let inverted = ~0x0f_u32;
        \\    let merged = Matrix { cells: [0.0_f32; 4], .. };
        \\    let moved_spread = Matrix { ..own merged };
        \\    let Matrix { var cells, &slice_opt, raw_ptr: renamed_ptr, .. } = moved_spread;
        \\    _ = (borrow_out, borrow_field, borrow_raw_elem, mod_buf, ui_children, escaping_cb);
        \\    _ = (header_byte, magic_bytes, inverted, cells, slice_opt, renamed_ptr);
        \\    let final_code = fsm: match MemoryOrder.Relaxed {
        \\        .Relaxed => continue :fsm .Acquire,
        \\        .Acquire => 42_i32,
        \\        _ => 0_i32,
        \\    };
        \\    .Ok(final_code)
        \\}
        \\
        \\test "matrix multi-index and async closure" {
        \\    let mat = Matrix { cells: [1.0_f32; 4], raw_ptr: .None, slice_opt: .None, borrowed_opt: .None };
        \\    let elem = &mat[0, 1];
        \\    let worker = own async |step: i32| step + 1;
        \\    _ = (elem, worker);
        \\}
        \\
        \\bench "matrix swap throughput" (bencher: &mut Bencher) {
        \\    _ = bencher;
        \\}
    ;

    _ = try parseSource(
        valid_dr22_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
    try std.testing.expect(!cst_arena.has_parse_errors);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        valid_dr22_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // Verify `[P0-B]` `unsafe { … }` CST origin carries `.kw_unsafe` token leaf:
    var has_unsafe_origin = false;
    var has_result_type = false;
    var has_subscript_decl = false;
    var has_yield_stmt = false;
    var has_test_decl = false;
    var has_bench_decl = false;
    var has_byte_lit = false;
    var has_byte_string_lit = false;
    for (0..ast_arena.countNodes()) |node_i| {
        const node_id = NodeIndex.fromInt(@intCast(node_i));
        const node = ast_arena.getNode(node_id);
        switch (node.tag) {
            .result_type => has_result_type = true,
            .subscript_decl => has_subscript_decl = true,
            .yield_stmt => has_yield_stmt = true,
            .test_decl => has_test_decl = true,
            .bench_decl => has_bench_decl = true,
            .byte_lit => has_byte_lit = true,
            .byte_string_lit => has_byte_string_lit = true,
            .block => {
                const origin_cst = ast_arena.getCstOrigin(node_id);
                if (!origin_cst.isNone()) {
                    const cst_rec = cst_arena.getNode(origin_cst);
                    if (!cst_rec.token.isNone() and
                        token_buf.getToken(cst_rec.token).kind == .kw_unsafe)
                    {
                        has_unsafe_origin = true;
                    }
                }
            },
            else => {},
        }
    }
    try std.testing.expect(has_unsafe_origin);
    try std.testing.expect(has_result_type);
    try std.testing.expect(has_subscript_decl);
    try std.testing.expect(has_yield_stmt);
    try std.testing.expect(has_test_decl);
    try std.testing.expect(has_bench_decl);
    try std.testing.expect(has_byte_lit);
    try std.testing.expect(has_byte_string_lit);

    // Verify `is_including_tests = false` omits `.test_decl` / `.bench_decl` from AST root while keeping CST lossless:
    cst_arena.nodes.shrinkRetainingCapacity(0);
    cst_arena.parse_stack.clearRetainingCapacity();
    cst_arena.has_parse_errors = false;
    ast_arena.nodes.shrinkRetainingCapacity(0);
    ast_arena.extra_data.clearRetainingCapacity();
    ast_arena.ast_to_cst.clearRetainingCapacity();
    var prod_parser = Parser.initWithOptions(
        valid_dr22_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
        .{ .is_including_tests = false },
    );
    const prod_root = try prod_parser.parse();
    const prod_root_node = ast_arena.getNode(prod_root);
    const prod_items = ast_arena.extra_data.items[prod_root_node.lhs.payload .. prod_root_node.lhs.payload + prod_root_node.rhs.payload];
    for (prod_items) |item_raw_id| {
        const tag_val = ast_arena.getNode(NodeIndex.fromInt(item_raw_id)).tag;
        try std.testing.expect(tag_val != .test_decl and tag_val != .bench_decl);
    }
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        valid_dr22_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    // [2] Verify all 10 `DR-22` retired-syntax diagnostics (`E0219`–`E0228`) + autofixes:
    const retired_src =
        \\@noalloc
        \\@cfg(os = "linux")
        \\struct LegacyStruct {
        \\    first: *const u8;
        \\    second: i32 ! u32 ! bool,
        \\}
        \\fn legacy_fn(mut self, /, *, a: inout i32, *) {
        \\    let mut flag = !true || false;
        \\    let val = *a;
        \\    _ = (flag, val);
        \\}
    ;
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(
        retired_src,
        FileId.fromInt(1),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        retired_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    var seen_codes: [10]bool = @splat(false);
    for (sink.asSlice()) |diag| {
        switch (diag.code) {
            .e0219_retired_logical_or => seen_codes[0] = true,
            .e0220_retired_bang_prefix => seen_codes[1] = true,
            .e0221_retired_mutability_or_param_mode => seen_codes[2] = true,
            .e0222_chained_result_type => seen_codes[3] = true,
            .e0223_retired_attribute_eq => seen_codes[4] = true,
            .e0224_retired_semicolon_member_sep => seen_codes[5] = true,
            .e0225_retired_noalloc_attribute => seen_codes[6] = true,
            .e0226_retired_const_raw_ptr => seen_codes[7] = true,
            .e0227_retired_prefix_deref => seen_codes[8] = true,
            .e0228_invalid_param_zone_separator => seen_codes[9] = true,
            else => {},
        }
    }
    for (seen_codes) |was_seen| {
        try std.testing.expect(was_seen);
    }

    // [3] Verify `[P1 Trap B]` `reparseIncremental` falls back on invalid `.byte_lit` (`E0117`) to preserve lexer diagnostics:
    const byte_src_ok = "fn check_byte() -> u8 { b'a' }\n";
    const byte_src_bad = "fn check_byte() -> u8 { b'\\u{100}' }\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(
        byte_src_ok,
        FileId.fromInt(2),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
    _ = try reparseIncremental(
        byte_src_bad,
        FileId.fromInt(2),
        .{ .start_byte = 26, .old_end_byte = 27, .new_end_byte = 33 },
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    var has_e0117 = false;
    for (sink.asSlice()) |diag| {
        if (diag.code == .e0117_non_ascii_byte_literal) has_e0117 = true;
    }
    try std.testing.expect(has_e0117);
}

test "test_parser_extern_blocks_extern_static_and_c_casing_exemption" {
    const extern_src =
        \\@cfg(target.os == "windows")
        \\pub extern "C" {
        \\    @link_name("CreateFileW")
        \\    pub fn CreateFileW(path: *u16, access: u32) -> *mut opaque;
        \\    pub(pkg) fn sqlite3_open_v2(filename: *u8, pp_db: *mut *mut opaque, flags: i32, vfs: *u8) -> i32;
        \\    fn EVP_DigestInit_ex(ctx: *mut opaque, md_type: *opaque, impl_ptr: *mut opaque) -> i32;
        \\    pub static mut _errno: i32;
        \\    static SQLITE_VERSION_NUMBER: i32;
        \\    pub const INVALID_HANDLE_VALUE: usize = 0xFFFF_FFFF_FFFF_FFFF;
        \\}
        \\
        \\extern {
        \\    fn free(ptr: *mut opaque);
        \\}
        \\
        \\@link_section(".bss")
        \\pub(super) extern "C" static mut __errno_location_cache: *mut i32;
        \\extern "C" fn WSAStartup(version_req: u16, data_out: *mut opaque) -> i32;
    ;

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
        extern_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);
    try std.testing.expect(!cst_arena.has_parse_errors);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        extern_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );

    const root_node = ast_arena.getNode(root_id);
    const top_items = ast_arena.getExtraSlice(ExtraIndex.fromInt(root_node.lhs.payload), root_node.rhs.payload);
    try std.testing.expectEqual(@as(usize, 4), top_items.len);

    // [1] First item: `@cfg(…) pub extern "C" { … }` with 6 members:
    const block1_id = NodeIndex.fromInt(top_items[0]);
    try std.testing.expectEqual(AstTag.extern_block_decl, ast_arena.getNode(block1_id).tag);
    try std.testing.expectEqual(CstNodeKind.extern_block_item, cst_arena.getNode(ast_arena.getCstOrigin(block1_id)).kind);
    const header1 = ast_arena.getExternBlockHeader(block1_id);
    try std.testing.expect(!header1.abi_tok.isNone());
    try std.testing.expectEqual(ExternVisibility.public, header1.flags.visibility);
    try std.testing.expectEqual(@as(u32, 1), header1.attr_len);
    const members1 = ast_arena.getExternBlockItems(block1_id);
    try std.testing.expectEqual(@as(usize, 6), members1.len);
    try std.testing.expectEqual(AstTag.fn_decl, ast_arena.getNode(NodeIndex.fromInt(members1[0])).tag);
    try std.testing.expectEqual(AstTag.fn_decl, ast_arena.getNode(NodeIndex.fromInt(members1[1])).tag);
    try std.testing.expectEqual(AstTag.fn_decl, ast_arena.getNode(NodeIndex.fromInt(members1[2])).tag);
    try std.testing.expectEqual(AstTag.extern_static_decl, ast_arena.getNode(NodeIndex.fromInt(members1[3])).tag);
    try std.testing.expectEqual(AstTag.extern_static_decl, ast_arena.getNode(NodeIndex.fromInt(members1[4])).tag);
    try std.testing.expectEqual(AstTag.const_decl, ast_arena.getNode(NodeIndex.fromInt(members1[5])).tag);

    const static_mut_info = ast_arena.getExternStaticExtra(NodeIndex.fromInt(members1[3]));
    try std.testing.expect(static_mut_info.flags.is_mut);
    try std.testing.expect(static_mut_info.flags.has_extern);
    try std.testing.expectEqual(ExternVisibility.public, static_mut_info.flags.visibility);

    // [2] Second item: bare `extern { fn free(…); }` with omitted ABI token (`TokenIndex.none`):
    const block2_id = NodeIndex.fromInt(top_items[1]);
    const header2 = ast_arena.getExternBlockHeader(block2_id);
    try std.testing.expect(header2.abi_tok.isNone());
    try std.testing.expectEqual(@as(usize, 1), ast_arena.getExternBlockItems(block2_id).len);

    // [3] Third item: standalone `pub(super) extern "C" static mut`:
    const standalone_static_id = NodeIndex.fromInt(top_items[2]);
    try std.testing.expectEqual(AstTag.extern_static_decl, ast_arena.getNode(standalone_static_id).tag);
    const standalone_info = ast_arena.getExternStaticExtra(standalone_static_id);
    try std.testing.expectEqual(ExternVisibility.pub_super, standalone_info.flags.visibility);
    try std.testing.expect(standalone_info.flags.is_mut);
    try std.testing.expectEqual(@as(u32, 1), standalone_info.attr_len);

    // [4] Error recovery inside `extern "C" { … }` produces `item_hole` and parses subsequent members:
    const bad_extern_src =
        \\extern "C" {
        \\    let invalid_local = 1;
        \\    fn valid_after_hole(code: i32) -> i32;
        \\}
    ;
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    const bad_root = try parseSource(
        bad_extern_src,
        FileId.fromInt(1),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expect(sink.error_count >= 1);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        bad_extern_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
    const bad_top = ast_arena.getExtraSlice(
        ExtraIndex.fromInt(ast_arena.getNode(bad_root).lhs.payload),
        ast_arena.getNode(bad_root).rhs.payload,
    );
    const bad_members = ast_arena.getExternBlockItems(NodeIndex.fromInt(bad_top[0]));
    try std.testing.expectEqual(@as(usize, 2), bad_members.len);
    try std.testing.expectEqual(AstTag.item_hole, ast_arena.getNode(NodeIndex.fromInt(bad_members[0])).tag);
    try std.testing.expectEqual(AstTag.fn_decl, ast_arena.getNode(NodeIndex.fromInt(bad_members[1])).tag);
}

test "test_parser_kw_async_module_path_segments_zero_diagnostics" {
    const async_mod_src =
        \\pub mod async;
        \\mod wrapper {
        \\    pub mod async {
        \\        pub struct TaskHeader {
        \\            pub state: u32,
        \\        }
        \\    }
        \\}
        \\use cx.async;
        \\use cx.async.*;
        \\use cx.async.{TaskGroup, TaskHandle, sleep};
        \\use core.async.TaskHeader;
        \\
        \\pub async fn run_tasks(
        \\    grp: &mut cx.async.TaskGroup[IoError],
        \\    local_grp: &async.TaskGroup[IoError],
        \\    hdr: core.async.TaskHeader,
        \\) -> unit ! IoError {
        \\    async.yield_now().await;
        \\    let fut = async {
        \\        cx.async.sleep(10).await
        \\    };
        \\    let _ = fut.await;
        \\    cx.async.task_group[IoError](async |sub_group| {
        \\        match cx.async.Poll.Ready(hdr.state) {
        \\            cx.async.Poll.Ready(val) => val,
        \\            async.Poll.Pending => 0,
        \\        }
        \\    }).await
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
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    _ = try parseSource(
        async_mod_src,
        FileId.fromInt(0),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(usize, 0), sink.countDiagnostics());
    try std.testing.expect(!cst_arena.has_parse_errors);
    try verifyCstAndAstInvariants(
        std.testing.allocator,
        async_mod_src,
        &token_buf,
        &cst_arena,
        &ast_arena,
    );
}

test "test_parser_depth_caps_precede_extern_attrs_and_incremental_w0201_parity" {
    const allocator = std.testing.allocator;
    var token_buf = TokenBuffer.init(allocator);
    defer token_buf.deinit();
    var cst_arena = LosslessCstArena.init(allocator);
    defer cst_arena.deinit();
    var ast_arena = AstArena.init(allocator);
    defer ast_arena.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    // [1] Deep `@` subpatterns, `~` / `#soa` types, `dyn` / `any`, and retired `ref` cap at `E0203`:
    const deep_cases = [_][]const u8{
        "fn deep_at(val: i32) { match val { a @ b @ c @ d @ e @ f @ g @ h @ _ => {} } }\n",
        "fn deep_tilde(val: ~ ~ ~ ~ ~ ~ ~ ~ ~ i32) {}\n",
        "fn deep_soa(val: #soa #soa #soa #soa #soa #soa #soa #soa i32) {}\n",
        "fn deep_dyn(val: dyn any dyn any dyn any dyn any TraitName) {}\n",
        "fn deep_ref(val: ref ref ref ref ref ref ref ref i32) {}\n",
    };
    for (deep_cases, 0..) |case_src, idx| {
        token_buf.tokens.shrinkRetainingCapacity(0);
        token_buf.trivia.clearRetainingCapacity();
        cst_arena.nodes.shrinkRetainingCapacity(0);
        cst_arena.parse_stack.clearRetainingCapacity();
        cst_arena.has_parse_errors = false;
        ast_arena.nodes.shrinkRetainingCapacity(0);
        ast_arena.extra_data.clearRetainingCapacity();
        ast_arena.ast_to_cst.clearRetainingCapacity();
        sink.diagnostics.clearRetainingCapacity();
        sink.error_count = 0;
        sink.warning_count = 0;

        try lexer.tokenize(case_src, FileId.fromInt(@intCast(idx)), &token_buf, &sink, &interner);
        var capped = Parser.initWithOptions(
            case_src,
            FileId.fromInt(@intCast(idx)),
            &token_buf,
            &cst_arena,
            &ast_arena,
            &sink,
            &interner,
            .{ .max_depth = 6 },
        );
        _ = try capped.parse();
        var has_e0203 = false;
        for (sink.asSlice()) |diag_item| {
            if (diag_item.code == .e0203_parse_depth_exceeded) has_e0203 = true;
        }
        try std.testing.expect(has_e0203);
        try verifyCstAndAstInvariants(allocator, case_src, &token_buf, &cst_arena, &ast_arena);
    }

    // [2] `precedeNode` shifts `attr_start` on `.extern_block_decl` and `.extern_static_decl`:
    const precede_extern_src =
        "fn check_expr() -> i32 {\n" ++
        "    return {\n" ++
        "        @link_name(\"cos\") extern \"C\" { fn c_cos(val: f64) -> f64; }\n" ++
        "        @link_name(\"errno\") extern \"C\" static mut c_errno: i32;\n" ++
        "        1\n" ++
        "    } + 2;\n" ++
        "}\n";
    sink.diagnostics.clearRetainingCapacity();
    sink.error_count = 0;
    sink.warning_count = 0;
    _ = try parseSource(
        precede_extern_src,
        FileId.fromInt(10),
        &token_buf,
        &cst_arena,
        &ast_arena,
        &sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try verifyCstAndAstInvariants(allocator, precede_extern_src, &token_buf, &cst_arena, &ast_arena);

    var has_checked_block_attr = false;
    var has_checked_static_attr = false;
    var node_i: usize = 0;
    while (node_i < ast_arena.countNodes()) : (node_i += 1) {
        const nid = NodeIndex.fromInt(@intCast(node_i));
        const tag = ast_arena.getNode(nid).tag;
        if (tag == .extern_block_decl) {
            const hdr = ast_arena.getExternBlockHeader(nid);
            try std.testing.expectEqual(@as(u32, 1), hdr.attr_len);
            try std.testing.expectEqual(
                CstNodeKind.attribute,
                cst_arena.getNode(CstNodeIndex.fromInt(hdr.attr_start)).kind,
            );
            has_checked_block_attr = true;
        } else if (tag == .extern_static_decl) {
            const ext_info = ast_arena.getExternStaticExtra(nid);
            try std.testing.expectEqual(@as(u32, 1), ext_info.attr_len);
            try std.testing.expectEqual(
                CstNodeKind.attribute,
                cst_arena.getNode(CstNodeIndex.fromInt(ext_info.attr_start)).kind,
            );
            has_checked_static_attr = true;
        }
    }
    try std.testing.expect(has_checked_block_attr and has_checked_static_attr);

    // [3] `reparseIncremental` preserves `W0201` warnings in untouched items identically to `parseSource`:
    const old_w0201_src =
        "struct Bad_Struct {}\n\n" ++
        "const BAD_const: i32 = 1;\n\n" ++
        "pub fn middle_target(val: i32) -> i32 {\n    return val + 1;\n}\n\n" ++
        "pub fn suffix_holder() -> i32 {\n    let bad_Camel = 1;\n    return bad_Camel;\n}\n";
    const new_w0201_src =
        "struct Bad_Struct {}\n\n" ++
        "const BAD_const: i32 = 1;\n\n" ++
        "pub fn middle_target(val: i32) -> i32 {\n    return val + 999;\n}\n\n" ++
        "pub fn suffix_holder() -> i32 {\n    let bad_Camel = 1;\n    return bad_Camel;\n}\n";

    const edit_off: u32 = @intCast(std.mem.indexOf(u8, old_w0201_src, "val + 1").?);
    var inc_tokens = TokenBuffer.init(allocator);
    defer inc_tokens.deinit();
    var inc_cst = LosslessCstArena.init(allocator);
    defer inc_cst.deinit();
    var inc_ast = AstArena.init(allocator);
    defer inc_ast.deinit();
    var init_sink = DiagnosticSink.init(allocator);
    defer init_sink.deinit();

    _ = try parseSource(old_w0201_src, FileId.fromInt(20), &inc_tokens, &inc_cst, &inc_ast, &init_sink, &interner);

    var inc_sink = DiagnosticSink.init(allocator);
    defer inc_sink.deinit();
    const inc_stats = try reparseIncremental(
        new_w0201_src,
        FileId.fromInt(20),
        .{ .start_byte = edit_off, .old_end_byte = edit_off + 7, .new_end_byte = edit_off + 9 },
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        &inc_sink,
        &interner,
    );
    try std.testing.expect(inc_stats.is_fast_splice);

    var scratch_tokens = TokenBuffer.init(allocator);
    defer scratch_tokens.deinit();
    var scratch_cst = LosslessCstArena.init(allocator);
    defer scratch_cst.deinit();
    var scratch_ast = AstArena.init(allocator);
    defer scratch_ast.deinit();
    var scratch_sink = DiagnosticSink.init(allocator);
    defer scratch_sink.deinit();
    _ = try parseSource(
        new_w0201_src,
        FileId.fromInt(20),
        &scratch_tokens,
        &scratch_cst,
        &scratch_ast,
        &scratch_sink,
        &interner,
    );

    try std.testing.expectEqual(scratch_sink.warning_count, inc_sink.warning_count);
    try std.testing.expectEqual(@as(u32, 4), inc_sink.warning_count);
    for (scratch_sink.asSlice(), inc_sink.asSlice()) |expected_d, actual_d| {
        try std.testing.expectEqual(expected_d.code, actual_d.code);
        try std.testing.expectEqual(expected_d.primary_span, actual_d.primary_span);
        try std.testing.expectEqualStrings(expected_d.labels[0].label, actual_d.labels[0].label);
        try std.testing.expectEqual(
            expected_d.suggestions[0].edits[0].replacement_id,
            actual_d.suggestions[0].edits[0].replacement_id,
        );
    }
}

test "test_parser_allow_non_canonical_case_and_c_scalar_aliases_suppress_w0201" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    const old_ffi_src =
        "pub type c_char = i8;\n" ++
        "pub type c_ulonglong = u64;\n" ++
        "pub type c_void = opaque;\n\n" ++
        "@allow(non_canonical_case)\n" ++
        "@repr(C)\n" ++
        "pub struct sqlite3_stmt {\n" ++
        "    pub pVm: i32,\n" ++
        "}\n\n" ++
        "pub struct SqliteRow {\n" ++
        "    @allow(non_canonical_case)\n" ++
        "    pub nCol: c_char,\n" ++
        "}\n\n" ++
        "impl sqlite3_stmt {\n" ++
        "    @allow(non_canonical_case)\n" ++
        "    pub fn isReady(&self) -> bool {\n" ++
        "        return self.pVm == 1;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn probe_ffi(stmt: *sqlite3_stmt, row: &SqliteRow) -> i32 {\n" ++
        "    if stmt != @default_init[*sqlite3_stmt]() {\n" ++
        "        return (row.nCol as i32) + 1;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    const new_ffi_src =
        "pub type c_char = i8;\n" ++
        "pub type c_ulonglong = u64;\n" ++
        "pub type c_void = opaque;\n\n" ++
        "@allow(non_canonical_case)\n" ++
        "@repr(C)\n" ++
        "pub struct sqlite3_stmt {\n" ++
        "    pub pVm: i32,\n" ++
        "}\n\n" ++
        "pub struct SqliteRow {\n" ++
        "    @allow(non_canonical_case)\n" ++
        "    pub nCol: c_char,\n" ++
        "}\n\n" ++
        "impl sqlite3_stmt {\n" ++
        "    @allow(non_canonical_case)\n" ++
        "    pub fn isReady(&self) -> bool {\n" ++
        "        return self.pVm == 1;\n" ++
        "    }\n" ++
        "}\n\n" ++
        "pub fn probe_ffi(stmt: *sqlite3_stmt, row: &SqliteRow) -> i32 {\n" ++
        "    if stmt != @default_init[*sqlite3_stmt]() {\n" ++
        "        return (row.nCol as i32) + 42;\n" ++
        "    }\n" ++
        "    return 0;\n" ++
        "}\n";

    // [1] Full scratch `parseSource` emits `0` errors and `0` `W0201` warnings:
    var inc_tokens = TokenBuffer.init(allocator);
    defer inc_tokens.deinit();
    var inc_cst = LosslessCstArena.init(allocator);
    defer inc_cst.deinit();
    var inc_ast = AstArena.init(allocator);
    defer inc_ast.deinit();
    var scratch_sink = DiagnosticSink.init(allocator);
    defer scratch_sink.deinit();

    _ = try parseSource(
        old_ffi_src,
        FileId.fromInt(42),
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        &scratch_sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 0), scratch_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), scratch_sink.warning_count);
    try std.testing.expectEqual(@as(usize, 0), scratch_sink.countDiagnostics());
    try verifyCstAndAstInvariants(allocator, old_ffi_src, &inc_tokens, &inc_cst, &inc_ast);

    // [2] Incremental `reparseIncremental` fast-splices with `0` `W0201` warnings (matching scratch parse):
    const edit_off: u32 = @intCast(std.mem.indexOf(u8, old_ffi_src, "+ 1;").?);
    var inc_sink = DiagnosticSink.init(allocator);
    defer inc_sink.deinit();
    const inc_stats = try reparseIncremental(
        new_ffi_src,
        FileId.fromInt(42),
        .{ .start_byte = edit_off, .old_end_byte = edit_off + 4, .new_end_byte = edit_off + 5 },
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        &inc_sink,
        &interner,
    );
    try std.testing.expect(inc_stats.is_fast_splice);
    try std.testing.expect(inc_stats.reused_prefix_items >= 5);
    try std.testing.expectEqual(@as(u32, 0), inc_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), inc_sink.warning_count);
    try std.testing.expectEqual(@as(usize, 0), inc_sink.countDiagnostics());
    try verifyCstAndAstInvariants(allocator, new_ffi_src, &inc_tokens, &inc_cst, &inc_ast);

    // [3] Verify `core/ffi.cx` parses from disk with `0` errors and `0` `W0201` warnings:
    const raw_core_ffi = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        "core/ffi.cx",
        allocator,
        .limited(256 * 1024),
    );
    defer allocator.free(raw_core_ffi);
    var lf_core_ffi: std.ArrayListUnmanaged(u8) = .empty;
    defer lf_core_ffi.deinit(allocator);
    for (raw_core_ffi) |byte_val| {
        if (byte_val != '\r') try lf_core_ffi.append(allocator, byte_val);
    }

    var core_ffi_sink = DiagnosticSink.init(allocator);
    defer core_ffi_sink.deinit();
    _ = try parseSource(
        lf_core_ffi.items,
        FileId.fromInt(43),
        &inc_tokens,
        &inc_cst,
        &inc_ast,
        &core_ffi_sink,
        &interner,
    );
    try std.testing.expectEqual(@as(u32, 0), core_ffi_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), core_ffi_sink.warning_count);
    try verifyCstAndAstInvariants(allocator, lf_core_ffi.items, &inc_tokens, &inc_cst, &inc_ast);
}

test "test_parser_inline_string_use_decl_and_diagnostics" {
    const allocator = std.testing.allocator;
    var interner = try StringInterner.init(allocator);
    defer interner.deinit();

    const valid_src =
        "use \"corex-http@^2.1.0\" as http;\n" ++
        "pub use \"https://github.com/org/repo.git#v1.2.0\" as repo_client;\n" ++
        "use \"./vendor/local-codec\" as local_codec;\n";

    var tokens = TokenBuffer.init(allocator);
    defer tokens.deinit();
    var cst = LosslessCstArena.init(allocator);
    defer cst.deinit();
    var ast = AstArena.init(allocator);
    defer ast.deinit();
    var sink = DiagnosticSink.init(allocator);
    defer sink.deinit();

    _ = try parseSource(valid_src, FileId.fromInt(90), &tokens, &cst, &ast, &sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);
    try verifyCstAndAstInvariants(allocator, valid_src, &tokens, &cst, &ast);

    const specs = try extractInlineStringUseSpecs(allocator, valid_src, FileId.fromInt(90), &tokens, &cst);
    defer allocator.free(specs);
    try std.testing.expectEqual(@as(usize, 3), specs.len);
    try std.testing.expectEqualStrings("corex-http@^2.1.0", specs[0].unquoted_spec);
    try std.testing.expectEqualStrings("http", specs[0].alias_slice);
    try std.testing.expect(!specs[0].is_pub);
    try std.testing.expect(specs[1].is_pub);
    try std.testing.expectEqualStrings("repo_client", specs[1].alias_slice);

    const bad_src =
        "use \"corex-http@\" as http;\n" ++
        "use \"corex-http@^2.0\" as pkg;\n" ++
        "use \"corex-http@^2.0\" as Http;\n";
    var bad_sink = DiagnosticSink.init(allocator);
    defer bad_sink.deinit();
    _ = try parseSource(bad_src, FileId.fromInt(91), &tokens, &cst, &ast, &bad_sink, &interner);
    try std.testing.expectEqual(@as(u32, 2), bad_sink.error_count);
    try std.testing.expectEqual(@as(u32, 1), bad_sink.warning_count);

    try std.testing.expect(isValidInlineUseSpec("github.com/corex-labs/http-router@v1.2.0"));
    try std.testing.expect(isValidInlineUseSpec("gitlab.com/corex-labs/http-router"));
    try std.testing.expect(isValidInlineUseSpec("registry:serde-json@1.4.2"));
    try std.testing.expect(isValidInlineUseSpec("../shared/local-codec"));
    try std.testing.expect(!isValidInlineUseSpec("serde_json@1.4.2"));
    try std.testing.expect(!isValidInlineUseSpec("serde-json"));
    try std.testing.expect(!isValidInlineUseSpec("registry:serde-json"));
    try std.testing.expect(!isValidInlineUseSpec("serde--json@1.0.0"));
    try std.testing.expect(!isValidInlineUseSpec("Serde@1.0.0"));
}

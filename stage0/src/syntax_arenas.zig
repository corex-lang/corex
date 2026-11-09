//! Lossless Concrete Syntax Tree, Token Buffer & Abstract Syntax Tree Arenas
//!
//! Defines the 112-variant CoreX `TokenKind` taxonomy, 12-byte SoA `TokenRecord` and 8-byte `TriviaPiece`
//! tables (`TokenBuffer`), 10-byte SoA `CstNodeRecord` arena with bounded non-recursive `ParseState` stack
//! (`LosslessCstArena`), and 13-byte SoA `AstNode` store with `extra_data` trail (`AstArena` / `AstStore`).
//!
//! All multi-field syntax records omit artificial padding fields so `std.MultiArrayList` decomposes them
//! into dense, zero-padding Structure-of-Arrays (SoA) columns with $O(1)$ index access and subtree skipping.

const std = @import("std");
const mem = @import("mem_foundation.zig");

const FileId = mem.FileId;
const TokenIndex = mem.TokenIndex;
const TokenId = mem.TokenId;
const CstNodeIndex = mem.CstNodeIndex;
const CstNodeId = mem.CstNodeId;
const NodeIndex = mem.NodeIndex;
const AstNodeId = mem.AstNodeId;
const ExtraIndex = mem.ExtraIndex;
const PackedOperand = mem.PackedOperand;
const Span = mem.Span;

// ---------------------------------------- TYPES ----------------------------------------

// -------------------- Token & Trivia Types --------------------

/// Authoritative 112-variant lexical token kind table (`0..111`, `DR-03` Section 5.2 & `DR-12` Section 1.4).
pub const TokenKind = enum(u8) {
    /// Keyword `pub` (`0`).
    kw_pub = 0,
    /// Keyword `mod` (`1`).
    kw_mod = 1,
    /// Keyword `use` (`2`).
    kw_use = 2,
    /// Keyword `as` (`3`).
    kw_as = 3,
    /// Keyword `fn` (`4`).
    kw_fn = 4,
    /// Keyword `struct` (`5`).
    kw_struct = 5,
    /// Keyword `enum` (`6`).
    kw_enum = 6,
    /// Keyword `union` (`7`).
    kw_union = 7,
    /// Keyword `trait` (`8`).
    kw_trait = 8,
    /// Keyword `impl` (`9`).
    kw_impl = 9,
    /// Keyword `type` (`10`).
    kw_type = 10,
    /// Keyword `const` (`11`).
    kw_const = 11,
    /// Keyword `let` (`12`).
    kw_let = 12,
    /// Keyword `var` (`13`).
    kw_var = 13,
    /// Keyword `bit_field` (`14`).
    kw_bit_field = 14,
    /// Keyword `comptime` (`15`).
    kw_comptime = 15,
    /// Keyword `mut` (`16`).
    kw_mut = 16,
    /// Keyword `own` (`17`).
    kw_own = 17,
    /// Keyword `ref` (`18`).
    kw_ref = 18,
    /// Keyword `where` (`19`).
    kw_where = 19,
    /// Keyword `extern` (`20`).
    kw_extern = 20,
    /// Keyword `async` (`21`).
    kw_async = 21,
    /// Keyword `await` (`22`).
    kw_await = 22,
    /// Keyword `unsafe` (`23`).
    kw_unsafe = 23,
    /// Keyword `defer` (`24`).
    kw_defer = 24,
    /// Keyword `errdefer` (`25`).
    kw_errdefer = 25,
    /// Keyword `is` (`26`).
    kw_is = 26,
    /// Keyword `if` (`27`).
    kw_if = 27,
    /// Keyword `else` (`28`).
    kw_else = 28,
    /// Keyword `match` (`29`).
    kw_match = 29,
    /// Keyword `for` (`30`).
    kw_for = 30,
    /// Keyword `in` (`31`).
    kw_in = 31,
    /// Keyword `while` (`32`).
    kw_while = 32,
    /// Keyword `loop` (`33`).
    kw_loop = 33,
    /// Keyword `return` (`34`).
    kw_return = 34,
    /// Keyword `break` (`35`).
    kw_break = 35,
    /// Keyword `continue` (`36`).
    kw_continue = 36,
    /// Keyword `catch` (`37`).
    kw_catch = 37,
    /// Boolean literal keyword `true` (`38`).
    kw_true = 38,
    /// Boolean literal keyword `false` (`39`).
    kw_false = 39,
    /// Logical operator keyword `and` (`40`).
    kw_and = 40,
    /// Logical operator keyword `or` (`41`).
    kw_or = 41,
    /// Logical operator keyword `not` (`42`).
    kw_not = 42,
    /// Value receiver keyword `self` (`43`).
    kw_self_val = 43,
    /// Type receiver keyword `Self` (`44`).
    kw_self_type = 44,
    /// Built-in primitive type keyword (`i8`..`f64`, `bool`, `char`, `str`, `never`, `unit`) (`45`).
    prim_type = 45,
    /// Lowercase `snake_case` value/function/module identifier (`46`).
    ident = 46,
    /// `PascalCase` type, trait, or enum variant identifier (`47`).
    type_ident = 47,
    /// `SCREAMING_SNAKE_CASE` compile-time constant identifier (`48`).
    const_ident = 48,
    /// Integer literal token (`49`).
    int_lit = 49,
    /// Floating-point literal token (`50`).
    float_lit = 50,
    /// UTF-8 string literal token (`51`).
    string_lit = 51,
    /// Unicode scalar character literal token (`52`).
    char_lit = 52,
    /// Left curly brace `{` (`53`).
    lbrace = 53,
    /// Right curly brace `}` (`54`).
    rbrace = 54,
    /// Left parenthesis `(` (`55`).
    lparen = 55,
    /// Right parenthesis `)` (`56`).
    rparen = 56,
    /// Left square bracket `[` (`57`).
    lbracket = 57,
    /// Right square bracket `]` (`58`).
    rbracket = 58,
    /// Semicolon `;` (`59`).
    semi = 59,
    /// Comma `,` (`60`).
    comma = 60,
    /// Colon `:` (`61`).
    colon = 61,
    /// Path separator `::` (`62`).
    coloncolon = 62,
    /// Member access period `.` (`63`).
    dot = 63,
    /// Exclusive range operator `..` (`64`).
    dotdot = 64,
    /// Inclusive range operator `..=` (`65`).
    dotdoteq = 65,
    /// Thin return arrow `->` (`66`).
    arrow = 66,
    /// Match arm fat arrow `=>` (`67`).
    fat_arrow = 67,
    /// Pipeline operator `|>` (`68`).
    pipe_gt = 68,
    /// Attribute introducer `@` (`69`).
    at = 69,
    /// Structure-of-Arrays directive `#soa` (`70`).
    hash_soa = 70,
    /// Error propagation / optional suffix `?` (`71`).
    question = 71,
    /// Wildcard underscore `_` (`72`).
    underscore = 72,
    /// Addition operator `+` (`73`).
    plus = 73,
    /// Subtraction / negation operator `-` (`74`).
    minus = 74,
    /// Multiplication / dereference operator `*` (`75`).
    star = 75,
    /// Division operator `/` (`76`).
    slash = 76,
    /// Remainder operator `%` (`77`).
    percent = 77,
    /// Wrapping addition operator `+%` (`78`).
    plus_percent = 78,
    /// Wrapping subtraction operator `-%` (`79`).
    minus_percent = 79,
    /// Wrapping multiplication operator `*%` (`80`).
    star_percent = 80,
    /// Saturating addition operator `+|` (`81`).
    plus_pipe = 81,
    /// Saturating subtraction operator `-|` (`82`).
    minus_pipe = 82,
    /// Saturating multiplication operator `*| (`83`).
    star_pipe = 83,
    /// Equality comparison operator `==` (`84`).
    eqeq = 84,
    /// Inequality comparison operator `!=` (`85`).
    bang_eq = 85,
    /// Less-than operator `<` (`86`).
    lt = 86,
    /// Less-than-or-equal operator `<=` (`87`).
    le = 87,
    /// Greater-than operator `>` (`88`).
    gt = 88,
    /// Greater-than-or-equal operator `>=` (`89`).
    ge = 89,
    /// Bitwise AND / borrow operator `&` (`90`).
    amp = 90,
    /// Logical short-circuit AND operator `&&` (`91`).
    ampamp = 91,
    /// Bitwise OR / closure delimiter `|` (`92`).
    pipe = 92,
    /// Logical short-circuit OR operator `||` (`93`).
    pipepipe = 93,
    /// Bitwise XOR operator `^` (`94`).
    caret = 94,
    /// Logical NOT / error union operator `!` (`95`).
    bang = 95,
    /// Bitwise NOT operator `~` (`96`).
    tilde = 96,
    /// Bitwise shift-left operator `<<` (`97`).
    shl = 97,
    /// Bitwise shift-right operator `>>` (`98`).
    shr = 98,
    /// Assignment operator `=` (`99`).
    eq = 99,
    /// Addition-assignment operator `+=` (`100`).
    plus_eq = 100,
    /// Subtraction-assignment operator `-=` (`101`).
    minus_eq = 101,
    /// Multiplication-assignment operator `*=` (`102`).
    star_eq = 102,
    /// Division-assignment operator `/=` (`103`).
    slash_eq = 103,
    /// Remainder-assignment operator `%=` (`104`).
    percent_eq = 104,
    /// Bitwise AND-assignment operator `&=` (`105`).
    amp_eq = 105,
    /// Bitwise OR-assignment operator `|=` (`106`).
    pipe_eq = 106,
    /// Bitwise XOR-assignment operator `^=` (`107`).
    caret_eq = 107,
    /// Shift-left-assignment operator `<<=` (`108`).
    shl_eq = 108,
    /// Shift-right-assignment operator `>>=` (`109`).
    shr_eq = 109,
    /// Lexer error recovery token (`110`).
    invalid_token = 110,
    /// End-of-file sentinel token (`111`).
    eof = 111,

    /// Alias for `.lbrace`.
    pub const l_brace: TokenKind = .lbrace;
    /// Alias for `.rbrace`.
    pub const r_brace: TokenKind = .rbrace;
    /// Alias for `.lparen`.
    pub const l_paren: TokenKind = .lparen;
    /// Alias for `.rparen`.
    pub const r_paren: TokenKind = .rparen;
    /// Alias for `.lbracket`.
    pub const l_bracket: TokenKind = .lbracket;
    /// Alias for `.rbracket`.
    pub const r_bracket: TokenKind = .rbracket;
    /// Alias for `.coloncolon`.
    pub const colon_colon: TokenKind = .coloncolon;
    /// Alias for `.dotdot`.
    pub const dot_dot: TokenKind = .dotdot;
    /// Alias for `.dotdoteq`.
    pub const dot_dot_eq: TokenKind = .dotdoteq;
    /// Alias for `.eqeq`.
    pub const eq_eq: TokenKind = .eqeq;
    /// Alias for `.le`.
    pub const lt_eq: TokenKind = .le;
    /// Alias for `.ge`.
    pub const gt_eq: TokenKind = .ge;
    /// Alias for `.ampamp`.
    pub const amp_amp: TokenKind = .ampamp;
    /// Alias for `.pipepipe`.
    pub const pipe_pipe: TokenKind = .pipepipe;
    /// Alias for `.invalid_token`.
    pub const invalid: TokenKind = .invalid_token;
};

/// 1-byte bit-packed flags attached to each `TokenRecord` for $O(1)$ trivia and recovery checks.
pub const TokenFlags = packed struct(u8) {
    /// `true` if at least one newline (`\n` or `\r\n`) precedes this token.
    has_leading_newline: bool = false,
    /// `true` if one or more leading `TriviaPiece` entries are attached to this token.
    has_leading_trivia_pieces: bool = false,
    /// `true` if one or more trailing `TriviaPiece` entries are attached to this token.
    has_trailing_trivia: bool = false,
    /// `true` if the lexer or parser synthesized this token during recovery (`byte_len == 0`).
    is_synthesized: bool = false,
    /// `true` if this token originated from macro or compile-time expansion.
    is_macro_expanded: bool = false,
    /// `true` if this token spans an unclosed literal or malformed byte sequence.
    has_lexer_error: bool = false,
    /// Reserved padding bits (`0`).
    reserved: u2 = 0,
};

/// 4-byte bit-packed handle indexing a token's leading and trailing `TriviaPiece` slices.
pub const PackedTriviaSpan = packed struct(u32) {
    /// Starting index into `TokenBuffer.trivia` (`0..16,777,215`).
    start_index: u24 = 0,
    /// Number of leading `TriviaPiece` items starting at `start_index` (`0..15`).
    leading_count: u4 = 0,
    /// Number of trailing `TriviaPiece` items starting at `start_index + leading_count` (`0..15`).
    trailing_count: u4 = 0,
};

/// Classification of whitespace, comment, and skipped-byte trivia spans.
pub const TriviaKind = enum(u8) {
    /// Contiguous ASCII space (`0x20`) characters.
    spaces = 0,
    /// Contiguous horizontal tab (`\t`) characters.
    tabs = 1,
    /// POSIX line feed (`\n`).
    newline_lf = 2,
    /// Windows carriage-return line-feed (`\r\n`).
    newline_crlf = 3,
    /// Regular single-line comment (`// …`).
    line_comment = 4,
    /// Outer item documentation comment (`/// …`).
    doc_comment = 5,
    /// Enclosing module documentation comment (`//! …`).
    module_doc_comment = 6,
    /// Nestable block comment (`/* … */`).
    block_comment = 7,
    /// Executable script interpreter shebang (`#!…`).
    shebang = 8,
    /// Malformed or unexpected source bytes preserved losslessly during recovery.
    skipped_unexpected = 9,

    /// Alias for `.doc_comment`.
    pub const doc_line_comment: TriviaKind = .doc_comment;
    /// Alias for `.module_doc_comment`.
    pub const mod_doc_comment: TriviaKind = .module_doc_comment;
    /// Alias for `.skipped_unexpected`.
    pub const malformed_bytes: TriviaKind = .skipped_unexpected;
};

/// Exact 8-byte trivia record (`extern struct`) referencing whitespace or comment bytes in source.
pub const TriviaPiece = extern struct {
    /// Syntactic kind of trivia piece.
    kind: TriviaKind,
    /// Optional bit-flags or column indentation metadata (`0` by default).
    flags: u8 = 0,
    /// Byte length of the trivia span in the source buffer.
    byte_len: u16,
    /// Starting byte offset of the trivia span in the source buffer.
    byte_offset: u32,
};

/// Exact 12-byte token record (`extern struct`, zero padding) decomposed into SoA arrays by `TokenBuffer`.
pub const TokenRecord = extern struct {
    /// Lexical classification of the token (`1` byte).
    kind: TokenKind,
    /// Bit-packed whitespace, synthesis, and error flags (`1` byte).
    flags: TokenFlags = .{},
    /// Byte length of the token lexeme in the source buffer (`0` for synthesized tokens).
    byte_len: u16,
    /// Starting byte offset of the token lexeme in the source buffer.
    byte_offset: u32,
    /// Packed reference to leading and trailing `TriviaPiece` slices (`4` bytes).
    trivia_span: PackedTriviaSpan = .{},
};

// ---------------- CST Node & Parse State Types ----------------

/// Concrete Syntax Tree (CST) node kind covering all CoreX surface grammar and recovery constructs.
pub const CstNodeKind = enum(u8) {
    /// Start bracket of a source file (`DR-12` Section 1.4).
    file_start = 0,
    /// End bracket of a source file (`source_file` root).
    file_end,
    /// Start of an `@attribute` annotation.
    attribute_start,
    /// Complete `@attribute` annotation node.
    attribute,
    /// Visibility modifier (`pub`).
    visibility_modifier,
    /// Module declaration introducer (`mod`).
    mod_introducer,
    /// Complete `mod` declaration item.
    mod_item,
    /// Import declaration introducer (`use`).
    use_introducer,
    /// Import path tree inside `use`.
    use_tree,
    /// Complete `use` declaration item.
    use_item,
    /// Constant declaration introducer (`const`).
    const_introducer,
    /// Complete `const` declaration item.
    const_item,
    /// Type alias introducer (`type`).
    type_alias_introducer,
    /// Complete `type` alias item.
    type_alias_item,
    /// Struct declaration introducer (`struct`).
    struct_introducer,
    /// Single field declaration inside a `struct` or `union`.
    struct_field,
    /// Complete `struct` declaration item.
    struct_item,
    /// Enum declaration introducer (`enum`).
    enum_introducer,
    /// Single variant declaration inside an `enum`.
    enum_variant,
    /// Complete `enum` declaration item.
    enum_item,
    /// Union declaration introducer (`union`).
    union_introducer,
    /// Complete `union` declaration item.
    union_item,
    /// Trait declaration introducer (`trait`).
    trait_introducer,
    /// Member declaration inside a `trait`.
    trait_member,
    /// Complete `trait` declaration item.
    trait_item,
    /// Implementation block introducer (`impl`).
    impl_introducer,
    /// Member declaration inside an `impl` block.
    impl_member,
    /// Complete `impl` declaration item.
    impl_item,
    /// Function declaration introducer (`fn`).
    fn_introducer,
    /// Opening delimiter of a parameter list.
    param_list_start,
    /// Single function parameter node.
    fn_param,
    /// Complete function parameter list.
    param_list,
    /// Function return type annotation (`-> Type`).
    return_type,
    /// Complete function signature header.
    fn_sig,
    /// Complete `fn` declaration item.
    fn_item,
    /// Opening bracket of generic type parameters.
    type_params_start,
    /// Single generic type parameter.
    type_param,
    /// Complete generic type parameter list.
    type_params,
    /// Introducer of a `where` constraint clause.
    where_clause_start,
    /// Single predicate inside a `where` clause.
    where_pred,
    /// Complete `where` constraint clause.
    where_clause,
    /// Opening bracket of generic type arguments.
    type_args_start,
    /// Complete generic type argument list.
    type_args,
    /// Primitive type reference (`i32`, `u64`, `bool`, etc.).
    prim_type_node,
    /// Named user-defined or path type reference.
    named_type,
    /// Borrowed reference type (`&T` or `&mut T`).
    ref_type,
    /// Raw pointer type (`*T` or `*mut T`).
    ptr_type,
    /// Ownership/region mode-qualified type (`own T`, `ref T`).
    mode_type,
    /// Fixed-size array `[T; N]` or slice `[T]` type.
    slice_or_array_type,
    /// Tuple type `(T1, T2)`.
    tuple_type,
    /// Function pointer/closure type `fn(T) -> U`.
    fn_type,
    /// Optional type `?T`.
    optional_type,
    /// Opening brace `{` of a statement block.
    block_start,
    /// Complete `{ … }` block expression or body.
    block,
    /// Introducer of a local `let` or `var` binding.
    local_decl_introducer,
    /// Diverging `else` block of a `let … else` statement.
    let_else_branch,
    /// Complete local variable declaration statement.
    local_decl_stmt,
    /// Introducer of a `defer` or `errdefer` statement.
    defer_introducer,
    /// Complete `defer` or `errdefer` statement.
    defer_stmt,
    /// Introducer of a `return` statement.
    return_introducer,
    /// Complete `return` statement.
    return_stmt,
    /// Introducer of a `break` statement.
    break_introducer,
    /// Complete `break` statement.
    break_stmt,
    /// Complete `continue` statement.
    continue_stmt,
    /// Introducer of a `for` loop.
    for_introducer,
    /// Header range/iterator clause of a `for` loop.
    for_header,
    /// Complete `for` loop statement.
    for_stmt,
    /// Introducer of a `while` loop.
    while_introducer,
    /// Condition header of a `while` loop.
    while_header,
    /// Complete `while` loop statement.
    while_stmt,
    /// Introducer of an unconditional `loop`.
    loop_introducer,
    /// Complete unconditional `loop` expression.
    loop_expr,
    /// Assignment or compound-assignment statement.
    assign_stmt,
    /// Expression statement terminated by `;`.
    expr_stmt,
    /// Empty semicolon statement.
    empty_stmt,
    /// Wildcard `_` pattern.
    wildcard_pat,
    /// Constant literal pattern.
    literal_pat,
    /// Inclusive or exclusive range pattern.
    range_pat,
    /// Opening parenthesis of a tuple pattern.
    tuple_pat_start,
    /// Complete tuple pattern.
    tuple_pat,
    /// Identifier binding pattern.
    ident_pat,
    /// Enum variant destructuring pattern.
    variant_pat,
    /// Qualified path pattern.
    path_pat,
    /// Opening brace of a struct destructuring pattern.
    struct_pat_start,
    /// Single field pattern inside a struct pattern.
    field_pat,
    /// Complete struct destructuring pattern.
    struct_pat,
    /// Disjunctive `|` pattern.
    or_pat,
    /// Scalar literal expression (`int`, `float`, `string`, `char`, `bool`).
    literal_expr,
    /// Receiver `self` value expression.
    self_expr,
    /// Contextual enum/union variant expression (`.Variant`).
    contextual_variant_expr,
    /// Opening parenthesis of a grouped or tuple expression.
    paren_expr_start,
    /// Complete parenthesized or tuple expression.
    tuple_or_paren_expr,
    /// Opening bracket of an array literal expression.
    array_expr_start,
    /// Complete array literal expression.
    array_expr,
    /// Opening delimiter of a closure expression.
    closure_start,
    /// Parameter declaration inside a closure header.
    closure_param,
    /// Complete closure expression.
    closure_expr,
    /// Introducer of an `if` expression.
    if_introducer,
    /// Condition expression of an `if` branch.
    if_cond,
    /// Complete `if` expression.
    if_expr,
    /// `else` or `else if` branch of an `if` expression.
    else_branch,
    /// Introducer of a `match` expression.
    match_introducer,
    /// Start of a single `match` arm.
    match_arm_start,
    /// Complete `match` arm (`pattern => expr`).
    match_arm,
    /// Complete `match` expression.
    match_expr,
    /// Unary prefix operator expression (`-x`, `!x`, `&x`, `*x`).
    prefix_expr,
    /// Binary infix operator expression (`lhs op rhs`).
    infix_expr,
    /// Postfix error propagation `?` expression.
    postfix_try_expr,
    /// Postfix `.await` expression.
    postfix_await_expr,
    /// Field access (`expr.field`) or method call receiver expression.
    field_or_method_expr,
    /// Slice or array indexing expression (`expr[index]`).
    index_expr,
    /// Opening parenthesis of a function call argument list.
    call_args_start,
    /// Single argument inside a function call.
    call_arg,
    /// Complete function or method call expression.
    call_expr,
    /// Opening brace of a struct literal initializer.
    struct_lit_start,
    /// Single `.field = value` initializer inside a struct literal.
    field_init,
    /// Complete struct literal expression.
    struct_lit_expr,
    /// View block expression.
    view_block_expr,
    /// Explicit type cast expression (`expr as Type`).
    cast_expr,
    /// Generic leaf token node in the lossless CST.
    token_leaf,
    /// Temporary pre-order placeholder node reserved while parsing a bracketed construct.
    placeholder,
    /// Leaf error recovery node wrapping an unexpected or skipped token.
    invalid_parse_leaf,
    /// Start marker of a bracketed syntax error recovery region.
    invalid_parse_start,
    /// Complete bracketed syntax error recovery subtree (`DR-12` Section 1.4).
    invalid_parse_subtree,

    /// Alias for `.file_end` representing the root source file CST node.
    pub const source_file: CstNodeKind = .file_end;
    /// Alias for `.fn_item`.
    pub const fn_decl: CstNodeKind = .fn_item;
    /// Alias for `.struct_item`.
    pub const struct_decl: CstNodeKind = .struct_item;
    /// Alias for `.enum_item`.
    pub const enum_decl: CstNodeKind = .enum_item;
    /// Alias for `.trait_item`.
    pub const trait_decl: CstNodeKind = .trait_item;
    /// Alias for `.impl_item`.
    pub const impl_decl: CstNodeKind = .impl_item;
    /// Alias for `.local_decl_stmt`.
    pub const let_stmt: CstNodeKind = .local_decl_stmt;
    /// Alias for `.block`.
    pub const block_expr: CstNodeKind = .block;
    /// Alias for `.infix_expr`.
    pub const binary_expr: CstNodeKind = .infix_expr;
    /// Alias for `.prefix_expr`.
    pub const unary_expr: CstNodeKind = .prefix_expr;
    /// Alias for `.field_or_method_expr`.
    pub const field_expr: CstNodeKind = .field_or_method_expr;
    /// Alias for `.ident_pat`.
    pub const ident_expr: CstNodeKind = .ident_pat;
    /// Alias for `.named_type`.
    pub const type_ref: CstNodeKind = .named_type;
    /// Alias for `.fn_param`.
    pub const param: CstNodeKind = .fn_param;
    /// Alias for `.invalid_parse_subtree`.
    pub const error_recovery: CstNodeKind = .invalid_parse_subtree;
};

/// 1-byte bit-packed flags attached to each `CstNodeRecord` (`DR-12` Section 1.4).
pub const CstNodeFlags = packed struct(u8) {
    /// `true` if this CST node or any child in its subtree contains a syntax error.
    has_error: bool = false,
    /// `true` if this node wraps a parser-synthesized or lexer-injected recovery token.
    is_missing_or_injected: bool = false,
    /// `true` if this node is a composite bracketed subtree with children.
    is_bracketed: bool = false,
    /// Small direct child count (`0..30`; `31` indicates variable arity walked via `subtree_size`).
    child_arity_small: u5 = 0,
};

/// 10-byte SoA CST node record (`1B kind + 1B flags + 4B token + 4B subtree_size`, zero padding in SoA).
pub const CstNodeRecord = struct {
    /// Syntactic classification of this CST node (`1` byte).
    kind: CstNodeKind,
    /// Bit-packed error, synthesis, and child arity flags (`1` byte).
    flags: CstNodeFlags = .{},
    /// Primary or anchor token associated with this CST node (`4` bytes).
    token: TokenIndex,
    /// Total number of CST nodes in this node's subtree including itself (`1` for leaves, `4` bytes).
    subtree_size: u32 = 1,
};

/// State tag for the explicit non-recursive parser state stack (`DR-12` Section 1.4).
pub const ParseStateKind = enum(u8) {
    /// Top-level file item loop.
    file_loop = 0,
    /// Top-level item introducer dispatch.
    item_dispatch,
    /// Top-level item completion handler.
    item_finish,
    /// Function signature state after parameter list.
    fn_sig_after_params,
    /// Function signature return type state.
    fn_sig_return_type,
    /// Function body block or extern semicolon state.
    fn_body_or_semi,
    /// Struct field declaration loop.
    struct_fields_loop,
    /// Enum variant declaration loop.
    enum_variants_loop,
    /// Trait member declaration loop.
    trait_members_loop,
    /// Impl block member declaration loop.
    impl_members_loop,
    /// Block statement loop (`{ stmt* }`).
    block_stmt_loop,
    /// Closing delimiter handler for a block.
    block_finish,
    /// Local binding state after pattern.
    local_decl_after_pat,
    /// Local binding state after optional `: Type`.
    local_decl_after_type,
    /// Local binding initializer expression state.
    local_decl_init,
    /// Local binding `else` diverging block state.
    local_decl_else_block,
    /// `if` expression state after condition.
    if_after_cond,
    /// `if` expression state after consequence block.
    if_after_then,
    /// `match` expression arm loop.
    match_arms_loop,
    /// `match` arm right-hand-side expression state.
    match_arm_rhs,
    /// Pratt operator-precedence expression loop.
    expr_pratt_loop,
    /// Unary prefix operator completion state.
    expr_prefix_finish,
    /// Function call argument list loop.
    call_args_loop,
    /// Struct literal field initializer loop.
    struct_lit_fields_loop,
    /// Type expression parsing state.
    type_parse,
    /// Pattern expression parsing state.
    pattern_parse,
    /// Parenthesized `( … )` group state.
    delimited_paren,
    /// Brace `{ … }` group state.
    delimited_brace,
    /// Bracket `[ … ]` group state.
    delimited_bracket,

    /// Alias for `.file_loop`.
    pub const root: ParseStateKind = .file_loop;
    /// Alias for `.item_dispatch`.
    pub const item_list: ParseStateKind = .item_dispatch;
    /// Alias for `.block_stmt_loop`.
    pub const stmt_list: ParseStateKind = .block_stmt_loop;
    /// Alias for `.expr_pratt_loop`.
    pub const expr_bp: ParseStateKind = .expr_pratt_loop;
    /// Alias for `.type_parse`.
    pub const type_annotation: ParseStateKind = .type_parse;
    /// Alias for `.pattern_parse`.
    pub const pattern: ParseStateKind = .pattern_parse;
};

/// Exact 8-byte explicit parser stack frame (`extern struct`, `512 * 8B = 4,096B` max stack).
pub const ParseState = extern struct {
    /// Active grammar production state (`1` byte).
    kind: ParseStateKind,
    /// Pratt minimum binding power (`0..30`) or mode bitmask (`1` byte).
    precedence_or_mode: u8 = 0,
    /// `true` if a syntax error occurred within this active production (`1` byte).
    has_error: bool = false,
    /// Recovery synchronization token set selector (`1` byte).
    recovery_sync_set: u8 = 0,
    /// Saved `CstNodeIndex` where this production's subtree started (`4` bytes).
    subtree_start: u32 = 0,
};

// ----------------------- AST Node Types -----------------------

/// Abstract Syntax Tree (AST) node discriminant tag, including fault-tolerant semantic hole variants.
pub const AstTag = enum(u8) {
    /// Root compilation unit node (`0`).
    root = 0,
    /// Module declaration (`mod`).
    mod_decl,
    /// Import declaration (`use`).
    use_decl,
    /// Compile-time constant declaration (`const`).
    const_decl,
    /// Type alias declaration (`type`).
    type_alias_decl,
    /// Struct type declaration (`struct`).
    struct_decl,
    /// Enum type declaration (`enum`).
    enum_decl,
    /// Untagged or tagged union declaration (`union`).
    union_decl,
    /// Trait interface declaration (`trait`).
    trait_decl,
    /// Trait or inherent implementation block (`impl`).
    impl_decl,
    /// Function declaration (`fn`).
    fn_decl,
    /// Built-in primitive type node.
    prim_type,
    /// Named path type node.
    named_type,
    /// Generic parameterized type node (`Type[A, B]`).
    generic_type,
    /// Borrowed reference type node (`&T` / `&mut T`).
    ref_type,
    /// Raw pointer type node (`*T` / `*mut T`).
    ptr_type,
    /// Ownership/region mode-annotated type node.
    mode_type,
    /// Fixed-length array type node (`[T; N]`).
    array_type,
    /// Dynamically sized slice type node (`[T]`).
    slice_type,
    /// Tuple type node (`(T1, T2)`).
    tuple_type,
    /// Function type node (`fn(T) -> U`).
    fn_type,
    /// Optional type node (`?T`).
    optional_type,
    /// Lexical statement block (`{ … }`).
    block,
    /// Local `let` or `var` variable declaration.
    local_var_decl,
    /// Scope-exit `defer` or `errdefer` statement.
    defer_stmt,
    /// Function `return` statement.
    return_stmt,
    /// Loop `break` statement.
    break_stmt,
    /// Loop `continue` statement.
    continue_stmt,
    /// Iterator `for` loop statement.
    for_stmt,
    /// Conditional `while` loop statement.
    while_stmt,
    /// Unconditional `loop` expression.
    loop_expr,
    /// Variable or place assignment statement.
    assign_stmt,
    /// Integer literal expression.
    int_lit,
    /// Floating-point literal expression.
    float_lit,
    /// UTF-8 string literal expression.
    string_lit,
    /// Unicode scalar character literal expression.
    char_lit,
    /// Boolean literal expression (`true` / `false`).
    bool_lit,
    /// Receiver `self` value expression.
    self_val,
    /// Unqualified identifier expression.
    ident_expr,
    /// Multi-segment path expression (`a::b::c`).
    path_expr,
    /// Contextual enum variant literal (`.Variant`).
    contextual_variant,
    /// Unary prefix operation expression.
    unary_expr,
    /// Binary infix operation expression.
    binary_expr,
    /// Pipeline `|>` expression.
    pipe_expr,
    /// Explicit `as` cast expression.
    cast_expr,
    /// Postfix `?` error-propagation expression.
    try_expr,
    /// Postfix `.await` expression.
    await_expr,
    /// Struct/tuple field access (`lhs.field`).
    field_access,
    /// Method call expression (`receiver.method(args)`).
    method_call,
    /// Generic function call with explicit type arguments.
    generic_call,
    /// Standard function call expression (`callee(args)`).
    call_expr,
    /// Array or slice indexing expression (`base[index]`).
    index_expr,
    /// Struct value initializer expression.
    struct_lit,
    /// Tuple value initializer expression.
    tuple_lit,
    /// Array value initializer expression.
    array_lit,
    /// Anonymous closure expression.
    closure_expr,
    /// Conditional `if` / `else` expression.
    if_expr,
    /// Pattern-matching `match` expression.
    match_expr,
    /// Wildcard `_` pattern.
    wildcard_pat,
    /// Variable binding pattern.
    bind_pat,
    /// Literal constant pattern.
    lit_pat,
    /// Enum variant destructuring pattern.
    variant_pat,
    /// Struct destructuring pattern.
    struct_pat,
    /// Tuple destructuring pattern.
    tuple_pat,
    /// Disjunctive `|` pattern.
    or_pat,
    /// Fault-tolerant top-level item hole membrane (`PLAN.md` Section 2.4 & `DR-12` Section 2.3).
    item_hole,
    /// Fault-tolerant statement hole membrane.
    stmt_hole,
    /// Fault-tolerant expression hole membrane (synthesizes `TypeId.err_ty`).
    expr_hole,
    /// Fault-tolerant type expression hole membrane (synthesizes `TypeId.err_ty`).
    type_hole,
    /// Fault-tolerant pattern hole membrane.
    pattern_hole,
    /// Incomplete member access (`expr.` at cursor) preserved for IDE completion.
    incomplete_member_access,
    /// Incomplete call (`callee(arg1, ` at cursor) preserved for IDE signature help.
    incomplete_call,

    /// Alias for `.local_var_decl`.
    pub const var_decl: AstTag = .local_var_decl;
    /// Alias for `.for_stmt`.
    pub const for_loop: AstTag = .for_stmt;
    /// Alias for `.while_stmt`.
    pub const while_loop: AstTag = .while_stmt;
    /// Alias for `.ident_expr`.
    pub const ident: AstTag = .ident_expr;
    /// Alias for `.int_lit`.
    pub const int_literal: AstTag = .int_lit;
    /// Alias for `.float_lit`.
    pub const float_literal: AstTag = .float_lit;
    /// Alias for `.string_lit`.
    pub const string_literal: AstTag = .string_lit;
    /// Alias for `.bool_lit`.
    pub const bool_literal: AstTag = .bool_lit;
    /// Alias for `.named_type`.
    pub const type_named: AstTag = .named_type;
    /// Alias for `.ptr_type`.
    pub const type_ptr: AstTag = .ptr_type;
    /// Alias for `.slice_type`.
    pub const type_slice: AstTag = .slice_type;
    /// Alias for `.expr_hole`.
    pub const error_node: AstTag = .expr_hole;
};

/// 13-byte SoA / 16-byte AoS AST node (`1B tag + 4B main_token + 4B lhs + 4B rhs`, zero wasted columns).
pub const AstNode = struct {
    /// Syntactic construct or semantic hole tag (`1` byte in SoA).
    tag: AstTag,
    /// Primary anchor token index (`4` bytes).
    main_token: TokenIndex,
    /// Left-hand operand (`NodeIndex`, `TokenIndex`, or `ExtraIndex`, `4` bytes).
    lhs: PackedOperand = .{},
    /// Right-hand operand (`NodeIndex`, `TokenIndex`, or `ExtraIndex`, `4` bytes).
    rhs: PackedOperand = .{},
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum number of lexical tokens allowed in a single source file (`4,194,304`, `E0104`).
pub const MAX_TOKENS_PER_FILE: usize = 4 * 1024 * 1024;
/// Maximum explicit parser state stack depth (`512` frames = `4,096` bytes, `E0203`).
pub const MAX_PARSE_DEPTH: usize = 512;
/// Maximum number of CST nodes allowed in a single `LosslessCstArena` (`8,388,608`).
pub const MAX_CST_NODES: usize = 8 * 1024 * 1024;
/// Maximum number of AST nodes allowed in a single `AstArena` (`8,388,608`).
pub const MAX_AST_NODES: usize = 8 * 1024 * 1024;

// -------------------------------------- INTERNALS --------------------------------------

comptime {
    std.debug.assert(@typeInfo(TokenKind).@"enum".field_names.len == 112);
    std.debug.assert(@sizeOf(TokenKind) == 1);
    std.debug.assert(@sizeOf(TokenFlags) == 1);
    std.debug.assert(@sizeOf(PackedTriviaSpan) == 4);
    std.debug.assert(@sizeOf(TriviaKind) == 1);
    std.debug.assert(@sizeOf(TriviaPiece) == 8);
    std.debug.assert(@alignOf(TriviaPiece) == 4);
    std.debug.assert(@sizeOf(TokenRecord) == 12);
    std.debug.assert(@alignOf(TokenRecord) == 4);
    std.debug.assert(@sizeOf(CstNodeKind) == 1);
    std.debug.assert(@sizeOf(CstNodeFlags) == 1);
    std.debug.assert(@sizeOf(CstNodeRecord) == 12);
    std.debug.assert(@sizeOf(ParseStateKind) == 1);
    std.debug.assert(@sizeOf(ParseState) == 8);
    std.debug.assert(@alignOf(ParseState) == 4);
    std.debug.assert(@sizeOf(AstTag) == 1);
    std.debug.assert(@sizeOf(AstNode) == 16);
    std.debug.assert(@alignOf(AstNode) == 4);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ------------------------ Token Buffer ------------------------

/// Structure-of-Arrays (SoA) token stream and trivia table (`12` bytes/token + `8` bytes/trivia).
pub const TokenBuffer = struct {
    /// Backing allocator owning the SoA token columns and trivia array.
    allocator: std.mem.Allocator,
    /// SoA token columns (`kind`, `flags`, `byte_len`, `byte_offset`, `trivia_span`).
    tokens: std.MultiArrayList(TokenRecord) = .empty,
    /// Contiguous table of leading and trailing `TriviaPiece` records.
    trivia: std.ArrayList(TriviaPiece) = .empty,

    /// Initializes an empty `TokenBuffer` bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) TokenBuffer {
        return .{ .allocator = allocator };
    }

    /// Releases all SoA token columns and trivia storage.
    pub fn deinit(self: *TokenBuffer) void {
        self.tokens.deinit(self.allocator);
        self.trivia.deinit(self.allocator);
        self.* = undefined;
    }

    /// Appends a token alongside its leading and trailing `TriviaPiece` slices, enforcing `MAX_TOKENS_PER_FILE`.
    pub fn appendToken(
        self: *TokenBuffer,
        kind: TokenKind,
        flags: TokenFlags,
        byte_offset: u32,
        byte_len: u16,
        leading_trivia: []const TriviaPiece,
        trailing_trivia: []const TriviaPiece,
    ) !TokenIndex {
        if (self.tokens.len >= MAX_TOKENS_PER_FILE) return error.TokenLimitExceeded;
        const clamped_leading: usize = @min(leading_trivia.len, std.math.maxInt(u4));
        const clamped_trailing: usize = @min(trailing_trivia.len, std.math.maxInt(u4));
        if (self.trivia.items.len > std.math.maxInt(u24) - (clamped_leading + clamped_trailing)) {
            return error.TokenLimitExceeded;
        }

        const trivia_start: u24 = @intCast(self.trivia.items.len);
        errdefer self.trivia.shrinkRetainingCapacity(trivia_start);

        if (clamped_leading > 0) {
            try self.trivia.appendSlice(self.allocator, leading_trivia[0..clamped_leading]);
        }
        if (clamped_trailing > 0) {
            try self.trivia.appendSlice(self.allocator, trailing_trivia[0..clamped_trailing]);
        }

        var merged_flags = flags;
        if (clamped_leading > 0) merged_flags.has_leading_trivia_pieces = true;
        if (clamped_trailing > 0) merged_flags.has_trailing_trivia = true;

        const token_index = TokenIndex.fromInt(@intCast(self.tokens.len));
        try self.tokens.append(self.allocator, .{
            .kind = kind,
            .flags = merged_flags,
            .byte_len = byte_len,
            .byte_offset = byte_offset,
            .trivia_span = .{
                .start_index = trivia_start,
                .leading_count = @intCast(clamped_leading),
                .trailing_count = @intCast(clamped_trailing),
            },
        });
        return token_index;
    }

    /// Appends a pre-built `TokenRecord` directly into the SoA buffer.
    pub fn appendTokenRecord(self: *TokenBuffer, record: TokenRecord) !TokenIndex {
        if (self.tokens.len >= MAX_TOKENS_PER_FILE) return error.TokenLimitExceeded;
        const token_index = TokenIndex.fromInt(@intCast(self.tokens.len));
        try self.tokens.append(self.allocator, record);
        return token_index;
    }

    /// Reconstructs the `TokenRecord` at `token_id` in $O(1)$ time.
    pub inline fn getToken(self: *const TokenBuffer, token_id: TokenIndex) TokenRecord {
        std.debug.assert(!token_id.isNone());
        return self.tokens.get(token_id.asInt());
    }

    /// Computes the exact 12-byte `Span` of `token_id` within `file_id`.
    pub inline fn getTokenSpan(self: *const TokenBuffer, file_id: FileId, token_id: TokenIndex) Span {
        const record = self.getToken(token_id);
        return Span.init(file_id, record.byte_offset, record.byte_offset + @as(u32, record.byte_len));
    }

    /// Returns the slice of leading `TriviaPiece` records attached to `token_id`.
    pub inline fn getLeadingTrivia(self: *const TokenBuffer, token_id: TokenIndex) []const TriviaPiece {
        const span_meta = self.tokens.items(.trivia_span)[token_id.asInt()];
        const start_idx: usize = span_meta.start_index;
        return self.trivia.items[start_idx .. start_idx + span_meta.leading_count];
    }

    /// Returns the slice of trailing `TriviaPiece` records attached to `token_id`.
    pub inline fn getTrailingTrivia(self: *const TokenBuffer, token_id: TokenIndex) []const TriviaPiece {
        const span_meta = self.tokens.items(.trivia_span)[token_id.asInt()];
        const start_idx: usize = @as(usize, span_meta.start_index) + span_meta.leading_count;
        return self.trivia.items[start_idx .. start_idx + span_meta.trailing_count];
    }

    /// Returns the total number of tokens stored in this `TokenBuffer`.
    pub inline fn countTokens(self: *const TokenBuffer) usize {
        return self.tokens.len;
    }
};

// --------------------- Lossless CST Arena ---------------------

/// Lossless Concrete Syntax Tree (CST) SoA arena (`10` bytes/node) with $O(1)$ subtree skipping.
pub const LosslessCstArena = struct {
    /// Backing allocator for the SoA CST columns and explicit parse stack.
    allocator: std.mem.Allocator,
    /// SoA CST node columns (`kind`, `flags`, `token`, `subtree_size`).
    nodes: std.MultiArrayList(CstNodeRecord) = .empty,
    /// Explicit non-recursive parser state stack bounded by `MAX_PARSE_DEPTH` (`512`).
    parse_stack: std.ArrayList(ParseState) = .empty,
    /// `true` if any node in the CST was marked with `flags.has_error`.
    has_parse_errors: bool = false,

    /// Initializes an empty `LosslessCstArena` bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) LosslessCstArena {
        return .{ .allocator = allocator };
    }

    /// Releases all CST node columns and parser stack storage.
    pub fn deinit(self: *LosslessCstArena) void {
        self.nodes.deinit(self.allocator);
        self.parse_stack.deinit(self.allocator);
        self.* = undefined;
    }

    /// Pushes `state` onto the explicit parser stack, returning `error.ParseDepthExceeded` past `MAX_PARSE_DEPTH`.
    pub fn pushParseState(self: *LosslessCstArena, state: ParseState) !void {
        if (self.parse_stack.items.len >= MAX_PARSE_DEPTH) return error.ParseDepthExceeded;
        try self.parse_stack.append(self.allocator, state);
    }

    /// Pops and returns the top `ParseState` from the explicit parser stack, or `null` if empty.
    pub fn popParseState(self: *LosslessCstArena) ?ParseState {
        return self.parse_stack.pop();
    }

    /// Starts a pre-order composite CST node, returning its `CstNodeIndex` for later `finishNode` patching.
    pub fn startNode(self: *LosslessCstArena, kind: CstNodeKind, token: TokenIndex) !CstNodeIndex {
        if (self.nodes.len >= MAX_CST_NODES) return error.CstNodeLimitExceeded;
        const node_id = CstNodeIndex.fromInt(@intCast(self.nodes.len));
        try self.nodes.append(self.allocator, .{
            .kind = kind,
            .flags = .{ .is_bracketed = true },
            .token = token,
            .subtree_size = 1,
        });
        return node_id;
    }

    /// Finishes the composite CST node at `node_id`, recording its exact pre-order `subtree_size`.
    pub fn finishNode(self: *LosslessCstArena, node_id: CstNodeIndex, flags: CstNodeFlags) void {
        const start_idx = node_id.asInt();
        std.debug.assert(start_idx < self.nodes.len);
        var merged_flags = flags;
        merged_flags.is_bracketed = true;
        if (merged_flags.has_error) self.has_parse_errors = true;

        self.nodes.items(.flags)[start_idx] = merged_flags;
        self.nodes.items(.subtree_size)[start_idx] = @intCast(self.nodes.len - start_idx);
    }

    /// Appends a single leaf CST node (`subtree_size = 1`), enforcing `MAX_CST_NODES`.
    pub fn appendLeafNode(
        self: *LosslessCstArena,
        kind: CstNodeKind,
        token: TokenIndex,
        flags: CstNodeFlags,
    ) !CstNodeIndex {
        if (self.nodes.len >= MAX_CST_NODES) return error.CstNodeLimitExceeded;
        if (flags.has_error) self.has_parse_errors = true;
        const node_id = CstNodeIndex.fromInt(@intCast(self.nodes.len));
        try self.nodes.append(self.allocator, .{
            .kind = kind,
            .flags = flags,
            .token = token,
            .subtree_size = 1,
        });
        return node_id;
    }

    /// Returns the `CstNodeRecord` at `node_id` in $O(1)$ time.
    pub inline fn getNode(self: *const LosslessCstArena, node_id: CstNodeIndex) CstNodeRecord {
        std.debug.assert(!node_id.isNone());
        return self.nodes.get(node_id.asInt());
    }

    /// Returns the total number of CST nodes currently stored in the arena.
    pub inline fn countNodes(self: *const LosslessCstArena) usize {
        return self.nodes.len;
    }

    /// Reconstructs the exact original UTF-8 source text from `token_buffer` and its trivia slices.
    pub fn reconstructSource(
        self: *const LosslessCstArena,
        allocator: std.mem.Allocator,
        original_source: []const u8,
        token_buffer: *const TokenBuffer,
    ) ![]u8 {
        _ = self;
        // [1] Compute total reconstructed byte length across all non-synthesized trivia and tokens:
        var total_bytes: usize = 0;
        const token_count = token_buffer.countTokens();
        var i: usize = 0;
        while (i < token_count) : (i += 1) {
            const token_id = TokenIndex.fromInt(@intCast(i));
            for (token_buffer.getLeadingTrivia(token_id)) |piece| {
                if (@as(usize, piece.byte_offset) + piece.byte_len > original_source.len) {
                    return error.OutOfBoundsTokenSpan;
                }
                total_bytes = try std.math.add(usize, total_bytes, piece.byte_len);
            }
            const record = token_buffer.getToken(token_id);
            if (!record.flags.is_synthesized) {
                if (@as(usize, record.byte_offset) + record.byte_len > original_source.len) {
                    return error.OutOfBoundsTokenSpan;
                }
                total_bytes = try std.math.add(usize, total_bytes, record.byte_len);
            }
            for (token_buffer.getTrailingTrivia(token_id)) |piece| {
                if (@as(usize, piece.byte_offset) + piece.byte_len > original_source.len) {
                    return error.OutOfBoundsTokenSpan;
                }
                total_bytes = try std.math.add(usize, total_bytes, piece.byte_len);
            }
        }

        // [2] Allocate output buffer once and copy each trivia/token slice in linear order:
        const output_buf = try allocator.alloc(u8, total_bytes);
        var write_cursor: usize = 0;
        i = 0;
        while (i < token_count) : (i += 1) {
            const token_id = TokenIndex.fromInt(@intCast(i));
            for (token_buffer.getLeadingTrivia(token_id)) |piece| {
                const start_off: usize = piece.byte_offset;
                @memcpy(
                    output_buf[write_cursor .. write_cursor + piece.byte_len],
                    original_source[start_off .. start_off + piece.byte_len],
                );
                write_cursor += piece.byte_len;
            }
            const record = token_buffer.getToken(token_id);
            if (!record.flags.is_synthesized and record.byte_len > 0) {
                const start_off: usize = record.byte_offset;
                @memcpy(
                    output_buf[write_cursor .. write_cursor + record.byte_len],
                    original_source[start_off .. start_off + record.byte_len],
                );
                write_cursor += record.byte_len;
            }
            for (token_buffer.getTrailingTrivia(token_id)) |piece| {
                const start_off: usize = piece.byte_offset;
                @memcpy(
                    output_buf[write_cursor .. write_cursor + piece.byte_len],
                    original_source[start_off .. start_off + piece.byte_len],
                );
                write_cursor += piece.byte_len;
            }
        }
        std.debug.assert(write_cursor == total_bytes);
        return output_buf;
    }
};

// ------------------------- AST Arena --------------------------

/// Lowered Structure-of-Arrays (SoA) Abstract Syntax Tree store (`13` bytes/node + `extra_data` trail).
pub const AstArena = struct {
    /// Backing allocator for the SoA node columns, `extra_data` trail, and `ast_to_cst` origin map.
    allocator: std.mem.Allocator,
    /// SoA AST node columns (`tag`, `main_token`, `lhs`, `rhs`).
    nodes: std.MultiArrayList(AstNode) = .empty,
    /// Contiguous `u32` trail storing variable-length child index lists and extended node payloads.
    extra_data: std.ArrayList(u32) = .empty,
    /// Dense side-table mapping each `NodeIndex` to its originating `CstNodeIndex` (`CstNodeIndex.none` if unmapped).
    ast_to_cst: std.ArrayList(CstNodeIndex) = .empty,

    /// Initializes an empty `AstArena` bound to `allocator`.
    pub fn init(allocator: std.mem.Allocator) AstArena {
        return .{ .allocator = allocator };
    }

    /// Releases all SoA AST columns, `extra_data` trail, and `ast_to_cst` mappings.
    pub fn deinit(self: *AstArena) void {
        self.nodes.deinit(self.allocator);
        self.extra_data.deinit(self.allocator);
        self.ast_to_cst.deinit(self.allocator);
        self.* = undefined;
    }

    /// Appends `node` to the SoA store with `.none` CST origin, enforcing `MAX_AST_NODES`.
    pub fn appendNode(self: *AstArena, node: AstNode) !NodeIndex {
        return self.appendNodeWithCst(node, .none);
    }

    /// Appends `node` and records its originating `cst_origin` handle in `ast_to_cst`.
    pub fn appendNodeWithCst(self: *AstArena, node: AstNode, cst_origin: CstNodeIndex) !NodeIndex {
        if (self.nodes.len >= MAX_AST_NODES) return error.AstNodeLimitExceeded;
        try self.nodes.ensureUnusedCapacity(self.allocator, 1);
        try self.ast_to_cst.ensureUnusedCapacity(self.allocator, 1);
        const node_id = NodeIndex.fromInt(@intCast(self.nodes.len));
        self.nodes.appendAssumeCapacity(node);
        self.ast_to_cst.appendAssumeCapacity(cst_origin);
        return node_id;
    }

    /// Retrieves the `AstNode` at `node_id` in $O(1)$ time.
    pub inline fn getNode(self: *const AstArena, node_id: NodeIndex) AstNode {
        std.debug.assert(!node_id.isNone());
        return self.nodes.get(node_id.asInt());
    }

    /// Returns the originating `CstNodeIndex` for `node_id`.
    pub inline fn getCstOrigin(self: *const AstArena, node_id: NodeIndex) CstNodeIndex {
        std.debug.assert(!node_id.isNone());
        return self.ast_to_cst.items[node_id.asInt()];
    }

    /// Appends `values` to `extra_data` and returns the starting `ExtraIndex`.
    pub fn appendExtraSlice(self: *AstArena, values: []const u32) !ExtraIndex {
        if (values.len > std.math.maxInt(u30) or
            self.extra_data.items.len > std.math.maxInt(u30) - values.len)
        {
            return error.OutOfMemory;
        }
        const start_extra = ExtraIndex.fromInt(@intCast(self.extra_data.items.len));
        try self.extra_data.appendSlice(self.allocator, values);
        return start_extra;
    }

    /// Returns a read-only slice of `slice_len` elements from `extra_data` starting at `start_extra`.
    pub inline fn getExtraSlice(self: *const AstArena, start_extra: ExtraIndex, slice_len: usize) []const u32 {
        std.debug.assert(!start_extra.isNone());
        const start_idx: usize = start_extra.asInt();
        return self.extra_data.items[start_idx .. start_idx + slice_len];
    }

    /// Returns the total number of AST nodes stored in this `AstArena`.
    pub inline fn countNodes(self: *const AstArena) usize {
        return self.nodes.len;
    }
};

/// Canonical alias for `AstArena` (`DR-01` Section 4.1).
pub const AstStore = AstArena;

// ------------------------- Unit Tests -------------------------

test "test_token_buffer_trivia_and_lossless_cst_reconstruction" {
    const source_code = "fn main() {\n    return 0;\n}\n";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();

    // Tokenize a small fragment with trivia pieces covering the entire `source_code`:
    const tok_fn = try token_buf.appendToken(.kw_fn, .{}, 0, 2, &.{}, &.{
        .{ .kind = .spaces, .byte_offset = 2, .byte_len = 1 },
    });
    const tok_main = try token_buf.appendToken(.ident, .{}, 3, 4, &.{}, &.{});
    const tok_lparen = try token_buf.appendToken(.lparen, .{}, 7, 1, &.{}, &.{});
    const tok_rparen = try token_buf.appendToken(.rparen, .{}, 8, 1, &.{}, &.{
        .{ .kind = .spaces, .byte_offset = 9, .byte_len = 1 },
    });
    const tok_lbrace = try token_buf.appendToken(.lbrace, .{}, 10, 1, &.{}, &.{
        .{ .kind = .newline_lf, .byte_offset = 11, .byte_len = 1 },
    });
    const tok_return = try token_buf.appendToken(
        .kw_return,
        .{ .has_leading_newline = true },
        16,
        6,
        &.{.{ .kind = .spaces, .byte_offset = 12, .byte_len = 4 }},
        &.{.{ .kind = .spaces, .byte_offset = 22, .byte_len = 1 }},
    );
    const tok_zero = try token_buf.appendToken(.int_lit, .{}, 23, 1, &.{}, &.{});
    const tok_semi = try token_buf.appendToken(.semi, .{}, 24, 1, &.{}, &.{
        .{ .kind = .newline_lf, .byte_offset = 25, .byte_len = 1 },
    });
    const tok_rbrace = try token_buf.appendToken(
        .rbrace,
        .{ .has_leading_newline = true },
        26,
        1,
        &.{},
        &.{.{ .kind = .newline_lf, .byte_offset = 27, .byte_len = 1 }},
    );
    // Synthesized recovery token (`byte_len == 0`) must not alter reconstructed output:
    _ = try token_buf.appendToken(.eof, .{ .is_synthesized = true }, 28, 0, &.{}, &.{});

    try std.testing.expectEqual(@as(usize, 10), token_buf.countTokens());
    try std.testing.expectEqual(@as(usize, 1), token_buf.getTrailingTrivia(tok_fn).len);
    try std.testing.expectEqual(@as(usize, 1), token_buf.getLeadingTrivia(tok_return).len);

    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();

    const root_node = try cst_arena.startNode(.source_file, tok_fn);
    const fn_node = try cst_arena.startNode(.fn_decl, tok_fn);
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_fn, .{});
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_main, .{});
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_lparen, .{});
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_rparen, .{});
    const block_node = try cst_arena.startNode(.block, tok_lbrace);
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_lbrace, .{});
    _ = try cst_arena.appendLeafNode(.return_stmt, tok_return, .{});
    _ = try cst_arena.appendLeafNode(.literal_expr, tok_zero, .{});
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_semi, .{});
    _ = try cst_arena.appendLeafNode(.token_leaf, tok_rbrace, .{});
    cst_arena.finishNode(block_node, .{ .child_arity_small = 5 });
    cst_arena.finishNode(fn_node, .{ .child_arity_small = 5 });
    cst_arena.finishNode(root_node, .{ .child_arity_small = 1 });

    // Verify O(1) pre-order subtree_size skipping invariant:
    const fn_rec = cst_arena.getNode(fn_node);
    try std.testing.expectEqual(@as(u32, 12), cst_arena.getNode(root_node).subtree_size);
    try std.testing.expectEqual(@as(u32, 11), fn_rec.subtree_size);
    try std.testing.expectEqual(@as(u32, 6), cst_arena.getNode(block_node).subtree_size);
    try std.testing.expectEqual(cst_arena.countNodes(), @as(usize, fn_node.asInt() + fn_rec.subtree_size));

    const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, source_code, &token_buf);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(source_code, reconstructed);
}

test "test_cst_parse_depth_cap_and_ast_arena_extra_data" {
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();

    var depth_idx: usize = 0;
    while (depth_idx < MAX_PARSE_DEPTH) : (depth_idx += 1) {
        try cst_arena.pushParseState(.{ .kind = .expr_pratt_loop, .subtree_start = @intCast(depth_idx) });
    }
    try std.testing.expectError(
        error.ParseDepthExceeded,
        cst_arena.pushParseState(.{ .kind = .expr_pratt_loop }),
    );
    try std.testing.expect(cst_arena.popParseState() != null);

    var ast_arena = AstArena.init(std.testing.allocator);
    defer ast_arena.deinit();

    const child_indices = [_]u32{ 1, 2, 3 };
    const extra_start = try ast_arena.appendExtraSlice(&child_indices);
    const hole_node = try ast_arena.appendNodeWithCst(.{
        .tag = .expr_hole,
        .main_token = TokenIndex.fromInt(0),
        .lhs = PackedOperand.initExtra(extra_start),
        .rhs = PackedOperand.initToken(TokenIndex.fromInt(4)),
    }, CstNodeIndex.fromInt(2));

    try std.testing.expectEqual(@as(usize, 1), ast_arena.countNodes());
    try std.testing.expectEqual(AstTag.expr_hole, ast_arena.getNode(hole_node).tag);
    try std.testing.expectEqual(CstNodeIndex.fromInt(2), ast_arena.getCstOrigin(hole_node));
    try std.testing.expectEqualSlices(u32, &child_indices, ast_arena.getExtraSlice(extra_start, 3));
}

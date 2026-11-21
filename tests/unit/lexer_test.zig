//! Unit Tests for High-Speed Deterministic Lexer & Trivia Scanner (`tests/unit/lexer_test.zig`)
//!
//! Verifies all 120 `TokenKind` variants (`0..119`), all 50 language keywords and 20 primitive types,
//! all 10 `TriviaKind` classifications across `LF` and `CRLF`, disjoint identifier casing (`W0201`),
//! numeric literals and suffixes (`E0103`), single/multiline/byte strings and escapes (`W0101`, `E0101`,
//! `E0102`, `E0113`–`E0117`), resource caps (`E0104`), and lossless CST reconstruction.
//!
//! Enforces 100% line and branch coverage of `stage0/src/lexer.zig` with zero memory leaks.

const std = @import("std");
const corex = @import("corex");

const lexer = corex.lexer;
const syntax = corex.syntax_arenas;
const diag = corex.diagnostic;
const FileId = corex.FileId;
const TokenIndex = corex.TokenIndex;
const StringInterner = corex.StringInterner;
const TokenKind = corex.TokenKind;
const TriviaKind = syntax.TriviaKind;
const TokenBuffer = corex.TokenBuffer;
const LosslessCstArena = corex.LosslessCstArena;
const IdentifierCase = corex.IdentifierCase;
const LexerOptions = corex.LexerOptions;
const Lexer = corex.Lexer;
const DiagnosticCode = corex.DiagnosticCode;
const DiagnosticSink = corex.DiagnosticSink;
const SuggestedFix = corex.SuggestedFix;
const TransactionalPatcher = corex.TransactionalPatcher;

// --------------------------------------- CONSTS ----------------------------------------

/// Exhaustive table mapping sample `.cx` lexemes to all 119 non-EOF `TokenKind` variants (`0..118`).
const EXHAUSTIVE_TOKEN_CASES = [_]struct {
    lexeme: []const u8,
    expected: TokenKind,
}{
    .{ .lexeme = "pub", .expected = .kw_pub },
    .{ .lexeme = "mod", .expected = .kw_mod },
    .{ .lexeme = "use", .expected = .kw_use },
    .{ .lexeme = "as", .expected = .kw_as },
    .{ .lexeme = "fn", .expected = .kw_fn },
    .{ .lexeme = "struct", .expected = .kw_struct },
    .{ .lexeme = "enum", .expected = .kw_enum },
    .{ .lexeme = "union", .expected = .kw_union },
    .{ .lexeme = "trait", .expected = .kw_trait },
    .{ .lexeme = "impl", .expected = .kw_impl },
    .{ .lexeme = "type", .expected = .kw_type },
    .{ .lexeme = "const", .expected = .kw_const },
    .{ .lexeme = "let", .expected = .kw_let },
    .{ .lexeme = "var", .expected = .kw_var },
    .{ .lexeme = "bit_field", .expected = .kw_bit_field },
    .{ .lexeme = "comptime", .expected = .kw_comptime },
    .{ .lexeme = "subscript", .expected = .kw_subscript },
    .{ .lexeme = "mut", .expected = .kw_mut },
    .{ .lexeme = "own", .expected = .kw_own },
    .{ .lexeme = "where", .expected = .kw_where },
    .{ .lexeme = "extern", .expected = .kw_extern },
    .{ .lexeme = "async", .expected = .kw_async },
    .{ .lexeme = "await", .expected = .kw_await },
    .{ .lexeme = "unsafe", .expected = .kw_unsafe },
    .{ .lexeme = "defer", .expected = .kw_defer },
    .{ .lexeme = "errdefer", .expected = .kw_errdefer },
    .{ .lexeme = "is", .expected = .kw_is },
    .{ .lexeme = "with", .expected = .kw_with },
    .{ .lexeme = "context", .expected = .kw_context },
    .{ .lexeme = "if", .expected = .kw_if },
    .{ .lexeme = "else", .expected = .kw_else },
    .{ .lexeme = "match", .expected = .kw_match },
    .{ .lexeme = "for", .expected = .kw_for },
    .{ .lexeme = "in", .expected = .kw_in },
    .{ .lexeme = "while", .expected = .kw_while },
    .{ .lexeme = "loop", .expected = .kw_loop },
    .{ .lexeme = "return", .expected = .kw_return },
    .{ .lexeme = "break", .expected = .kw_break },
    .{ .lexeme = "continue", .expected = .kw_continue },
    .{ .lexeme = "catch", .expected = .kw_catch },
    .{ .lexeme = "orelse", .expected = .kw_orelse },
    .{ .lexeme = "unreachable", .expected = .kw_unreachable },
    .{ .lexeme = "yield", .expected = .kw_yield },
    .{ .lexeme = "true", .expected = .kw_true },
    .{ .lexeme = "false", .expected = .kw_false },
    .{ .lexeme = "and", .expected = .kw_and },
    .{ .lexeme = "or", .expected = .kw_or },
    .{ .lexeme = "not", .expected = .kw_not },
    .{ .lexeme = "self", .expected = .kw_self_val },
    .{ .lexeme = "Self", .expected = .kw_self_type },
    .{ .lexeme = "i32", .expected = .prim_type },
    .{ .lexeme = "snake_ident", .expected = .ident },
    .{ .lexeme = "PascalType", .expected = .type_ident },
    .{ .lexeme = "MAX_LIMIT", .expected = .const_ident },
    .{ .lexeme = "42_000", .expected = .int_lit },
    .{ .lexeme = "3.14159", .expected = .float_lit },
    .{ .lexeme = "\"corex\"", .expected = .string_lit },
    .{ .lexeme = "'x'", .expected = .char_lit },
    .{ .lexeme = "b'x'", .expected = .byte_lit },
    .{ .lexeme = "b\"corex\"", .expected = .byte_string_lit },
    .{ .lexeme = "{", .expected = .lbrace },
    .{ .lexeme = "}", .expected = .rbrace },
    .{ .lexeme = "(", .expected = .lparen },
    .{ .lexeme = ")", .expected = .rparen },
    .{ .lexeme = "[", .expected = .lbracket },
    .{ .lexeme = "]", .expected = .rbracket },
    .{ .lexeme = ";", .expected = .semi },
    .{ .lexeme = ",", .expected = .comma },
    .{ .lexeme = ":", .expected = .colon },
    .{ .lexeme = ".", .expected = .dot },
    .{ .lexeme = "..", .expected = .dotdot },
    .{ .lexeme = "..=", .expected = .dotdoteq },
    .{ .lexeme = "...", .expected = .dotdotdot },
    .{ .lexeme = "->", .expected = .arrow },
    .{ .lexeme = "=>", .expected = .fat_arrow },
    .{ .lexeme = "|>", .expected = .pipe_gt },
    .{ .lexeme = "@", .expected = .at },
    .{ .lexeme = "#soa", .expected = .hash_soa },
    .{ .lexeme = "?", .expected = .question },
    .{ .lexeme = "_", .expected = .underscore },
    .{ .lexeme = ":=", .expected = .colon_eq },
    .{ .lexeme = "$", .expected = .dollar },
    .{ .lexeme = "+", .expected = .plus },
    .{ .lexeme = "-", .expected = .minus },
    .{ .lexeme = "*", .expected = .star },
    .{ .lexeme = "/", .expected = .slash },
    .{ .lexeme = "%", .expected = .percent },
    .{ .lexeme = "+%", .expected = .plus_percent },
    .{ .lexeme = "-%", .expected = .minus_percent },
    .{ .lexeme = "*%", .expected = .star_percent },
    .{ .lexeme = "+|", .expected = .plus_pipe },
    .{ .lexeme = "-|", .expected = .minus_pipe },
    .{ .lexeme = "*|", .expected = .star_pipe },
    .{ .lexeme = "==", .expected = .eqeq },
    .{ .lexeme = "!=", .expected = .bang_eq },
    .{ .lexeme = "<", .expected = .lt },
    .{ .lexeme = "<=", .expected = .le },
    .{ .lexeme = ">", .expected = .gt },
    .{ .lexeme = ">=", .expected = .ge },
    .{ .lexeme = "&", .expected = .amp },
    .{ .lexeme = "|", .expected = .pipe },
    .{ .lexeme = "||", .expected = .pipepipe },
    .{ .lexeme = "^", .expected = .caret },
    .{ .lexeme = "!", .expected = .bang },
    .{ .lexeme = "~", .expected = .tilde },
    .{ .lexeme = "<<", .expected = .shl },
    .{ .lexeme = ">>", .expected = .shr },
    .{ .lexeme = "=", .expected = .eq },
    .{ .lexeme = "+=", .expected = .plus_eq },
    .{ .lexeme = "-=", .expected = .minus_eq },
    .{ .lexeme = "*=", .expected = .star_eq },
    .{ .lexeme = "/=", .expected = .slash_eq },
    .{ .lexeme = "%=", .expected = .percent_eq },
    .{ .lexeme = "&=", .expected = .amp_eq },
    .{ .lexeme = "|=", .expected = .pipe_eq },
    .{ .lexeme = "^=", .expected = .caret_eq },
    .{ .lexeme = "<<=", .expected = .shl_eq },
    .{ .lexeme = ">>=", .expected = .shr_eq },
    .{ .lexeme = "`", .expected = .invalid_token },
};

/// Authoritative list of all 20 primitive type keywords that map to `TokenKind.prim_type` (`50`).
const ALL_20_PRIMITIVE_TYPES = [_][]const u8{
    "i8",   "i16",    "i32",  "i64",  "i128", "isize",
    "u8",   "u16",    "u32",  "u64",  "u128", "usize",
    "f32",  "f64",    "bool", "char", "str",  "never",
    "unit", "opaque",
};

// -------------------------------------- INTERNALS --------------------------------------

/// Asserts that `LosslessCstArena.reconstructSource` reproduces `source` byte-for-bit.
fn expectLosslessRoundTrip(source: []const u8, token_buffer: *const TokenBuffer) !void {
    var cst_arena = LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();

    const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, source, token_buffer);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualSlices(u8, source, reconstructed);
}

// ------------------------------------- PUBLIC API --------------------------------------

// ----------------- All 120 TokenKind Variants -----------------

test "test_lexer_all_120_token_kinds_and_20_prim_types_exhaustive" {
    var seen_variants: [120]bool = @splat(false);

    // [1] Verify each of the 119 non-EOF token kinds (`0..118`) and final `.eof` (`119`):
    for (EXHAUSTIVE_TOKEN_CASES, 0..) |test_case, i| {
        var token_buf = TokenBuffer.init(std.testing.allocator);
        defer token_buf.deinit();
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();

        try corex.tokenize(test_case.lexeme, FileId.fromInt(0), &token_buf, &sink, null);
        try std.testing.expectEqual(@as(usize, 2), token_buf.countTokens());

        const tok_record = token_buf.getToken(TokenIndex.fromInt(0));
        const eof_record = token_buf.getToken(TokenIndex.fromInt(1));
        try std.testing.expectEqual(test_case.expected, tok_record.kind);
        try std.testing.expectEqual(@as(usize, i), @as(usize, @backingInt(tok_record.kind)));
        try std.testing.expectEqual(@as(u32, 0), tok_record.byte_offset);
        try std.testing.expectEqual(@as(u16, @intCast(test_case.lexeme.len)), tok_record.byte_len);
        try std.testing.expectEqual(TokenKind.eof, eof_record.kind);

        seen_variants[@backingInt(tok_record.kind)] = true;
        seen_variants[@backingInt(eof_record.kind)] = true;
        try expectLosslessRoundTrip(test_case.lexeme, &token_buf);
    }

    for (seen_variants) |was_seen| {
        try std.testing.expect(was_seen);
    }

    // [2] Verify all 20 primitive type keywords map to `TokenKind.prim_type` (`50`) with zero warnings:
    try std.testing.expectEqual(@as(usize, 20), ALL_20_PRIMITIVE_TYPES.len);
    for (ALL_20_PRIMITIVE_TYPES) |prim_lexeme| {
        const classification = corex.classifyIdentifierOrKeyword(prim_lexeme);
        try std.testing.expectEqual(TokenKind.prim_type, classification.kind);
        try std.testing.expectEqual(IdentifierCase.reserved_or_wildcard, classification.expected_case);
        try std.testing.expect(classification.is_canonical);
        try std.testing.expect(!classification.has_case_violation);

        var token_buf = TokenBuffer.init(std.testing.allocator);
        defer token_buf.deinit();
        var sink = DiagnosticSink.init(std.testing.allocator);
        defer sink.deinit();

        try corex.lexFile(prim_lexeme, FileId.fromInt(0), &token_buf, &sink, null);
        try std.testing.expectEqual(@as(u32, 0), sink.error_count);
        try std.testing.expectEqual(@as(u32, 0), sink.warning_count);
        try std.testing.expectEqual(TokenKind.prim_type, token_buf.getToken(TokenIndex.fromInt(0)).kind);
    }
}

// ----------------- All 10 TriviaKind Variants -----------------

test "test_lexer_all_10_trivia_kinds_lf_crlf_and_comment_utf8_validation" {
    var seen_trivia: [10]bool = @splat(false);

    // [1] Combine UTF-8 BOM, shebang, spaces, tabs, LF, CRLF, comments, and control chars:
    const trivia_source =
        "\xEF\xBB\xBF#!/usr/bin/env corex\r\n" ++
        "  \t\t\n" ++
        "//! Module doc header\r\n" ++
        "/// Item doc comment\n" ++
        "// Regular line comment\n" ++
        "//// Four-slash regular line comment\r\n" ++
        "/* Outer /* nested\r\ninner */ block comment */\x0B\x0C\rlet x = 1;";

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try corex.tokenize(trivia_source, FileId.fromInt(0), &token_buf, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try expectLosslessRoundTrip(trivia_source, &token_buf);

    const let_tok_id = TokenIndex.fromInt(0);
    try std.testing.expect(token_buf.getToken(let_tok_id).flags.has_leading_newline);
    for (token_buf.getLeadingTrivia(let_tok_id)) |piece| {
        seen_trivia[@backingInt(piece.kind)] = true;
    }
    for (seen_trivia) |was_seen| {
        try std.testing.expect(was_seen);
    }

    // [2] Verify shebang without BOM at offset 0 and invalid UTF-8 inside comments / shebang:
    const bad_comment_utf8 = "#!/bin/cx \xFF\n// bad \xC3\x28\n/* nested \xFF unclosed";
    var bad_buf = TokenBuffer.init(std.testing.allocator);
    defer bad_buf.deinit();
    var bad_sink = DiagnosticSink.init(std.testing.allocator);
    defer bad_sink.deinit();

    try corex.tokenize(bad_comment_utf8, FileId.fromInt(0), &bad_buf, &bad_sink, null);
    try std.testing.expectEqual(@as(u32, 4), bad_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0101_invalid_utf8_sequence, bad_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0101_invalid_utf8_sequence, bad_sink.asSlice()[1].code);
    try std.testing.expectEqual(DiagnosticCode.e0101_invalid_utf8_sequence, bad_sink.asSlice()[2].code);
    try std.testing.expectEqual(DiagnosticCode.e0202_unclosed_delimiter, bad_sink.asSlice()[3].code);
    try std.testing.expect(bad_buf.getToken(TokenIndex.fromInt(0)).flags.has_lexer_error);
    try expectLosslessRoundTrip(bad_comment_utf8, &bad_buf);
}

// ----------------- Identifier Casing & W0201 ------------------

test "test_lexer_identifier_classification_casing_helpers_and_w0201_autofix" {
    // [1] Verify `classifyIdentifierOrKeyword` reject paths for empty or non-identifier strings:
    const empty_class = corex.classifyIdentifierOrKeyword("");
    try std.testing.expectEqual(TokenKind.invalid_token, empty_class.kind);
    try std.testing.expect(!empty_class.is_canonical);
    try std.testing.expect(empty_class.has_case_violation);

    try std.testing.expectEqual(
        TokenKind.invalid_token,
        corex.classifyIdentifierOrKeyword("9ident").kind,
    );
    try std.testing.expectEqual(
        TokenKind.invalid_token,
        corex.classifyIdentifierOrKeyword("valid_start$bad").kind,
    );

    // [2] Verify `IdentifierCase` aliases and conversion helpers on boundary inputs:
    try std.testing.expectEqual(IdentifierCase.snake_case, IdentifierCase.snake);
    try std.testing.expectEqual(IdentifierCase.pascal_case, IdentifierCase.pascal);
    try std.testing.expectEqual(IdentifierCase.screaming_snake_case, IdentifierCase.screaming_snake);
    try std.testing.expectEqual(IdentifierCase.reserved_or_wildcard, IdentifierCase.none);

    const snake_underscores = try corex.toSnakeCase(std.testing.allocator, "___");
    defer std.testing.allocator.free(snake_underscores);
    try std.testing.expectEqualStrings("_", snake_underscores);

    const snake_empty = try corex.toSnakeCase(std.testing.allocator, "");
    defer std.testing.allocator.free(snake_empty);
    try std.testing.expectEqualStrings("_", snake_empty);

    const snake_acronym = try corex.toSnakeCase(std.testing.allocator, "parseHTTP2Response");
    defer std.testing.allocator.free(snake_acronym);
    try std.testing.expectEqualStrings("parse_http2_response", snake_acronym);

    const pascal_empty = try corex.toPascalCase(std.testing.allocator, "___");
    defer std.testing.allocator.free(pascal_empty);
    try std.testing.expectEqualStrings("T", pascal_empty);

    const pascal_all_caps = try corex.toPascalCase(std.testing.allocator, "A_B");
    defer std.testing.allocator.free(pascal_all_caps);
    try std.testing.expectEqualStrings("Ab", pascal_all_caps);

    const const_empty = try corex.toScreamingSnakeCase(std.testing.allocator, "___");
    defer std.testing.allocator.free(const_empty);
    try std.testing.expectEqualStrings("CONST_0", const_empty);

    // [3] Verify `is_casing_warning_enabled = false` and `interner = null` modes:
    const bad_casing_src = "badCamel Bad_Type BAD__CONST";
    var silent_buf = TokenBuffer.init(std.testing.allocator);
    defer silent_buf.deinit();
    var silent_sink = DiagnosticSink.init(std.testing.allocator);
    defer silent_sink.deinit();

    var silent_lexer = Lexer.initWithOptions(
        bad_casing_src,
        FileId.fromInt(0),
        &silent_buf,
        &silent_sink,
        null,
        .{ .is_casing_warning_enabled = false },
    );
    try silent_lexer.tokenize();
    try std.testing.expectEqual(@as(u32, 0), silent_sink.warning_count);
    try std.testing.expect(silent_buf.getToken(TokenIndex.fromInt(0)).flags.has_lexer_error);

    var no_intern_buf = TokenBuffer.init(std.testing.allocator);
    defer no_intern_buf.deinit();
    var no_intern_sink = DiagnosticSink.init(std.testing.allocator);
    defer no_intern_sink.deinit();

    try corex.tokenize(bad_casing_src, FileId.fromInt(0), &no_intern_buf, &no_intern_sink, null);
    try std.testing.expectEqual(@as(u32, 3), no_intern_sink.warning_count);
    try std.testing.expectEqual(@as(usize, 0), no_intern_sink.asSlice()[0].suggestions.len);
}

// ------------------ Numeric & Range Literals ------------------

test "test_lexer_numeric_literals_ranges_method_calls_and_e0103_errors" {
    // [1] Valid decimal, hex, binary, octal, float, range (`..`, `..=`), and method call (`10.max`):
    const valid_numbers =
        "0 42 1_000_000 0xdead_BEEF 0X00_FF 0b1010_0101 0B0 0o755 0O0_7 " ++
        "0.0 3.141_592 1e9 2E+10 5.5e-3 1_0.2_5E+1_0 0..10 0..=10 10.max(20) 99.";
    var valid_buf = TokenBuffer.init(std.testing.allocator);
    defer valid_buf.deinit();
    var valid_sink = DiagnosticSink.init(std.testing.allocator);
    defer valid_sink.deinit();

    try corex.tokenize(valid_numbers, FileId.fromInt(0), &valid_buf, &valid_sink, null);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.warning_count);
    try expectLosslessRoundTrip(valid_numbers, &valid_buf);

    // Verify trailing `99.` at end of file produces `.int_lit` followed by `.dot`:
    const count = valid_buf.countTokens();
    try std.testing.expectEqual(TokenKind.int_lit, valid_buf.getToken(TokenIndex.fromInt(@intCast(count - 3))).kind);
    try std.testing.expectEqual(TokenKind.dot, valid_buf.getToken(TokenIndex.fromInt(@intCast(count - 2))).kind);

    // Verify `DR-21` nested tuple projections (`tup.0.1.2`) vs range float (`0..0.5`):
    const tuple_proj_src = "tup.0.1.2 0..0.5";
    var tuple_buf = TokenBuffer.init(std.testing.allocator);
    defer tuple_buf.deinit();
    var tuple_sink = DiagnosticSink.init(std.testing.allocator);
    defer tuple_sink.deinit();
    try corex.tokenize(tuple_proj_src, FileId.fromInt(0), &tuple_buf, &tuple_sink, null);
    try std.testing.expectEqual(@as(u32, 0), tuple_sink.error_count);
    try std.testing.expectEqual(@as(usize, 11), tuple_buf.countTokens());
    try std.testing.expectEqual(TokenKind.ident, tuple_buf.getToken(TokenIndex.fromInt(0)).kind);
    try std.testing.expectEqual(TokenKind.dot, tuple_buf.getToken(TokenIndex.fromInt(1)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, tuple_buf.getToken(TokenIndex.fromInt(2)).kind);
    try std.testing.expectEqual(TokenKind.dot, tuple_buf.getToken(TokenIndex.fromInt(3)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, tuple_buf.getToken(TokenIndex.fromInt(4)).kind);
    try std.testing.expectEqual(TokenKind.dot, tuple_buf.getToken(TokenIndex.fromInt(5)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, tuple_buf.getToken(TokenIndex.fromInt(6)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, tuple_buf.getToken(TokenIndex.fromInt(7)).kind);
    try std.testing.expectEqual(TokenKind.dotdot, tuple_buf.getToken(TokenIndex.fromInt(8)).kind);
    try std.testing.expectEqual(TokenKind.float_lit, tuple_buf.getToken(TokenIndex.fromInt(9)).kind);
    try expectLosslessRoundTrip(tuple_proj_src, &tuple_buf);

    // [2] Exhaustive malformed numeric literals emitting `E0103`:
    const malformed_numbers = [_][]const u8{
        "0x",      "0X",      "0b",     "0B",       "0o",     "0O",
        "0x_1",    "0x1_",    "0x1__2", "0x1g",     "0b102",  "0o78",
        "1__2",    "123_",    "1.2__3", "1.2_",     "1.0e",   "1.0e+",
        "1.0e-",   "1.0e_2",  "1.0e2_", "1.0e2__3", "123abc", "0b10_f32",
        "1.5_u64", "42__u64",
    };
    for (malformed_numbers) |bad_num| {
        var num_buf = TokenBuffer.init(std.testing.allocator);
        defer num_buf.deinit();
        var num_sink = DiagnosticSink.init(std.testing.allocator);
        defer num_sink.deinit();

        try corex.tokenize(bad_num, FileId.fromInt(0), &num_buf, &num_sink, null);
        try std.testing.expectEqual(@as(u32, 1), num_sink.error_count);
        try std.testing.expectEqual(DiagnosticCode.e0103_invalid_numeric_literal, num_sink.asSlice()[0].code);
        try std.testing.expect(num_buf.getToken(TokenIndex.fromInt(0)).flags.has_lexer_error);
        try expectLosslessRoundTrip(bad_num, &num_buf);
    }
}

// ----------------- Strings, Escapes & Interp ------------------

test "test_lexer_strings_escapes_w0101_e0101_e0102_and_nested_interpolation" {
    // [1] Valid escapes (`\n`, `\r`, `\t`, `\\`, `\0`, `\"`, `{{`, `}}`, `\x7F`, `\u{10FFFF}`) and interpolation:
    const valid_str =
        "\"\\n\\r\\t\\\\\\0\\\"{{}}\\x7F\\u{0}\\u{10FFFF} " ++
        "{if ok { \"nested {r#\"raw } str\"#} {'}'} /* }} */ // }}\n\" } else { \"fallback\" }}\"";
    var valid_buf = TokenBuffer.init(std.testing.allocator);
    defer valid_buf.deinit();
    var valid_sink = DiagnosticSink.init(std.testing.allocator);
    defer valid_sink.deinit();

    try corex.tokenize(valid_str, FileId.fromInt(0), &valid_buf, &valid_sink, null);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.warning_count);
    try std.testing.expectEqual(@as(usize, 2), valid_buf.countTokens());
    try std.testing.expectEqual(TokenKind.string_lit, valid_buf.getToken(TokenIndex.fromInt(0)).kind);
    try expectLosslessRoundTrip(valid_str, &valid_buf);

    // [2] Redundant escape `W0101` (`\'`, `\a`, `\é`) and `TransactionalPatcher` auto-fix:
    const redundant_src = "\"\\'\\a\\é\" '\\\"'";
    var red_buf = TokenBuffer.init(std.testing.allocator);
    defer red_buf.deinit();
    var red_sink = DiagnosticSink.init(std.testing.allocator);
    defer red_sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try corex.tokenize(redundant_src, FileId.fromInt(0), &red_buf, &red_sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), red_sink.error_count);
    try std.testing.expectEqual(@as(u32, 4), red_sink.warning_count);

    var fixes: [4]SuggestedFix = undefined;
    for (red_sink.asSlice(), 0..) |diag_item, i| {
        try std.testing.expectEqual(DiagnosticCode.w0101_redundant_escape_sequence, diag_item.code);
        fixes[i] = diag_item.suggestions[0];
    }
    const patched = try TransactionalPatcher.apply(
        std.testing.allocator,
        redundant_src,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patched.patched_source);
    try std.testing.expectEqual(@as(u32, 4), patched.applied_count);
    try std.testing.expectEqualStrings("\"'aé\" '\"'", patched.patched_source);

    // Verify `is_escape_warning_enabled = false` and `interner = null` on redundant escapes:
    var no_warn_buf = TokenBuffer.init(std.testing.allocator);
    defer no_warn_buf.deinit();
    var no_warn_sink = DiagnosticSink.init(std.testing.allocator);
    defer no_warn_sink.deinit();
    var no_warn_lexer = Lexer.initWithOptions(
        redundant_src,
        FileId.fromInt(0),
        &no_warn_buf,
        &no_warn_sink,
        null,
        .{ .is_escape_warning_enabled = false },
    );
    try no_warn_lexer.tokenize();
    try std.testing.expectEqual(@as(u32, 0), no_warn_sink.warning_count);

    var no_intern_buf = TokenBuffer.init(std.testing.allocator);
    defer no_intern_buf.deinit();
    var no_intern_sink = DiagnosticSink.init(std.testing.allocator);
    defer no_intern_sink.deinit();
    try corex.tokenize(redundant_src, FileId.fromInt(0), &no_intern_buf, &no_intern_sink, null);
    try std.testing.expectEqual(@as(u32, 4), no_intern_sink.warning_count);
    try std.testing.expectEqual(@as(usize, 0), no_intern_sink.asSlice()[0].suggestions.len);

    // [3] Invalid `\x` / `\u{…}` escapes and raw invalid UTF-8 inside strings (`E0101`) + unclosed (`E0102`):
    const invalid_escapes = [_][]const u8{
        "\"\\x\"",
        "\"\\x1\"",
        "\"\\xGG\"",
        "\"\\u\"",
        "\"\\u1234\"",
        "\"\\u{}\"",
        "\"\\u{1234567}\"",
        "\"\\u{D800}\"",
        "\"\\u{110000}\"",
        "\"\\u{ZZZZ}\"",
        "\"\\u{123\"",
        "\"\xFF\"",
        "\"{\xFF}\"",
    };
    for (invalid_escapes) |bad_str| {
        var str_buf = TokenBuffer.init(std.testing.allocator);
        defer str_buf.deinit();
        var str_sink = DiagnosticSink.init(std.testing.allocator);
        defer str_sink.deinit();

        try corex.tokenize(bad_str, FileId.fromInt(0), &str_buf, &str_sink, null);
        try std.testing.expect(str_sink.error_count >= 1);
        try std.testing.expectEqual(DiagnosticCode.e0101_invalid_utf8_sequence, str_sink.asSlice()[0].code);
        try expectLosslessRoundTrip(bad_str, &str_buf);
    }

    const unclosed_strings = [_][]const u8{
        "\"unterminated",
        "\"trailing backslash \\",
        "\"unclosed interp { 1 + 2",
    };
    for (unclosed_strings) |unclosed_str| {
        var str_buf = TokenBuffer.init(std.testing.allocator);
        defer str_buf.deinit();
        var str_sink = DiagnosticSink.init(std.testing.allocator);
        defer str_sink.deinit();

        try corex.tokenize(unclosed_str, FileId.fromInt(0), &str_buf, &str_sink, null);
        try std.testing.expectEqual(@as(u32, 1), str_sink.error_count);
        try std.testing.expectEqual(DiagnosticCode.e0102_unterminated_string_literal, str_sink.asSlice()[0].code);
        try expectLosslessRoundTrip(unclosed_str, &str_buf);
    }
}

// ---------------- Raw Strings & Char Literals -----------------

test "test_lexer_raw_strings_char_literals_and_directives" {
    // [1] Valid raw strings (`r"…"`, `r#"…"#`, multi-line) and multi-byte UTF-8 character literals:
    const valid_raw_and_chars =
        "r\"raw \\n {no_interp}\" r#\"inner \" quote\"# r##\"multi #\"# line\r\nstr\"## " ++
        "'a' 'é' '─' '𐍈' '\\n' '\\'' '\\x41' '\\u{03B1}' #soa";
    var valid_buf = TokenBuffer.init(std.testing.allocator);
    defer valid_buf.deinit();
    var valid_sink = DiagnosticSink.init(std.testing.allocator);
    defer valid_sink.deinit();

    try corex.tokenize(valid_raw_and_chars, FileId.fromInt(0), &valid_buf, &valid_sink, null);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.warning_count);
    try expectLosslessRoundTrip(valid_raw_and_chars, &valid_buf);

    // [2] Malformed raw strings (`r#`, `r#ident`, unclosed `r#"…"`, `> 255` `#` delimiters):
    var over_255_hashes: [520]u8 = undefined;
    over_255_hashes[0] = 'r';
    @memset(over_255_hashes[1..257], '#');
    over_255_hashes[257] = '"';
    over_255_hashes[258] = 'a';
    over_255_hashes[259] = '"';
    @memset(over_255_hashes[260..516], '#');

    const bad_raw_cases = [_][]const u8{
        "r#",
        "r#ident",
        "r\"unclosed",
        "r##\"mismatched\"#",
        over_255_hashes[0..516],
    };
    for (bad_raw_cases) |bad_raw| {
        var raw_buf = TokenBuffer.init(std.testing.allocator);
        defer raw_buf.deinit();
        var raw_sink = DiagnosticSink.init(std.testing.allocator);
        defer raw_sink.deinit();

        try corex.tokenize(bad_raw, FileId.fromInt(0), &raw_buf, &raw_sink, null);
        try std.testing.expectEqual(@as(u32, 1), raw_sink.error_count);
        try std.testing.expectEqual(DiagnosticCode.e0102_unterminated_string_literal, raw_sink.asSlice()[0].code);
        try expectLosslessRoundTrip(bad_raw, &raw_buf);
    }

    // Raw string with invalid UTF-8 emits `E0101`:
    const raw_bad_utf8 = "r\"\xFF\"";
    var raw_utf8_buf = TokenBuffer.init(std.testing.allocator);
    defer raw_utf8_buf.deinit();
    var raw_utf8_sink = DiagnosticSink.init(std.testing.allocator);
    defer raw_utf8_sink.deinit();
    try corex.tokenize(raw_bad_utf8, FileId.fromInt(0), &raw_utf8_buf, &raw_utf8_sink, null);
    try std.testing.expectEqual(@as(u32, 1), raw_utf8_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0101_invalid_utf8_sequence, raw_utf8_sink.asSlice()[0].code);

    // [3] Malformed character literals (`''`, `'ab'`, `'a`, `'a\n`, `'\xFF'`) and `#` directives:
    const bad_char_cases = [_][]const u8{ "''", "'ab'", "'a", "'a\n", "'\\\r\n'" };
    for (bad_char_cases) |bad_char| {
        var char_buf = TokenBuffer.init(std.testing.allocator);
        defer char_buf.deinit();
        var char_sink = DiagnosticSink.init(std.testing.allocator);
        defer char_sink.deinit();

        try corex.tokenize(bad_char, FileId.fromInt(0), &char_buf, &char_sink, null);
        try std.testing.expect(char_sink.error_count >= 1);
        try std.testing.expectEqual(DiagnosticCode.e0102_unterminated_string_literal, char_sink.asSlice()[0].code);
        try expectLosslessRoundTrip(bad_char, &char_buf);
    }

    const unexpected_tokens = "#unknown #soa_extra # ` λ \xFF\xFE";
    var unexp_buf = TokenBuffer.init(std.testing.allocator);
    defer unexp_buf.deinit();
    var unexp_sink = DiagnosticSink.init(std.testing.allocator);
    defer unexp_sink.deinit();

    try corex.tokenize(unexpected_tokens, FileId.fromInt(0), &unexp_buf, &unexp_sink, null);
    try std.testing.expectEqual(@as(u32, 6), unexp_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0201_unexpected_token, unexp_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0201_unexpected_token, unexp_sink.asSlice()[4].code);
    try std.testing.expectEqual(DiagnosticCode.e0101_invalid_utf8_sequence, unexp_sink.asSlice()[5].code);
    try expectLosslessRoundTrip(unexpected_tokens, &unexp_buf);
}

// ----------------- Resource Caps & Round-Trip -----------------

test "test_lexer_trivia_carrier_flush_slot14_coalescing_and_e0104_limit" {
    // [1] > 15 distinct trivia pieces before a token coalesce into slot 14 losslessly:
    const many_trivia_src = " \t \t \t \t \t \t \t \t \t \t \t \tlet val = 1;";
    var many_buf = TokenBuffer.init(std.testing.allocator);
    defer many_buf.deinit();
    var many_sink = DiagnosticSink.init(std.testing.allocator);
    defer many_sink.deinit();

    try corex.tokenize(many_trivia_src, FileId.fromInt(0), &many_buf, &many_sink, null);
    try std.testing.expectEqual(@as(u32, 0), many_sink.error_count);
    try std.testing.expectEqual(@as(usize, 15), many_buf.getLeadingTrivia(TokenIndex.fromInt(0)).len);
    try expectLosslessRoundTrip(many_trivia_src, &many_buf);

    // [2] > 983,025 bytes of contiguous leading trivia flushes a synthesized `.invalid_token` carrier:
    const carrier_len: usize = lexer.MAX_TRIVIA_BYTES_PER_TOKEN + 128;
    const carrier_source = try std.testing.allocator.alloc(u8, carrier_len + 10);
    defer std.testing.allocator.free(carrier_source);
    @memset(carrier_source[0..carrier_len], ' ');
    @memcpy(carrier_source[carrier_len..], "let x = 1;");

    var carrier_buf = TokenBuffer.init(std.testing.allocator);
    defer carrier_buf.deinit();
    var carrier_sink = DiagnosticSink.init(std.testing.allocator);
    defer carrier_sink.deinit();

    try corex.tokenize(carrier_source, FileId.fromInt(0), &carrier_buf, &carrier_sink, null);
    try std.testing.expectEqual(@as(u32, 0), carrier_sink.error_count);
    const first_carrier = carrier_buf.getToken(TokenIndex.fromInt(0));
    try std.testing.expectEqual(TokenKind.invalid_token, first_carrier.kind);
    try std.testing.expect(first_carrier.flags.is_synthesized);
    try std.testing.expectEqual(@as(u16, 0), first_carrier.byte_len);
    try expectLosslessRoundTrip(carrier_source, &carrier_buf);

    // [3] Carrier trivia when `max_tokens = 1` defers directly to `E0104` tail preservation:
    var capped_carrier_buf = TokenBuffer.init(std.testing.allocator);
    defer capped_carrier_buf.deinit();
    var capped_carrier_sink = DiagnosticSink.init(std.testing.allocator);
    defer capped_carrier_sink.deinit();
    var capped_lexer = Lexer.initWithOptions(
        carrier_source,
        FileId.fromInt(0),
        &capped_carrier_buf,
        &capped_carrier_sink,
        null,
        .{ .max_tokens = 1 },
    );
    try capped_lexer.tokenize();
    try std.testing.expectEqual(@as(u32, 1), capped_carrier_sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0104_token_limit_exceeded,
        capped_carrier_sink.asSlice()[0].code,
    );
    try expectLosslessRoundTrip(carrier_source, &capped_carrier_buf);
}

// ------------- Retired :: Path Separator (E0112) --------------

test "test_lexer_retired_colon_colon_emits_e0112_with_dot_fix" {
    const retired_src = "use cx::mem::size_of;";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try corex.tokenize(retired_src, FileId.fromInt(0), &token_buf, &sink, &interner);
    try std.testing.expectEqual(@as(u32, 2), sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0112_retired_path_separator, sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0112_retired_path_separator, sink.asSlice()[1].code);
    try std.testing.expectEqual(TokenKind.dot, token_buf.getToken(TokenIndex.fromInt(2)).kind);
    try std.testing.expect(token_buf.getToken(TokenIndex.fromInt(2)).flags.has_lexer_error);
    try expectLosslessRoundTrip(retired_src, &token_buf);

    var fixes: [2]SuggestedFix = .{ sink.asSlice()[0].suggestions[0], sink.asSlice()[1].suggestions[0] };
    const patched = try TransactionalPatcher.apply(
        std.testing.allocator,
        retired_src,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patched.patched_source);
    try std.testing.expectEqual(@as(u32, 2), patched.applied_count);
    try std.testing.expectEqualStrings("use cx.mem.size_of;", patched.patched_source);
}

test "test_lexer_tuple_index_after_dot_rejects_suffixes_hex_and_underscores" {
    // [1] Valid decimal tuple indices (`tup.0`, `tup.12`) scan cleanly without errors:
    const valid_src = "let val = tup.0 + tup.12;";
    var valid_buf = TokenBuffer.init(std.testing.allocator);
    defer valid_buf.deinit();
    var valid_sink = DiagnosticSink.init(std.testing.allocator);
    defer valid_sink.deinit();
    try corex.tokenize(valid_src, FileId.fromInt(0), &valid_buf, &valid_sink, null);
    try std.testing.expectEqual(@as(u32, 0), valid_sink.error_count);
    try expectLosslessRoundTrip(valid_src, &valid_buf);

    // [2] Suffixed, exponent, hex, and underscored tuple indices emit `E0103`:
    const invalid_cases = [_][]const u8{
        "tup.0u32",
        "tup.0e5",
        "tup.0e+5",
        "tup.0x0",
        "tup.0_0",
    };
    for (invalid_cases) |bad_src| {
        var bad_buf = TokenBuffer.init(std.testing.allocator);
        defer bad_buf.deinit();
        var bad_sink = DiagnosticSink.init(std.testing.allocator);
        defer bad_sink.deinit();

        try corex.tokenize(bad_src, FileId.fromInt(0), &bad_buf, &bad_sink, null);
        try std.testing.expect(bad_sink.error_count >= 1);
        try std.testing.expectEqual(
            DiagnosticCode.e0103_invalid_numeric_literal,
            bad_sink.asSlice()[0].code,
        );
        try std.testing.expect(bad_buf.getToken(TokenIndex.fromInt(2)).flags.has_lexer_error);
        try expectLosslessRoundTrip(bad_src, &bad_buf);
    }
}

// ------------- DR-22 Literals, Suffixes & Escapes -------------

test "test_lexer_dr22_retired_ampamp_brace_escapes_multiline_byte_literals_and_fmt_spec" {
    // [1] Retired `&&` (`E0113`) and `\{` / `\}` (`E0114`) with spacing-safe autofixes:
    const legacy_source = "let ok = flag_a && flag_b&&flag_c; let text = \"\\{k\\} = {{v}}\"; fn c_fn(fmt: *opaque, ...);";
    var legacy_buf = TokenBuffer.init(std.testing.allocator);
    defer legacy_buf.deinit();
    var legacy_sink = DiagnosticSink.init(std.testing.allocator);
    defer legacy_sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try corex.tokenize(legacy_source, FileId.fromInt(0), &legacy_buf, &legacy_sink, &interner);
    try std.testing.expectEqual(@as(u32, 4), legacy_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0113_retired_logical_and, legacy_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0113_retired_logical_and, legacy_sink.asSlice()[1].code);
    try std.testing.expectEqual(DiagnosticCode.e0114_invalid_brace_escape, legacy_sink.asSlice()[2].code);
    try std.testing.expectEqual(DiagnosticCode.e0114_invalid_brace_escape, legacy_sink.asSlice()[3].code);
    try std.testing.expectEqual(TokenKind.kw_and, legacy_buf.getToken(TokenIndex.fromInt(4)).kind);
    try std.testing.expectEqual(TokenKind.dotdotdot, legacy_buf.getToken(TokenIndex.fromInt(22)).kind);
    try expectLosslessRoundTrip(legacy_source, &legacy_buf);

    var fixes: [4]SuggestedFix = .{
        legacy_sink.asSlice()[0].suggestions[0],
        legacy_sink.asSlice()[1].suggestions[0],
        legacy_sink.asSlice()[2].suggestions[0],
        legacy_sink.asSlice()[3].suggestions[0],
    };
    const patch_res = try TransactionalPatcher.apply(
        std.testing.allocator,
        legacy_source,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 4), patch_res.applied_count);
    try std.testing.expectEqualStrings(
        "let ok = flag_a and flag_b and flag_c; let text = \"{{k}} = {{v}}\"; fn c_fn(fmt: *opaque, ...);",
        patch_res.patched_source,
    );

    // [2] Multiline `"""…"""`, `b'…'`, `b"…"`, and negative `E0115`, `E0116`, `E0117`:
    const multi_valid =
        \\let banner = """
        \\    outer {"inner"} and {
        \\        """
        \\        nested "quote"
        \\        """
        \\    }
        \\    """;
        \\let wire = b"HTTP/1.1\r\n\xFF";
        \\let sep = b'\r';
        \\let raw_bytes = br#"A"B"#;
    ;
    var multi_buf = TokenBuffer.init(std.testing.allocator);
    defer multi_buf.deinit();
    var multi_sink = DiagnosticSink.init(std.testing.allocator);
    defer multi_sink.deinit();
    try corex.tokenize(multi_valid, FileId.fromInt(0), &multi_buf, &multi_sink, null);
    try std.testing.expectEqual(@as(u32, 0), multi_sink.error_count);
    try std.testing.expectEqual(TokenKind.string_lit, multi_buf.getToken(TokenIndex.fromInt(3)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, multi_buf.getToken(TokenIndex.fromInt(8)).kind);
    try std.testing.expectEqual(TokenKind.byte_lit, multi_buf.getToken(TokenIndex.fromInt(13)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, multi_buf.getToken(TokenIndex.fromInt(18)).kind);
    try std.testing.expectEqual(@as(?u8, '\r'), lexer.extractByteLiteralValue("b'\\r'"));
    try std.testing.expectEqual(@as(?u8, 0xFF), lexer.extractByteLiteralValue("b'\\xFF'"));
    try expectLosslessRoundTrip(multi_valid, &multi_buf);

    const multi_err_src =
        "let e1 = \"\"\"bad\n\"\"\"; let e2 = \"\"\"\n  under\n    \"\"\"; let e3 = b'é'; let e4 = b\"\\u{41}\";";
    var multi_err_buf = TokenBuffer.init(std.testing.allocator);
    defer multi_err_buf.deinit();
    var multi_err_sink = DiagnosticSink.init(std.testing.allocator);
    defer multi_err_sink.deinit();
    try corex.tokenize(multi_err_src, FileId.fromInt(0), &multi_err_buf, &multi_err_sink, null);
    try std.testing.expectEqual(@as(u32, 4), multi_err_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0115_multiline_string_opening, multi_err_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0116_multiline_string_indent, multi_err_sink.asSlice()[1].code);
    try std.testing.expectEqual(DiagnosticCode.e0117_non_ascii_byte_literal, multi_err_sink.asSlice()[2].code);
    try std.testing.expectEqual(DiagnosticCode.e0117_non_ascii_byte_literal, multi_err_sink.asSlice()[3].code);
    try expectLosslessRoundTrip(multi_err_src, &multi_err_buf);

    // [3] Numeric suffixes (`42_u64`, `0.5_f32`, `0x1f32`) and 8-byte `FmtSpec`:
    const suffix_src = "42_u64 42u64 0x4358_574C_u32 0b1010_i8 0o77_usize 10_f32 0.5_f32 1e-3f64 0x1f32";
    var suffix_buf = TokenBuffer.init(std.testing.allocator);
    defer suffix_buf.deinit();
    var suffix_sink = DiagnosticSink.init(std.testing.allocator);
    defer suffix_sink.deinit();
    try corex.tokenize(suffix_src, FileId.fromInt(0), &suffix_buf, &suffix_sink, null);
    try std.testing.expectEqual(@as(u32, 0), suffix_sink.error_count);
    try expectLosslessRoundTrip(suffix_src, &suffix_buf);

    const parsed_hex = try lexer.extractNumericSuffix("0x4358_574C_u32");
    try std.testing.expectEqualStrings("0x4358_574C", parsed_hex.digits_slice);
    try std.testing.expectEqual(@as(?corex.TypeId, .u32_ty), parsed_hex.suffix_type);
    try std.testing.expect(parsed_hex.has_underscore_sep);
    try std.testing.expectEqual(@as(?corex.TypeId, null), (try lexer.extractNumericSuffix("0x1f32")).suffix_type);

    try std.testing.expectEqual(@as(usize, 8), @sizeOf(lexer.FmtSpec));
    const hex_spec = try lexer.parseFormatSpec("#010x", true);
    try std.testing.expect(hex_spec.hasAltFlag());
    try std.testing.expect(hex_spec.hasZeroPad());
    try std.testing.expect(hex_spec.hasDebugEq());
    try std.testing.expectEqual(@as(?u16, 10), hex_spec.extractWidth());
    try std.testing.expectEqual(lexer.FmtTypeCode.lower_hex, hex_spec.extractTypeCode());

    // [4] Unmatched closing `}` in interpolated strings emits `E0114` with `"}}"` fix (`SE-12`):
    const lone_close_src = "let bad = \"hello } world\";";
    var lone_buf = TokenBuffer.init(std.testing.allocator);
    defer lone_buf.deinit();
    var lone_sink = DiagnosticSink.init(std.testing.allocator);
    defer lone_sink.deinit();
    var lone_intern = try corex.StringInterner.init(std.testing.allocator);
    defer lone_intern.deinit();
    try corex.tokenize(lone_close_src, FileId.fromInt(0), &lone_buf, &lone_sink, &lone_intern);
    try std.testing.expectEqual(@as(u32, 1), lone_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0114_invalid_brace_escape, lone_sink.asSlice()[0].code);
    try std.testing.expectEqual(@as(usize, 1), lone_sink.asSlice()[0].suggestions.len);
    try std.testing.expectEqualStrings(
        "}}",
        lone_intern.get(lone_sink.asSlice()[0].suggestions[0].edits[0].replacement_id),
    );
    try expectLosslessRoundTrip(lone_close_src, &lone_buf);
    try std.testing.expectError(error.InvalidStringLiteral, lexer.cookStringLiteral(std.testing.allocator, "\"a}b\""));
    const decoded_braces = try lexer.cookStringLiteral(std.testing.allocator, "\"{{ok}}\"");
    defer std.testing.allocator.free(decoded_braces);
    try std.testing.expectEqualStrings("{ok}", decoded_braces);
}

// ---------- Phase 10.6 (DR-23) Block Doc Diagnostics ----------

test "test_lexer_dr23_block_doc_comments_e0118_and_four_slash_banners" {
    // [1] Empty `/**/`, non-doc `/***/`, nested `/* … */`, and `////`+ banners emit zero errors (`ADR-23A`):
    const valid_comments_src =
        "//! Module header doc\n" ++
        "/**/ /***/ /* outer /* inner */ comment */\n" ++
        "//// Four-slash banner comment\n" ++
        "///// Five-slash banner comment\n" ++
        "/// Exact three-slash item doc\n" ++
        "pub const LIMIT: u32 = 16;\n";

    var ok_buf = TokenBuffer.init(std.testing.allocator);
    defer ok_buf.deinit();
    var ok_sink = DiagnosticSink.init(std.testing.allocator);
    defer ok_sink.deinit();

    try corex.tokenize(valid_comments_src, FileId.fromInt(0), &ok_buf, &ok_sink, null);
    try std.testing.expectEqual(@as(u32, 0), ok_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), ok_sink.warning_count);
    try expectLosslessRoundTrip(valid_comments_src, &ok_buf);

    var doc_count: usize = 0;
    var mod_doc_count: usize = 0;
    var line_cmt_count: usize = 0;
    var block_cmt_count: usize = 0;
    for (ok_buf.getLeadingTrivia(TokenIndex.fromInt(0))) |piece| {
        switch (piece.kind) {
            .doc_comment => doc_count += 1,
            .module_doc_comment => mod_doc_count += 1,
            .line_comment => line_cmt_count += 1,
            .block_comment => block_cmt_count += 1,
            else => {},
        }
    }
    try std.testing.expectEqual(@as(usize, 1), mod_doc_count);
    try std.testing.expectEqual(@as(usize, 1), doc_count);
    try std.testing.expectEqual(@as(usize, 2), line_cmt_count);
    try std.testing.expectEqual(@as(usize, 3), block_cmt_count);

    // [2] Banned `/** … */` and `/*! … */` block doc comments emit `E0118` with auto-fix suggestions:
    const banned_block_doc_cases = [_][]const u8{
        "/** Single-line outer block doc */\npub fn ping() -> u32 = 1;\n",
        "/**\n * Multiline outer block doc\n * with aligned star border.\n */\npub struct Slot { pub id: u32 }\n",
        "/*! Inner block module doc */\npub const SEED: u32 = 7;\n",
    };
    for (banned_block_doc_cases) |bad_src| {
        var bad_buf = TokenBuffer.init(std.testing.allocator);
        defer bad_buf.deinit();
        var bad_sink = DiagnosticSink.init(std.testing.allocator);
        defer bad_sink.deinit();
        var interner = try StringInterner.init(std.testing.allocator);
        defer interner.deinit();

        try corex.tokenize(bad_src, FileId.fromInt(0), &bad_buf, &bad_sink, &interner);
        try std.testing.expectEqual(@as(u32, 1), bad_sink.error_count);
        try std.testing.expectEqual(
            DiagnosticCode.e0118_block_doc_comment_forbidden,
            bad_sink.asSlice()[0].code,
        );
        try std.testing.expect(bad_sink.asSlice()[0].suggestions.len >= 1);
        try expectLosslessRoundTrip(bad_src, &bad_buf);
    }
}

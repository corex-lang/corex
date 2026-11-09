//! High-Speed Deterministic Lexer & Lossless Trivia Scanner
//!
//! Scans UTF-8 source buffers into a contiguous Structure-of-Arrays (SoA) `TokenBuffer` in a single
//! non-backtracking $O(N)$ linear pass while enforcing the `DR-03` 112-token lexical taxonomy.
//!
//! Preserves 100% of source bytes across leading/trailing `TriviaPiece` slices (`<= 65,535`-byte chunking,
//! slot-14 coalescing, carrier token flushing past `983,025` trivia bytes, and `E0104` tail preservation)
//! so `LosslessCstArena.reconstructSource` reproduces any input byte-for-bit.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");

const FileId = mem_foundation.FileId;
const Span = mem_foundation.Span;
const StringInterner = mem_foundation.StringInterner;
const TokenIndex = mem_foundation.TokenIndex;
const TokenKind = syntax_arenas.TokenKind;
const TokenFlags = syntax_arenas.TokenFlags;
const TriviaKind = syntax_arenas.TriviaKind;
const TriviaPiece = syntax_arenas.TriviaPiece;
const TokenBuffer = syntax_arenas.TokenBuffer;
const DiagnosticCode = diagnostic.DiagnosticCode;
const DiagnosticSink = diagnostic.DiagnosticSink;
const LabeledSpan = diagnostic.LabeledSpan;
const SuggestedFix = diagnostic.SuggestedFix;
const TextEdit = diagnostic.TextEdit;

// ---------------------------------------- TYPES ----------------------------------------

// --------------------- Identifier Casing ----------------------

/// Canonical CoreX orthographic casing category (`DR-03` Section 4.3).
pub const IdentifierCase = enum(u8) {
    /// Lowercase `snake_case` value, function, method, field, or module identifier (`ident`).
    snake_case = 0,
    /// Uppercase-initial `PascalCase` type, trait, enum variant, or type parameter (`type_ident`).
    pascal_case = 1,
    /// All-uppercase `SCREAMING_SNAKE_CASE` compile-time constant identifier (`const_ident`).
    screaming_snake_case = 2,
    /// Reserved language keyword, primitive type keyword, or standalone `_` wildcard.
    reserved_or_wildcard = 3,

    /// Alias for `.snake_case`.
    pub const snake: IdentifierCase = .snake_case;
    /// Alias for `.pascal_case`.
    pub const pascal: IdentifierCase = .pascal_case;
    /// Alias for `.screaming_snake_case`.
    pub const screaming_snake: IdentifierCase = .screaming_snake_case;
    /// Alias for `.reserved_or_wildcard`.
    pub const none: IdentifierCase = .reserved_or_wildcard;
};

/// Result of classifying a raw identifier or keyword lexeme under the `DR-03` disjoint casing invariant.
pub const IdentifierClassification = struct {
    /// Resolved `TokenKind` (`.kw_*`, `.prim_type`, `.underscore`, `.ident`, `.type_ident`, `.const_ident`).
    kind: TokenKind,
    /// Canonical casing style required for this identifier class.
    expected_case: IdentifierCase,
    /// Alias field matching `expected_case` for caller ergonomics.
    case_style: IdentifierCase,
    /// `true` if `lexeme` strictly satisfies the canonical casing pattern for `kind`.
    is_canonical: bool,
    /// `true` if `lexeme` violates internal casing rules and requires a `W0201` diagnostic.
    has_case_violation: bool,
};

// -------------------- Lexer Configuration ---------------------

/// Configurable resource caps and lint toggles for `Lexer`.
pub const LexerOptions = struct {
    /// Maximum number of tokens (including `.eof`) permitted before emitting `E0104`.
    max_tokens: usize = syntax_arenas.MAX_TOKENS_PER_FILE,
    /// Whether to emit `W0201` warnings on non-canonical identifier casing.
    is_casing_warning_enabled: bool = true,
    /// Whether to emit `W0101` warnings on redundant character/string escape sequences.
    is_escape_warning_enabled: bool = true,
};

// --------------------- Trivia Accumulator ---------------------

/// Bounded 15-slot accumulator packing inter-token trivia into `PackedTriviaSpan` (`u4` count).
pub const TriviaAccumulator = struct {
    /// Fixed 15-slot buffer matching `PackedTriviaSpan.leading_count` (`u4` = `0..15`).
    pieces: [MAX_TRIVIA_SLOTS]TriviaPiece = undefined,
    /// Number of active trivia slots currently populated (`0..15`).
    count: u8 = 0,
    /// `true` if at least one `\n` or `\r` line break was accumulated since the previous token.
    has_newline: bool = false,

    /// Resets the accumulator for the next token.
    pub inline fn reset(self: *TriviaAccumulator) void {
        self.count = 0;
        self.has_newline = false;
    }

    /// Returns the active slice of accumulated `TriviaPiece` records (`0..15`).
    pub inline fn asSlice(self: *const TriviaAccumulator) []const TriviaPiece {
        return self.pieces[0..self.count];
    }

    /// Returns `true` if all 15 slots are occupied and every slot has reached `65,535` bytes (`983,025` B).
    pub inline fn isCompletelyFull(self: *const TriviaAccumulator) bool {
        if (self.count < MAX_TRIVIA_SLOTS) return false;
        return self.pieces[MAX_TRIVIA_SLOTS - 1].byte_len == MAX_TRIVIA_PIECE_BYTES and
            !self.hasCompactableEarlierSlots();
    }

    /// Returns `true` if any adjacent pair in `pieces[0..14]` can absorb additional bytes.
    fn hasCompactableEarlierSlots(self: *const TriviaAccumulator) bool {
        if (self.count < 2) return false;
        var i: usize = 0;
        const limit: usize = @min(@as(usize, self.count) - 1, MAX_TRIVIA_SLOTS - 1);
        while (i < limit) : (i += 1) {
            if (self.pieces[i].byte_len < MAX_TRIVIA_PIECE_BYTES) {
                return true;
            }
        }
        return false;
    }

    /// Compacts adjacent slots in `pieces[0..15]` to free room in slot 14 while staying `<= 983,025` bytes.
    fn compactOneSlot(self: *TriviaAccumulator) bool {
        if (self.count < MAX_TRIVIA_SLOTS) return true;
        var i: usize = 0;
        while (i + 1 < MAX_TRIVIA_SLOTS) : (i += 1) {
            const first_len: usize = self.pieces[i].byte_len;
            if (first_len >= MAX_TRIVIA_PIECE_BYTES) continue;

            const second_len: usize = self.pieces[i + 1].byte_len;
            const room_in_first: usize = MAX_TRIVIA_PIECE_BYTES - first_len;
            if (second_len <= room_in_first) {
                // Merge `pieces[i + 1]` completely into `pieces[i]` and shift subsequent slots left:
                self.pieces[i].byte_len = @intCast(first_len + second_len);
                var j: usize = i + 1;
                while (j + 1 < MAX_TRIVIA_SLOTS) : (j += 1) {
                    self.pieces[j] = self.pieces[j + 1];
                }
                self.count -= 1;
                return true;
            } else {
                // Top up `pieces[i]` to 65,535 bytes by shifting bytes from `pieces[i + 1]`:
                const transfer_bytes: u16 = @intCast(room_in_first);
                self.pieces[i].byte_len = MAX_TRIVIA_PIECE_BYTES;
                self.pieces[i + 1].byte_offset += transfer_bytes;
                self.pieces[i + 1].byte_len -= transfer_bytes;
            }
        }
        return self.count < MAX_TRIVIA_SLOTS or
            self.pieces[MAX_TRIVIA_SLOTS - 1].byte_len < MAX_TRIVIA_PIECE_BYTES;
    }

    /// Appends up to `chunk_len` bytes (`<= 65,535`), returning the number of bytes accepted.
    pub fn pushChunk(
        self: *TriviaAccumulator,
        kind: TriviaKind,
        byte_offset: u32,
        chunk_len: u16,
    ) u16 {
        if (chunk_len == 0) return 0;

        // [1] Direct insertion into slots `0..14`:
        if (self.count < MAX_TRIVIA_SLOTS) {
            self.pieces[self.count] = .{
                .kind = kind,
                .flags = 0,
                .byte_len = chunk_len,
                .byte_offset = byte_offset,
            };
            self.count += 1;
            return chunk_len;
        }

        // [2] Slot-14 coalescing when all 15 slots are occupied:
        const slot14_len: usize = self.pieces[MAX_TRIVIA_SLOTS - 1].byte_len;
        const slot14_room: usize = MAX_TRIVIA_PIECE_BYTES - slot14_len;
        if (slot14_room > 0) {
            const accepted: u16 = @intCast(@min(@as(usize, chunk_len), slot14_room));
            self.pieces[MAX_TRIVIA_SLOTS - 1].byte_len += accepted;
            return accepted;
        }

        // [3] Compact earlier under-full slots so up to `983,025` bytes fit before carrier flush:
        if (self.compactOneSlot()) {
            return self.pushChunk(kind, byte_offset, chunk_len);
        }
        return 0;
    }
};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum number of `TriviaPiece` slots per token list (`u4` = `15`).
pub const MAX_TRIVIA_SLOTS: usize = std.math.maxInt(u4);
/// Maximum byte length of a single `TriviaPiece` (`u16` = `65,535`).
pub const MAX_TRIVIA_PIECE_BYTES: u16 = std.math.maxInt(u16);
/// Maximum leading trivia bytes attachable to a single token (`15 * 65,535 = 983,025` bytes).
pub const MAX_TRIVIA_BYTES_PER_TOKEN: usize = MAX_TRIVIA_SLOTS * @as(usize, MAX_TRIVIA_PIECE_BYTES);
/// Maximum number of `#` delimiters allowed on a raw string literal (`r###"…"###`).
pub const MAX_RAW_STRING_HASHES: usize = 255;

/// Character-class bitflag for ASCII whitespace (`' '`, `'\t'`, `'\n'`, `'\r'`).
const CLASS_WHITESPACE: u8 = 0x01;
/// Character-class bitflag for lowercase ASCII or underscore (`'a'..'z'`, `'_'`).
const CLASS_LOWER_OR_UNDERSCORE: u8 = 0x02;
/// Character-class bitflag for uppercase ASCII (`'A'..'Z'`).
const CLASS_UPPER: u8 = 0x04;
/// Character-class bitflag for decimal digits (`'0'..'9'`).
const CLASS_DEC_DIGIT: u8 = 0x08;
/// Character-class bitflag for hexadecimal digits (`'0'..'9'`, `'a'..'f'`, `'A'..'F'`).
const CLASS_HEX_DIGIT: u8 = 0x10;
/// Character-class bitflag for identifier continuation bytes (`'a'..'z'`, `'A'..'Z'`, `'0'..'9'`, `'_'`).
const CLASS_IDENT_CONTINUE: u8 = 0x20;
/// Character-class bitflag for octal digits (`'0'..'7'`).
const CLASS_OCT_DIGIT: u8 = 0x40;
/// Character-class bitflag for binary digits (`'0'..'1'`).
const CLASS_BIN_DIGIT: u8 = 0x80;

/// Static $O(1)$ 256-entry character classification lookup table (`AGENTS.md` Section 2).
pub const CHAR_CLASS_TABLE: [256]u8 = blk: {
    var table: [256]u8 = @splat(0);
    var byte_idx: usize = 0;
    while (byte_idx < 256) : (byte_idx += 1) {
        var mask: u8 = 0;
        if (byte_idx == ' ' or byte_idx == '\t' or byte_idx == '\n' or byte_idx == '\r') {
            mask |= CLASS_WHITESPACE;
        }
        if ((byte_idx >= 'a' and byte_idx <= 'z') or byte_idx == '_') {
            mask |= CLASS_LOWER_OR_UNDERSCORE | CLASS_IDENT_CONTINUE;
        }
        if (byte_idx >= 'A' and byte_idx <= 'Z') {
            mask |= CLASS_UPPER | CLASS_IDENT_CONTINUE;
        }
        if (byte_idx >= '0' and byte_idx <= '9') {
            mask |= CLASS_DEC_DIGIT | CLASS_HEX_DIGIT | CLASS_IDENT_CONTINUE;
        }
        if ((byte_idx >= 'a' and byte_idx <= 'f') or (byte_idx >= 'A' and byte_idx <= 'F')) {
            mask |= CLASS_HEX_DIGIT;
        }
        if (byte_idx >= '0' and byte_idx <= '7') {
            mask |= CLASS_OCT_DIGIT;
        }
        if (byte_idx == '0' or byte_idx == '1') {
            mask |= CLASS_BIN_DIGIT;
        }
        table[byte_idx] = mask;
    }
    break :blk table;
};

/// Authoritative compile-time lookup map for all 45 language keywords and 19 primitive types (`DR-03` §5.2).
pub const KEYWORD_OR_PRIM_MAP = std.StaticStringMap(TokenKind).initComptime(.{
    .{ "Self", .kw_self_type },
    .{ "and", .kw_and },
    .{ "as", .kw_as },
    .{ "async", .kw_async },
    .{ "await", .kw_await },
    .{ "bit_field", .kw_bit_field },
    .{ "bool", .prim_type },
    .{ "break", .kw_break },
    .{ "catch", .kw_catch },
    .{ "char", .prim_type },
    .{ "comptime", .kw_comptime },
    .{ "const", .kw_const },
    .{ "continue", .kw_continue },
    .{ "defer", .kw_defer },
    .{ "else", .kw_else },
    .{ "enum", .kw_enum },
    .{ "errdefer", .kw_errdefer },
    .{ "extern", .kw_extern },
    .{ "f32", .prim_type },
    .{ "f64", .prim_type },
    .{ "false", .kw_false },
    .{ "fn", .kw_fn },
    .{ "for", .kw_for },
    .{ "i128", .prim_type },
    .{ "i16", .prim_type },
    .{ "i32", .prim_type },
    .{ "i64", .prim_type },
    .{ "i8", .prim_type },
    .{ "if", .kw_if },
    .{ "impl", .kw_impl },
    .{ "in", .kw_in },
    .{ "is", .kw_is },
    .{ "isize", .prim_type },
    .{ "let", .kw_let },
    .{ "loop", .kw_loop },
    .{ "match", .kw_match },
    .{ "mod", .kw_mod },
    .{ "mut", .kw_mut },
    .{ "never", .prim_type },
    .{ "not", .kw_not },
    .{ "or", .kw_or },
    .{ "own", .kw_own },
    .{ "pub", .kw_pub },
    .{ "ref", .kw_ref },
    .{ "return", .kw_return },
    .{ "self", .kw_self_val },
    .{ "str", .prim_type },
    .{ "struct", .kw_struct },
    .{ "trait", .kw_trait },
    .{ "true", .kw_true },
    .{ "type", .kw_type },
    .{ "u128", .prim_type },
    .{ "u16", .prim_type },
    .{ "u32", .prim_type },
    .{ "u64", .prim_type },
    .{ "u8", .prim_type },
    .{ "union", .kw_union },
    .{ "unit", .prim_type },
    .{ "unsafe", .kw_unsafe },
    .{ "use", .kw_use },
    .{ "usize", .prim_type },
    .{ "var", .kw_var },
    .{ "where", .kw_where },
    .{ "while", .kw_while },
});

// -------------------------------------- INTERNALS --------------------------------------

// ------------------ Character Classification ------------------

/// Returns `true` if `byte_val` is `[a-zA-Z_]` in $O(1)$ table lookup time.
inline fn isIdentStart(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & (CLASS_LOWER_OR_UNDERSCORE | CLASS_UPPER)) != 0;
}

/// Returns `true` if `byte_val` is `[a-zA-Z0-9_]` in $O(1)$ table lookup time.
inline fn isIdentContinue(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_IDENT_CONTINUE) != 0;
}

/// Returns `true` if `byte_val` is `'A'..'Z'` in $O(1)$ table lookup time.
inline fn isAsciiUpper(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_UPPER) != 0;
}

/// Returns `true` if `byte_val` is `'a'..'z'` in $O(1)$ table lookup time.
inline fn isAsciiLower(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_LOWER_OR_UNDERSCORE) != 0 and byte_val != '_';
}

/// Returns `true` if `byte_val` is `'0'..'9'` in $O(1)$ table lookup time.
inline fn isDecimalDigit(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_DEC_DIGIT) != 0;
}

/// Returns `true` if `byte_val` is `[0-9a-fA-F]` in $O(1)$ table lookup time.
inline fn isHexDigit(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_HEX_DIGIT) != 0;
}

/// Returns `true` if `byte_val` is `'0'..'7'` in $O(1)$ table lookup time.
inline fn isOctalDigit(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_OCT_DIGIT) != 0;
}

/// Returns `true` if `byte_val` is `'0'` or `'1'` in $O(1)$ table lookup time.
inline fn isBinaryDigit(byte_val: u8) bool {
    return (CHAR_CLASS_TABLE[byte_val] & CLASS_BIN_DIGIT) != 0;
}

/// Returns `true` if `byte_val` is valid for integer `radix` (`2`, `8`, `10`, or `16`).
inline fn isValidDigitForRadix(byte_val: u8, radix: u8) bool {
    return switch (radix) {
        2 => isBinaryDigit(byte_val),
        8 => isOctalDigit(byte_val),
        10 => isDecimalDigit(byte_val),
        16 => isHexDigit(byte_val),
        else => false,
    };
}

/// Converts a single valid hexadecimal ASCII character into its 4-bit value (`0..15`).
inline fn hexDigitValue(byte_val: u8) u21 {
    if (byte_val >= '0' and byte_val <= '9') return byte_val - '0';
    if (byte_val >= 'a' and byte_val <= 'f') return 10 + (byte_val - 'a');
    return 10 + (byte_val - 'A');
}

// ------------------ Case Conversion Helpers -------------------

/// Returns `true` if a word boundary occurs immediately before `index` inside `trimmed_ident`.
fn isIdentifierWordBoundary(trimmed_ident: []const u8, index: usize) bool {
    if (index == 0 or index >= trimmed_ident.len) return false;
    const curr_byte = trimmed_ident[index];
    const prev_byte = trimmed_ident[index - 1];
    if (curr_byte == '_' or prev_byte == '_') return false;

    if (isAsciiUpper(curr_byte)) {
        if (isAsciiLower(prev_byte) or isDecimalDigit(prev_byte)) {
            return true;
        }
        if (isAsciiUpper(prev_byte) and index + 1 < trimmed_ident.len and isAsciiLower(trimmed_ident[index + 1])) {
            return true;
        }
    }
    return false;
}

comptime {
    std.debug.assert(KEYWORD_OR_PRIM_MAP.keys().len == 64);
}

// ------------------------------------- PUBLIC API --------------------------------------

// --------------------- Identifier Casing ----------------------

/// Looks up `lexeme` in the compile-time table of 45 language keywords and 19 primitive types.
pub inline fn lookupKeywordOrPrim(lexeme: []const u8) ?TokenKind {
    return KEYWORD_OR_PRIM_MAP.get(lexeme);
}

/// Classifies an identifier or keyword `lexeme` under the `DR-03` Section 5.2 disjoint casing invariant.
pub fn classifyIdentifierOrKeyword(lexeme: []const u8) IdentifierClassification {
    if (lexeme.len == 0 or !isIdentStart(lexeme[0])) {
        return .{
            .kind = .invalid_token,
            .expected_case = .reserved_or_wildcard,
            .case_style = .reserved_or_wildcard,
            .is_canonical = false,
            .has_case_violation = true,
        };
    }

    // [1] Standalone `_` wildcard token (`72`):
    if (lexeme.len == 1 and lexeme[0] == '_') {
        return .{
            .kind = .underscore,
            .expected_case = .reserved_or_wildcard,
            .case_style = .reserved_or_wildcard,
            .is_canonical = true,
            .has_case_violation = false,
        };
    }

    // [2] Reserved language keywords (`0..44`) and primitive types (`45`):
    if (lookupKeywordOrPrim(lexeme)) |keyword_or_prim_kind| {
        return .{
            .kind = keyword_or_prim_kind,
            .expected_case = .reserved_or_wildcard,
            .case_style = .reserved_or_wildcard,
            .is_canonical = true,
            .has_case_violation = false,
        };
    }

    // [3] Single-pass character class tally across `lexeme`:
    var upper_count: usize = 0;
    var has_lower = false;
    var has_underscore = false;
    var has_consecutive_underscores = false;
    var is_prev_underscore = false;

    for (lexeme) |byte_val| {
        if (!isIdentContinue(byte_val)) {
            return .{
                .kind = .invalid_token,
                .expected_case = .reserved_or_wildcard,
                .case_style = .reserved_or_wildcard,
                .is_canonical = false,
                .has_case_violation = true,
            };
        }
        if (isAsciiUpper(byte_val)) {
            upper_count += 1;
            is_prev_underscore = false;
        } else if (isAsciiLower(byte_val)) {
            has_lower = true;
            is_prev_underscore = false;
        } else if (byte_val == '_') {
            if (is_prev_underscore) {
                has_consecutive_underscores = true;
            }
            has_underscore = true;
            is_prev_underscore = true;
        } else {
            is_prev_underscore = false;
        }
    }

    // [4] Lowercase or leading-underscore identifiers (`len >= 2`) always classify as `.ident` (`46`):
    if (!isAsciiUpper(lexeme[0])) {
        const is_valid_snake = (upper_count == 0) and !has_consecutive_underscores;
        return .{
            .kind = .ident,
            .expected_case = .snake_case,
            .case_style = .snake_case,
            .is_canonical = is_valid_snake,
            .has_case_violation = !is_valid_snake,
        };
    }

    // [5] Uppercase-initial with lowercase or single capital without `_` (`T`, `V4`) -> `.type_ident` (`47`):
    if (has_lower or (upper_count == 1 and !has_underscore)) {
        const is_valid_pascal = !has_underscore;
        return .{
            .kind = .type_ident,
            .expected_case = .pascal_case,
            .case_style = .pascal_case,
            .is_canonical = is_valid_pascal,
            .has_case_violation = !is_valid_pascal,
        };
    }

    // [6] All-caps with `upper_count >= 2` or `_` (`MAX_SIZE`, `PI_2`, `IO`) -> `.const_ident` (`48`):
    const is_valid_const = !has_consecutive_underscores and (lexeme[lexeme.len - 1] != '_');
    return .{
        .kind = .const_ident,
        .expected_case = .screaming_snake_case,
        .case_style = .screaming_snake_case,
        .is_canonical = is_valid_const,
        .has_case_violation = !is_valid_const,
    };
}

/// Converts `raw_ident` into canonical `snake_case` (preserving at most one leading `_` prefix).
pub fn toSnakeCase(allocator: std.mem.Allocator, raw_ident: []const u8) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);
    try builder.ensureTotalCapacity(allocator, raw_ident.len + 4);

    // [1] Preserve a single leading `_` if `raw_ident` begins with one or more underscores:
    var start_idx: usize = 0;
    while (start_idx < raw_ident.len and raw_ident[start_idx] == '_') : (start_idx += 1) {}
    var end_idx: usize = raw_ident.len;
    while (end_idx > start_idx and raw_ident[end_idx - 1] == '_') : (end_idx -= 1) {}

    if (start_idx > 0) {
        try builder.append(allocator, '_');
    }
    const core_slice = raw_ident[start_idx..end_idx];
    if (core_slice.len == 0) {
        if (builder.items.len == 0) {
            try builder.append(allocator, '_');
        }
        return builder.toOwnedSlice(allocator);
    }

    // [2] Emit lowercase word segments separated by single `_` characters:
    var has_prev_emitted_underscore = true;
    for (core_slice, 0..) |byte_val, i| {
        if (byte_val == '_') {
            if (!has_prev_emitted_underscore) {
                try builder.append(allocator, '_');
                has_prev_emitted_underscore = true;
            }
            continue;
        }
        if (isIdentifierWordBoundary(core_slice, i) and !has_prev_emitted_underscore) {
            try builder.append(allocator, '_');
        }
        try builder.append(allocator, std.ascii.toLower(byte_val));
        has_prev_emitted_underscore = false;
    }

    // [3] Append a trailing `_` if normalization produced a reserved keyword or primitive (`type_`):
    if (lookupKeywordOrPrim(builder.items) != null) {
        try builder.append(allocator, '_');
    }
    return builder.toOwnedSlice(allocator);
}

/// Converts `raw_ident` into canonical `PascalCase` (stripping all `_` separators).
pub fn toPascalCase(allocator: std.mem.Allocator, raw_ident: []const u8) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);
    try builder.ensureTotalCapacity(allocator, raw_ident.len + 4);

    var start_idx: usize = 0;
    while (start_idx < raw_ident.len and raw_ident[start_idx] == '_') : (start_idx += 1) {}
    var end_idx: usize = raw_ident.len;
    while (end_idx > start_idx and raw_ident[end_idx - 1] == '_') : (end_idx -= 1) {}

    const core_slice = raw_ident[start_idx..end_idx];
    var is_start_of_word = true;
    for (core_slice, 0..) |byte_val, i| {
        if (byte_val == '_') {
            is_start_of_word = true;
            continue;
        }
        if (isIdentifierWordBoundary(core_slice, i)) {
            is_start_of_word = true;
        }
        if (is_start_of_word) {
            try builder.append(allocator, std.ascii.toUpper(byte_val));
            is_start_of_word = false;
        } else {
            try builder.append(allocator, std.ascii.toLower(byte_val));
        }
    }

    // Ensure the result always classifies as a canonical `.type_ident` (`DR-03` §5.2):
    var upper_count: usize = 0;
    var has_lower = false;
    var last_upper_idx: ?usize = null;
    for (builder.items, 0..) |byte_val, i| {
        if (isAsciiUpper(byte_val)) {
            upper_count += 1;
            last_upper_idx = i;
        } else if (isAsciiLower(byte_val)) {
            has_lower = true;
        }
    }
    if (upper_count >= 2 and !has_lower) {
        if (last_upper_idx) |target_idx| {
            builder.items[target_idx] = std.ascii.toLower(builder.items[target_idx]);
        }
    }
    if (std.mem.eql(u8, builder.items, "Self")) {
        try builder.appendSlice(allocator, "Type");
    } else if (builder.items.len == 0) {
        try builder.append(allocator, 'T');
    }
    return builder.toOwnedSlice(allocator);
}

/// Converts `raw_ident` into canonical `SCREAMING_SNAKE_CASE` without consecutive or trailing `_`.
pub fn toScreamingSnakeCase(allocator: std.mem.Allocator, raw_ident: []const u8) ![]u8 {
    var builder: std.ArrayList(u8) = .empty;
    errdefer builder.deinit(allocator);
    try builder.ensureTotalCapacity(allocator, raw_ident.len + 4);

    var start_idx: usize = 0;
    while (start_idx < raw_ident.len and raw_ident[start_idx] == '_') : (start_idx += 1) {}
    var end_idx: usize = raw_ident.len;
    while (end_idx > start_idx and raw_ident[end_idx - 1] == '_') : (end_idx -= 1) {}

    const core_slice = raw_ident[start_idx..end_idx];
    var has_prev_emitted_underscore = true;
    for (core_slice, 0..) |byte_val, i| {
        if (byte_val == '_') {
            if (!has_prev_emitted_underscore) {
                try builder.append(allocator, '_');
                has_prev_emitted_underscore = true;
            }
            continue;
        }
        if (isIdentifierWordBoundary(core_slice, i) and !has_prev_emitted_underscore) {
            try builder.append(allocator, '_');
        }
        try builder.append(allocator, std.ascii.toUpper(byte_val));
        has_prev_emitted_underscore = false;
    }

    // Ensure single-capital constants (`A_`, `A1_`) retain `_` so they remain `.const_ident`:
    var upper_count: usize = 0;
    var has_underscore = false;
    for (builder.items) |byte_val| {
        if (isAsciiUpper(byte_val)) {
            upper_count += 1;
        } else if (byte_val == '_') {
            has_underscore = true;
        }
    }
    if (upper_count == 1 and !has_underscore) {
        if (builder.items.len > 1) {
            try builder.insert(allocator, 1, '_');
        } else {
            try builder.appendSlice(allocator, "_0");
        }
    } else if (builder.items.len == 0) {
        try builder.appendSlice(allocator, "CONST_0");
    }
    return builder.toOwnedSlice(allocator);
}

// ------------------- Stateful Lexer Scanner -------------------

/// Stateless-grammar deterministic maximal-munch lexer scanning UTF-8 source into `TokenBuffer`.
pub const Lexer = struct {
    /// Complete immutable UTF-8 source buffer being tokenized.
    source: []const u8,
    /// Source file handle used for emitted diagnostic spans and `TextEdit` records.
    file_id: FileId,
    /// Target Structure-of-Arrays token and trivia buffer.
    token_buffer: *TokenBuffer,
    /// Optional diagnostic sink receiving `E0101`–`E0104`, `W0101`, and `W0201` diagnostics.
    diagnostic_sink: ?*DiagnosticSink,
    /// Optional string interner used to intern `SuggestedFix` replacement text.
    interner: ?*StringInterner,
    /// Resource cap and warning configuration options.
    options: LexerOptions = .{},
    /// Current byte cursor into `source`.
    cursor: usize = 0,
    /// Leading trivia accumulator for the upcoming token.
    trivia_acc: TriviaAccumulator = .{},

    /// Initializes a `Lexer` with default `LexerOptions`.
    pub fn init(
        source: []const u8,
        file_id: FileId,
        token_buffer: *TokenBuffer,
        diagnostic_sink: ?*DiagnosticSink,
        interner: ?*StringInterner,
    ) Lexer {
        return .{
            .source = source,
            .file_id = file_id,
            .token_buffer = token_buffer,
            .diagnostic_sink = diagnostic_sink,
            .interner = interner,
            .options = .{},
        };
    }

    /// Initializes a `Lexer` with custom `LexerOptions`.
    pub fn initWithOptions(
        source: []const u8,
        file_id: FileId,
        token_buffer: *TokenBuffer,
        diagnostic_sink: ?*DiagnosticSink,
        interner: ?*StringInterner,
        options: LexerOptions,
    ) Lexer {
        return .{
            .source = source,
            .file_id = file_id,
            .token_buffer = token_buffer,
            .diagnostic_sink = diagnostic_sink,
            .interner = interner,
            .options = options,
        };
    }

    /// Scans the entire `source` buffer in a single linear pass, terminating with `TokenKind.eof`.
    pub fn tokenize(self: *Lexer) !void {
        const effective_max_tokens: usize = @min(
            @max(self.options.max_tokens, 1),
            syntax_arenas.MAX_TOKENS_PER_FILE,
        );

        // [1] Pre-reserve approximate token capacity (~1 token per 6 source bytes) to minimize reallocs:
        try self.token_buffer.tokens.ensureTotalCapacity(
            self.token_buffer.allocator,
            @min((self.source.len / 6) + 8, effective_max_tokens),
        );

        while (true) {
            // [2] Scan all leading trivia (whitespace, shebang, comments) before the next token:
            var has_trivia_error = false;
            try self.scanLeadingTrivia(effective_max_tokens, &has_trivia_error);

            // [3] Emit `.eof` once `cursor` reaches the end of `source`:
            if (self.cursor >= self.source.len) {
                _ = try self.token_buffer.appendToken(
                    .eof,
                    .{
                        .has_leading_newline = self.trivia_acc.has_newline,
                        .has_lexer_error = has_trivia_error,
                    },
                    @intCast(self.source.len),
                    0,
                    self.trivia_acc.asSlice(),
                    &.{},
                );
                self.trivia_acc.reset();
                return;
            }

            // [4] Enforce `MAX_TOKENS_PER_FILE` / `options.max_tokens` (`E0104`) with tail preservation:
            if (self.token_buffer.countTokens() + 1 >= effective_max_tokens) {
                try self.emitTokenLimitExceededAndFinish();
                return;
            }

            // [5] Scan the next syntactic token and append it with its accumulated leading trivia:
            try self.scanAndAppendNextToken(effective_max_tokens, has_trivia_error);
        }
    }

    /// Appends a trivia span of arbitrary length, chunking at `65,535` bytes and flushing carrier tokens.
    fn appendTriviaSpan(
        self: *Lexer,
        kind: TriviaKind,
        start_byte: u32,
        total_len: usize,
        effective_max_tokens: usize,
    ) !void {
        if (total_len == 0) return;
        if (kind == .newline_lf or kind == .newline_crlf) {
            self.trivia_acc.has_newline = true;
        }

        var current_offset: u32 = start_byte;
        var remaining_len: usize = total_len;
        while (remaining_len > 0) {
            const chunk_len: u16 = @intCast(@min(remaining_len, @as(usize, MAX_TRIVIA_PIECE_BYTES)));
            const accepted = self.trivia_acc.pushChunk(kind, current_offset, chunk_len);
            if (accepted > 0) {
                current_offset += accepted;
                remaining_len -= accepted;
                continue;
            }

            // All 15 leading trivia slots are at `65,535` bytes (`983,025` bytes total);
            // flush a zero-length synthesized carrier token if token budget permits:
            if (self.token_buffer.countTokens() + 1 < effective_max_tokens) {
                _ = try self.token_buffer.appendToken(
                    .invalid_token,
                    .{
                        .has_leading_newline = self.trivia_acc.has_newline,
                        .is_synthesized = true,
                    },
                    current_offset,
                    0,
                    self.trivia_acc.asSlice(),
                    &.{},
                );
                self.trivia_acc.reset();
            } else {
                // Token budget is at the final `.eof` slot; defer remaining bytes to `E0104` handler:
                self.cursor = current_offset;
                return;
            }
        }
    }

    /// Scans whitespace, `#!` shebang at offset 0, line/doc comments, and nested block comments.
    fn scanLeadingTrivia(self: *Lexer, effective_max_tokens: usize, has_trivia_error: *bool) !void {
        // [1] Optional UTF-8 BOM (`0xEF 0xBB 0xBF`) and `#!` shebang at start of file:
        if (self.cursor == 0) {
            if (self.source.len >= 3 and
                self.source[0] == 0xEF and
                self.source[1] == 0xBB and
                self.source[2] == 0xBF)
            {
                self.cursor = 3;
                try self.appendTriviaSpan(.skipped_unexpected, 0, 3, effective_max_tokens);
            }
            if (self.cursor + 1 < self.source.len and
                self.source[self.cursor] == '#' and
                self.source[self.cursor + 1] == '!')
            {
                const shebang_start: u32 = @intCast(self.cursor);
                self.cursor += 2;
                try self.scanToEndOfLineValidatingUtf8(has_trivia_error);
                try self.appendTriviaSpan(
                    .shebang,
                    shebang_start,
                    self.cursor - @as(usize, shebang_start),
                    effective_max_tokens,
                );
            }
        }

        // [2] Main trivia loop for spaces, tabs, newlines, and comments:
        while (self.cursor < self.source.len) {
            if (self.trivia_acc.isCompletelyFull() and
                self.token_buffer.countTokens() + 1 >= effective_max_tokens)
            {
                return;
            }

            const byte_val = self.source[self.cursor];
            switch (byte_val) {
                ' ' => {
                    const run_start: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    while (self.cursor < self.source.len and self.source[self.cursor] == ' ') {
                        self.cursor += 1;
                    }
                    try self.appendTriviaSpan(
                        .spaces,
                        run_start,
                        self.cursor - @as(usize, run_start),
                        effective_max_tokens,
                    );
                },
                '\t' => {
                    const run_start: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                        self.cursor += 1;
                    }
                    try self.appendTriviaSpan(
                        .tabs,
                        run_start,
                        self.cursor - @as(usize, run_start),
                        effective_max_tokens,
                    );
                },
                '\n' => {
                    const lf_offset: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    try self.appendTriviaSpan(.newline_lf, lf_offset, 1, effective_max_tokens);
                },
                '\r' => {
                    const cr_offset: u32 = @intCast(self.cursor);
                    if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '\n') {
                        self.cursor += 2;
                        try self.appendTriviaSpan(.newline_crlf, cr_offset, 2, effective_max_tokens);
                    } else {
                        self.cursor += 1;
                        self.trivia_acc.has_newline = true;
                        try self.appendTriviaSpan(.skipped_unexpected, cr_offset, 1, effective_max_tokens);
                    }
                },
                0x0B, 0x0C => {
                    const ctrl_offset: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    try self.appendTriviaSpan(.skipped_unexpected, ctrl_offset, 1, effective_max_tokens);
                },
                '/' => {
                    if (self.cursor + 1 >= self.source.len) return;
                    const second_byte = self.source[self.cursor + 1];
                    if (second_byte == '/') {
                        const comment_start: u32 = @intCast(self.cursor);
                        var comment_kind: TriviaKind = .line_comment;
                        if (self.cursor + 2 < self.source.len) {
                            if (self.source[self.cursor + 2] == '!') {
                                comment_kind = .module_doc_comment;
                            } else if (self.source[self.cursor + 2] == '/' and
                                (self.cursor + 3 >= self.source.len or self.source[self.cursor + 3] != '/'))
                            {
                                comment_kind = .doc_comment;
                            }
                        }
                        self.cursor += 2;
                        try self.scanToEndOfLineValidatingUtf8(has_trivia_error);
                        try self.appendTriviaSpan(
                            comment_kind,
                            comment_start,
                            self.cursor - @as(usize, comment_start),
                            effective_max_tokens,
                        );
                    } else if (second_byte == '*') {
                        const block_start: u32 = @intCast(self.cursor);
                        if (try self.scanNestedBlockComment(has_trivia_error)) {
                            self.trivia_acc.has_newline = true;
                        }
                        try self.appendTriviaSpan(
                            .block_comment,
                            block_start,
                            self.cursor - @as(usize, block_start),
                            effective_max_tokens,
                        );
                    } else {
                        return;
                    }
                },
                else => return,
            }
        }
    }

    /// Advances `cursor` to the next `\r` or `\n` (without consuming it), validating UTF-8 sequences.
    fn scanToEndOfLineValidatingUtf8(self: *Lexer, has_error: *bool) !void {
        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '\n' or byte_val == '\r') return;
            if (byte_val < 0x80) {
                self.cursor += 1;
            } else {
                try self.validateAndAdvanceUtf8Codepoint(has_error);
            }
        }
    }

    /// Scans a nestable `/* … */` block comment starting at `cursor`, returning `true` if it spans `\n`.
    fn scanNestedBlockComment(self: *Lexer, has_error: *bool) !bool {
        const open_start: u32 = @intCast(self.cursor);
        self.cursor += 2;
        var depth: u32 = 1;
        var has_newline = false;

        while (self.cursor < self.source.len and depth > 0) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '/' and self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '*') {
                depth += 1;
                self.cursor += 2;
            } else if (byte_val == '*' and
                self.cursor + 1 < self.source.len and
                self.source[self.cursor + 1] == '/')
            {
                depth -= 1;
                self.cursor += 2;
            } else if (byte_val == '\n' or byte_val == '\r') {
                has_newline = true;
                self.cursor += 1;
            } else if (byte_val < 0x80) {
                self.cursor += 1;
            } else {
                try self.validateAndAdvanceUtf8Codepoint(has_error);
            }
        }

        if (depth > 0) {
            has_error.* = true;
            try self.emitSimpleError(
                .e0202_unclosed_delimiter,
                Span.init(self.file_id, open_start, @intCast(self.cursor)),
                "unterminated block comment `/* … */`",
                "block comment opened here was never closed before end of file",
            );
        }
        return has_newline;
    }

    /// Validates a single UTF-8 multi-byte sequence at `cursor`, emitting `E0101` on invalid bytes.
    fn validateAndAdvanceUtf8Codepoint(self: *Lexer, has_error: *bool) !void {
        const start_offset = self.cursor;
        const seq_len = std.unicode.utf8ByteSequenceLength(self.source[start_offset]) catch {
            return self.consumeInvalidUtf8Run(start_offset, has_error);
        };
        if (start_offset + seq_len > self.source.len) {
            return self.consumeInvalidUtf8Run(start_offset, has_error);
        }
        _ = std.unicode.utf8Decode(self.source[start_offset .. start_offset + seq_len]) catch {
            return self.consumeInvalidUtf8Run(start_offset, has_error);
        };
        self.cursor += seq_len;
    }

    /// Consumes a contiguous run of invalid UTF-8 continuation/high bytes and emits a single `E0101`.
    fn consumeInvalidUtf8Run(self: *Lexer, start_offset: usize, has_error: *bool) !void {
        has_error.* = true;
        self.cursor += 1;
        while (self.cursor < self.source.len and self.source[self.cursor] >= 0x80) {
            const next_len = std.unicode.utf8ByteSequenceLength(self.source[self.cursor]) catch {
                self.cursor += 1;
                continue;
            };
            if (self.cursor + next_len <= self.source.len) {
                if (std.unicode.utf8Decode(self.source[self.cursor .. self.cursor + next_len])) |_| {
                    break;
                } else |_| {}
            }
            self.cursor += 1;
        }
        try self.emitSimpleError(
            .e0101_invalid_utf8_sequence,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            "invalid UTF-8 byte sequence in source file",
            "expected valid UTF-8 encoded text here",
        );
    }

    /// Emits `E0104` when `max_tokens` is reached and preserves all remaining bytes on the final `.eof`.
    fn emitTokenLimitExceededAndFinish(self: *Lexer) !void {
        const overflow_start: u32 = @intCast(self.cursor);
        const source_end: u32 = @intCast(self.source.len);
        try self.emitSimpleError(
            .e0104_token_limit_exceeded,
            Span.init(self.file_id, overflow_start, source_end),
            "source file token count exceeds maximum token limit",
            "remaining source bytes preserved as unparsed tail trivia",
        );

        var trailing_acc = TriviaAccumulator{};
        var remaining_len: usize = self.source.len - self.cursor;
        var current_offset: u32 = overflow_start;

        while (remaining_len > 0) {
            const chunk_len: u16 = @intCast(@min(remaining_len, @as(usize, MAX_TRIVIA_PIECE_BYTES)));
            const accepted_leading = self.trivia_acc.pushChunk(.skipped_unexpected, current_offset, chunk_len);
            if (accepted_leading > 0) {
                current_offset += accepted_leading;
                remaining_len -= accepted_leading;
                continue;
            }
            const accepted_trailing = trailing_acc.pushChunk(.skipped_unexpected, current_offset, chunk_len);
            if (accepted_trailing > 0) {
                current_offset += accepted_trailing;
                remaining_len -= accepted_trailing;
                continue;
            }
            if (self.token_buffer.countTokens() + 1 < syntax_arenas.MAX_TOKENS_PER_FILE) {
                _ = try self.token_buffer.appendToken(
                    .invalid_token,
                    .{
                        .has_leading_newline = self.trivia_acc.has_newline,
                        .has_lexer_error = true,
                        .is_synthesized = true,
                    },
                    current_offset,
                    0,
                    self.trivia_acc.asSlice(),
                    trailing_acc.asSlice(),
                );
                self.trivia_acc.reset();
                trailing_acc.reset();
                continue;
            }
            break;
        }

        self.cursor = self.source.len;
        _ = try self.token_buffer.appendToken(
            .eof,
            .{
                .has_leading_newline = self.trivia_acc.has_newline,
                .has_lexer_error = true,
            },
            source_end,
            0,
            self.trivia_acc.asSlice(),
            trailing_acc.asSlice(),
        );
        self.trivia_acc.reset();
    }

    /// Scans the next token starting at `self.cursor` and appends it to `self.token_buffer`.
    fn scanAndAppendNextToken(self: *Lexer, effective_max_tokens: usize, has_initial_error: bool) !void {
        const token_start: usize = self.cursor;
        var has_lexer_error = has_initial_error;
        const first_byte = self.source[token_start];

        const token_kind: TokenKind = if (first_byte == 'r' and
            token_start + 1 < self.source.len and
            (self.source[token_start + 1] == '"' or self.source[token_start + 1] == '#'))
            try self.scanRawStringLiteral(&has_lexer_error)
        else if (isIdentStart(first_byte))
            try self.scanIdentifierOrKeyword(&has_lexer_error)
        else if (isDecimalDigit(first_byte))
            try self.scanNumericLiteral(&has_lexer_error)
        else switch (first_byte) {
            '"' => try self.scanStandardStringLiteral(&has_lexer_error),
            '\'' => try self.scanCharLiteral(&has_lexer_error),
            '{' => blk: {
                self.cursor += 1;
                break :blk .lbrace;
            },
            '}' => blk: {
                self.cursor += 1;
                break :blk .rbrace;
            },
            '(' => blk: {
                self.cursor += 1;
                break :blk .lparen;
            },
            ')' => blk: {
                self.cursor += 1;
                break :blk .rparen;
            },
            '[' => blk: {
                self.cursor += 1;
                break :blk .lbracket;
            },
            ']' => blk: {
                self.cursor += 1;
                break :blk .rbracket;
            },
            ';' => blk: {
                self.cursor += 1;
                break :blk .semi;
            },
            ',' => blk: {
                self.cursor += 1;
                break :blk .comma;
            },
            '@' => blk: {
                self.cursor += 1;
                break :blk .at;
            },
            '?' => blk: {
                self.cursor += 1;
                break :blk .question;
            },
            '~' => blk: {
                self.cursor += 1;
                break :blk .tilde;
            },
            ':' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == ':') {
                    self.cursor += 2;
                    break :blk .coloncolon;
                }
                self.cursor += 1;
                break :blk .colon;
            },
            '.' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '.') {
                    if (self.cursor + 2 < self.source.len and self.source[self.cursor + 2] == '=') {
                        self.cursor += 3;
                        break :blk .dotdoteq;
                    }
                    self.cursor += 2;
                    break :blk .dotdot;
                }
                self.cursor += 1;
                break :blk .dot;
            },
            '+' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    switch (self.source[self.cursor + 1]) {
                        '%' => {
                            self.cursor += 2;
                            break :blk .plus_percent;
                        },
                        '|' => {
                            self.cursor += 2;
                            break :blk .plus_pipe;
                        },
                        '=' => {
                            self.cursor += 2;
                            break :blk .plus_eq;
                        },
                        else => {},
                    }
                }
                self.cursor += 1;
                break :blk .plus;
            },
            '-' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    switch (self.source[self.cursor + 1]) {
                        '>' => {
                            self.cursor += 2;
                            break :blk .arrow;
                        },
                        '%' => {
                            self.cursor += 2;
                            break :blk .minus_percent;
                        },
                        '|' => {
                            self.cursor += 2;
                            break :blk .minus_pipe;
                        },
                        '=' => {
                            self.cursor += 2;
                            break :blk .minus_eq;
                        },
                        else => {},
                    }
                }
                self.cursor += 1;
                break :blk .minus;
            },
            '*' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    switch (self.source[self.cursor + 1]) {
                        '%' => {
                            self.cursor += 2;
                            break :blk .star_percent;
                        },
                        '|' => {
                            self.cursor += 2;
                            break :blk .star_pipe;
                        },
                        '=' => {
                            self.cursor += 2;
                            break :blk .star_eq;
                        },
                        else => {},
                    }
                }
                self.cursor += 1;
                break :blk .star;
            },
            '/' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '=') {
                    self.cursor += 2;
                    break :blk .slash_eq;
                }
                self.cursor += 1;
                break :blk .slash;
            },
            '%' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '=') {
                    self.cursor += 2;
                    break :blk .percent_eq;
                }
                self.cursor += 1;
                break :blk .percent;
            },
            '=' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    switch (self.source[self.cursor + 1]) {
                        '=' => {
                            self.cursor += 2;
                            break :blk .eqeq;
                        },
                        '>' => {
                            self.cursor += 2;
                            break :blk .fat_arrow;
                        },
                        else => {},
                    }
                }
                self.cursor += 1;
                break :blk .eq;
            },
            '!' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '=') {
                    self.cursor += 2;
                    break :blk .bang_eq;
                }
                self.cursor += 1;
                break :blk .bang;
            },
            '<' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    if (self.source[self.cursor + 1] == '<') {
                        if (self.cursor + 2 < self.source.len and self.source[self.cursor + 2] == '=') {
                            self.cursor += 3;
                            break :blk .shl_eq;
                        }
                        self.cursor += 2;
                        break :blk .shl;
                    }
                    if (self.source[self.cursor + 1] == '=') {
                        self.cursor += 2;
                        break :blk .le;
                    }
                }
                self.cursor += 1;
                break :blk .lt;
            },
            '>' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    if (self.source[self.cursor + 1] == '>') {
                        if (self.cursor + 2 < self.source.len and self.source[self.cursor + 2] == '=') {
                            self.cursor += 3;
                            break :blk .shr_eq;
                        }
                        self.cursor += 2;
                        break :blk .shr;
                    }
                    if (self.source[self.cursor + 1] == '=') {
                        self.cursor += 2;
                        break :blk .ge;
                    }
                }
                self.cursor += 1;
                break :blk .gt;
            },
            '&' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    if (self.source[self.cursor + 1] == '&') {
                        self.cursor += 2;
                        break :blk .ampamp;
                    }
                    if (self.source[self.cursor + 1] == '=') {
                        self.cursor += 2;
                        break :blk .amp_eq;
                    }
                }
                self.cursor += 1;
                break :blk .amp;
            },
            '|' => blk: {
                if (self.cursor + 1 < self.source.len) {
                    switch (self.source[self.cursor + 1]) {
                        '>' => {
                            self.cursor += 2;
                            break :blk .pipe_gt;
                        },
                        '|' => {
                            self.cursor += 2;
                            break :blk .pipepipe;
                        },
                        '=' => {
                            self.cursor += 2;
                            break :blk .pipe_eq;
                        },
                        else => {},
                    }
                }
                self.cursor += 1;
                break :blk .pipe;
            },
            '^' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '=') {
                    self.cursor += 2;
                    break :blk .caret_eq;
                }
                self.cursor += 1;
                break :blk .caret;
            },
            '#' => try self.scanHashDirectiveOrInvalid(&has_lexer_error),
            else => try self.scanInvalidByteOrUtf8(&has_lexer_error),
        };

        // Append the scanned token (chunking > 65,535-byte tokens losslessly if needed):
        const total_token_bytes: usize = self.cursor - token_start;
        const clamped_token_len: u16 = @intCast(@min(total_token_bytes, @as(usize, MAX_TRIVIA_PIECE_BYTES)));
        var trailing_overflow_acc = TriviaAccumulator{};
        var overflow_remaining: usize = total_token_bytes - @as(usize, clamped_token_len);
        var overflow_offset: u32 = @intCast(token_start + @as(usize, clamped_token_len));

        while (overflow_remaining > 0) {
            const chunk_len: u16 = @intCast(@min(overflow_remaining, @as(usize, MAX_TRIVIA_PIECE_BYTES)));
            const accepted = trailing_overflow_acc.pushChunk(.skipped_unexpected, overflow_offset, chunk_len);
            if (accepted == 0) break;
            overflow_offset += accepted;
            overflow_remaining -= accepted;
        }

        _ = try self.token_buffer.appendToken(
            token_kind,
            .{
                .has_leading_newline = self.trivia_acc.has_newline,
                .has_lexer_error = has_lexer_error,
            },
            @intCast(token_start),
            clamped_token_len,
            self.trivia_acc.asSlice(),
            trailing_overflow_acc.asSlice(),
        );
        self.trivia_acc.reset();

        if (overflow_remaining > 0) {
            try self.appendTriviaSpan(
                .skipped_unexpected,
                overflow_offset,
                overflow_remaining,
                effective_max_tokens,
            );
        }
    }

    /// Scans an identifier, keyword, primitive type, or `_`, checking the `DR-03` casing invariant.
    fn scanIdentifierOrKeyword(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1;
        while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
            self.cursor += 1;
        }
        const lexeme = self.source[start_offset..self.cursor];
        const classification = classifyIdentifierOrKeyword(lexeme);

        if (classification.has_case_violation) {
            has_lexer_error.* = true;
            if (self.options.is_casing_warning_enabled) {
                try self.emitIdentifierCasingWarning(
                    Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                    lexeme,
                    classification.expected_case,
                );
            }
        }
        return classification.kind;
    }

    /// Scans a decimal, hexadecimal (`0x`), binary (`0b`), or octal (`0o`) integer or float literal.
    fn scanNumericLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        var is_malformed = false;

        // [1] Non-decimal radix integer literals (`0x`/`0X`, `0b`/`0B`, `0o`/`0O`):
        if (self.source[start_offset] == '0' and self.cursor + 1 < self.source.len) {
            const maybe_radix: ?u8 = switch (self.source[self.cursor + 1]) {
                'x', 'X' => 16,
                'b', 'B' => 2,
                'o', 'O' => 8,
                else => null,
            };
            if (maybe_radix) |radix| {
                self.cursor += 2;
                var digit_count: usize = 0;
                var is_prev_underscore = false;

                if (self.cursor < self.source.len and self.source[self.cursor] == '_') {
                    is_malformed = true;
                }
                while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                    const byte_val = self.source[self.cursor];
                    if (byte_val == '_') {
                        if (is_prev_underscore) is_malformed = true;
                        is_prev_underscore = true;
                    } else if (isValidDigitForRadix(byte_val, radix)) {
                        digit_count += 1;
                        is_prev_underscore = false;
                    } else {
                        is_malformed = true;
                        is_prev_underscore = false;
                    }
                    self.cursor += 1;
                }
                if (digit_count == 0 or is_prev_underscore) {
                    is_malformed = true;
                }
                if (is_malformed) {
                    has_lexer_error.* = true;
                    try self.emitNumericLiteralError(start_offset, self.cursor);
                }
                return .int_lit;
            }
        }

        // [2] Decimal integer mantissa digits and `_` visual separators:
        var is_prev_underscore = false;
        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (isDecimalDigit(byte_val)) {
                is_prev_underscore = false;
                self.cursor += 1;
            } else if (byte_val == '_') {
                if (is_prev_underscore) is_malformed = true;
                is_prev_underscore = true;
                self.cursor += 1;
            } else {
                break;
            }
        }
        if (is_prev_underscore) {
            is_malformed = true;
        }

        // [3] Fractional `.` part; only consume `.` when followed immediately by `[0-9]`:
        var is_float = false;
        if (self.cursor + 1 < self.source.len and
            self.source[self.cursor] == '.' and
            isDecimalDigit(self.source[self.cursor + 1]))
        {
            is_float = true;
            self.cursor += 1;
            is_prev_underscore = false;
            while (self.cursor < self.source.len) {
                const byte_val = self.source[self.cursor];
                if (isDecimalDigit(byte_val)) {
                    is_prev_underscore = false;
                    self.cursor += 1;
                } else if (byte_val == '_') {
                    if (is_prev_underscore) is_malformed = true;
                    is_prev_underscore = true;
                    self.cursor += 1;
                } else {
                    break;
                }
            }
            if (is_prev_underscore) {
                is_malformed = true;
            }
        }

        // [4] Scientific exponent `e` / `E` with optional `+` / `-` sign:
        if (self.cursor < self.source.len and
            (self.source[self.cursor] == 'e' or self.source[self.cursor] == 'E'))
        {
            is_float = true;
            self.cursor += 1;
            if (self.cursor < self.source.len and
                (self.source[self.cursor] == '+' or self.source[self.cursor] == '-'))
            {
                self.cursor += 1;
            }
            if (self.cursor < self.source.len and self.source[self.cursor] == '_') {
                is_malformed = true;
            }
            var exp_digits: usize = 0;
            is_prev_underscore = false;
            while (self.cursor < self.source.len) {
                const byte_val = self.source[self.cursor];
                if (isDecimalDigit(byte_val)) {
                    exp_digits += 1;
                    is_prev_underscore = false;
                    self.cursor += 1;
                } else if (byte_val == '_') {
                    if (is_prev_underscore) is_malformed = true;
                    is_prev_underscore = true;
                    self.cursor += 1;
                } else {
                    break;
                }
            }
            if (exp_digits == 0 or is_prev_underscore) {
                is_malformed = true;
            }
        }

        // [5] Reject attached identifier or type suffixes (`123abc`, `42u64`):
        if (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
            is_malformed = true;
            while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                self.cursor += 1;
            }
        }

        if (is_malformed) {
            has_lexer_error.* = true;
            try self.emitNumericLiteralError(start_offset, self.cursor);
        }
        return if (is_float) .float_lit else .int_lit;
    }

    /// Scans a standard `"…"` string literal, validating escapes, UTF-8, and `{expr}` interpolation.
    fn scanStandardStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        try self.scanStandardStringBody(has_lexer_error);
        return .string_lit;
    }

    /// Scans from an opening `"` through its matching closing `"`, supporting nested `{expr}` blocks.
    fn scanStandardStringBody(self: *Lexer, has_lexer_error: *bool) !void {
        const start_offset = self.cursor;
        self.cursor += 1;
        var interp_depth: u32 = 0;
        var interp_brace_stack: [syntax_arenas.MAX_PARSE_DEPTH]u32 = undefined;
        var nested_str_depth: usize = 0;
        var has_emitted_depth_error = false;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (interp_depth == 0) {
                if (byte_val == '"') {
                    self.cursor += 1;
                    if (nested_str_depth == 0) {
                        return;
                    }
                    nested_str_depth -= 1;
                    interp_depth = if (nested_str_depth < syntax_arenas.MAX_PARSE_DEPTH)
                        interp_brace_stack[nested_str_depth]
                    else
                        1;
                    continue;
                }
                if (byte_val == '\\') {
                    try self.scanEscapeSequence(true, has_lexer_error);
                    continue;
                }
                if (byte_val == '{') {
                    interp_depth = 1;
                    self.cursor += 1;
                    continue;
                }
                if (byte_val < 0x80) {
                    self.cursor += 1;
                } else {
                    try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                }
            } else {
                // Inside `{expr}` interpolation; track nested braces, strings, chars, and comments:
                if (byte_val == '{') {
                    interp_depth += 1;
                    self.cursor += 1;
                } else if (byte_val == '}') {
                    interp_depth -= 1;
                    self.cursor += 1;
                } else if (byte_val == '"') {
                    if (nested_str_depth < syntax_arenas.MAX_PARSE_DEPTH) {
                        interp_brace_stack[nested_str_depth] = interp_depth;
                    } else if (!has_emitted_depth_error) {
                        has_lexer_error.* = true;
                        has_emitted_depth_error = true;
                        try self.emitSimpleError(
                            .e0203_parse_depth_exceeded,
                            Span.init(
                                self.file_id,
                                @intCast(self.cursor),
                                @intCast(self.cursor + 1),
                            ),
                            "nested string interpolation exceeds maximum parse depth of 512",
                            "simplify or extract deeply nested interpolated string expressions",
                        );
                    }
                    nested_str_depth += 1;
                    interp_depth = 0;
                    self.cursor += 1;
                } else if (byte_val == 'r' and
                    (self.cursor == 0 or !isIdentContinue(self.source[self.cursor - 1])) and
                    self.cursor + 1 < self.source.len and
                    (self.source[self.cursor + 1] == '"' or self.source[self.cursor + 1] == '#'))
                {
                    _ = try self.scanRawStringLiteral(has_lexer_error);
                } else if (byte_val == '\'') {
                    _ = try self.scanCharLiteral(has_lexer_error);
                } else if (byte_val == '/' and self.cursor + 1 < self.source.len) {
                    if (self.source[self.cursor + 1] == '/') {
                        self.cursor += 2;
                        try self.scanToEndOfLineValidatingUtf8(has_lexer_error);
                    } else if (self.source[self.cursor + 1] == '*') {
                        _ = try self.scanNestedBlockComment(has_lexer_error);
                    } else {
                        self.cursor += 1;
                    }
                } else if (byte_val < 0x80) {
                    self.cursor += 1;
                } else {
                    try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                }
            }
        }

        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0102_unterminated_string_literal,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            "unterminated string literal",
            "string literal opened here was not closed before end of file",
        );
    }

    /// Scans a raw string literal `r"…"` or `r#"…"#` (`0..255` `#` delimiters).
    fn scanRawStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1; // Advance past `'r'`.

        var hash_count: usize = 0;
        while (self.cursor < self.source.len and self.source[self.cursor] == '#') {
            hash_count += 1;
            self.cursor += 1;
        }

        // If `r#…` is not followed by `"`, consume attached identifier characters and emit `E0102`:
        if (self.cursor >= self.source.len or self.source[self.cursor] != '"') {
            while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                self.cursor += 1;
            }
            has_lexer_error.* = true;
            try self.emitSimpleError(
                .e0102_unterminated_string_literal,
                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                "malformed or unterminated raw string literal",
                "expected opening `\"` after raw string prefix",
            );
            return .string_lit;
        }

        if (hash_count > MAX_RAW_STRING_HASHES) {
            has_lexer_error.* = true;
        }
        self.cursor += 1; // Advance past opening `'"'`.

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"') {
                self.cursor += 1;
                var matched_hashes: usize = 0;
                while (matched_hashes < hash_count and
                    self.cursor < self.source.len and
                    self.source[self.cursor] == '#')
                {
                    matched_hashes += 1;
                    self.cursor += 1;
                }
                if (matched_hashes == hash_count) {
                    if (hash_count > MAX_RAW_STRING_HASHES) {
                        try self.emitSimpleError(
                            .e0102_unterminated_string_literal,
                            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                            "raw string delimiter exceeds maximum of 255 `#` characters",
                            "reduce `#` delimiter count to at most 255",
                        );
                    }
                    return .string_lit;
                }
            } else if (byte_val < 0x80) {
                self.cursor += 1;
            } else {
                try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
            }
        }

        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0102_unterminated_string_literal,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            "unterminated raw string literal",
            "raw string literal was not closed by matching delimiter before end of file",
        );
        return .string_lit;
    }

    /// Scans a character literal `'c'`, validating escapes, codepoint count, and line termination.
    fn scanCharLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1; // Advance past opening `'\''`.
        var codepoint_count: usize = 0;
        var has_closing_quote = false;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '\'') {
                self.cursor += 1;
                has_closing_quote = true;
                break;
            }
            if (byte_val == '\n' or byte_val == '\r') {
                break;
            }
            if (byte_val == '\\') {
                try self.scanEscapeSequence(false, has_lexer_error);
                codepoint_count += 1;
            } else if (byte_val < 0x80) {
                self.cursor += 1;
                codepoint_count += 1;
            } else {
                try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                codepoint_count += 1;
            }
        }

        if (!has_closing_quote or codepoint_count != 1) {
            has_lexer_error.* = true;
            try self.emitSimpleError(
                .e0102_unterminated_string_literal,
                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                if (!has_closing_quote)
                    "unterminated character literal"
                else if (codepoint_count == 0)
                    "empty character literal `''`"
                else
                    "character literal may only contain a single Unicode scalar value",
                "expected a single character or escape sequence enclosed in `'…'`",
            );
        }
        return .char_lit;
    }

    /// Validates a `\` escape sequence at `self.cursor` inside a string (`is_string = true`) or char literal.
    fn scanEscapeSequence(self: *Lexer, is_string: bool, has_lexer_error: *bool) !void {
        const escape_start = self.cursor;
        self.cursor += 1; // Advance past `'\\'`.
        if (self.cursor >= self.source.len) return;

        const esc_byte = self.source[self.cursor];
        switch (esc_byte) {
            '\n', '\r' => {
                if (!is_string) {
                    return;
                }
                if (esc_byte == '\r' and
                    self.cursor + 1 < self.source.len and
                    self.source[self.cursor + 1] == '\n')
                {
                    self.cursor += 2;
                } else {
                    self.cursor += 1;
                }
            },
            'n', 'r', 't', '\\', '0' => {
                self.cursor += 1;
            },
            '"', '{', '}' => {
                self.cursor += 1;
                if (!is_string and self.options.is_escape_warning_enabled) {
                    try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                }
            },
            '\'' => {
                self.cursor += 1;
                if (is_string and self.options.is_escape_warning_enabled) {
                    try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                }
            },
            'x' => {
                self.cursor += 1;
                if (self.cursor + 2 <= self.source.len and
                    isHexDigit(self.source[self.cursor]) and
                    isHexDigit(self.source[self.cursor + 1]))
                {
                    self.cursor += 2;
                } else {
                    while (self.cursor < self.source.len and
                        self.cursor < escape_start + 4 and
                        isIdentContinue(self.source[self.cursor]))
                    {
                        self.cursor += 1;
                    }
                    has_lexer_error.* = true;
                    try self.emitSimpleError(
                        .e0101_invalid_utf8_sequence,
                        Span.init(self.file_id, @intCast(escape_start), @intCast(self.cursor)),
                        "malformed hexadecimal escape sequence `\\xHH`",
                        "expected exactly two hexadecimal digits `[0-9a-fA-F]` after `\\x`",
                    );
                }
            },
            'u' => {
                self.cursor += 1;
                if (self.cursor >= self.source.len or self.source[self.cursor] != '{') {
                    has_lexer_error.* = true;
                    try self.emitSimpleError(
                        .e0101_invalid_utf8_sequence,
                        Span.init(self.file_id, @intCast(escape_start), @intCast(self.cursor)),
                        "malformed Unicode escape sequence `\\u{…}`",
                        "expected `{` after `\\u`",
                    );
                    return;
                }
                self.cursor += 1; // Advance past `'{'`.
                var digit_count: usize = 0;
                var scalar_val: u32 = 0;
                var has_invalid_hex = false;

                while (self.cursor < self.source.len) {
                    const hex_byte = self.source[self.cursor];
                    if (hex_byte == '}' or hex_byte == '"' or hex_byte == '\'' or hex_byte == '\n' or hex_byte == '\r') {
                        break;
                    }
                    if (isHexDigit(hex_byte)) {
                        digit_count += 1;
                        if (digit_count <= 6) {
                            scalar_val = (scalar_val << 4) | @as(u32, hexDigitValue(hex_byte));
                        }
                    } else {
                        has_invalid_hex = true;
                    }
                    self.cursor += 1;
                }

                const has_closing_brace = self.cursor < self.source.len and self.source[self.cursor] == '}';
                if (has_closing_brace) {
                    self.cursor += 1;
                }
                const is_valid_codepoint = digit_count >= 1 and
                    digit_count <= 6 and
                    !has_invalid_hex and
                    has_closing_brace and
                    scalar_val <= 0x10FFFF and
                    std.unicode.utf8ValidCodepoint(@intCast(scalar_val));

                if (!is_valid_codepoint) {
                    has_lexer_error.* = true;
                    try self.emitSimpleError(
                        .e0101_invalid_utf8_sequence,
                        Span.init(self.file_id, @intCast(escape_start), @intCast(self.cursor)),
                        "invalid Unicode scalar value in `\\u{…}` escape",
                        "expected 1 to 6 hex digits encoding a valid Unicode scalar (`0x0..0xD7FF` or `0xE000..0x10FFFF`)",
                    );
                }
            },
            else => {
                if (esc_byte < 0x80) {
                    self.cursor += 1;
                    if (self.options.is_escape_warning_enabled) {
                        try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                    }
                } else {
                    try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                    if (self.options.is_escape_warning_enabled) {
                        try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                    }
                }
            },
        }
    }

    /// Scans `#soa` (`TokenKind.hash_soa` = `70`) or emits `.invalid_token` on unknown `#` directives.
    fn scanHashDirectiveOrInvalid(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        if (self.cursor + 4 <= self.source.len and
            std.mem.eql(u8, self.source[self.cursor .. self.cursor + 4], "#soa") and
            (self.cursor + 4 == self.source.len or !isIdentContinue(self.source[self.cursor + 4])))
        {
            self.cursor += 4;
            return .hash_soa;
        }

        self.cursor += 1;
        while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
            self.cursor += 1;
        }
        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0201_unexpected_token,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            "unrecognized `#` directive; only `#soa` is valid in CoreX",
            "unexpected directive token",
        );
        return .invalid_token;
    }

    /// Scans an unrecognized ASCII punctuation byte or invalid/non-ASCII UTF-8 sequence as `.invalid_token`.
    fn scanInvalidByteOrUtf8(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        has_lexer_error.* = true;
        if (self.source[start_offset] < 0x80) {
            self.cursor += 1;
            try self.emitSimpleError(
                .e0201_unexpected_token,
                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                "unexpected character in source file",
                "unrecognized lexical character",
            );
            return .invalid_token;
        }

        // Non-ASCII byte outside string or comment; validate UTF-8 to distinguish `E0101` vs. `E0201`:
        var is_utf8_invalid = false;
        try self.validateAndAdvanceUtf8Codepoint(&is_utf8_invalid);
        if (!is_utf8_invalid) {
            try self.emitSimpleError(
                .e0201_unexpected_token,
                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                "non-ASCII character is not permitted in identifiers or operators",
                "unexpected non-ASCII codepoint",
            );
        }
        return .invalid_token;
    }

    /// Emits an error diagnostic into `self.diagnostic_sink` when present.
    fn emitSimpleError(
        self: *Lexer,
        code: DiagnosticCode,
        span: Span,
        message: []const u8,
        label_text: []const u8,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const primary_labels = [_]LabeledSpan{.{
            .span = span,
            .label = label_text,
            .style = .primary,
        }};
        try sink.emit(.{
            .code = code,
            .severity = .err,
            .primary_span = span,
            .message = message,
            .labels = &primary_labels,
        });
    }

    /// Emits `E0103` (`e0103_invalid_numeric_literal`) for a malformed numeric token.
    fn emitNumericLiteralError(self: *Lexer, start_offset: usize, end_offset: usize) !void {
        try self.emitSimpleError(
            .e0103_invalid_numeric_literal,
            Span.init(self.file_id, @intCast(start_offset), @intCast(end_offset)),
            "malformed numeric literal",
            "invalid digits, radix prefix, `_` separator placement, or trailing suffix",
        );
    }

    /// Emits `W0101` (`w0101_redundant_escape_sequence`) with a `.machine_applicable` fix replacing `\c` with `c`.
    fn emitRedundantEscapeWarning(self: *Lexer, escape_start: u32, escape_end: u32) !void {
        const sink = self.diagnostic_sink orelse return;
        const escape_span = Span.init(self.file_id, escape_start, escape_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = escape_span,
            .label = "unnecessary backslash escape; character stands for itself",
            .style = .primary,
        }};

        if (self.interner) |str_interner| {
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = escape_start,
                .end_byte = escape_end,
                .replacement_id = try str_interner.intern(
                    self.source[@as(usize, escape_start) + 1 .. @as(usize, escape_end)],
                ),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "remove redundant backslash escape",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .w0101_redundant_escape_sequence,
                .severity = .warning,
                .primary_span = escape_span,
                .message = "redundant character escape sequence in literal",
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
        } else {
            try sink.emit(.{
                .code = .w0101_redundant_escape_sequence,
                .severity = .warning,
                .primary_span = escape_span,
                .message = "redundant character escape sequence in literal",
                .labels = &primary_labels,
            });
        }
    }

    /// Emits `W0201` (`w0201_non_canonical_identifier_case`) with a `.machine_applicable` casing fix.
    fn emitIdentifierCasingWarning(
        self: *Lexer,
        ident_span: Span,
        lexeme: []const u8,
        expected_case: IdentifierCase,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const label_msg = switch (expected_case) {
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

        if (self.interner) |str_interner| {
            const converted = switch (expected_case) {
                .snake_case => try toSnakeCase(sink.arena.asAllocator(), lexeme),
                .pascal_case => try toPascalCase(sink.arena.asAllocator(), lexeme),
                .screaming_snake_case => try toScreamingSnakeCase(sink.arena.asAllocator(), lexeme),
                .reserved_or_wildcard => lexeme,
            };
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
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
};

/// Tokenizes `source` into `token_buffer` in a single linear pass using default `LexerOptions`.
pub fn tokenize(
    source: []const u8,
    file_id: FileId,
    token_buffer: *TokenBuffer,
    diagnostic_sink: ?*DiagnosticSink,
    interner: ?*StringInterner,
) !void {
    var lexer_instance = Lexer.init(source, file_id, token_buffer, diagnostic_sink, interner);
    try lexer_instance.tokenize();
}

/// Canonical alias for `tokenize` used by file-level compilation queries.
pub const lexFile = tokenize;

// ------------------------- Unit Tests -------------------------

test "test_all_45_keywords_19_prim_types_and_disjoint_casing" {
    try std.testing.expectEqual(@as(?TokenKind, .kw_pub), lookupKeywordOrPrim("pub"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_self_val), lookupKeywordOrPrim("self"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_self_type), lookupKeywordOrPrim("Self"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_bit_field), lookupKeywordOrPrim("bit_field"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("i32"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("usize"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("never"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("unit"));
    try std.testing.expectEqual(@as(?TokenKind, null), lookupKeywordOrPrim("custom_ident"));

    // Standalone `_` vs canonical/non-canonical `.ident`, `.type_ident`, and `.const_ident`:
    const wild = classifyIdentifierOrKeyword("_");
    try std.testing.expectEqual(TokenKind.underscore, wild.kind);
    try std.testing.expect(wild.is_canonical);

    for ([_][]const u8{ "foo_bar", "_unused", "_123", "type_", "x" }) |valid_ident| {
        const res = classifyIdentifierOrKeyword(valid_ident);
        try std.testing.expectEqual(TokenKind.ident, res.kind);
        try std.testing.expect(res.is_canonical);
    }
    for ([_][]const u8{ "badCamelCase", "my_Var", "_BadName", "bad__ident" }) |bad_ident| {
        const res = classifyIdentifierOrKeyword(bad_ident);
        try std.testing.expectEqual(TokenKind.ident, res.kind);
        try std.testing.expect(!res.is_canonical);
    }

    for ([_][]const u8{ "HttpServer", "T", "K", "V", "V4", "V6", "T0" }) |valid_type| {
        const res = classifyIdentifierOrKeyword(valid_type);
        try std.testing.expectEqual(TokenKind.type_ident, res.kind);
        try std.testing.expect(res.is_canonical);
    }
    for ([_][]const u8{ "Bad_Snake_Case", "My_Type_" }) |bad_type| {
        const res = classifyIdentifierOrKeyword(bad_type);
        try std.testing.expectEqual(TokenKind.type_ident, res.kind);
        try std.testing.expect(!res.is_canonical);
    }

    for ([_][]const u8{ "MAX_SIZE", "PI_2", "SHA_256", "IO", "EOF" }) |valid_const| {
        const res = classifyIdentifierOrKeyword(valid_const);
        try std.testing.expectEqual(TokenKind.const_ident, res.kind);
        try std.testing.expect(res.is_canonical);
    }
    for ([_][]const u8{ "BAD__CONST", "MAX_", "A_" }) |bad_const| {
        const res = classifyIdentifierOrKeyword(bad_const);
        try std.testing.expectEqual(TokenKind.const_ident, res.kind);
        try std.testing.expect(!res.is_canonical);
    }
}

test "test_case_conversion_helpers_and_w0201_transactional_patching" {
    const snake_1 = try toSnakeCase(std.testing.allocator, "badCamelCase");
    defer std.testing.allocator.free(snake_1);
    try std.testing.expectEqualStrings("bad_camel_case", snake_1);

    const snake_2 = try toSnakeCase(std.testing.allocator, "_BadName");
    defer std.testing.allocator.free(snake_2);
    try std.testing.expectEqualStrings("_bad_name", snake_2);

    const pascal_1 = try toPascalCase(std.testing.allocator, "Bad_Snake_Case");
    defer std.testing.allocator.free(pascal_1);
    try std.testing.expectEqualStrings("BadSnakeCase", pascal_1);

    const const_1 = try toScreamingSnakeCase(std.testing.allocator, "BAD__CONST_");
    defer std.testing.allocator.free(const_1);
    try std.testing.expectEqualStrings("BAD_CONST", const_1);

    const source = "let badCamel = 1; struct Bad_Type {} const MAX__VAL: i32 = 2;";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(source, FileId.fromInt(0), &token_buf, &sink, &interner);
    try std.testing.expectEqual(@as(u32, 3), sink.warning_count);

    var fixes: [3]SuggestedFix = undefined;
    for (sink.asSlice(), 0..) |diag_item, i| {
        try std.testing.expectEqual(DiagnosticCode.w0201_non_canonical_identifier_case, diag_item.code);
        fixes[i] = diag_item.suggestions[0];
    }
    const patch_res = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        source,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 3), patch_res.applied_count);
    try std.testing.expectEqualStrings(
        "let bad_camel = 1; struct BadType {} const MAX_VAL: i32 = 2;",
        patch_res.patched_source,
    );
}

test "test_numeric_range_disambiguation_and_string_interpolation_roundtrip" {
    const source =
        \\#!/usr/bin/env corex
        \\// Range, method call, raw string, and nested interpolation:
        \\fn demo() {
        \\    for i in 0..10 {
        \\        let m = 10.max(20);
        \\        let msg = "val={if i > 0 { "ok /* } */" } else { r#"raw } str"# }}\n";
        \\        let arr: #soa [u32] = [];
        \\    }
        \\}
    ;
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try lexFile(source, FileId.fromInt(0), &token_buf, &sink, null);
    try std.testing.expect(!sink.hasErrors());
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);

    // Verify `0..10` and `10.max(20)` tokenization:
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(8)).kind);
    try std.testing.expectEqual(TokenKind.dotdot, token_buf.getToken(TokenIndex.fromInt(9)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(10)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(15)).kind);
    try std.testing.expectEqual(TokenKind.dot, token_buf.getToken(TokenIndex.fromInt(16)).kind);
    try std.testing.expectEqual(TokenKind.ident, token_buf.getToken(TokenIndex.fromInt(17)).kind);

    var cst_arena = syntax_arenas.LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, source, &token_buf);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(source, reconstructed);
}

test "test_malformed_literals_escapes_and_e0104_tail_preservation" {
    const bad_source = "0x 0x_1 0b102 0o78 1__2 1.0e+ 42u64 'ab' '' \"\\z\" r#bad";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(bad_source, FileId.fromInt(0), &token_buf, &sink, &interner);
    try std.testing.expectEqual(@as(u32, 10), sink.error_count);
    try std.testing.expectEqual(@as(u32, 1), sink.warning_count);

    var cst_arena = syntax_arenas.LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed_bad = try cst_arena.reconstructSource(
        std.testing.allocator,
        bad_source,
        &token_buf,
    );
    defer std.testing.allocator.free(reconstructed_bad);
    try std.testing.expectEqualStrings(bad_source, reconstructed_bad);

    // Verify `E0104` token limit exceeded preserves the entire unlexed tail byte-for-bit:
    const tail_source = "let a = 1; let b = 2; let c = 3; // trailing comment\n";
    var capped_buf = TokenBuffer.init(std.testing.allocator);
    defer capped_buf.deinit();
    var capped_sink = DiagnosticSink.init(std.testing.allocator);
    defer capped_sink.deinit();

    var capped_lexer = Lexer.initWithOptions(
        tail_source,
        FileId.fromInt(1),
        &capped_buf,
        &capped_sink,
        null,
        .{ .max_tokens = 4 },
    );
    try capped_lexer.tokenize();
    try std.testing.expectEqual(@as(usize, 4), capped_buf.countTokens());
    try std.testing.expectEqual(@as(u32, 1), capped_sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0104_token_limit_exceeded,
        capped_sink.asSlice()[0].code,
    );

    const reconstructed_capped = try cst_arena.reconstructSource(
        std.testing.allocator,
        tail_source,
        &capped_buf,
    );
    defer std.testing.allocator.free(reconstructed_capped);
    try std.testing.expectEqualStrings(tail_source, reconstructed_capped);
}

test "test_deep_nested_string_interpolation_bounded_stack_and_lossless" {
    const depth: usize = 600;
    var nested_builder: std.ArrayList(u8) = .empty;
    defer nested_builder.deinit(std.testing.allocator);
    try nested_builder.append(std.testing.allocator, '"');
    var i: usize = 0;
    while (i < depth) : (i += 1) {
        try nested_builder.appendSlice(std.testing.allocator, "{\"");
    }
    try nested_builder.appendSlice(std.testing.allocator, "leaf");
    i = 0;
    while (i < depth) : (i += 1) {
        try nested_builder.appendSlice(std.testing.allocator, "\"}");
    }
    try nested_builder.append(std.testing.allocator, '"');

    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try tokenize(nested_builder.items, FileId.fromInt(0), &token_buf, &sink, null);
    try std.testing.expectEqual(@as(u32, 1), sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0203_parse_depth_exceeded,
        sink.asSlice()[0].code,
    );

    var cst_arena = syntax_arenas.LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed = try cst_arena.reconstructSource(
        std.testing.allocator,
        nested_builder.items,
        &token_buf,
    );
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(nested_builder.items, reconstructed);

    // Unclosed 600-deep interpolation emits a single `E0203` and a single `E0102`:
    const unclosed_slice = nested_builder.items[0 .. depth * 2 + 1];
    var unclosed_buf = TokenBuffer.init(std.testing.allocator);
    defer unclosed_buf.deinit();
    var unclosed_sink = DiagnosticSink.init(std.testing.allocator);
    defer unclosed_sink.deinit();

    try tokenize(unclosed_slice, FileId.fromInt(0), &unclosed_buf, &unclosed_sink, null);
    try std.testing.expectEqual(@as(u32, 2), unclosed_sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0203_parse_depth_exceeded,
        unclosed_sink.asSlice()[0].code,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0102_unterminated_string_literal,
        unclosed_sink.asSlice()[1].code,
    );
}

test "test_trivia_accumulator_compaction_ripples_into_slot_14" {
    var acc = TriviaAccumulator{};
    var offset: u32 = 0;

    // Slot 0 has 1 byte; slots 1..15 each have 65,535 bytes:
    try std.testing.expectEqual(@as(u16, 1), acc.pushChunk(.spaces, offset, 1));
    offset += 1;
    var i: usize = 1;
    while (i < MAX_TRIVIA_SLOTS) : (i += 1) {
        try std.testing.expectEqual(
            MAX_TRIVIA_PIECE_BYTES,
            acc.pushChunk(.spaces, offset, MAX_TRIVIA_PIECE_BYTES),
        );
        offset += MAX_TRIVIA_PIECE_BYTES;
    }

    // Pushing 65,534 more bytes must succeed by rippling slot 0..14 left:
    const extra_chunk: u16 = MAX_TRIVIA_PIECE_BYTES - 1;
    try std.testing.expectEqual(extra_chunk, acc.pushChunk(.spaces, offset, extra_chunk));
    try std.testing.expect(acc.isCompletelyFull());
}

test "test_w0201_autofix_soundness_across_edge_case_identifiers" {
    const source = "lEt bit__field bitField sTr A_b A_1_b Self_ A_ A1_";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(source, FileId.fromInt(0), &token_buf, &sink, &interner);
    try std.testing.expectEqual(@as(u32, 9), sink.warning_count);

    var fixes: [9]SuggestedFix = undefined;
    for (sink.asSlice(), 0..) |diag_item, i| {
        try std.testing.expectEqual(
            DiagnosticCode.w0201_non_canonical_identifier_case,
            diag_item.code,
        );
        fixes[i] = diag_item.suggestions[0];
    }

    const patch_res = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        source,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 9), patch_res.applied_count);
    try std.testing.expectEqualStrings(
        "l_et bit_field_ bit_field_ s_tr Ab A1b SelfType A_0 A_1",
        patch_res.patched_source,
    );

    // Re-lex patched source and verify identical `TokenKind`s with zero `W0201` warnings:
    var relex_buf = TokenBuffer.init(std.testing.allocator);
    defer relex_buf.deinit();
    var relex_sink = DiagnosticSink.init(std.testing.allocator);
    defer relex_sink.deinit();

    try tokenize(patch_res.patched_source, FileId.fromInt(0), &relex_buf, &relex_sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), relex_sink.warning_count);
    try std.testing.expectEqual(@as(u32, 0), relex_sink.error_count);
    try std.testing.expectEqual(token_buf.countTokens(), relex_buf.countTokens());

    var i: u32 = 0;
    while (i < @as(u32, @intCast(token_buf.countTokens()))) : (i += 1) {
        const orig_tok = token_buf.getToken(TokenIndex.fromInt(i));
        const new_tok = relex_buf.getToken(TokenIndex.fromInt(i));
        try std.testing.expectEqual(orig_tok.kind, new_tok.kind);
        try std.testing.expect(!new_tok.flags.has_lexer_error);
    }
}

test "test_escaped_raw_newline_in_char_and_string_literals_and_cr_block_comment" {
    const char_source = "'\\\n'";
    var char_buf = TokenBuffer.init(std.testing.allocator);
    defer char_buf.deinit();
    var char_sink = DiagnosticSink.init(std.testing.allocator);
    defer char_sink.deinit();

    try tokenize(char_source, FileId.fromInt(0), &char_buf, &char_sink, null);
    try std.testing.expectEqual(@as(u32, 0), char_sink.warning_count);
    try std.testing.expect(char_sink.error_count >= 1);
    try std.testing.expectEqual(
        DiagnosticCode.e0102_unterminated_string_literal,
        char_sink.asSlice()[0].code,
    );

    const str_source = "\"hello \\\nworld \\\r\n!\" /* block\rcomment */ let ok = 1;";
    var str_buf = TokenBuffer.init(std.testing.allocator);
    defer str_buf.deinit();
    var str_sink = DiagnosticSink.init(std.testing.allocator);
    defer str_sink.deinit();

    try tokenize(str_source, FileId.fromInt(0), &str_buf, &str_sink, null);
    try std.testing.expectEqual(@as(u32, 0), str_sink.warning_count);
    try std.testing.expectEqual(@as(u32, 0), str_sink.error_count);
    try std.testing.expect(str_buf.getToken(TokenIndex.fromInt(1)).flags.has_leading_newline);
}

test "test_oversized_token_and_multimegabyte_tail_lossless_reconstruction" {
    // [1] Single token > 65,535 bytes (70,000-byte string literal) followed by `let a = 1;`:
    const big_token_len: usize = 70_000;
    var big_source = try std.testing.allocator.alloc(u8, big_token_len + 12);
    defer std.testing.allocator.free(big_source);
    big_source[0] = '"';
    @memset(big_source[1 .. big_token_len - 1], 'a');
    big_source[big_token_len - 1] = '"';
    @memcpy(big_source[big_token_len..], " let a = 1;\n");

    var big_buf = TokenBuffer.init(std.testing.allocator);
    defer big_buf.deinit();
    var big_sink = DiagnosticSink.init(std.testing.allocator);
    defer big_sink.deinit();

    try tokenize(big_source, FileId.fromInt(0), &big_buf, &big_sink, null);
    try std.testing.expectEqual(@as(u32, 0), big_sink.error_count);

    var cst_arena = syntax_arenas.LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed_big = try cst_arena.reconstructSource(
        std.testing.allocator,
        big_source,
        &big_buf,
    );
    defer std.testing.allocator.free(reconstructed_big);
    try std.testing.expectEqualSlices(u8, big_source, reconstructed_big);

    // [2] Multi-megabyte (2.2 MB) unlexed tail after `E0104` token limit exceeded:
    const tail_bytes: usize = 2_200_000;
    const huge_tail_source = try std.testing.allocator.alloc(u8, tail_bytes);
    defer std.testing.allocator.free(huge_tail_source);
    @memcpy(huge_tail_source[0..10], "let a = 1;");
    @memset(huge_tail_source[10..], ' ');

    var tail_buf = TokenBuffer.init(std.testing.allocator);
    defer tail_buf.deinit();
    var tail_sink = DiagnosticSink.init(std.testing.allocator);
    defer tail_sink.deinit();

    var tail_lexer = Lexer.initWithOptions(
        huge_tail_source,
        FileId.fromInt(0),
        &tail_buf,
        &tail_sink,
        null,
        .{ .max_tokens = 3 },
    );
    try tail_lexer.tokenize();
    try std.testing.expectEqual(@as(u32, 1), tail_sink.error_count);
    try std.testing.expectEqual(
        DiagnosticCode.e0104_token_limit_exceeded,
        tail_sink.asSlice()[0].code,
    );

    const reconstructed_tail = try cst_arena.reconstructSource(
        std.testing.allocator,
        huge_tail_source,
        &tail_buf,
    );
    defer std.testing.allocator.free(reconstructed_tail);
    try std.testing.expectEqualSlices(u8, huge_tail_source, reconstructed_tail);
}

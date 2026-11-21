//! High-Speed Deterministic Lexer & Lossless Trivia Scanner
//!
//! Scans UTF-8 source buffers into a contiguous Structure-of-Arrays (SoA) `TokenBuffer` in a single
//! non-backtracking $O(N)$ linear pass while enforcing the `DR-03`, `DR-21`, & `DR-22` 120-token lexical taxonomy.
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
const TypeId = mem_foundation.TypeId;
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

// --------------------- Format Specifiers ----------------------

/// Alignment mode encoded in bits `21..22` of `FmtSpec.flags_and_fill` (`DR-22` Section 2.2).
pub const FmtAlignMode = enum(u2) {
    /// Type-default alignment (left for strings, right for numbers).
    none = 0,
    /// Explicit left alignment (`<`).
    left = 1,
    /// Explicit center alignment (`^`).
    center = 2,
    /// Explicit right alignment (`>`).
    right = 3,
};

/// Sign display mode encoded in bits `23..24` of `FmtSpec.flags_and_fill` (`DR-22` Section 2.2).
pub const FmtSignMode = enum(u2) {
    /// Default sign behavior (`-` on negative values only).
    default = 0,
    /// Explicit leading `+` on non-negative numeric values (`+`).
    plus = 1,
    /// Explicit `-` sign mode (`-`).
    minus = 2,
};

/// Presentation verb encoded in bits `27..30` of `FmtSpec.flags_and_fill` (`DR-22` Section 2.2).
pub const FmtTypeCode = enum(u4) {
    /// Default `Display` formatting (empty verb).
    display = 0,
    /// Structured `Debug` formatting (`?`).
    debug = 1,
    /// Lowercase hexadecimal integer formatting (`x`).
    lower_hex = 2,
    /// Uppercase hexadecimal integer formatting (`X`).
    upper_hex = 3,
    /// Binary integer formatting (`b`).
    binary = 4,
    /// Octal integer formatting (`o`).
    octal = 5,
    /// Lowercase scientific notation formatting (`e`).
    lower_exp = 6,
    /// Uppercase scientific notation formatting (`E`).
    upper_exp = 7,
    /// Fixed-point decimal floating-point formatting (`f`).
    fixed = 8,
    /// Pointer address hexadecimal formatting (`p`).
    pointer = 9,
};

/// Exact 8-byte (`align 4`) compile-time format descriptor for `SE-12` `FmtArgs` (`DR-22` Section 2.2).
pub const FmtSpec = extern struct {
    /// Packed `u32`: `fill_char: u21` (`0..20`) | `align: u2` (`21..22`) | `sign: u2` (`23..24`) |
    /// `is_alt: u1` (`25`) | `is_zero_pad: u1` (`26`) | `type_code: u4` (`27..30`) | `is_debug_eq: u1` (`31`).
    flags_and_fill: u32 = 0x20,
    /// Minimum field width (`0..65534`), or `SPEC_NONE` (`0xFFFF`) when unspecified.
    width_or_none: u16 = SPEC_NONE,
    /// Floating-point/string precision (`0..65534`), or `SPEC_NONE` (`0xFFFF`) when unspecified.
    precision_or_none: u16 = SPEC_NONE,

    /// Sentinel `u16` value indicating an omitted width or precision field.
    pub const SPEC_NONE: u16 = 0xFFFF;
    /// Default `Display` format specification (`fill = ' '`, no width/precision).
    pub const DEFAULT: FmtSpec = .{};

    /// Packs all bitfields into a canonical 8-byte `FmtSpec` record.
    pub inline fn pack(
        fill_cp: u21,
        align_val: FmtAlignMode,
        sign_val: FmtSignMode,
        is_alt: bool,
        is_zero_pad: bool,
        verb: FmtTypeCode,
        is_debug_eq: bool,
        width_val: ?u16,
        precision_val: ?u16,
    ) FmtSpec {
        const packed_flags: u32 = @as(u32, fill_cp) |
            (@as(u32, @backingInt(align_val)) << 21) |
            (@as(u32, @backingInt(sign_val)) << 23) |
            (@as(u32, @intFromBool(is_alt)) << 25) |
            (@as(u32, @intFromBool(is_zero_pad)) << 26) |
            (@as(u32, @backingInt(verb)) << 27) |
            (@as(u32, @intFromBool(is_debug_eq)) << 31);
        return .{
            .flags_and_fill = packed_flags,
            .width_or_none = width_val orelse SPEC_NONE,
            .precision_or_none = precision_val orelse SPEC_NONE,
        };
    }

    /// Extracts the Unicode scalar fill character (`bits 0..20`, default `' '`).
    pub inline fn extractFillChar(self: FmtSpec) u21 {
        return @intCast(self.flags_and_fill & 0x1F_FFFF);
    }

    /// Extracts the alignment mode (`bits 21..22`).
    pub inline fn extractAlignMode(self: FmtSpec) FmtAlignMode {
        return @fromBackingInt(@intCast(@as(u2, @intCast((self.flags_and_fill >> 21) & 0x3))));
    }

    /// Extracts the sign mode (`bits 23..24`).
    pub inline fn extractSignMode(self: FmtSpec) FmtSignMode {
        return @fromBackingInt(@intCast(@as(u2, @intCast((self.flags_and_fill >> 23) & 0x3))));
    }

    /// Returns `true` if the alternate `#` flag (`bit 25`) is set.
    pub inline fn hasAltFlag(self: FmtSpec) bool {
        return ((self.flags_and_fill >> 25) & 0x1) != 0;
    }

    /// Returns `true` if the zero-padding `0` flag (`bit 26`) is set.
    pub inline fn hasZeroPad(self: FmtSpec) bool {
        return ((self.flags_and_fill >> 26) & 0x1) != 0;
    }

    /// Extracts the presentation type verb (`bits 27..30`).
    pub inline fn extractTypeCode(self: FmtSpec) FmtTypeCode {
        return @fromBackingInt(@intCast(@as(u4, @intCast((self.flags_and_fill >> 27) & 0xF))));
    }

    /// Returns `true` if self-debugging `=` (`bit 31`) was written on this interpolation hole.
    pub inline fn hasDebugEq(self: FmtSpec) bool {
        return ((self.flags_and_fill >> 31) & 0x1) != 0;
    }

    /// Returns the explicit width (`0..65534`), or `null` when `width_or_none == SPEC_NONE`.
    pub inline fn extractWidth(self: FmtSpec) ?u16 {
        return if (self.width_or_none == SPEC_NONE) null else self.width_or_none;
    }

    /// Returns the explicit precision (`0..65534`), or `null` when `precision_or_none == SPEC_NONE`.
    pub inline fn extractPrecision(self: FmtSpec) ?u16 {
        return if (self.precision_or_none == SPEC_NONE) null else self.precision_or_none;
    }
};

/// Zero-allocation decomposition of a numeric literal lexeme and its optional `SE-13` type suffix.
pub const ParsedNumericSuffix = struct {
    /// Leading numeric body slice excluding any `_` suffix separator and type suffix.
    digits_slice: []const u8,
    /// Trailing primitive suffix slice (e.g., `"u64"`, `"f32"`), or `""` when unsuffixed.
    suffix_slice: []const u8,
    /// Resolved primitive `TypeId` (`.i8_ty`..`.f64_ty`), or `null` when unsuffixed.
    suffix_type: ?TypeId,
    /// `true` if a `_` separator immediately preceded `suffix_slice` (`42_u64` vs. `42u64`).
    has_underscore_sep: bool,
    /// Integer radix (`2`, `8`, `10`, or `16`; always `10` for floating-point literals).
    radix: u8,
    /// `true` if `digits_slice` contains a fractional `.` or scientific `e`/`E` exponent.
    is_float_syntax: bool,
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
                self.pieces[i].flags |= syntax_arenas.TRIVIA_FLAG_COALESCED;
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
                self.pieces[i].flags |= syntax_arenas.TRIVIA_FLAG_COALESCED;
                self.pieces[i + 1].byte_offset += transfer_bytes;
                self.pieces[i + 1].byte_len -= transfer_bytes;
                self.pieces[i + 1].flags |= syntax_arenas.TRIVIA_FLAG_COALESCED;
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
            self.pieces[MAX_TRIVIA_SLOTS - 1].flags |= syntax_arenas.TRIVIA_FLAG_COALESCED;
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

/// Authoritative compile-time lookup map for all 50 language keywords and 20 primitive types (`DR-03`, `DR-21`, & `DR-22`).
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
    .{ "context", .kw_context },
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
    .{ "opaque", .prim_type },
    .{ "or", .kw_or },
    .{ "orelse", .kw_orelse },
    .{ "own", .kw_own },
    .{ "pub", .kw_pub },
    .{ "return", .kw_return },
    .{ "self", .kw_self_val },
    .{ "str", .prim_type },
    .{ "struct", .kw_struct },
    .{ "subscript", .kw_subscript },
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
    .{ "unreachable", .kw_unreachable },
    .{ "unsafe", .kw_unsafe },
    .{ "use", .kw_use },
    .{ "usize", .prim_type },
    .{ "var", .kw_var },
    .{ "where", .kw_where },
    .{ "while", .kw_while },
    .{ "with", .kw_with },
    .{ "yield", .kw_yield },
});

/// Authoritative compile-time lookup map for all 14 `SE-13` numeric literal type suffixes (`DR-22` Section 2.2).
pub const NUMERIC_SUFFIX_MAP = std.StaticStringMap(TypeId).initComptime(.{
    .{ "f32", .f32_ty },
    .{ "f64", .f64_ty },
    .{ "i128", .i128_ty },
    .{ "i16", .i16_ty },
    .{ "i32", .i32_ty },
    .{ "i64", .i64_ty },
    .{ "i8", .i8_ty },
    .{ "isize", .isize_ty },
    .{ "u128", .u128_ty },
    .{ "u16", .u16_ty },
    .{ "u32", .u32_ty },
    .{ "u64", .u64_ty },
    .{ "u8", .u8_ty },
    .{ "usize", .usize_ty },
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

/// Returns `true` if `byte_val` is `[a-zA-Z]` (excluding `'_'`) in $O(1)$ table lookup time.
inline fn isAsciiAlpha(byte_val: u8) bool {
    return isIdentStart(byte_val) and byte_val != '_';
}

/// Returns `true` if `source_bytes[start_pos..]` begins with at least `hash_count` `'#'` characters.
inline fn hasExactHashesAt(source_bytes: []const u8, start_pos: usize, hash_count: usize) bool {
    if (start_pos + hash_count > source_bytes.len) return false;
    var idx: usize = 0;
    while (idx < hash_count) : (idx += 1) {
        if (source_bytes[start_pos + idx] != '#') return false;
    }
    return true;
}

/// Returns `true` if `source_bytes[quote_pos..]` opens a `"""` multiline string rather than single-line `r#""…""#`.
inline fn isTripleQuoteOpening(
    source_bytes: []const u8,
    quote_pos: usize,
    is_raw: bool,
    hash_count: usize,
) bool {
    var quote_run: usize = 0;
    while (quote_pos + quote_run < source_bytes.len and source_bytes[quote_pos + quote_run] == '"') : (quote_run += 1) {}
    if (quote_run < 3) return false;
    if (is_raw and hash_count > 0 and hasExactHashesAt(source_bytes, quote_pos + quote_run, hash_count)) {
        return false;
    }
    return true;
}

/// Lexical context passed to `Lexer.scanEscapeSequence` to enforce mode-specific escape rules.
const EscapeContext = enum(u8) {
    /// Standard `"…"` or `"""…"""` UTF-8 string (`\{` / `\}` -> `E0114`, `\'` -> `W0101`, `\u{…}` valid).
    interpolated_string = 0,
    /// Unicode scalar `'c'` literal (`\"`, `\{`, `\}` -> `W0101`, `\u{…}` valid).
    char_literal = 1,
    /// Single ASCII byte `b'x'` literal (`\xHH` valid for `0x00..0xFF`, `\u{…}` -> `E0117`).
    byte_char = 2,
    /// ASCII byte string `b"…"` / `b"""…"""` (`\xHH` valid, `\u{…}` -> `E0117`, `\'` -> `W0101`).
    byte_string = 3,
};

/// Saved outer string frame for nested `{expr}` string interpolations (`[P1 Trap A]`).
const InterpStackFrame = struct {
    /// Active `{ … }` brace nesting depth at the moment the inner string opened.
    brace_depth: u32,
    /// `true` if the suspended outer string was opened by `"""` rather than `"`.
    is_triple_quote: bool,
    /// `true` if the suspended outer `"""` satisfied the immediate newline rule (`E0115`).
    has_valid_opening: bool,
    /// Byte offset of the suspended outer string's opening quote delimiter.
    open_quote_offset: u32,
    /// Byte offset immediately following the suspended outer string's opening delimiter/newline.
    body_start_offset: u32,
};

/// Decomposed delimiter metadata for any single-line or multiline string / byte-string lexeme.
const ParsedStringDelimiters = struct {
    /// Inner slice strictly between opening quote(s) and closing quote(s).
    raw_inner: []const u8,
    /// `true` if the literal uses raw `r` or `br` rules (no backslash escapes).
    is_raw: bool,
    /// `true` if the literal is a byte string (`b"…"`, `b"""…"""`, `br#"…"#`, `br#"""…"""#`).
    is_byte: bool,
    /// `true` if the literal uses triple-quote `"""` closing-quote dedent rules.
    is_triple_quote: bool,
};

/// Parses the prefix and matching quote/`#` delimiters of a string or byte-string `lexeme`.
fn parseStringDelimiters(lexeme: []const u8) ?ParsedStringDelimiters {
    if (lexeme.len < 2) return null;
    var cursor: usize = 0;
    var is_byte = false;
    var is_raw = false;

    if (lexeme[cursor] == 'b') {
        is_byte = true;
        cursor += 1;
    }
    if (cursor < lexeme.len and lexeme[cursor] == 'r') {
        is_raw = true;
        cursor += 1;
    }
    var hash_count: usize = 0;
    if (is_raw) {
        while (cursor < lexeme.len and lexeme[cursor] == '#') : (cursor += 1) {
            hash_count += 1;
        }
    }
    if (cursor >= lexeme.len or lexeme[cursor] != '"') return null;

    // Distinguish single-line `r#"""#` / `r#""""#` / `br#""""#` from multiline `r#"""\n…\n"""#`:
    const can_be_triple = cursor + 6 + hash_count <= lexeme.len and
        isTripleQuoteOpening(lexeme, cursor, is_raw, hash_count);

    const quote_len: usize = if (can_be_triple) 3 else 1;
    const suffix_len: usize = quote_len + hash_count;
    if (cursor + quote_len + suffix_len > lexeme.len) return null;
    if (!hasExactHashesAt(lexeme, lexeme.len - hash_count, hash_count)) return null;

    const close_quote_pos = lexeme.len - suffix_len;
    var q_idx: usize = 0;
    while (q_idx < quote_len) : (q_idx += 1) {
        if (lexeme[close_quote_pos + q_idx] != '"') return null;
    }

    return .{
        .raw_inner = lexeme[cursor + quote_len .. close_quote_pos],
        .is_raw = is_raw,
        .is_byte = is_byte,
        .is_triple_quote = can_be_triple,
    };
}

/// Counts consecutive trailing `\` bytes at the end of `line_slice`.
inline fn countTrailingBackslashes(line_slice: []const u8) usize {
    var count: usize = 0;
    while (count < line_slice.len and line_slice[line_slice.len - 1 - count] == '\\') {
        count += 1;
    }
    return count;
}

/// Advances past a `{expr}` interpolation hole inside `body_bytes` starting at `open_brace_idx`.
fn skipInterpolationHoleInBody(body_bytes: []const u8, open_brace_idx: usize) usize {
    var cursor = open_brace_idx + 1;
    var brace_depth: u32 = 1;
    while (cursor < body_bytes.len and brace_depth > 0) {
        const cur_byte = body_bytes[cursor];
        if (cur_byte == '{') {
            brace_depth += 1;
            cursor += 1;
        } else if (cur_byte == '}') {
            brace_depth -= 1;
            cursor += 1;
        } else if (cur_byte == 'r' and
            (cursor == 0 or !isIdentContinue(body_bytes[cursor - 1])) and
            cursor + 1 < body_bytes.len and
            (body_bytes[cursor + 1] == '"' or body_bytes[cursor + 1] == '#'))
        {
            cursor = skipRawStringInExpr(body_bytes, cursor + 1);
        } else if (cur_byte == 'b' and (cursor == 0 or !isIdentContinue(body_bytes[cursor - 1])) and
            cursor + 1 < body_bytes.len)
        {
            if (body_bytes[cursor + 1] == '\'') {
                cursor = skipQuotedNonRawInExpr(body_bytes, cursor + 2, '\'', false);
            } else if (body_bytes[cursor + 1] == '"') {
                const is_triple = cursor + 3 < body_bytes.len and
                    body_bytes[cursor + 2] == '"' and
                    body_bytes[cursor + 3] == '"';
                cursor = skipQuotedNonRawInExpr(body_bytes, cursor + (if (is_triple) @as(usize, 4) else 2), '"', is_triple);
            } else if (body_bytes[cursor + 1] == 'r' and cursor + 2 < body_bytes.len and
                (body_bytes[cursor + 2] == '"' or body_bytes[cursor + 2] == '#'))
            {
                cursor = skipRawStringInExpr(body_bytes, cursor + 2);
            } else {
                cursor += 1;
            }
        } else if (cur_byte == '"') {
            const is_triple = cursor + 2 < body_bytes.len and
                body_bytes[cursor + 1] == '"' and
                body_bytes[cursor + 2] == '"';
            cursor = skipInterpolatedStringInExpr(body_bytes, cursor + (if (is_triple) @as(usize, 3) else 1), is_triple);
        } else if (cur_byte == '\'') {
            cursor = skipQuotedNonRawInExpr(body_bytes, cursor + 1, '\'', false);
        } else if (cur_byte == '/' and cursor + 1 < body_bytes.len) {
            if (body_bytes[cursor + 1] == '/') {
                cursor += 2;
                while (cursor < body_bytes.len and body_bytes[cursor] != '\n' and body_bytes[cursor] != '\r') {
                    cursor += 1;
                }
            } else if (body_bytes[cursor + 1] == '*') {
                cursor += 2;
                var comment_depth: u32 = 1;
                while (cursor < body_bytes.len and comment_depth > 0) {
                    if (body_bytes[cursor] == '/' and cursor + 1 < body_bytes.len and body_bytes[cursor + 1] == '*') {
                        comment_depth += 1;
                        cursor += 2;
                    } else if (body_bytes[cursor] == '*' and cursor + 1 < body_bytes.len and body_bytes[cursor + 1] == '/') {
                        comment_depth -= 1;
                        cursor += 2;
                    } else {
                        cursor += 1;
                    }
                }
            } else {
                cursor += 1;
            }
        } else {
            cursor += 1;
        }
    }
    return cursor;
}

/// Skips a non-interpolated `'…'`, `b'…'`, `b"…"`, or `b"""…"""` literal inside an `{expr}` scan.
fn skipQuotedNonRawInExpr(body_bytes: []const u8, after_open_idx: usize, quote_byte: u8, is_triple: bool) usize {
    var cursor = after_open_idx;
    while (cursor < body_bytes.len) {
        if (body_bytes[cursor] == '\\') {
            cursor = @min(cursor + 2, body_bytes.len);
            continue;
        }
        if (body_bytes[cursor] == quote_byte) {
            if (is_triple) {
                if (cursor + 2 < body_bytes.len and
                    body_bytes[cursor + 1] == quote_byte and
                    body_bytes[cursor + 2] == quote_byte)
                {
                    return cursor + 3;
                }
                cursor += 1;
                continue;
            }
            return cursor + 1;
        }
        cursor += 1;
    }
    return body_bytes.len;
}

/// Skips a raw `r#"…"#` or `r#"""…"""#` string literal inside an `{expr}` scan (`after_r_idx` points past `'r'`).
fn skipRawStringInExpr(body_bytes: []const u8, after_r_idx: usize) usize {
    var cursor = after_r_idx;
    var hash_count: usize = 0;
    while (cursor < body_bytes.len and body_bytes[cursor] == '#') : (cursor += 1) {
        hash_count += 1;
    }
    if (cursor >= body_bytes.len or body_bytes[cursor] != '"') return cursor;
    const is_triple = isTripleQuoteOpening(body_bytes, cursor, true, hash_count);
    const quote_len: usize = if (is_triple) 3 else 1;
    cursor += quote_len;

    while (cursor < body_bytes.len) {
        if (body_bytes[cursor] == '"') {
            if (is_triple) {
                if (cursor + 2 < body_bytes.len and
                    body_bytes[cursor + 1] == '"' and
                    body_bytes[cursor + 2] == '"' and
                    hasExactHashesAt(body_bytes, cursor + 3, hash_count))
                {
                    return cursor + 3 + hash_count;
                }
                cursor += 1;
                continue;
            }
            if (hasExactHashesAt(body_bytes, cursor + 1, hash_count)) {
                return cursor + 1 + hash_count;
            }
        }
        cursor += 1;
    }
    return body_bytes.len;
}

/// Skips an interpolated `"…"` or `"""…"""` literal nested inside an `{expr}` scan.
fn skipInterpolatedStringInExpr(body_bytes: []const u8, after_open_idx: usize, is_triple: bool) usize {
    var cursor = after_open_idx;
    while (cursor < body_bytes.len) {
        const cur_byte = body_bytes[cursor];
        if (cur_byte == '\\') {
            cursor = @min(cursor + 2, body_bytes.len);
            continue;
        }
        if (cur_byte == '"') {
            if (is_triple) {
                if (cursor + 2 < body_bytes.len and body_bytes[cursor + 1] == '"' and body_bytes[cursor + 2] == '"') {
                    return cursor + 3;
                }
                cursor += 1;
                continue;
            }
            return cursor + 1;
        }
        if (cur_byte == '{') {
            if (cursor + 1 < body_bytes.len and body_bytes[cursor + 1] == '{') {
                cursor += 2;
                continue;
            }
            cursor = skipInterpolationHoleInBody(body_bytes, cursor);
            continue;
        }
        cursor += 1;
    }
    return body_bytes.len;
}

/// Scans `body_after_open_nl` for the next outer line break (`\n`), skipping `{expr}` holes when enabled.
fn findNextOuterLineFeed(
    body_bytes: []const u8,
    start_pos: usize,
    is_raw: bool,
    is_interpolation_allowed: bool,
) ?usize {
    var cursor = start_pos;
    while (cursor < body_bytes.len) {
        const cur_byte = body_bytes[cursor];
        if (cur_byte == '\n') return cursor;
        if (!is_raw and cur_byte == '\\' and cursor + 1 < body_bytes.len) {
            const next_byte = body_bytes[cursor + 1];
            if (next_byte != '\n' and next_byte != '\r') {
                cursor += 2;
                continue;
            }
        }
        if (is_interpolation_allowed and !is_raw and cur_byte == '{') {
            if (cursor + 1 < body_bytes.len and body_bytes[cursor + 1] == '{') {
                cursor += 2;
                continue;
            }
            cursor = skipInterpolationHoleInBody(body_bytes, cursor);
            continue;
        }
        cursor += 1;
    }
    return null;
}

/// Validates (and optionally materializes into `maybe_out`) a multiline string body after its opening newline.
fn processMultilineStringBody(
    body_after_open_nl: []const u8,
    is_raw: bool,
    is_interpolation_allowed: bool,
    allocator: ?std.mem.Allocator,
    maybe_out: ?*std.ArrayList(u8),
) error{ InvalidMultilineIndent, OutOfMemory }!void {
    // [1] Locate the last outer `\n` separating content lines from the closing `"""` indentation prefix:
    var last_outer_lf: ?usize = null;
    var scan_pos: usize = 0;
    while (findNextOuterLineFeed(body_after_open_nl, scan_pos, is_raw, is_interpolation_allowed)) |lf_pos| {
        last_outer_lf = lf_pos;
        scan_pos = lf_pos + 1;
    }

    const close_prefix = if (last_outer_lf) |lf_idx|
        body_after_open_nl[lf_idx + 1 ..]
    else
        body_after_open_nl;

    // Closing `"""` must sit on its own line preceded exclusively by `' '` spaces (`W_close`):
    for (close_prefix) |prefix_byte| {
        if (prefix_byte != ' ') return error.InvalidMultilineIndent;
    }
    const close_indent: usize = close_prefix.len;

    // Zero content lines (`"""\n    """`): valid empty string!
    const final_lf_idx = last_outer_lf orelse return;
    const content_end: usize = if (final_lf_idx > 0 and body_after_open_nl[final_lf_idx - 1] == '\r')
        final_lf_idx - 1
    else
        final_lf_idx;
    const content_bytes = body_after_open_nl[0..content_end];

    // [2] Validate `W_close` and zero space/tab mixing on every content line (materializing if requested):
    var line_start: usize = 0;
    while (true) {
        const maybe_lf = findNextOuterLineFeed(content_bytes, line_start, is_raw, is_interpolation_allowed);
        const raw_line_end = maybe_lf orelse content_bytes.len;
        const clean_line_end = if (raw_line_end > line_start and content_bytes[raw_line_end - 1] == '\r')
            raw_line_end - 1
        else
            raw_line_end;
        const line_slice = content_bytes[line_start..clean_line_end];

        if (line_slice.len > 0) {
            if (line_slice.len < close_indent) return error.InvalidMultilineIndent;
            var ws_idx: usize = 0;
            var has_leading_space = false;
            var has_leading_tab = false;
            while (ws_idx < line_slice.len and (line_slice[ws_idx] == ' ' or line_slice[ws_idx] == '\t')) : (ws_idx += 1) {
                if (line_slice[ws_idx] == ' ') {
                    has_leading_space = true;
                } else {
                    has_leading_tab = true;
                }
            }
            if (has_leading_space and has_leading_tab) return error.InvalidMultilineIndent;
            if (close_indent > 0 and ws_idx < close_indent) return error.InvalidMultilineIndent;
            if (close_indent > 0 and has_leading_tab) return error.InvalidMultilineIndent;

            var dedented_slice = line_slice[close_indent..];
            const has_line_continuation = !is_raw and (countTrailingBackslashes(dedented_slice) % 2 == 1);
            if (has_line_continuation) {
                dedented_slice = dedented_slice[0 .. dedented_slice.len - 1];
            }
            if (maybe_out) |out_buf| {
                const alloc = allocator.?;
                try out_buf.appendSlice(alloc, dedented_slice);
                if (maybe_lf != null and !has_line_continuation) {
                    try out_buf.append(alloc, '\n');
                }
            }
        } else if (maybe_out) |out_buf| {
            if (maybe_lf != null) {
                try out_buf.append(allocator.?, '\n');
            }
        }

        if (maybe_lf) |lf_pos| {
            line_start = lf_pos + 1;
        } else {
            break;
        }
    }
}

/// Decodes backslash escape sequences (and `{{`/`}}` when `is_interpolated`) into `out_buf`.
fn decodeEscapedStringSlice(
    allocator: std.mem.Allocator,
    raw_slice: []const u8,
    is_byte_mode: bool,
    is_interpolated: bool,
    out_buf: *std.ArrayList(u8),
) error{ InvalidStringLiteral, OutOfMemory }!void {
    var cursor: usize = 0;
    while (cursor < raw_slice.len) {
        if (raw_slice[cursor] == '\\') {
            if (cursor + 1 >= raw_slice.len) return error.InvalidStringLiteral;
            const esc_byte = raw_slice[cursor + 1];
            switch (esc_byte) {
                'n' => {
                    try out_buf.append(allocator, '\n');
                    cursor += 2;
                },
                'r' => {
                    try out_buf.append(allocator, '\r');
                    cursor += 2;
                },
                't' => {
                    try out_buf.append(allocator, '\t');
                    cursor += 2;
                },
                '0' => {
                    try out_buf.append(allocator, 0);
                    cursor += 2;
                },
                '\\', '"', '\'' => {
                    try out_buf.append(allocator, esc_byte);
                    cursor += 2;
                },
                '\n' => {
                    cursor += 2;
                },
                '\r' => {
                    cursor += if (cursor + 2 < raw_slice.len and raw_slice[cursor + 2] == '\n') 3 else 2;
                },
                'x' => {
                    if (cursor + 3 >= raw_slice.len or
                        !isHexDigit(raw_slice[cursor + 2]) or
                        !isHexDigit(raw_slice[cursor + 3]))
                    {
                        return error.InvalidStringLiteral;
                    }
                    const decoded_byte: u8 = @intCast(
                        (hexDigitValue(raw_slice[cursor + 2]) << 4) | hexDigitValue(raw_slice[cursor + 3]),
                    );
                    try out_buf.append(allocator, decoded_byte);
                    cursor += 4;
                },
                'u' => {
                    if (is_byte_mode or cursor + 3 >= raw_slice.len or raw_slice[cursor + 2] != '{') {
                        return error.InvalidStringLiteral;
                    }
                    const close_pos = std.mem.indexOfScalarPos(u8, raw_slice, cursor + 3, '}') orelse
                        return error.InvalidStringLiteral;
                    const hex_digits = raw_slice[cursor + 3 .. close_pos];
                    if (hex_digits.len == 0 or hex_digits.len > 6) return error.InvalidStringLiteral;
                    var scalar_val: u32 = 0;
                    for (hex_digits) |digit_byte| {
                        if (!isHexDigit(digit_byte)) return error.InvalidStringLiteral;
                        scalar_val = (scalar_val << 4) | @as(u32, hexDigitValue(digit_byte));
                    }
                    if (scalar_val > 0x10FFFF or !std.unicode.utf8ValidCodepoint(@intCast(scalar_val))) {
                        return error.InvalidStringLiteral;
                    }
                    var utf8_bytes: [4]u8 = undefined;
                    const encoded_len = std.unicode.utf8Encode(@intCast(scalar_val), &utf8_bytes) catch
                        return error.InvalidStringLiteral;
                    try out_buf.appendSlice(allocator, utf8_bytes[0..encoded_len]);
                    cursor = close_pos + 1;
                },
                '{', '}' => {
                    if (is_interpolated) return error.InvalidStringLiteral;
                    try out_buf.append(allocator, esc_byte);
                    cursor += 2;
                },
                else => {
                    try out_buf.append(allocator, esc_byte);
                    cursor += 2;
                },
            }
            continue;
        }
        if (is_interpolated and (raw_slice[cursor] == '{' or raw_slice[cursor] == '}')) {
            if (cursor + 1 >= raw_slice.len or raw_slice[cursor + 1] != raw_slice[cursor]) {
                return error.InvalidStringLiteral;
            }
            try out_buf.append(allocator, raw_slice[cursor]);
            cursor += 2;
            continue;
        }
        if (is_byte_mode and raw_slice[cursor] >= 0x80) {
            return error.InvalidStringLiteral;
        }
        try out_buf.append(allocator, raw_slice[cursor]);
        cursor += 1;
    }
}

/// Parses an unsigned decimal integer (`0..65534`) at `spec_text[cursor..]` for `parseFormatSpec`.
fn parseFormatSpecU16(spec_text: []const u8, cursor: *usize) error{InvalidFormatSpec}!u16 {
    if (cursor.* >= spec_text.len or !isDecimalDigit(spec_text[cursor.*])) {
        return error.InvalidFormatSpec;
    }
    var acc_val: u32 = 0;
    var is_prev_underscore = false;
    while (cursor.* < spec_text.len) {
        const cur_byte = spec_text[cursor.*];
        if (isDecimalDigit(cur_byte)) {
            acc_val = acc_val * 10 + @as(u32, cur_byte - '0');
            if (acc_val >= FmtSpec.SPEC_NONE) return error.InvalidFormatSpec;
            is_prev_underscore = false;
            cursor.* += 1;
        } else if (cur_byte == '_') {
            if (is_prev_underscore) return error.InvalidFormatSpec;
            is_prev_underscore = true;
            cursor.* += 1;
        } else {
            break;
        }
    }
    if (is_prev_underscore) return error.InvalidFormatSpec;
    return @intCast(acc_val);
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
    std.debug.assert(KEYWORD_OR_PRIM_MAP.keys().len == 70);
    std.debug.assert(NUMERIC_SUFFIX_MAP.keys().len == 14);
    std.debug.assert(@sizeOf(FmtSpec) == 8);
    std.debug.assert(@alignOf(FmtSpec) == 4);
}

// ------------------------------------- PUBLIC API --------------------------------------

// --------------------- Identifier Casing ----------------------

/// Looks up `lexeme` in the compile-time table of 50 language keywords and 20 primitive types.
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

    // [1] Standalone `_` wildcard token (`77`):
    if (lexeme.len == 1 and lexeme[0] == '_') {
        return .{
            .kind = .underscore,
            .expected_case = .reserved_or_wildcard,
            .case_style = .reserved_or_wildcard,
            .is_canonical = true,
            .has_case_violation = false,
        };
    }

    // [2] Reserved language keywords (`0..48`) and primitive types (`49`):
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

    // [4] Lowercase or leading-underscore identifiers (`len >= 2`) always classify as `.ident` (`50`):
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

    // [5] Uppercase-initial with lowercase or single capital without `_` (`T`, `V4`) -> `.type_ident` (`51`):
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

    // [6] All-caps with `upper_count >= 2` or `_` (`MAX_SIZE`, `PI_2`, `IO`) -> `.const_ident` (`52`):
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

// ------------------ Numeric & String Helpers ------------------

/// Parses a `SE-12` `FormatSpec` slice (`[ [FillChar] Align ] [Sign] [#] [0] [Width] [.Prec] [Type]`)
/// into a packed 8-byte `FmtSpec` record (`DR-22` Section 2.2).
pub fn parseFormatSpec(spec_text: []const u8, has_debug_eq: bool) error{InvalidFormatSpec}!FmtSpec {
    var cursor: usize = 0;
    var fill_cp: u21 = ' ';
    var align_mode: FmtAlignMode = .none;

    // [1] Optional `[ FillChar ] ( "<" | "^" | ">" )`:
    if (cursor < spec_text.len) {
        const first_len = std.unicode.utf8ByteSequenceLength(spec_text[cursor]) catch
            return error.InvalidFormatSpec;
        if (cursor + first_len <= spec_text.len and cursor + first_len < spec_text.len) {
            const second_byte = spec_text[cursor + first_len];
            if (second_byte == '<' or second_byte == '^' or second_byte == '>') {
                fill_cp = std.unicode.utf8Decode(spec_text[cursor .. cursor + first_len]) catch
                    return error.InvalidFormatSpec;
                align_mode = switch (second_byte) {
                    '<' => .left,
                    '^' => .center,
                    '>' => .right,
                    else => unreachable,
                };
                cursor += first_len + 1;
            }
        }
        if (align_mode == .none) {
            switch (spec_text[cursor]) {
                '<' => {
                    align_mode = .left;
                    cursor += 1;
                },
                '^' => {
                    align_mode = .center;
                    cursor += 1;
                },
                '>' => {
                    align_mode = .right;
                    cursor += 1;
                },
                else => {},
            }
        }
    }

    // [2] Optional sign (`+` | `-`), alternate `#`, and zero-padding `0`:
    var sign_mode: FmtSignMode = .default;
    if (cursor < spec_text.len) {
        if (spec_text[cursor] == '+') {
            sign_mode = .plus;
            cursor += 1;
        } else if (spec_text[cursor] == '-') {
            sign_mode = .minus;
            cursor += 1;
        }
    }

    var is_alt = false;
    if (cursor < spec_text.len and spec_text[cursor] == '#') {
        is_alt = true;
        cursor += 1;
    }

    var is_zero_pad = false;
    if (cursor < spec_text.len and spec_text[cursor] == '0') {
        is_zero_pad = true;
        cursor += 1;
    }

    // [3] Optional minimum `Width` (`0..65534`) and `.Precision` (`0..65534`):
    var width_val: ?u16 = null;
    if (cursor < spec_text.len and isDecimalDigit(spec_text[cursor])) {
        width_val = try parseFormatSpecU16(spec_text, &cursor);
    }

    var precision_val: ?u16 = null;
    if (cursor < spec_text.len and spec_text[cursor] == '.') {
        cursor += 1;
        precision_val = try parseFormatSpecU16(spec_text, &cursor);
    }

    // [4] Optional presentation verb (`?`, `x`, `X`, `b`, `o`, `e`, `E`, `f`, `p`):
    var verb: FmtTypeCode = if (has_debug_eq) .debug else .display;
    if (cursor < spec_text.len) {
        verb = switch (spec_text[cursor]) {
            '?' => .debug,
            'x' => .lower_hex,
            'X' => .upper_hex,
            'b' => .binary,
            'o' => .octal,
            'e' => .lower_exp,
            'E' => .upper_exp,
            'f' => .fixed,
            'p' => .pointer,
            else => return error.InvalidFormatSpec,
        };
        cursor += 1;
    }

    if (cursor != spec_text.len) return error.InvalidFormatSpec;
    return FmtSpec.pack(
        fill_cp,
        align_mode,
        sign_mode,
        is_alt,
        is_zero_pad,
        verb,
        has_debug_eq,
        width_val,
        precision_val,
    );
}

/// Decomposes an `INT_LIT` or `FLOAT_LIT` `lexeme` into its numeric digits and optional `SE-13` primitive suffix.
pub fn extractNumericSuffix(lexeme: []const u8) error{InvalidNumericSuffix}!ParsedNumericSuffix {
    if (lexeme.len == 0 or !isDecimalDigit(lexeme[0])) return error.InvalidNumericSuffix;

    // [1] Non-decimal radix (`0x`, `0b`, `0o`):
    if (lexeme[0] == '0' and lexeme.len >= 2) {
        const maybe_radix: ?u8 = switch (lexeme[1]) {
            'x', 'X' => 16,
            'b', 'B' => 2,
            'o', 'O' => 8,
            else => null,
        };
        if (maybe_radix) |radix| {
            var cursor: usize = 2;
            var digit_count: usize = 0;
            var is_prev_underscore = false;
            if (cursor < lexeme.len and lexeme[cursor] == '_') return error.InvalidNumericSuffix;

            while (cursor < lexeme.len) {
                const cur_byte = lexeme[cursor];
                if (isValidDigitForRadix(cur_byte, radix)) {
                    digit_count += 1;
                    is_prev_underscore = false;
                    cursor += 1;
                } else if (cur_byte == '_') {
                    if (!is_prev_underscore and
                        digit_count > 0 and
                        cursor + 1 < lexeme.len and
                        isAsciiAlpha(lexeme[cursor + 1]) and
                        !isValidDigitForRadix(lexeme[cursor + 1], radix))
                    {
                        break;
                    }
                    if (is_prev_underscore) return error.InvalidNumericSuffix;
                    is_prev_underscore = true;
                    cursor += 1;
                } else {
                    break;
                }
            }
            if (digit_count == 0 or is_prev_underscore) return error.InvalidNumericSuffix;

            const digits_end = cursor;
            if (cursor == lexeme.len) {
                return .{
                    .digits_slice = lexeme,
                    .suffix_slice = "",
                    .suffix_type = null,
                    .has_underscore_sep = false,
                    .radix = radix,
                    .is_float_syntax = false,
                };
            }

            var has_sep = false;
            if (lexeme[cursor] == '_') {
                has_sep = true;
                cursor += 1;
            }
            const suffix_slice = lexeme[cursor..];
            const suffix_ty = NUMERIC_SUFFIX_MAP.get(suffix_slice) orelse return error.InvalidNumericSuffix;
            if (suffix_ty == .f32_ty or suffix_ty == .f64_ty) return error.InvalidNumericSuffix;
            return .{
                .digits_slice = lexeme[0..digits_end],
                .suffix_slice = suffix_slice,
                .suffix_type = suffix_ty,
                .has_underscore_sep = has_sep,
                .radix = radix,
                .is_float_syntax = false,
            };
        }
    }

    // [2] Base-10 integer or floating-point literal:
    var cursor: usize = 0;
    var is_prev_underscore = false;
    while (cursor < lexeme.len) {
        const cur_byte = lexeme[cursor];
        if (isDecimalDigit(cur_byte)) {
            is_prev_underscore = false;
            cursor += 1;
        } else if (cur_byte == '_') {
            if (!is_prev_underscore and cursor + 1 < lexeme.len and isAsciiAlpha(lexeme[cursor + 1])) {
                break;
            }
            if (is_prev_underscore) return error.InvalidNumericSuffix;
            is_prev_underscore = true;
            cursor += 1;
        } else {
            break;
        }
    }
    if (is_prev_underscore) return error.InvalidNumericSuffix;

    var is_float_syntax = false;
    if (cursor + 1 < lexeme.len and lexeme[cursor] == '.' and isDecimalDigit(lexeme[cursor + 1])) {
        is_float_syntax = true;
        cursor += 1;
        while (cursor < lexeme.len) {
            const cur_byte = lexeme[cursor];
            if (isDecimalDigit(cur_byte)) {
                is_prev_underscore = false;
                cursor += 1;
            } else if (cur_byte == '_') {
                if (!is_prev_underscore and cursor + 1 < lexeme.len and isAsciiAlpha(lexeme[cursor + 1])) {
                    break;
                }
                if (is_prev_underscore) return error.InvalidNumericSuffix;
                is_prev_underscore = true;
                cursor += 1;
            } else {
                break;
            }
        }
        if (is_prev_underscore) return error.InvalidNumericSuffix;
    }

    if (cursor < lexeme.len and (lexeme[cursor] == 'e' or lexeme[cursor] == 'E')) {
        is_float_syntax = true;
        cursor += 1;
        if (cursor < lexeme.len and (lexeme[cursor] == '+' or lexeme[cursor] == '-')) {
            cursor += 1;
        }
        if (cursor >= lexeme.len or lexeme[cursor] == '_') return error.InvalidNumericSuffix;
        var exp_digits: usize = 0;
        while (cursor < lexeme.len) {
            const cur_byte = lexeme[cursor];
            if (isDecimalDigit(cur_byte)) {
                exp_digits += 1;
                is_prev_underscore = false;
                cursor += 1;
            } else if (cur_byte == '_') {
                if (!is_prev_underscore and
                    exp_digits > 0 and
                    cursor + 1 < lexeme.len and
                    isAsciiAlpha(lexeme[cursor + 1]))
                {
                    break;
                }
                if (is_prev_underscore) return error.InvalidNumericSuffix;
                is_prev_underscore = true;
                cursor += 1;
            } else {
                break;
            }
        }
        if (exp_digits == 0 or is_prev_underscore) return error.InvalidNumericSuffix;
    }

    const digits_end = cursor;
    if (cursor == lexeme.len) {
        return .{
            .digits_slice = lexeme,
            .suffix_slice = "",
            .suffix_type = null,
            .has_underscore_sep = false,
            .radix = 10,
            .is_float_syntax = is_float_syntax,
        };
    }

    var has_sep = false;
    if (lexeme[cursor] == '_') {
        has_sep = true;
        cursor += 1;
    }
    const suffix_slice = lexeme[cursor..];
    const suffix_ty = NUMERIC_SUFFIX_MAP.get(suffix_slice) orelse return error.InvalidNumericSuffix;
    if (is_float_syntax and suffix_ty != .f32_ty and suffix_ty != .f64_ty) {
        return error.InvalidNumericSuffix;
    }
    return .{
        .digits_slice = lexeme[0..digits_end],
        .suffix_slice = suffix_slice,
        .suffix_type = suffix_ty,
        .has_underscore_sep = has_sep,
        .radix = 10,
        .is_float_syntax = is_float_syntax,
    };
}

/// Returns `true` if `lexeme` is a triple-quoted multiline string or byte-string literal (`"""…"""`).
pub inline fn isMultilineStringLexeme(lexeme: []const u8) bool {
    const parsed = parseStringDelimiters(lexeme) orelse return false;
    return parsed.is_triple_quote;
}

/// Extracts and closing-quote dedents a `"""…"""`, `r#"""…"""#`, `b"""…"""`, or `br#"""…"""#` `lexeme`
/// without decoding `\n` / `\xHH` / `{{` escapes (preserving `{expr}` holes for downstream Sema/HIR).
pub fn extractMultilineStringContent(
    allocator: std.mem.Allocator,
    lexeme: []const u8,
) error{ InvalidMultilineOpening, InvalidMultilineIndent, InvalidStringLiteral, OutOfMemory }![]u8 {
    const parsed = parseStringDelimiters(lexeme) orelse return error.InvalidStringLiteral;
    if (!parsed.is_triple_quote) return error.InvalidStringLiteral;

    var after_open_nl: usize = 0;
    if (parsed.raw_inner.len >= 1 and parsed.raw_inner[0] == '\n') {
        after_open_nl = 1;
    } else if (parsed.raw_inner.len >= 2 and parsed.raw_inner[0] == '\r' and parsed.raw_inner[1] == '\n') {
        after_open_nl = 2;
    } else {
        return error.InvalidMultilineOpening;
    }

    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try out_buf.ensureTotalCapacity(allocator, parsed.raw_inner.len - after_open_nl);
    try processMultilineStringBody(
        parsed.raw_inner[after_open_nl..],
        parsed.is_raw,
        !parsed.is_raw and !parsed.is_byte,
        allocator,
        &out_buf,
    );
    return out_buf.toOwnedSlice(allocator);
}

/// Canonical alias for `extractMultilineStringContent`.
pub const extractMultilineString = extractMultilineStringContent;

/// Fully cooks any non-interpolated string or byte-string `lexeme` (`"…"`, `"""…"""`, `r#"…"#`,
/// `r#"""…"""#`, `b"…"`, `b"""…"""`, `br#"…"#`, `br#"""…"""#`), applying multiline dedent and escape decoding.
pub fn cookStringLiteral(
    allocator: std.mem.Allocator,
    lexeme: []const u8,
) error{ InvalidMultilineOpening, InvalidMultilineIndent, InvalidStringLiteral, OutOfMemory }![]u8 {
    const parsed = parseStringDelimiters(lexeme) orelse return error.InvalidStringLiteral;

    if (parsed.is_triple_quote) {
        const dedented = try extractMultilineStringContent(allocator, lexeme);
        if (parsed.is_raw) {
            if (parsed.is_byte) {
                for (dedented) |raw_byte| {
                    if (raw_byte >= 0x80) {
                        allocator.free(dedented);
                        return error.InvalidStringLiteral;
                    }
                }
            }
            return dedented;
        }
        defer allocator.free(dedented);
        var out_buf: std.ArrayList(u8) = .empty;
        errdefer out_buf.deinit(allocator);
        try out_buf.ensureTotalCapacity(allocator, dedented.len);
        try decodeEscapedStringSlice(allocator, dedented, parsed.is_byte, !parsed.is_byte, &out_buf);
        return out_buf.toOwnedSlice(allocator);
    }

    if (parsed.is_raw) {
        if (parsed.is_byte) {
            for (parsed.raw_inner) |raw_byte| {
                if (raw_byte >= 0x80) return error.InvalidStringLiteral;
            }
        }
        return allocator.dupe(u8, parsed.raw_inner);
    }

    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try out_buf.ensureTotalCapacity(allocator, parsed.raw_inner.len);
    try decodeEscapedStringSlice(allocator, parsed.raw_inner, parsed.is_byte, !parsed.is_byte, &out_buf);
    return out_buf.toOwnedSlice(allocator);
}

/// Decodes a single-byte `b'x'` literal `lexeme` (`0x00..0x7F` or `\xHH`/`\n`/`\r`/`\t`/`\0`/`\\`/`\'`) into `u8`.
pub fn extractByteLiteralValue(lexeme: []const u8) ?u8 {
    if (lexeme.len < 4 or lexeme[0] != 'b' or lexeme[1] != '\'' or lexeme[lexeme.len - 1] != '\'') {
        return null;
    }
    const body = lexeme[2 .. lexeme.len - 1];
    if (body.len == 1) {
        if (body[0] == '\\' or body[0] == '\'' or body[0] == '\n' or body[0] == '\r' or body[0] >= 0x80) {
            return null;
        }
        return body[0];
    }
    if (body[0] != '\\') return null;
    if (body.len == 2) {
        return switch (body[1]) {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '0' => 0,
            '\\' => '\\',
            '\'' => '\'',
            '"' => '"',
            else => if (body[1] < 0x80 and body[1] != 'x' and body[1] != 'u' and body[1] != '\n' and body[1] != '\r')
                body[1]
            else
                null,
        };
    }
    if (body.len == 4 and body[1] == 'x' and isHexDigit(body[2]) and isHexDigit(body[3])) {
        return @intCast((hexDigitValue(body[2]) << 4) | hexDigitValue(body[3]));
    }
    return null;
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
    /// Optional diagnostic sink receiving `E0101`–`E0117`, `W0101`, and `W0201` diagnostics.
    diagnostic_sink: ?*DiagnosticSink,
    /// Optional string interner used to intern `SuggestedFix` replacement text.
    interner: ?*StringInterner,
    /// Resource cap and warning configuration options.
    options: LexerOptions = .{},
    /// Current byte cursor into `source`.
    cursor: usize = 0,
    /// Leading trivia accumulator for the upcoming token.
    trivia_acc: TriviaAccumulator = .{},
    /// Kind of the immediately preceding significant syntactic token (`.eof` at start of file).
    prev_sig_kind: TokenKind = .eof,

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
                        if (try self.scanNestedBlockComment(has_trivia_error, true)) {
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
    fn scanNestedBlockComment(self: *Lexer, has_error: *bool, is_trivia_context: bool) !bool {
        const open_idx: usize = self.cursor;
        const open_start: u32 = @intCast(open_idx);
        const is_inner_block_doc = open_idx + 2 < self.source.len and self.source[open_idx + 2] == '!';
        const is_outer_block_doc = open_idx + 2 < self.source.len and
            self.source[open_idx + 2] == '*' and
            (open_idx + 3 >= self.source.len or
                (self.source[open_idx + 3] != '*' and self.source[open_idx + 3] != '/'));
        self.cursor += 2;
        var depth: u32 = 1;
        var has_newline = false;
        var had_inner_utf8_err = false;

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
                var had_utf8_step_err = false;
                try self.validateAndAdvanceUtf8Codepoint(&had_utf8_step_err);
                if (had_utf8_step_err) {
                    has_error.* = true;
                    had_inner_utf8_err = true;
                }
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
        } else if (is_inner_block_doc or is_outer_block_doc) {
            has_error.* = true;
            try self.emitBlockDocCommentError(
                open_start,
                @intCast(self.cursor),
                is_inner_block_doc,
                is_trivia_context and !had_inner_utf8_err,
            );
        }
        return has_newline;
    }

    /// Returns `true` if `[open_start .. close_end)` sits before token `0` and is followed by a blank line.
    fn isDetachedFileTopBlockDoc(self: *const Lexer, open_start: u32, close_end: u32) bool {
        if (self.token_buffer.countTokens() != 0) return false;
        const limit: usize = @min(@as(usize, open_start), self.source.len);
        var scan_idx: usize = 0;
        if (limit >= 3 and
            self.source[0] == 0xEF and
            self.source[1] == 0xBB and
            self.source[2] == 0xBF)
        {
            scan_idx = 3;
        }
        if (scan_idx + 1 < limit and self.source[scan_idx] == '#' and self.source[scan_idx + 1] == '!') {
            scan_idx += 2;
            while (scan_idx < limit and self.source[scan_idx] != '\n' and self.source[scan_idx] != '\r') {
                scan_idx += 1;
            }
        }
        while (scan_idx < limit) {
            const cur_byte = self.source[scan_idx];
            if (cur_byte == ' ' or cur_byte == '\t' or cur_byte == '\r' or cur_byte == '\n') {
                scan_idx += 1;
            } else if (scan_idx + 2 < limit and
                cur_byte == '/' and
                self.source[scan_idx + 1] == '/' and
                self.source[scan_idx + 2] == '!')
            {
                scan_idx += 3;
                while (scan_idx < limit and self.source[scan_idx] != '\n' and self.source[scan_idx] != '\r') {
                    scan_idx += 1;
                }
            } else {
                return false;
            }
        }

        var after_idx: usize = @min(@as(usize, close_end), self.source.len);
        var line_breaks: u32 = 0;
        while (after_idx < self.source.len) {
            const cur_byte = self.source[after_idx];
            if (cur_byte == ' ' or cur_byte == '\t') {
                after_idx += 1;
            } else if (cur_byte == '\r') {
                line_breaks += 1;
                after_idx += 1;
                if (after_idx < self.source.len and self.source[after_idx] == '\n') {
                    after_idx += 1;
                }
            } else if (cur_byte == '\n') {
                line_breaks += 1;
                after_idx += 1;
            } else {
                break;
            }
        }
        return line_breaks >= 2;
    }

    /// Emits `E0118` (`e0118_block_doc_comment_forbidden`) with a `.machine_applicable` `///` or `//!` rewrite.
    fn emitBlockDocCommentError(
        self: *Lexer,
        open_start: u32,
        close_end: u32,
        is_inner_block_doc: bool,
        is_trivia_context: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const comment_span = Span.init(self.file_id, open_start, close_end);
        const use_module_doc = is_inner_block_doc or
            (is_trivia_context and self.isDetachedFileTopBlockDoc(open_start, close_end));
        const marker_text: []const u8 = if (use_module_doc) "//!" else "///";
        const primary_labels = [_]LabeledSpan{.{
            .span = comment_span,
            .label = if (use_module_doc)
                "block doc comments are forbidden (`ADR-23A`); use `//!` lines"
            else
                "block doc comments are forbidden (`ADR-23A`); use `///` lines",
            .style = .primary,
        }};
        const msg_text: []const u8 = if (is_inner_block_doc)
            "inner block doc comment `/*! … */` is forbidden; write top-of-file `//!` lines instead"
        else
            "outer block doc comment `/** … */` is forbidden; write `///` lines instead";

        if (is_trivia_context) {
            if (self.interner) |str_interner| {
                const arena_alloc = sink.arena.asAllocator();
                const open_usize: usize = @intCast(open_start);
                const close_usize: usize = @intCast(close_end);
                if (close_usize >= open_usize + 5 and close_usize <= self.source.len) {
                    var line_start: usize = open_usize;
                    while (line_start > 0 and
                        self.source[line_start - 1] != '\n' and
                        self.source[line_start - 1] != '\r')
                    {
                        line_start -= 1;
                    }
                    var is_pure_indent = true;
                    for (self.source[line_start..open_usize]) |ind_byte| {
                        if (ind_byte != ' ' and ind_byte != '\t') {
                            is_pure_indent = false;
                            break;
                        }
                    }
                    const base_indent: []const u8 = if (is_pure_indent)
                        self.source[line_start..open_usize]
                    else
                        "";

                    const inner = self.source[open_usize + 3 .. close_usize - 2];
                    var builder: std.ArrayListUnmanaged(u8) = .empty;
                    const has_inner_newline = std.mem.indexOfAny(u8, inner, "\r\n") != null;

                    if (!has_inner_newline) {
                        const trimmed = std.mem.trim(u8, inner, " \t");
                        try builder.appendSlice(arena_alloc, marker_text);
                        if (trimmed.len > 0) {
                            try builder.append(arena_alloc, ' ');
                            try builder.appendSlice(arena_alloc, trimmed);
                        }
                    } else {
                        var line_count: usize = 1;
                        var count_pos: usize = 0;
                        while (count_pos < inner.len) {
                            if (inner[count_pos] == '\r') {
                                line_count += 1;
                                count_pos += if (count_pos + 1 < inner.len and inner[count_pos + 1] == '\n') 2 else 1;
                            } else if (inner[count_pos] == '\n') {
                                line_count += 1;
                                count_pos += 1;
                            } else {
                                count_pos += 1;
                            }
                        }
                        var seg_idx: usize = 0;
                        var has_emitted_line = false;
                        var pos: usize = 0;
                        while (pos <= inner.len) : (seg_idx += 1) {
                            const nl_rel = std.mem.indexOfAnyPos(u8, inner, pos, "\r\n");
                            const seg_end = nl_rel orelse inner.len;
                            const raw_line = inner[pos..seg_end];

                            if (seg_idx == 0) {
                                const first_trimmed = std.mem.trim(u8, raw_line, " \t");
                                if (first_trimmed.len > 0) {
                                    try builder.appendSlice(arena_alloc, marker_text);
                                    try builder.append(arena_alloc, ' ');
                                    try builder.appendSlice(arena_alloc, first_trimmed);
                                    has_emitted_line = true;
                                }
                            } else if (seg_idx + 1 == line_count and std.mem.trim(u8, raw_line, " \t").len == 0) {
                                // Skip trailing closing-delimiter indentation line before `*/`.
                            } else {
                                const after_ws = std.mem.trimStart(u8, raw_line, " \t");
                                var content: []const u8 = after_ws;
                                if (after_ws.len == 1 and after_ws[0] == '*') {
                                    content = "";
                                } else if (after_ws.len >= 2 and
                                    after_ws[0] == '*' and
                                    (after_ws[1] == ' ' or after_ws[1] == '\t'))
                                {
                                    content = if (after_ws[1] == ' ') after_ws[2..] else after_ws[1..];
                                }
                                content = std.mem.trimEnd(u8, content, " \t");

                                if (has_emitted_line) {
                                    try builder.append(arena_alloc, '\n');
                                    try builder.appendSlice(arena_alloc, base_indent);
                                }
                                try builder.appendSlice(arena_alloc, marker_text);
                                if (content.len > 0) {
                                    try builder.append(arena_alloc, ' ');
                                    try builder.appendSlice(arena_alloc, content);
                                }
                                has_emitted_line = true;
                            }

                            if (nl_rel) |found_nl| {
                                pos = if (inner[found_nl] == '\r' and
                                    found_nl + 1 < inner.len and
                                    inner[found_nl + 1] == '\n')
                                    found_nl + 2
                                else
                                    found_nl + 1;
                            } else {
                                break;
                            }
                        }
                        if (!has_emitted_line) {
                            try builder.appendSlice(arena_alloc, marker_text);
                        }
                    }

                    // Preserve any code placed on the same line after `*/` by inserting a line break:
                    var edit_end_usize: usize = close_usize;
                    var scan_after: usize = close_usize;
                    while (scan_after < self.source.len and
                        (self.source[scan_after] == ' ' or self.source[scan_after] == '\t'))
                    {
                        scan_after += 1;
                    }
                    if (scan_after < self.source.len and
                        self.source[scan_after] != '\n' and
                        self.source[scan_after] != '\r')
                    {
                        edit_end_usize = scan_after;
                        try builder.append(arena_alloc, '\n');
                        try builder.appendSlice(arena_alloc, base_indent);
                    }

                    const fix_edits = try arena_alloc.alloc(TextEdit, 1);
                    fix_edits[0] = .{
                        .file_id = self.file_id,
                        .start_byte = open_start,
                        .end_byte = @intCast(edit_end_usize),
                        .replacement_id = try str_interner.intern(builder.items),
                    };
                    const fixes = try arena_alloc.alloc(SuggestedFix, 1);
                    fixes[0] = .{
                        .message = if (use_module_doc)
                            "rewrite block doc comment as `//!` module doc lines"
                        else
                            "rewrite block doc comment as `///` outer doc lines",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = fix_edits,
                    };
                    try sink.emit(.{
                        .code = .e0118_block_doc_comment_forbidden,
                        .severity = .err,
                        .primary_span = comment_span,
                        .message = msg_text,
                        .labels = &primary_labels,
                        .suggestions = fixes,
                    });
                    return;
                }
            }
        }

        try sink.emit(.{
            .code = .e0118_block_doc_comment_forbidden,
            .severity = .err,
            .primary_span = comment_span,
            .message = msg_text,
            .labels = &primary_labels,
        });
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
        else if (first_byte == 'b' and token_start + 1 < self.source.len and self.source[token_start + 1] == '\'')
            try self.scanByteLiteral(&has_lexer_error)
        else if (first_byte == 'b' and token_start + 1 < self.source.len and self.source[token_start + 1] == '"')
            try self.scanByteStringLiteral(&has_lexer_error)
        else if (first_byte == 'b' and
            token_start + 2 < self.source.len and
            self.source[token_start + 1] == 'r' and
            (self.source[token_start + 2] == '"' or self.source[token_start + 2] == '#'))
            try self.scanRawByteStringLiteral(&has_lexer_error)
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
            '$' => blk: {
                self.cursor += 1;
                break :blk .dollar;
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
                if (self.cursor + 1 < self.source.len) {
                    if (self.source[self.cursor + 1] == '=') {
                        self.cursor += 2;
                        break :blk .colon_eq;
                    }
                    if (self.source[self.cursor + 1] == ':') {
                        const sep_start: u32 = @intCast(self.cursor);
                        self.cursor += 2;
                        has_lexer_error = true;
                        try self.emitRetiredPathSeparatorError(sep_start, sep_start + 2);
                        break :blk .dot;
                    }
                }
                self.cursor += 1;
                break :blk .colon;
            },
            '.' => blk: {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '.') {
                    if (self.cursor + 2 < self.source.len) {
                        if (self.source[self.cursor + 2] == '.') {
                            self.cursor += 3;
                            break :blk .dotdotdot;
                        }
                        if (self.source[self.cursor + 2] == '=') {
                            self.cursor += 3;
                            break :blk .dotdoteq;
                        }
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
                        const op_start: u32 = @intCast(self.cursor);
                        self.cursor += 2;
                        has_lexer_error = true;
                        try self.emitRetiredLogicalAndError(op_start, op_start + 2);
                        break :blk .kw_and;
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
        self.prev_sig_kind = token_kind;
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

        // [0] Tuple element projection after `.`: scan `[0-9]+` only and reject `[A-Za-z_]` (`E0103`):
        if (self.prev_sig_kind == .dot) {
            while (self.cursor < self.source.len and isDecimalDigit(self.source[self.cursor])) {
                self.cursor += 1;
            }
            if (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                    self.cursor += 1;
                }
                if ((self.source[self.cursor - 1] == 'e' or self.source[self.cursor - 1] == 'E') and
                    self.cursor < self.source.len and
                    (self.source[self.cursor] == '+' or self.source[self.cursor] == '-'))
                {
                    self.cursor += 1;
                    while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                        self.cursor += 1;
                    }
                }
                has_lexer_error.* = true;
                try self.emitNumericLiteralError(start_offset, self.cursor);
            }
            return .int_lit;
        }

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
                while (self.cursor < self.source.len) {
                    const byte_val = self.source[self.cursor];
                    if (isValidDigitForRadix(byte_val, radix)) {
                        digit_count += 1;
                        is_prev_underscore = false;
                        self.cursor += 1;
                    } else if (byte_val == '_') {
                        if (!is_prev_underscore and
                            digit_count > 0 and
                            self.cursor + 1 < self.source.len and
                            isAsciiAlpha(self.source[self.cursor + 1]) and
                            !isValidDigitForRadix(self.source[self.cursor + 1], radix))
                        {
                            break;
                        }
                        if (is_prev_underscore) is_malformed = true;
                        is_prev_underscore = true;
                        self.cursor += 1;
                    } else {
                        break;
                    }
                }
                if (digit_count == 0 or is_prev_underscore) {
                    is_malformed = true;
                }

                // Optional `[_](i8..usize)` integer suffix (`f32`/`f64` prohibited on non-base-10):
                if (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                    if (self.source[self.cursor] == '_') {
                        if (self.cursor + 1 < self.source.len and isAsciiAlpha(self.source[self.cursor + 1])) {
                            self.cursor += 1;
                        } else {
                            is_malformed = true;
                        }
                    }
                    const suffix_start = self.cursor;
                    while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                        self.cursor += 1;
                    }
                    if (!is_malformed) {
                        if (NUMERIC_SUFFIX_MAP.get(self.source[suffix_start..self.cursor])) |suffix_ty| {
                            if (suffix_ty == .f32_ty or suffix_ty == .f64_ty) {
                                is_malformed = true;
                            }
                        } else {
                            is_malformed = true;
                        }
                    }
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
                if (!is_prev_underscore and
                    self.cursor + 1 < self.source.len and
                    isAsciiAlpha(self.source[self.cursor + 1]))
                {
                    break;
                }
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

        // [3] Fractional `.` part (`3.14`):
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
                    if (!is_prev_underscore and
                        self.cursor + 1 < self.source.len and
                        isAsciiAlpha(self.source[self.cursor + 1]))
                    {
                        break;
                    }
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
                    if (!is_prev_underscore and
                        exp_digits > 0 and
                        self.cursor + 1 < self.source.len and
                        isAsciiAlpha(self.source[self.cursor + 1]))
                    {
                        break;
                    }
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

        // [5] Optional `[_](i8..usize|f32|f64)` suffix on base-10 `INT_LIT` or `[_](f32|f64)` on `FLOAT_LIT`:
        if (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
            if (self.source[self.cursor] == '_') {
                if (self.cursor + 1 < self.source.len and isAsciiAlpha(self.source[self.cursor + 1])) {
                    self.cursor += 1;
                } else {
                    is_malformed = true;
                }
            }
            const suffix_start = self.cursor;
            while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                self.cursor += 1;
            }
            if (!is_malformed) {
                if (NUMERIC_SUFFIX_MAP.get(self.source[suffix_start..self.cursor])) |suffix_ty| {
                    if (is_float and suffix_ty != .f32_ty and suffix_ty != .f64_ty) {
                        is_malformed = true;
                    }
                } else {
                    is_malformed = true;
                }
            }
            if (is_malformed and
                (self.source[self.cursor - 1] == 'e' or self.source[self.cursor - 1] == 'E') and
                self.cursor < self.source.len and
                (self.source[self.cursor] == '+' or self.source[self.cursor] == '-'))
            {
                self.cursor += 1;
                while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                    self.cursor += 1;
                }
            }
        }

        if (is_malformed) {
            has_lexer_error.* = true;
            try self.emitNumericLiteralError(start_offset, self.cursor);
        }
        return if (is_float) .float_lit else .int_lit;
    }

    /// Scans a standard `"…"` or multiline `"""…"""` string literal, validating escapes, UTF-8, and `{expr}` holes.
    fn scanStandardStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        try self.scanStandardStringBody(has_lexer_error);
        return .string_lit;
    }

    /// Checks and consumes the mandatory `\n` or `\r\n` immediately following an opening `"""` (`E0115`).
    fn consumeMultilineOpeningNewline(self: *Lexer, open_quote_offset: u32, has_lexer_error: *bool) !bool {
        if (self.cursor < self.source.len and self.source[self.cursor] == '\n') {
            self.cursor += 1;
            return true;
        }
        if (self.cursor + 1 < self.source.len and
            self.source[self.cursor] == '\r' and
            self.source[self.cursor + 1] == '\n')
        {
            self.cursor += 2;
            return true;
        }
        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0115_multiline_string_opening,
            Span.init(self.file_id, open_quote_offset, open_quote_offset + 3),
            "opening `\"\"\"` of multiline string literal must be followed immediately by a newline",
            "insert a line break immediately after `\"\"\"`",
        );
        return false;
    }

    /// Validates closing-quote indentation (`W_close`) and tab/space discipline on a multiline string body (`E0116`).
    fn validateMultilineIndentation(
        self: *Lexer,
        body_start_offset: u32,
        close_quote_offset: usize,
        literal_span: Span,
        is_raw: bool,
        is_interpolation_allowed: bool,
        has_lexer_error: *bool,
    ) !void {
        processMultilineStringBody(
            self.source[body_start_offset..close_quote_offset],
            is_raw,
            is_interpolation_allowed,
            null,
            null,
        ) catch {
            has_lexer_error.* = true;
            try self.emitSimpleError(
                .e0116_multiline_string_indent,
                literal_span,
                "invalid multiline string indentation or mixed leading tabs and spaces",
                "closing `\"\"\"` must sit on its own space-indented line and every non-empty line must match its indent",
            );
        };
    }

    /// Scans from an opening `"` or `"""` through its matching closing delimiter, tracking `is_triple_quote`
    /// per `{expr}` brace-nesting level (`[P1 Trap A]`).
    fn scanStandardStringBody(self: *Lexer, has_lexer_error: *bool) !void {
        const start_offset = self.cursor;
        var is_triple_quote = false;
        var open_quote_offset: u32 = @intCast(start_offset);
        var has_valid_opening = true;

        if (self.cursor + 2 < self.source.len and
            self.source[self.cursor + 1] == '"' and
            self.source[self.cursor + 2] == '"')
        {
            is_triple_quote = true;
            self.cursor += 3;
            has_valid_opening = try self.consumeMultilineOpeningNewline(open_quote_offset, has_lexer_error);
        } else {
            self.cursor += 1;
        }
        var body_start_offset: u32 = @intCast(self.cursor);

        var interp_depth: u32 = 0;
        var interp_brace_stack: [syntax_arenas.MAX_PARSE_DEPTH]InterpStackFrame = undefined;
        var nested_str_depth: usize = 0;
        var has_emitted_depth_error = false;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (interp_depth == 0) {
                if (byte_val == '"') {
                    if (is_triple_quote) {
                        if (self.cursor + 2 < self.source.len and
                            self.source[self.cursor + 1] == '"' and
                            self.source[self.cursor + 2] == '"')
                        {
                            const close_quote_offset = self.cursor;
                            self.cursor += 3;
                            if (has_valid_opening) {
                                try self.validateMultilineIndentation(
                                    body_start_offset,
                                    close_quote_offset,
                                    Span.init(self.file_id, open_quote_offset, @intCast(self.cursor)),
                                    false,
                                    true,
                                    has_lexer_error,
                                );
                            }
                            if (nested_str_depth == 0) return;
                            nested_str_depth -= 1;
                            if (nested_str_depth < syntax_arenas.MAX_PARSE_DEPTH) {
                                const saved_frame = interp_brace_stack[nested_str_depth];
                                interp_depth = saved_frame.brace_depth;
                                is_triple_quote = saved_frame.is_triple_quote;
                                has_valid_opening = saved_frame.has_valid_opening;
                                open_quote_offset = saved_frame.open_quote_offset;
                                body_start_offset = saved_frame.body_start_offset;
                            } else {
                                interp_depth = 1;
                                is_triple_quote = false;
                            }
                            continue;
                        }
                        self.cursor += 1;
                        continue;
                    }

                    self.cursor += 1;
                    if (nested_str_depth == 0) return;
                    nested_str_depth -= 1;
                    if (nested_str_depth < syntax_arenas.MAX_PARSE_DEPTH) {
                        const saved_frame = interp_brace_stack[nested_str_depth];
                        interp_depth = saved_frame.brace_depth;
                        is_triple_quote = saved_frame.is_triple_quote;
                        has_valid_opening = saved_frame.has_valid_opening;
                        open_quote_offset = saved_frame.open_quote_offset;
                        body_start_offset = saved_frame.body_start_offset;
                    } else {
                        interp_depth = 1;
                        is_triple_quote = false;
                    }
                    continue;
                }
                if (byte_val == '\\') {
                    try self.scanEscapeSequence(.interpolated_string, has_lexer_error);
                    continue;
                }
                if (byte_val == '{') {
                    if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '{') {
                        self.cursor += 2;
                        continue;
                    }
                    interp_depth = 1;
                    self.cursor += 1;
                    continue;
                }
                if (byte_val == '}') {
                    if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '}') {
                        self.cursor += 2;
                        continue;
                    }
                    has_lexer_error.* = true;
                    const brace_offset: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    try self.emitUnmatchedCloseBraceInStringError(brace_offset, brace_offset + 1);
                    continue;
                }
                if (byte_val < 0x80) {
                    self.cursor += 1;
                } else {
                    try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                }
            } else {
                // Inside `{expr}` interpolation; track nested braces, strings, byte literals, chars, and comments:
                if (byte_val == '{') {
                    interp_depth += 1;
                    self.cursor += 1;
                } else if (byte_val == '}') {
                    interp_depth -= 1;
                    self.cursor += 1;
                } else if (byte_val == '"') {
                    if (nested_str_depth < syntax_arenas.MAX_PARSE_DEPTH) {
                        interp_brace_stack[nested_str_depth] = .{
                            .brace_depth = interp_depth,
                            .is_triple_quote = is_triple_quote,
                            .has_valid_opening = has_valid_opening,
                            .open_quote_offset = open_quote_offset,
                            .body_start_offset = body_start_offset,
                        };
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
                    open_quote_offset = @intCast(self.cursor);
                    if (self.cursor + 2 < self.source.len and
                        self.source[self.cursor + 1] == '"' and
                        self.source[self.cursor + 2] == '"')
                    {
                        is_triple_quote = true;
                        self.cursor += 3;
                        has_valid_opening = try self.consumeMultilineOpeningNewline(
                            open_quote_offset,
                            has_lexer_error,
                        );
                    } else {
                        is_triple_quote = false;
                        has_valid_opening = true;
                        self.cursor += 1;
                    }
                    body_start_offset = @intCast(self.cursor);
                } else if (byte_val == 'b' and
                    (self.cursor == 0 or !isIdentContinue(self.source[self.cursor - 1])) and
                    self.cursor + 1 < self.source.len)
                {
                    if (self.source[self.cursor + 1] == '\'') {
                        _ = try self.scanByteLiteral(has_lexer_error);
                    } else if (self.source[self.cursor + 1] == '"') {
                        _ = try self.scanByteStringLiteral(has_lexer_error);
                    } else if (self.source[self.cursor + 1] == 'r' and
                        self.cursor + 2 < self.source.len and
                        (self.source[self.cursor + 2] == '"' or self.source[self.cursor + 2] == '#'))
                    {
                        _ = try self.scanRawByteStringLiteral(has_lexer_error);
                    } else {
                        self.cursor += 1;
                    }
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
                        _ = try self.scanNestedBlockComment(has_lexer_error, false);
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

    /// Scans a raw string literal `r"…"`, `r#"…"#`, `r"""…"""`, or `r#"""…"""#` (`0..255` `#` delimiters).
    fn scanRawStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        try self.scanRawStringCommon(false, has_lexer_error);
        return .string_lit;
    }

    /// Scans a raw byte string literal `br"…"`, `br#"…"#`, `br"""…"""`, or `br#"""…"""#` (`.byte_string_lit`).
    fn scanRawByteStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        try self.scanRawStringCommon(true, has_lexer_error);
        return .byte_string_lit;
    }

    /// Shared scanner for `r` (UTF-8) and `br` (ASCII-only `E0117`) single-line and multiline raw strings.
    fn scanRawStringCommon(self: *Lexer, is_byte_mode: bool, has_lexer_error: *bool) !void {
        const start_offset = self.cursor;
        self.cursor += if (is_byte_mode) @as(usize, 2) else 1;

        var hash_count: usize = 0;
        while (self.cursor < self.source.len and self.source[self.cursor] == '#') {
            hash_count += 1;
            self.cursor += 1;
        }

        if (self.cursor >= self.source.len or self.source[self.cursor] != '"') {
            while (self.cursor < self.source.len and isIdentContinue(self.source[self.cursor])) {
                self.cursor += 1;
            }
            has_lexer_error.* = true;
            try self.emitSimpleError(
                .e0102_unterminated_string_literal,
                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                if (is_byte_mode)
                    "malformed or unterminated raw byte string literal"
                else
                    "malformed or unterminated raw string literal",
                "expected opening `\"` after raw string prefix",
            );
            return;
        }

        if (hash_count > MAX_RAW_STRING_HASHES) {
            has_lexer_error.* = true;
        }

        const open_quote_offset: u32 = @intCast(self.cursor);
        const is_triple_quote = isTripleQuoteOpening(self.source, self.cursor, true, hash_count);

        var has_valid_opening = true;
        if (is_triple_quote) {
            self.cursor += 3;
            has_valid_opening = try self.consumeMultilineOpeningNewline(open_quote_offset, has_lexer_error);
        } else {
            self.cursor += 1;
        }
        const body_start_offset: u32 = @intCast(self.cursor);

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"') {
                if (is_triple_quote) {
                    if (self.cursor + 2 < self.source.len and
                        self.source[self.cursor + 1] == '"' and
                        self.source[self.cursor + 2] == '"' and
                        hasExactHashesAt(self.source, self.cursor + 3, hash_count))
                    {
                        const close_quote_offset = self.cursor;
                        self.cursor += 3 + hash_count;
                        if (hash_count > MAX_RAW_STRING_HASHES) {
                            try self.emitSimpleError(
                                .e0102_unterminated_string_literal,
                                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                                "raw string delimiter exceeds maximum of 255 `#` characters",
                                "reduce `#` delimiter count to at most 255",
                            );
                        }
                        if (has_valid_opening) {
                            try self.validateMultilineIndentation(
                                body_start_offset,
                                close_quote_offset,
                                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                                true,
                                false,
                                has_lexer_error,
                            );
                        }
                        return;
                    }
                    self.cursor += 1;
                    continue;
                }

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
                    return;
                }
            } else if (byte_val < 0x80) {
                self.cursor += 1;
            } else if (is_byte_mode) {
                const non_ascii_start = self.cursor;
                var is_bad_utf8 = false;
                try self.validateAndAdvanceUtf8Codepoint(&is_bad_utf8);
                has_lexer_error.* = true;
                if (!is_bad_utf8) {
                    try self.emitSimpleError(
                        .e0117_non_ascii_byte_literal,
                        Span.init(self.file_id, @intCast(non_ascii_start), @intCast(self.cursor)),
                        "raw byte string literal may only contain ASCII characters (`0x00..0x7F`)",
                        "non-ASCII character is not allowed in byte string literal",
                    );
                }
            } else {
                try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
            }
        }

        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0102_unterminated_string_literal,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            if (is_byte_mode) "unterminated raw byte string literal" else "unterminated raw string literal",
            "raw string literal was not closed by matching delimiter before end of file",
        );
    }

    /// Scans a cooked byte string literal `b"…"` or `b"""…"""` (`.byte_string_lit`, interpolation disabled).
    fn scanByteStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1; // Advance past `'b'`.
        const open_quote_offset: u32 = @intCast(self.cursor);
        const is_triple_quote = self.cursor + 2 < self.source.len and
            self.source[self.cursor + 1] == '"' and
            self.source[self.cursor + 2] == '"';

        var has_valid_opening = true;
        if (is_triple_quote) {
            self.cursor += 3;
            has_valid_opening = try self.consumeMultilineOpeningNewline(open_quote_offset, has_lexer_error);
        } else {
            self.cursor += 1;
        }
        const body_start_offset: u32 = @intCast(self.cursor);

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"') {
                if (is_triple_quote) {
                    if (self.cursor + 2 < self.source.len and
                        self.source[self.cursor + 1] == '"' and
                        self.source[self.cursor + 2] == '"')
                    {
                        const close_quote_offset = self.cursor;
                        self.cursor += 3;
                        if (has_valid_opening) {
                            try self.validateMultilineIndentation(
                                body_start_offset,
                                close_quote_offset,
                                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                                false,
                                false,
                                has_lexer_error,
                            );
                        }
                        return .byte_string_lit;
                    }
                    self.cursor += 1;
                    continue;
                }
                self.cursor += 1;
                return .byte_string_lit;
            }
            if (byte_val == '\\') {
                try self.scanEscapeSequence(.byte_string, has_lexer_error);
                continue;
            }
            if (byte_val < 0x80) {
                self.cursor += 1;
            } else {
                const non_ascii_start = self.cursor;
                var is_bad_utf8 = false;
                try self.validateAndAdvanceUtf8Codepoint(&is_bad_utf8);
                has_lexer_error.* = true;
                if (!is_bad_utf8) {
                    try self.emitSimpleError(
                        .e0117_non_ascii_byte_literal,
                        Span.init(self.file_id, @intCast(non_ascii_start), @intCast(self.cursor)),
                        "byte string literal may only contain ASCII bytes (`0x00..0x7F`) or `\\xHH` escapes",
                        "replace non-ASCII character with explicit `\\xHH` byte escapes",
                    );
                }
            }
        }

        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0102_unterminated_string_literal,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            "unterminated byte string literal",
            "byte string literal opened here was not closed before end of file",
        );
        return .byte_string_lit;
    }

    /// Scans a single-byte literal `b'x'` (`.byte_lit`), emitting `E0117` on non-ASCII bytes or `\u{…}` escapes.
    fn scanByteLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 2; // Advance past `"b'"`.
        var byte_unit_count: usize = 0;
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
                try self.scanEscapeSequence(.byte_char, has_lexer_error);
                byte_unit_count += 1;
            } else if (byte_val < 0x80) {
                self.cursor += 1;
                byte_unit_count += 1;
            } else {
                const non_ascii_start = self.cursor;
                var is_bad_utf8 = false;
                try self.validateAndAdvanceUtf8Codepoint(&is_bad_utf8);
                has_lexer_error.* = true;
                if (!is_bad_utf8) {
                    try self.emitSimpleError(
                        .e0117_non_ascii_byte_literal,
                        Span.init(self.file_id, @intCast(non_ascii_start), @intCast(self.cursor)),
                        "byte literal `b'…'` may only contain an ASCII byte (`0x00..0x7F`) or `\\xHH` escape",
                        "non-ASCII character is not valid in `b'…'`; use `'…'` (`char`) or `b'\\xHH'`",
                    );
                }
                byte_unit_count += 1;
            }
        }

        if (!has_closing_quote or byte_unit_count != 1) {
            has_lexer_error.* = true;
            try self.emitSimpleError(
                .e0102_unterminated_string_literal,
                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                if (!has_closing_quote)
                    "unterminated byte literal"
                else if (byte_unit_count == 0)
                    "empty byte literal `b''`"
                else
                    "byte literal may only contain a single ASCII byte or `\\xHH` escape",
                "expected a single ASCII byte or escape sequence enclosed in `b'…'`",
            );
        }
        return .byte_lit;
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
                try self.scanEscapeSequence(.char_literal, has_lexer_error);
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

    /// Validates a `\` escape sequence at `self.cursor` under `escape_ctx`.
    fn scanEscapeSequence(self: *Lexer, escape_ctx: EscapeContext, has_lexer_error: *bool) !void {
        const escape_start = self.cursor;
        self.cursor += 1; // Advance past `'\\'`.
        if (self.cursor >= self.source.len) return;

        const is_string_like = escape_ctx == .interpolated_string or escape_ctx == .byte_string;
        const is_byte_mode = escape_ctx == .byte_char or escape_ctx == .byte_string;
        const esc_byte = self.source[self.cursor];
        switch (esc_byte) {
            '\n', '\r' => {
                if (!is_string_like) {
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
            '"' => {
                self.cursor += 1;
                if (!is_string_like and self.options.is_escape_warning_enabled) {
                    try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                }
            },
            '{', '}' => {
                self.cursor += 1;
                if (escape_ctx == .interpolated_string) {
                    has_lexer_error.* = true;
                    try self.emitInvalidBraceEscapeError(
                        @intCast(escape_start),
                        @intCast(self.cursor),
                        esc_byte == '{',
                    );
                } else if (self.options.is_escape_warning_enabled) {
                    try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                }
            },
            '\'' => {
                self.cursor += 1;
                if (is_string_like and self.options.is_escape_warning_enabled) {
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
                        if (is_byte_mode) .e0117_non_ascii_byte_literal else .e0101_invalid_utf8_sequence,
                        Span.init(self.file_id, @intCast(escape_start), @intCast(self.cursor)),
                        if (is_byte_mode)
                            "Unicode escape `\\u{…}` is not permitted in byte literals; use `\\xHH` instead"
                        else
                            "malformed Unicode escape sequence `\\u{…}`",
                        if (is_byte_mode) "replace `\\u{…}` with `\\xHH`" else "expected `{` after `\\u`",
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
                if (is_byte_mode) {
                    has_lexer_error.* = true;
                    try self.emitSimpleError(
                        .e0117_non_ascii_byte_literal,
                        Span.init(self.file_id, @intCast(escape_start), @intCast(self.cursor)),
                        "Unicode escape `\\u{…}` is not permitted in byte literals; use `\\xHH` instead",
                        "byte literals only support single-byte `\\xHH` escapes",
                    );
                    return;
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
                    var is_bad_utf8 = false;
                    try self.validateAndAdvanceUtf8Codepoint(&is_bad_utf8);
                    if (is_bad_utf8) {
                        has_lexer_error.* = true;
                    } else if (is_byte_mode) {
                        has_lexer_error.* = true;
                        try self.emitSimpleError(
                            .e0117_non_ascii_byte_literal,
                            Span.init(self.file_id, @intCast(escape_start), @intCast(self.cursor)),
                            "non-ASCII character is not permitted in byte literal",
                            "use `\\xHH` for raw byte values",
                        );
                    } else if (self.options.is_escape_warning_enabled) {
                        try self.emitRedundantEscapeWarning(@intCast(escape_start), @intCast(self.cursor));
                    }
                }
            },
        }
    }

    /// Scans `#soa` (`TokenKind.hash_soa` = `74`) or emits `.invalid_token` on unknown `#` directives.
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

    /// Emits `E0112` (`e0112_retired_path_separator`) with a `.machine_applicable` fix replacing `::` with `.`.
    fn emitRetiredPathSeparatorError(self: *Lexer, sep_start: u32, sep_end: u32) !void {
        const sink = self.diagnostic_sink orelse return;
        const sep_span = Span.init(self.file_id, sep_start, sep_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = sep_span,
            .label = "retired `::` separator; use `.` instead",
            .style = .primary,
        }};

        if (self.interner) |str_interner| {
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = sep_start,
                .end_byte = sep_end,
                .replacement_id = try str_interner.intern("."),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "replace '::' with '.'",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0112_retired_path_separator,
                .severity = .err,
                .primary_span = sep_span,
                .message = "path separator '::' has been retired in favor of unified '.'",
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
        } else {
            try sink.emit(.{
                .code = .e0112_retired_path_separator,
                .severity = .err,
                .primary_span = sep_span,
                .message = "path separator '::' has been retired in favor of unified '.'",
                .labels = &primary_labels,
            });
        }
    }

    /// Emits `E0113` (`e0113_retired_logical_and`) with a `.machine_applicable` fix replacing `&&` with `and`.
    fn emitRetiredLogicalAndError(self: *Lexer, op_start: u32, op_end: u32) !void {
        const sink = self.diagnostic_sink orelse return;
        const op_span = Span.init(self.file_id, op_start, op_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = op_span,
            .label = "retired `&&` operator; use `and` instead",
            .style = .primary,
        }};

        if (self.interner) |str_interner| {
            const needs_left_space = op_start > 0 and isIdentContinue(self.source[op_start - 1]);
            const needs_right_space = @as(usize, op_end) < self.source.len and
                isIdentContinue(self.source[op_end]);
            const replacement_text: []const u8 = if (needs_left_space and needs_right_space)
                " and "
            else if (needs_left_space)
                " and"
            else if (needs_right_space)
                "and "
            else
                "and";

            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = op_start,
                .end_byte = op_end,
                .replacement_id = try str_interner.intern(replacement_text),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "replace '&&' with 'and'",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0113_retired_logical_and,
                .severity = .err,
                .primary_span = op_span,
                .message = "logical AND operator '&&' has been retired in favor of 'and'",
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
        } else {
            try sink.emit(.{
                .code = .e0113_retired_logical_and,
                .severity = .err,
                .primary_span = op_span,
                .message = "logical AND operator '&&' has been retired in favor of 'and'",
                .labels = &primary_labels,
            });
        }
    }

    /// Emits `E0114` (`e0114_invalid_brace_escape`) with a `.machine_applicable` fix replacing `\{`/`\}` with `{{`/`}}`.
    fn emitInvalidBraceEscapeError(
        self: *Lexer,
        escape_start: u32,
        escape_end: u32,
        is_open_brace: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const escape_span = Span.init(self.file_id, escape_start, escape_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = escape_span,
            .label = if (is_open_brace)
                "invalid `\\{` brace escape; write `{{` for a literal `{`"
            else
                "invalid `\\}` brace escape; write `}}` for a literal `}`",
            .style = .primary,
        }};

        if (self.interner) |str_interner| {
            const replacement_text: []const u8 = if (is_open_brace) "{{" else "}}";
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = escape_start,
                .end_byte = escape_end,
                .replacement_id = try str_interner.intern(replacement_text),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = if (is_open_brace) "replace '\\{' with '{{'" else "replace '\\}' with '}}'",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0114_invalid_brace_escape,
                .severity = .err,
                .primary_span = escape_span,
                .message = "retired backslash brace escape in interpolated string literal; use '{{' or '}}'",
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
        } else {
            try sink.emit(.{
                .code = .e0114_invalid_brace_escape,
                .severity = .err,
                .primary_span = escape_span,
                .message = "retired backslash brace escape in interpolated string literal; use '{{' or '}}'",
                .labels = &primary_labels,
            });
        }
    }

    /// Emits `E0114` (`e0114_invalid_brace_escape`) with a `.machine_applicable` fix replacing a lone `}` with `}}`.
    fn emitUnmatchedCloseBraceInStringError(self: *Lexer, brace_start: u32, brace_end: u32) !void {
        const sink = self.diagnostic_sink orelse return;
        const brace_span = Span.init(self.file_id, brace_start, brace_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = brace_span,
            .label = "unmatched `}` in interpolated string literal; write `}}` for a literal `}`",
            .style = .primary,
        }};

        if (self.interner) |str_interner| {
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = brace_start,
                .end_byte = brace_end,
                .replacement_id = try str_interner.intern("}}"),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "replace '}' with '}}'",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0114_invalid_brace_escape,
                .severity = .err,
                .primary_span = brace_span,
                .message = "unmatched '}' in interpolated string literal; escape literal closing braces as '}}'",
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
        } else {
            try sink.emit(.{
                .code = .e0114_invalid_brace_escape,
                .severity = .err,
                .primary_span = brace_span,
                .message = "unmatched '}' in interpolated string literal; escape literal closing braces as '}}'",
                .labels = &primary_labels,
            });
        }
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

test "test_all_50_keywords_20_prim_types_and_disjoint_casing" {
    try std.testing.expectEqual(@as(?TokenKind, .kw_pub), lookupKeywordOrPrim("pub"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_self_val), lookupKeywordOrPrim("self"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_self_type), lookupKeywordOrPrim("Self"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_bit_field), lookupKeywordOrPrim("bit_field"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_subscript), lookupKeywordOrPrim("subscript"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_yield), lookupKeywordOrPrim("yield"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_orelse), lookupKeywordOrPrim("orelse"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_with), lookupKeywordOrPrim("with"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_context), lookupKeywordOrPrim("context"));
    try std.testing.expectEqual(@as(?TokenKind, .kw_unreachable), lookupKeywordOrPrim("unreachable"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("i32"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("usize"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("never"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("unit"));
    try std.testing.expectEqual(@as(?TokenKind, .prim_type), lookupKeywordOrPrim("opaque"));
    try std.testing.expectEqual(@as(?TokenKind, null), lookupKeywordOrPrim("ref"));
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
        \\        let msg = "val={if i > 0 { "ok /* }} */" } else { r#"raw } str"# }}\n";
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
    const bad_source = "0x 0x_1 0b102 0o78 1__2 1.0e+ 42u99 'ab' '' \"\\z\" r#bad";
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

test "test_dr21_walrus_dollar_retired_coloncolon_and_tuple_projection_lexing" {
    // [1] `:=`, `$`, new keywords, and tuple projection `tup.0.1.2` vs float literals `0.1` / `1.5e2`:
    const dr21_source =
        "if (val := opt orelse unreachable) { with context.alloc = arena { let sum_val = buf[$ - 1] + tup.0.1.2; let flt = 0.1 + 1.5e2; } }";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try tokenize(dr21_source, FileId.fromInt(0), &token_buf, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);

    try std.testing.expectEqual(TokenKind.colon_eq, token_buf.getToken(TokenIndex.fromInt(3)).kind);
    try std.testing.expectEqual(TokenKind.kw_orelse, token_buf.getToken(TokenIndex.fromInt(5)).kind);
    try std.testing.expectEqual(TokenKind.kw_unreachable, token_buf.getToken(TokenIndex.fromInt(6)).kind);
    try std.testing.expectEqual(TokenKind.kw_with, token_buf.getToken(TokenIndex.fromInt(9)).kind);
    try std.testing.expectEqual(TokenKind.kw_context, token_buf.getToken(TokenIndex.fromInt(10)).kind);
    try std.testing.expectEqual(TokenKind.dollar, token_buf.getToken(TokenIndex.fromInt(21)).kind);
    try std.testing.expectEqual(TokenKind.ident, token_buf.getToken(TokenIndex.fromInt(26)).kind);
    try std.testing.expectEqual(TokenKind.dot, token_buf.getToken(TokenIndex.fromInt(27)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(28)).kind);
    try std.testing.expectEqual(TokenKind.dot, token_buf.getToken(TokenIndex.fromInt(29)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(30)).kind);
    try std.testing.expectEqual(TokenKind.dot, token_buf.getToken(TokenIndex.fromInt(31)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(32)).kind);
    try std.testing.expectEqual(TokenKind.float_lit, token_buf.getToken(TokenIndex.fromInt(37)).kind);
    try std.testing.expectEqual(TokenKind.float_lit, token_buf.getToken(TokenIndex.fromInt(39)).kind);
    try std.testing.expectEqual(@as(usize, 44), token_buf.countTokens());

    // Scientific exponent `e`/`E` immediately after `.` (`tup.0e2`) is rejected with `E0103`:
    var exp_buf = TokenBuffer.init(std.testing.allocator);
    defer exp_buf.deinit();
    var exp_sink = DiagnosticSink.init(std.testing.allocator);
    defer exp_sink.deinit();
    try tokenize("tup.0e2", FileId.fromInt(0), &exp_buf, &exp_sink, null);
    try std.testing.expectEqual(@as(u32, 1), exp_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0103_invalid_numeric_literal, exp_sink.asSlice()[0].code);
    try std.testing.expectEqual(TokenKind.int_lit, exp_buf.getToken(TokenIndex.fromInt(2)).kind);

    // [2] Retired `::` emits `E0112` with machine-applicable `.` autofix and lossless CST round-trip:
    const retired_source = "use cx::mem::Allocator;";
    var retired_buf = TokenBuffer.init(std.testing.allocator);
    defer retired_buf.deinit();
    var retired_sink = DiagnosticSink.init(std.testing.allocator);
    defer retired_sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(retired_source, FileId.fromInt(0), &retired_buf, &retired_sink, &interner);
    try std.testing.expectEqual(@as(u32, 2), retired_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0112_retired_path_separator, retired_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0112_retired_path_separator, retired_sink.asSlice()[1].code);

    const recovered_dot = retired_buf.getToken(TokenIndex.fromInt(2));
    try std.testing.expectEqual(TokenKind.dot, recovered_dot.kind);
    try std.testing.expectEqual(@as(u16, 2), recovered_dot.byte_len);
    try std.testing.expect(recovered_dot.flags.has_lexer_error);

    var cst_arena = syntax_arenas.LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed = try cst_arena.reconstructSource(
        std.testing.allocator,
        retired_source,
        &retired_buf,
    );
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(retired_source, reconstructed);

    var fixes: [2]SuggestedFix = .{
        retired_sink.asSlice()[0].suggestions[0],
        retired_sink.asSlice()[1].suggestions[0],
    };
    const patch_res = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        retired_source,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 2), patch_res.applied_count);
    try std.testing.expectEqualStrings("use cx.mem.Allocator;", patch_res.patched_source);

    // [3] Backtick `` ` `` remains an unrecognized ASCII character (`.invalid_token`, `E0201`):
    var inv_buf = TokenBuffer.init(std.testing.allocator);
    defer inv_buf.deinit();
    var inv_sink = DiagnosticSink.init(std.testing.allocator);
    defer inv_sink.deinit();
    try tokenize("`", FileId.fromInt(0), &inv_buf, &inv_sink, null);
    try std.testing.expectEqual(@as(u32, 1), inv_sink.error_count);
    try std.testing.expectEqual(TokenKind.invalid_token, inv_buf.getToken(TokenIndex.fromInt(0)).kind);
}

test "test_dr22_retired_ampamp_dotdotdot_brace_escapes_and_autofixes" {
    const legacy_source = "let ok = flag_a && flag_b&&flag_c; let s = \"\\{k\\} = {{v}}\"; fn c_fn(fmt: *opaque, ...);";
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(legacy_source, FileId.fromInt(0), &token_buf, &sink, &interner);
    try std.testing.expectEqual(@as(u32, 4), sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0113_retired_logical_and, sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0113_retired_logical_and, sink.asSlice()[1].code);
    try std.testing.expectEqual(DiagnosticCode.e0114_invalid_brace_escape, sink.asSlice()[2].code);
    try std.testing.expectEqual(DiagnosticCode.e0114_invalid_brace_escape, sink.asSlice()[3].code);

    // Recovery token for `&&` is `.kw_and` with exact 2-byte span and lossless CST reconstruction:
    const recovered_and = token_buf.getToken(TokenIndex.fromInt(4));
    try std.testing.expectEqual(TokenKind.kw_and, recovered_and.kind);
    try std.testing.expectEqual(@as(u16, 2), recovered_and.byte_len);
    try std.testing.expect(recovered_and.flags.has_lexer_error);

    // Verify `.dotdotdot` (`...`) before `)`:
    try std.testing.expectEqual(TokenKind.dotdotdot, token_buf.getToken(TokenIndex.fromInt(22)).kind);

    var cst_arena = syntax_arenas.LosslessCstArena.init(std.testing.allocator);
    defer cst_arena.deinit();
    const reconstructed = try cst_arena.reconstructSource(std.testing.allocator, legacy_source, &token_buf);
    defer std.testing.allocator.free(reconstructed);
    try std.testing.expectEqualStrings(legacy_source, reconstructed);

    var fixes: [4]SuggestedFix = .{
        sink.asSlice()[0].suggestions[0],
        sink.asSlice()[1].suggestions[0],
        sink.asSlice()[2].suggestions[0],
        sink.asSlice()[3].suggestions[0],
    };
    const patch_res = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        legacy_source,
        FileId.fromInt(0),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 4), patch_res.applied_count);
    try std.testing.expectEqualStrings(
        "let ok = flag_a and flag_b and flag_c; let s = \"{{k}} = {{v}}\"; fn c_fn(fmt: *opaque, ...);",
        patch_res.patched_source,
    );
}

test "test_dr22_multiline_strings_nested_interp_trap_a_and_byte_literals" {
    // [1] `[P1 Trap A]`: `"""outer {"inner"} and {"""nested"""} tail"""` + byte literals:
    const valid_source =
        \\let banner = """
        \\    outer {"inner"} and {
        \\        """
        \\        nested "quote" ""pair""
        \\        """
        \\    } \
        \\    tail {{v1.0}}
        \\    """;
        \\let raw_multi = r#"""
        \\    line 1 /\
        \\    line 2 "triple"
        \\    """#;
        \\let wire = b"HTTP/1.1\r\n\xFF";
        \\let sep = b'\r';
        \\let raw_bytes = br#"A"B"#;
    ;
    var token_buf = TokenBuffer.init(std.testing.allocator);
    defer token_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try tokenize(valid_source, FileId.fromInt(0), &token_buf, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), sink.warning_count);

    try std.testing.expectEqual(TokenKind.string_lit, token_buf.getToken(TokenIndex.fromInt(3)).kind);
    try std.testing.expectEqual(TokenKind.string_lit, token_buf.getToken(TokenIndex.fromInt(8)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, token_buf.getToken(TokenIndex.fromInt(13)).kind);
    try std.testing.expectEqual(TokenKind.byte_lit, token_buf.getToken(TokenIndex.fromInt(18)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, token_buf.getToken(TokenIndex.fromInt(23)).kind);

    // Verify `cookStringLiteral`, `extractMultilineStringContent`, and `extractByteLiteralValue`:
    const raw_rec = token_buf.getToken(TokenIndex.fromInt(8));
    const raw_lexeme = valid_source[raw_rec.byte_offset .. raw_rec.byte_offset + raw_rec.byte_len];
    try std.testing.expect(isMultilineStringLexeme(raw_lexeme));
    const cooked_raw = try cookStringLiteral(std.testing.allocator, raw_lexeme);
    defer std.testing.allocator.free(cooked_raw);
    try std.testing.expectEqualStrings("line 1 /\\\nline 2 \"triple\"", cooked_raw);

    const wire_rec = token_buf.getToken(TokenIndex.fromInt(13));
    const cooked_wire = try cookStringLiteral(
        std.testing.allocator,
        valid_source[wire_rec.byte_offset .. wire_rec.byte_offset + wire_rec.byte_len],
    );
    defer std.testing.allocator.free(cooked_wire);
    try std.testing.expectEqualSlices(u8, "HTTP/1.1\r\n\xFF", cooked_wire);
    try std.testing.expectEqual(@as(?u8, '\r'), extractByteLiteralValue("b'\\r'"));
    try std.testing.expectEqual(@as(?u8, 0xFF), extractByteLiteralValue("b'\\xFF'"));
    try std.testing.expectEqual(@as(?u8, 'A'), extractByteLiteralValue("b'A'"));

    // [2] Negative diagnostics `E0115`, `E0116`, and `E0117`:
    const err_source =
        "let e1 = \"\"\"bad\n\"\"\"; let e2 = \"\"\"\n  under\n    \"\"\"; let e3 = b'é'; let e4 = b\"\\u{41}\";";
    var err_buf = TokenBuffer.init(std.testing.allocator);
    defer err_buf.deinit();
    var err_sink = DiagnosticSink.init(std.testing.allocator);
    defer err_sink.deinit();

    try tokenize(err_source, FileId.fromInt(0), &err_buf, &err_sink, null);
    try std.testing.expectEqual(@as(u32, 4), err_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0115_multiline_string_opening, err_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0116_multiline_string_indent, err_sink.asSlice()[1].code);
    try std.testing.expectEqual(DiagnosticCode.e0117_non_ascii_byte_literal, err_sink.asSlice()[2].code);
    try std.testing.expectEqual(DiagnosticCode.e0117_non_ascii_byte_literal, err_sink.asSlice()[3].code);
}

test "test_dr22_numeric_suffixes_and_8byte_fmt_spec_parser" {
    const num_source = "42_u64 42u64 0x4358_574C_u32 0b1010_i8 0o77_usize 10_f32 0.5_f32 1e-3f64 0x1f32";
    var num_buf = TokenBuffer.init(std.testing.allocator);
    defer num_buf.deinit();
    var num_sink = DiagnosticSink.init(std.testing.allocator);
    defer num_sink.deinit();

    try tokenize(num_source, FileId.fromInt(0), &num_buf, &num_sink, null);
    try std.testing.expectEqual(@as(u32, 0), num_sink.error_count);

    const parsed_hex = try extractNumericSuffix("0x4358_574C_u32");
    try std.testing.expectEqualStrings("0x4358_574C", parsed_hex.digits_slice);
    try std.testing.expectEqualStrings("u32", parsed_hex.suffix_slice);
    try std.testing.expectEqual(@as(?TypeId, .u32_ty), parsed_hex.suffix_type);
    try std.testing.expect(parsed_hex.has_underscore_sep);
    try std.testing.expectEqual(@as(u8, 16), parsed_hex.radix);

    const parsed_pure_hex = try extractNumericSuffix("0x1f32");
    try std.testing.expectEqual(@as(?TypeId, null), parsed_pure_hex.suffix_type);
    try std.testing.expectEqualStrings("0x1f32", parsed_pure_hex.digits_slice);

    const parsed_int_flt = try extractNumericSuffix("10_f32");
    try std.testing.expectEqual(@as(?TypeId, .f32_ty), parsed_int_flt.suffix_type);
    try std.testing.expect(!parsed_int_flt.is_float_syntax);

    // Reject float suffix on binary/octal and int suffix on float literal (`E0103`):
    var bad_num_buf = TokenBuffer.init(std.testing.allocator);
    defer bad_num_buf.deinit();
    var bad_num_sink = DiagnosticSink.init(std.testing.allocator);
    defer bad_num_sink.deinit();
    try tokenize("0b10_f32 1.5_u64 42__u64 42_", FileId.fromInt(0), &bad_num_buf, &bad_num_sink, null);
    try std.testing.expectEqual(@as(u32, 4), bad_num_sink.error_count);

    // Verify 8-byte `FmtSpec` packing and `parseFormatSpec`:
    try std.testing.expectEqual(@as(usize, 8), @sizeOf(FmtSpec));
    const hex_spec = try parseFormatSpec("#010x", true);
    try std.testing.expect(hex_spec.hasAltFlag());
    try std.testing.expect(hex_spec.hasZeroPad());
    try std.testing.expect(hex_spec.hasDebugEq());
    try std.testing.expectEqual(@as(?u16, 10), hex_spec.extractWidth());
    try std.testing.expectEqual(@as(?u16, null), hex_spec.extractPrecision());
    try std.testing.expectEqual(FmtTypeCode.lower_hex, hex_spec.extractTypeCode());

    const debug_eq_default = try parseFormatSpec("", true);
    try std.testing.expectEqual(FmtTypeCode.debug, debug_eq_default.extractTypeCode());
    try std.testing.expect(debug_eq_default.hasDebugEq());

    const unicode_fill = try parseFormatSpec("─^20.2f", false);
    try std.testing.expectEqual(@as(u21, '─'), unicode_fill.extractFillChar());
    try std.testing.expectEqual(FmtAlignMode.center, unicode_fill.extractAlignMode());
    try std.testing.expectEqual(@as(?u16, 20), unicode_fill.extractWidth());
    try std.testing.expectEqual(@as(?u16, 2), unicode_fill.extractPrecision());
    try std.testing.expectEqual(FmtTypeCode.fixed, unicode_fill.extractTypeCode());
}

test "test_stage4_single_line_hashed_raw_quote_runs_and_nested_interp" {
    const src = "r#\"\"\"\"# br#\"\"\"\"# r##\"\"\"\"\"## \"outer {r#\"\"\"\"#} ok\"";
    var tok_buf = TokenBuffer.init(std.testing.allocator);
    defer tok_buf.deinit();
    var sink = DiagnosticSink.init(std.testing.allocator);
    defer sink.deinit();

    try tokenize(src, FileId.fromInt(0), &tok_buf, &sink, null);
    try std.testing.expectEqual(@as(u32, 0), sink.error_count);
    try std.testing.expectEqual(@as(usize, 5), tok_buf.countTokens());
    try std.testing.expectEqual(TokenKind.string_lit, tok_buf.getToken(TokenIndex.fromInt(0)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, tok_buf.getToken(TokenIndex.fromInt(1)).kind);
    try std.testing.expectEqual(TokenKind.string_lit, tok_buf.getToken(TokenIndex.fromInt(2)).kind);
    try std.testing.expectEqual(TokenKind.string_lit, tok_buf.getToken(TokenIndex.fromInt(3)).kind);

    const cooked_two_quotes = try cookStringLiteral(std.testing.allocator, "r#\"\"\"\"#");
    defer std.testing.allocator.free(cooked_two_quotes);
    try std.testing.expectEqualStrings("\"\"", cooked_two_quotes);

    const cooked_byte_quotes = try cookStringLiteral(std.testing.allocator, "br#\"\"\"\"#");
    defer std.testing.allocator.free(cooked_byte_quotes);
    try std.testing.expectEqualStrings("\"\"", cooked_byte_quotes);

    const cooked_three_quotes = try cookStringLiteral(std.testing.allocator, "r##\"\"\"\"\"##");
    defer std.testing.allocator.free(cooked_three_quotes);
    try std.testing.expectEqualStrings("\"\"\"", cooked_three_quotes);
}

test "test_adr23a_e0118_block_doc_comments_and_ordinary_star_block_comments" {
    // `/**/` and `/***/` and nested `/* /** inner */ */` must emit zero errors:
    const clean_src = "/**/ /***/ /**** banner ****/ /* outer /** inner */ /*! inner */ end */ pub fn ok() {}\n";
    var clean_buf = TokenBuffer.init(std.testing.allocator);
    defer clean_buf.deinit();
    var clean_sink = DiagnosticSink.init(std.testing.allocator);
    defer clean_sink.deinit();
    try tokenize(clean_src, FileId.fromInt(0), &clean_buf, &clean_sink, null);
    try std.testing.expectEqual(@as(u32, 0), clean_sink.error_count);

    // `/*! … */` and `/** … */` must emit `E0118` with machine-applicable `//!` / `///` fixes:
    const bad_src =
        "/**\n" ++
        " * Detached file header.\n" ++
        " */\n\n" ++
        "/** Single-line item doc. */ pub struct Item {\n" ++
        "    /*! Misplaced inner block doc. */\n" ++
        "    pub count: u32,\n" ++
        "}\n";
    var bad_buf = TokenBuffer.init(std.testing.allocator);
    defer bad_buf.deinit();
    var bad_sink = DiagnosticSink.init(std.testing.allocator);
    defer bad_sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(bad_src, FileId.fromInt(1), &bad_buf, &bad_sink, &interner);
    try std.testing.expectEqual(@as(u32, 3), bad_sink.error_count);

    var fixes: [3]SuggestedFix = undefined;
    for (bad_sink.asSlice(), 0..) |diag_item, i| {
        try std.testing.expectEqual(DiagnosticCode.e0118_block_doc_comment_forbidden, diag_item.code);
        fixes[i] = diag_item.suggestions[0];
    }

    const patch_res = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        bad_src,
        FileId.fromInt(1),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 3), patch_res.applied_count);
    try std.testing.expectEqualStrings(
        "//! Detached file header.\n\n" ++
            "/// Single-line item doc.\n" ++
            "pub struct Item {\n" ++
            "    //! Misplaced inner block doc.\n" ++
            "    pub count: u32,\n" ++
            "}\n",
        patch_res.patched_source,
    );

    var relex_buf = TokenBuffer.init(std.testing.allocator);
    defer relex_buf.deinit();
    var relex_sink = DiagnosticSink.init(std.testing.allocator);
    defer relex_sink.deinit();
    try tokenize(patch_res.patched_source, FileId.fromInt(1), &relex_buf, &relex_sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), relex_sink.error_count);
}

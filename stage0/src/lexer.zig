//! High-Speed Deterministic Lexer & Lossless Trivia Scanner
//!
//! Scans UTF-8 source buffers into a contiguous Structure-of-Arrays (SoA) `TokenBuffer` in a single
//! non-backtracking $O(N)$ linear pass while enforcing the `DR-03`, `DR-21`, `DR-22`, & `DR-24` 121-token lexical taxonomy.
//!
//! Preserves 100% of source bytes across leading/trailing `TriviaPiece` slices (`<= 65,535`-byte chunking,
//! slot-14 coalescing, carrier token flushing past `983,025` trivia bytes, and `E0104` tail preservation)
//! so `LosslessCstArena.reconstructSource` reproduces any input byte-for-bit.

const std = @import("std");
const mem_foundation = @import("mem_foundation.zig");
const syntax_arenas = @import("syntax_arenas.zig");
const diagnostic = @import("diag/diagnostic.zig");
const lint_filter = @import("lint_filter.zig");
const unicode_confusables = @import("unicode_confusables.zig");

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
    /// Whether to emit `W0201` warnings on non-canonical identifier casing in standalone mode.
    is_casing_warning_enabled: bool = true,
    /// Whether to emit `W0101` warnings on redundant character/string escape sequences in standalone mode.
    is_escape_warning_enabled: bool = true,
    /// Active semantic lint configuration (`[lint.settings]`, `DR-25` §3.1).
    lint_settings: lint_filter.LintSettings = .{},
    /// Optional Stage-1 `RawLintCandidate` output list (`null` in standalone mode emits directly to `sink`).
    raw_lint_candidates_out: ?*std.ArrayListUnmanaged(lint_filter.RawLintCandidate) = null,
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

/// Structural delimiter and multiline dedent boundary metadata for any string, byte-string, or format-string lexeme (`DR-24` §2.1).
pub const StringLiteralBodyInfo = struct {
    /// Byte length of the leading alphabetic prefix (`0` for `""`, `1` for `r`/`b`/`f`, `2` for `br`).
    prefix_len: u8 = 0,
    /// Number of `#` quote-guard characters between the prefix and opening `"` (`0..=255`).
    hash_count: u8 = 0,
    /// `true` if backslash escapes are disabled (`r"…"`, `r#"…"#`, `br"…"`, `br#"…"#`).
    is_raw: bool = false,
    /// `true` if the literal produces byte storage (`b"…"`, `br"…"`, `br#"…"#`).
    is_bytes: bool = false,
    /// `true` if the literal is an explicit interpolated format string (`f"…"`, `f#"…"#`).
    is_fmt: bool = false,
    /// `true` if the literal uses `"<newline> … "` (or recovered `"""`) multiline dedent boundaries.
    is_multiline: bool = false,
    /// `true` if the literal opened with a retired `"""` delimiter (`E0115` recovery).
    is_retired_triple: bool = false,
    /// Number of leading ASCII `' '` columns preceding the standalone closing quote on multiline strings.
    closing_indent_spaces: u32 = 0,
    /// Inclusive starting byte offset of the string payload within `lexeme` (after opening `"` or `"\r?\n`).
    body_start: u32 = 0,
    /// Exclusive ending byte offset of the string payload within `lexeme` (before closing `"` or final `\r?\n[ ]*"`).
    body_end: u32 = 0,
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
/// Maximum number of `#` quote-guard delimiters allowed on a format string literal (`f#"…"#`, `0..=15`).
pub const MAX_FMT_STRING_HASHES: usize = 15;
/// Maximum nested `f"…"` format string depth inside `{expr}` holes before emitting `E0203` (`DR-24` §1.2).
pub const MAX_FMT_NESTING: u32 = 4;
/// Maximum byte span scanned for top-of-file `--- … ---` script TOML frontmatter (`1 MiB`).
pub const MAX_FRONTMATTER_BYTES: usize = 1024 * 1024;

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

/// Returns `true` if `source_bytes[quote_pos..]` opens a retired `"""` literal (`E0115`) rather than `r#""…""#`.
inline fn isRetiredTripleQuoteOpening(
    source_bytes: []const u8,
    quote_pos: usize,
    hash_count: usize,
) bool {
    if (quote_pos + 2 >= source_bytes.len or
        source_bytes[quote_pos] != '"' or
        source_bytes[quote_pos + 1] != '"' or
        source_bytes[quote_pos + 2] != '"')
    {
        return false;
    }
    if (hash_count == 0) return true;
    if (quote_pos + 3 < source_bytes.len and source_bytes[quote_pos + 3] == '\n') return true;
    return quote_pos + 4 < source_bytes.len and
        source_bytes[quote_pos + 3] == '\r' and
        source_bytes[quote_pos + 4] == '\n';
}

/// Returns the exclusive end offset of a matched top-of-file `--- … ---` TOML frontmatter block, or `null`.
pub fn matchScriptFrontmatterEnd(source_bytes: []const u8, start_pos: usize) ?usize {
    if (start_pos + 4 > source_bytes.len or !std.mem.eql(u8, source_bytes[start_pos .. start_pos + 3], "---")) {
        return null;
    }
    var cursor: usize = start_pos + 3;
    while (cursor < source_bytes.len and (source_bytes[cursor] == ' ' or source_bytes[cursor] == '\t')) {
        cursor += 1;
    }
    if (cursor < source_bytes.len and source_bytes[cursor] == '\n') {
        cursor += 1;
    } else if (cursor + 1 < source_bytes.len and
        source_bytes[cursor] == '\r' and
        source_bytes[cursor + 1] == '\n')
    {
        cursor += 2;
    } else {
        return null;
    }

    const scan_limit: usize = @min(source_bytes.len, start_pos + MAX_FRONTMATTER_BYTES);
    while (cursor < scan_limit) {
        var line_end: usize = cursor;
        while (line_end < scan_limit and
            source_bytes[line_end] != '\n' and
            source_bytes[line_end] != '\r')
        {
            line_end += 1;
        }
        if (line_end - cursor >= 3 and std.mem.eql(u8, source_bytes[cursor .. cursor + 3], "---")) {
            var is_clean_fence = true;
            for (source_bytes[cursor + 3 .. line_end]) |trail_byte| {
                if (trail_byte != ' ' and trail_byte != '\t') {
                    is_clean_fence = false;
                    break;
                }
            }
            const has_valid_eol = line_end == source_bytes.len or
                source_bytes[line_end] == '\n' or
                (source_bytes[line_end] == '\r' and
                    line_end + 1 < source_bytes.len and
                    source_bytes[line_end + 1] == '\n');
            if (is_clean_fence and has_valid_eol) {
                return line_end;
            }
        }
        if (line_end >= scan_limit) break;
        if (source_bytes[line_end] == '\r' and
            line_end + 1 < scan_limit and
            source_bytes[line_end + 1] == '\n')
        {
            cursor = line_end + 2;
        } else {
            cursor = line_end + 1;
        }
    }
    return null;
}

/// Lexical context passed to `Lexer.scanEscapeSequence` to enforce mode-specific escape rules.
const EscapeContext = enum(u8) {
    /// Plain `"…"` UTF-8 string (`{` / `}` literal; `\{`, `\}`, `\'` -> `W0101`; `\u{…}` valid).
    plain_string = 0,
    /// Explicit `f"…"` / `f#"…"#` format string (`\{` / `\}` -> `E0114`; `\'` -> `W0101`; `\u{…}` valid).
    fmt_string = 1,
    /// Unicode scalar `'c'` literal (`\"`, `\{`, `\}` -> `W0101`; `\u{…}` valid).
    char_literal = 2,
    /// Single ASCII byte `b'x'` literal (`\xHH` valid for `0x00..0xFF`; `\u{…}` -> `E0117`).
    byte_char = 3,
    /// ASCII byte string `b"…"` (`\xHH` valid; `\u{…}` -> `E0117`; `\{`, `\}`, `\'` -> `W0101`).
    byte_string = 4,
};

/// Advances past a `{expr}` interpolation hole inside `body_bytes` starting at `open_brace_idx`.
fn skipInterpolationHoleInBody(body_bytes: []const u8, open_brace_idx: usize) usize {
    var cursor = open_brace_idx + 1;
    var brace_depth: u32 = 1;
    var paren_depth: u32 = 0;
    var bracket_depth: u32 = 0;
    var is_in_fmt_spec = false;

    while (cursor < body_bytes.len and brace_depth > 0) {
        const cur_byte = body_bytes[cursor];
        if (cur_byte == '{') {
            brace_depth += 1;
            cursor += 1;
        } else if (cur_byte == '}') {
            brace_depth -= 1;
            if (brace_depth == 0) is_in_fmt_spec = false;
            cursor += 1;
        } else if (is_in_fmt_spec) {
            cursor += 1;
        } else if (cur_byte == '(') {
            paren_depth += 1;
            cursor += 1;
        } else if (cur_byte == ')') {
            if (paren_depth > 0) paren_depth -= 1;
            cursor += 1;
        } else if (cur_byte == '[') {
            bracket_depth += 1;
            cursor += 1;
        } else if (cur_byte == ']') {
            if (bracket_depth > 0) bracket_depth -= 1;
            cursor += 1;
        } else if (cur_byte == ':' and brace_depth == 1 and paren_depth == 0 and bracket_depth == 0) {
            if (cursor + 1 < body_bytes.len and body_bytes[cursor + 1] != ':' and body_bytes[cursor + 1] != '=') {
                is_in_fmt_spec = true;
            }
            cursor += 1;
        } else if (cur_byte == 'f' and
            (cursor == 0 or !isIdentContinue(body_bytes[cursor - 1])) and
            cursor + 1 < body_bytes.len and
            (body_bytes[cursor + 1] == '"' or body_bytes[cursor + 1] == '#'))
        {
            cursor = skipFmtStringInExpr(body_bytes, cursor + 1);
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
                const is_triple = isRetiredTripleQuoteOpening(body_bytes, cursor + 1, 0);
                cursor = skipQuotedNonRawInExpr(body_bytes, cursor + (if (is_triple) @as(usize, 4) else 2), '"', is_triple);
            } else if (body_bytes[cursor + 1] == 'r' and cursor + 2 < body_bytes.len and
                (body_bytes[cursor + 2] == '"' or body_bytes[cursor + 2] == '#'))
            {
                cursor = skipRawStringInExpr(body_bytes, cursor + 2);
            } else {
                cursor += 1;
            }
        } else if (cur_byte == '"') {
            const is_triple = isRetiredTripleQuoteOpening(body_bytes, cursor, 0);
            cursor = skipQuotedNonRawInExpr(body_bytes, cursor + (if (is_triple) @as(usize, 3) else 1), '"', is_triple);
        } else if (cur_byte == '\'') {
            cursor = skipQuotedNonRawInExpr(body_bytes, cursor + 1, '\'', false);
        } else if (cur_byte == '/' and cursor + 1 < body_bytes.len) {
            const second_byte = body_bytes[cursor + 1];
            if (second_byte == '/' or second_byte == '|' or second_byte == '#') {
                cursor += 2;
                while (cursor < body_bytes.len and body_bytes[cursor] != '\n' and body_bytes[cursor] != '\r') {
                    cursor += 1;
                }
            } else if (second_byte == '*') {
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

/// Skips a non-interpolated `'…'`, `b'…'`, `"…"`, `b"…"`, or retired `"""…"""` literal inside an `{expr}` scan.
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

/// Skips a raw `r#"…"#` or retired `r"""…"""` string literal inside an `{expr}` scan (`after_r_idx` points past `'r'`).
fn skipRawStringInExpr(body_bytes: []const u8, after_r_idx: usize) usize {
    var cursor = after_r_idx;
    var hash_count: usize = 0;
    while (cursor < body_bytes.len and body_bytes[cursor] == '#') : (cursor += 1) {
        hash_count += 1;
    }
    if (cursor >= body_bytes.len or body_bytes[cursor] != '"') return cursor;
    const is_triple = isRetiredTripleQuoteOpening(body_bytes, cursor, hash_count);
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

/// Skips an interpolated `f"…"` / `f#"…"#` literal inside an `{expr}` scan (`after_f_idx` points past `'f'`).
fn skipFmtStringInExpr(body_bytes: []const u8, after_f_idx: usize) usize {
    var cursor = after_f_idx;
    var hash_count: usize = 0;
    while (cursor < body_bytes.len and body_bytes[cursor] == '#') : (cursor += 1) {
        hash_count += 1;
    }
    if (cursor >= body_bytes.len or body_bytes[cursor] != '"') return cursor;
    const is_triple = isRetiredTripleQuoteOpening(body_bytes, cursor, hash_count);
    cursor += if (is_triple) 3 else 1;

    while (cursor < body_bytes.len) {
        const cur_byte = body_bytes[cursor];
        if (cur_byte == '\\') {
            cursor = @min(cursor + 2, body_bytes.len);
            continue;
        }
        if (cur_byte == '"') {
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
            cursor += 1;
            continue;
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

/// Scans `body_bytes` for the next outer line break (`\n`), skipping `{expr}` holes when `is_fmt` is `true`.
fn findNextOuterLineFeed(
    body_bytes: []const u8,
    start_pos: usize,
    is_raw: bool,
    is_fmt: bool,
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
        if (is_fmt and !is_raw and cur_byte == '{') {
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

/// Infers `TokenKind` from a raw string, byte-string, or format-string `lexeme` slice.
inline fn inferStringTokenKind(lexeme: []const u8) TokenKind {
    if (lexeme.len >= 2 and lexeme[0] == 'f' and (lexeme[1] == '"' or lexeme[1] == '#')) {
        return .fmt_string_lit;
    }
    if (lexeme.len >= 2 and lexeme[0] == 'b' and (lexeme[1] == '"' or lexeme[1] == 'r')) {
        return .byte_string_lit;
    }
    return .string_lit;
}

/// Validates closing-line standalone quote rules and `< C` leading `' '` indentation on `body_after_open_nl`.
fn validateMultilineStringBodyPure(
    body_after_open_nl: []const u8,
    is_raw: bool,
    is_fmt: bool,
) error{ InvalidMultilineOpening, InvalidMultilineIndent }!u32 {
    var last_outer_lf: ?usize = null;
    var scan_pos: usize = 0;
    while (findNextOuterLineFeed(body_after_open_nl, scan_pos, is_raw, is_fmt)) |lf_pos| {
        last_outer_lf = lf_pos;
        scan_pos = lf_pos + 1;
    }

    const close_prefix = if (last_outer_lf) |lf_idx|
        body_after_open_nl[lf_idx + 1 ..]
    else
        body_after_open_nl;

    for (close_prefix) |prefix_byte| {
        if (prefix_byte == '\t') return error.InvalidMultilineIndent;
        if (prefix_byte != ' ') return error.InvalidMultilineOpening;
    }
    const close_indent: usize = close_prefix.len;
    const final_lf_idx = last_outer_lf orelse return @intCast(close_indent);
    const content_end: usize = if (final_lf_idx > 0 and body_after_open_nl[final_lf_idx - 1] == '\r')
        final_lf_idx - 1
    else
        final_lf_idx;
    const content_bytes = body_after_open_nl[0..content_end];

    var line_start: usize = 0;
    while (true) {
        const maybe_lf = findNextOuterLineFeed(content_bytes, line_start, is_raw, is_fmt);
        const raw_line_end = maybe_lf orelse content_bytes.len;
        const clean_line_end = if (raw_line_end > line_start and content_bytes[raw_line_end - 1] == '\r')
            raw_line_end - 1
        else
            raw_line_end;
        const line_slice = content_bytes[line_start..clean_line_end];

        if (line_slice.len > 0) {
            var leading_spaces: usize = 0;
            while (leading_spaces < line_slice.len and line_slice[leading_spaces] == ' ') : (leading_spaces += 1) {}
            if (leading_spaces < line_slice.len and leading_spaces < close_indent) {
                return error.InvalidMultilineIndent;
            }
        }
        if (maybe_lf) |lf_pos| {
            line_start = lf_pos + 1;
        } else {
            break;
        }
    }
    return @intCast(close_indent);
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

/// Classifies an identifier or keyword `lexeme` under `DR-03` §5.2 and `DR-25` `UAX #31` rules.
pub fn classifyIdentifierOrKeyword(lexeme: []const u8) IdentifierClassification {
    if (lexeme.len == 0) {
        return .{
            .kind = .invalid_token,
            .expected_case = .reserved_or_wildcard,
            .case_style = .reserved_or_wildcard,
            .is_canonical = false,
            .has_case_violation = true,
        };
    }

    // [0] Non-ASCII `UAX #31` identifier path (zero overhead on pure ASCII `< 0x80` identifiers):
    var has_non_ascii = false;
    for (lexeme) |check_byte| {
        if (check_byte >= 0x80) {
            has_non_ascii = true;
            break;
        }
    }
    if (has_non_ascii) {
        return classifyUnicodeIdentifier(lexeme);
    }

    if (!isIdentStart(lexeme[0])) {
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

/// Validates and classifies a UTF-8 `UAX #31` identifier containing at least one byte `>= 0x80` (`DR-25` `W0103`).
fn classifyUnicodeIdentifier(lexeme: []const u8) IdentifierClassification {
    const invalid_res = IdentifierClassification{
        .kind = .invalid_token,
        .expected_case = .reserved_or_wildcard,
        .case_style = .reserved_or_wildcard,
        .is_canonical = false,
        .has_case_violation = true,
    };

    var upper_count: usize = 0;
    var has_lower = false;
    var has_underscore = false;
    var has_consecutive_underscores = false;
    var is_prev_underscore = false;
    var is_first_upper = false;

    var pos: usize = 0;
    var is_first_cp = true;
    while (pos < lexeme.len) {
        const cur_byte = lexeme[pos];
        if (cur_byte < 0x80) {
            if (is_first_cp) {
                if (!isIdentStart(cur_byte)) return invalid_res;
                is_first_upper = isAsciiUpper(cur_byte);
            } else if (!isIdentContinue(cur_byte)) {
                return invalid_res;
            }
            if (isAsciiUpper(cur_byte)) {
                upper_count += 1;
                is_prev_underscore = false;
            } else if (isAsciiLower(cur_byte)) {
                has_lower = true;
                is_prev_underscore = false;
            } else if (cur_byte == '_') {
                if (is_prev_underscore) has_consecutive_underscores = true;
                has_underscore = true;
                is_prev_underscore = true;
            } else {
                is_prev_underscore = false;
            }
            pos += 1;
        } else {
            const seq_len = std.unicode.utf8ByteSequenceLength(cur_byte) catch return invalid_res;
            if (pos + seq_len > lexeme.len) return invalid_res;
            const decoded_cp = std.unicode.utf8Decode(lexeme[pos .. pos + seq_len]) catch return invalid_res;
            if (is_first_cp) {
                if (!unicode_confusables.isUnicodeXidStart(decoded_cp)) return invalid_res;
                is_first_upper = unicode_confusables.isUnicodeUppercase(decoded_cp);
            } else if (!unicode_confusables.isUnicodeXidContinue(decoded_cp)) {
                return invalid_res;
            }
            if (unicode_confusables.isUnicodeUppercase(decoded_cp)) {
                upper_count += 1;
            } else {
                has_lower = true;
            }
            is_prev_underscore = false;
            pos += seq_len;
        }
        is_first_cp = false;
    }

    // Scientific `Δ` (`U+0394`) prefix exemption (`Δt`, `Δx`, `_Δt`): canonical `.ident` (`snake_case`):
    const core_lex = if (lexeme[0] == '_') lexeme[1..] else lexeme;
    if (std.mem.startsWith(u8, core_lex, "\u{0394}") and core_lex.len > "\u{0394}".len) {
        const delta_tail = core_lex["\u{0394}".len..];
        if (delta_tail[0] != '_' and delta_tail[delta_tail.len - 1] != '_' and !has_consecutive_underscores) {
            const tail_upper = upper_count -| @as(usize, 1);
            if (tail_upper == 0) {
                return .{
                    .kind = .ident,
                    .expected_case = .snake_case,
                    .case_style = .snake_case,
                    .is_canonical = true,
                    .has_case_violation = false,
                };
            }
        }
    }

    if (!is_first_upper) {
        const is_valid_snake = (upper_count == 0) and !has_consecutive_underscores;
        return .{
            .kind = .ident,
            .expected_case = .snake_case,
            .case_style = .snake_case,
            .is_canonical = is_valid_snake,
            .has_case_violation = !is_valid_snake,
        };
    }

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

/// Extracts delimiter flags and multiline dedent boundaries from `lexeme` (`DR-24` §2.1).
pub fn extractStringBodyInfo(tok_kind: TokenKind, lexeme: []const u8) StringLiteralBodyInfo {
    var info = StringLiteralBodyInfo{
        .is_bytes = tok_kind == .byte_string_lit,
        .is_fmt = tok_kind == .fmt_string_lit,
    };
    if (lexeme.len == 0) return info;

    var cursor: usize = 0;
    if (cursor + 1 < lexeme.len and lexeme[cursor] == 'b' and lexeme[cursor + 1] == 'r') {
        info.prefix_len = 2;
        info.is_bytes = true;
        info.is_raw = true;
        cursor += 2;
    } else if (lexeme[cursor] == 'b' and cursor + 1 < lexeme.len and lexeme[cursor + 1] == '"') {
        info.prefix_len = 1;
        info.is_bytes = true;
        cursor += 1;
    } else if (lexeme[cursor] == 'r' and cursor + 1 < lexeme.len and
        (lexeme[cursor + 1] == '"' or lexeme[cursor + 1] == '#'))
    {
        info.prefix_len = 1;
        info.is_raw = true;
        cursor += 1;
    } else if (lexeme[cursor] == 'f' and cursor + 1 < lexeme.len and
        (lexeme[cursor + 1] == '"' or lexeme[cursor + 1] == '#'))
    {
        info.prefix_len = 1;
        info.is_fmt = true;
        cursor += 1;
    }

    var hash_count: usize = 0;
    if (info.is_raw or info.is_fmt) {
        while (cursor < lexeme.len and lexeme[cursor] == '#') : (cursor += 1) {
            hash_count += 1;
        }
        info.hash_count = @intCast(@min(hash_count, 255));
    }

    if (cursor >= lexeme.len or lexeme[cursor] != '"') {
        info.body_start = @intCast(lexeme.len);
        info.body_end = @intCast(lexeme.len);
        return info;
    }

    info.is_retired_triple = isRetiredTripleQuoteOpening(lexeme, cursor, hash_count);
    const quote_len: usize = if (info.is_retired_triple) 3 else 1;
    cursor += quote_len;

    const close_suffix_len: usize = quote_len + hash_count;
    const has_valid_close = lexeme.len >= cursor + close_suffix_len and
        hasExactHashesAt(lexeme, lexeme.len - hash_count, hash_count) and blk: {
        const close_pos = lexeme.len - close_suffix_len;
        var q_idx: usize = 0;
        while (q_idx < quote_len) : (q_idx += 1) {
            if (lexeme[close_pos + q_idx] != '"') break :blk false;
        }
        break :blk true;
    };
    const close_quote_pos: usize = if (has_valid_close) lexeme.len - close_suffix_len else lexeme.len;

    var open_nl_len: usize = 0;
    if (cursor < close_quote_pos and lexeme[cursor] == '\n') {
        open_nl_len = 1;
    } else if (cursor + 1 < close_quote_pos and lexeme[cursor] == '\r' and lexeme[cursor + 1] == '\n') {
        open_nl_len = 2;
    }

    if (open_nl_len > 0) {
        info.is_multiline = true;
        const after_open_nl: usize = cursor + open_nl_len;
        info.body_start = @intCast(after_open_nl);
        const raw_after_open_nl = lexeme[after_open_nl..close_quote_pos];

        var last_outer_lf: ?usize = null;
        var scan_pos: usize = 0;
        while (findNextOuterLineFeed(raw_after_open_nl, scan_pos, info.is_raw, info.is_fmt)) |lf_pos| {
            last_outer_lf = lf_pos;
            scan_pos = lf_pos + 1;
        }

        const close_prefix = if (last_outer_lf) |lf_idx|
            raw_after_open_nl[lf_idx + 1 ..]
        else
            raw_after_open_nl;

        var space_cols: u32 = 0;
        while (space_cols < close_prefix.len and close_prefix[space_cols] == ' ') : (space_cols += 1) {}
        info.closing_indent_spaces = space_cols;

        if (last_outer_lf) |final_lf_rel| {
            const content_end_rel: usize = if (final_lf_rel > 0 and raw_after_open_nl[final_lf_rel - 1] == '\r')
                final_lf_rel - 1
            else
                final_lf_rel;
            info.body_end = @intCast(after_open_nl + content_end_rel);
        } else {
            info.body_end = @intCast(after_open_nl);
        }
        return info;
    }

    info.body_start = @intCast(cursor);
    info.body_end = @intCast(close_quote_pos);
    return info;
}

/// Strips up to `indent_spaces` leading `' '` bytes per non-empty line and normalizes `\r\n` to `\n`.
pub fn stripMultilineIndentAlloc(
    allocator: std.mem.Allocator,
    raw_body: []const u8,
    indent_spaces: u32,
) ![]u8 {
    if (raw_body.len == 0) return allocator.alloc(u8, 0);
    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try out_buf.ensureTotalCapacity(allocator, raw_body.len);

    var line_start: usize = 0;
    while (true) {
        const maybe_lf = std.mem.indexOfScalarPos(u8, raw_body, line_start, '\n');
        const raw_end = maybe_lf orelse raw_body.len;
        const clean_end = if (raw_end > line_start and raw_body[raw_end - 1] == '\r')
            raw_end - 1
        else
            raw_end;
        const line_slice = raw_body[line_start..clean_end];

        if (line_slice.len > 0) {
            var strip_count: usize = 0;
            const max_strip: usize = @min(line_slice.len, @as(usize, indent_spaces));
            while (strip_count < max_strip and line_slice[strip_count] == ' ') : (strip_count += 1) {}
            try out_buf.appendSlice(allocator, line_slice[strip_count..]);
        }

        if (maybe_lf) |lf_pos| {
            try out_buf.append(allocator, '\n');
            line_start = lf_pos + 1;
        } else {
            break;
        }
    }
    return out_buf.toOwnedSlice(allocator);
}

/// Returns `true` if `lexeme` is a `"<newline> … "` (or recovered `"""`) multiline string literal.
pub inline fn isMultilineStringLexeme(lexeme: []const u8) bool {
    return extractStringBodyInfo(inferStringTokenKind(lexeme), lexeme).is_multiline;
}

/// Extracts and closing-quote dedents a multiline string `lexeme` without decoding backslash escapes.
pub fn extractMultilineStringContent(
    allocator: std.mem.Allocator,
    lexeme: []const u8,
) error{ InvalidMultilineOpening, InvalidMultilineIndent, InvalidStringLiteral, OutOfMemory }![]u8 {
    const info = extractStringBodyInfo(inferStringTokenKind(lexeme), lexeme);
    if (!info.is_multiline) {
        if (info.is_retired_triple) return error.InvalidMultilineOpening;
        return error.InvalidStringLiteral;
    }

    const quote_len: usize = if (info.is_retired_triple) 3 else 1;
    const suffix_len: usize = quote_len + @as(usize, info.hash_count);
    if (lexeme.len < @as(usize, info.body_start) + suffix_len) return error.InvalidStringLiteral;
    const close_quote_pos: usize = lexeme.len - suffix_len;

    const indent_spaces = try validateMultilineStringBodyPure(
        lexeme[@as(usize, info.body_start)..close_quote_pos],
        info.is_raw,
        info.is_fmt,
    );
    const stripped = try stripMultilineIndentAlloc(
        allocator,
        lexeme[@as(usize, info.body_start)..@as(usize, info.body_end)],
        indent_spaces,
    );
    if (info.is_raw) return stripped;

    // Apply `\` line continuations while preserving all non-newline escape sequences verbatim:
    defer allocator.free(stripped);
    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try out_buf.ensureTotalCapacity(allocator, stripped.len);
    var cursor: usize = 0;
    while (cursor < stripped.len) {
        if (stripped[cursor] == '\\' and cursor + 1 < stripped.len) {
            if (stripped[cursor + 1] == '\n') {
                cursor += 2;
                continue;
            }
            try out_buf.appendSlice(allocator, stripped[cursor .. cursor + 2]);
            cursor += 2;
            continue;
        }
        try out_buf.append(allocator, stripped[cursor]);
        cursor += 1;
    }
    return out_buf.toOwnedSlice(allocator);
}

/// Canonical alias for `extractMultilineStringContent`.
pub const extractMultilineString = extractMultilineStringContent;

/// Cooks any non-interpolated string, byte-string, or 0-hole format-string `lexeme` (`DR-24` §1.2),
/// applying multiline `"<newline> … "` dedent and mode-specific escape decoding.
pub fn cookStringLiteral(
    allocator: std.mem.Allocator,
    lexeme: []const u8,
) error{ InvalidMultilineOpening, InvalidMultilineIndent, InvalidStringLiteral, OutOfMemory }![]u8 {
    if (lexeme.len < 2) return error.InvalidStringLiteral;
    const info = extractStringBodyInfo(inferStringTokenKind(lexeme), lexeme);
    const quote_len: usize = if (info.is_retired_triple) 3 else 1;
    const suffix_len: usize = quote_len + @as(usize, info.hash_count);
    const min_total_len: usize = @as(usize, info.prefix_len) + @as(usize, info.hash_count) + quote_len + suffix_len;
    if (lexeme.len < min_total_len) return error.InvalidStringLiteral;
    if (!hasExactHashesAt(lexeme, lexeme.len - @as(usize, info.hash_count), info.hash_count)) {
        return error.InvalidStringLiteral;
    }
    const close_quote_pos = lexeme.len - suffix_len;
    var q_idx: usize = 0;
    while (q_idx < quote_len) : (q_idx += 1) {
        if (lexeme[close_quote_pos + q_idx] != '"') return error.InvalidStringLiteral;
    }

    if (info.is_multiline or info.is_retired_triple) {
        if (!info.is_multiline) return error.InvalidMultilineOpening;
        _ = try validateMultilineStringBodyPure(
            lexeme[@as(usize, info.body_start)..close_quote_pos],
            info.is_raw,
            info.is_fmt,
        );
        const stripped = try stripMultilineIndentAlloc(
            allocator,
            lexeme[@as(usize, info.body_start)..@as(usize, info.body_end)],
            info.closing_indent_spaces,
        );
        if (info.is_raw) {
            if (info.is_bytes) {
                for (stripped) |raw_byte| {
                    if (raw_byte >= 0x80) {
                        allocator.free(stripped);
                        return error.InvalidStringLiteral;
                    }
                }
            }
            return stripped;
        }
        defer allocator.free(stripped);
        var out_buf: std.ArrayList(u8) = .empty;
        errdefer out_buf.deinit(allocator);
        try out_buf.ensureTotalCapacity(allocator, stripped.len);
        try decodeEscapedStringSlice(allocator, stripped, info.is_bytes, info.is_fmt, &out_buf);
        return out_buf.toOwnedSlice(allocator);
    }

    const raw_inner = lexeme[@as(usize, info.body_start)..@as(usize, info.body_end)];
    if (info.is_raw) {
        if (info.is_bytes) {
            for (raw_inner) |raw_byte| {
                if (raw_byte >= 0x80) return error.InvalidStringLiteral;
            }
        }
        return allocator.dupe(u8, raw_inner);
    }

    var out_buf: std.ArrayList(u8) = .empty;
    errdefer out_buf.deinit(allocator);
    try out_buf.ensureTotalCapacity(allocator, raw_inner.len);
    try decodeEscapedStringSlice(allocator, raw_inner, info.is_bytes, info.is_fmt, &out_buf);
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
    /// Optional diagnostic sink receiving `E0101`–`E0118`, `E0203`, `W0101`, `W0119`, and `W0201` diagnostics.
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
    /// `true` while scanning at the top of the file before any non-module-doc comment or token.
    is_at_file_top: bool = true,

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
        self.is_at_file_top = (self.cursor == 0);
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

    /// Scans whitespace, `#!` shebang, `--- … ---` frontmatter, `/` docstrings, and `//` comments.
    fn scanLeadingTrivia(self: *Lexer, effective_max_tokens: usize, has_trivia_error: *bool) !void {
        // [1] Optional UTF-8 BOM, `#!` shebang, and `--- … ---` TOML frontmatter at start of file:
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
                if (self.cursor < self.source.len and self.source[self.cursor] == '\n') {
                    const lf_offset: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    try self.appendTriviaSpan(.newline_lf, lf_offset, 1, effective_max_tokens);
                } else if (self.cursor + 1 < self.source.len and
                    self.source[self.cursor] == '\r' and
                    self.source[self.cursor + 1] == '\n')
                {
                    const cr_offset: u32 = @intCast(self.cursor);
                    self.cursor += 2;
                    try self.appendTriviaSpan(.newline_crlf, cr_offset, 2, effective_max_tokens);
                }
            }
            if (matchScriptFrontmatterEnd(self.source, self.cursor)) |fm_end| {
                const fm_start: u32 = @intCast(self.cursor);
                while (self.cursor < fm_end) {
                    if (self.source[self.cursor] < 0x80) {
                        self.cursor += 1;
                    } else {
                        try self.validateAndAdvanceUtf8Codepoint(has_trivia_error);
                    }
                }
                self.trivia_acc.has_newline = true;
                try self.appendTriviaSpan(
                    .skipped_unexpected,
                    fm_start,
                    fm_end - @as(usize, fm_start),
                    effective_max_tokens,
                );
            }
        }

        // [2] Main trivia loop for spaces, tabs (`E0116`), newlines, and `/` DFA (`ADR-24A`):
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
                    const run_len: usize = self.cursor - @as(usize, run_start);
                    has_trivia_error.* = true;
                    try self.emitHardTabRunError(run_start, run_len, false);
                    try self.appendTriviaSpan(
                        .tabs,
                        run_start,
                        run_len,
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
                    if (second_byte == '|') {
                        self.is_at_file_top = false;
                        const comment_start: u32 = @intCast(self.cursor);
                        self.cursor += 2;
                        try self.scanCommentBodyToEndOfLine(has_trivia_error);
                        try self.appendTriviaSpan(
                            .doc_comment,
                            comment_start,
                            self.cursor - @as(usize, comment_start),
                            effective_max_tokens,
                        );
                    } else if (second_byte == '#') {
                        const comment_start: u32 = @intCast(self.cursor);
                        self.cursor += 2;
                        try self.scanCommentBodyToEndOfLine(has_trivia_error);
                        try self.appendTriviaSpan(
                            .module_doc_comment,
                            comment_start,
                            self.cursor - @as(usize, comment_start),
                            effective_max_tokens,
                        );
                    } else if (second_byte == '/') {
                        const comment_start: u32 = @intCast(self.cursor);
                        var comment_kind: TriviaKind = .line_comment;
                        if (self.cursor + 2 < self.source.len and self.source[self.cursor + 2] == '!') {
                            const was_at_top = self.is_at_file_top;
                            comment_kind = if (was_at_top) .module_doc_comment else .line_comment;
                            has_trivia_error.* = true;
                            try self.emitRetiredSlashDocError(comment_start, true, was_at_top);
                            self.cursor += 3;
                        } else if (self.cursor + 2 < self.source.len and
                            self.source[self.cursor + 2] == '/' and
                            (self.cursor + 3 >= self.source.len or
                                (self.source[self.cursor + 3] != '/' and
                                    self.source[self.cursor + 3] != '|' and
                                    self.source[self.cursor + 3] != '#')))
                        {
                            self.is_at_file_top = false;
                            comment_kind = .doc_comment;
                            has_trivia_error.* = true;
                            try self.emitRetiredSlashDocError(comment_start, false, false);
                            self.cursor += 3;
                        } else {
                            self.is_at_file_top = false;
                            self.cursor += 2;
                        }
                        try self.scanCommentBodyToEndOfLine(has_trivia_error);
                        try self.appendTriviaSpan(
                            comment_kind,
                            comment_start,
                            self.cursor - @as(usize, comment_start),
                            effective_max_tokens,
                        );
                    } else if (second_byte == '*') {
                        self.is_at_file_top = false;
                        const block_start: u32 = @intCast(self.cursor);
                        if (try self.scanRetiredBlockComment(has_trivia_error, true)) {
                            self.trivia_acc.has_newline = true;
                        }
                        try self.appendTriviaSpan(
                            .skipped_unexpected,
                            block_start,
                            self.cursor - @as(usize, block_start),
                            effective_max_tokens,
                        );
                    } else {
                        return;
                    }
                },
                else => {
                    if (byte_val >= 0x80) {
                        if (std.unicode.utf8ByteSequenceLength(byte_val)) |seq_len| {
                            if (self.cursor + seq_len <= self.source.len) {
                                if (std.unicode.utf8Decode(self.source[self.cursor .. self.cursor + seq_len])) |trojan_cp| {
                                    if (unicode_confusables.isTrojanControlCodepoint(trojan_cp, self.cursor)) {
                                        const cp_start: u32 = @intCast(self.cursor);
                                        self.cursor += seq_len;
                                        try self.appendTriviaSpan(
                                            .skipped_unexpected,
                                            cp_start,
                                            seq_len,
                                            effective_max_tokens,
                                        );
                                        try self.recordOrEmitLexLintCandidate(.{
                                            .rule_id = .unicode_trojan_control,
                                            .fix_kind = 2,
                                            .start_byte = cp_start,
                                            .end_byte = @intCast(self.cursor),
                                            .aux_payload = trojan_cp,
                                        });
                                        continue;
                                    }
                                } else |_| {}
                            }
                        } else |_| {}
                    }
                    return;
                },
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

    /// Advances `cursor` across a `//`, `/|`, or `/#` comment body, validating UTF-8 and rejecting `\t` (`E0116`).
    fn scanCommentBodyToEndOfLine(self: *Lexer, has_error: *bool) !void {
        const body_start = self.cursor;
        var saw_non_ascii = false;
        var had_utf8_err = false;
        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '\n' or byte_val == '\r') break;
            if (byte_val == '\t') {
                const tab_start: u32 = @intCast(self.cursor);
                self.cursor += 1;
                while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                    self.cursor += 1;
                }
                has_error.* = true;
                try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), false);
            } else if (byte_val < 0x80) {
                self.cursor += 1;
            } else {
                saw_non_ascii = true;
                var step_utf8_err = false;
                try self.validateAndAdvanceUtf8Codepoint(&step_utf8_err);
                if (step_utf8_err) {
                    has_error.* = true;
                    had_utf8_err = true;
                }
            }
        }
        if (saw_non_ascii and !had_utf8_err) {
            var dummy_raw_cook = false;
            try self.scanTextSegmentUnicodeLints(body_start, self.cursor, 2, 1, null, null, &dummy_raw_cook);
        }
    }

    /// Scans a retired `/* … */` block comment (`E0118`, plus `E0102` if unclosed), returning `true` if multiline.
    fn scanRetiredBlockComment(self: *Lexer, has_error: *bool, is_trivia_context: bool) !bool {
        const open_idx: usize = self.cursor;
        const open_start: u32 = @intCast(open_idx);
        self.cursor += 2;
        const body_start = self.cursor;
        var depth: u32 = 1;
        var has_newline = false;
        var had_inner_utf8_err = false;
        var saw_non_ascii = false;

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
                saw_non_ascii = true;
                var had_utf8_step_err = false;
                try self.validateAndAdvanceUtf8Codepoint(&had_utf8_step_err);
                if (had_utf8_step_err) {
                    has_error.* = true;
                    had_inner_utf8_err = true;
                }
            }
        }

        if (saw_non_ascii and !had_inner_utf8_err) {
            const body_end = if (depth == 0 and self.cursor >= 2) self.cursor - 2 else self.cursor;
            if (body_end > body_start) {
                var dummy_raw_cook = false;
                try self.scanTextSegmentUnicodeLints(body_start, body_end, 2, 1, null, null, &dummy_raw_cook);
            }
        }

        has_error.* = true;
        if (depth > 0) {
            const unclosed_span = Span.init(self.file_id, open_start, @intCast(self.cursor));
            try self.emitSimpleError(
                .e0118_block_doc_comment_forbidden,
                unclosed_span,
                "block comments `/* … */` are retired; use `//` line comments instead",
                "retired `/* … */` block comment",
            );
            try self.emitSimpleError(
                .e0102_unterminated_string_literal,
                unclosed_span,
                "unterminated block comment `/* … */`",
                "block comment opened here was never closed before end of file",
            );
        } else {
            try self.emitRetiredBlockCommentError(
                open_start,
                @intCast(self.cursor),
                is_trivia_context and !had_inner_utf8_err,
            );
        }
        return has_newline;
    }

    /// Appends `slice` into `builder`, expanding any literal `\t` bytes to 4 spaces.
    fn appendSliceExpandingTabs(
        arena_alloc: std.mem.Allocator,
        builder: *std.ArrayListUnmanaged(u8),
        slice: []const u8,
    ) !void {
        for (slice) |byte_val| {
            if (byte_val == '\t') {
                try builder.appendSlice(arena_alloc, "    ");
            } else {
                try builder.append(arena_alloc, byte_val);
            }
        }
    }

    /// Emits `E0118` (`e0118_block_doc_comment_forbidden`) for a closed `/* … */` comment with a `//` rewrite.
    fn emitRetiredBlockCommentError(
        self: *Lexer,
        open_start: u32,
        close_end: u32,
        can_emit_fix: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const comment_span = Span.init(self.file_id, open_start, close_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = comment_span,
            .label = "retired `/* … */` block comment; write `//` line comments instead",
            .style = .primary,
        }};
        const msg_text = "block comments `/* … */` are retired (`ADR-24A`); use `//` line comments instead";

        if (can_emit_fix) {
            if (self.interner) |str_interner| {
                const arena_alloc = sink.arena.asAllocator();
                const open_usize: usize = @intCast(open_start);
                const close_usize: usize = @intCast(close_end);
                if (close_usize >= open_usize + 4 and close_usize <= self.source.len) {
                    var line_start: usize = open_usize;
                    while (line_start > 0 and
                        self.source[line_start - 1] != '\n' and
                        self.source[line_start - 1] != '\r')
                    {
                        line_start -= 1;
                    }
                    var has_code_before = false;
                    var ws_end_idx: usize = line_start;
                    for (self.source[line_start..open_usize], 0..) |ind_byte, rel_idx| {
                        if (ind_byte != ' ' and ind_byte != '\t') {
                            has_code_before = true;
                            break;
                        }
                        ws_end_idx = line_start + rel_idx + 1;
                    }
                    var base_indent_buf: std.ArrayListUnmanaged(u8) = .empty;
                    try appendSliceExpandingTabs(
                        arena_alloc,
                        &base_indent_buf,
                        self.source[line_start..if (has_code_before) ws_end_idx else open_usize],
                    );

                    var inner = self.source[open_usize + 2 .. close_usize - 2];
                    if (inner.len >= 1 and (inner[0] == '*' or inner[0] == '!') and
                        (inner.len == 1 or inner[1] == ' ' or inner[1] == '\t' or inner[1] == '\n' or inner[1] == '\r'))
                    {
                        inner = inner[1..];
                    }

                    var builder: std.ArrayListUnmanaged(u8) = .empty;
                    const has_inner_newline = std.mem.indexOfAny(u8, inner, "\r\n") != null;
                    if (!has_inner_newline) {
                        const trimmed = std.mem.trim(u8, inner, " \t");
                        try builder.appendSlice(arena_alloc, "//");
                        if (trimmed.len > 0) {
                            try builder.append(arena_alloc, ' ');
                            try appendSliceExpandingTabs(arena_alloc, &builder, trimmed);
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
                                    try builder.appendSlice(arena_alloc, "// ");
                                    try appendSliceExpandingTabs(arena_alloc, &builder, first_trimmed);
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
                                    try builder.appendSlice(arena_alloc, base_indent_buf.items);
                                }
                                try builder.appendSlice(arena_alloc, "//");
                                if (content.len > 0) {
                                    try builder.append(arena_alloc, ' ');
                                    try appendSliceExpandingTabs(arena_alloc, &builder, content);
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
                            try builder.appendSlice(arena_alloc, "//");
                        }
                    }

                    var edit_end_usize: usize = close_usize;
                    var scan_after: usize = close_usize;
                    while (scan_after < self.source.len and
                        (self.source[scan_after] == ' ' or self.source[scan_after] == '\t'))
                    {
                        scan_after += 1;
                    }
                    const has_code_after = scan_after < self.source.len and
                        self.source[scan_after] != '\n' and
                        self.source[scan_after] != '\r';
                    if (has_code_after) {
                        edit_end_usize = scan_after;
                        try builder.append(arena_alloc, '\n');
                        try builder.appendSlice(arena_alloc, base_indent_buf.items);
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
                        .message = "rewrite `/* … */` block comment as `//` line comment(s)",
                        .applicability = if (has_code_before and has_code_after)
                            .maybe_incorrect
                        else
                            .machine_applicable,
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

    /// Emits `E0118` (`e0118_block_doc_comment_forbidden`) for retired `//!` or `///` prefixes (`ADR-24A`).
    fn emitRetiredSlashDocError(
        self: *Lexer,
        prefix_start: u32,
        is_bang_doc: bool,
        is_at_top: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const prefix_span = Span.init(self.file_id, prefix_start, prefix_start + 3);
        const replacement_text: []const u8 = if (is_bang_doc)
            (if (is_at_top) "/#" else "//")
        else
            "/|";
        const primary_labels = [_]LabeledSpan{.{
            .span = prefix_span,
            .label = if (is_bang_doc)
                (if (is_at_top)
                    "retired `//!` module doc prefix; use `/#` instead"
                else
                    "retired `//!` inner doc prefix; `/#` is valid only at top of file, use `//` here")
            else
                "retired `///` doc prefix; use `/|` instead",
            .style = .primary,
        }};
        const msg_text: []const u8 = if (is_bang_doc)
            "3-character doc prefix `//!` is retired (`ADR-24A`); use `/#` at top of file or `//` elsewhere"
        else
            "3-character doc prefix `///` is retired (`ADR-24A`); use `/|` for outer docstrings";

        if (self.interner) |str_interner| {
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = prefix_start,
                .end_byte = prefix_start + 3,
                .replacement_id = try str_interner.intern(replacement_text),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = if (is_bang_doc)
                    (if (is_at_top) "replace `//!` with `/#`" else "replace mid-file `//!` with `//`")
                else
                    "replace `///` with `/|`",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0118_block_doc_comment_forbidden,
                .severity = .err,
                .primary_span = prefix_span,
                .message = msg_text,
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
            return;
        }

        try sink.emit(.{
            .code = .e0118_block_doc_comment_forbidden,
            .severity = .err,
            .primary_span = prefix_span,
            .message = msg_text,
            .labels = &primary_labels,
        });
    }

    /// Emits `E0116` (`e0116_multiline_string_indent`) on a contiguous hard `\t` (`0x09`) run (`ADR-24B`).
    fn emitHardTabRunError(
        self: *Lexer,
        tab_start: u32,
        run_len: usize,
        replace_with_escape: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const tab_end: u32 = tab_start + @as(u32, @intCast(run_len));
        const tab_span = Span.init(self.file_id, tab_start, tab_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = tab_span,
            .label = if (replace_with_escape)
                "hard `\\t` tab byte is forbidden in cooked literals; write `\\t` escape instead"
            else
                "hard `\\t` tab character is forbidden in `.cx` files; use 4-space indentation",
            .style = .primary,
        }};
        const msg_text: []const u8 = if (replace_with_escape)
            "raw tab character (`0x09`) is not permitted in cooked literals; use `\\t` escape"
        else
            "hard tab indentation (`0x09`) is forbidden in `.cx` source files; use 4 ASCII spaces";

        if (self.interner) |str_interner| {
            const arena_alloc = sink.arena.asAllocator();
            const unit_len: usize = if (replace_with_escape) 2 else 4;
            const repl_buf = try arena_alloc.alloc(u8, run_len * unit_len);
            var idx: usize = 0;
            while (idx < run_len) : (idx += 1) {
                if (replace_with_escape) {
                    repl_buf[idx * 2] = '\\';
                    repl_buf[idx * 2 + 1] = 't';
                } else {
                    @memset(repl_buf[idx * 4 .. idx * 4 + 4], ' ');
                }
            }
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = tab_start,
                .end_byte = tab_end,
                .replacement_id = try str_interner.intern(repl_buf),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = if (replace_with_escape)
                    "escape literal tab as `\\t`"
                else
                    "replace hard tab(s) with 4-space indentation",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0116_multiline_string_indent,
                .severity = .err,
                .primary_span = tab_span,
                .message = msg_text,
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
            return;
        }

        try sink.emit(.{
            .code = .e0116_multiline_string_indent,
            .severity = .err,
            .primary_span = tab_span,
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
        self.is_at_file_top = false;
        var has_lexer_error = has_initial_error;
        const first_byte = self.source[token_start];

        const token_kind: TokenKind = if (first_byte == 'f' and
            token_start + 1 < self.source.len and
            (self.source[token_start + 1] == '"' or self.source[token_start + 1] == '#'))
            try self.scanFmtStringLiteral(1, &has_lexer_error)
        else if (first_byte == 'r' and
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
            else => blk_non_ascii: {
                if (first_byte >= 0x80) {
                    if (std.unicode.utf8ByteSequenceLength(first_byte)) |seq_len| {
                        if (self.cursor + seq_len <= self.source.len) {
                            if (std.unicode.utf8Decode(self.source[self.cursor .. self.cursor + seq_len])) |start_cp| {
                                if (!unicode_confusables.isTrojanControlCodepoint(start_cp, self.cursor) and
                                    unicode_confusables.isUnicodeXidStart(start_cp))
                                {
                                    break :blk_non_ascii try self.scanIdentifierOrKeyword(&has_lexer_error);
                                }
                            } else |_| {}
                        }
                    } else |_| {}
                }
                break :blk_non_ascii try self.scanInvalidByteOrUtf8(&has_lexer_error);
            },
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

    /// Scans an identifier, keyword, primitive type, or `_`, checking `DR-03` casing and `UAX #31` (`DR-25`).
    fn scanIdentifierOrKeyword(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        if (self.source[self.cursor] < 0x80) {
            self.cursor += 1;
        } else {
            const first_len = std.unicode.utf8ByteSequenceLength(self.source[self.cursor]) catch 1;
            self.cursor += @min(first_len, self.source.len - self.cursor);
        }

        while (self.cursor < self.source.len) {
            const cur_byte = self.source[self.cursor];
            if (cur_byte < 0x80) {
                if (isIdentContinue(cur_byte)) {
                    self.cursor += 1;
                    continue;
                }
                break;
            }
            const seq_len = std.unicode.utf8ByteSequenceLength(cur_byte) catch break;
            if (self.cursor + seq_len > self.source.len) break;
            const cont_cp = std.unicode.utf8Decode(self.source[self.cursor .. self.cursor + seq_len]) catch break;
            if (!unicode_confusables.isUnicodeXidContinue(cont_cp)) break;
            if (unicode_confusables.isTrojanControlCodepoint(cont_cp, self.cursor)) {
                try self.recordOrEmitLexLintCandidate(.{
                    .rule_id = .unicode_trojan_control,
                    .fix_kind = 0,
                    .start_byte = @intCast(self.cursor),
                    .end_byte = @intCast(self.cursor + seq_len),
                    .aux_payload = cont_cp,
                });
            }
            self.cursor += seq_len;
        }

        const lexeme = self.source[start_offset..self.cursor];
        const classification = classifyIdentifierOrKeyword(lexeme);

        if (classification.has_case_violation) {
            has_lexer_error.* = true;
            if (self.options.raw_lint_candidates_out == null and self.options.is_casing_warning_enabled) {
                try self.emitIdentifierCasingWarning(
                    Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                    lexeme,
                    classification.expected_case,
                );
            }
        }
        return classification.kind;
    }

    /// Checks whether `int_slice` violates `W0122` (`ungrouped-numeric-literal`) for `radix`, returning group width.
    fn checkNumericGroupingViolation(self: *const Lexer, int_slice: []const u8, radix: u8) ?u8 {
        var digit_count: usize = 0;
        var has_underscore = false;
        for (int_slice) |byte_val| {
            if (byte_val == '_') {
                has_underscore = true;
            } else {
                digit_count += 1;
            }
        }
        if (digit_count == 0) return null;

        const canonical_width: u8 = if (radix == 16 or radix == 2) 4 else 3;
        if (!has_underscore) {
            const threshold: usize = switch (radix) {
                10 => self.options.lint_settings.min_grouped_int_digits,
                16 => self.options.lint_settings.min_grouped_hex_digits,
                else => 5,
            };
            if (threshold > 0 and digit_count >= threshold) return canonical_width;
            return null;
        }

        const is_consistent_width = struct {
            fn check(slice: []const u8, width: usize) bool {
                var group_iter = std.mem.splitScalar(u8, slice, '_');
                const first_grp = group_iter.next() orelse return false;
                if (first_grp.len == 0 or first_grp.len > width) return false;
                while (group_iter.next()) |grp| {
                    if (grp.len != width) return false;
                }
                return true;
            }
        }.check;

        const is_valid_grouped = switch (radix) {
            10, 8 => is_consistent_width(int_slice, 3),
            16 => is_consistent_width(int_slice, 4) or is_consistent_width(int_slice, 2),
            2 => is_consistent_width(int_slice, 4) or is_consistent_width(int_slice, 8),
            else => true,
        };
        return if (is_valid_grouped) null else canonical_width;
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
                const int_digits_start = self.cursor;
                var digit_count: usize = 0;
                var is_prev_underscore = false;
                var has_lower_hex = false;

                if (self.cursor < self.source.len and self.source[self.cursor] == '_') {
                    is_malformed = true;
                }
                while (self.cursor < self.source.len) {
                    const byte_val = self.source[self.cursor];
                    if (isValidDigitForRadix(byte_val, radix)) {
                        if (radix == 16 and byte_val >= 'a' and byte_val <= 'f') {
                            has_lower_hex = true;
                        }
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
                const int_digits_end = self.cursor;
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
                } else {
                    const tok_start_u32: u32 = @intCast(start_offset);
                    const tok_end_u32: u32 = @intCast(self.cursor);
                    const int_end_u32: u32 = @intCast(int_digits_end);
                    const group_viol = self.checkNumericGroupingViolation(
                        self.source[int_digits_start..int_digits_end],
                        radix,
                    );
                    const has_hex_case_viol = (radix == 16) and
                        (self.source[start_offset + 1] == 'X' or has_lower_hex);
                    const is_standalone_fused = (self.options.raw_lint_candidates_out == null) and
                        (group_viol != null) and has_hex_case_viol;

                    if (group_viol) |grp_w| {
                        try self.recordOrEmitLexLintCandidate(.{
                            .rule_id = .ungrouped_numeric_literal,
                            .fix_kind = if (is_standalone_fused) 2 else 1,
                            .aux_u16 = (@as(u16, radix) << 8) | @as(u16, grp_w),
                            .start_byte = tok_start_u32,
                            .end_byte = tok_end_u32,
                            .aux_payload = (@as(u64, @as(u32, @intCast(int_digits_start))) << 32) | @as(u64, int_end_u32),
                        });
                    }
                    if (has_hex_case_viol) {
                        try self.recordOrEmitLexLintCandidate(.{
                            .rule_id = .non_upper_hex_literal,
                            .fix_kind = if (is_standalone_fused) 0 else 1,
                            .start_byte = tok_start_u32,
                            .end_byte = tok_end_u32,
                            .aux_payload = (@as(u64, int_end_u32) << 32) | @as(u64, tok_start_u32),
                        });
                    }
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
        const dec_int_end = self.cursor;
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
        } else if (self.checkNumericGroupingViolation(self.source[start_offset..dec_int_end], 10)) |grp_w| {
            try self.recordOrEmitLexLintCandidate(.{
                .rule_id = .ungrouped_numeric_literal,
                .fix_kind = 1,
                .aux_u16 = (@as(u16, 10) << 8) | @as(u16, grp_w),
                .start_byte = @intCast(start_offset),
                .end_byte = @intCast(self.cursor),
                .aux_payload = (@as(u64, @as(u32, @intCast(start_offset))) << 32) |
                    @as(u64, @as(u32, @intCast(dec_int_end))),
            });
        }
        return if (is_float) .float_lit else .int_lit;
    }

    /// Consumes `\n` or `\r\n` immediately following an opening `"`, returning `true` when multiline mode activates.
    fn consumeOptionalMultilineOpeningNewline(self: *Lexer) bool {
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
        return false;
    }

    /// Validates standalone `[ ]*"#*` closing placement (`E0115`) and space-only `< C` indentation (`E0116`).
    fn validateMultilineIndentation(
        self: *Lexer,
        body_start_offset: u32,
        close_quote_offset: usize,
        is_raw: bool,
        is_fmt: bool,
        has_lexer_error: *bool,
    ) !void {
        const body_after_open_nl = self.source[@as(usize, body_start_offset)..close_quote_offset];

        // [1] Locate the last outer `\n` separating content lines from the closing quote line:
        var last_outer_lf: ?usize = null;
        var scan_pos: usize = 0;
        while (findNextOuterLineFeed(body_after_open_nl, scan_pos, is_raw, is_fmt)) |lf_pos| {
            last_outer_lf = lf_pos;
            scan_pos = lf_pos + 1;
        }

        const close_line_rel_start: usize = if (last_outer_lf) |lf_idx| lf_idx + 1 else 0;
        const close_line_abs_start: u32 = body_start_offset + @as(u32, @intCast(close_line_rel_start));
        const close_prefix = body_after_open_nl[close_line_rel_start..];

        // [2] Enforce standalone `[ ]*"#*` on the closing line (`E0115` on content, `E0116` on `\t`):
        var has_non_ws_before_close = false;
        var close_leading_spaces: usize = 0;
        var counted_leading = true;
        for (close_prefix) |prefix_byte| {
            if (prefix_byte == ' ') {
                if (counted_leading) close_leading_spaces += 1;
            } else if (prefix_byte == '\t') {
                if (counted_leading) close_leading_spaces += 4;
            } else {
                has_non_ws_before_close = true;
                counted_leading = false;
            }
        }
        if (has_non_ws_before_close) {
            has_lexer_error.* = true;
            try self.emitMultilineClosingLineContentError(
                close_line_abs_start,
                @intCast(close_quote_offset),
                close_leading_spaces,
            );
            return;
        }

        var close_indent_cols: usize = 0;
        var prefix_idx: usize = 0;
        while (prefix_idx < close_prefix.len) {
            if (close_prefix[prefix_idx] == ' ') {
                close_indent_cols += 1;
                prefix_idx += 1;
            } else {
                const tab_run_start = prefix_idx;
                while (prefix_idx < close_prefix.len and close_prefix[prefix_idx] == '\t') {
                    prefix_idx += 1;
                }
                const run_len = prefix_idx - tab_run_start;
                close_indent_cols += run_len * 4;
                has_lexer_error.* = true;
                try self.emitHardTabRunError(
                    close_line_abs_start + @as(u32, @intCast(tab_run_start)),
                    run_len,
                    false,
                );
            }
        }

        const final_lf_idx = last_outer_lf orelse return;
        const content_end: usize = if (final_lf_idx > 0 and body_after_open_nl[final_lf_idx - 1] == '\r')
            final_lf_idx - 1
        else
            final_lf_idx;
        const content_bytes = body_after_open_nl[0..content_end];

        // [3] Validate `< C` leading spaces and `>= C` tab rules on every non-empty content line:
        var line_rel_start: usize = 0;
        while (true) {
            const maybe_lf = findNextOuterLineFeed(content_bytes, line_rel_start, is_raw, is_fmt);
            const raw_line_end = maybe_lf orelse content_bytes.len;
            const clean_line_end = if (raw_line_end > line_rel_start and content_bytes[raw_line_end - 1] == '\r')
                raw_line_end - 1
            else
                raw_line_end;
            const line_slice = content_bytes[line_rel_start..clean_line_end];
            const line_abs_start: u32 = body_start_offset + @as(u32, @intCast(line_rel_start));

            if (line_slice.len > 0) {
                var visual_col: usize = 0;
                var byte_idx: usize = 0;
                while (byte_idx < line_slice.len and visual_col < close_indent_cols) {
                    if (line_slice[byte_idx] == ' ') {
                        visual_col += 1;
                        byte_idx += 1;
                    } else if (line_slice[byte_idx] == '\t') {
                        const tab_run_start = byte_idx;
                        while (byte_idx < line_slice.len and
                            line_slice[byte_idx] == '\t' and
                            visual_col < close_indent_cols)
                        {
                            visual_col += 4;
                            byte_idx += 1;
                        }
                        has_lexer_error.* = true;
                        try self.emitHardTabRunError(
                            line_abs_start + @as(u32, @intCast(tab_run_start)),
                            byte_idx - tab_run_start,
                            false,
                        );
                    } else {
                        break;
                    }
                }

                if (byte_idx < line_slice.len and visual_col < close_indent_cols) {
                    has_lexer_error.* = true;
                    try self.emitUnderIndentedMultilineLineError(
                        line_abs_start,
                        line_abs_start + @as(u32, @intCast(byte_idx)),
                        close_indent_cols - visual_col,
                    );
                }

                // At column `>= C`: raw strings allow literal `\t`, whereas cooked strings require `\t` escape:
                if (!is_raw) {
                    var payload_idx = byte_idx;
                    while (payload_idx < line_slice.len) {
                        const cur_byte = line_slice[payload_idx];
                        if (cur_byte == '\\' and payload_idx + 1 < line_slice.len) {
                            payload_idx += 2;
                        } else if (is_fmt and cur_byte == '{') {
                            if (payload_idx + 1 < line_slice.len and line_slice[payload_idx + 1] == '{') {
                                payload_idx += 2;
                            } else {
                                payload_idx = skipInterpolationHoleInBody(line_slice, payload_idx);
                            }
                        } else if (cur_byte == '\t') {
                            const tab_run_start = payload_idx;
                            while (payload_idx < line_slice.len and line_slice[payload_idx] == '\t') {
                                payload_idx += 1;
                            }
                            has_lexer_error.* = true;
                            try self.emitHardTabRunError(
                                line_abs_start + @as(u32, @intCast(tab_run_start)),
                                payload_idx - tab_run_start,
                                true,
                            );
                        } else {
                            payload_idx += 1;
                        }
                    }
                }
            }

            if (maybe_lf) |lf_pos| {
                line_rel_start = lf_pos + 1;
            } else {
                break;
            }
        }
    }

    /// Scans a retired `"""…"""` literal (`E0115`) for single-token recovery and emits a `"<newline> … "` fix.
    fn scanRetiredTripleQuoteString(
        self: *Lexer,
        token_start: usize,
        hash_count: usize,
        is_raw: bool,
        is_bytes: bool,
        is_fmt: bool,
        has_lexer_error: *bool,
    ) !TokenKind {
        const result_kind: TokenKind = if (is_fmt)
            .fmt_string_lit
        else if (is_bytes)
            .byte_string_lit
        else
            .string_lit;

        const open_quote_pos = self.cursor;
        self.cursor += 3;
        var had_inner_err = false;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"' and
                self.cursor + 2 < self.source.len and
                self.source[self.cursor + 1] == '"' and
                self.source[self.cursor + 2] == '"' and
                hasExactHashesAt(self.source, self.cursor + 3, hash_count))
            {
                const close_quote_pos = self.cursor;
                self.cursor += 3 + hash_count;
                has_lexer_error.* = true;
                try self.emitRetiredTripleQuoteError(
                    @intCast(token_start),
                    @intCast(self.cursor),
                    self.source[open_quote_pos + 3 .. close_quote_pos],
                    hash_count,
                    is_raw,
                    is_bytes,
                    is_fmt,
                    !had_inner_err,
                );
                return result_kind;
            }
            if (!is_raw and byte_val == '\\') {
                const esc_ctx: EscapeContext = if (is_fmt)
                    .fmt_string
                else if (is_bytes)
                    .byte_string
                else
                    .plain_string;
                var step_err = false;
                try self.scanEscapeSequence(esc_ctx, &step_err);
                if (step_err) had_inner_err = true;
                continue;
            }
            if (!is_raw and !is_bytes and byte_val == '{') {
                if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '{') {
                    self.cursor += 2;
                    continue;
                }
                self.cursor = skipInterpolationHoleInBody(self.source, self.cursor);
                continue;
            }
            if (byte_val < 0x80) {
                self.cursor += 1;
            } else if (is_bytes) {
                const non_ascii_start = self.cursor;
                var is_bad_utf8 = false;
                try self.validateAndAdvanceUtf8Codepoint(&is_bad_utf8);
                had_inner_err = true;
                if (!is_bad_utf8) {
                    try self.emitSimpleError(
                        .e0117_non_ascii_byte_literal,
                        Span.init(self.file_id, @intCast(non_ascii_start), @intCast(self.cursor)),
                        "byte string literal may only contain ASCII bytes (`0x00..0x7F`)",
                        "non-ASCII character is not allowed in byte string literal",
                    );
                }
            } else {
                var step_err = false;
                try self.validateAndAdvanceUtf8Codepoint(&step_err);
                if (step_err) had_inner_err = true;
            }
        }

        has_lexer_error.* = true;
        const unclosed_span = Span.init(self.file_id, @intCast(token_start), @intCast(self.cursor));
        try self.emitSimpleError(
            .e0115_multiline_string_opening,
            Span.init(self.file_id, @intCast(open_quote_pos), @intCast(open_quote_pos + 3)),
            "triple-quoted `\"\"\"` string delimiters are retired (`ADR-24B`); open multiline strings with `\"<newline>`",
            "retired `\"\"\"` delimiter",
        );
        try self.emitSimpleError(
            .e0102_unterminated_string_literal,
            unclosed_span,
            "unterminated string literal",
            "string literal opened here was not closed before end of file",
        );
        return result_kind;
    }

    /// Scans a plain `"…"` or multiline `"\n … "` string literal (`TokenKind.string_lit`, literal `{` / `}`).
    fn scanStandardStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        if (isRetiredTripleQuoteOpening(self.source, self.cursor, 0)) {
            return self.scanRetiredTripleQuoteString(start_offset, 0, false, false, false, has_lexer_error);
        }

        self.cursor += 1;
        const is_multiline = self.consumeOptionalMultilineOpeningNewline();
        const body_start_offset: u32 = @intCast(self.cursor);
        var saw_non_ascii = false;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"') {
                const close_quote_offset = self.cursor;
                self.cursor += 1;
                if (is_multiline) {
                    try self.validateMultilineIndentation(
                        body_start_offset,
                        close_quote_offset,
                        false,
                        false,
                        has_lexer_error,
                    );
                }
                if (saw_non_ascii and !has_lexer_error.*) {
                    var dummy_raw_cook = false;
                    try self.scanTextSegmentUnicodeLints(
                        @intCast(body_start_offset),
                        close_quote_offset,
                        1,
                        3,
                        null,
                        null,
                        &dummy_raw_cook,
                    );
                }
                return .string_lit;
            }
            if (byte_val == '\\') {
                try self.scanEscapeSequence(.plain_string, has_lexer_error);
                continue;
            }
            if (byte_val == '\n' or byte_val == '\r') {
                if (!is_multiline) {
                    has_lexer_error.* = true;
                    try self.emitSimpleError(
                        .e0102_unterminated_string_literal,
                        Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                        "unterminated string literal",
                        "single-line string cannot span a raw newline; open with `\"<newline>` for multiline strings",
                    );
                    return .string_lit;
                }
                self.cursor += 1;
                continue;
            }
            if (byte_val == '\t') {
                if (!is_multiline) {
                    const tab_start: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                        self.cursor += 1;
                    }
                    has_lexer_error.* = true;
                    try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), true);
                    continue;
                }
                self.cursor += 1;
                continue;
            }
            if (byte_val < 0x80) {
                self.cursor += 1;
            } else {
                saw_non_ascii = true;
                try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
            }
        }

        has_lexer_error.* = true;
        try self.emitSimpleError(
            .e0102_unterminated_string_literal,
            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
            "unterminated string literal",
            "string literal opened here was not closed before end of file",
        );
        return .string_lit;
    }

    /// Scans an explicit `f"…"` or `f#"…"#` format string (`TokenKind.fmt_string_lit`, `DR-24` §1.2).
    fn scanFmtStringLiteral(self: *Lexer, fmt_depth: u32, has_lexer_error: *bool) anyerror!TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1; // Advance past `'f'`.

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
                "malformed or unterminated format string literal",
                "expected opening `\"` after `f` format string prefix",
            );
            return .fmt_string_lit;
        }

        if (hash_count > MAX_FMT_STRING_HASHES) {
            has_lexer_error.* = true;
        }

        if (isRetiredTripleQuoteOpening(self.source, self.cursor, hash_count)) {
            return self.scanRetiredTripleQuoteString(
                start_offset,
                hash_count,
                false,
                false,
                true,
                has_lexer_error,
            );
        }

        self.cursor += 1; // Advance past opening `'"'`.
        const is_multiline = self.consumeOptionalMultilineOpeningNewline();
        const body_start_offset: u32 = @intCast(self.cursor);

        var hole_count: u32 = 0;
        var brace_depth: u32 = 0;
        var paren_depth: u32 = 0;
        var bracket_depth: u32 = 0;
        var is_in_fmt_spec = false;
        var has_emitted_depth_error = false;
        var lit_seg_start: usize = self.cursor;
        var lit_seg_non_ascii = false;
        var has_lit_quote = false;
        var has_lit_backslash = false;
        var max_lit_quote_hashes: usize = 0;
        const initial_err_count: u32 = if (self.diagnostic_sink) |sink| sink.error_count else 0;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (brace_depth == 0) {
                if (byte_val == '"') {
                    if (hasExactHashesAt(self.source, self.cursor + 1, hash_count)) {
                        const close_quote_offset = self.cursor;
                        if (lit_seg_non_ascii and !has_lexer_error.*) {
                            var dummy_raw_cook = false;
                            try self.scanTextSegmentUnicodeLints(
                                lit_seg_start,
                                close_quote_offset,
                                1,
                                if (hash_count > 0) 2 else 3,
                                if (hash_count > 0) hash_count else null,
                                null,
                                &dummy_raw_cook,
                            );
                        }
                        self.cursor += 1 + hash_count;
                        if (hash_count > MAX_FMT_STRING_HASHES) {
                            try self.emitSimpleError(
                                .e0102_unterminated_string_literal,
                                Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                                "format string delimiter exceeds maximum of 15 `#` characters",
                                "reduce `#` quote-guard count to at most 15",
                            );
                        }
                        if (is_multiline) {
                            try self.validateMultilineIndentation(
                                body_start_offset,
                                close_quote_offset,
                                false,
                                true,
                                has_lexer_error,
                            );
                        }
                        if (hole_count == 0 and hash_count <= MAX_FMT_STRING_HASHES and !has_lexer_error.*) {
                            const had_inner_errors = if (self.diagnostic_sink) |sink|
                                sink.error_count > initial_err_count
                            else
                                false;
                            try self.emitUselessFormatStringWarning(
                                @intCast(start_offset),
                                @intCast(self.cursor),
                                hash_count,
                                !had_inner_errors,
                            );
                        } else if (hole_count > 0 and hash_count >= 1 and
                            hash_count <= MAX_FMT_STRING_HASHES and !has_lexer_error.*)
                        {
                            const req_hashes: usize = if (!has_lit_quote and !has_lit_backslash)
                                0
                            else if (has_lit_quote)
                                @max(@as(usize, 1), max_lit_quote_hashes)
                            else
                                1;
                            if (hash_count > req_hashes) {
                                try self.recordOrEmitLexLintCandidate(.{
                                    .rule_id = .needless_raw_string_hashes,
                                    .fix_kind = 5,
                                    .aux_u16 = @intCast(req_hashes),
                                    .start_byte = @intCast(start_offset),
                                    .end_byte = @intCast(self.cursor),
                                    .aux_payload = @intCast(hash_count),
                                });
                            }
                        }
                        return .fmt_string_lit;
                    }
                    has_lit_quote = true;
                    var q_hashes: usize = 0;
                    var q_scan = self.cursor + 1;
                    while (q_scan < self.source.len and self.source[q_scan] == '#') : (q_scan += 1) {
                        q_hashes += 1;
                    }
                    if (q_hashes + 1 > max_lit_quote_hashes) max_lit_quote_hashes = q_hashes + 1;
                    self.cursor += 1;
                    continue;
                }
                if (byte_val == '\\') {
                    has_lit_backslash = true;
                    try self.scanEscapeSequence(.fmt_string, has_lexer_error);
                    continue;
                }
                if (byte_val == '{') {
                    if (self.cursor + 1 < self.source.len and self.source[self.cursor + 1] == '{') {
                        self.cursor += 2;
                        continue;
                    }
                    if (lit_seg_non_ascii and !has_lexer_error.*) {
                        var dummy_raw_cook = false;
                        try self.scanTextSegmentUnicodeLints(
                            lit_seg_start,
                            self.cursor,
                            1,
                            if (hash_count > 0) 2 else 3,
                            if (hash_count > 0) hash_count else null,
                            null,
                            &dummy_raw_cook,
                        );
                    }
                    lit_seg_non_ascii = false;
                    hole_count += 1;
                    brace_depth = 1;
                    paren_depth = 0;
                    bracket_depth = 0;
                    is_in_fmt_spec = false;
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
                if (byte_val == '\n' or byte_val == '\r') {
                    if (!is_multiline) {
                        has_lexer_error.* = true;
                        try self.emitSimpleError(
                            .e0102_unterminated_string_literal,
                            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                            "unterminated format string literal",
                            "single-line format string cannot span a raw newline; open with `f\"<newline>`",
                        );
                        return .fmt_string_lit;
                    }
                    self.cursor += 1;
                    continue;
                }
                if (byte_val == '\t') {
                    if (!is_multiline) {
                        const tab_start: u32 = @intCast(self.cursor);
                        self.cursor += 1;
                        while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                            self.cursor += 1;
                        }
                        has_lexer_error.* = true;
                        try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), true);
                        continue;
                    }
                    self.cursor += 1;
                    continue;
                }
                if (byte_val < 0x80) {
                    self.cursor += 1;
                } else {
                    lit_seg_non_ascii = true;
                    try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                }
            } else {
                // Inside `{expr}` interpolation hole (`MAX_FMT_NESTING = 4`):
                if (byte_val == '{') {
                    brace_depth += 1;
                    if (brace_depth > syntax_arenas.MAX_PARSE_DEPTH and !has_emitted_depth_error) {
                        has_lexer_error.* = true;
                        has_emitted_depth_error = true;
                        try self.emitSimpleError(
                            .e0203_parse_depth_exceeded,
                            Span.init(self.file_id, @intCast(self.cursor), @intCast(self.cursor + 1)),
                            "nested brace depth inside format string exceeds maximum parse depth of 512",
                            "simplify deeply nested format hole expression",
                        );
                    }
                    self.cursor += 1;
                } else if (byte_val == '}') {
                    brace_depth -= 1;
                    self.cursor += 1;
                    if (brace_depth == 0) {
                        is_in_fmt_spec = false;
                        lit_seg_start = self.cursor;
                        lit_seg_non_ascii = false;
                    }
                } else if (is_in_fmt_spec) {
                    if ((byte_val == '\n' or byte_val == '\r') and !is_multiline) {
                        has_lexer_error.* = true;
                        try self.emitSimpleError(
                            .e0102_unterminated_string_literal,
                            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                            "unterminated format string interpolation hole",
                            "missing closing `}` before end of line",
                        );
                        return .fmt_string_lit;
                    } else if (byte_val == '\t') {
                        const tab_start: u32 = @intCast(self.cursor);
                        self.cursor += 1;
                        while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                            self.cursor += 1;
                        }
                        has_lexer_error.* = true;
                        try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), false);
                    } else if (byte_val < 0x80) {
                        self.cursor += 1;
                    } else {
                        try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                    }
                } else if (byte_val == '(') {
                    paren_depth += 1;
                    self.cursor += 1;
                } else if (byte_val == ')') {
                    if (paren_depth > 0) paren_depth -= 1;
                    self.cursor += 1;
                } else if (byte_val == '[') {
                    bracket_depth += 1;
                    self.cursor += 1;
                } else if (byte_val == ']') {
                    if (bracket_depth > 0) bracket_depth -= 1;
                    self.cursor += 1;
                } else if (byte_val == ':' and brace_depth == 1 and paren_depth == 0 and bracket_depth == 0) {
                    if (self.cursor + 1 < self.source.len and
                        self.source[self.cursor + 1] != ':' and
                        self.source[self.cursor + 1] != '=')
                    {
                        is_in_fmt_spec = true;
                    }
                    self.cursor += 1;
                } else if (byte_val == 'f' and
                    (self.cursor == 0 or !isIdentContinue(self.source[self.cursor - 1])) and
                    self.cursor + 1 < self.source.len and
                    (self.source[self.cursor + 1] == '"' or self.source[self.cursor + 1] == '#'))
                {
                    if (fmt_depth < MAX_FMT_NESTING) {
                        _ = try self.scanFmtStringLiteral(fmt_depth + 1, has_lexer_error);
                    } else {
                        if (!has_emitted_depth_error) {
                            has_lexer_error.* = true;
                            has_emitted_depth_error = true;
                            try self.emitSimpleError(
                                .e0203_parse_depth_exceeded,
                                Span.init(self.file_id, @intCast(self.cursor), @intCast(self.cursor + 2)),
                                "nested format string interpolation exceeds maximum depth of 4 (`MAX_FMT_NESTING`)",
                                "extract nested `f\"…\"` expression into a local binding",
                            );
                        }
                        self.cursor = skipFmtStringInExpr(self.source, self.cursor + 1);
                    }
                } else if (byte_val == 'r' and
                    (self.cursor == 0 or !isIdentContinue(self.source[self.cursor - 1])) and
                    self.cursor + 1 < self.source.len and
                    (self.source[self.cursor + 1] == '"' or self.source[self.cursor + 1] == '#'))
                {
                    _ = try self.scanRawStringLiteral(has_lexer_error);
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
                } else if (byte_val == '"') {
                    _ = try self.scanStandardStringLiteral(has_lexer_error);
                } else if (byte_val == '\'') {
                    _ = try self.scanCharLiteral(has_lexer_error);
                } else if (byte_val == '/' and self.cursor + 1 < self.source.len) {
                    const second_byte = self.source[self.cursor + 1];
                    if (second_byte == '|' or second_byte == '#') {
                        self.cursor += 2;
                        try self.scanCommentBodyToEndOfLine(has_lexer_error);
                    } else if (second_byte == '/') {
                        const cmt_start: u32 = @intCast(self.cursor);
                        if (self.cursor + 2 < self.source.len and self.source[self.cursor + 2] == '!') {
                            has_lexer_error.* = true;
                            try self.emitRetiredSlashDocError(cmt_start, true, false);
                            self.cursor += 3;
                        } else if (self.cursor + 2 < self.source.len and
                            self.source[self.cursor + 2] == '/' and
                            (self.cursor + 3 >= self.source.len or
                                (self.source[self.cursor + 3] != '/' and
                                    self.source[self.cursor + 3] != '|' and
                                    self.source[self.cursor + 3] != '#')))
                        {
                            has_lexer_error.* = true;
                            try self.emitRetiredSlashDocError(cmt_start, false, false);
                            self.cursor += 3;
                        } else {
                            self.cursor += 2;
                        }
                        try self.scanCommentBodyToEndOfLine(has_lexer_error);
                    } else if (second_byte == '*') {
                        _ = try self.scanRetiredBlockComment(has_lexer_error, false);
                    } else {
                        self.cursor += 1;
                    }
                } else if (byte_val == '\t') {
                    const tab_start: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                        self.cursor += 1;
                    }
                    has_lexer_error.* = true;
                    try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), false);
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
            "unterminated format string literal",
            "format string literal opened here was not closed before end of file",
        );
        return .fmt_string_lit;
    }

    /// Scans a raw string literal `r"…"` or `r#"…"#` (`0..255` `#` delimiters, single-line or `r"\n … "`).
    fn scanRawStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        try self.scanRawStringCommon(false, has_lexer_error);
        return .string_lit;
    }

    /// Scans a raw byte string literal `br"…"` or `br#"…"#` (`.byte_string_lit`).
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

        if (isRetiredTripleQuoteOpening(self.source, self.cursor, hash_count)) {
            _ = try self.scanRetiredTripleQuoteString(
                start_offset,
                hash_count,
                true,
                is_byte_mode,
                false,
                has_lexer_error,
            );
            return;
        }

        const open_quote_offset = self.cursor;
        self.cursor += 1;
        const is_multiline = self.consumeOptionalMultilineOpeningNewline();
        const body_start_offset: u32 = @intCast(self.cursor);
        var saw_non_ascii = false;

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"') {
                if (hasExactHashesAt(self.source, self.cursor + 1, hash_count)) {
                    const close_quote_offset = self.cursor;
                    self.cursor += 1 + hash_count;
                    if (hash_count > MAX_RAW_STRING_HASHES) {
                        try self.emitSimpleError(
                            .e0102_unterminated_string_literal,
                            Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                            "raw string delimiter exceeds maximum of 255 `#` characters",
                            "reduce `#` delimiter count to at most 255",
                        );
                    }
                    if (is_multiline) {
                        try self.validateMultilineIndentation(
                            body_start_offset,
                            close_quote_offset,
                            true,
                            false,
                            has_lexer_error,
                        );
                    }
                    var has_emitted_raw_cook = false;
                    if (!is_byte_mode and saw_non_ascii and !has_lexer_error.*) {
                        try self.scanTextSegmentUnicodeLints(
                            open_quote_offset + 1,
                            close_quote_offset,
                            3,
                            2,
                            hash_count,
                            .{ .start = @intCast(start_offset), .end = @intCast(self.cursor) },
                            &has_emitted_raw_cook,
                        );
                    }
                    if (!has_lexer_error.* and hash_count <= MAX_RAW_STRING_HASHES and !has_emitted_raw_cook) {
                        const raw_body = self.source[open_quote_offset + 1 .. close_quote_offset];
                        const has_quote = std.mem.indexOfScalar(u8, raw_body, '"') != null;
                        const has_backslash = std.mem.indexOfScalar(u8, raw_body, '\\') != null;
                        const has_tab = std.mem.indexOfScalar(u8, raw_body, '\t') != null;
                        if (!has_quote and !has_backslash and !has_tab) {
                            try self.recordOrEmitLexLintCandidate(.{
                                .rule_id = .needless_raw_string_hashes,
                                .fix_kind = if (is_byte_mode) 3 else 1,
                                .aux_u16 = 0,
                                .start_byte = @intCast(start_offset),
                                .end_byte = @intCast(self.cursor),
                                .aux_payload = @intCast(hash_count),
                            });
                        } else {
                            const req_hashes = if (has_quote)
                                lint_filter.computeMinRawQuoteGuardHashes(raw_body)
                            else
                                0;
                            if (hash_count > req_hashes) {
                                try self.recordOrEmitLexLintCandidate(.{
                                    .rule_id = .needless_raw_string_hashes,
                                    .fix_kind = if (is_byte_mode) 4 else 2,
                                    .aux_u16 = @intCast(req_hashes),
                                    .start_byte = @intCast(start_offset),
                                    .end_byte = @intCast(self.cursor),
                                    .aux_payload = @intCast(hash_count),
                                });
                            }
                        }
                    }
                    return;
                }
                self.cursor += 1;
            } else if ((byte_val == '\n' or byte_val == '\r') and !is_multiline) {
                has_lexer_error.* = true;
                try self.emitSimpleError(
                    .e0102_unterminated_string_literal,
                    Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                    if (is_byte_mode) "unterminated raw byte string literal" else "unterminated raw string literal",
                    "single-line raw string cannot span a newline; open with `\"<newline>` for multiline strings",
                );
                return;
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
                saw_non_ascii = true;
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

    /// Scans a cooked byte string literal `b"…"` or `b"\n … "` (`.byte_string_lit`, interpolation disabled).
    fn scanByteStringLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1; // Advance past `'b'`.
        if (isRetiredTripleQuoteOpening(self.source, self.cursor, 0)) {
            return self.scanRetiredTripleQuoteString(start_offset, 0, false, true, false, has_lexer_error);
        }

        self.cursor += 1;
        const is_multiline = self.consumeOptionalMultilineOpeningNewline();
        const body_start_offset: u32 = @intCast(self.cursor);

        while (self.cursor < self.source.len) {
            const byte_val = self.source[self.cursor];
            if (byte_val == '"') {
                const close_quote_offset = self.cursor;
                self.cursor += 1;
                if (is_multiline) {
                    try self.validateMultilineIndentation(
                        body_start_offset,
                        close_quote_offset,
                        false,
                        false,
                        has_lexer_error,
                    );
                }
                return .byte_string_lit;
            }
            if (byte_val == '\\') {
                try self.scanEscapeSequence(.byte_string, has_lexer_error);
                continue;
            }
            if (byte_val == '\n' or byte_val == '\r') {
                if (!is_multiline) {
                    has_lexer_error.* = true;
                    try self.emitSimpleError(
                        .e0102_unterminated_string_literal,
                        Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                        "unterminated byte string literal",
                        "single-line byte string cannot span a raw newline; open with `b\"<newline>`",
                    );
                    return .byte_string_lit;
                }
                self.cursor += 1;
                continue;
            }
            if (byte_val == '\t') {
                if (!is_multiline) {
                    const tab_start: u32 = @intCast(self.cursor);
                    self.cursor += 1;
                    while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                        self.cursor += 1;
                    }
                    has_lexer_error.* = true;
                    try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), true);
                    continue;
                }
                self.cursor += 1;
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
        const initial_diag_len: usize = if (self.diagnostic_sink) |sink| sink.asSlice().len else 0;
        const initial_cand_len: usize = if (self.options.raw_lint_candidates_out) |out| out.items.len else 0;

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
            if (byte_val == '\t') {
                const tab_start: u32 = @intCast(self.cursor);
                self.cursor += 1;
                while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                    self.cursor += 1;
                    byte_unit_count += 1;
                }
                byte_unit_count += 1;
                has_lexer_error.* = true;
                try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), true);
            } else if (byte_val == '\\') {
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
            self.rollbackRedundantEscapeWarningsSince(initial_diag_len, initial_cand_len);
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

    /// Scans a character literal `'c'`, emitting `E0102` (with `"…"` `SuggestedFix` on `'multi'`).
    fn scanCharLiteral(self: *Lexer, has_lexer_error: *bool) !TokenKind {
        const start_offset = self.cursor;
        self.cursor += 1; // Advance past opening `'\''`.
        const inner_start = self.cursor;
        var codepoint_count: usize = 0;
        var has_closing_quote = false;
        var saw_non_ascii = false;
        const initial_diag_len: usize = if (self.diagnostic_sink) |sink| sink.asSlice().len else 0;
        const initial_cand_len: usize = if (self.options.raw_lint_candidates_out) |out| out.items.len else 0;

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
            if (byte_val == '\t') {
                const tab_start: u32 = @intCast(self.cursor);
                self.cursor += 1;
                while (self.cursor < self.source.len and self.source[self.cursor] == '\t') {
                    self.cursor += 1;
                    codepoint_count += 1;
                }
                codepoint_count += 1;
                has_lexer_error.* = true;
                try self.emitHardTabRunError(tab_start, self.cursor - @as(usize, tab_start), true);
            } else if (byte_val == '\\') {
                try self.scanEscapeSequence(.char_literal, has_lexer_error);
                codepoint_count += 1;
            } else if (byte_val < 0x80) {
                self.cursor += 1;
                codepoint_count += 1;
            } else {
                saw_non_ascii = true;
                try self.validateAndAdvanceUtf8Codepoint(has_lexer_error);
                codepoint_count += 1;
            }
        }

        if (!has_closing_quote or codepoint_count != 1) {
            self.rollbackRedundantEscapeWarningsSince(initial_diag_len, initial_cand_len);
            has_lexer_error.* = true;
            if (has_closing_quote and codepoint_count > 1) {
                const had_inner_diags = if (self.diagnostic_sink) |sink|
                    sink.asSlice().len > initial_diag_len
                else
                    false;
                try self.emitMultiCharLiteralError(
                    @intCast(start_offset),
                    @intCast(self.cursor),
                    !had_inner_diags,
                );
            } else {
                try self.emitSimpleError(
                    .e0102_unterminated_string_literal,
                    Span.init(self.file_id, @intCast(start_offset), @intCast(self.cursor)),
                    if (!has_closing_quote)
                        "unterminated character literal"
                    else
                        "empty character literal `''`",
                    "expected a single character or escape sequence enclosed in `'…'`",
                );
            }
        } else if (saw_non_ascii and !has_lexer_error.* and self.cursor >= inner_start + 1) {
            var dummy_raw_cook = false;
            try self.scanTextSegmentUnicodeLints(
                inner_start,
                self.cursor - 1,
                1,
                4,
                null,
                null,
                &dummy_raw_cook,
            );
        }
        return .char_lit;
    }

    /// Validates a `\` escape sequence at `self.cursor` under `escape_ctx`.
    fn scanEscapeSequence(self: *Lexer, escape_ctx: EscapeContext, has_lexer_error: *bool) !void {
        const escape_start = self.cursor;
        self.cursor += 1; // Advance past `'\\'`.
        if (self.cursor >= self.source.len) return;

        const is_string_like = escape_ctx == .plain_string or
            escape_ctx == .fmt_string or
            escape_ctx == .byte_string;
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
                if (escape_ctx == .fmt_string) {
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

    /// Emits `E0102` on a multi-character `'abc'` literal with a `.machine_applicable` `"abc"` fix (`ADR-24B`).
    fn emitMultiCharLiteralError(
        self: *Lexer,
        lit_start: u32,
        lit_end: u32,
        can_emit_fix: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const lit_span = Span.init(self.file_id, lit_start, lit_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = lit_span,
            .label = "single quotes `'…'` are reserved for single `char` scalars; use `\"…\"` for strings",
            .style = .primary,
        }};
        const msg_text = "character literal may only contain a single Unicode scalar value";

        if (can_emit_fix) {
            if (self.interner) |str_interner| {
                const start_usize: usize = @intCast(lit_start);
                const end_usize: usize = @intCast(lit_end);
                if (end_usize >= start_usize + 2 and end_usize <= self.source.len) {
                    const arena_alloc = sink.arena.asAllocator();
                    const inner = self.source[start_usize + 1 .. end_usize - 1];
                    var builder: std.ArrayListUnmanaged(u8) = .empty;
                    try builder.append(arena_alloc, '"');
                    var idx: usize = 0;
                    while (idx < inner.len) {
                        if (inner[idx] == '\\' and idx + 1 < inner.len) {
                            if (inner[idx + 1] == '\'') {
                                try builder.append(arena_alloc, '\'');
                            } else {
                                try builder.appendSlice(arena_alloc, inner[idx .. idx + 2]);
                            }
                            idx += 2;
                        } else if (inner[idx] == '"') {
                            try builder.appendSlice(arena_alloc, "\\\"");
                            idx += 1;
                        } else {
                            try builder.append(arena_alloc, inner[idx]);
                            idx += 1;
                        }
                    }
                    try builder.append(arena_alloc, '"');

                    const fix_edits = try arena_alloc.alloc(TextEdit, 1);
                    fix_edits[0] = .{
                        .file_id = self.file_id,
                        .start_byte = lit_start,
                        .end_byte = lit_end,
                        .replacement_id = try str_interner.intern(builder.items),
                    };
                    const fixes = try arena_alloc.alloc(SuggestedFix, 1);
                    fixes[0] = .{
                        .message = "replace single quotes with double quotes",
                        .applicability = .machine_applicable,
                        .priority = .syntax_canonicalization,
                        .edits = fix_edits,
                    };
                    try sink.emit(.{
                        .code = .e0102_unterminated_string_literal,
                        .severity = .err,
                        .primary_span = lit_span,
                        .message = msg_text,
                        .labels = &primary_labels,
                        .suggestions = fixes,
                    });
                    return;
                }
            }
        }

        try sink.emit(.{
            .code = .e0102_unterminated_string_literal,
            .severity = .err,
            .primary_span = lit_span,
            .message = msg_text,
            .labels = &primary_labels,
        });
    }

    /// Emits `E0115` when non-space characters precede closing `"` on a multiline string's closing line.
    fn emitMultilineClosingLineContentError(
        self: *Lexer,
        close_line_start: u32,
        close_quote_offset: u32,
        indent_spaces: usize,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const err_span = Span.init(self.file_id, close_line_start, close_quote_offset + 1);
        const primary_labels = [_]LabeledSpan{.{
            .span = err_span,
            .label = "closing `\"` of multiline string must sit on its own space-indented line",
            .style = .primary,
        }};
        const msg_text = "multiline string closing delimiter must appear on a standalone space-indented line";

        if (self.interner) |str_interner| {
            const arena_alloc = sink.arena.asAllocator();
            const repl_buf = try arena_alloc.alloc(u8, 1 + indent_spaces);
            repl_buf[0] = '\n';
            @memset(repl_buf[1..], ' ');
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = close_quote_offset,
                .end_byte = close_quote_offset,
                .replacement_id = try str_interner.intern(repl_buf),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "move closing `\"` onto its own indented line",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0115_multiline_string_opening,
                .severity = .err,
                .primary_span = err_span,
                .message = msg_text,
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
            return;
        }

        try sink.emit(.{
            .code = .e0115_multiline_string_opening,
            .severity = .err,
            .primary_span = err_span,
            .message = msg_text,
            .labels = &primary_labels,
        });
    }

    /// Emits `E0116` when a non-empty multiline string content line has `< C` leading ASCII spaces.
    fn emitUnderIndentedMultilineLineError(
        self: *Lexer,
        line_start_byte: u32,
        ws_end_byte: u32,
        missing_spaces: usize,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const err_span = Span.init(self.file_id, line_start_byte, @max(ws_end_byte, line_start_byte + 1));
        const primary_labels = [_]LabeledSpan{.{
            .span = err_span,
            .label = "content line has fewer leading spaces than the closing quote column",
            .style = .primary,
        }};
        const msg_text = "multiline string content line is indented less than the closing quote column";

        if (self.interner) |str_interner| {
            const arena_alloc = sink.arena.asAllocator();
            const pad_buf = try arena_alloc.alloc(u8, missing_spaces);
            @memset(pad_buf, ' ');
            const fix_edits = [_]TextEdit{.{
                .file_id = self.file_id,
                .start_byte = line_start_byte,
                .end_byte = line_start_byte,
                .replacement_id = try str_interner.intern(pad_buf),
            }};
            const fixes = [_]SuggestedFix{.{
                .message = "indent content line to match closing quote column",
                .applicability = .machine_applicable,
                .priority = .syntax_canonicalization,
                .edits = &fix_edits,
            }};
            try sink.emit(.{
                .code = .e0116_multiline_string_indent,
                .severity = .err,
                .primary_span = err_span,
                .message = msg_text,
                .labels = &primary_labels,
                .suggestions = &fixes,
            });
            return;
        }

        try sink.emit(.{
            .code = .e0116_multiline_string_indent,
            .severity = .err,
            .primary_span = err_span,
            .message = msg_text,
            .labels = &primary_labels,
        });
    }

    /// Computes the minimum `#` guard count (`>= min_hashes`) so `"` + `#^count` does not occur in `payload`.
    fn computeRequiredQuoteGuardHashes(
        payload: []const u8,
        min_hashes: usize,
        is_raw: bool,
        is_fmt: bool,
    ) usize {
        var needed: usize = min_hashes;
        var cursor: usize = 0;
        while (cursor < payload.len) {
            const cur_byte = payload[cursor];
            if (!is_raw and cur_byte == '\\' and cursor + 1 < payload.len) {
                cursor += 2;
                continue;
            }
            if (is_fmt and cur_byte == '{') {
                if (cursor + 1 < payload.len and payload[cursor + 1] == '{') {
                    cursor += 2;
                    continue;
                }
                cursor = skipInterpolationHoleInBody(payload, cursor);
                continue;
            }
            if (cur_byte == '"') {
                var run_hashes: usize = 0;
                var scan_idx = cursor + 1;
                while (scan_idx < payload.len and payload[scan_idx] == '#') : (scan_idx += 1) {
                    run_hashes += 1;
                }
                if (run_hashes + 1 > needed) {
                    needed = run_hashes + 1;
                }
                cursor = scan_idx;
                continue;
            }
            cursor += 1;
        }
        return needed;
    }

    /// Emits `E0115` for retired `"""` delimiters with a `.machine_applicable` `"<newline> … "` rewrite.
    fn emitRetiredTripleQuoteError(
        self: *Lexer,
        lit_start: u32,
        lit_end: u32,
        raw_inner: []const u8,
        hash_count: usize,
        is_raw: bool,
        is_bytes: bool,
        is_fmt: bool,
        can_emit_fix: bool,
    ) !void {
        const sink = self.diagnostic_sink orelse return;
        const lit_span = Span.init(self.file_id, lit_start, lit_end);
        const primary_labels = [_]LabeledSpan{.{
            .span = lit_span,
            .label = "retired `\"\"\"` delimiter; open multiline strings with `\"<newline>` instead",
            .style = .primary,
        }};
        const msg_text = "triple-quoted `\"\"\"` string delimiters are retired (`ADR-24B`); use `\"<newline> … \"`";

        if (can_emit_fix) {
            if (self.interner) |str_interner| {
                const arena_alloc = sink.arena.asAllocator();
                var open_nl_len: usize = 0;
                if (raw_inner.len >= 1 and raw_inner[0] == '\n') {
                    open_nl_len = 1;
                } else if (raw_inner.len >= 2 and raw_inner[0] == '\r' and raw_inner[1] == '\n') {
                    open_nl_len = 2;
                }

                var normalized_body: []const u8 = raw_inner;
                var is_valid_multiline_shape = false;
                if (open_nl_len > 0) {
                    if (validateMultilineStringBodyPure(raw_inner[open_nl_len..], is_raw, is_fmt)) |_| {
                        is_valid_multiline_shape = true;
                    } else |_| {}
                } else if (std.mem.indexOfScalar(u8, raw_inner, '\t') == null) {
                    var wrapped: std.ArrayListUnmanaged(u8) = .empty;
                    try wrapped.append(arena_alloc, '\n');
                    try wrapped.appendSlice(arena_alloc, raw_inner);
                    try wrapped.append(arena_alloc, '\n');
                    if (validateMultilineStringBodyPure(wrapped.items[1..], is_raw, is_fmt)) |_| {
                        normalized_body = wrapped.items;
                        is_valid_multiline_shape = true;
                    } else |_| {}
                }

                if (is_valid_multiline_shape) {
                    var builder: std.ArrayListUnmanaged(u8) = .empty;
                    if (is_raw or is_fmt) {
                        const guard_hashes = computeRequiredQuoteGuardHashes(
                            normalized_body,
                            hash_count,
                            is_raw,
                            is_fmt,
                        );
                        if (!is_fmt or guard_hashes <= MAX_FMT_STRING_HASHES) {
                            if (is_fmt) {
                                try builder.append(arena_alloc, 'f');
                            } else if (is_bytes) {
                                try builder.appendSlice(arena_alloc, "br");
                            } else {
                                try builder.append(arena_alloc, 'r');
                            }
                            var h_idx: usize = 0;
                            while (h_idx < guard_hashes) : (h_idx += 1) {
                                try builder.append(arena_alloc, '#');
                            }
                            try builder.append(arena_alloc, '"');
                            try builder.appendSlice(arena_alloc, normalized_body);
                            try builder.append(arena_alloc, '"');
                            h_idx = 0;
                            while (h_idx < guard_hashes) : (h_idx += 1) {
                                try builder.append(arena_alloc, '#');
                            }
                        }
                    } else {
                        if (is_bytes) {
                            try builder.append(arena_alloc, 'b');
                        }
                        try builder.append(arena_alloc, '"');
                        var idx: usize = 0;
                        while (idx < normalized_body.len) {
                            if (normalized_body[idx] == '\\' and idx + 1 < normalized_body.len) {
                                try builder.appendSlice(arena_alloc, normalized_body[idx .. idx + 2]);
                                idx += 2;
                            } else if (normalized_body[idx] == '"') {
                                try builder.appendSlice(arena_alloc, "\\\"");
                                idx += 1;
                            } else {
                                try builder.append(arena_alloc, normalized_body[idx]);
                                idx += 1;
                            }
                        }
                        try builder.append(arena_alloc, '"');
                    }

                    if (builder.items.len > 0) {
                        const fix_edits = try arena_alloc.alloc(TextEdit, 1);
                        fix_edits[0] = .{
                            .file_id = self.file_id,
                            .start_byte = lit_start,
                            .end_byte = lit_end,
                            .replacement_id = try str_interner.intern(builder.items),
                        };
                        const fixes = try arena_alloc.alloc(SuggestedFix, 1);
                        fixes[0] = .{
                            .message = "replace retired `\"\"\"` delimiter with `\"<newline> … \"`",
                            .applicability = .machine_applicable,
                            .priority = .syntax_canonicalization,
                            .edits = fix_edits,
                        };
                        try sink.emit(.{
                            .code = .e0115_multiline_string_opening,
                            .severity = .err,
                            .primary_span = lit_span,
                            .message = msg_text,
                            .labels = &primary_labels,
                            .suggestions = fixes,
                        });
                        return;
                    }
                }
            }
        }

        try sink.emit(.{
            .code = .e0115_multiline_string_opening,
            .severity = .err,
            .primary_span = lit_span,
            .message = msg_text,
            .labels = &primary_labels,
        });
    }

    /// Appends `cand` to `raw_lint_candidates_out` (`CompilerDb`) or materializes directly into `diagnostic_sink`.
    fn recordOrEmitLexLintCandidate(self: *Lexer, cand: lint_filter.RawLintCandidate) !void {
        if (self.options.raw_lint_candidates_out) |out_list| {
            try out_list.append(self.token_buffer.allocator, cand);
            return;
        }
        const is_standalone_emitted = switch (cand.rule_id) {
            .redundant_escape_sequence,
            .unicode_trojan_control,
            .ambiguous_unicode_text,
            .useless_format_string,
            => true,
            else => false,
        };
        if (!is_standalone_emitted) return;
        if (self.diagnostic_sink) |sink| {
            try lint_filter.materializeLexCstLintCandidate(
                self.source,
                self.file_id,
                self.interner,
                cand,
                sink,
            );
        }
    }

    /// Rolls back `W0101` candidates/warnings emitted inside a malformed or multi-char `'…'` / `b'…'` literal.
    fn rollbackRedundantEscapeWarningsSince(
        self: *Lexer,
        initial_diag_len: usize,
        initial_cand_len: usize,
    ) void {
        if (self.options.raw_lint_candidates_out) |out_list| {
            var write_idx = initial_cand_len;
            var read_idx = initial_cand_len;
            while (read_idx < out_list.items.len) : (read_idx += 1) {
                if (out_list.items[read_idx].rule_id != .redundant_escape_sequence) {
                    out_list.items[write_idx] = out_list.items[read_idx];
                    write_idx += 1;
                }
            }
            out_list.items.len = write_idx;
            return;
        }
        if (self.diagnostic_sink) |sink| {
            var write_idx = initial_diag_len;
            var read_idx = initial_diag_len;
            while (read_idx < sink.diagnostics.items.len) : (read_idx += 1) {
                const diag_item = sink.diagnostics.items[read_idx];
                if (diag_item.code == .w0101_redundant_escape_sequence) {
                    sink.warning_count -|= 1;
                } else {
                    sink.diagnostics.items[write_idx] = diag_item;
                    write_idx += 1;
                }
            }
            sink.diagnostics.items.len = write_idx;
        }
    }

    /// Scans `source[seg_start .. seg_end]` (invoked only when `saw_non_ascii` is true) for `W0102` and `W0104`.
    fn scanTextSegmentUnicodeLints(
        self: *Lexer,
        seg_start: usize,
        seg_end: usize,
        w0102_fix_kind: u8,
        w0104_fix_kind: u8,
        quote_guard_hashes: ?usize,
        raw_lit_bounds: ?struct { start: u32, end: u32 },
        has_emitted_raw_cook: *bool,
    ) !void {
        if (seg_start >= seg_end or seg_end > self.source.len) return;
        const seg_slice = self.source[seg_start..seg_end];
        var pure_word_skip_until: usize = 0;
        var mixed_word_until: usize = 0;

        var rel_pos: usize = 0;
        while (rel_pos < seg_slice.len) {
            const cur_byte = seg_slice[rel_pos];
            if (cur_byte < 0x80) {
                if (w0104_fix_kind >= 3 and cur_byte == '\\' and rel_pos + 1 < seg_slice.len) {
                    rel_pos += 2;
                    continue;
                }
                rel_pos += 1;
                continue;
            }
            const seq_len = std.unicode.utf8ByteSequenceLength(cur_byte) catch {
                rel_pos += 1;
                continue;
            };
            if (rel_pos + seq_len > seg_slice.len) break;
            const decoded_cp = std.unicode.utf8Decode(seg_slice[rel_pos .. rel_pos + seq_len]) catch {
                rel_pos += seq_len;
                continue;
            };
            const abs_start = seg_start + rel_pos;
            const abs_end = abs_start + seq_len;

            if (unicode_confusables.isTrojanControlCodepoint(decoded_cp, abs_start)) {
                const eff_fix: u8 = if (w0102_fix_kind == 3) blk_raw: {
                    if (has_emitted_raw_cook.*) break :blk_raw 0;
                    has_emitted_raw_cook.* = true;
                    break :blk_raw 3;
                } else w0102_fix_kind;
                const payload: u64 = if (eff_fix == 3 and raw_lit_bounds != null)
                    (@as(u64, raw_lit_bounds.?.end) << 32) | @as(u64, decoded_cp)
                else
                    @as(u64, decoded_cp);
                const tok_start_u32: u32 = if (eff_fix == 3 and raw_lit_bounds != null)
                    raw_lit_bounds.?.start
                else
                    0;
                try self.recordOrEmitLexLintCandidate(.{
                    .rule_id = .unicode_trojan_control,
                    .fix_kind = eff_fix,
                    .start_byte = @intCast(abs_start),
                    .end_byte = @intCast(abs_end),
                    .node_or_tok = tok_start_u32,
                    .aux_payload = payload,
                });
                rel_pos += seq_len;
                continue;
            }

            if (!self.options.lint_settings.isAllowedConfusable(decoded_cp)) {
                if (unicode_confusables.lookupConfusable(decoded_cp)) |entry| {
                    if (entry.isStandaloneImpostor()) {
                        const is_quote_guard_hazard = if (quote_guard_hashes) |guard_hashes|
                            entry.skelByte0() == '"' and
                                (hasExactHashesAt(self.source, abs_end, guard_hashes) or
                                    (guard_hashes > 0 and abs_start == seg_start and
                                        abs_end + 1 < self.source.len and
                                        self.source[abs_end] == '"' and
                                        (self.source[abs_end + 1] == '\n' or
                                            (self.source[abs_end + 1] == '\r' and
                                                abs_end + 2 < self.source.len and
                                                self.source[abs_end + 2] == '\n'))))
                        else
                            false;
                        const eff_w0104_fix: u8 = if (is_quote_guard_hazard)
                            0
                        else
                            w0104_fix_kind;
                        try self.recordOrEmitLexLintCandidate(.{
                            .rule_id = .ambiguous_unicode_text,
                            .fix_kind = eff_w0104_fix,
                            .start_byte = @intCast(abs_start),
                            .end_byte = @intCast(abs_end),
                            .aux_payload = decoded_cp,
                        });
                    } else if (entry.isIdentConfusable() and rel_pos >= pure_word_skip_until) {
                        var is_mixed = rel_pos < mixed_word_until;
                        if (!is_mixed) {
                            var word_end_rel: usize = rel_pos + seq_len;
                            is_mixed = unicode_confusables.isMixedScriptWordAt(
                                seg_slice,
                                rel_pos,
                                rel_pos + seq_len,
                                &word_end_rel,
                            );
                            if (is_mixed) {
                                mixed_word_until = word_end_rel;
                            } else {
                                pure_word_skip_until = word_end_rel;
                            }
                        }
                        if (is_mixed) {
                            try self.recordOrEmitLexLintCandidate(.{
                                .rule_id = .ambiguous_unicode_text,
                                .fix_kind = w0104_fix_kind,
                                .start_byte = @intCast(abs_start),
                                .end_byte = @intCast(abs_end),
                                .aux_payload = decoded_cp,
                            });
                        }
                    }
                }
            }
            rel_pos += seq_len;
        }
    }

    /// Emits `W0119` (`w0119_useless_format_string`) on a 0-hole `f"…"` / `f#"…"#` literal (`ADR-24B`).
    fn emitUselessFormatStringWarning(
        self: *Lexer,
        lit_start: u32,
        lit_end: u32,
        hash_count: usize,
        can_emit_fix: bool,
    ) !void {
        try self.recordOrEmitLexLintCandidate(.{
            .rule_id = .useless_format_string,
            .fix_kind = if (can_emit_fix) 1 else 0,
            .aux_u16 = @intCast(hash_count),
            .start_byte = lit_start,
            .end_byte = lit_end,
        });
    }

    /// Emits `W0101` (`w0101_redundant_escape_sequence`) with a `.machine_applicable` fix replacing `\c` with `c`.
    fn emitRedundantEscapeWarning(self: *Lexer, escape_start: u32, escape_end: u32) !void {
        try self.recordOrEmitLexLintCandidate(.{
            .rule_id = .redundant_escape_sequence,
            .fix_kind = 1,
            .start_byte = escape_start,
            .end_byte = escape_end,
        });
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

/// Tokenizes `source` into `token_buffer` in a single linear pass with explicit `LexerOptions`.
pub fn tokenizeWithOptions(
    source: []const u8,
    file_id: FileId,
    token_buffer: *TokenBuffer,
    diagnostic_sink: ?*DiagnosticSink,
    interner: ?*StringInterner,
    options: LexerOptions,
) !void {
    var lexer_instance = Lexer.initWithOptions(source, file_id, token_buffer, diagnostic_sink, interner, options);
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
        \\// Range, method call, raw string, and nested f-string interpolation:
        \\fn demo() {
        \\    for i in 0..10 {
        \\        let m = 10.max(20);
        \\        let msg = f"val={if i > 0 => "ok }}" else r#"raw } str"#}\n";
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

    // Verify `0..10`, `10.max(20)`, and `f"…"` (`.fmt_string_lit`) tokenization:
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(8)).kind);
    try std.testing.expectEqual(TokenKind.dotdot, token_buf.getToken(TokenIndex.fromInt(9)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(10)).kind);
    try std.testing.expectEqual(TokenKind.int_lit, token_buf.getToken(TokenIndex.fromInt(15)).kind);
    try std.testing.expectEqual(TokenKind.dot, token_buf.getToken(TokenIndex.fromInt(16)).kind);
    try std.testing.expectEqual(TokenKind.ident, token_buf.getToken(TokenIndex.fromInt(17)).kind);
    try std.testing.expectEqual(TokenKind.fmt_string_lit, token_buf.getToken(TokenIndex.fromInt(25)).kind);

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
    // Multi-scalar `'ab'` must attach a `.machine_applicable` `"ab"` `SuggestedFix`:
    try std.testing.expectEqual(@as(usize, 1), sink.asSlice()[7].suggestions.len);
    try std.testing.expectEqualStrings(
        "\"ab\"",
        interner.get(sink.asSlice()[7].suggestions[0].edits[0].replacement_id),
    );

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

test "test_deep_nested_fmt_string_interpolation_bounded_stack_and_lossless" {
    // 4-deep `f"…"` (`== MAX_FMT_NESTING`) succeeds with 0 errors; 5-deep (`> MAX_FMT_NESTING`) emits `E0203`:
    const valid_4_deep = "f\"{f\"{f\"{f\"{x}\"}\"}\"}\"";
    var ok_buf = TokenBuffer.init(std.testing.allocator);
    defer ok_buf.deinit();
    var ok_sink = DiagnosticSink.init(std.testing.allocator);
    defer ok_sink.deinit();
    try tokenize(valid_4_deep, FileId.fromInt(0), &ok_buf, &ok_sink, null);
    try std.testing.expectEqual(@as(u32, 0), ok_sink.error_count);
    try std.testing.expectEqual(TokenKind.fmt_string_lit, ok_buf.getToken(TokenIndex.fromInt(0)).kind);

    const depth: usize = 8;
    var nested_builder: std.ArrayList(u8) = .empty;
    defer nested_builder.deinit(std.testing.allocator);
    try nested_builder.appendSlice(std.testing.allocator, "f\"");
    var i: usize = 0;
    while (i < depth) : (i += 1) {
        try nested_builder.appendSlice(std.testing.allocator, "{f\"");
    }
    try nested_builder.appendSlice(std.testing.allocator, "{leaf}");
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

    // Unclosed 5-deep `f"…"` emits `E0203` plus `E0102`:
    const unclosed_slice = "f\"{f\"{f\"{f\"{f\"{x";
    var unclosed_buf = TokenBuffer.init(std.testing.allocator);
    defer unclosed_buf.deinit();
    var unclosed_sink = DiagnosticSink.init(std.testing.allocator);
    defer unclosed_sink.deinit();

    try tokenize(unclosed_slice, FileId.fromInt(0), &unclosed_buf, &unclosed_sink, null);
    try std.testing.expect(unclosed_sink.error_count >= 2);
    try std.testing.expectEqual(
        DiagnosticCode.e0203_parse_depth_exceeded,
        unclosed_sink.asSlice()[0].code,
    );
    try std.testing.expectEqual(
        DiagnosticCode.e0102_unterminated_string_literal,
        unclosed_sink.asSlice()[unclosed_sink.asSlice().len - 1].code,
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

    // Line continuations `\` + `\n` / `\r\n` stay valid; retired `/* … */` emits `E0118` and preserves newline flag:
    const str_source = "\"hello \\\nworld \\\r\n!\" /* block\rcomment */ let ok = 1;";
    var str_buf = TokenBuffer.init(std.testing.allocator);
    defer str_buf.deinit();
    var str_sink = DiagnosticSink.init(std.testing.allocator);
    defer str_sink.deinit();

    try tokenize(str_source, FileId.fromInt(0), &str_buf, &str_sink, null);
    try std.testing.expectEqual(@as(u32, 0), str_sink.warning_count);
    try std.testing.expectEqual(@as(u32, 1), str_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0118_block_doc_comment_forbidden, str_sink.asSlice()[0].code);
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
    const legacy_source = "let ok = flag_a && flag_b&&flag_c; let s = f\"\\{k\\} = {v}\"; fn c_fn(fmt: *opaque, ...);";
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
        "let ok = flag_a and flag_b and flag_c; let s = f\"{{k}} = {v}\"; fn c_fn(fmt: *opaque, ...);",
        patch_res.patched_source,
    );
}

test "test_dr24_multiline_strings_nested_fmt_and_byte_literals" {
    const valid_source =
        \\let banner = f"
        \\    outer {"inner"} and {
        \\        f#"
        \\        nested "quote" {val:'<8}
        \\        "#
        \\    } \
        \\    tail {{v1.0}}
        \\    ";
        \\let raw_multi = r#"
        \\    line 1 /\
        \\    line 2 "triple"
        \\    "#;
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

    try std.testing.expectEqual(TokenKind.fmt_string_lit, token_buf.getToken(TokenIndex.fromInt(3)).kind);
    try std.testing.expectEqual(TokenKind.string_lit, token_buf.getToken(TokenIndex.fromInt(8)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, token_buf.getToken(TokenIndex.fromInt(13)).kind);
    try std.testing.expectEqual(TokenKind.byte_lit, token_buf.getToken(TokenIndex.fromInt(18)).kind);
    try std.testing.expectEqual(TokenKind.byte_string_lit, token_buf.getToken(TokenIndex.fromInt(23)).kind);

    // Verify `extractStringBodyInfo`, `stripMultilineIndentAlloc`, `cookStringLiteral`, and `extractByteLiteralValue`:
    const raw_rec = token_buf.getToken(TokenIndex.fromInt(8));
    const raw_lexeme = valid_source[raw_rec.byte_offset .. raw_rec.byte_offset + raw_rec.byte_len];
    try std.testing.expect(isMultilineStringLexeme(raw_lexeme));
    const body_info = extractStringBodyInfo(.string_lit, raw_lexeme);
    try std.testing.expect(body_info.is_raw);
    try std.testing.expect(body_info.is_multiline);
    try std.testing.expectEqual(@as(u8, 1), body_info.hash_count);
    try std.testing.expectEqual(@as(u32, 4), body_info.closing_indent_spaces);
    const stripped_raw = try stripMultilineIndentAlloc(
        std.testing.allocator,
        raw_lexeme[body_info.body_start..body_info.body_end],
        body_info.closing_indent_spaces,
    );
    defer std.testing.allocator.free(stripped_raw);
    try std.testing.expectEqualStrings("line 1 /\\\nline 2 \"triple\"", stripped_raw);

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

    // Negative diagnostics `E0115`, `E0116`, and `E0117`:
    const err_source =
        "let e1 = \"\n    bad\"; let e2 = \"\n  under\n    \"; let e3 = b'é'; let e4 = b\"\\u{41}\";";
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
    const src = "r#\"\"\"\"# br#\"\"\"\"# r##\"\"\"\"\"## f\"outer {r#\"\"\"\"#} ok\"";
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
    try std.testing.expectEqual(TokenKind.fmt_string_lit, tok_buf.getToken(TokenIndex.fromInt(3)).kind);

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

test "test_adr24a_slash_dfa_retired_comments_and_mid_file_window_is_at_file_top" {
    // [1] Canonical `/#`, `/|`, `///|`, `///#`, `////` banner, and `#!` + `--- … ---` frontmatter with tabs:
    const canonical_src =
        "#!/usr/bin/env\tcorex\n" ++
        "---\n" ++
        "name = \"demo\"\t# tab in frontmatter allowed\n" ++
        "---\n" ++
        "/# Module docstring.\n" ++
        "//// Banner line comment\n" ++
        "///| Commented-out outer doc\n" ++
        "///# Commented-out module doc\n" ++
        "/| Outer item docstring.\n" ++
        "pub fn ok() {}\n";
    var clean_buf = TokenBuffer.init(std.testing.allocator);
    defer clean_buf.deinit();
    var clean_sink = DiagnosticSink.init(std.testing.allocator);
    defer clean_sink.deinit();
    try tokenize(canonical_src, FileId.fromInt(0), &clean_buf, &clean_sink, null);
    try std.testing.expectEqual(@as(u32, 0), clean_sink.error_count);
    try std.testing.expectEqual(@as(u32, 0), clean_sink.warning_count);

    // [2] Retired `//!` (top -> `/#`, mid-file -> `//`), `///` -> `/|`, and `/* … */` -> `//` (`E0118`):
    const legacy_src =
        "//! Top module doc.\n\n" ++
        "/// Item doc.\n" ++
        "/* Hoisted comment */ pub struct Item {\n" ++
        "    //! Mid-file inner doc.\n" ++
        "    pub count: u32, /* trailing */\n" ++
        "}\n";
    var bad_buf = TokenBuffer.init(std.testing.allocator);
    defer bad_buf.deinit();
    var bad_sink = DiagnosticSink.init(std.testing.allocator);
    defer bad_sink.deinit();
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    try tokenize(legacy_src, FileId.fromInt(1), &bad_buf, &bad_sink, &interner);
    try std.testing.expectEqual(@as(u32, 5), bad_sink.error_count);

    var fixes: [5]SuggestedFix = undefined;
    for (bad_sink.asSlice(), 0..) |diag_item, idx| {
        try std.testing.expectEqual(DiagnosticCode.e0118_block_doc_comment_forbidden, diag_item.code);
        fixes[idx] = diag_item.suggestions[0];
    }

    const patch_res = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        legacy_src,
        FileId.fromInt(1),
        &fixes,
        &interner,
    );
    defer std.testing.allocator.free(patch_res.patched_source);
    try std.testing.expectEqual(@as(u32, 5), patch_res.applied_count);
    try std.testing.expectEqualStrings(
        "/# Top module doc.\n\n" ++
            "/| Item doc.\n" ++
            "// Hoisted comment\n" ++
            "pub struct Item {\n" ++
            "    // Mid-file inner doc.\n" ++
            "    pub count: u32, // trailing\n" ++
            "}\n",
        patch_res.patched_source,
    );

    var relex_buf = TokenBuffer.init(std.testing.allocator);
    defer relex_buf.deinit();
    var relex_sink = DiagnosticSink.init(std.testing.allocator);
    defer relex_sink.deinit();
    try tokenize(patch_res.patched_source, FileId.fromInt(1), &relex_buf, &relex_sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), relex_sink.error_count);

    // [3] Mid-file `win_lexer` (`cursor > 0` with empty `token_buffer`) MUST rewrite `//!` to `//`, NOT `/#`:
    const mid_src = "pub fn a() {}\n//! mid\npub fn b() {}\n";
    var win_buf = TokenBuffer.init(std.testing.allocator);
    defer win_buf.deinit();
    var win_sink = DiagnosticSink.init(std.testing.allocator);
    defer win_sink.deinit();
    var win_lexer = Lexer.init(mid_src, FileId.fromInt(2), &win_buf, &win_sink, &interner);
    win_lexer.cursor = 14; // Points directly at `"//! mid\n"`.
    try win_lexer.tokenize();
    try std.testing.expectEqual(@as(u32, 1), win_sink.error_count);
    try std.testing.expectEqualStrings(
        "//",
        interner.get(win_sink.asSlice()[0].suggestions[0].edits[0].replacement_id),
    );

    // [4] Unclosed `/*` at EOF emits both `E0118` and `E0102`:
    var unc_buf = TokenBuffer.init(std.testing.allocator);
    defer unc_buf.deinit();
    var unc_sink = DiagnosticSink.init(std.testing.allocator);
    defer unc_sink.deinit();
    try tokenize("let a = 1; /* unclosed", FileId.fromInt(3), &unc_buf, &unc_sink, null);
    try std.testing.expectEqual(@as(u32, 2), unc_sink.error_count);
    try std.testing.expectEqual(DiagnosticCode.e0118_block_doc_comment_forbidden, unc_sink.asSlice()[0].code);
    try std.testing.expectEqual(DiagnosticCode.e0102_unterminated_string_literal, unc_sink.asSlice()[1].code);
}

test "test_adr24b_plain_braces_retired_triple_quotes_hard_tabs_and_w0119" {
    var interner = try StringInterner.init(std.testing.allocator);
    defer interner.deinit();

    // [1] Plain `"…"` treats `{` / `}` literally (`0` `E0114`), while `\{`/`\}` emit `W0101` (`{`/`}`):
    var plain_buf = TokenBuffer.init(std.testing.allocator);
    defer plain_buf.deinit();
    var plain_sink = DiagnosticSink.init(std.testing.allocator);
    defer plain_sink.deinit();
    try tokenize("let brace = \"{x} } {\"; let esc = \"\\{a\\}\";", FileId.fromInt(0), &plain_buf, &plain_sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), plain_sink.error_count);
    try std.testing.expectEqual(@as(u32, 2), plain_sink.warning_count);
    try std.testing.expectEqual(DiagnosticCode.w0101_redundant_escape_sequence, plain_sink.asSlice()[0].code);
    try std.testing.expectEqualStrings(
        "{",
        interner.get(plain_sink.asSlice()[0].suggestions[0].edits[0].replacement_id),
    );
    const cooked_plain = try cookStringLiteral(std.testing.allocator, "\"{x} {{y}}\"");
    defer std.testing.allocator.free(cooked_plain);
    try std.testing.expectEqualStrings("{x} {{y}}", cooked_plain);

    // [2] `W0119` (`useless-format-string`) on 0-hole `f"…"` / `f#"…"#`:
    const w0119_src = "let s1 = f\"abc {{ok}}\"; let s2 = f#\"a\"b\"#; let s3 = f#\"a\"b\\n\"#;";
    var w_buf = TokenBuffer.init(std.testing.allocator);
    defer w_buf.deinit();
    var w_sink = DiagnosticSink.init(std.testing.allocator);
    defer w_sink.deinit();
    try tokenize(w0119_src, FileId.fromInt(1), &w_buf, &w_sink, &interner);
    try std.testing.expectEqual(@as(u32, 0), w_sink.error_count);
    try std.testing.expectEqual(@as(u32, 3), w_sink.warning_count);
    var w_fixes: [3]SuggestedFix = .{
        w_sink.asSlice()[0].suggestions[0],
        w_sink.asSlice()[1].suggestions[0],
        w_sink.asSlice()[2].suggestions[0],
    };
    const w_patch = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        w0119_src,
        FileId.fromInt(1),
        &w_fixes,
        &interner,
    );
    defer std.testing.allocator.free(w_patch.patched_source);
    try std.testing.expectEqualStrings(
        "let s1 = \"abc {ok}\"; let s2 = r#\"a\"b\"#; let s3 = \"a\\\"b\\n\";",
        w_patch.patched_source,
    );

    // [3] Retired `"""` across `""`, `r`, `f` (`E0115`) with `#`-guard synthesis when inner `"` is present:
    const triple_src =
        "let m1 = \"\"\"\n    plain\n    \"\"\";\n" ++
        "let m2 = r\"\"\"\n    say \"hi\"\n    \"\"\";\n" ++
        "let m3 = f\"\"\"\n    val=\"{x}\"\n    \"\"\";\n";
    var t_buf = TokenBuffer.init(std.testing.allocator);
    defer t_buf.deinit();
    var t_sink = DiagnosticSink.init(std.testing.allocator);
    defer t_sink.deinit();
    try tokenize(triple_src, FileId.fromInt(2), &t_buf, &t_sink, &interner);
    try std.testing.expectEqual(@as(u32, 3), t_sink.error_count);
    var t_fixes: [3]SuggestedFix = .{
        t_sink.asSlice()[0].suggestions[0],
        t_sink.asSlice()[1].suggestions[0],
        t_sink.asSlice()[2].suggestions[0],
    };
    const t_patch = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        triple_src,
        FileId.fromInt(2),
        &t_fixes,
        &interner,
    );
    defer std.testing.allocator.free(t_patch.patched_source);
    try std.testing.expectEqualStrings(
        "let m1 = \"\n    plain\n    \";\n" ++
            "let m2 = r#\"\n    say \"hi\"\n    \"#;\n" ++
            "let m3 = f#\"\n    val=\"{x}\"\n    \"#;\n",
        t_patch.patched_source,
    );

    // [4] Hard `\t` (`0x09`) rules: raw single-line & raw multiline `>= C` allow `\t`; `< C` and cooked reject (`E0116`):
    const raw_tab_ok = "let r1 = r\"a\tb\"; let r2 = br#\"x\ty\"#; let r3 = r\"\n    \tpayload\n    \";";
    var rt_buf = TokenBuffer.init(std.testing.allocator);
    defer rt_buf.deinit();
    var rt_sink = DiagnosticSink.init(std.testing.allocator);
    defer rt_sink.deinit();
    try tokenize(raw_tab_ok, FileId.fromInt(3), &rt_buf, &rt_sink, null);
    try std.testing.expectEqual(@as(u32, 0), rt_sink.error_count);

    const bad_tab_src = "\tlet s_val = \"a\tb\"; // cmt\ttab\nlet rm = r\"\n\t\tdata\n    \";";
    var bt_buf = TokenBuffer.init(std.testing.allocator);
    defer bt_buf.deinit();
    var bt_sink = DiagnosticSink.init(std.testing.allocator);
    defer bt_sink.deinit();
    try tokenize(bad_tab_src, FileId.fromInt(4), &bt_buf, &bt_sink, &interner);
    try std.testing.expectEqual(@as(u32, 4), bt_sink.error_count);
    var bt_fixes: [4]SuggestedFix = .{
        bt_sink.asSlice()[0].suggestions[0],
        bt_sink.asSlice()[1].suggestions[0],
        bt_sink.asSlice()[2].suggestions[0],
        bt_sink.asSlice()[3].suggestions[0],
    };
    const bt_patch = try diagnostic.TransactionalPatcher.apply(
        std.testing.allocator,
        bad_tab_src,
        FileId.fromInt(4),
        &bt_fixes,
        &interner,
    );
    defer std.testing.allocator.free(bt_patch.patched_source);
    try std.testing.expectEqualStrings(
        "    let s_val = \"a\\tb\"; // cmt    tab\nlet rm = r\"\n    \tdata\n    \";",
        bt_patch.patched_source,
    );
}
